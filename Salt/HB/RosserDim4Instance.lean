/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs
import Salt.BrunLower.Pointwise
import Salt.BrunLower.WRatio
import Salt.BrunLower.Lemma3
import Salt.BrunLower.Pair
import Salt.HB.RosserDim4
import Salt.HB.RosserDim4FL

/-!
# The HB instance wiring — the dimension-4 Rosser-sieve service layer (N5 wave 3)

Waves 1–2 built the *abstract* dimension-4 machinery: the block-Brun level bound
(`chi_le_rpow_level`), the `A = 4` Mertens package (`hMert_dim4`, `brun_lower_dim4`,
`brun_upper_dim4`), the fundamental-lemma packaging (`fl_dim4_lower`/`fl_dim4_upper`) and
the first-failure decomposition with its per-δ transfer (`firstFailure_decomposition`,
`hb_perDelta_transfer`).  This file **wires them to Heath-Brown's objects**
(`docs/sources/hb1983-notes.md` §§1–2): the sifted object, the sandwich (2.2), the `W(z)`
identification, and the composed exit statement N8 consumes.

## a4(1) — the sifted object

`Salt/HB/RosserDim4Instance.lean` carries two carriers, and the split is deliberate.

* **The density carrier** `hbSieve P hP hPodd : BoundingSieve` — `prodPrimes = P`,
  `nu = nuG` where `nuG d = ω_G(d)/d` is the multiplicative extension of HB's Lemma-5
  density `G(p)/p = 2(2p−1)/(p(p+1))`.  Its `support`/`weights`/`totalMass` are **zero**:
  everything wave 3 needs from the `BoundingSieve` interface (`W`, `mainSum`, `Wratio`,
  `windowPrimes`) depends only on `(prodPrimes, nu)`, and the *arithmetic* support — the
  `Λ*(l₁)Λ*(l₂)` weights over `x < n ≤ 2x` — cannot be defined until `Λ*` exists.  Wiring a
  fake support would be a lie about `rem`; a zero support is an honest statement that this
  carrier is the density bookkeeping and nothing else.  **What N8 owes:** the real support
  with `rem d` bounded by Lemma 5's `O(x L⁴ z^{−1} d^{−1} 4^{ω(d)})`.
* **The interface structure** `HBSieveData` — the sifted object as HB states it, with the
  parts that are definable today *defined* and the parts that await N8 *carried as fields*:
  the window `support`, the form value `val n = l(n) = l₁(n)l₂(n)`, the weight
  `a n = Λ*(l₁(n))Λ*(l₂(n))`, and the field `a_nonneg` — **HB's Lemma 1 (`Λ* ≥ 0`)**, the
  hypothesis the whole sandwich rests on.  From these, `S d` (HB's `S(d)`) and `S3` (his
  `S⁽³⁾`) are honest *definitions*, not fields.

The sifting set is HB's own: `hbSiftSet χ z = {p : 2 < p, p < z, χ(p) = 1}` for a
`DirichletCharacter ℝ q`, and `hbP χ z = ∏` of it — squarefree, odd, `< z`, and inside the
character's fibre (`hbP_squarefree`, `hbP_odd`, `hbP_lt_z`, `hbP_chi`).

## a4(2) — the sandwich (2.2)

`hb_sandwich_lower` / `hb_sandwich_upper`:

  `Σ_{d∣P} λ⁻_d S(d) ≤ S⁽³⁾ ≤ Σ_{d∣P} λ⁺_d S(d)`,   `λ^±_d = μ(d)·χ_ν(d)` at `ν = 2, 1`.

The proof is the exchange `Σ_{d∣P} λ_d S(d) = Σ_n a_n Σ_{d ∣ (l(n), P)} λ_d`
(`lamSum_eq_sum_over_support`, via `divisors_filter_dvd : {d ∣ P : d ∣ m} = (m, P).divisors`)
followed by the **pointwise** block-Brun pair `Salt.BrunLower.sum_moebius_chi_lower/upper`
at `n = (l(n), P)` — a squarefree divisor of `P` — against the sign `a_n ≥ 0`.  HB derives
(2.2) from Iwaniec's `λ^±` axioms `±Σ_{d∣n} λ^±_d ≥ 0`; at the block-Brun weights that
axiom **is** H-R's (2.5), already in the kernel, so no axiom is assumed here.

## a4(3) — the `W(z)` identification

`moebSum_nu_eq_W : Σ_{d∣P} μ(d)ν(d) = W(z)` (the divisors→powerset reindex against
`Salt.BrunLower.sum_powerset_prod_neg_nu`), and its consequence

  `mainSum_chi_eq_W_sub_correction : Σ_{d∣P} μ(d)χ_ν(d)ν(d) = W(z) − (−1)^ν Σ_{δ∈𝒮} S(δ)`,

which is wave 2's decomposition read literally as "**`W(z)` + a one-signed correction**".
This is the gap the wave-2 handoff named.

## a4(4) — THE N5 EXIT THEOREM

`hbSieve_fl_sandwich` — the three conclusions N8 consumes, at HB's own operating point
(`D = q^{1/3}`, `z ≤ q^{1/3}`, `s = (log D)/(log z) = z₀/3`, recorded by
`hb_levelRatio_eq`):

1. **the sandwich** `Σ λ⁻ S(d) ≤ S⁽³⁾ ≤ Σ λ⁺ S(d)`;
2. **the main-term defect at `ρ₁ = G(d)/d`** — `W(z)(1 − Ce^{−cs}) ≤ Σ_{d∣P} λ⁻_d ρ₁(d)` and
   `Σ_{d∣P} λ⁺_d ρ₁(d) ≤ W(z)(1 + λCe^{−cs})`, `c = flRate λ = log(1/λ)`,
   `C = flConst λ Λ₄` (wave 2's true constants);
3. **the transfer** — for *any* `ρ_i` and *any* per-δ domination `B`,
   `|S_i′ − S_i| ≤ B·|S₁′ − S₁|` (HB p.200).

**N5 IS COMPLETE** with this file.  **What N8 owes** (deliberately not built here):
Lemma 5's evaluation of `S(d)` (the Kloosterman core — `κ G(d)/d {…} + O(xL⁴z^{−1}d^{−1}4^{ω(d)})`,
which is what turns the density carrier into an arithmetic one), and **Lemma 6's per-δ
bounds** `S^{(2)}(δ), S^{(3)}(δ) ≪ BL·S^{(1)}(δ)` together with `S^{(1)}(δ) ≥ 0` — the two
hypotheses conclusion 3 takes as inputs, exactly as HB states them.  Also N8's: HB's
Lemmas 1/2/4 (the `Λ̃`/`Λ*` reduction), which supply this file's `a_nonneg` field.
-/

open Finset Nat
open scoped ArithmeticFunction.Moebius

namespace Salt.HB

open Salt.BrunLower

/-! ## a4(1a) — the density `ν_G` and its `BoundingSieve` carrier -/

/-- **HB's Lemma-5 density as a sieve `ν`**: `ν_G(d) = ω_G(d)/d`, the multiplicative
extension of `G(p)/p = 2(2p−1)/(p(p+1))`.  This is HB's `ρ₁(d) = G(d)/d` (Lemma 6). -/
noncomputable def nuG : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else omegaG d / (d : ℝ), by simp⟩

lemma nuG_apply {d : ℕ} (hd : d ≠ 0) : nuG d = omegaG d / (d : ℝ) := by
  simp only [nuG, ArithmeticFunction.coe_mk, if_neg hd]

/-- At a prime, `ν_G(p) = G(p)/p` — HB's density exactly. -/
lemma nuG_prime {p : ℕ} (hp : p.Prime) : nuG p = Gdens p / (p : ℝ) := by
  rw [nuG_apply hp.ne_zero, omegaG_prime hp]

lemma omegaG_one : omegaG 1 = 1 := by
  rw [omegaG, Nat.primeFactors_one, Finset.prod_empty]

/-- `ω_G` is multiplicative on coprime moduli (disjoint prime supports). -/
lemma omegaG_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    omegaG (m * n) = omegaG m * omegaG n := by
  rw [omegaG, omegaG, omegaG, Nat.primeFactors_mul hm hn,
    Finset.prod_union h.disjoint_primeFactors]

/-- **`nu_mult`** for the density carrier. -/
lemma nuG_isMultiplicative : nuG.IsMultiplicative := by
  constructor
  · rw [nuG_apply one_ne_zero, omegaG_one]; norm_num
  · intro m n h
    rcases eq_or_ne m 0 with rfl | hm
    · rw [Nat.coprime_zero_left] at h; subst h; simp [nuG]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.coprime_zero_right] at h; subst h; simp [nuG]
    have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [nuG_apply hmn, nuG_apply hm, nuG_apply hn, omegaG_mul_of_coprime hm hn h]
    push_cast
    field_simp

/-- **`nu_pos_of_prime`** at the `G`-density. -/
lemma nuG_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < nuG p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  rw [nuG_prime hp, Gdens]
  apply _root_.div_pos (_root_.div_pos (by linarith) (by linarith)) (by linarith)

/-- **`nu_lt_one_of_prime`** at the `G`-density — this is where the sifting primes must be
**odd**: `G(2)/2 = 1` exactly, while `G(p)/p < 1` for `p ≥ 3` because
`1 − G(p)/p = (p−1)(p−2)/(p(p+1))` (HB p.207). -/
lemma nuG_lt_one_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : nuG p < 1 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  rw [nuG_prime hp, Gdens, div_lt_one (by linarith), div_lt_iff₀ (by linarith)]
  nlinarith [hpR]

/-- **THE DENSITY CARRIER.**  HB's sieve situation as a `BoundingSieve`, at the level the
`W`/`mainSum` bookkeeping actually uses: `prodPrimes = P` (the sifting modulus) and
`nu = ν_G`.  The support is **empty by design** — see the module docstring: the arithmetic
support carries `Λ*(l₁)Λ*(l₂)`, which awaits N8, and a fake support would be a false
statement about `rem`.  Every wave-3 consumer (`W`, `mainSum`, `Wratio`, `windowPrimes`,
`hMert_dim4`, `fl_dim4_lower/upper`) reads only `(prodPrimes, nu)`. -/
noncomputable def hbSieve (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) : BoundingSieve where
  support := ∅
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 0
  weights_nonneg := fun _ => le_refl 0
  totalMass := 0
  nu := nuG
  nu_mult := nuG_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => nuG_pos_of_prime hp
  nu_lt_one_of_prime := fun p hp hdvd =>
    nuG_lt_one_of_prime hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hP.ne_zero⟩))

@[simp] lemma hbSieve_prodPrimes {P : ℕ} {hP : Squarefree P}
    {hPodd : ∀ p ∈ P.primeFactors, p ≠ 2} : (hbSieve P hP hPodd).prodPrimes = P := rfl

@[simp] lemma hbSieve_nu {P : ℕ} {hP : Squarefree P}
    {hPodd : ∀ p ∈ P.primeFactors, p ≠ 2} : (hbSieve P hP hPodd).nu = nuG := rfl

/-- The `hnuG` hypothesis of `hMert_dim4`/`brun_lower_dim4` at the carrier: an **equality**,
since the carrier's `ν` *is* the `G`-density. -/
lemma hbSieve_nuG_le {P : ℕ} {hP : Squarefree P} {hPodd : ∀ p ∈ P.primeFactors, p ≠ 2} :
    ∀ q ∈ (hbSieve P hP hPodd).prodPrimes.primeFactors,
      (hbSieve P hP hPodd).nu q ≤ Gdens q / (q : ℝ) := by
  intro q hq
  rw [hbSieve_nu, nuG_prime (Nat.prime_of_mem_primeFactors hq)]

/-! ## a4(1b) — HB's sifting set `{p : 2 < p < z, χ(p) = 1}` and its product `P` -/

open scoped Classical in
/-- **HB's sifting set** (`hb1983-notes.md` §1): the primes `2 < p < z` with `χ(p) = 1`, for
a Dirichlet character `χ` mod `q` (HB's is real primitive; nothing here needs that). -/
noncomputable def hbSiftSet {q : ℕ} (χ : DirichletCharacter ℝ q) (z : ℝ) : Finset ℕ :=
  (Finset.range ⌈z⌉₊).filter
    (fun p => p.Prime ∧ 2 < p ∧ (p : ℝ) < z ∧ χ (p : ZMod q) = 1)

lemma mem_hbSiftSet {q : ℕ} {χ : DirichletCharacter ℝ q} {z : ℝ} {p : ℕ} :
    p ∈ hbSiftSet χ z ↔ p.Prime ∧ 2 < p ∧ (p : ℝ) < z ∧ χ (p : ZMod q) = 1 := by
  classical
  rw [hbSiftSet]
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨Nat.lt_ceil.mpr h3, h1, h2, h3, h4⟩

/-- **HB's sifting modulus** `P = ∏_{2 < p < z, χ(p) = 1} p`. -/
noncomputable def hbP {q : ℕ} (χ : DirichletCharacter ℝ q) (z : ℝ) : ℕ :=
  ∏ p ∈ hbSiftSet χ z, p

/-- A product of distinct primes is squarefree. -/
lemma squarefree_prod_of_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hpp := hS p (Finset.mem_coe.mp hp)
    have hqp := hS q (Finset.mem_coe.mp hq)
    change IsRelPrime p q
    exact hpp.prime.irreducible.isRelPrime_iff_not_dvd.mpr
      (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hpp hqp).mp h))
  · exact fun p hp => (hS p hp).squarefree

lemma hbP_squarefree {q : ℕ} (χ : DirichletCharacter ℝ q) (z : ℝ) : Squarefree (hbP χ z) :=
  squarefree_prod_of_primes (fun _ hp => (mem_hbSiftSet.mp hp).1)

@[simp] lemma hbP_primeFactors {q : ℕ} (χ : DirichletCharacter ℝ q) (z : ℝ) :
    (hbP χ z).primeFactors = hbSiftSet χ z :=
  Nat.primeFactors_prod (fun _ hp => (mem_hbSiftSet.mp hp).1)

lemma hbP_odd {q : ℕ} (χ : DirichletCharacter ℝ q) (z : ℝ) :
    ∀ p ∈ (hbP χ z).primeFactors, p ≠ 2 := by
  intro p hp
  rw [hbP_primeFactors] at hp
  have := (mem_hbSiftSet.mp hp).2.1
  omega

lemma hbP_lt_z {q : ℕ} (χ : DirichletCharacter ℝ q) (z : ℝ) :
    ∀ p ∈ (hbP χ z).primeFactors, (p : ℝ) < z := by
  intro p hp
  rw [hbP_primeFactors] at hp
  exact (mem_hbSiftSet.mp hp).2.2.1

lemma hbP_chi {q : ℕ} (χ : DirichletCharacter ℝ q) (z : ℝ) :
    ∀ p ∈ (hbP χ z).primeFactors, χ (p : ZMod q) = 1 := by
  intro p hp
  rw [hbP_primeFactors] at hp
  exact (mem_hbSiftSet.mp hp).2.2.2

/-! ## a4(1c) — the sifted object as an interface structure -/

/-- **THE HB SIEVE SITUATION** (`hb1983-notes.md` §1–§2a).  The fields split into
*definable today* and *carried for N8*:

* `q`, `chi`, `z`, `P` — the character and the sifting modulus (`hbP` realises `P`);
* `support`, `val`, `a` — the window `x < n ≤ 2x`, the form value `l(n) = l₁(n)l₂(n)`, and
  the weight `a n = Λ*(l₁(n))Λ*(l₂(n))`;
* `a_nonneg` — **HB's Lemma 1**, `Λ*(n) ≥ 0`, hence `a ≥ 0`.  This is the *only* analytic
  input the sandwich needs, and it is carried as an interface field precisely because `Λ*`
  awaits N8. -/
structure HBSieveData where
  /-- The modulus of HB's character. -/
  q : ℕ
  /-- HB's character `χ` (his is real primitive; the sieve side does not use that). -/
  chi : DirichletCharacter ℝ q
  /-- The sifting parameter `z` (HB: `2 ≤ z ≤ q^{1/3}`). -/
  z : ℝ
  /-- `2 ≤ z`. -/
  two_le_z : 2 ≤ z
  /-- The sifting modulus `P = ∏_{2<p<z, χ(p)=1} p`. -/
  P : ℕ
  /-- `P` is squarefree (a product of distinct primes). -/
  P_squarefree : Squarefree P
  /-- The sifting primes are odd (HB sifts `2 < p`); this is what makes `ν_G < 1`. -/
  P_odd : ∀ p ∈ P.primeFactors, p ≠ 2
  /-- The sifting primes lie below `z`. -/
  P_lt_z : ∀ p ∈ P.primeFactors, (p : ℝ) < z
  /-- The sifting primes lie in the fibre `χ(p) = 1`. -/
  P_chi : ∀ p ∈ P.primeFactors, chi (p : ZMod q) = 1
  /-- The window `x < n ≤ 2x`. -/
  support : Finset ℕ
  /-- `val n = l(n) = l₁(n)·l₂(n)`, the quantity the sieve divides. -/
  val : ℕ → ℕ
  /-- `a n = Λ*(l₁(n))·Λ*(l₂(n))`. -/
  a : ℕ → ℝ
  /-- **HB Lemma 1** (`Λ* ≥ 0`), carried: the sandwich's one analytic input. -/
  a_nonneg : ∀ n ∈ support, 0 ≤ a n

/-- **The interface closes on HB's own sifting set.**  Building an `HBSieveData` at
`P = hbP χ z` discharges all four `P`-fields (`hbP_squarefree`/`hbP_odd`/`hbP_lt_z`/
`hbP_chi`), leaving exactly the window data — `support`, `val`, `a`, and HB's Lemma 1 — for
the caller.  That residue is precisely what awaits N8, and nothing else does. -/
noncomputable def HBSieveData.ofHbP {q : ℕ} (χ : DirichletCharacter ℝ q) {z : ℝ}
    (hz : 2 ≤ z) (support : Finset ℕ) (val : ℕ → ℕ) (a : ℕ → ℝ)
    (ha : ∀ n ∈ support, 0 ≤ a n) : HBSieveData where
  q := q
  chi := χ
  z := z
  two_le_z := hz
  P := hbP χ z
  P_squarefree := hbP_squarefree χ z
  P_odd := hbP_odd χ z
  P_lt_z := hbP_lt_z χ z
  P_chi := hbP_chi χ z
  support := support
  val := val
  a := a
  a_nonneg := ha

@[simp] lemma HBSieveData.ofHbP_P {q : ℕ} {χ : DirichletCharacter ℝ q} {z : ℝ}
    {hz : 2 ≤ z} {support : Finset ℕ} {val : ℕ → ℕ} {a : ℕ → ℝ}
    {ha : ∀ n ∈ support, 0 ≤ a n} :
    (HBSieveData.ofHbP χ hz support val a ha).P = hbP χ z := rfl

namespace HBSieveData

variable (H : HBSieveData)

/-- **HB's `S(d)`** (p.198): `S(d) = Σ_{x<n≤2x, d ∣ l} Λ*(l₁)Λ*(l₂)`. -/
noncomputable def S (d : ℕ) : ℝ :=
  ∑ n ∈ H.support.filter (fun n => d ∣ H.val n), H.a n

/-- **HB's `S⁽³⁾`**: the sifted sum, `(l, P) = 1`. -/
noncomputable def S3 : ℝ :=
  ∑ n ∈ H.support.filter (fun n => Nat.Coprime (H.val n) H.P), H.a n

/-- `S(d) ≥ 0` — this is the `hSnonneg` the brief names, and it is a *theorem* here, off the
`a_nonneg` field (HB Lemma 1). -/
lemma S_nonneg (d : ℕ) : 0 ≤ H.S d :=
  Finset.sum_nonneg fun n hn => H.a_nonneg n (Finset.mem_filter.mp hn).1

/-- The density carrier attached to the situation. -/
noncomputable def sieve : BoundingSieve := hbSieve H.P H.P_squarefree H.P_odd

@[simp] lemma sieve_prodPrimes : H.sieve.prodPrimes = H.P := rfl

@[simp] lemma sieve_nu : H.sieve.nu = nuG := rfl

end HBSieveData

/-! ## a4(2) — the weights, the two aggregate sums, and the sandwich (2.2) -/

/-- **The block-Brun weight system** `λ_d = μ(d)·χ_ν(d)` (H-R (2.10)); `ν = 1` is the upper
side, `ν = 2` the lower.  These are the `λ^±_d(D)` of HB (2.2): the level `D` enters through
the depth `b = flB s Λ`, which makes every kept `d` lie below `D` (`flB_level_bound`). -/
noncomputable def lamBB (Lam z : ℝ) (side b d : ℕ) : ℝ :=
  (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0)

/-- HB's `S_i′ = Σ_{d ∣ P} ρ_i(d) λ_d` (p.200). -/
noncomputable def lamSum (Lam z : ℝ) (side b P : ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ d ∈ P.divisors, lamBB Lam z side b d * rho d

/-- HB's `S_i = Σ_{d ∣ P} ρ_i(d) μ(d)` (Lemma 6). -/
noncomputable def moebSum (P : ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ d ∈ P.divisors, (μ d : ℝ) * rho d

/-- The divisors of `P` that also divide `m` are exactly the divisors of `(m, P)`. -/
lemma divisors_filter_dvd {P : ℕ} (hP : P ≠ 0) (m : ℕ) :
    P.divisors.filter (fun d => d ∣ m) = (Nat.gcd m P).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdP, _⟩, hdm⟩
    exact ⟨Nat.dvd_gcd hdm hdP, fun h => hP (Nat.eq_zero_of_gcd_eq_zero_right h)⟩
  · rintro ⟨hd, _⟩
    exact ⟨⟨hd.trans (Nat.gcd_dvd_right _ _), hP⟩, hd.trans (Nat.gcd_dvd_left _ _)⟩

/-- **THE EXCHANGE.**  For any weight system `λ`,
`Σ_{d∣P} λ_d S(d) = Σ_n a_n · Σ_{d ∣ (l(n), P)} λ_d`.  This is the step that turns a sum
over moduli into a sum over the window against the *pointwise* sieve sum — the only place
the double sum is reordered. -/
lemma lamSum_eq_sum_over_support (H : HBSieveData) (lamf : ℕ → ℝ) :
    ∑ d ∈ H.P.divisors, lamf d * H.S d
      = ∑ n ∈ H.support, H.a n * ∑ d ∈ (Nat.gcd (H.val n) H.P).divisors, lamf d := by
  have hP0 : H.P ≠ 0 := H.P_squarefree.ne_zero
  have hstep : ∀ d : ℕ, lamf d * H.S d
      = ∑ n ∈ H.support, (if d ∣ H.val n then lamf d * H.a n else 0) := by
    intro d
    rw [HBSieveData.S, Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by by_cases h : d ∣ H.val n <;> simp [h]
  rw [Finset.sum_congr rfl (fun d _ => hstep d), Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_filter, divisors_filter_dvd hP0 (H.val n), Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- `S⁽³⁾` in the pointwise-indicator form the sandwich compares against. -/
lemma S3_eq_sum_indicator (H : HBSieveData) :
    H.S3 = ∑ n ∈ H.support, H.a n * (if Nat.gcd (H.val n) H.P = 1 then (1 : ℝ) else 0) := by
  rw [HBSieveData.S3, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : Nat.gcd (H.val n) H.P = 1
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Every `(l(n), P)` is a squarefree divisor of `P` with all prime factors below `z`. -/
lemma gcd_val_facts (H : HBSieveData) (n : ℕ) :
    Squarefree (Nat.gcd (H.val n) H.P)
      ∧ ∀ p ∈ (Nat.gcd (H.val n) H.P).primeFactors, (p : ℝ) < H.z := by
  have hdvd : Nat.gcd (H.val n) H.P ∣ H.P := Nat.gcd_dvd_right _ _
  refine ⟨Squarefree.squarefree_of_dvd hdvd H.P_squarefree, fun p hp => ?_⟩
  exact H.P_lt_z p (Nat.primeFactors_mono hdvd H.P_squarefree.ne_zero hp)

/-- **a4(2) — THE SANDWICH (2.2), UPPER SIDE.**  `S⁽³⁾ ≤ Σ_{d∣P} λ⁺_d S(d)` at the
block-Brun weights `λ⁺ = μ·χ₁`.  HB gets this from Iwaniec's `λ^±` axioms; here it is
H-R's own pointwise inequality (`sum_moebius_chi_upper`, already in the kernel) against
`Λ*Λ* ≥ 0`. -/
theorem hb_sandwich_upper (H : HBSieveData) {Lam : ℝ} {b : ℕ} (hb : 1 ≤ b) :
    H.S3 ≤ lamSum Lam H.z 1 b H.P H.S := by
  rw [lamSum, lamSum_eq_sum_over_support H (fun d => lamBB Lam H.z 1 b d),
    S3_eq_sum_indicator H]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hsq, hpz⟩ := gcd_val_facts H n
  have hpt := sum_moebius_chi_upper (Lam := Lam) (z := H.z) (b := b) hb hsq hpz
  exact mul_le_mul_of_nonneg_left hpt (H.a_nonneg n hn)

/-- **a4(2) — THE SANDWICH (2.2), LOWER SIDE.**  `Σ_{d∣P} λ⁻_d S(d) ≤ S⁽³⁾` at
`λ⁻ = μ·χ₂`.  HB: "the treatment of the lower bound being similar" (p.199); here it is the
mirror pointwise inequality `sum_moebius_chi_lower`. -/
theorem hb_sandwich_lower (H : HBSieveData) {Lam : ℝ} {b : ℕ} (hb : 1 ≤ b) :
    lamSum Lam H.z 2 b H.P H.S ≤ H.S3 := by
  rw [lamSum, lamSum_eq_sum_over_support H (fun d => lamBB Lam H.z 2 b d),
    S3_eq_sum_indicator H]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hsq, hpz⟩ := gcd_val_facts H n
  have hpt := sum_moebius_chi_lower (Lam := Lam) (z := H.z) (b := b) hb hsq hpz
  exact mul_le_mul_of_nonneg_left hpt (H.a_nonneg n hn)

/-! ## a4(3) — the `W(z)` identification and the "`W(z)` + correction" reading -/

/-- **a4(3) — `Σ_{d∣P} μ(d)ν(d) = W(z)`.**  The singular-product bookkeeping: the divisor
sum over a squarefree `P` reindexes along the powerset of its prime factors
(`sum_divisors_eq_sum_powerset`), each term folds the Möbius sign into the density
(`moebius_nu_prod_eq`), and the powerset sum is the Euler product
(`sum_powerset_prod_neg_nu`).  This is the identification the wave-2 handoff named as
missing. -/
theorem moebSum_nu_eq_W (s : BoundingSieve) :
    moebSum s.prodPrimes (fun d => s.nu d) = W s := by
  rw [moebSum, sum_divisors_eq_sum_powerset s.prodPrimes_squarefree
    (fun d => (μ d : ℝ) * s.nu d), ← sum_powerset_prod_neg_nu s]
  exact Finset.sum_congr rfl fun T hT => moebius_nu_prod_eq s (Finset.mem_powerset.mp hT)

/-- `mainSum` at any weight system *is* `lamSum`/`moebSum` at the carrier's density. -/
lemma mainSum_eq_lamSum (s : BoundingSieve) (Lam z : ℝ) (side b : ℕ) :
    s.mainSum (fun d => lamBB Lam z side b d) = lamSum Lam z side b s.prodPrimes
      (fun d => s.nu d) := rfl

/-- **a4(3) — "`W(z)` + a one-signed correction".**  Wave 2's decomposition read at the
density: the λ-weighted main sum is `W(z)` minus the first-failure correction, whose sign is
`(−1)^ν` (constant on `𝒮`, `failSet_moebius`).  At `ν = 1` the correction is subtracted with
a `+`, at `ν = 2` with a `−` — which is exactly why `ν = 1` over- and `ν = 2` under-shoots. -/
theorem mainSum_chi_eq_W_sub_correction (s : BoundingSieve) {Lam z : ℝ} {side b : ℕ}
    (hb : 1 ≤ b) (hside : side ≤ 2) :
    lamSum Lam z side b s.prodPrimes (fun d => s.nu d)
      = W s - ((-1 : ℝ) ^ side) *
          ∑ δ ∈ failSet Lam z side b s.prodPrimes,
            deltaSum s.prodPrimes δ (fun d => s.nu d) := by
  have hdec := firstFailure_decomposition_signed (Lam := Lam) (z := z) hb hside
    s.prodPrimes_squarefree (fun d => s.nu d)
  have hW := moebSum_nu_eq_W s
  rw [moebSum] at hW
  rw [lamSum]
  simp only [lamBB]
  linarith [hdec, hW]

/-! ## a4(4) — the fundamental-lemma endpoints at the HB instance -/

/-- The level ratio at HB's operating point: with `D = q^{1/3}` and `z₀ = (log q)/(log z)`,
`s = (log D)/(log z) = z₀/3`.  This is the `sRatio` every constant below is measured in
(HB p.200: "since `(log D)/(log z) = ⅓z₀`"). -/
lemma hb_levelRatio_eq {qR z : ℝ} (hq : 0 < qR) :
    Real.log (qR ^ ((1 : ℝ) / 3)) / Real.log z = (Real.log qR / Real.log z) / 3 := by
  rw [Real.log_rpow hq]
  ring

/-- **THE FL LOWER ENDPOINT AT THE HB INSTANCE.**  At the density carrier, with the depth
`b = flB s Λ₄` (every kept modulus below `D = z^s`, `flB_level_bound`),

  `W(z)·(1 − C·e^{−c·s}) ≤ Σ_{d∣P} λ⁻_d ρ₁(d)`,  `c = log(1/λ)`, `C = flConst λ Λ₄`.

All of `fl_dim4_lower`'s hypotheses are discharged from the instance data: the (2.16)
density inputs from `Wratio_le_exp`/`windowSum_le` against `hMert_dim4`, and `hcorr` from
`hcorr_lower`. -/
theorem hb_fl_lower (P : ℕ) (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2)
    {lam z sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) (hz : zThresh lam ≤ z)
    (hPz : ∀ p ∈ P.primeFactors, (p : ℝ) < z)
    (hs : levelE (Lam4 lam z) ≤ sRatio) :
    W (hbSieve P hP hPodd) * (1 - flConst lam (Lam4 lam z) * Real.exp (-(flRate lam) * sRatio))
      ≤ lamSum (Lam4 lam z) z 2 (flB sRatio (Lam4 lam z)) P (fun d => nuG d) := by
  set s := hbSieve P hP hPodd with hsdef
  set Lam := Lam4 lam z with hLdef
  obtain ⟨_, _, _, _, _, _, hz2⟩ := zThresh_facts hlam hlam' hz
  have hz1 : (1 : ℝ) < z := by linarith
  have hLam : 0 < Lam := Lam4_pos hlam hlam' hz
  have hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z := hPz
  have hodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2 := hPodd
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ Gdens q / (q : ℝ) := hbSieve_nuG_le
  have hMert := hMert_dim4 s hlam hlam' hz hp hodd hnu
  exact fl_dim4_lower s hlam (lam_exp_lt_one hlam hlam') hs
    (windowPrimes s Lam z) (windowPrimes_subset s Lam z)
    (Wratio s Lam z) (fun n _ => (Wratio_pos s Lam z n).le)
    (Wratio_le_exp s (kappa_dim4 lam) hMert) (windowSum_le s (kappa_dim4 lam) hMert)
    (hcorr_lower s hLam hz1 (one_le_flB hs) hp)

/-- **THE FL UPPER ENDPOINT AT THE HB INSTANCE.**  `Σ_{d∣P} λ⁺_d ρ₁(d) ≤ W(z)·(1 + λC e^{−cs})`
— the upper side's defect carries the extra power of `λ` (H-R's `λ^{2b+1}`). -/
theorem hb_fl_upper (P : ℕ) (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2)
    {lam z sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) (hz : zThresh lam ≤ z)
    (hPz : ∀ p ∈ P.primeFactors, (p : ℝ) < z)
    (hs : levelE (Lam4 lam z) ≤ sRatio) :
    lamSum (Lam4 lam z) z 1 (flB sRatio (Lam4 lam z)) P (fun d => nuG d)
      ≤ W (hbSieve P hP hPodd)
        * (1 + lam * flConst lam (Lam4 lam z) * Real.exp (-(flRate lam) * sRatio)) := by
  set s := hbSieve P hP hPodd with hsdef
  set Lam := Lam4 lam z with hLdef
  obtain ⟨_, _, _, _, _, _, hz2⟩ := zThresh_facts hlam hlam' hz
  have hz1 : (1 : ℝ) < z := by linarith
  have hLam : 0 < Lam := Lam4_pos hlam hlam' hz
  have hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z := hPz
  have hodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2 := hPodd
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ Gdens q / (q : ℝ) := hbSieve_nuG_le
  have hMert := hMert_dim4 s hlam hlam' hz hp hodd hnu
  exact fl_dim4_upper s hlam (lam_exp_lt_one hlam hlam') hs
    (windowPrimes s Lam z) (windowPrimes_subset s Lam z)
    (Wratio s Lam z) (fun n _ => (Wratio_pos s Lam z n).le)
    (Wratio_le_exp s (kappa_dim4 lam) hMert) (windowSum_le s (kappa_dim4 lam) hMert)
    (hcorr_upper s hLam hz1 (one_le_flB hs) hp)

/-- **THE TRANSFER AT THE HB INSTANCE** (HB p.200).  For any density `ρ_i` dominated per-δ
by `ρ₁ = G(d)/d`, the fundamental-lemma saving transfers at the cost of the single factor
`B` (HB's `BL`).  The two hypotheses are *exactly* Lemma 6's, which is N8's. -/
theorem hb_transfer (P : ℕ) (hP : Squarefree P) {Lam z : ℝ} {side b : ℕ}
    (hb : 1 ≤ b) (hside : side ≤ 2) (rhoi : ℕ → ℝ) (B : ℝ)
    (hnn : ∀ δ ∈ failSet Lam z side b P, 0 ≤ deltaSum P δ (fun d => nuG d))
    (hdom : ∀ δ ∈ failSet Lam z side b P,
      |deltaSum P δ rhoi| ≤ B * deltaSum P δ (fun d => nuG d)) :
    |lamSum Lam z side b P rhoi - moebSum P rhoi|
      ≤ B * |lamSum Lam z side b P (fun d => nuG d) - moebSum P (fun d => nuG d)| :=
  hb_perDelta_transfer hb hside hP (fun d => nuG d) rhoi B hnn hdom

/-! ## THE N5 EXIT THEOREM -/

/-- **N5 COMPLETE — THE DIMENSION-4 ROSSER-SIEVE SERVICE LAYER.**

At HB's operating point (`hb_levelRatio_eq`: `D = q^{1/3}`, `z ≤ q^{1/3}`,
`s = (log D)/(log z) = z₀/3`), with the block depth `b = flB s Λ₄` — the depth for which
every kept modulus lies below `D` (`flB_level_bound`) — and the dimension-4 ladder scale
`Λ₄ = (λ/2)(1 − 300/loglog z)`, the three things HB's p.200 assembly consumes hold at once:

1. **THE SANDWICH (2.2)** — `Σ_{d∣P} λ⁻_d S(d) ≤ S⁽³⁾ ≤ Σ_{d∣P} λ⁺_d S(d)`, off `Λ* ≥ 0`
   (HB Lemma 1, the `a_nonneg` field) and H-R's pointwise pair.
2. **THE MAIN-TERM DEFECT** at `ρ₁ = G(d)/d` — `W(z)(1 − C e^{−cs}) ≤ S₁′⁻` and
   `S₁′⁺ ≤ W(z)(1 + λC e^{−cs})`, with the **true** constants `c = flRate λ = log(1/λ)`
   (`= log 4 = 1.386` at `λ = 1/4`) and `C = flConst λ Λ₄` (`flConst_quarter_le`:
   `≤ 14e^{31}` once `Λ₄ ≥ 1/10`).  This is the block-Brun substitute for Iwaniec
   [10, Thm 4]'s `S₁′ − S₁ ≪ e^{−z₀/4}S₁`.
3. **THE ρ₂/ρ₃ TRANSFER** — at *any* per-δ domination `B`, `|S_i′ − S_i| ≤ B|S₁′ − S₁|`.

**WHAT N8 OWES.**  (i) **Lemma 5** — the evaluation `S(d) = κ(G(d)/d){(L′/L)² + A²(d) + A′(d)
+ C₀} + O(xL⁴z^{−1}d^{−1}4^{ω(d)})`, the Kloosterman core; it is what upgrades the density
carrier `hbSieve` (whose support is empty by design) to an arithmetic one with a bounded
`rem`.  (ii) **Lemma 6** — the per-δ bounds `S^{(1)}(δ) ≥ 0` and `S^{(2)}(δ), S^{(3)}(δ) ≪
BL·S^{(1)}(δ)`, which conclusion 3 takes as hypotheses verbatim.  (iii) HB's Lemmas 1/2/4
(the `Λ̃`/`Λ*` reduction `S⁽⁰⁾ = S⁽³⁾ + O(xz₀^{−1})`), which supply the `a_nonneg` field. -/
theorem hbSieve_fl_sandwich (H : HBSieveData) {lam sRatio : ℝ}
    (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) (hz : zThresh lam ≤ H.z)
    (hs : levelE (Lam4 lam H.z) ≤ sRatio) :
    -- (1) the sandwich (2.2)
    (lamSum (Lam4 lam H.z) H.z 2 (flB sRatio (Lam4 lam H.z)) H.P H.S ≤ H.S3
      ∧ H.S3 ≤ lamSum (Lam4 lam H.z) H.z 1 (flB sRatio (Lam4 lam H.z)) H.P H.S)
    -- (2) the main-term defect at `ρ₁ = G(d)/d`
    ∧ (W H.sieve * (1 - flConst lam (Lam4 lam H.z) * Real.exp (-(flRate lam) * sRatio))
          ≤ lamSum (Lam4 lam H.z) H.z 2 (flB sRatio (Lam4 lam H.z)) H.P (fun d => nuG d)
        ∧ lamSum (Lam4 lam H.z) H.z 1 (flB sRatio (Lam4 lam H.z)) H.P (fun d => nuG d)
          ≤ W H.sieve
            * (1 + lam * flConst lam (Lam4 lam H.z) * Real.exp (-(flRate lam) * sRatio)))
    -- (3) the per-δ transfer, at any density `ρ_i` and any domination `B`
    ∧ (∀ (side : ℕ), side ≤ 2 → ∀ (rhoi : ℕ → ℝ) (B : ℝ),
        (∀ δ ∈ failSet (Lam4 lam H.z) H.z side (flB sRatio (Lam4 lam H.z)) H.P,
          0 ≤ deltaSum H.P δ (fun d => nuG d)) →
        (∀ δ ∈ failSet (Lam4 lam H.z) H.z side (flB sRatio (Lam4 lam H.z)) H.P,
          |deltaSum H.P δ rhoi| ≤ B * deltaSum H.P δ (fun d => nuG d)) →
        |lamSum (Lam4 lam H.z) H.z side (flB sRatio (Lam4 lam H.z)) H.P rhoi
            - moebSum H.P rhoi|
          ≤ B * |lamSum (Lam4 lam H.z) H.z side (flB sRatio (Lam4 lam H.z)) H.P
              (fun d => nuG d) - moebSum H.P (fun d => nuG d)|) := by
  have hb : 1 ≤ flB sRatio (Lam4 lam H.z) := one_le_flB hs
  refine ⟨⟨hb_sandwich_lower H hb, hb_sandwich_upper H hb⟩,
    ⟨hb_fl_lower H.P H.P_squarefree H.P_odd hlam hlam' hz H.P_lt_z hs,
     hb_fl_upper H.P H.P_squarefree H.P_odd hlam hlam' hz H.P_lt_z hs⟩,
    fun side hside rhoi B hnn hdom =>
      hb_transfer H.P H.P_squarefree hb hside rhoi B hnn hdom⟩

end Salt.HB
