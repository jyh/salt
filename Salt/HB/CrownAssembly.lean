/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cCore
import Salt.HB.SieveWire
import Salt.HB.CharTrio
import Salt.Maynard.Mertens

/-!
# N8, THE SIEVE HALF — HB 1983's p.200 assembly from the dimension-4 sieve (design freeze v2)

**STATUS: A DESIGN FREEZE, v2 (after the refuter pass).  Every theorem below is
`sorry`-bodied by design.**  This file is one half of node N8 of the Heath-Brown engine
(`docs/sources/hb1983-notes.md` §1–§2, pp.199–200, and Lemma 6, pp.204–206): the sieve wire
at the crown window, HB Lemma 6 proved here with literal constants, HB Lemma 5 as an
INTERFACE (N7's exit, Wave C-2 row C2-10), and the p.200 assembly
`S⁽³⁾ ≤ κS₁{(L′/L)² + O(BL) + O(B²e^{−z₀/4})} + O(xL⁸/z)` (both signs).  The other half —
the reduction chain `S⁽⁰⁾ → S⁽³⁾` on the window and Lemma 3 at the pretense sum — is
`Salt/HB/CrownChain.lean`; the two files share no declaration and neither imports the
other, so two executors can work them in parallel in one checkout (one file each).  Each
docstring carries the row's **class**, its **line cap**, the **red-first idea**, and the
**consumer** of the statement by Lean name.

Nothing here bears on twin primes: N8 assembles nothing on its own.  The dichotomy
`fulcrum_dichotomy` stays conditional on `hEngine` until N7 (Waves A/B/C), N8, N4's
composition wave, the `z` witness (seam S3), N9, N10 and N12 land.  N11 is closed
(`twinPrimeConjecture_of_frequently_S1`, `Salt/HB/DoorBridge.lean`, sorry-free).

## THE TWO DESIGN DECISIONS OF THIS HALF (seams S1, S2 of the crown census)

**S1 — the window is `l2cWindow χ z x`** (chosen in `CrownChain.lean`); the sieve reaches it
through a second wire `hbDataN8` (the `SieveWire` pattern at this window).  `hbData`
(`SieveWire.lean`) is SUPERSEDED for the crown path (it stays landed, untouched).

**S2 — ONE `S⁽³⁾`.**  `excPrimorial χ z` is the product of the primes `p < z` with
`χ_ℝ(p) ≠ −1`, and HB's sifting modulus `hbP` is the product of the primes `2 < p < z` with
`χ_ℝ(p) = 1` — a sub-product.  So `excPrimorial`-coprimality (the window's) gives
`hbP`-coprimality, the `(l, P) = 1` filter of `hbData_S3_eq` is the identity on the window,
and `hbDataN8_S3_eq` identifies the interface's sifted sum with the star step's
`S3 χ z (l2cWindow χ z x)` with NO residual filter.

## THE STATEMENT REPAIRS OF v2 (the refuter pass, 2026-09-03 18:1x)

* `deltaSum_nuG_mul_additive` (HB (3.6)) now carries `hPodd` — v1 divided by `1 − ν_G(p)`
  with `ν_G(2) = 1` exactly (`nuG_lt_one_of_prime` carries `p ≠ 2` for this reason; HB p.205
  invokes "`P` is odd" at exactly this line).  Counterexample to v1: `P = 6`, `δ = 3`.
* `Lemma5Eval` carries the three nonnegativity fields `CA_nonneg`, `CA'_nonneg`,
  `Cerr_nonneg`: the Lemma-6 rows demand `0 ≤ B′`, `0 ≤ CA`, and `Lemma5Eval`'s prime-wise
  bounds are VACUOUS when `hbP = 1`, so nothing else supplies them.  (`0 ≤ CC` follows from
  `C₀_le` at `L ≥ 3`; not a field.)  Wave C-2 prints literal nonnegative constants anyway.

## WHAT N8 KEEPS SYMBOLIC (and why)

* The VALUES `LL = L′(1,χ)/L(1,χ)` and `kappa` are free parameters here, identified by N9
  with N4's terminals (`(L1)`, `hb_L2_at_split_point_charTrio`).
* `Lemma5Eval` is an interface: Wave C-2 (row C2-10) PRODUCES it at `H := hbDataN8 …`; the
  p.200 rows CONSUME it.  Its constants `CA CA' CC Cerr` are literal parameters — Wave C must
  print them; N8 never writes `≪`.
* `z` is free with the landed binders carried (`hzt hs` of the sieve, and
  `3·sRatio·log z ≤ L` for HB's `D = q^{1/3}`); N9 discharges them at HB's `z = q^{1/z₀}`,
  `z₀ = A·log log η` (seam S3 is N9's, not N8's).  ⚠ `hzt` forces `log log z ≥ 400`
  (`zThresh_facts`), so the crown's threshold is `log q ≥ z₀·e^{400}` — a threshold in `q`,
  not in `η`; N9's `C0` must name it.

## THE ROWS (executor order; class per the salt CLAUDE.md table)

§1 the wire at the window · §5 Lemma 6 (the densities) · §6 Lemma 5 interface + the p.200
assembly · §7 the `κS₁` wire.  (§2–§4 are `CrownChain.lean`'s; the numbering is the freeze
brief's.)  Order: W2–W4 → D0–D3 → D4 → D5/D7/D8 → D6/D9 → D10 → T1/T2 → E1/E2 → P+ → P− → K1.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius
open Salt.TwinBar
open Salt.BrunLower
open Salt.SW

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the sieve wire at the crown window (S2) -/

/-- **The `(l, P) = 1` filter is vacuous on the N8 window.**  Every prime of
`hbP (chiReChar χ hsq) z` is `2 < p < z` with `χ_ℝ(p) = 1`, hence `≠ −1`, hence a factor of
`excPrimorial χ z` (`StarWindow.lean`: the primes `p < z` with `chiRe χ p ≠ −1`); so
`excPrimorial`-coprimality gives `hbP`-coprimality.  Class **A**, cap 60.
Red-first: `Nat.Coprime.coprime_dvd_right` with `hbP ∣ excPrimorial` proved by
`Finset.prod_dvd_prod_of_subset` after `hbSiftSet_chiReChar`, from
`l2cWindow_excPrimorial_coprime`.  Consumer: `hbDataN8_S3_eq`. -/
theorem l2cWindow_coprime_hbP (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ) :
    ∀ n ∈ l2cWindow χ z x, Nat.Coprime (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ)) := by
  classical
  intro n hn
  have hcop := l2cWindow_excPrimorial_coprime χ z x n hn
  refine Nat.Coprime.coprime_dvd_right ?_ hcop
  rw [hbP, hbSiftSet_chiReChar, excPrimorial]
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  obtain ⟨hr, hpp, _, hchi⟩ := hp
  refine ⟨hr, hpp, ?_⟩
  rw [hchi]
  norm_num

/-- **THE N8 WIRE.**  The `HBSieveData` at the N8 window: character `chiReChar χ hsq`,
modulus `hbP`, `support := l2cWindow χ z x`, `val n = n(n+2)`, `a n = Λ*(n)Λ*(n+2)` with
HB's Lemma 1 (`LamStar_nonneg`) as `a_nonneg`.  A definition (no obligation).  This supersedes
`hbData` (`SieveWire.lean`) on the crown path; both are wires, neither is an estimate. -/
noncomputable def hbDataN8 (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (x : ℕ) : HBSieveData :=
  HBSieveData.ofHbP (chiReChar χ hsq) (z := (z : ℝ)) (by exact_mod_cast hz)
    (l2cWindow χ z x) (fun n => n * (n + 2))
    (fun n => LamStar χ z n * LamStar χ z (n + 2))
    (fun n _ => mul_nonneg (LamStar_nonneg χ hsq z n) (LamStar_nonneg χ hsq z (n + 2)))

/-- The N8 wire sifts by HB's own modulus (`rfl`; no obligation). -/
theorem hbDataN8_P (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) : (hbDataN8 χ hsq hz x).P = hbP (chiReChar χ hsq) (z : ℝ) := rfl

/-- **ONE `S⁽³⁾` (seam S2 closed with no residual).**  The interface's sifted sum at the N8
wire IS the star step's `S3` on the N8 window — the `(l, P) = 1` filter is the identity there
(`l2cWindow_coprime_hbP`).  Class **A**, cap 40.  Red-first: unfold `HBSieveData.S3`, then
`Finset.filter_true_of_mem`.  Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem hbDataN8_S3_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) :
    (hbDataN8 χ hsq hz x).S3 = S3 χ z (l2cWindow χ z x) := by
  change ∑ n ∈ (l2cWindow χ z x).filter
      (fun n => Nat.Coprime (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ))),
      LamStar χ z n * LamStar χ z (n + 2) = _
  rw [Finset.filter_true_of_mem (l2cWindow_coprime_hbP χ hsq z x)]
  rfl

/-- **The N5 exit at the N8 wire** — `hbSieve_fl_sandwich` at `hbDataN8`, with the sifted sum
rewritten through `hbDataN8_S3_eq`.  Class **A**, cap 60 (the mirror of `hbData_fl_sandwich`,
mechanical).  Consumer: `hb_p200_upper`, `hb_p200_lower`.  Only conclusion (1) is restated
here; (2) and (3) are read directly off `hbSieve_fl_sandwich (hbDataN8 …)`. -/
theorem hbDataN8_sandwich (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (x : ℕ) {lam sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hzt : zThresh lam ≤ (z : ℝ)) (hs : levelE (Lam4 lam (z : ℝ)) ≤ sRatio) :
    lamSum (Lam4 lam (z : ℝ)) (z : ℝ) 2 (flB sRatio (Lam4 lam (z : ℝ)))
          (hbP (chiReChar χ hsq) (z : ℝ)) (hbDataN8 χ hsq hz x).S
        ≤ S3 χ z (l2cWindow χ z x)
      ∧ S3 χ z (l2cWindow χ z x)
        ≤ lamSum (Lam4 lam (z : ℝ)) (z : ℝ) 1 (flB sRatio (Lam4 lam (z : ℝ)))
            (hbP (chiReChar χ hsq) (z : ℝ)) (hbDataN8 χ hsq hz x).S := by
  have h := hbSieve_fl_sandwich (hbDataN8 χ hsq hz x) hlam hlam' hzt hs
  rw [hbDataN8_S3_eq] at h
  exact h.1

/-! ## §5 — HB Lemma 6 (pp.199, 204–206): the three densities and the per-δ bounds

The landed sieve (`RosserDim4FL`, `RosserDim4Instance`) proves the per-δ TRANSFER
(`hb_transfer`) for ANY density dominated per-δ by `ρ₁ = ν_G`; Lemma 6 is exactly the two
hypotheses it takes, and this section proves them for `ρ₂ = ν_G·A′` and `ρ₃ = ν_G·A²` with
`A, A′` additive on the divisors of `P` and bounded at primes.  The constants are literal;
HB's `≪ BL` becomes `64·B′·L` and his `≪ L²` becomes `(128·CA·L)²` (both with ample slack,
computed in the freeze brief §2 and re-derived by the refuter pass; bounded numeral amendment
is pre-authorised: `64 → ≤ 256`, `128 → ≤ 512`, the `3 ≤ L` guard `→ ≤ 10`). -/

/-- **Additivity on the divisors of a squarefree modulus.**  Mathlib has `IsMultiplicative`
(`ArithmeticFunction/Defs.lean`) and no additive sibling (the Wave C scout, §0); this is the
one N8 and Wave C-2 (row C2-07) share — Wave C imports it from here. -/
def IsAdditiveOn (P : ℕ) (A : ℕ → ℝ) : Prop :=
  A 1 = 0 ∧ ∀ d e : ℕ, d ∣ P → e ∣ P → Nat.Coprime d e → A (d * e) = A d + A e

/-- `ν_G` on a product of distinct primes. -/
lemma nuG_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    nuG (∏ p ∈ S, p) = ∏ p ∈ S, nuG p :=
  nuG_isMultiplicative.map_prod_of_subset_primeFactors _ _
    (by rw [Nat.primeFactors_prod hS])

/-- `μ(∏S)·ν_G(∏S) = ∏_{p∈S}(−ν_G p)`. -/
lemma moebius_nuG_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (μ (∏ p ∈ S, p) : ℝ) * nuG (∏ p ∈ S, p) = ∏ p ∈ S, (- nuG p) := by
  rw [moebius_real_of_squarefree (squarefree_prod_of_primes hS), Nat.primeFactors_prod hS,
    nuG_prod_primes hS,
    show (∏ p ∈ S, (- nuG p)) = ∏ p ∈ S, ((-1 : ℝ) * nuG p) from
      Finset.prod_congr rfl (fun p _ => by ring),
    Finset.prod_mul_distrib, Finset.prod_const]

/-- `lowDiv P δ` is the divisor set of `P(δ) = ∏_{p ∣ P, p < p(δ)} p`. -/
lemma lowDiv_eq_divisors {P δ : ℕ} (hP : Squarefree P) :
    lowDiv P δ = (∏ p ∈ P.primeFactors.filter (fun p => p < δ.minFac), p).divisors := by
  classical
  set Q := P.primeFactors.filter (fun p => p < δ.minFac) with hQ
  have hQprime : ∀ p ∈ Q, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hQsub : Q ⊆ P.primeFactors := Finset.filter_subset _ _
  have hPdsq : Squarefree (∏ p ∈ Q, p) := squarefree_prod_of_primes hQprime
  have hPdpf : (∏ p ∈ Q, p).primeFactors = Q := Nat.primeFactors_prod hQprime
  have hPddvd : (∏ p ∈ Q, p) ∣ P := by
    rw [← Nat.prod_primeFactors_of_squarefree hP]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hQsub
  ext e
  rw [mem_lowDiv, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨heP, hP0⟩, hlow⟩
    refine ⟨?_, hPdsq.ne_zero⟩
    have he0 : e ≠ 0 := by rintro rfl; exact hP0 (Nat.eq_zero_of_zero_dvd heP)
    have hsub : e.primeFactors ⊆ Q := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨Nat.primeFactors_mono heP hP.ne_zero hp, hlow p hp⟩
    calc e = ∏ p ∈ e.primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd heP)).symm
      _ ∣ ∏ p ∈ Q, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
  · rintro ⟨hdvd, _⟩
    refine ⟨⟨hdvd.trans hPddvd, hP.ne_zero⟩, ?_⟩
    intro p hp
    have := Nat.primeFactors_mono hdvd hPdsq.ne_zero hp
    rw [hPdpf] at this
    exact (Finset.mem_filter.mp this).2

/-- **`S^{(1)}(δ)` in closed form** (HB p.204): `ν_G` multiplicative gives
`S^{(1)}(δ) = ν_G(δ)·∏_{p ∣ P, p < p(δ)} (1 − ν_G(p))`.  Class **B**, cap 150.  Red-first:
`deltaSum` unfolds to a sum over `lowDiv P δ`; `lowDiv P δ` is the divisor set of the product
of the primes of `P` below `δ.minFac` (`mem_lowDiv`), so `sum_divisors_eq_sum_powerset` +
`nuG_isMultiplicative`, then the two lemmas `moebSum_nu_eq_W` itself uses
(`RosserDim4Instance.lean`): `Salt.BrunLower.sum_powerset_prod_neg_nu` and
`moebius_nu_prod_eq`.  True without `hPodd` (no division).  Consumer: `deltaSum_nuG_nonneg`,
`deltaSum_nuG_mul_additive`. -/
theorem deltaSum_nuG_eq (P : ℕ) (hP : Squarefree P) (δ : ℕ) (hδ : δ ∣ P) :
    deltaSum P δ (fun d => nuG d)
      = nuG δ * ∏ p ∈ P.primeFactors.filter (fun p => p < δ.minFac), (1 - nuG p) := by
  classical
  set Q := P.primeFactors.filter (fun p => p < δ.minFac) with hQ
  have hQprime : ∀ p ∈ Q, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hPdsq : Squarefree (∏ p ∈ Q, p) := squarefree_prod_of_primes hQprime
  have hPdpf : (∏ p ∈ Q, p).primeFactors = Q := Nat.primeFactors_prod hQprime
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hP.ne_zero (Nat.eq_zero_of_zero_dvd hδ)
  rw [deltaSum, lowDiv_eq_divisors hP, ← hQ,
    sum_divisors_eq_sum_powerset hPdsq (fun e => (μ e : ℝ) * nuG (δ * e)), hPdpf]
  have key : ∀ S ∈ Q.powerset, (μ (∏ p ∈ S, p) : ℝ) * nuG (δ * ∏ p ∈ S, p)
      = nuG δ * ∏ p ∈ S, (- nuG p) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hSprime : ∀ p ∈ S, p.Prime := fun p hp => hQprime p (hS hp)
    have hpf : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod hSprime
    have he0 : (∏ p ∈ S, p) ≠ 0 := (squarefree_prod_of_primes hSprime).ne_zero
    have hcop : Nat.Coprime δ (∏ p ∈ S, p) := by
      refine coprime_of_mem_lowDiv hδ0 he0 ?_
      intro p hp
      rw [hpf] at hp
      exact (Finset.mem_filter.mp (hS hp)).2
    rw [nuG_isMultiplicative.map_mul_of_coprime hcop, ← mul_assoc, mul_comm (μ (∏ p ∈ S, p) : ℝ),
      mul_assoc, moebius_nuG_prod_primes hSprime]
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Finset.prod_one_add]
  exact congrArg _ (Finset.prod_congr rfl fun p _ => by ring)

/-- **`S^{(1)}(δ) ≥ 0`** (HB p.204, "`0 ≤ G(p) ≤ p`").  Class **B**, cap 60.  Red-first:
`deltaSum_nuG_eq`, then `nuG_pos_of_prime`/`nuG_lt_one_of_prime` factorwise (`P` odd).
Consumer: `hb_transfer_additive`, `hb_transfer_sq_additive`, `lamSum_nuG_sub_W_bounds`. -/
theorem deltaSum_nuG_nonneg (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (δ : ℕ) (hδ : δ ∣ P) :
    0 ≤ deltaSum P δ (fun d => nuG d) := by
  classical
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hP.ne_zero (Nat.eq_zero_of_zero_dvd hδ)
  rw [deltaSum_nuG_eq P hP δ hδ]
  refine mul_nonneg ?_ (Finset.prod_nonneg fun p hp => ?_)
  · rw [nuG_apply hδ0]
    refine div_nonneg (Finset.prod_nonneg fun p hp => ?_) (Nat.cast_nonneg _)
    exact Gdens_nonneg (Nat.prime_of_mem_primeFactors hp).pos
  · have hpmem := (Finset.mem_filter.mp hp).1
    have := nuG_lt_one_of_prime (Nat.prime_of_mem_primeFactors hpmem) (hPodd p hpmem)
    linarith

/-- **The one-signedness of the FL defect at `ρ₁`.**  `S₁′⁺ − S₁ ≥ 0` and `S₁ − S₁′⁻ ≥ 0`, from
`mainSum_chi_eq_W_sub_correction` (`lamSum = W − (−1)^side·Σ_δ S^{(1)}(δ)`) and
`deltaSum_nuG_nonneg`.  Class **A**, cap 60.  Consumer: `hb_p200_upper`, `hb_p200_lower`
(it is what turns `|S₁′ − S₁|` into the FL defect of `hbSieve_fl_sandwich` (2)). -/
theorem lamSum_nuG_sub_W_bounds (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) {Lam z : ℝ} {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ lamSum Lam z 1 b P (fun d => nuG d) - W (hbSieve P hP hPodd)
      ∧ 0 ≤ W (hbSieve P hP hPodd) - lamSum Lam z 2 b P (fun d => nuG d) := by
  have hnn : ∀ (side : ℕ), 0 ≤ ∑ δ ∈ failSet Lam z side b P, deltaSum P δ (fun d => nuG d) :=
    fun side => Finset.sum_nonneg fun δ hδ =>
      deltaSum_nuG_nonneg P hP hPodd δ (mem_failSet.mp hδ).1.1
  have h1 := mainSum_chi_eq_W_sub_correction (hbSieve P hP hPodd)
    (Lam := Lam) (z := z) (side := 1) (b := b) hb (by norm_num)
  have h2 := mainSum_chi_eq_W_sub_correction (hbSieve P hP hPodd)
    (Lam := Lam) (z := z) (side := 2) (b := b) hb (by norm_num)
  simp only [hbSieve_prodPrimes, hbSieve_nu] at h1 h2
  norm_num at h1 h2
  exact ⟨by linarith [hnn 1], by linarith [hnn 2]⟩

/-- An additive function on the divisors of a squarefree `P` is the sum over the primes. -/
lemma additive_prod {P : ℕ} (hP : Squarefree P) {A : ℕ → ℝ} (hA : IsAdditiveOn P A) :
    ∀ {S : Finset ℕ}, S ⊆ P.primeFactors → A (∏ p ∈ S, p) = ∑ p ∈ S, A p := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simpa using hA.1
  | insert a S ha ih =>
    intro hS
    have haP : a ∈ P.primeFactors := hS (Finset.mem_insert_self a S)
    have hSP : S ⊆ P.primeFactors := fun x hx => hS (Finset.mem_insert_of_mem hx)
    have hap : a.Prime := Nat.prime_of_mem_primeFactors haP
    have hcop : Nat.Coprime a (∏ p ∈ S, p) := by
      refine Nat.Coprime.prod_right ?_
      intro p hp
      exact (Nat.coprime_primes hap (Nat.prime_of_mem_primeFactors (hSP hp))).mpr
        (fun h => ha (by rw [h]; exact hp))
    have hadvd : a ∣ P := Nat.dvd_of_mem_primeFactors haP
    have hSdvd : (∏ p ∈ S, p) ∣ P := by
      rw [← Nat.prod_primeFactors_of_squarefree hP]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hSP
    rw [Finset.prod_insert ha, Finset.sum_insert ha, hA.2 a _ hadvd hSdvd hcop, ih hSP]

/-- The subsets of `S` containing a fixed `p`, summed against `∏ f`. -/
lemma sum_powerset_filter_mem {S : Finset ℕ} (f : ℕ → ℝ) {p : ℕ} (hp : p ∈ S) :
    ∑ T ∈ S.powerset.filter (fun T => p ∈ T), ∏ r ∈ T, f r
      = f p * ∏ r ∈ S.erase p, (1 + f r) := by
  classical
  rw [Finset.prod_one_add, Finset.mul_sum]
  refine Finset.sum_nbij' (fun T => T.erase p) (fun U => insert p U) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    exact Finset.mem_powerset.mpr (Finset.erase_subset_erase p hT.1)
  · intro U hU
    rw [Finset.mem_powerset] at hU
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_insert_self p U⟩
    exact Finset.insert_subset hp (hU.trans (Finset.erase_subset p S))
  · intro T hT
    rw [Finset.mem_filter] at hT
    exact Finset.insert_erase hT.2
  · intro U hU
    rw [Finset.mem_powerset] at hU
    exact Finset.erase_insert (fun h => (Finset.mem_erase.mp (hU h)).1 rfl)
  · intro T hT
    rw [Finset.mem_filter] at hT
    exact (Finset.mul_prod_erase _ f hT.2).symm

/-- The off-diagonal swap: the additive twist against the signed density over a powerset. -/
lemma sum_powerset_prod_neg_nuG_mul_sum {Q : Finset ℕ} (A' : ℕ → ℝ)
    (hne : ∀ p ∈ Q, (1 : ℝ) - nuG p ≠ 0) :
    ∑ T ∈ Q.powerset, ((∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A' r))
      = - ((∏ p ∈ Q, (1 - nuG p)) * ∑ p ∈ Q, A' p * (nuG p / (1 - nuG p))) := by
  classical
  have h1 : ∀ T ∈ Q.powerset, ((∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A' r))
      = ∑ p ∈ Q, (if p ∈ T then A' p * ∏ r ∈ T, (- nuG r) else 0) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hT, ← Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ p ∈ Q, (∑ T ∈ Q.powerset, (if p ∈ T then A' p * ∏ r ∈ T, (- nuG r) else 0))
      = - ((∏ r ∈ Q, (1 - nuG r)) * (A' p * (nuG p / (1 - nuG p)))) := by
    intro p hp
    rw [← Finset.sum_filter, ← Finset.mul_sum, sum_powerset_filter_mem (fun r => - nuG r) hp]
    have hc : (1 : ℝ) - nuG p ≠ 0 := hne p hp
    have herase : ∏ r ∈ Q, (1 - nuG r)
        = (1 - nuG p) * ∏ r ∈ Q.erase p, (1 + - nuG r) := by
      rw [← Finset.mul_prod_erase Q (fun r => 1 - nuG r) hp]
      exact congrArg _ (Finset.prod_congr rfl fun r _ => by ring)
    rw [herase]
    field_simp
  rw [Finset.sum_congr rfl h2, Finset.mul_sum]
  exact Finset.sum_neg_distrib _

/-- **HB (3.6), the additive-twist fibre identity.**  For `A′` additive on `P`'s divisors,
`S^{(2)}(δ) = S^{(1)}(δ)·(A′(δ) − Σ_{p ∣ P, p < p(δ)} A′(p)·ν_G(p)/(1 − ν_G(p)))`.
**`hPodd` is load-bearing**: the identity divides by `1 − ν_G(p)`, and `ν_G(2) = 1` exactly
(HB p.205: "`P` is odd, and so `G(p) < p`"); v1 omitted it and was false at `P = 6`, `δ = 3`.
Class **C**, cap 300.  Red-first: on `lowDiv P δ` every `e` is coprime to `δ`, so
`ν_G(δe)A′(δe) = ν_G(δ)ν_G(e)(A′(δ) + A′(e))`; the `A′(δ)` part is `deltaSum_nuG_eq`; for the
`A′(e)` part write `A′(e) = Σ_{p ∣ e} A′(p)` (additivity + squarefree) and swap the sums:
`Σ_{e ∋ p} μ(e)ν_G(e) = −ν_G(p)·∏_{p′ ≠ p}(1 − ν_G(p′))`; `nuG_lt_one_of_prime` clears the
denominators.  Consumer: `deltaSum_nuG_mul_additive_le`. -/
theorem deltaSum_nuG_mul_additive (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ)
    (hA' : IsAdditiveOn P A') (δ : ℕ) (hδ : δ ∣ P) :
    deltaSum P δ (fun d => nuG d * A' d)
      = deltaSum P δ (fun d => nuG d)
          * (A' δ - ∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
              A' p * (nuG p / (1 - nuG p))) := by
  classical
  set Q := P.primeFactors.filter (fun p => p < δ.minFac) with hQ
  have hQprime : ∀ p ∈ Q, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hQsub : Q ⊆ P.primeFactors := Finset.filter_subset _ _
  have hPdsq : Squarefree (∏ p ∈ Q, p) := squarefree_prod_of_primes hQprime
  have hPdpf : (∏ p ∈ Q, p).primeFactors = Q := Nat.primeFactors_prod hQprime
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hP.ne_zero (Nat.eq_zero_of_zero_dvd hδ)
  have hne : ∀ p ∈ Q, (1 : ℝ) - nuG p ≠ 0 := fun p hp => by
    have := nuG_lt_one_of_prime (hQprime p hp) (hPodd p (hQsub hp)); linarith
  rw [deltaSum_nuG_eq P hP δ hδ, ← hQ, deltaSum, lowDiv_eq_divisors hP, ← hQ,
    sum_divisors_eq_sum_powerset hPdsq (fun e => (μ e : ℝ) * (nuG (δ * e) * A' (δ * e))),
    hPdpf]
  have key : ∀ T ∈ Q.powerset,
      (μ (∏ p ∈ T, p) : ℝ) * (nuG (δ * ∏ p ∈ T, p) * A' (δ * ∏ p ∈ T, p))
        = nuG δ * ((∏ r ∈ T, (- nuG r)) * (A' δ + ∑ r ∈ T, A' r)) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hTprime : ∀ p ∈ T, p.Prime := fun p hp => hQprime p (hT hp)
    have hpf : (∏ p ∈ T, p).primeFactors = T := Nat.primeFactors_prod hTprime
    have he0 : (∏ p ∈ T, p) ≠ 0 := (squarefree_prod_of_primes hTprime).ne_zero
    have hTsub : T ⊆ P.primeFactors := hT.trans hQsub
    have hedvd : (∏ p ∈ T, p) ∣ P := by
      rw [← Nat.prod_primeFactors_of_squarefree hP]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hTsub
    have hcop : Nat.Coprime δ (∏ p ∈ T, p) := by
      refine coprime_of_mem_lowDiv hδ0 he0 ?_
      intro p hp
      rw [hpf] at hp
      exact (Finset.mem_filter.mp (hT hp)).2
    rw [nuG_isMultiplicative.map_mul_of_coprime hcop, hA'.2 δ _ hδ hedvd hcop,
      additive_prod hP hA' hTsub, ← moebius_nuG_prod_primes hTprime]
    ring
  rw [Finset.sum_congr rfl key]
  -- split the two halves
  have hsplit : ∀ T ∈ Q.powerset,
      nuG δ * ((∏ r ∈ T, (- nuG r)) * (A' δ + ∑ r ∈ T, A' r))
        = nuG δ * A' δ * (∏ r ∈ T, (- nuG r))
          + nuG δ * ((∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A' r)) := by
    intro T _; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hW : ∑ T ∈ Q.powerset, ∏ r ∈ T, (- nuG r) = ∏ p ∈ Q, (1 - nuG p) := by
    rw [← Finset.prod_one_add]
    exact Finset.prod_congr rfl fun p _ => by ring
  have hswap := sum_powerset_prod_neg_nuG_mul_sum (Q := Q) A' hne
  rw [hW, hswap]
  ring

/-- `ν_G(p)/(1 − ν_G(p)) ≤ 20/p` at every odd prime (`= 2(2p−1)/((p−1)(p−2))`; the bound is
`16p² − 58p + 40 ≥ 0`, true from `p ≥ 3`, and at `p = 3` it reads `5 ≤ 20/3`). -/
lemma nuG_ratio_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    0 ≤ nuG p / (1 - nuG p) ∧ nuG p / (1 - nuG p) ≤ 20 / (p : ℝ) := by
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by
    have h2 := hp.two_le
    have h3' : 3 ≤ p := by omega
    exact_mod_cast h3'
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpos : 0 < nuG p := nuG_pos_of_prime hp
  have hlt : nuG p < 1 := nuG_lt_one_of_prime hp hp2
  have hnu : nuG p = 2 * (2 * (p : ℝ) - 1) / (((p : ℝ) + 1) * (p : ℝ)) := by
    rw [nuG_prime hp, Gdens]
    field_simp
  have hd : (0 : ℝ) < ((p : ℝ) + 1) * (p : ℝ) := by positivity
  have hkey : nuG p * (p : ℝ) + 20 * nuG p ≤ 20 := by
    rw [← sub_nonneg]
    have heq : (20 : ℝ) - (nuG p * (p : ℝ) + 20 * nuG p)
        = (16 * (p : ℝ) ^ 2 - 58 * (p : ℝ) + 40) / (((p : ℝ) + 1) * (p : ℝ)) := by
      rw [hnu]; field_simp; ring
    rw [heq]
    apply div_nonneg _ hd.le
    nlinarith [h3]
  refine ⟨div_nonneg hpos.le (by linarith), ?_⟩
  rw [div_le_div_iff₀ (by linarith) hp0]
  linarith

/-- **The Mertens-1 price of the `ν/(1−ν)` prime sum** (HB p.205): with `|A′(p)| ≤ B′ log p`
and every prime of `P` below `e^L`, `|Σ_{p∈Q} A′(p)ν_G(p)/(1−ν_G(p))| ≤ 20B′(L + log 4 + 4)`. -/
lemma abs_sum_nuG_ratio_le (P : ℕ) (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ)
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    {Q : Finset ℕ} (hQ : Q ⊆ P.primeFactors) :
    |∑ p ∈ Q, A' p * (nuG p / (1 - nuG p))| ≤ 20 * B' * (L + (Real.log 4 + 4)) := by
  classical
  set N := ⌊Real.exp L⌋₊ with hN
  have hexp1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp (by linarith)
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hexp1)
  have hNle : (N : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
  have hlogN : Real.log N ≤ L := by
    have : Real.log N ≤ Real.log (Real.exp L) :=
      Real.log_le_log (by exact_mod_cast hN1) hNle
    rwa [Real.log_exp] at this
  have hsub : Q ⊆ (Finset.range (N + 1)).filter Nat.Prime := by
    intro p hp
    have hpP := hQ hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpP
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hple : (p : ℝ) ≤ Real.exp L := by
      have := Real.exp_le_exp.mpr (hPL p hpP)
      rwa [Real.exp_log hp0] at this
    have hpN : p ≤ N := Nat.le_floor hple
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩
  have hterm : ∀ p ∈ Q, |A' p * (nuG p / (1 - nuG p))| ≤ 20 * B' * (Real.log p / p) := by
    intro p hp
    have hpP := hQ hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpP
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    obtain ⟨hr0, hr⟩ := nuG_ratio_le hpp (hPodd p hpP)
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [abs_mul, abs_of_nonneg hr0]
    calc |A' p| * (nuG p / (1 - nuG p)) ≤ (B' * Real.log p) * (20 / (p : ℝ)) :=
          mul_le_mul (hA'p p hpP) hr hr0 (by positivity)
      _ = 20 * B' * (Real.log p / p) := by ring
  have hmert : ∑ p ∈ Q, Real.log p / p ≤ Real.log N + (Real.log 4 + 4) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
      (Salt.Maynard.sum_log_div_prime_le hN1)
    intro p _ _
    rcases Nat.eq_zero_or_pos p with rfl | hpp
    · simp
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp)) (Nat.cast_nonneg p)
  calc |∑ p ∈ Q, A' p * (nuG p / (1 - nuG p))|
      ≤ ∑ p ∈ Q, |A' p * (nuG p / (1 - nuG p))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Q, 20 * B' * (Real.log p / p) := Finset.sum_le_sum hterm
    _ = 20 * B' * ∑ p ∈ Q, Real.log p / p := by rw [Finset.mul_sum]
    _ ≤ 20 * B' * (L + (Real.log 4 + 4)) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)


/-- **HB LEMMA 6 at `ρ₂ = ν_G·A′` — the per-δ domination, literal constant.**  With
`|A′(p)| ≤ B′·log p`, `log δ ≤ L`, every prime of `P` below `e^L` and `3 ≤ L`:
`|S^{(2)}(δ)| ≤ 64·B′·L·S^{(1)}(δ)`.  The `64`: `|A′(δ)| ≤ B′·L`; at `p = 3`,
`ν/(1−ν) = 5`; for `p ≥ 5`, `ν/(1−ν) ≤ 4/(p−4) ≤ 20/p`; Mertens' first theorem
(`sum_log_div_prime_le`: `Σ_{p ≤ N} log p/p ≤ log N + log 4 + 4`) gives
`≤ B′(L + 5.5 + 20(L + 5.4)) ≤ B′(21L + 114) ≤ 64·B′·L` at `L ≥ 3`.  Class **C**, cap 350.
Red-first: `deltaSum_nuG_mul_additive`, `abs_mul`, then the prime sum.  Consumer:
`hb_transfer_additive`. -/
theorem deltaSum_nuG_mul_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A')
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (δ : ℕ) (hδ : δ ∣ P) (hδL : Real.log δ ≤ L) :
    |deltaSum P δ (fun d => nuG d * A' d)| ≤ 64 * B' * L * deltaSum P δ (fun d => nuG d) := by
  classical
  have hnn := deltaSum_nuG_nonneg P hP hPodd δ hδ
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [h]; linarith [Real.log_two_lt_d9]
  have hδsq : Squarefree δ := hP.squarefree_of_dvd hδ
  have hδsub : δ.primeFactors ⊆ P.primeFactors := Nat.primeFactors_mono hδ hP.ne_zero
  have hAδeq : A' δ = ∑ p ∈ δ.primeFactors, A' p := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hδsq]
    exact additive_prod hP hA' hδsub
  have hlogsum : ∑ p ∈ δ.primeFactors, Real.log p = Real.log δ := by
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hδsq]
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hAδ : |A' δ| ≤ B' * L := by
    calc |A' δ| = |∑ p ∈ δ.primeFactors, A' p| := by rw [hAδeq]
      _ ≤ ∑ p ∈ δ.primeFactors, |A' p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ δ.primeFactors, B' * Real.log p :=
          Finset.sum_le_sum fun p hp => hA'p p (hδsub hp)
      _ = B' * Real.log δ := by rw [← Finset.mul_sum, hlogsum]
      _ ≤ B' * L := mul_le_mul_of_nonneg_left hδL hB'
  have hSig := abs_sum_nuG_ratio_le P hPodd A' hB' hA'p hL3 hPL
    (Q := P.primeFactors.filter (fun p => p < δ.minFac)) (Finset.filter_subset _ _)
  have hbnd : |A' δ - ∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
      A' p * (nuG p / (1 - nuG p))| ≤ 64 * B' * L := by
    have habs : |A' δ - ∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
        A' p * (nuG p / (1 - nuG p))|
        ≤ |A' δ| + |∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
            A' p * (nuG p / (1 - nuG p))| := by
      have := abs_add_le (A' δ) (-∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
        A' p * (nuG p / (1 - nuG p)))
      rwa [← sub_eq_add_neg, abs_neg] at this
    nlinarith [mul_nonneg hB' (show (0 : ℝ) ≤ 43 * L - 20 * Real.log 4 - 80 by linarith)]
  rw [deltaSum_nuG_mul_additive P hP hPodd A' hA' δ hδ, abs_mul, abs_of_nonneg hnn]
  calc deltaSum P δ (fun d => nuG d)
        * |A' δ - ∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
            A' p * (nuG p / (1 - nuG p))|
      ≤ deltaSum P δ (fun d => nuG d) * (64 * B' * L) := mul_le_mul_of_nonneg_left hbnd hnn
    _ = 64 * B' * L * deltaSum P δ (fun d => nuG d) := by ring

/-- The subsets of `S` containing two fixed distinct elements, summed against `∏ f`. -/
lemma sum_powerset_filter_mem₂ {S : Finset ℕ} (f : ℕ → ℝ) {p p' : ℕ}
    (hp : p ∈ S) (hp' : p' ∈ S) (hpp' : p ≠ p') :
    ∑ T ∈ S.powerset.filter (fun T => p ∈ T ∧ p' ∈ T), ∏ r ∈ T, f r
      = f p * f p' * ∏ r ∈ (S.erase p).erase p', (1 + f r) := by
  classical
  rw [Finset.prod_one_add, Finset.mul_sum]
  refine Finset.sum_nbij' (fun T => (T.erase p).erase p')
    (fun U => insert p (insert p' U)) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    exact Finset.mem_powerset.mpr
      (Finset.erase_subset_erase p' (Finset.erase_subset_erase p hT.1))
  · intro U hU
    rw [Finset.mem_powerset] at hU
    have hUS : U ⊆ S := hU.trans ((Finset.erase_subset p' _).trans (Finset.erase_subset p S))
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩
    · exact Finset.insert_subset hp (Finset.insert_subset hp' hUS)
    · exact Finset.mem_insert_self p _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self p' U)
  · intro T hT
    rw [Finset.mem_filter] at hT
    have hp'T : p' ∈ T.erase p := Finset.mem_erase.mpr ⟨(Ne.symm hpp'), hT.2.2⟩
    rw [Finset.insert_erase hp'T, Finset.insert_erase hT.2.1]
  · intro U hU
    rw [Finset.mem_powerset] at hU
    have hpU : p ∉ U := fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hU h))).1 rfl
    have hp'U : p' ∉ U := fun h => (Finset.mem_erase.mp (hU h)).1 rfl
    have h1 : p ∉ insert p' U := by
      simp only [Finset.mem_insert]
      rintro (h | h)
      · exact hpp' h
      · exact hpU h
    rw [Finset.erase_insert h1, Finset.erase_insert hp'U]
  · intro T hT
    rw [Finset.mem_filter] at hT
    have hp'T : p' ∈ T.erase p := Finset.mem_erase.mpr ⟨(Ne.symm hpp'), hT.2.2⟩
    rw [← Finset.mul_prod_erase _ f hT.2.1, ← Finset.mul_prod_erase _ f hp'T, mul_assoc]

/-- **The `A²` fibre identity** (HB (3.7)): the second moment of an additive twist against the
signed density over a powerset. -/
lemma sum_powerset_prod_neg_nuG_mul_sum_sq {Q : Finset ℕ} (A : ℕ → ℝ)
    (hne : ∀ p ∈ Q, (1 : ℝ) - nuG p ≠ 0) :
    ∑ T ∈ Q.powerset, ((∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A r) ^ 2)
      = (∏ p ∈ Q, (1 - nuG p))
        * ((∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
            - (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
            - ∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))) := by
  classical
  set W := ∏ p ∈ Q, (1 - nuG p) with hWdef
  have hWe : ∀ p ∈ Q, (∏ r ∈ Q.erase p, (1 + - nuG r)) = W / (1 - nuG p) := by
    intro p hp
    rw [eq_div_iff (hne p hp),
      show (∏ r ∈ Q.erase p, (1 + - nuG r)) = ∏ r ∈ Q.erase p, (1 - nuG r) from
        Finset.prod_congr rfl fun r _ => by ring, hWdef,
      ← Finset.mul_prod_erase Q (fun r => 1 - nuG r) hp]
    ring
  have hWe2 : ∀ p ∈ Q, ∀ p' ∈ Q, p ≠ p' →
      (∏ r ∈ (Q.erase p).erase p', (1 + - nuG r)) = W / ((1 - nuG p) * (1 - nuG p')) := by
    intro p hp p' hp' hpp'
    have hp'e : p' ∈ Q.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpp', hp'⟩
    rw [eq_div_iff (mul_ne_zero (hne p hp) (hne p' hp')),
      show (∏ r ∈ (Q.erase p).erase p', (1 + - nuG r))
          = ∏ r ∈ (Q.erase p).erase p', (1 - nuG r) from
        Finset.prod_congr rfl fun r _ => by ring, hWdef,
      ← Finset.mul_prod_erase Q (fun r => 1 - nuG r) hp,
      ← Finset.mul_prod_erase (Q.erase p) (fun r => 1 - nuG r) hp'e]
    ring
  have hcell : ∀ p ∈ Q, ∀ p' ∈ Q,
      (∑ T ∈ Q.powerset.filter (fun T => p ∈ T ∧ p' ∈ T), ∏ r ∈ T, (- nuG r))
        = W * ((nuG p / (1 - nuG p)) * (nuG p' / (1 - nuG p')))
          + (if p = p' then - (W * (nuG p / (1 - nuG p)))
                - W * (nuG p / (1 - nuG p)) ^ 2 else 0) := by
    intro p hp p' hp'
    by_cases h : p = p'
    · subst h
      have hc := hne p hp
      rw [if_pos rfl]
      have hfil : Q.powerset.filter (fun T => p ∈ T ∧ p ∈ T)
          = Q.powerset.filter (fun T => p ∈ T) := by
        simp only [and_self]
      rw [hfil, sum_powerset_filter_mem (fun r => - nuG r) hp, hWe p hp]
      field_simp
      ring
    · have hc := hne p hp
      have hc' := hne p' hp'
      rw [if_neg h, add_zero, sum_powerset_filter_mem₂ (fun r => - nuG r) hp hp' h,
        hWe2 p hp p' hp' h]
      field_simp
  have hexp : ∀ T ∈ Q.powerset, (∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A r) ^ 2
      = ∑ p ∈ Q, ∑ p' ∈ Q,
          (if p ∈ T ∧ p' ∈ T then A p * A p' * ∏ r ∈ T, (- nuG r) else 0) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have h2 : ∀ p : ℕ,
        (∑ p' ∈ Q, (if p ∈ T ∧ p' ∈ T then A p * A p' * ∏ r ∈ T, (- nuG r) else 0))
          = if p ∈ T then ∑ p' ∈ T, A p * A p' * ∏ r ∈ T, (- nuG r) else 0 := by
      intro p
      by_cases hpT : p ∈ T
      · simp only [hpT, true_and, if_true]
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hT]
      · simp [hpT]
    rw [Finset.sum_congr rfl (fun p _ => h2 p), Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hT, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p' _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hinner : ∀ p ∈ Q,
      (∑ T ∈ Q.powerset, ∑ p' ∈ Q,
          (if p ∈ T ∧ p' ∈ T then A p * A p' * ∏ r ∈ T, (- nuG r) else 0))
        = ∑ p' ∈ Q, (W * ((A p * (nuG p / (1 - nuG p))) * (A p' * (nuG p' / (1 - nuG p'))))
            + (if p = p' then A p ^ 2 * (- (W * (nuG p / (1 - nuG p)))
                  - W * (nuG p / (1 - nuG p)) ^ 2) else 0)) := by
    intro p hp
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' hp' => ?_
    rw [← Finset.sum_filter, ← Finset.mul_sum, hcell p hp p' hp']
    by_cases h : p = p'
    · subst h; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [Finset.sum_congr rfl hinner]
  have hfinal : ∀ p ∈ Q,
      (∑ p' ∈ Q, (W * ((A p * (nuG p / (1 - nuG p))) * (A p' * (nuG p' / (1 - nuG p'))))
          + (if p = p' then A p ^ 2 * (- (W * (nuG p / (1 - nuG p)))
                - W * (nuG p / (1 - nuG p)) ^ 2) else 0)))
        = W * ((A p * (nuG p / (1 - nuG p))) * ∑ p' ∈ Q, A p' * (nuG p' / (1 - nuG p')))
          + A p ^ 2 * (- (W * (nuG p / (1 - nuG p)))
              - W * (nuG p / (1 - nuG p)) ^ 2) := by
    intro p hp
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum, Finset.mul_sum]
    · rw [Finset.sum_ite_eq Q p (fun _ => A p ^ 2 * (- (W * (nuG p / (1 - nuG p)))
          - W * (nuG p / (1 - nuG p)) ^ 2)), if_pos hp]
  rw [Finset.sum_congr rfl hfinal, Finset.sum_add_distrib]
  have e1 : (∑ p ∈ Q, W * ((A p * (nuG p / (1 - nuG p)))
        * ∑ p' ∈ Q, A p' * (nuG p' / (1 - nuG p'))))
      = W * (∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2 := by
    rw [show ∀ x : ℝ, W * x ^ 2 = (W * x) * x from fun x => by ring, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have e2 : (∑ p ∈ Q, A p ^ 2 * (- (W * (nuG p / (1 - nuG p)))
        - W * (nuG p / (1 - nuG p)) ^ 2))
      = - (W * ((∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
          + ∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e1, e2]
  ring

/-- HB p.205's `|A′(δ) − Σ_{p<p(δ)} A′(p)ν/(1−ν)| ≤ 64B′L` — the bracket of (3.6) at `L ≥ 3`. -/
lemma abs_A_sub_sum_ratio_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A')
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (δ : ℕ) (hδ : δ ∣ P) (hδL : Real.log δ ≤ L) :
    |A' δ - ∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
        A' p * (nuG p / (1 - nuG p))| ≤ 64 * B' * L := by
  classical
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [h]; linarith [Real.log_two_lt_d9]
  have hδsq : Squarefree δ := hP.squarefree_of_dvd hδ
  have hδsub : δ.primeFactors ⊆ P.primeFactors := Nat.primeFactors_mono hδ hP.ne_zero
  have hAδeq : A' δ = ∑ p ∈ δ.primeFactors, A' p := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hδsq]
    exact additive_prod hP hA' hδsub
  have hlogsum : ∑ p ∈ δ.primeFactors, Real.log p = Real.log δ := by
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hδsq]
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hAδ : |A' δ| ≤ B' * L := by
    calc |A' δ| = |∑ p ∈ δ.primeFactors, A' p| := by rw [hAδeq]
      _ ≤ ∑ p ∈ δ.primeFactors, |A' p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ δ.primeFactors, B' * Real.log p :=
          Finset.sum_le_sum fun p hp => hA'p p (hδsub hp)
      _ = B' * Real.log δ := by rw [← Finset.mul_sum, hlogsum]
      _ ≤ B' * L := mul_le_mul_of_nonneg_left hδL hB'
  have hSig := abs_sum_nuG_ratio_le P hPodd A' hB' hA'p hL3 hPL
    (Q := P.primeFactors.filter (fun p => p < δ.minFac)) (Finset.filter_subset _ _)
  have habs : |A' δ - ∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
      A' p * (nuG p / (1 - nuG p))|
      ≤ |A' δ| + |∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
          A' p * (nuG p / (1 - nuG p))| := by
    have := abs_add_le (A' δ) (-∑ p ∈ P.primeFactors.filter (fun p => p < δ.minFac),
      A' p * (nuG p / (1 - nuG p)))
    rwa [← sub_eq_add_neg, abs_neg] at this
  nlinarith [mul_nonneg hB' (show (0 : ℝ) ≤ 43 * L - 20 * Real.log 4 - 80 by linarith)]

/-- `|A(p)²| ≤ CA²·L·log p` and `|A(p)²·ν/(1−ν)| ≤ (20/3)CA²L·log p` — the two twisted
weights the `A²` grade feeds to `abs_sum_nuG_ratio_le`. -/
lemma sq_weight_bounds (P : ℕ) (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A : ℕ → ℝ)
    {CA L : ℝ} (_hCA : 0 ≤ CA) (hAp : ∀ p ∈ P.primeFactors, |A p| ≤ CA * Real.log p)
    (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L) :
    (∀ p ∈ P.primeFactors, |A p ^ 2| ≤ (CA ^ 2 * L) * Real.log p)
      ∧ (∀ p ∈ P.primeFactors, |A p ^ 2 * (nuG p / (1 - nuG p))|
          ≤ ((20 / 3) * (CA ^ 2 * L)) * Real.log p) := by
  have hsq : ∀ p ∈ P.primeFactors, |A p ^ 2| ≤ (CA ^ 2 * L) * Real.log p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h1 := hAp p hp
    have h2 := hPL p hp
    have habs : |A p ^ 2| = |A p| ^ 2 := by rw [← sq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [habs]
    calc |A p| ^ 2 ≤ (CA * Real.log p) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = CA ^ 2 * Real.log p * Real.log p := by ring
      _ ≤ CA ^ 2 * L * Real.log p := by
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg CA) hlog0) (sub_nonneg.mpr h2)]
  refine ⟨hsq, fun p hp => ?_⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    have h2 := hpp.two_le
    have h3 : 3 ≤ p := by have := hPodd p hp; omega
    exact_mod_cast h3
  obtain ⟨hr0, hr⟩ := nuG_ratio_le hpp (hPodd p hp)
  have hrle : nuG p / (1 - nuG p) ≤ 20 / 3 := by
    refine le_trans hr ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have hL0 : (0 : ℝ) ≤ L := le_trans hlog0 (hPL p hp)
  rw [abs_mul, abs_of_nonneg hr0]
  calc |A p ^ 2| * (nuG p / (1 - nuG p)) ≤ ((CA ^ 2 * L) * Real.log p) * (20 / 3) :=
        mul_le_mul (hsq p hp) hrle hr0
          (mul_nonneg (mul_nonneg (sq_nonneg CA) hL0) hlog0)
    _ = ((20 / 3) * (CA ^ 2 * L)) * Real.log p := by ring

/-- **HB LEMMA 6 at `ρ₃ = ν_G·A²` — the per-δ domination, literal constant** (HB (3.7)–(3.8),
the `L²` grade — sharper than his stated `BL`, as his p.206 remark notes).  Split
`A(δe)² = A(δ)² + 2A(δ)A(e) + A(e)²` and `A(e)² = Σ_{p∣e}A(p)² + Σ_{p≠p′∣e}A(p)A(p′)`; the
diagonal is additive with `A(p)² ≤ CA²·L·log p`, the off-diagonal expands to
`∏(1−ν)·Σ_{p≠p′} A(p)A(p′)·[ν/(1−ν)](p)[ν/(1−ν)](p′) ≤ ∏(1−ν)·(Σ_p |A(p)|ν/(1−ν))²`.  Totals
`≤ CA²(461L² + 4902L + 12996)·S^{(1)}(δ) ≤ (128·CA·L)²·S^{(1)}(δ)` at `L ≥ 3`.  Class **C**,
cap 500.  Consumer: `hb_transfer_sq_additive`. -/
theorem deltaSum_nuG_mul_sq_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A : ℕ → ℝ) (hA : IsAdditiveOn P A)
    {CA L : ℝ} (hCA : 0 ≤ CA) (hAp : ∀ p ∈ P.primeFactors, |A p| ≤ CA * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (δ : ℕ) (hδ : δ ∣ P) (hδL : Real.log δ ≤ L) :
    |deltaSum P δ (fun d => nuG d * A d ^ 2)|
      ≤ (128 * CA * L) ^ 2 * deltaSum P δ (fun d => nuG d) := by
  classical
  set Q := P.primeFactors.filter (fun p => p < δ.minFac) with hQ
  have hQprime : ∀ p ∈ Q, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hQsub : Q ⊆ P.primeFactors := Finset.filter_subset _ _
  have hPdsq : Squarefree (∏ p ∈ Q, p) := squarefree_prod_of_primes hQprime
  have hPdpf : (∏ p ∈ Q, p).primeFactors = Q := Nat.primeFactors_prod hQprime
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hP.ne_zero (Nat.eq_zero_of_zero_dvd hδ)
  have hne : ∀ p ∈ Q, (1 : ℝ) - nuG p ≠ 0 := fun p hp => by
    have := nuG_lt_one_of_prime (hQprime p hp) (hPodd p (hQsub hp)); linarith
  have hW : ∑ T ∈ Q.powerset, ∏ r ∈ T, (- nuG r) = ∏ p ∈ Q, (1 - nuG p) := by
    rw [← Finset.prod_one_add]
    exact Finset.prod_congr rfl fun p _ => by ring
  -- (1) the fibre identity
  have hid : deltaSum P δ (fun d => nuG d * A d ^ 2)
      = deltaSum P δ (fun d => nuG d)
        * ((A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
            - (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
            - ∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))) := by
    rw [deltaSum, lowDiv_eq_divisors hP, ← hQ,
      sum_divisors_eq_sum_powerset hPdsq
        (fun e => (μ e : ℝ) * (nuG (δ * e) * A (δ * e) ^ 2)), hPdpf]
    have key : ∀ T ∈ Q.powerset,
        (μ (∏ p ∈ T, p) : ℝ) * (nuG (δ * ∏ p ∈ T, p) * A (δ * ∏ p ∈ T, p) ^ 2)
          = nuG δ * ((∏ r ∈ T, (- nuG r)) * (A δ + ∑ r ∈ T, A r) ^ 2) := by
      intro T hT
      rw [Finset.mem_powerset] at hT
      have hTprime : ∀ p ∈ T, p.Prime := fun p hp => hQprime p (hT hp)
      have hpf : (∏ p ∈ T, p).primeFactors = T := Nat.primeFactors_prod hTprime
      have he0 : (∏ p ∈ T, p) ≠ 0 := (squarefree_prod_of_primes hTprime).ne_zero
      have hTsub : T ⊆ P.primeFactors := hT.trans hQsub
      have hedvd : (∏ p ∈ T, p) ∣ P := by
        rw [← Nat.prod_primeFactors_of_squarefree hP]
        exact Finset.prod_dvd_prod_of_subset _ _ _ hTsub
      have hcop : Nat.Coprime δ (∏ p ∈ T, p) := by
        refine coprime_of_mem_lowDiv hδ0 he0 ?_
        intro p hp
        rw [hpf] at hp
        exact (Finset.mem_filter.mp (hT hp)).2
      rw [nuG_isMultiplicative.map_mul_of_coprime hcop, hA.2 δ _ hδ hedvd hcop,
        additive_prod hP hA hTsub, ← moebius_nuG_prod_primes hTprime]
      ring
    rw [Finset.sum_congr rfl key]
    have hsplit : ∀ T ∈ Q.powerset,
        nuG δ * ((∏ r ∈ T, (- nuG r)) * (A δ + ∑ r ∈ T, A r) ^ 2)
          = nuG δ * A δ ^ 2 * (∏ r ∈ T, (- nuG r))
            + 2 * (nuG δ * A δ) * ((∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A r))
            + nuG δ * ((∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A r) ^ 2) := fun T _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hW,
      sum_powerset_prod_neg_nuG_mul_sum A hne, sum_powerset_prod_neg_nuG_mul_sum_sq A hne,
      deltaSum_nuG_eq P hP δ hδ, ← hQ]
    ring
  -- (2) the three bounds
  have hnn := deltaSum_nuG_nonneg P hP hPodd δ hδ
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [h]; linarith [Real.log_two_lt_d9]
  have hb1 := abs_A_sub_sum_ratio_le P hP hPodd A hA hCA hAp hL3 hPL δ hδ hδL
  obtain ⟨hsq1, hsq2⟩ := sq_weight_bounds P hPodd A hCA hAp hPL
  have hCAL : (0 : ℝ) ≤ CA ^ 2 * L := mul_nonneg (sq_nonneg CA) (by linarith)
  have hb2 := abs_sum_nuG_ratio_le P hPodd (fun p => A p ^ 2)
    hCAL hsq1 hL3 hPL (Q := Q) hQsub
  have hb3 := abs_sum_nuG_ratio_le P hPodd (fun p => A p ^ 2 * (nuG p / (1 - nuG p)))
    (by linarith : (0:ℝ) ≤ (20 / 3) * (CA ^ 2 * L)) hsq2 hL3 hPL (Q := Q) hQsub
  have hb3' : |∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2|
      ≤ 20 * (20 / 3 * (CA ^ 2 * L)) * (L + (Real.log 4 + 4)) := by
    rw [show (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
        = ∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) * (nuG p / (1 - nuG p)) from
      Finset.sum_congr rfl fun p _ => by ring]
    exact hb3
  have hbr : |(A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
      - (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
      - ∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))| ≤ (128 * CA * L) ^ 2 := by
    have hsqle : (A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2 ≤ (64 * CA * L) ^ 2 := by
      have := abs_nonneg (A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p)))
      nlinarith [sq_abs (A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p)))]
    have hsq0 : 0 ≤ (A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2 := sq_nonneg _
    have habs : |(A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
        - (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
        - ∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))|
        ≤ (A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
          + |∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2|
          + |∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))| := by
      calc |(A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
              - (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
              - ∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))|
          ≤ |(A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
              - (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)|
            + |∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))| := by
              have := abs_add_le ((A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
                  - (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2))
                (-∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)))
              rwa [← sub_eq_add_neg, abs_neg] at this
        _ ≤ ((A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
              + |∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2|)
            + |∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))| := by
              have h2 := abs_add_le ((A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2)
                (-∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
              rw [← sub_eq_add_neg, abs_neg] at h2
              rw [abs_of_nonneg hsq0] at h2
              linarith
    have hLpos : (0 : ℝ) < L := by linarith
    have hCA2 : (0 : ℝ) ≤ CA ^ 2 := sq_nonneg CA
    nlinarith [mul_nonneg (mul_nonneg hCA2 hLpos.le)
        (show (0 : ℝ) ≤ 2.8 * L - (L + (Real.log 4 + 4)) by linarith),
      mul_nonneg hCA2 (sq_nonneg L)]
  rw [hid, abs_mul, abs_of_nonneg hnn]
  calc deltaSum P δ (fun d => nuG d)
        * |(A δ - ∑ p ∈ Q, A p * (nuG p / (1 - nuG p))) ^ 2
            - (∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
            - ∑ p ∈ Q, A p ^ 2 * (nuG p / (1 - nuG p))|
      ≤ deltaSum P δ (fun d => nuG d) * (128 * CA * L) ^ 2 :=
        mul_le_mul_of_nonneg_left hbr hnn
    _ = (128 * CA * L) ^ 2 * deltaSum P δ (fun d => nuG d) := by ring

/-- **HB Lemma 6, the δ-free sums `S₂ ≪ BL·S₁`, identity form.**  `moebSum P (ν_G·A′)
= −W·Σ_{p ∣ P} A′(p)ν_G(p)/(1 − ν_G(p))` (the `δ = 1`, `p(δ) = ∞` case of (3.6) — note
`deltaSum P 1` is NOT `moebSum P`, since `lowDiv P 1 = {1}`; hence a separate row).
Class **B**, cap 200.  Red-first: as `deltaSum_nuG_mul_additive` over `P.divisors` with
`moebSum_nu_eq_W`.  Consumer: `moebSum_nuG_mul_additive_le`. -/
theorem moebSum_nuG_mul_additive (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A') :
    moebSum P (fun d => nuG d * A' d)
      = - W (hbSieve P hP hPodd) * ∑ p ∈ P.primeFactors, A' p * (nuG p / (1 - nuG p)) := by
  classical
  have hne : ∀ p ∈ P.primeFactors, (1 : ℝ) - nuG p ≠ 0 := fun p hp => by
    have := nuG_lt_one_of_prime (Nat.prime_of_mem_primeFactors hp) (hPodd p hp); linarith
  have hW : W (hbSieve P hP hPodd) = ∏ p ∈ P.primeFactors, (1 - nuG p) := rfl
  rw [moebSum, sum_divisors_eq_sum_powerset hP (fun d => (μ d : ℝ) * (nuG d * A' d))]
  have key : ∀ T ∈ P.primeFactors.powerset,
      (μ (∏ p ∈ T, p) : ℝ) * (nuG (∏ p ∈ T, p) * A' (∏ p ∈ T, p))
        = (∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A' r) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hTprime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
    rw [additive_prod hP hA' hT, ← mul_assoc, moebius_nuG_prod_primes hTprime]
  rw [Finset.sum_congr rfl key, sum_powerset_prod_neg_nuG_mul_sum A' hne, hW]
  ring

/-- **`|S₂| ≤ 64·B′·L·S₁`.**  Class **B**, cap 150 (the prime sum of
`deltaSum_nuG_mul_additive_le` without the `A′(δ)` term; `moebSum P ν_G = W > 0` by
`moebSum_nu_eq_W`, `W_pos`).  Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem moebSum_nuG_mul_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A')
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L) :
    |moebSum P (fun d => nuG d * A' d)| ≤ 64 * B' * L * moebSum P (fun d => nuG d) := by
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [h]; linarith [Real.log_two_lt_d9]
  have hW : moebSum P (fun d => nuG d) = W (hbSieve P hP hPodd) := by
    have h := moebSum_nu_eq_W (hbSieve P hP hPodd)
    simpa [hbSieve_prodPrimes, hbSieve_nu] using h
  have hWpos : 0 < W (hbSieve P hP hPodd) := W_pos _
  have hSig := abs_sum_nuG_ratio_le P hPodd A' hB' hA'p hL3 hPL
    (Q := P.primeFactors) Finset.Subset.rfl
  rw [moebSum_nuG_mul_additive P hP hPodd A' hA', hW, abs_mul, abs_neg, abs_of_pos hWpos]
  calc W (hbSieve P hP hPodd) * |∑ p ∈ P.primeFactors, A' p * (nuG p / (1 - nuG p))|
      ≤ W (hbSieve P hP hPodd) * (20 * B' * (L + (Real.log 4 + 4))) :=
        mul_le_mul_of_nonneg_left hSig hWpos.le
    _ ≤ 64 * B' * L * W (hbSieve P hP hPodd) := by
        nlinarith [mul_nonneg (mul_nonneg hWpos.le hB')
          (show (0 : ℝ) ≤ 44 * L - 20 * Real.log 4 - 80 by linarith)]

/-- **`|S₃| ≤ (128·CA·L)²·S₁`.**  Class **C**, cap 300 (the off-diagonal expansion of
`deltaSum_nuG_mul_sq_additive_le` over `P.divisors`).  Consumer: `hb_p200_upper`,
`hb_p200_lower`. -/
theorem moebSum_nuG_mul_sq_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A : ℕ → ℝ) (hA : IsAdditiveOn P A)
    {CA L : ℝ} (hCA : 0 ≤ CA) (hAp : ∀ p ∈ P.primeFactors, |A p| ≤ CA * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L) :
    |moebSum P (fun d => nuG d * A d ^ 2)|
      ≤ (128 * CA * L) ^ 2 * moebSum P (fun d => nuG d) := by
  classical
  have hne : ∀ p ∈ P.primeFactors, (1 : ℝ) - nuG p ≠ 0 := fun p hp => by
    have := nuG_lt_one_of_prime (Nat.prime_of_mem_primeFactors hp) (hPodd p hp); linarith
  have hWprod : W (hbSieve P hP hPodd) = ∏ p ∈ P.primeFactors, (1 - nuG p) := rfl
  have hWpos : (0 : ℝ) < ∏ p ∈ P.primeFactors, (1 - nuG p) := hWprod ▸ W_pos _
  have hWeq : moebSum P (fun d => nuG d) = ∏ p ∈ P.primeFactors, (1 - nuG p) := by
    have h := moebSum_nu_eq_W (hbSieve P hP hPodd)
    rw [hWprod] at h
    simpa [hbSieve_prodPrimes, hbSieve_nu] using h
  have hid : moebSum P (fun d => nuG d * A d ^ 2)
      = (∏ p ∈ P.primeFactors, (1 - nuG p))
        * ((∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
            - (∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
            - ∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))) := by
    rw [moebSum, sum_divisors_eq_sum_powerset hP (fun d => (μ d : ℝ) * (nuG d * A d ^ 2))]
    have key : ∀ T ∈ P.primeFactors.powerset,
        (μ (∏ p ∈ T, p) : ℝ) * (nuG (∏ p ∈ T, p) * A (∏ p ∈ T, p) ^ 2)
          = (∏ r ∈ T, (- nuG r)) * (∑ r ∈ T, A r) ^ 2 := by
      intro T hT
      rw [Finset.mem_powerset] at hT
      have hTprime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
      rw [additive_prod hP hA hT, ← mul_assoc, moebius_nuG_prod_primes hTprime]
    rw [Finset.sum_congr rfl key, sum_powerset_prod_neg_nuG_mul_sum_sq A hne]
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [h]; linarith [Real.log_two_lt_d9]
  have hlog40 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hCAL : (0 : ℝ) ≤ CA ^ 2 * L := mul_nonneg (sq_nonneg CA) (by linarith)
  have hCAL2 : (0 : ℝ) ≤ CA ^ 2 * L ^ 2 := mul_nonneg (sq_nonneg CA) (sq_nonneg L)
  have h28 : (0 : ℝ) ≤ 2.8 * L - (L + (Real.log 4 + 4)) := by linarith
  obtain ⟨hsq1, hsq2⟩ := sq_weight_bounds P hPodd A hCA hAp hPL
  have hS1 := abs_sum_nuG_ratio_le P hPodd A hCA hAp hL3 hPL
    (Q := P.primeFactors) Finset.Subset.rfl
  have hb2 := abs_sum_nuG_ratio_le P hPodd (fun p => A p ^ 2) hCAL hsq1 hL3 hPL
    (Q := P.primeFactors) Finset.Subset.rfl
  have hb3 := abs_sum_nuG_ratio_le P hPodd (fun p => A p ^ 2 * (nuG p / (1 - nuG p)))
    (by linarith : (0 : ℝ) ≤ (20 / 3) * (CA ^ 2 * L)) hsq2 hL3 hPL
    (Q := P.primeFactors) Finset.Subset.rfl
  have hb3' : |∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2|
      ≤ 20 * (20 / 3 * (CA ^ 2 * L)) * (L + (Real.log 4 + 4)) := by
    rw [show (∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
        = ∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) * (nuG p / (1 - nuG p)) from
      Finset.sum_congr rfl fun p _ => by ring]
    exact hb3
  have e1 : (∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
      ≤ 3136 * (CA ^ 2 * L ^ 2) := by
    have h1 : |∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))| ≤ 56 * (CA * L) := by
      refine le_trans hS1 ?_
      nlinarith [mul_nonneg hCA h28]
    have h2 : (0 : ℝ) ≤ 56 * (CA * L) := le_trans (abs_nonneg _) h1
    nlinarith [sq_abs (∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))), abs_nonneg
      (∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p)))]
  have e2 : |∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))|
      ≤ 56 * (CA ^ 2 * L ^ 2) := by
    refine le_trans hb2 ?_
    nlinarith [mul_nonneg hCAL h28]
  have e3 : |∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2|
      ≤ 374 * (CA ^ 2 * L ^ 2) := by
    refine le_trans hb3' ?_
    nlinarith [mul_nonneg hCAL h28]
  have hbr : |(∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
      - (∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
      - ∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))| ≤ (128 * CA * L) ^ 2 := by
    have hsq0 : (0 : ℝ) ≤ (∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2 :=
      sq_nonneg _
    have habs : |(∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
        - (∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
        - ∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))|
        ≤ (∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
          + |∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2|
          + |∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))| := by
      calc |(∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
              - (∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
              - ∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))|
          ≤ |(∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
              - (∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)|
            + |∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))| := by
              have := abs_add_le ((∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
                  - (∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2))
                (-∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)))
              rwa [← sub_eq_add_neg, abs_neg] at this
        _ ≤ ((∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
              + |∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2|)
            + |∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))| := by
              have h2 := abs_add_le ((∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2)
                (-∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
              rw [← sub_eq_add_neg, abs_neg] at h2
              rw [abs_of_nonneg hsq0] at h2
              linarith
    nlinarith [hCAL2]
  rw [hid, hWeq, abs_mul, abs_of_pos hWpos]
  calc (∏ p ∈ P.primeFactors, (1 - nuG p))
        * |(∑ p ∈ P.primeFactors, A p * (nuG p / (1 - nuG p))) ^ 2
            - (∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p)) ^ 2)
            - ∑ p ∈ P.primeFactors, A p ^ 2 * (nuG p / (1 - nuG p))|
      ≤ (∏ p ∈ P.primeFactors, (1 - nuG p)) * (128 * CA * L) ^ 2 :=
        mul_le_mul_of_nonneg_left hbr hWpos.le
    _ = (128 * CA * L) ^ 2 * ∏ p ∈ P.primeFactors, (1 - nuG p) := by ring

/-- **HB's "`δ ≤ q`" at the block-Brun weights** (p.199: "to obtain the bound `δ ≤ q` we need
the sieving limit `β ≥ 3`"; here the level bound does it).  A first-failure `δ` has `δ/p(δ)`
passing `χ_ν`, so `δ/p(δ) ≤ z^{sRatio}` (`flB_level_bound`) and `p(δ) < z`; hence
`log δ ≤ (sRatio + 1)·log z`.  Class **B**, cap 120.  Consumer: `hb_transfer_additive`,
`hb_transfer_sq_additive` (their `hδL`), and `hb_p200_*` via `3·sRatio·log z ≤ L`. -/
theorem failSet_log_le (P : ℕ) (hP : Squarefree P) {Lam z sRatio : ℝ} {side : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hside : 1 ≤ side) (hs : levelE Lam ≤ sRatio)
    (hPz : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    ∀ δ ∈ failSet Lam z side (flB sRatio Lam) P,
      Real.log δ ≤ (sRatio + 1) * Real.log z := by
  intro δ hδ
  obtain ⟨⟨hδP, hP0⟩, hnot, hchi⟩ := mem_failSet.mp hδ
  have hδ0 : δ ≠ 0 := failSet_ne_zero hδ
  have hδsq : Squarefree δ := hP.squarefree_of_dvd hδP
  have hz0 : (0 : ℝ) < z := by linarith
  set p := δ.minFac with hpdef
  have hpdvd : p ∣ δ := Nat.minFac_dvd δ
  have hddvd : δ / p ∣ δ := Nat.div_dvd_of_dvd hpdvd
  have hd0 : δ / p ≠ 0 := by
    intro h
    have := Nat.div_mul_cancel hpdvd
    rw [h, zero_mul] at this
    exact hδ0 this.symm
  have hdsq : Squarefree (δ / p) := hδsq.squarefree_of_dvd hddvd
  have hdz : ∀ r ∈ (δ / p).primeFactors, (r : ℝ) < z := by
    intro r hr
    exact hPz r (Nat.primeFactors_mono ((hddvd.trans hδP)) hP.ne_zero hr)
  have hlev := flB_level_bound hLam hz hside hs hd0 hdsq hdz hchi
  have hpz : (p : ℝ) < z := by
    rcases eq_or_ne δ 1 with rfl | hδ1
    · simp only [hpdef, Nat.minFac_one, Nat.cast_one]; linarith
    · have hpp : p.Prime := Nat.minFac_prime hδ1
      exact hPz p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hδP, hP.ne_zero⟩)
  have hcast : (δ : ℝ) = ((δ / p : ℕ) : ℝ) * (p : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hpdvd]
  have hzpow : (0 : ℝ) < z ^ sRatio := Real.rpow_pos_of_pos hz0 sRatio
  have hle : (δ : ℝ) ≤ z ^ (sRatio + 1) := by
    rw [hcast, Real.rpow_add hz0, Real.rpow_one]
    exact mul_le_mul hlev hpz.le (Nat.cast_nonneg p) hzpow.le
  have hδpos : (0 : ℝ) < (δ : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hδ0
  calc Real.log δ ≤ Real.log (z ^ (sRatio + 1)) := Real.log_le_log hδpos hle
    _ = (sRatio + 1) * Real.log z := Real.log_rpow hz0 _

/-- **The per-δ transfer at `ρ₂`** — `hb_transfer` fed Lemma 6.  Class **A**, cap 60.
Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem hb_transfer_additive (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) {Lam z : ℝ} {side b : ℕ}
    (hb : 1 ≤ b) (hside : side ≤ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A')
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (hfailL : ∀ δ ∈ failSet Lam z side b P, Real.log δ ≤ L) :
    |lamSum Lam z side b P (fun d => nuG d * A' d) - moebSum P (fun d => nuG d * A' d)|
      ≤ 64 * B' * L
          * |lamSum Lam z side b P (fun d => nuG d) - moebSum P (fun d => nuG d)| :=
  hb_transfer P hP hb hside (fun d => nuG d * A' d) (64 * B' * L)
    (fun δ hδ => deltaSum_nuG_nonneg P hP hPodd δ (mem_failSet.mp hδ).1.1)
    (fun δ hδ => deltaSum_nuG_mul_additive_le P hP hPodd A' hA' hB' hA'p hL3 hPL δ
      (mem_failSet.mp hδ).1.1 (hfailL δ hδ))

/-- **The per-δ transfer at `ρ₃`** — `hb_transfer` fed Lemma 6.  Class **A**, cap 60.
Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem hb_transfer_sq_additive (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) {Lam z : ℝ} {side b : ℕ}
    (hb : 1 ≤ b) (hside : side ≤ 2) (A : ℕ → ℝ) (hA : IsAdditiveOn P A)
    {CA L : ℝ} (hCA : 0 ≤ CA) (hAp : ∀ p ∈ P.primeFactors, |A p| ≤ CA * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L)
    (hfailL : ∀ δ ∈ failSet Lam z side b P, Real.log δ ≤ L) :
    |lamSum Lam z side b P (fun d => nuG d * A d ^ 2) - moebSum P (fun d => nuG d * A d ^ 2)|
      ≤ (128 * CA * L) ^ 2
          * |lamSum Lam z side b P (fun d => nuG d) - moebSum P (fun d => nuG d)| :=
  hb_transfer P hP hb hside (fun d => nuG d * A d ^ 2) ((128 * CA * L) ^ 2)
    (fun δ hδ => deltaSum_nuG_nonneg P hP hPodd δ (mem_failSet.mp hδ).1.1)
    (fun δ hδ => deltaSum_nuG_mul_sq_additive_le P hP hPodd A hA hCA hAp hL3 hPL δ
      (mem_failSet.mp hδ).1.1 (hfailL δ hδ))

/-! ## §6 — HB Lemma 5 as an INTERFACE (N7's exit) and the p.200 assembly -/

/-- **HB LEMMA 5, AS THE INTERFACE N7 FILLS AND N8 CONSUMES** (p.199; the Wave C scout's §1
says "write the exit to the consumer at `RosserDim4Instance.lean:558`, not invented" — this
is that consumer, made explicit).  For a sieve situation `H` (in practice `hbDataN8 …`):

    S(d) = κ·(G(d)/d)·{LL² + A(d)² + A′(d) + C₀} + O(x·L⁴·z⁻¹·d⁻¹·4^{ω(d)})

for `d ∣ P`, `(d, α) = 1`, `d ≤ q^{1/3}` (spelled `d³ ≤ e^L`, `L = log q`), with `A, A′`
additive on `P`'s divisors, `|A(p)| ≤ CA·log p`, `|A′(p)| ≤ CA′·B·log p`, `|C₀| ≤ CC·B·L`,
`B = L + |LL|`, `LL = L′(1,χ)/L(1,χ)` (a free real here; N9 identifies it with N4's `(L1)`
terminal).  Every `≪` of the paper is a literal parameter: **Wave C-2 (row C2-10) must print
`CA CA' CC Cerr`, nonnegative** (the three `_nonneg` fields are v2's: the Lemma-6 rows demand
them and the prime-wise bounds cannot supply them when `hbP = 1`), and the `x` is produced by
the `t`-integration (scout §5), never carried.
Producer: Wave C-2 at `H := hbDataN8 χ hsq hz x`.  Consumers: `hb_p200_upper`, `hb_p200_lower`. -/
structure Lemma5Eval (H : HBSieveData) (α : ℕ) (x L LL kappa C₀ Cerr CA CA' CC : ℝ)
    (A A' : ℕ → ℝ) : Prop where
  CA_nonneg : 0 ≤ CA
  CA'_nonneg : 0 ≤ CA'
  Cerr_nonneg : 0 ≤ Cerr
  A_add : IsAdditiveOn H.P A
  A'_add : IsAdditiveOn H.P A'
  A_prime : ∀ p ∈ H.P.primeFactors, |A p| ≤ CA * Real.log p
  A'_prime : ∀ p ∈ H.P.primeFactors, |A' p| ≤ CA' * (L + |LL|) * Real.log p
  C₀_le : |C₀| ≤ CC * (L + |LL|) * L
  eval : ∀ d ∈ H.P.divisors, Nat.Coprime d α → (d : ℝ) ^ 3 ≤ Real.exp L →
    |H.S d - kappa * (hbG α d / d) * (LL ^ 2 + A d ^ 2 + A' d + C₀)|
      ≤ Cerr * x * L ^ 4 / (H.z * d) * (4 : ℝ) ^ d.primeFactors.card

/-- **`G(d)/d = ν_G(d)` off `α`.**  `hbG α d = 2^{ω(d)}∏(2p−1)/(p+1) = ∏_{p∣d} G(p) = ω_G(d)`
when `(d, α) = 1`.  Class **A**, cap 60.  Red-first: `Finset.prod_mul_distrib` +
`Finset.prod_const` against `omegaG`/`Gdens`.  Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem hbG_div_eq_nuG {α d : ℕ} (hd : d ≠ 0) (hdα : Nat.Coprime d α) :
    hbG α d / (d : ℝ) = nuG d := by
  rw [nuG_apply hd, hbG, if_pos hdα, omegaG]
  congr 1
  rw [show (∏ p ∈ d.primeFactors, Gdens p)
      = ∏ p ∈ d.primeFactors, (2 * ((2 * (p : ℝ) - 1) / ((p : ℝ) + 1))) from
    Finset.prod_congr rfl fun p _ => by rw [Gdens]; ring,
    Finset.prod_mul_distrib, Finset.prod_const]

/-- **The (2.3) error sum** `Σ_{d ∣ P} 4^{ω(d)}/d` — a definition, so the p.200 rows carry it
by name and `n8ErrSum_le` prices it once. -/
noncomputable def n8ErrSum (P : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, (4 : ℝ) ^ d.primeFactors.card / (d : ℝ)

/-- **Mertens' second constant, explicit** — the `C` of `sum_inv_prime_le_aux`
(`Salt/Maynard/Mertens.lean`): `Σ_{p ≤ n} 1/p ≤ log log n + mertens2C` for `n ≥ 2`. -/
noncomputable def mertens2C : ℝ :=
  1 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)

/-- **HB (2.3): `Σ_{d∣P} 4^{ω(d)}/d ≪ L⁴`.**  `= ∏_{p ∣ P}(1 + 4/p) ≤ exp(4·Σ_{p<z} 1/p)
≤ exp(4·(log log z + mertens2C)) = e^{4·mertens2C}·(log z)⁴`.  Class **B**, cap 200.
Red-first: `sum_divisors_eq_sum_powerset` + `Finset.prod_add`-shape for the product identity,
`Real.add_one_le_exp` factorwise, `sum_inv_prime_le_aux`.  Consumer: **N9** (the p.200 rows
carry `n8ErrSum P` by name; N9 prices it here, through its `log z ≤ L`). -/
theorem n8ErrSum_le (P : ℕ) (hP : Squarefree P) {z : ℕ} (hz : 2 ≤ z)
    (hPz : ∀ p ∈ P.primeFactors, p ≤ z) :
    n8ErrSum P ≤ Real.exp (4 * mertens2C) * Real.log z ^ 4 := by
  classical
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hprod : n8ErrSum P = ∏ p ∈ P.primeFactors, (1 + 4 / (p : ℝ)) := by
    rw [n8ErrSum,
      sum_divisors_eq_sum_powerset hP (fun d => (4 : ℝ) ^ d.primeFactors.card / (d : ℝ)),
      Finset.prod_one_add]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    have hTprime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hT hp)
    rw [Nat.primeFactors_prod hTprime, Nat.cast_prod, ← Finset.prod_const,
      ← Finset.prod_div_distrib]
  have hstep2 : ∏ p ∈ P.primeFactors, (1 + 4 / (p : ℝ))
      ≤ Real.exp (∑ p ∈ P.primeFactors, 4 / (p : ℝ)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have hp0 : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      positivity
    · have := Real.add_one_le_exp (4 / (p : ℝ))
      linarith
  have hsub : P.primeFactors ⊆ (Finset.range (z + 1)).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hPz p hp; omega),
      Nat.prime_of_mem_primeFactors hp⟩
  have hstep3 : ∑ p ∈ P.primeFactors, 4 / (p : ℝ)
      ≤ 4 * (Real.log (Real.log z) + mertens2C) := by
    have hinv : ∑ p ∈ P.primeFactors, (1 : ℝ) / (p : ℝ)
        ≤ Real.log (Real.log z) + mertens2C := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
        (Salt.Maynard.sum_inv_prime_le_aux hz)
      intro p _ _
      positivity
    have heq : ∑ p ∈ P.primeFactors, 4 / (p : ℝ)
        = 4 * ∑ p ∈ P.primeFactors, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [heq]
    linarith
  have h4 : Real.exp (4 * (Real.log (Real.log z) + mertens2C))
      = Real.exp (4 * mertens2C) * Real.log z ^ 4 := by
    rw [show (4 : ℝ) * (Real.log (Real.log z) + mertens2C)
        = 4 * mertens2C + (Real.log (Real.log z) + (Real.log (Real.log z)
            + (Real.log (Real.log z) + Real.log (Real.log z)))) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hlogz]
    ring
  calc n8ErrSum P = ∏ p ∈ P.primeFactors, (1 + 4 / (p : ℝ)) := hprod
    _ ≤ Real.exp (∑ p ∈ P.primeFactors, 4 / (p : ℝ)) := hstep2
    _ ≤ Real.exp (4 * (Real.log (Real.log z) + mertens2C)) := Real.exp_le_exp.mpr hstep3
    _ = Real.exp (4 * mertens2C) * Real.log z ^ 4 := h4

/-- **The N8 Lemma-6 constant**: `64·CA′ + (128·CA)² + CC` — the sum of the three
per-density constants, so that `S₂ + S₃ + C₀S₁ ≤ n8C6·B·L·S₁` (using `L² ≤ B·L`). -/
noncomputable def n8C6 (CA CA' CC : ℝ) : ℝ := 64 * CA' + (128 * CA) ^ 2 + CC

/-- **HB p.200, THE UPPER ASSEMBLY.**  From the sandwich (2.2) at the N8 wire, Lemma 5 as the
interface `Lemma5Eval`, Lemma 6 (§5), the FL defect (`hbSieve_fl_sandwich` (2), side 1:
`S₁′⁺ ≤ W(1 + λ·C·e^{−cs})`, `C = flConst λ Λ₄`, `c = flRate λ`) and the per-δ transfers:

    S⁽³⁾ ≤ κ·W·(1 + λCe^{−cs})·(LL² + n8C6·B·L) + Cerr·x·L⁴·z⁻¹·n8ErrSum P.

HB's form `κS₁{(L′/L)² + O(BL) + O(B²e^{−z₀/4})} + O(xL⁸z⁻¹)` is this at `S₁ = W`
(`hbS1_eq_W`), `LL² ≤ B²`, and `n8ErrSum ≤ e^{4·mertens2C}L⁴` (`n8ErrSum_le`).
Hypotheses: the sieve's operating packet (`hlam hlam' hzt hs`), HB's `D = q^{1/3}` as
`3·sRatio·log z ≤ L` (so every kept `d` has `d³ ≤ e^L` by `flB_level_bound`, and every
first-failure `δ` has `log δ ≤ L` by `failSet_log_le`), `κ ≥ 0`, and `(P, α) = 1` (true at
the twin instance `α = 4`: `P` is odd).  The sign guards `0 ≤ CA, CA′, Cerr` are
`Lemma5Eval`'s fields.
Class **C**, cap 600.  **Red-first, the preamble (four landed facts, ~40 ln, before any
algebra):** `Lam4_pos hlam hlam' hzt` gives `0 < Λ₄`; `levelE Λ = 2e^Λ/(e^Λ − 1) > 2` for
`Λ > 0` (two lines from the definition, `RosserDim4FL.lean`; `levelE_pos` gives only `> 0`),
so `sRatio > 2` and `hD` gives `log z ≤ L/6`; `hPL : log p ≤ L` for `p ∣ P` from
`HBSieveData.P_lt_z`; `hδL : log δ ≤ L` on the fail set from `failSet_log_le` and
`(sRatio + 1)·log z ≤ L/3 + L/6`.  **Then the algebra:** `Σ_d λ⁺_d S(d) = κ Σ_d λ⁺_d
ν_G(d)(LL² + A² + A′ + C₀) + Σ_d λ⁺_d e_d` with `|e_d| ≤ Cerr·x·L⁴/(z·d)·4^{ω(d)}` and
`|λ_d| ≤ 1`; the main sum is `κ(LL²·S₁′ + S₃′ + S₂′ + C₀·S₁′)`; bound `S₂′ ≤ |S₂| + |S₂′ − S₂|`
by `moebSum_nuG_mul_additive_le` + `hb_transfer_additive` + `lamSum_nuG_sub_W_bounds`; same
for `S₃′`.  Consumer: **N9** (`hb_theorem1`, with `kappa := hbKappa χ α x (hbL1 χ z)` and
`LL` from N4's `(L1)`). -/
theorem hb_p200_upper (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz : 2 ≤ z) {lam sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hzt : zThresh lam ≤ (z : ℝ)) (hs : levelE (Lam4 lam (z : ℝ)) ≤ sRatio)
    {α : ℕ} {L LL kappa C₀ Cerr CA CA' CC : ℝ} {A A' : ℕ → ℝ}
    (hL3 : 3 ≤ L) (hD : 3 * sRatio * Real.log z ≤ L)
    (hPα : Nat.Coprime (hbDataN8 χ hsq hz x).P α) (hκ : 0 ≤ kappa)
    (hL5 : Lemma5Eval (hbDataN8 χ hsq hz x) α x L LL kappa C₀ Cerr CA CA' CC A A') :
    S3 χ z (l2cWindow χ z x)
      ≤ kappa * W (hbDataN8 χ hsq hz x).sieve
          * (1 + lam * flConst lam (Lam4 lam (z : ℝ)) * Real.exp (-(flRate lam) * sRatio))
          * (LL ^ 2 + n8C6 CA CA' CC * (L + |LL|) * L)
        + Cerr * x * L ^ 4 / (z : ℝ) * n8ErrSum (hbDataN8 χ hsq hz x).P := by
  sorry

/-- **HB p.200, THE LOWER ASSEMBLY** ("an analogous argument shows
`S⁽³⁾ ≥ x𝔖C(α) + O(xe^{−z₀/4})`").  Side 2 of the sandwich with the FL lower endpoint
`W(1 − C·e^{−cs}) ≤ S₁′⁻ ≤ W`:

    S⁽³⁾ ≥ κ·W·(LL²·(1 − Ce^{−cs}) − n8C6·B·L·(1 + Ce^{−cs})) − Cerr·x·L⁴·z⁻¹·n8ErrSum P.

Same hypotheses and route as `hb_p200_upper` (the same preamble); class **C**, cap 400 (the
mirror, once the upper's bookkeeping lemmas exist).  ⚠ For N9, not for the executor: at the
sieve's own threshold `sRatio = levelE Λ₄` the FL factor `flConst·e^{−flRate·sRatio}` is the
Λ-free constant `2e^{2λ}/(1 − λ²e^{2+2λ}) ≈ 13.82` at `λ = 1/4`, so the bracket is negative
and the statement, though true, says nothing; it is non-vacuous once
`sRatio ≥ levelE Λ₄ + log(13.82)/log 4 ≈ levelE Λ₄ + 1.9`, which N9's `s = z₀/3` supplies
for free but its `hb_theorem1` must CARRY.  Consumer: **N9** (`hb_theorem1` — THIS is the
sign the door consumes: a LOWER bound on `S⁽³⁾`, hence on `S1 (Ioc x (2x))` through
`hb_lemma4_l2cWindow`, is what `twinPrimeConjecture_of_frequently_S1` needs). -/
theorem hb_p200_lower (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z x : ℕ}
    (hz : 2 ≤ z) {lam sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hzt : zThresh lam ≤ (z : ℝ)) (hs : levelE (Lam4 lam (z : ℝ)) ≤ sRatio)
    {α : ℕ} {L LL kappa C₀ Cerr CA CA' CC : ℝ} {A A' : ℕ → ℝ}
    (hL3 : 3 ≤ L) (hD : 3 * sRatio * Real.log z ≤ L)
    (hPα : Nat.Coprime (hbDataN8 χ hsq hz x).P α) (hκ : 0 ≤ kappa)
    (hL5 : Lemma5Eval (hbDataN8 χ hsq hz x) α x L LL kappa C₀ Cerr CA CA' CC A A') :
    kappa * W (hbDataN8 χ hsq hz x).sieve
        * (LL ^ 2 * (1 - flConst lam (Lam4 lam (z : ℝ)) * Real.exp (-(flRate lam) * sRatio))
            - n8C6 CA CA' CC * (L + |LL|) * L
                * (1 + flConst lam (Lam4 lam (z : ℝ)) * Real.exp (-(flRate lam) * sRatio)))
      - Cerr * x * L ^ 4 / (z : ℝ) * n8ErrSum (hbDataN8 χ hsq hz x).P
      ≤ S3 χ z (l2cWindow χ z x) := by
  sorry

/-! ## §7 — the `κS₁` wire: HB's `S₁` (p.207, N4's object) IS the sieve's `W` -/

/-- **`S₁ = W`.**  N4's `(L2)` terminal (`hb_L2_at_split_point_charTrio`) evaluates
`hbKappa · hbS1 χ α z`, where `hbS1` is the product over primes `p ≤ ⌊z⌋`, `χ_ℝ(p) = 1`,
`p ∤ α` of `(p−1)(p−2)/(p(p+1))`; the sieve's `W` is the product over `2 < p < z`,
`χ_ℝ(p) = 1` of `1 − G(p)/p`.  At an integer `z` the index sets agree at `hbS1`'s argument
`z − 1` once `p ∤ α ↔ 2 < p` on primes (`2 ∣ α` and every odd prime is prime to `α` — true at
the twin instance `α = 4`), and the factors agree by `one_sub_hbG_div_eq`.  Class **B**,
cap 200.  Red-first: `hbSiftSet_chiReChar` + `Finset.prod_congr` after an `ext` on the two
filters.  Consumer: **N9** (composes N4's `κS₁ = (1+δ)x𝔖C(α)/(ηL)²` into `hb_p200_*`'s
`kappa · W`; N4's row takes a FREE real `z`, so N9 instantiates it at `(z:ℝ) − 1`). -/
theorem hbS1_eq_W (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) {α : ℕ} (hα2 : 2 ∣ α) (hαodd : ∀ p : ℕ, p.Prime → p ∣ α → p = 2) :
    hbS1 χ α ((z : ℝ) - 1) = W (hbDataN8 χ hsq hz x).sieve := by
  classical
  have hWeq : W (hbDataN8 χ hsq hz x).sieve
      = ∏ p ∈ (hbP (chiReChar χ hsq) (z : ℝ)).primeFactors, (1 - nuG p) := rfl
  have hzc : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ z)]
    ring
  have hfloor : ⌊(z : ℝ) - 1⌋₊ + 1 = z := by
    rw [← hzc, Nat.floor_natCast]
    omega
  rw [hWeq, hbP_primeFactors, hbSiftSet_chiReChar, hbS1, hfloor]
  have hfil : (Finset.range z).filter
        (fun p => Nat.Prime p ∧ Salt.TwinBar.chiRe χ p = 1 ∧ ¬ (p ∣ α))
      = (Finset.range z).filter
        (fun p => p.Prime ∧ 2 < p ∧ Salt.TwinBar.chiRe χ p = 1) := by
    refine Finset.filter_congr fun p _ => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h2⟩
      have hp2 : p ≠ 2 := by rintro rfl; exact h3 hα2
      have := h1.two_le
      omega
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h3, fun hd => ?_⟩
      have := hαodd p h1 hd
      omega
  rw [hfil]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hpp, hp2, _⟩ := hp
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
  rw [nuG_prime hpp, Gdens]
  field_simp
  ring

end Salt.HB
