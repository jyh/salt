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
  sorry

/-- **`S^{(1)}(δ) ≥ 0`** (HB p.204, "`0 ≤ G(p) ≤ p`").  Class **B**, cap 60.  Red-first:
`deltaSum_nuG_eq`, then `nuG_pos_of_prime`/`nuG_lt_one_of_prime` factorwise (`P` odd).
Consumer: `hb_transfer_additive`, `hb_transfer_sq_additive`, `lamSum_nuG_sub_W_bounds`. -/
theorem deltaSum_nuG_nonneg (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (δ : ℕ) (hδ : δ ∣ P) :
    0 ≤ deltaSum P δ (fun d => nuG d) := by
  sorry

/-- **The one-signedness of the FL defect at `ρ₁`.**  `S₁′⁺ − S₁ ≥ 0` and `S₁ − S₁′⁻ ≥ 0`, from
`mainSum_chi_eq_W_sub_correction` (`lamSum = W − (−1)^side·Σ_δ S^{(1)}(δ)`) and
`deltaSum_nuG_nonneg`.  Class **A**, cap 60.  Consumer: `hb_p200_upper`, `hb_p200_lower`
(it is what turns `|S₁′ − S₁|` into the FL defect of `hbSieve_fl_sandwich` (2)). -/
theorem lamSum_nuG_sub_W_bounds (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) {Lam z : ℝ} {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ lamSum Lam z 1 b P (fun d => nuG d) - W (hbSieve P hP hPodd)
      ∧ 0 ≤ W (hbSieve P hP hPodd) - lamSum Lam z 2 b P (fun d => nuG d) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **HB Lemma 6, the δ-free sums `S₂ ≪ BL·S₁`, identity form.**  `moebSum P (ν_G·A′)
= −W·Σ_{p ∣ P} A′(p)ν_G(p)/(1 − ν_G(p))` (the `δ = 1`, `p(δ) = ∞` case of (3.6) — note
`deltaSum P 1` is NOT `moebSum P`, since `lowDiv P 1 = {1}`; hence a separate row).
Class **B**, cap 200.  Red-first: as `deltaSum_nuG_mul_additive` over `P.divisors` with
`moebSum_nu_eq_W`.  Consumer: `moebSum_nuG_mul_additive_le`. -/
theorem moebSum_nuG_mul_additive (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A') :
    moebSum P (fun d => nuG d * A' d)
      = - W (hbSieve P hP hPodd) * ∑ p ∈ P.primeFactors, A' p * (nuG p / (1 - nuG p)) := by
  sorry

/-- **`|S₂| ≤ 64·B′·L·S₁`.**  Class **B**, cap 150 (the prime sum of
`deltaSum_nuG_mul_additive_le` without the `A′(δ)` term; `moebSum P ν_G = W > 0` by
`moebSum_nu_eq_W`, `W_pos`).  Consumer: `hb_p200_upper`, `hb_p200_lower`. -/
theorem moebSum_nuG_mul_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A' : ℕ → ℝ) (hA' : IsAdditiveOn P A')
    {B' L : ℝ} (hB' : 0 ≤ B') (hA'p : ∀ p ∈ P.primeFactors, |A' p| ≤ B' * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L) :
    |moebSum P (fun d => nuG d * A' d)| ≤ 64 * B' * L * moebSum P (fun d => nuG d) := by
  sorry

/-- **`|S₃| ≤ (128·CA·L)²·S₁`.**  Class **C**, cap 300 (the off-diagonal expansion of
`deltaSum_nuG_mul_sq_additive_le` over `P.divisors`).  Consumer: `hb_p200_upper`,
`hb_p200_lower`. -/
theorem moebSum_nuG_mul_sq_additive_le (P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, p ≠ 2) (A : ℕ → ℝ) (hA : IsAdditiveOn P A)
    {CA L : ℝ} (hCA : 0 ≤ CA) (hAp : ∀ p ∈ P.primeFactors, |A p| ≤ CA * Real.log p)
    (hL3 : 3 ≤ L) (hPL : ∀ p ∈ P.primeFactors, Real.log p ≤ L) :
    |moebSum P (fun d => nuG d * A d ^ 2)|
      ≤ (128 * CA * L) ^ 2 * moebSum P (fun d => nuG d) := by
  sorry

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
  sorry

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
          * |lamSum Lam z side b P (fun d => nuG d) - moebSum P (fun d => nuG d)| := by
  sorry

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
          * |lamSum Lam z side b P (fun d => nuG d) - moebSum P (fun d => nuG d)| := by
  sorry

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
  sorry

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
  sorry

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
  sorry

end Salt.HB
