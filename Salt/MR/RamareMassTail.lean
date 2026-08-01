/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MobiusChiRamare
import Salt.MR.CofactorDist
import Salt.MR.TypicalDensity
import Salt.MR.SeamCalibrationK

/-!
# ⟦O6, the two owed carrier pages⟧ — THE WINDOW MASS and THE RANKIN TAIL (node D3)

`Salt/MR/MobiusChiRamare.lean` (the landed O6 carrier) states its two window rows as NAMED
IN-STATEMENT HYPOTHESES and says so twice — its header (`:78–83`, "**That Euler-product
evaluation is NOT performed here** … it is named as the consumer's route") and
`MmuGrChi_rate`'s docstring (`:659–660`, "It is stated, not proved, here").  This file performs
both, at `r = 0` (which by the carrier's own `ramTailWeight_le_zero_param` is the worst case, so
every bound here is `r`-UNIFORM on `[0,1]`):

* **THE MASS PAGE (§2)** — `∑_{b ≤ z} w_r(b)/b ≤ windowMassConst P Q`, the Euler-product
  evaluation `∏_{P≤p≤Q}(1−1/p)^{−1}` composed with the LANDED Mertens window constant
  `Salt.MR.blockWindow_mertens_const` (`CofactorDist.lean:139`).  The value is
  `exp(c·(loglog Q − loglog P + 25)) = e^{25c}·(log Q/log P)^c` with `c = 1 + 1/(P−1)`
  (`windowMassConst_eq_ratio_rpow`) — the freeze's `≍ log Q/log P` shape, `H`-free, `z`-free
  and `y`-free.  At the door windows it is `≈ e^{25}·M` (`ramTailWeight_mass_door`).

* **THE RANKIN-TAIL PAGE (§3)** — `∑_{z < b ≤ y} w_r(b)/b ≤ z^{−σ}·windowRankinConst P Q σ`
  at every `σ ∈ (0, 1/2]`, the shifted-Euler/Rankin bound with
  `windowRankinConst P Q σ = exp(2·Q^σ·(loglog Q − loglog P + 25))`; the consumer picks `σ`.
  Calibrated at `σ = 2A·loglog y/log z` it delivers `(log y)^{−2A}` times the window constant
  (`ramTailWeight_tail_calibrated`), and at `z = ⌊√y⌋` it delivers the carrier's hypothesis
  VERBATIM — `≤ 1/(log y)^A` (`ramTailWeight_htail_door`).

Both pages carry their gates IN-STATEMENT (nothing absorbed, no `O(·)`, no hidden threshold).

## The engine (§1), and why it is one engine

Both rows are the same object at two exponents.  `w_0` is the `[P,Q]`-smooth indicator
(`ramTailWeight_zero_param`), so the mass is `∑_{b ≤ z, b smooth} b^{−1}` and — after the
Rankin shift `1/b ≤ z^{−σ}·b^{−(1−σ)}` for `b > z` — the tail is
`z^{−σ}·∑_{b ≤ y, b smooth} b^{−(1−σ)}`.  §1 bounds BOTH by the finite Euler product

  `∑_{b ≤ z, b [P,Q]-smooth} b^{−u} ≤ ∏_{P≤p≤Q} (1 − p^{−u})^{−1}`   (`windowSmooth_rpow_sum_le`)

for every `u > 0`.  The route is the DIVISOR DOMINATION: a window-smooth `b ≤ z` divides
`N = ∏_{P≤p≤Q} p^z` (its exponents are `< b ≤ z` by `Nat.factorization_lt`), so the sum is at
most `∑_{d ∣ N} d^{−u} = (ζ ∗ n^{−u})(N)`, which is multiplicative and factors over the band
into geometric series `∑_{j≤z} p^{−ju} ≤ (1 − p^{−u})^{−1}`.  No smooth-number counting, no
tsum over an infinite support: the whole page is finite Finset algebra plus one geometric
majorant.

## The four log scales, kept strictly apart

* `log y` — the statement scale of the carrier's rows (only §3's calibration reads it);
* `log z` — the split scale (`z = ⌊√y⌋` at the door, where `log z ≥ (log y)/4` by the LANDED
  `Salt.TwinBar.log_natSqrt_ge`); the Rankin exponent is `σ = 2A·loglog y/log z`;
* `loglog y` — the calibration scale (it is what `(log y)^{−2A}` is made of);
* `log Q/log P` — the WINDOW scale, the ONLY place `P,Q` enter the constants.
  The `o(1)` of the Rankin page is exactly the coupling `σ·log Q = 2A·loglog y·log Q/log z`
  between the last two, and it rides as the named gate `hgateO1` — never absorbed.
  (At the door windows `log P₁ = Adoor M·log 2`, `log Q₁ = M·Adoor M·log 2`
  — `SeamCalibration.calE_one`, `SeamCalibrationK.log_calQK` — so the gate is
  `8A·loglog y·M·Adoor M·log 2 ≤ log y`, free by an astronomical margin at the door tower.)

## What is NOT here (stated, so nothing is silently given up)

* The tail page is Rankin at a CONSTANT `σ ≤ 1/2`, i.e. the crude shift; no `σ → 0`
  optimisation and no `A!`-genre log-moment variant (the carrier header's alternative device).
  The delivered decay `(log y)^{−2A}` is twice the demanded `(log y)^{−A}`, and the surplus
  exponent is what pays the window constant through `hgateWin` — that is the whole design.
* `windowMassConst`/`windowRankinConst` use the Mertens window bound with its explicit `+25`
  (`blockWindow_mertens_const`); the sharper `−logloglog` gain of `CofactorDist`'s honest page
  is discarded, as there.
* The composition of these two pages INTO `MmuGrChi_rate` (i.e. an eventual-in-`y` statement at
  a fixed window) is the consumer's step (D3-DISCHARGE): both gates of §3 are `y`-dependent, and
  the carrier's `∃C', x₀` is uniform in `P,Q`, so the composition changes the quantifier order.
  Nothing here presumes it.
-/

open scoped BigOperators

namespace Salt.MR

/-! ## §0 — the two landed inputs, re-cut for this file

`primeBand P Q` (`TypicalDensity.lean:74`) is the band `{p prime : P ≤ p ≤ Q}`;
`blockWindowPrimes P Q X` (`RamWeight.lean:240`) is the same band truncated at `X`.  At `X = Q`
the truncation is vacuous, which is how the LANDED `blockWindow_mertens_const` becomes the
window sum this file needs. -/

/-- The band `{p prime : P ≤ p ≤ Q}` is the `X = Q` block window (the truncation is vacuous). -/
lemma primeBand_eq_blockWindowPrimes (P Q : ℕ) :
    primeBand P Q = blockWindowPrimes P Q (Q : ℝ) := by
  ext p
  rw [primeBand, blockWindowPrimes, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_range, Nat.floor_natCast]
  constructor
  · rintro ⟨⟨hPp, hpQ⟩, hp⟩; exact ⟨⟨by omega, hp⟩, hPp, hpQ⟩
  · rintro ⟨⟨-, hp⟩, hPp, hpQ⟩; exact ⟨⟨hPp, hpQ⟩, hp⟩

/-- **THE MERTENS WINDOW INPUT.**  `∑_{P≤p≤Q} 1/p ≤ loglog Q − loglog P + 25` — the LANDED
`blockWindow_mertens_const` (`CofactorDist.lean:139`) at `X = Q`. -/
theorem sum_inv_primeBand_le (P Q : ℕ) (hP : Real.exp 1 ≤ (P : ℝ)) (hPQ : P ≤ Q) :
    ∑ p ∈ primeBand P Q, (1 : ℝ) / (p : ℝ)
      ≤ Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25 := by
  rw [primeBand_eq_blockWindowPrimes]
  exact blockWindow_mertens_const P Q (Q : ℝ) hP hPQ

/-- `∑_{P≤p≤Q} 1/p ≥ 0` and the Mertens majorant is therefore nonnegative — used whenever the
window constant's exponent must be multiplied by a nonnegative factor. -/
lemma mertens_window_nonneg (P Q : ℕ) (hP : 4 ≤ P) (hPQ : P ≤ Q) :
    (0 : ℝ) ≤ Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25 := by
  have hP1 : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos hP1
  have : Real.log (Real.log (P : ℝ)) ≤ Real.log (Real.log (Q : ℝ)) :=
    Real.log_le_log hlogP (Real.log_le_log (by linarith) hPQR)
  linarith

/-- A finite geometric sum is at most `(1−r)⁻¹`. -/
private lemma geom_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  have hsum := Summable.sum_le_tsum (f := fun i : ℕ => r ^ i) (Finset.range n)
    (fun i _ => pow_nonneg hr0 i) (summable_geometric_of_lt_one hr0 hr1)
  rwa [tsum_geometric_of_lt_one hr0 hr1] at hsum

/-- Every local factor `(1 − p^{−u})⁻¹` is positive (`p ≥ 2`, `u > 0`). -/
lemma one_sub_rpow_inv_pos {p : ℕ} (hp : 2 ≤ p) {u : ℝ} (hu : 0 < u) :
    0 < (1 - (p : ℝ) ^ (-u))⁻¹ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have : (p : ℝ) ^ (-u) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  exact inv_pos.mpr (by linarith)

/-! ## §1 — THE ENGINE: the window-smooth `b^{−u}` mass, by divisor domination -/

/-- The completely multiplicative weight `n ↦ n^{−u}` (as an `ArithmeticFunction ℝ`; the value
at `0` is `0`). -/
noncomputable def invRpow (u : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ (-u), by simp⟩

@[simp] lemma invRpow_apply (u : ℝ) (n : ℕ) :
    invRpow u n = if n = 0 then 0 else (n : ℝ) ^ (-u) := rfl

lemma invRpow_apply_of {u : ℝ} {n : ℕ} (hn : n ≠ 0) : invRpow u n = (n : ℝ) ^ (-u) := by
  simp [hn]

lemma invRpow_nonneg (u : ℝ) (n : ℕ) : 0 ≤ invRpow u n := by
  rw [invRpow_apply]
  split_ifs
  · exact le_refl 0
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

lemma invRpow_isMultiplicative (u : ℝ) : (invRpow u).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [invRpow_apply], ?_⟩
  intro m n hm hn _
  rw [invRpow_apply_of hm, invRpow_apply_of hn, invRpow_apply_of (Nat.mul_ne_zero hm hn)]
  push_cast
  exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- The divisor sum `n ↦ ∑_{d ∣ n} d^{−u}` (i.e. `ζ ∗ n^{−u}`), multiplicative by construction —
this is the object the divisor domination evaluates. -/
noncomputable def divisorRpow (u : ℝ) : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * invRpow u

lemma divisorRpow_apply (u : ℝ) (n : ℕ) :
    divisorRpow u n = ∑ d ∈ n.divisors, invRpow u d :=
  ArithmeticFunction.coe_zeta_mul_apply

lemma divisorRpow_isMultiplicative (u : ℝ) : (divisorRpow u).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_zeta.natCast).mul (invRpow_isMultiplicative u)

lemma divisorRpow_nonneg (u : ℝ) (n : ℕ) : 0 ≤ divisorRpow u n := by
  rw [divisorRpow_apply]
  exact Finset.sum_nonneg fun d _ => invRpow_nonneg u d

/-- **THE LOCAL FACTOR.**  At a prime power the divisor sum is the geometric series
`∑_{j≤k} p^{−ju} ≤ (1 − p^{−u})^{−1}` — the Euler factor, for EVERY exponent `k`, which is why
the engine never needs the exact exponents of `N`. -/
theorem divisorRpow_prime_pow_le {p : ℕ} (hp : p.Prime) {u : ℝ} (hu : 0 < u) (k : ℕ) :
    divisorRpow u (p ^ k) ≤ (1 - (p : ℝ) ^ (-u))⁻¹ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ (p : ℝ) ^ (-u) := Real.rpow_nonneg hp0.le _
  have hr1 : (p : ℝ) ^ (-u) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  rw [divisorRpow_apply, Nat.sum_divisors_prime_pow hp]
  have hterm : ∀ i ∈ Finset.range (k + 1),
      invRpow u (p ^ i) = ((p : ℝ) ^ (-u)) ^ i := by
    intro i _
    rw [invRpow_apply_of (pow_ne_zero i hp.pos.ne')]
    have hcast : ((p ^ i : ℕ) : ℝ) = (p : ℝ) ^ (i : ℝ) := by
      push_cast; rw [Real.rpow_natCast]
    rw [hcast, ← Real.rpow_mul hp0.le, show (i : ℝ) * (-u) = (-u) * (i : ℝ) from mul_comm _ _,
      Real.rpow_mul hp0.le, Real.rpow_natCast]
  rw [Finset.sum_congr rfl hterm]
  exact geom_range_le hr0 hr1 _

/-- Every window-smooth `b` with `1 ≤ b ≤ z` divides `N = ∏_{P≤p≤Q} p^z`: its prime factors lie
in the band, and its exponents are `< b ≤ z` (`Nat.factorization_lt`). -/
lemma windowSmooth_dvd_bandPow {P Q z b : ℕ} (hb1 : 1 ≤ b) (hbz : b ≤ z)
    (hbsm : WindowSmooth P Q b) : b ∣ ∏ p ∈ primeBand P Q, p ^ z := by
  have hb0 : b ≠ 0 := by omega
  have hbfac : ∏ p ∈ b.primeFactors, p ^ (b.factorization p) = b := by
    have h := Nat.prod_factorization_pow_eq_self hb0
    rwa [Finsupp.prod, Nat.support_factorization] at h
  have hsubset : b.primeFactors ⊆ primeBand P Q := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨hPp, hpQ⟩ := hbsm p hp
    rw [primeBand, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hPp, hpQ⟩, hpp⟩
  rw [← hbfac]
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ ?_)
    (Finset.prod_dvd_prod_of_subset _ _ _ hsubset)
  intro p _
  exact pow_dvd_pow p (le_trans (Nat.factorization_lt p hb0).le hbz)

/-- **THE ENGINE.**  For every `u > 0` the window-smooth `b^{−u}` mass up to any height `z` is
bounded by the finite band Euler product:

  `∑_{b ≤ z, b [P,Q]-smooth} b^{−u} ≤ ∏_{P≤p≤Q} (1 − p^{−u})^{−1}`.

The bound is `z`-FREE (the height enters only through the auxiliary modulus `N = ∏ p^z`), which
is what makes the mass page `z`-free and the tail page's `y`-dependence live entirely in the
Rankin shift. -/
theorem windowSmooth_rpow_sum_le (P Q z : ℕ) {u : ℝ} (hu : 0 < u) :
    ∑ b ∈ (Finset.Icc 1 z).filter (WindowSmooth P Q), (b : ℝ) ^ (-u)
      ≤ ∏ p ∈ primeBand P Q, (1 - (p : ℝ) ^ (-u))⁻¹ := by
  classical
  have hprime : ∀ p ∈ primeBand P Q, p.Prime := by
    intro p hp; rw [primeBand, Finset.mem_filter] at hp; exact hp.2
  set N : ℕ := ∏ p ∈ primeBand P Q, p ^ z with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    exact Finset.prod_pos fun p hp => pow_pos (hprime p hp).pos z
  -- STEP 1: the smooth set sits inside `N.divisors`
  have hsub : (Finset.Icc 1 z).filter (WindowSmooth P Q) ⊆ N.divisors := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb1, hbz⟩, hbsm⟩ := hb
    rw [Nat.mem_divisors]
    exact ⟨hNdef ▸ windowSmooth_dvd_bandPow hb1 hbz hbsm, hNpos.ne'⟩
  -- STEP 2: dominate, then evaluate the divisor sum as an Euler product
  have hcop : ((primeBand P Q : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime (fun p => p ^ z)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _
      ((Nat.coprime_primes (hprime p (Finset.mem_coe.mp hp))
        (hprime q (Finset.mem_coe.mp hq))).mpr hpq)
  calc ∑ b ∈ (Finset.Icc 1 z).filter (WindowSmooth P Q), (b : ℝ) ^ (-u)
      = ∑ b ∈ (Finset.Icc 1 z).filter (WindowSmooth P Q), invRpow u b := by
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_filter, Finset.mem_Icc] at hb
        rw [invRpow_apply_of (by omega : b ≠ 0)]
    _ ≤ ∑ d ∈ N.divisors, invRpow u d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => invRpow_nonneg u d)
    _ = divisorRpow u N := (divisorRpow_apply u N).symm
    _ = ∏ p ∈ primeBand P Q, divisorRpow u (p ^ z) := by
        rw [hNdef]
        exact ArithmeticFunction.IsMultiplicative.map_prod (fun p => p ^ z)
          (divisorRpow_isMultiplicative u) (primeBand P Q) hcop
    _ ≤ ∏ p ∈ primeBand P Q, (1 - (p : ℝ) ^ (-u))⁻¹ :=
        Finset.prod_le_prod (fun p _ => divisorRpow_nonneg u _)
          (fun p hp => divisorRpow_prime_pow_le (hprime p hp) hu z)

/-- The `r = 0` weight is the smooth indicator, so the carrier's rows are smooth-restricted
harmonic sums (`ramTailWeight_zero_param`). -/
lemma sum_ramTailWeight_zero_div_eq (P Q : ℕ) (s : Finset ℕ) (hs : ∀ b ∈ s, 1 ≤ b) :
    ∑ b ∈ s, ramTailWeight P Q 0 b / (b : ℝ)
      = ∑ b ∈ s.filter (WindowSmooth P Q), 1 / (b : ℝ) := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb0 : b ≠ 0 := by have := hs b hb; omega
  rw [ramTailWeight_zero_param]
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd h1.2 h2
  · exact absurd ⟨hb0, h3⟩ h1
  · exact zero_div _

/-! ## §2 — THE MASS PAGE

`∑_{b ≤ z} w_r(b)/b ≤ windowMassConst P Q` — the engine at `u = 1` composed with the LANDED
Mertens window constant.  The bound is uniform in `r ∈ [0,1]` (the carrier's
`ramTailWeight_le_zero_param`), uniform in `z`, and carries no `y`, no `H`, no `X`. -/

/-- **THE WINDOW MASS CONSTANT.**  `exp(c·(loglog Q − loglog P + 25))` with `c = 1 + 1/(P−1)`:
the band Euler product `∏_{P≤p≤Q}(1−1/p)^{−1}` majorised through `1/(p−1) ≤ c/p` and the
Mertens window sum.  `c` is the ONLY price of `1/(p−1)` vs `1/p`, and it is `≈ 1` at any window
whose lower endpoint is large (at the door, `c = 1 + 1/(2^{Adoor M} − 1}`). -/
noncomputable def windowMassConst (P Q : ℕ) : ℝ :=
  Real.exp ((1 + 1 / ((P : ℝ) - 1))
    * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))

/-- The band Euler product at `u = 1`, bounded by the window mass constant. -/
theorem prod_band_geom_one_le (P Q : ℕ) (hP : 4 ≤ P) (hPQ : P ≤ Q) :
    ∏ p ∈ primeBand P Q, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ ≤ windowMassConst P Q := by
  have hPR : (4 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hPm : (0 : ℝ) < (P : ℝ) - 1 := by linarith
  set c : ℝ := 1 + 1 / ((P : ℝ) - 1) with hc
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]; have : (0 : ℝ) ≤ 1 / ((P : ℝ) - 1) := by positivity
    linarith
  have hstep : ∀ p ∈ primeBand P Q,
      (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ ≤ Real.exp (c * (1 / (p : ℝ))) := by
    intro p hp
    rw [primeBand, Finset.mem_filter, Finset.mem_Icc] at hp
    have hPp : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.1
    have hp4 : (4 : ℝ) ≤ (p : ℝ) := le_trans hPR hPp
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hpm' : ((p : ℝ) - 1) ≠ 0 := ne_of_gt hpm
    -- the local factor in closed form
    have hloc : (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_one,
        show (1 : ℝ) - ((p : ℝ))⁻¹ = ((p : ℝ) - 1) / (p : ℝ) by field_simp, inv_div,
        show (1 : ℝ) + 1 / ((p : ℝ) - 1) = ((p : ℝ) - 1 + 1) / ((p : ℝ) - 1) by
          rw [add_div, div_self hpm']]
      congr 1
      ring
    -- `1/(p−1) ≤ c/p`
    have hkey : 1 / ((p : ℝ) - 1) ≤ c * (1 / (p : ℝ)) := by
      rw [hc, mul_one_div, div_le_div_iff₀ hpm hp0]
      have hratio : (1 : ℝ) ≤ ((p : ℝ) - 1) / ((P : ℝ) - 1) := by
        rw [le_div_iff₀ hPm]; linarith
      have hexp : (1 + 1 / ((P : ℝ) - 1)) * ((p : ℝ) - 1)
          = ((p : ℝ) - 1) + ((p : ℝ) - 1) / ((P : ℝ) - 1) := by
        rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul]
      linarith [hexp, hratio]
    calc (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ = 1 + 1 / ((p : ℝ) - 1) := hloc
      _ ≤ Real.exp (1 / ((p : ℝ) - 1)) := by
          linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1))]
      _ ≤ Real.exp (c * (1 / (p : ℝ))) := Real.exp_le_exp.mpr hkey
  calc ∏ p ∈ primeBand P Q, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹
      ≤ ∏ p ∈ primeBand P Q, Real.exp (c * (1 / (p : ℝ))) :=
        Finset.prod_le_prod (fun p hp => by
          refine (one_sub_rpow_inv_pos ?_ (by norm_num : (0:ℝ) < 1)).le
          rw [primeBand, Finset.mem_filter] at hp
          exact hp.2.two_le) hstep
    _ = Real.exp (∑ p ∈ primeBand P Q, c * (1 / (p : ℝ))) := (Real.exp_sum _ _).symm
    _ = Real.exp (c * ∑ p ∈ primeBand P Q, 1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ windowMassConst P Q := by
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hc0)
        refine sum_inv_primeBand_le P Q ?_ hPQ
        have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        linarith

/-- **THE MASS PAGE, `r = 0`.**  `∑_{b ≤ z} w_0(b)/b ≤ windowMassConst P Q` for every height
`z` — the carrier's `hmass` slot at the worst case. -/
theorem ramTailWeight_zero_mass_le (P Q z : ℕ) (hP : 4 ≤ P) (hPQ : P ≤ Q) :
    ∑ b ∈ Finset.Icc 1 z, ramTailWeight P Q 0 b / (b : ℝ) ≤ windowMassConst P Q := by
  classical
  rw [sum_ramTailWeight_zero_div_eq P Q _ (fun b hb => (Finset.mem_Icc.mp hb).1)]
  have hrw : ∀ b ∈ (Finset.Icc 1 z).filter (WindowSmooth P Q),
      1 / (b : ℝ) = (b : ℝ) ^ (-(1 : ℝ)) := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    have hb0 : (0 : ℝ) < (b : ℝ) := by
      have : 1 ≤ b := hb.1.1
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    rw [Real.rpow_neg hb0.le, Real.rpow_one, one_div]
  rw [Finset.sum_congr rfl hrw]
  exact le_trans (windowSmooth_rpow_sum_le P Q z (by norm_num))
    (prod_band_geom_one_le P Q hP hPQ)

/-- **THE MASS PAGE — the carrier's `hmass`, `r`-UNIFORMLY.**  For every damping `r ∈ [0,1]`
and every height `z`,

  `∑_{b ≤ z} w_r(b)/b ≤ windowMassConst P Q`,

the `M` of `MmuGrChi_rate` / `norm_MmuGrChi_le_split`.  Uniformity in `r` is the carrier's
`ramTailWeight_le_zero_param` (`r = 0` is the worst case), which is what makes the `∫₀¹ dr`
composition of `MmuRamChi_rate` free. -/
theorem ramTailWeight_mass_le (P Q z : ℕ) (hP : 4 ≤ P) (hPQ : P ≤ Q) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ b ∈ Finset.Icc 1 z, ramTailWeight P Q r b / (b : ℝ) ≤ windowMassConst P Q := by
  refine le_trans (Finset.sum_le_sum ?_) (ramTailWeight_zero_mass_le P Q z hP hPQ)
  intro b hb
  exact div_le_div_of_nonneg_right (ramTailWeight_le_zero_param hr0 hr1 b) (Nat.cast_nonneg b)

/-- **THE `H`-FREE RATIO FORM** (the refuter's value).  `windowMassConst P Q =
e^{25c}·(log Q/log P)^c` with `c = 1 + 1/(P−1)` — the freeze's `≍ log Q/log P` shape, with the
whole constant explicit and no `H`, `X` or `y` anywhere. -/
theorem windowMassConst_eq_ratio_rpow (P Q : ℕ) (hP : 4 ≤ P) (hPQ : P ≤ Q) :
    windowMassConst P Q
      = Real.exp (25 * (1 + 1 / ((P : ℝ) - 1)))
          * (Real.log (Q : ℝ) / Real.log (P : ℝ)) ^ (1 + 1 / ((P : ℝ) - 1)) := by
  have hP1 : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hPQR : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos hP1
  have hlogQ : 0 < Real.log (Q : ℝ) := lt_of_lt_of_le hlogP (Real.log_le_log (by linarith) hPQR)
  set c : ℝ := 1 + 1 / ((P : ℝ) - 1) with hc
  rw [windowMassConst, Real.rpow_def_of_pos (by positivity), Real.log_div hlogQ.ne' hlogP.ne']
  rw [show c * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25)
      = 25 * c + (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ))) * c by ring]
  rw [Real.exp_add]

/-! ### The door instantiation

The door windows are `P₁ = calP (Adoor M) G 1 = 2^{Adoor M}` and
`Q₁ = calQK (Adoor M) G M 1 = 2^{M·Adoor M}` (`SeamCalibration.calE_one`,
`SeamCalibrationK.calQK`), so `log Q₁/log P₁ = M` EXACTLY and the mass is `≈ e^{25}·M`. -/

/-- **THE DOOR WINDOW RATIO.**  `loglog Q₁ − loglog P₁ = log M` at the calibrated `j = 1`
window (`P₁ = 2^A`, `Q₁ = 2^{MA}`). -/
theorem loglog_calQK_sub_calP (A G M : ℕ) (hA : 1 ≤ A) (hM : 1 ≤ M) :
    Real.log (Real.log ((calQK A G M 1 : ℕ) : ℝ))
        - Real.log (Real.log ((calP A G 1 : ℕ) : ℝ))
      = Real.log (M : ℝ) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hP : Real.log ((calP A G 1 : ℕ) : ℝ) = (A : ℝ) * Real.log 2 := by
    rw [calP, calE_one]
    push_cast
    rw [Real.log_pow]
  have hQ : Real.log ((calQK A G M 1 : ℕ) : ℝ) = (M : ℝ) * ((A : ℝ) * Real.log 2) := by
    rw [log_calQK, calE_one]
    push_cast
    ring
  rw [hP, hQ, Real.log_mul (by linarith) (by positivity)]
  ring

/-- **THE MASS PAGE AT THE DOOR.**  At the calibrated `j = 1` window the carrier's `hmass` is
discharged with the `H`-free value `exp(c·(log M + 25))`, `c = 1 + 1/(2^A − 1)` — i.e.
`≈ e^{25}·M`, the freeze's `log Q/log P` shape at the door ratio `M`. -/
theorem ramTailWeight_mass_door (A G M z : ℕ) (hA : 2 ≤ A) (hM : 1 ≤ M) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ b ∈ Finset.Icc 1 z, ramTailWeight (calP A G 1) (calQK A G M 1) r b / (b : ℝ)
      ≤ Real.exp ((1 + 1 / ((2 : ℝ) ^ A - 1)) * (Real.log (M : ℝ) + 25)) := by
  have hPeq : calP A G 1 = 2 ^ A := by rw [calP, calE_one]
  have hP4 : 4 ≤ calP A G 1 := by
    rw [hPeq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA
  have hPQ : calP A G 1 ≤ calQK A G M 1 := by
    rw [hPeq, calQK, calE_one]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith [hM])
  refine le_trans (ramTailWeight_mass_le _ _ z hP4 hPQ hr0 hr1) ?_
  rw [windowMassConst, loglog_calQK_sub_calP A G M (by omega) hM]
  refine Real.exp_le_exp.mpr (le_of_eq ?_)
  congr 2
  rw [hPeq]
  push_cast
  ring

/-! ## §3 — THE RANKIN-TAIL PAGE

The shifted-Euler bound.  For `b > z` the Rankin shift `1/b ≤ z^{−σ}·b^{−(1−σ)}` moves one
`σ` of the exponent out of the sum; the engine at `u = 1−σ` then evaluates what is left, and
the band Euler product costs `exp(2·Q^σ·(loglog Q − loglog P + 25))`.  `σ` is the CONSUMER's
choice; §3's last two theorems make the door choice `σ = 2A·loglog y/log z`. -/

/-- **THE RANKIN WINDOW CONSTANT** `exp(2·Q^σ·(loglog Q − loglog P + 25))`.  The factor `2`
is the local `(1 − p^{σ−1})^{−1} ≤ 1 + 2p^{σ−1}` at `p ≥ 4`, `σ ≤ 1/2`; the factor `Q^σ` is the
`p^σ ≤ Q^σ` shift — the ONLY place the Rankin exponent meets the window scale, and the source of
the page's `o(1)` gate. -/
noncomputable def windowRankinConst (P Q : ℕ) (σ : ℝ) : ℝ :=
  Real.exp (2 * (Q : ℝ) ^ σ
    * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))

/-- The band Euler product at `u = 1−σ`, bounded by the Rankin window constant. -/
theorem prod_band_geom_shift_le (P Q : ℕ) {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 1 / 2)
    (hP : 4 ≤ P) (hPQ : P ≤ Q) :
    ∏ p ∈ primeBand P Q, (1 - (p : ℝ) ^ (-(1 - σ)))⁻¹ ≤ windowRankinConst P Q σ := by
  have hPR : (4 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hQ4 : (4 : ℝ) ≤ (Q : ℝ) := le_trans hPR (by exact_mod_cast hPQ)
  have hQσ0 : (0 : ℝ) < (Q : ℝ) ^ σ := Real.rpow_pos_of_pos (by linarith) σ
  have hhalf : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have hstep : ∀ p ∈ primeBand P Q,
      (1 - (p : ℝ) ^ (-(1 - σ)))⁻¹ ≤ Real.exp (2 * (Q : ℝ) ^ σ * (1 / (p : ℝ))) := by
    intro p hp
    rw [primeBand, Finset.mem_filter, Finset.mem_Icc] at hp
    have hPp : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.1
    have hpQ : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hp.1.2
    have hp4 : (4 : ℝ) ≤ (p : ℝ) := le_trans hPR hPp
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
    set v : ℝ := (p : ℝ) ^ (-(1 - σ)) with hv
    have hv0 : (0 : ℝ) ≤ v := Real.rpow_nonneg hp0.le _
    -- `v ≤ 1/2`: the exponent is `≤ −1/2` and the base is `≥ 4`
    have hvhalf : v ≤ 1 / 2 := by
      calc v ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
        _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hp4 (by norm_num)
        _ = 1 / 2 := hhalf
    -- `v = p^σ/p ≤ Q^σ/p`
    have hvform : v = (p : ℝ) ^ σ / (p : ℝ) := by
      rw [hv, show -(1 - σ) = σ - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
    have hvle : v ≤ (Q : ℝ) ^ σ * (1 / (p : ℝ)) := by
      rw [hvform, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hp0.le hpQ hσ0.le) (by positivity)
    -- the local factor
    have hloc : (1 - v)⁻¹ ≤ 1 + 2 * v := by
      have h1v : (0 : ℝ) < 1 - v := by linarith
      rw [inv_eq_one_div, div_le_iff₀ h1v]
      nlinarith [mul_nonneg hv0 (by linarith : (0 : ℝ) ≤ 1 - 2 * v)]
    calc (1 - v)⁻¹ ≤ 1 + 2 * v := hloc
      _ ≤ Real.exp (2 * v) := by linarith [Real.add_one_le_exp (2 * v)]
      _ ≤ Real.exp (2 * ((Q : ℝ) ^ σ * (1 / (p : ℝ)))) := by
          refine Real.exp_le_exp.mpr ?_
          linarith [hvle]
      _ = Real.exp (2 * (Q : ℝ) ^ σ * (1 / (p : ℝ))) := by rw [mul_assoc]
  calc ∏ p ∈ primeBand P Q, (1 - (p : ℝ) ^ (-(1 - σ)))⁻¹
      ≤ ∏ p ∈ primeBand P Q, Real.exp (2 * (Q : ℝ) ^ σ * (1 / (p : ℝ))) :=
        Finset.prod_le_prod (fun p hp => by
          refine (one_sub_rpow_inv_pos ?_ (by linarith : (0 : ℝ) < 1 - σ)).le
          rw [primeBand, Finset.mem_filter] at hp
          exact hp.2.two_le) hstep
    _ = Real.exp (∑ p ∈ primeBand P Q, 2 * (Q : ℝ) ^ σ * (1 / (p : ℝ))) :=
        (Real.exp_sum _ _).symm
    _ = Real.exp (2 * (Q : ℝ) ^ σ * ∑ p ∈ primeBand P Q, 1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ windowRankinConst P Q σ := by
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (by positivity))
        refine sum_inv_primeBand_le P Q ?_ hPQ
        have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        linarith

/-- **THE RANKIN-TAIL PAGE, `r = 0`, `σ`-PARAMETERIZED.**  For every `σ ∈ (0, 1/2]` and every
split height `z ≥ 1`,

  `∑_{z < b ≤ y} w_0(b)/b ≤ z^{−σ} · exp(2·Q^σ·(loglog Q − loglog P + 25))`.

Both factors are explicit; `σ` is the consumer's choice (the calibration `σ = 2A·loglog y/log z`
is `ramTailWeight_tail_calibrated`).  The `y`-dependence is ONLY through the range of the sum:
the bound itself is `y`-free. -/
theorem ramTailWeight_zero_tail_le (P Q z y : ℕ) {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 1 / 2)
    (hP : 4 ≤ P) (hPQ : P ≤ Q) (hz : 1 ≤ z) :
    ∑ b ∈ Finset.Ioc z y, ramTailWeight P Q 0 b / (b : ℝ)
      ≤ (z : ℝ) ^ (-σ) * windowRankinConst P Q σ := by
  classical
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hz
  have hzσ0 : (0 : ℝ) < (z : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hz0 _
  rw [sum_ramTailWeight_zero_div_eq P Q _
    (fun b hb => by have := (Finset.mem_Ioc.mp hb).1; omega)]
  -- STEP 1: the Rankin shift, termwise
  have hshift : ∀ b ∈ (Finset.Ioc z y).filter (WindowSmooth P Q),
      1 / (b : ℝ) ≤ (z : ℝ) ^ (-σ) * (b : ℝ) ^ (-(1 - σ)) := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Ioc] at hb
    have hzb : (z : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.1.1.le
    have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
    have hsplit : (b : ℝ) ^ (-(1 : ℝ)) = (b : ℝ) ^ (-(1 - σ)) * (b : ℝ) ^ (-σ) := by
      rw [← Real.rpow_add hb0]; ring_nf
    have hzb' : (b : ℝ) ^ (-σ) ≤ (z : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hz0 hzb (by linarith)
    have h1 : 1 / (b : ℝ) = (b : ℝ) ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg hb0.le, Real.rpow_one, one_div]
    rw [h1, hsplit, mul_comm ((z : ℝ) ^ (-σ))]
    exact mul_le_mul_of_nonneg_left hzb' (Real.rpow_nonneg hb0.le _)
  -- STEP 2: widen the range and fire the engine at `u = 1 − σ`
  have hwiden : (Finset.Ioc z y).filter (WindowSmooth P Q)
      ⊆ (Finset.Icc 1 y).filter (WindowSmooth P Q) := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Ioc] at hb
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hb.1.2⟩, hb.2⟩
  calc ∑ b ∈ (Finset.Ioc z y).filter (WindowSmooth P Q), 1 / (b : ℝ)
      ≤ ∑ b ∈ (Finset.Ioc z y).filter (WindowSmooth P Q),
          (z : ℝ) ^ (-σ) * (b : ℝ) ^ (-(1 - σ)) := Finset.sum_le_sum hshift
    _ = (z : ℝ) ^ (-σ) * ∑ b ∈ (Finset.Ioc z y).filter (WindowSmooth P Q),
          (b : ℝ) ^ (-(1 - σ)) := by rw [Finset.mul_sum]
    _ ≤ (z : ℝ) ^ (-σ) * ∑ b ∈ (Finset.Icc 1 y).filter (WindowSmooth P Q),
          (b : ℝ) ^ (-(1 - σ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hzσ0.le
        exact Finset.sum_le_sum_of_subset_of_nonneg hwiden
          (fun b _ _ => Real.rpow_nonneg (Nat.cast_nonneg b) _)
    _ ≤ (z : ℝ) ^ (-σ) * ∏ p ∈ primeBand P Q, (1 - (p : ℝ) ^ (-(1 - σ)))⁻¹ :=
        mul_le_mul_of_nonneg_left (windowSmooth_rpow_sum_le P Q y (by linarith)) hzσ0.le
    _ ≤ (z : ℝ) ^ (-σ) * windowRankinConst P Q σ :=
        mul_le_mul_of_nonneg_left (prod_band_geom_shift_le P Q hσ0 hσ2 hP hPQ) hzσ0.le

/-- **THE RANKIN-TAIL PAGE — `r`-UNIFORM, `σ`-PARAMETERIZED.**  The same bound for every
damping `r ∈ [0,1]` (the carrier's `ramTailWeight_le_zero_param`). -/
theorem ramTailWeight_tail_le (P Q z y : ℕ) {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 1 / 2)
    (hP : 4 ≤ P) (hPQ : P ≤ Q) (hz : 1 ≤ z) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ b ∈ Finset.Ioc z y, ramTailWeight P Q r b / (b : ℝ)
      ≤ (z : ℝ) ^ (-σ) * windowRankinConst P Q σ := by
  refine le_trans (Finset.sum_le_sum ?_) (ramTailWeight_zero_tail_le P Q z y hσ0 hσ2 hP hPQ hz)
  intro b hb
  exact div_le_div_of_nonneg_right (ramTailWeight_le_zero_param hr0 hr1 b) (Nat.cast_nonneg b)

/-- **THE CALIBRATION.**  At `σ = 2A·loglog y/log z` the Rankin factor is EXACTLY
`z^{−σ} = (log y)^{−2A}`, and the two gates are the honest content of the page:

* `hgateHalf : 4A·loglog y ≤ log z` — the `σ ≤ 1/2` gate (the shift may not eat the whole
  exponent);
* `hgateO1 : 2A·loglog y·log Q ≤ log z` — **THE `o(1)` GATE**, i.e. `σ·log Q ≤ 1`: it is the
  coupling `O(A·loglog y·log Q/log z)` between the calibration scale and the WINDOW scale, and
  it is the one thing this page cannot discharge for the consumer (it is false when
  `log Q ≍ log y`, exactly as the carrier's header says).  Under it, `Q^σ ≤ e`.

Delivered: `∑_{z<b≤y} w_r(b)/b ≤ (log y)^{−2A} · exp(2e·(loglog Q − loglog P + 25))` — the
`(log y)^{−2A}` shape with the window constant fully explicit and no `o(1)` absorbed. -/
theorem ramTailWeight_tail_calibrated (P Q z y : ℕ) (A : ℝ) (hA : 0 < A)
    (hP : 4 ≤ P) (hPQ : P ≤ Q) (hz2 : 2 ≤ z) (hy : 1 < Real.log (y : ℝ))
    (hgateHalf : 4 * A * Real.log (Real.log (y : ℝ)) ≤ Real.log (z : ℝ))
    (hgateO1 : 2 * A * Real.log (Real.log (y : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (z : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ b ∈ Finset.Ioc z y, ramTailWeight P Q r b / (b : ℝ)
      ≤ (Real.log (y : ℝ)) ^ (-(2 * A))
          * Real.exp (2 * Real.exp 1
              * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25)) := by
  have hz1 : 1 ≤ z := by omega
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hz0 : (0 : ℝ) < (z : ℝ) := by linarith
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hLy : 0 < Real.log (y : ℝ) := by linarith
  have hLLy : 0 < Real.log (Real.log (y : ℝ)) := Real.log_pos hy
  set σ : ℝ := 2 * A * Real.log (Real.log (y : ℝ)) / Real.log (z : ℝ) with hσ
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσ2 : σ ≤ 1 / 2 := by
    rw [hσ, div_le_iff₀ hlogz]
    linarith [hgateHalf]
  -- the Rankin factor IS `(log y)^{−2A}`
  have hzfac : (z : ℝ) ^ (-σ) = (Real.log (y : ℝ)) ^ (-(2 * A)) := by
    rw [Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hLy, hσ]
    congr 1
    field_simp
  -- the `o(1)` gate gives `Q^σ ≤ e`
  have hQσ : (Q : ℝ) ^ σ ≤ Real.exp 1 := by
    have hQ4 : (4 : ℝ) ≤ (Q : ℝ) := by
      have : (4 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
      exact le_trans this (by exact_mod_cast hPQ)
    have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
    rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < (Q:ℝ))]
    refine Real.exp_le_exp.mpr ?_
    rw [hσ, ← mul_div_assoc, div_le_one hlogz]
    linarith [hgateO1]
  refine le_trans (ramTailWeight_tail_le P Q z y hσ0 hσ2 hP hPQ hz1 hr0 hr1) ?_
  rw [hzfac]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hLy.le _)
  rw [windowRankinConst]
  refine Real.exp_le_exp.mpr ?_
  have hmert := mertens_window_nonneg P Q hP hPQ
  have h2 : 2 * (Q : ℝ) ^ σ ≤ 2 * Real.exp 1 := by linarith
  exact mul_le_mul_of_nonneg_right h2 hmert

/-- **THE CARRIER'S `htail`, VERBATIM, AT THE DOOR SPLIT `z = ⌊√y⌋`.**  Three explicit gates in
`log y`, `loglog y`, `log P`, `log Q` — nothing else — deliver exactly the hypothesis
`MmuGrChi_rate` demands:

  `∑_{√y < b ≤ y} w_r(b)/b ≤ 1/(log y)^A`.

* `hgateHalf : 16A·loglog y ≤ log y` and `hgateO1 : 8A·loglog y·log Q ≤ log y` are the two gates
  of `ramTailWeight_tail_calibrated` transported through the LANDED
  `Salt.TwinBar.log_natSqrt_ge` (`log ⌊√y⌋ ≥ (log y)/4`, `y ≥ 16`) — the factor `4` is the
  floor's price, the same one the carrier pays for its `4^A`;
* `hgateWin : exp(2e·(loglog Q − loglog P + 25)) ≤ (log y)^A` is where the surplus decay
  `(log y)^{−2A} → (log y)^{−A}` pays the WINDOW constant.  At the door windows the left side is
  `≈ (e^{25}·M)^{2e}` against a tower-sized `(log y)^A`: free by an astronomical margin, and
  STATED rather than absorbed. -/
theorem ramTailWeight_htail_door (P Q y : ℕ) (A : ℝ) (hA : 0 < A)
    (hP : 4 ≤ P) (hPQ : P ≤ Q) (hy : 16 ≤ y)
    (hgateHalf : 16 * A * Real.log (Real.log (y : ℝ)) ≤ Real.log (y : ℝ))
    (hgateO1 : 8 * A * Real.log (Real.log (y : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (y : ℝ))
    (hgateWin : Real.exp (2 * Real.exp 1
        * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
      ≤ (Real.log (y : ℝ)) ^ A)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q r b / (b : ℝ)
      ≤ 1 / (Real.log (y : ℝ)) ^ A := by
  have hyR : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hLy1 : 1 < Real.log (y : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 16) hyR
    have h16 : (1 : ℝ) < Real.log 16 := by
      have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
      rw [this]; linarith
    linarith
  have hLy : 0 < Real.log (y : ℝ) := by linarith
  -- the split height and its log
  have hs4 : 4 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by omega)
  have hs2 : 2 ≤ Nat.sqrt y := by omega
  have hlogs : Real.log (y : ℝ) / 4 ≤ Real.log ((Nat.sqrt y : ℕ) : ℝ) :=
    Salt.TwinBar.log_natSqrt_ge hy
  refine le_trans (ramTailWeight_tail_calibrated P Q (Nat.sqrt y) y A hA hP hPQ hs2 hLy1
    (by linarith) (by linarith) hr0 hr1) ?_
  -- `(log y)^{−2A}·exp(window) ≤ (log y)^{−2A}·(log y)^A = 1/(log y)^A`
  have hLA : (0 : ℝ) < (Real.log (y : ℝ)) ^ A := Real.rpow_pos_of_pos hLy A
  calc (Real.log (y : ℝ)) ^ (-(2 * A))
        * Real.exp (2 * Real.exp 1
            * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
      ≤ (Real.log (y : ℝ)) ^ (-(2 * A)) * (Real.log (y : ℝ)) ^ A :=
        mul_le_mul_of_nonneg_left hgateWin (Real.rpow_nonneg hLy.le _)
    _ = 1 / (Real.log (y : ℝ)) ^ A := by
        rw [← Real.rpow_add hLy, show -(2 * A) + A = -A by ring, Real.rpow_neg hLy.le, one_div]

/-! ## §4 — ⟦THE PRIME-SET ENGINE⟧ (LEVEL2-PROD, 2026-07-31): THE SAME ENGINE AT AN
ARBITRARY PRIME SET, AND THE PRODUCT SPLIT

§1's engine reads `P, Q` ONLY through membership in `primeBand P Q`: the divisor domination
`b ∣ ∏_{p ∈ S} p^z`, the multiplicativity, and the local geometric majorant are all
statements about a FINSET OF PRIMES.  This section states them that way
(`primeSet_rpow_sum_le`), adds the union split `∏_{S₁ ∪ S₂} ≤ ∏_{S₁}·∏_{S₂}` (every Euler
factor is `≥ 1`), and composes both at `u = 1` into the TWO-WINDOW mass
(`twoWindow_mass_le`).

⟦WHY⟧ the door's mask names two blocks; pricing them against ONE covering window forces the
covering ratio `log 𝒬₂/log 𝒫₁`, which at the `G`-lever carries `2^K`.  Priced PER BLOCK the
two ratios are `M` and `4M` at EVERY base — the lever cancels inside each block.

**PURELY ADDITIVE**: §1–§3 are untouched; `windowSmooth_rpow_sum_le` remains the door of the
single-window lane. -/

/-- Every `b` with `1 ≤ b ≤ z` whose prime factors lie in `S` divides `N = ∏_{p ∈ S} p^z`. -/
lemma primeSetSmooth_dvd_setPow {S : Finset ℕ} {z b : ℕ} (hb1 : 1 ≤ b) (hbz : b ≤ z)
    (hbsm : b.primeFactors ⊆ S) : b ∣ ∏ p ∈ S, p ^ z := by
  have hb0 : b ≠ 0 := by omega
  have hbfac : ∏ p ∈ b.primeFactors, p ^ (b.factorization p) = b := by
    have h := Nat.prod_factorization_pow_eq_self hb0
    rwa [Finsupp.prod, Nat.support_factorization] at h
  rw [← hbfac]
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ ?_)
    (Finset.prod_dvd_prod_of_subset _ _ _ hbsm)
  intro p _
  exact pow_dvd_pow p (le_trans (Nat.factorization_lt p hb0).le hbz)

/-- **THE ENGINE, PRIME-SET GENERIC.** -/
theorem primeSet_rpow_sum_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (z : ℕ) {u : ℝ}
    (hu : 0 < u) :
    ∑ b ∈ (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ S), (b : ℝ) ^ (-u)
      ≤ ∏ p ∈ S, (1 - (p : ℝ) ^ (-u))⁻¹ := by
  classical
  set N : ℕ := ∏ p ∈ S, p ^ z with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    exact Finset.prod_pos fun p hp => pow_pos (hS p hp).pos z
  have hsub : (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ S) ⊆ N.divisors := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb1, hbz⟩, hbsm⟩ := hb
    rw [Nat.mem_divisors]
    exact ⟨hNdef ▸ primeSetSmooth_dvd_setPow hb1 hbz hbsm, hNpos.ne'⟩
  have hcop : ((S : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime (fun p => p ^ z)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _
      ((Nat.coprime_primes (hS p (Finset.mem_coe.mp hp))
        (hS q (Finset.mem_coe.mp hq))).mpr hpq)
  calc ∑ b ∈ (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ S), (b : ℝ) ^ (-u)
      = ∑ b ∈ (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ S), invRpow u b := by
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_filter, Finset.mem_Icc] at hb
        rw [invRpow_apply_of (by omega : b ≠ 0)]
    _ ≤ ∑ d ∈ N.divisors, invRpow u d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => invRpow_nonneg u d)
    _ = divisorRpow u N := (divisorRpow_apply u N).symm
    _ = ∏ p ∈ S, divisorRpow u (p ^ z) := by
        rw [hNdef]
        exact ArithmeticFunction.IsMultiplicative.map_prod (fun p => p ^ z)
          (divisorRpow_isMultiplicative u) S hcop
    _ ≤ ∏ p ∈ S, (1 - (p : ℝ) ^ (-u))⁻¹ :=
        Finset.prod_le_prod (fun p _ => divisorRpow_nonneg u _)
          (fun p hp => divisorRpow_prime_pow_le (hS p hp) hu z)

/-- Every local Euler factor at a prime is `≥ 1`. -/
lemma one_le_geom_factor {p : ℕ} (hp : p.Prime) {u : ℝ} (hu : 0 < u) :
    (1 : ℝ) ≤ (1 - (p : ℝ) ^ (-u))⁻¹ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr0 : (0 : ℝ) < (p : ℝ) ^ (-u) := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : (p : ℝ) ^ (-u) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  rw [le_inv_comm₀ (by norm_num) (by linarith)]
  linarith

/-- **THE PRODUCT SPLIT.**  The Euler product over a union is at most the product of the two
Euler products (every factor is `≥ 1`). -/
theorem prod_geom_union_le (S₁ S₂ : Finset ℕ) (hS₁ : ∀ p ∈ S₁, p.Prime)
    (hS₂ : ∀ p ∈ S₂, p.Prime) {u : ℝ} (hu : 0 < u) :
    ∏ p ∈ S₁ ∪ S₂, (1 - (p : ℝ) ^ (-u))⁻¹
      ≤ (∏ p ∈ S₁, (1 - (p : ℝ) ^ (-u))⁻¹) * ∏ p ∈ S₂, (1 - (p : ℝ) ^ (-u))⁻¹ := by
  classical
  have hdisj : Disjoint S₁ (S₂ \ S₁) := Finset.disjoint_sdiff
  have hunion : S₁ ∪ S₂ = S₁ ∪ (S₂ \ S₁) := by
    ext p; simp [Finset.mem_union]
  rw [hunion, Finset.prod_union hdisj]
  have hle : ∏ p ∈ S₂ \ S₁, (1 - (p : ℝ) ^ (-u))⁻¹
      ≤ ∏ p ∈ S₂, (1 - (p : ℝ) ^ (-u))⁻¹ := by
    refine Finset.prod_le_prod_of_subset_of_one_le Finset.sdiff_subset
      (fun p hp => le_trans zero_le_one
        (one_le_geom_factor (hS₂ p (Finset.sdiff_subset hp)) hu)) ?_
    intro p hp _
    exact one_le_geom_factor (hS₂ p hp) hu
  have hpos : (0 : ℝ) ≤ ∏ p ∈ S₁, (1 - (p : ℝ) ^ (-u))⁻¹ :=
    Finset.prod_nonneg fun p hp => le_trans zero_le_one (one_le_geom_factor (hS₁ p hp) hu)
  exact mul_le_mul_of_nonneg_left hle hpos


/-! ### W1b — the two-window composition at `u = 1` -/

/-- **THE TWO-WINDOW MASS.**  The `[P₁,Q₁] ∪ [P₂,Q₂]`-smooth harmonic mass is at most the
PRODUCT of the two window mass constants. -/
theorem twoWindow_mass_le (P₁ Q₁ P₂ Q₂ z : ℕ) (h₁4 : 4 ≤ P₁) (h₁ : P₁ ≤ Q₁)
    (h₂4 : 4 ≤ P₂) (h₂ : P₂ ≤ Q₂) :
    ∑ b ∈ (Finset.Icc 1 z).filter
        (fun b => b.primeFactors ⊆ primeBand P₁ Q₁ ∪ primeBand P₂ Q₂), 1 / (b : ℝ)
      ≤ windowMassConst P₁ Q₁ * windowMassConst P₂ Q₂ := by
  classical
  have hpb : ∀ (P Q : ℕ), ∀ p ∈ primeBand P Q, p.Prime := by
    intro P Q p hp; rw [primeBand, Finset.mem_filter] at hp; exact hp.2
  have hprime : ∀ p ∈ primeBand P₁ Q₁ ∪ primeBand P₂ Q₂, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hpb _ _ p h
    · exact hpb _ _ p h
  have hrw : ∀ b ∈ (Finset.Icc 1 z).filter
      (fun b => b.primeFactors ⊆ primeBand P₁ Q₁ ∪ primeBand P₂ Q₂),
      1 / (b : ℝ) = (b : ℝ) ^ (-(1 : ℝ)) := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    have hb0 : (0 : ℝ) < (b : ℝ) := by
      have : 1 ≤ b := hb.1.1
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    rw [Real.rpow_neg hb0.le, Real.rpow_one, one_div]
  rw [Finset.sum_congr rfl hrw]
  refine le_trans (primeSet_rpow_sum_le _ hprime z (by norm_num)) ?_
  refine le_trans (prod_geom_union_le _ _ (hpb _ _) (hpb _ _) (by norm_num)) ?_
  have hA := prod_band_geom_one_le P₁ Q₁ h₁4 h₁
  have hB := prod_band_geom_one_le P₂ Q₂ h₂4 h₂
  have hB0 : (0 : ℝ) ≤ ∏ p ∈ primeBand P₂ Q₂, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ :=
    Finset.prod_nonneg fun p hp =>
      le_trans zero_le_one (one_le_geom_factor (hpb _ _ p hp) (by norm_num))
  have hM0 : (0 : ℝ) ≤ windowMassConst P₁ Q₁ := (Real.exp_pos _).le
  exact mul_le_mul hA hB hB0 hM0


end Salt.MR
