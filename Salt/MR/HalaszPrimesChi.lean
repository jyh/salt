/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszPrimesCore
import Salt.MR.VkTwistRegion
import Salt.MR.VkTwistRegionReal
import Salt.MR.HybridLargeValues
import Salt.MR.HybridMoments

/-!
# STONE C — the `χ`-twisted MR Lemma 11 (`halasz_primes_chi`)

Wave P-6-CORE's stone C: the `χ`-twin of the landed `halasz_primes_pow`
(`HalaszPrimesCore.lean`), on the two maestro rulings (the height split; the rows).

## THE FINDING (the reason this file is 900 lines and not 4000)

The ruled ROW statement — for ONE character `χ`, a well-spaced `𝒯 ⊆ [−T, T]` and
prime-supported data,

  `∑_{t∈𝒯} ‖∑_{p∈S} p^{−it}·χ̄(p)·a_p‖² ≤ C·(P + |𝒯|·P·e^{−c log P/D(T)}·(log T)²)/log P·∑‖a_p‖²`,

**needs no twisted `L`-function at all**: it is the landed `halasz_primes_pow` at the
coefficient sequence `a_p ↦ χ̄(p)·a_p`, because `‖χ̄(p)‖ ≤ 1` and the Halász bound is
monotone in the coefficient mass `∑‖a_p‖²`.  Consequently:

* the row holds for **every** `χ` (principal, complex, real, exceptional) — the ruled
  carve-out disjunction is NOT needed on the row, and stating it would state a hypothesis
  the proof never reads (`halasz_primes_chi`, §2);
* the ruled **principal-row corollary** is the same theorem at `χ = 1`; the
  `neg_re_logDeriv_trivChar_le_zeta` correction (the `p ∣ q` debit) is not needed either,
  because the row's `χ̄(p)` sits in the DATUM, not in an Euler product
  (`halasz_primes_chi_principal`, §2);
* the χ-VK zero-free region (stones A+B) is **not** consumed by the row.

Where the twisted region *is* irreducible: the P-6-E consumer's named socket
`Salt.MR.HalaszPrimesChi` (`USetChi.lean`) sums over a per-fibre-well-spaced set of
**PAIRS** `ℰ ⊆ (characters mod q) × [−T, T]` with the diagonal term `P` — not `φ(q)·P`.
Dualising that (`primes_dual_iff` at `φ(r, n) = n^{−i r.2}·χ̄_{r.1}(n)`) produces per-pair
sums `∑_p (χ_r·χ̄_{r'})(p)·p^{i(t−t')}` whose character `ψ = χ_r·χ̄_{r'}` is **non-principal
exactly on the cross-character pairs** — and those pairs are what buy the `P` (the
fibrewise route pays `φ(q)·P`; see `halasz_primes_chi_fibres`, §3, which lands that route
with the debit exhibited, and the counterexample sketch in its docstring).  So:

  **ROW = free (this file).  SOCKET = the cross-character twisted per-pair stone (residue).**

The residue's interface is pinned byte-exactly in §4 (`TwistedWindowPrice`) together with
the reusable twisted representation layer (§1) it consumes, and the honest numerology of
the ruled height split is recorded below.

## §1 — the reusable layer: the twisted Perron representation (REP-χ)

`lambda_window_rep_chi` is the exact `χ`-twin of `lambda_window_rep`: the REPRESENTATION
layer of `HalaszPrimesCore` (`primeWindow_contour_rep`) is generic in `a : ℕ → ℂ`, so the
character enters only through the coefficient, and the Dirichlet series folds to
`−L′/L(·, χ)` by `Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist` ∘
`Salt.SW.neg_logDeriv_LSeries_eq`.  This is the whole `q = 1`→`q` cost of the W-KER/REP
rungs; TRUNC transfers the same way (the `c`-line price `∑ Λ(n)/nᶜ` is character-blind,
`‖χ(n)‖ ≤ 1`).  **The RES rung vanishes** (`L(·,χ)` is entire for `χ ≠ 1` — the B-probe's
finding) and with it the POLE-ROW: the twisted per-pair estimate has NO main term.

## RULING (i) — the height split, and its honest numerology

The ruled split of the edge legs at the landed floor `E := exp(exp 100) + 1`:

* **above `E`**: stone B (`LFunction_zero_free_region_vk`, `χ² ≠ 1`) or the real arm
  (`LFunction_real_zero_free_region_vk`, `χ² = 1`) gives width
  `(1/(10⁸(A+7)))·1/((log|γ|)^{3/4}(loglog|γ|)³)` under the `q`-gate
  `log(20000·(vkStripConst q + 8104)) ≤ A·loglog|γ|`.  Since `loglog|γ| ≥ 100` above the
  floor, `A` may be taken `≈ log(10⁸·5000q)/100`, so the assembled width carries
  `A + 7` — i.e. `c/((log|γ|)^{3/4}(loglog|γ|)²·(7·loglog|γ| + log q/100))`.  **Absorbing
  that back into the VK shape `(log)^{3/4}(loglog)³` costs the gate**

    `log q ≤ K·loglog(q(5T+1))`  (`K` absolute),

  which at the port's parameters (`q ≤ (log H)^12`, `loglog H ∈ [173, 241]`,
  `T ≍ X`) reads `12·loglog H ≤ K·loglog X` — TRUE at `K ≈ 19`, and TIGHT: it is the
  `(log H)^12` conductor range itself.  This gate is a REAL demand of the split, not a
  bookkeeping artefact, and it is recorded here because ruling (i) predicted the `q`-cost
  would sit "only inside the log" — it does, but the `A`-parameterisation of stones A/B
  moves it into the width's *constant*, and only the gate above puts it back.
* **below `E`**: the classical explicit region `Salt.SW.zero_free_region_all'`
  (`c₀ = 1/126848`, effective, `q`-explicit) gives the fixed width
  `c₀/log(q(|γ|+2)) ≥ c₀/log(q(E+2))`.  Ruling (i)'s "any fixed width beats the needed
  decay" is TRUE but not free: the comparison
  `c_vk/((log(5T+1))^{3/4}(loglog(5T+1))³) ≤ c₀/log(q(E+2))` is a second in-statement
  gate, and it FAILS for `q` astronomically large relative to `T` (at `T` at the floor,
  `(log q)^{3/4}(loglog q)³ < log q` once `log q ≳ 10³⁰`).  At the port's parameters it
  holds with ~30 orders of room.  **The non-effective `logDeriv_Zc_compact_bound` is
  nowhere cited** — that part of the ruling is clean, and is why the split is the right
  design.

Both gates are carried in-statement by `TwistedWindowPrice` (§4) as the region hypothesis,
in the shape stones A/B and `zero_free_region_all'` deliver (instantiate, don't restate).

## RULING (ii) — the rows

* non-principal `χ`: `halasz_primes_chi` (§2) — delivered for ALL `χ`, unconditionally,
  strictly stronger than the ruled carve-out form (see THE FINDING);
* principal `χ`: `halasz_primes_chi_principal` (§2);
* the exceptional real character `ξ₁`: covered by the same row (the row is carve-out-free).
  It is the SOCKET's cross-character stone that needs the Siegel gate — `ψ = χ_r·χ̄_{r'}`
  can BE `ξ₁` — and that is P-7's, per the ruling.

## Scales and conventions (the banked traps)

* the four log scales: `log P`, `log T`, `log(qT)`, `loglog(qT)`.  §2 is at `log T`
  (sharp); `halasz_primes_chi_hybridHeight` weakens it to `log(qT)` — the socket's height,
  and the WEAKER statement (a larger denominator is a smaller decay);
* `σ = 1` sign convention throughout, matching `chiBarCoeff` and
  `USetChi.ramQ_chiBar_eq_halaszSum` (no reflection);
* no `set L := …` (the `LSeries`-notation collision; this file opens the notation);
* `Cq = vkStripConst q = 5000·q` rides through from stone A symbolically.
-/

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-! ## §1 — REP-χ: the twisted Perron representation of the log-weighted window sum

The `χ`-twin of `lambda_window_rep`.  Specialise the generic `primeWindow_contour_rep` to
`aₙ = χ(n)·Λ(n)·n^{iu}`; the twist re-indexes the Dirichlet series to
`LSeries (↗χ * ↗Λ) ((c+it) − iu) = −L′/L((c+it) − iu, χ)`. -/

/-- The `χ`-twisted von Mangoldt series is dominated termwise by the untwisted one:
`‖χ(n)·Λ(n)·n^{iu}‖ ≤ Λ(n)` (`‖χ(n)‖ ≤ 1`, `‖n^{iu}‖ = 1`). -/
lemma norm_chi_vonMangoldt_twist_le {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) (n : ℕ) :
    ‖(χ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I)‖ ≤ vonMangoldt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show (vonMangoldt 0 : ℂ) = 0 by rw [ArithmeticFunction.map_zero]; norm_num]
    simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcp : ‖(n : ℂ) ^ ((u : ℂ) * I)‖ = 1 := by
      rw [← Complex.ofReal_natCast (n := n), Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp
    rw [norm_mul, hcp, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]
    calc ‖χ (n : ZMod q)‖ * vonMangoldt n ≤ 1 * vonMangoldt n :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) vonMangoldt_nonneg
      _ = vonMangoldt n := one_mul _

/-- **REP-χ — the per-`u` twisted Perron representation.**  For `2 ≤ P`, `1 < c`, any twist
`u` and any `χ mod q`, the `χ`-twisted log-weighted window sum has the exact contour
representation

`∑_n χ(n)·Λ(n)·n^{iu}·w(n) = (1/2π)∫ (−L′/L)((c+it) − iu, χ)·windowKernel(P,c,t) dt`.

Rides `primeWindow_contour_rep` (W-KER, generic in the coefficient) plus the twisted
`−L′/L` identity (`Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist` ∘
`Salt.SW.neg_logDeriv_LSeries_eq`).  This is the ENTIRE `q = 1`→`q` cost of the
representation ladder; the RES/POLE-ROW rungs of the `ζ` engine have no twin
(`L(·,χ)` is entire for `χ ≠ 1`). -/
theorem lambda_window_rep_chi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {P c u : ℝ}
    (hP : 2 ≤ P) (hc : 1 < c) :
    ∑' n : ℕ, ((χ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
        * (primeWindow P n : ℂ)
      = (1 / (2 * Real.pi)) • ∫ t : ℝ,
          (- logDeriv (LFunction χ) ((c : ℂ) + (t : ℂ) * I - (u : ℂ) * I))
            * windowKernel P c t := by
  set a : ℕ → ℂ := fun n =>
    (χ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I) with hadef
  have hc0 : (0 : ℝ) < c := by linarith
  have ha0 : a 0 = 0 := by
    rw [hadef]
    simp only
    rw [show (vonMangoldt 0 : ℂ) = 0 by rw [ArithmeticFunction.map_zero]; norm_num]
    ring
  have hnle : ∀ n : ℕ, ‖a n‖ ≤ vonMangoldt n := fun n => by
    rw [hadef]; exact norm_chi_vonMangoldt_twist_le χ u n
  have hsum : Summable (fun n => ‖a n‖ / (n : ℝ) ^ c) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_vonMangoldt_div_rpow hc)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ha0]
      simp
    · have hpos : (0 : ℝ) < (n : ℝ) ^ c :=
        Real.rpow_pos_of_pos (by exact_mod_cast hn) c
      rw [div_le_div_iff_of_pos_right hpos]
      exact hnle n
  rw [show (∑' n : ℕ, ((χ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
        * (primeWindow P n : ℂ)) = ∑' n, a n * (primeWindow P n : ℂ) from rfl,
    primeWindow_contour_rep a ha0 hP hc0 hsum]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  congr 1
  set w : ℂ := (c : ℂ) + (t : ℂ) * I - (u : ℂ) * I with hwdef
  have hwre : 1 < w.re := by rw [hwdef]; simp; linarith
  have hterm : ∀ n : ℕ, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      = LSeries.term (↗χ * ↗vonMangoldt) w n := by
    intro n
    rw [LSeries.term_def₀ (by simp) w n]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ha0]; simp
    · have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      rw [hadef]
      simp only [Pi.mul_apply]
      rw [mul_div_assoc]
      congr 1
      rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hne]
      congr 1
      rw [hwdef]; ring
  have hLS : (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
      = LSeries (↗χ * ↗vonMangoldt) w := tsum_congr hterm
  rw [hLS, ← Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist χ hwre,
    Salt.SW.neg_logDeriv_LSeries_eq χ hwre]

/-! ## §2 — THE ROWS (ruling (ii))

The row statement, for EVERY character mod `q`, from the landed `halasz_primes_pow`.
See THE FINDING in the module docstring: the row is the untwisted engine at the twisted
DATUM, and the twisted zero-free region is not consumed. -/

/-- **STONE C's ROW — `halasz_primes_chi`.**  The `χ`-twisted MR Lemma 11 at the sharp
`log T` height: for every `q > 0`, every `χ mod q`, every `T ≥ T₀`, `2 ≤ P ≤ T^10`, every
well-spaced `𝒯 ⊆ [−T, T]` and every prime-supported `S ⊆ [P, 2P]`,

`∑_{t∈𝒯} ‖∑_{n∈S} n^{−it}·χ̄(n)·aₙ‖²`
`  ≤ C·(P + |𝒯|·P·exp(−c·log P/((log T)^{3/4}(loglog T)⁴))·(log T)²)/log P·∑_{n∈S}‖aₙ‖²`,

with `∃ C c T₀` outermost, the `σ = 1` sign convention, and the `χ̄`-twist carried by
`chiBarCoeff` — the socket's exact datum (`USetChi.HalaszPrimesChi`).

**No carve-out, no `χ ≠ 1` hypothesis, no χ-VK region.**  The twist lives in the
coefficient, `‖χ̄(n)·aₙ‖ ≤ ‖aₙ‖` (`norm_chiBarCoeff_le`), and `halasz_primes_pow` is
monotone in the coefficient mass.  The ruled exceptional disjunction would be a hypothesis
this proof never reads; the strictly stronger unconditional form is delivered instead
(deviation recorded in the module docstring). -/
theorem halasz_primes_chi :
    ∃ (C c T₀ : ℝ), 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧
      ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℂ q),
      ∀ (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
      ∀ (𝒯 : Finset ℝ), WellSpaced 𝒯 → (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ t ∈ 𝒯, ‖∑ n ∈ S, (n : ℂ) ^ (-(t : ℂ) * I) * chiBarCoeff q χ a n‖ ^ 2
          ≤ C * (P + (𝒯.card : ℝ) * P
                * Real.exp (-c * Real.log P
                    / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)))
                * (Real.log T) ^ 2)
            / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hbase⟩ := halasz_primes_pow
  refine ⟨C, c, T₀, hC, hc, hT₀, ?_⟩
  intro q hq χ T P hT hP hPT 𝒯 hws hsub S hS a
  haveI : NeZero q := ⟨hq.ne'⟩
  have hP0 : (0 : ℝ) ≤ P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hrow := hbase T P hT hP hPT 𝒯 hws hsub S hS (chiBarCoeff q χ a)
  refine hrow.trans ?_
  have hpre : (0 : ℝ) ≤ C * (P + (𝒯.card : ℝ) * P
        * Real.exp (-c * Real.log P
            / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)))
        * (Real.log T) ^ 2) / Real.log P := by
    refine div_nonneg ?_ hlogP.le
    have h1 : (0 : ℝ) ≤ (𝒯.card : ℝ) * P
        * Real.exp (-c * Real.log P
            / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)))
        * (Real.log T) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hP0) (Real.exp_pos _).le)
        (sq_nonneg _)
    exact mul_nonneg hC.le (by linarith)
  refine mul_le_mul_of_nonneg_left ?_ hpre
  refine Finset.sum_le_sum (fun n _ => ?_)
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_chiBarCoeff_le χ a n) 2

/-- **The PRINCIPAL row** (ruling (ii)'s second delivery).  `halasz_primes_chi` at
`χ = 1`: the principal character mod `q`.  Note the `p ∣ q` debit that ruling (ii)
anticipated (`neg_re_logDeriv_trivChar_le_zeta`, the `≤ log q` Euler correction) does NOT
arise: `χ̄₀(p) = 0` for `p ∣ q` DELETES those primes from the datum, and deleting terms
only decreases both sides of a monotone-in-mass bound.  The correction is needed only where
the principal character enters through an EULER PRODUCT (the `−L′/L` route), i.e. in the
residue stone of §4, not here. -/
theorem halasz_primes_chi_principal :
    ∃ (C c T₀ : ℝ), 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧
      ∀ (q : ℕ), 0 < q →
      ∀ (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
      ∀ (𝒯 : Finset ℝ), WellSpaced 𝒯 → (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ t ∈ 𝒯, ‖∑ n ∈ S, (n : ℂ) ^ (-(t : ℂ) * I)
              * chiBarCoeff q (1 : DirichletCharacter ℂ q) a n‖ ^ 2
          ≤ C * (P + (𝒯.card : ℝ) * P
                * Real.exp (-c * Real.log P
                    / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)))
                * (Real.log T) ^ 2)
            / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hrow⟩ := halasz_primes_chi
  exact ⟨C, c, T₀, hC, hc, hT₀, fun q hq => hrow q hq (1 : DirichletCharacter ℂ q)⟩

/-! ### The hybrid height `qT`

The socket reads the decay denominator and the `(log)²` factor at the HYBRID height `qT`
(`USetChi.HalaszPrimesChi`), which is the WEAKER statement: `q ≥ 1` gives
`log T ≤ log(qT)`, hence `D(T) ≤ D(qT)` and `exp(−c log P/D(T)) ≤ exp(−c log P/D(qT))`,
and `(log T)² ≤ (log qT)²`.  This is the monotonicity P-7 needs to connect §2 to the
socket's single-fibre content. -/

/-- **The row at the socket's hybrid height.**  `halasz_primes_chi` with the decay
denominator and the `(log)²` factor read at `q·T` instead of `T` — the socket's shape, and
the weaker statement.  `T₀` is raised to `exp(exp 1)` so that `1 ≤ log T` and
`1 ≤ loglog T` (needed for the `loglog` monotonicity step). -/
theorem halasz_primes_chi_hybridHeight :
    ∃ (C c T₀ : ℝ), 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧
      ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℂ q),
      ∀ (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
      ∀ (𝒯 : Finset ℝ), WellSpaced 𝒯 → (∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ t ∈ 𝒯, ‖∑ n ∈ S, (n : ℂ) ^ (-(t : ℂ) * I) * chiBarCoeff q χ a n‖ ^ 2
          ≤ C * (P + (𝒯.card : ℝ) * P
                * Real.exp (-c * Real.log P
                    / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                        * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                * (Real.log ((q : ℝ) * T)) ^ 2)
            / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hrow⟩ := halasz_primes_chi
  refine ⟨C, c, max T₀ (Real.exp (Real.exp 1)), hC, hc,
    le_trans hT₀ (le_max_left _ _), ?_⟩
  intro q hq χ T P hT hP hPT 𝒯 hws hsub S hS a
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTe : Real.exp (Real.exp 1) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos _) hTe
  have hP0 : (0 : ℝ) ≤ P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  -- the two heights
  have hLTe : Real.exp 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) hTe
    rwa [Real.log_exp] at h
  have hLT1 : (1 : ℝ) ≤ Real.log T := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith
  have hLT0 : 0 < Real.log T := by linarith
  have hll1 : (1 : ℝ) ≤ Real.log (Real.log T) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLTe
    rwa [Real.log_exp] at h
  have hqT0 : (0 : ℝ) < (q : ℝ) * T := by positivity
  have hmono : Real.log T ≤ Real.log ((q : ℝ) * T) := by
    apply Real.log_le_log hT0
    nlinarith
  have hLqT1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * T) := by linarith
  have hllmono : Real.log (Real.log T) ≤ Real.log (Real.log ((q : ℝ) * T)) :=
    Real.log_le_log hLT0 hmono
  have hll1' : (1 : ℝ) ≤ Real.log (Real.log ((q : ℝ) * T)) := by linarith
  -- the denominators
  have hD1pos : 0 < (Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ) := by
    have h1 : 0 < (Real.log T) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hLT0 _
    have h2 : 0 < (Real.log (Real.log T)) ^ (4 : ℕ) := by positivity
    exact mul_pos h1 h2
  have hDle : (Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)
      ≤ (Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ) := by
    have h1 : (Real.log T) ^ ((3 : ℝ) / 4) ≤ (Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hLT0.le hmono (by norm_num)
    have h2 : (Real.log (Real.log T)) ^ (4 : ℕ)
        ≤ (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ) :=
      pow_le_pow_left₀ (by linarith) hllmono 4
    have h3 : (0 : ℝ) ≤ (Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4) :=
      le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
    exact mul_le_mul h1 h2 (by positivity) h3
  have hD2pos : 0 < (Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ) := lt_of_lt_of_le hD1pos hDle
  -- the decay comparison
  have hexpmono : Real.exp (-c * Real.log P
        / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)))
      ≤ Real.exp (-c * Real.log P
        / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ))) := by
    apply Real.exp_le_exp.mpr
    have hnum : 0 < c * Real.log P := mul_pos hc hlogP
    have hdiv : c * Real.log P
          / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ))
        ≤ c * Real.log P
          / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)) := by
      apply div_le_div_of_nonneg_left hnum.le hD1pos hDle
    have e1 : -c * Real.log P
        / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ))
        = -(c * Real.log P
          / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ))) := by ring
    have e2 : -c * Real.log P
        / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ))
        = -(c * Real.log P
          / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ))) := by ring
    rw [e1, e2]
    exact neg_le_neg hdiv
  have hsqmono : (Real.log T) ^ 2 ≤ (Real.log ((q : ℝ) * T)) ^ 2 :=
    pow_le_pow_left₀ hLT0.le hmono 2
  refine (hrow q hq χ T P hTT₀ hP hPT 𝒯 hws hsub S hS a).trans ?_
  have hM0 : (0 : ℝ) ≤ ∑ n ∈ S, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ hM0
  refine div_le_div_of_nonneg_right ?_ hlogP.le
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  have hcard0 : (0 : ℝ) ≤ (𝒯.card : ℝ) := by positivity
  have hstep : (𝒯.card : ℝ) * P
        * Real.exp (-c * Real.log P
            / ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)))
        * (Real.log T) ^ 2
      ≤ (𝒯.card : ℝ) * P
        * Real.exp (-c * Real.log P
            / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
        * (Real.log ((q : ℝ) * T)) ^ 2 := by
    have hA : (0 : ℝ) ≤ (𝒯.card : ℝ) * P := mul_nonneg hcard0 hP0
    exact mul_le_mul (mul_le_mul_of_nonneg_left hexpmono hA) hsqmono (sq_nonneg _)
      (mul_nonneg hA (Real.exp_pos _).le)
  linarith

/-! ## §3 — THE FIBRE ROUTE toward the socket, with the debit exhibited

`USetChi.HalaszPrimesChi` sums over a per-fibre-well-spaced set of PAIRS and asks for the
diagonal term `P`.  Splitting `ℰ` into character fibres (`exists_charFibre`) and applying
§2's row per fibre gives everything EXCEPT that: the `P` becomes
`#(characters mod q)·P`.  This section lands that route exactly, so the gap is a
kernel-checked statement rather than a claim.

**Why the debit is not removable fibrewise.**  Take `S` = all primes in `[P, 2P]`,
`a_p = 1`, and `ℰ = {(χ, 0) : χ mod q}`.  Then `|ℰ| = φ(q)` and, by orthogonality,
`∑_χ |∑_{p∈S} χ̄(p)|² = φ(q)·∑_{(cₐ,q)=1} |#{p ∈ S : p ≡ cₐ}|² ≍ π(P)²/1` — matching the
socket's `C·P/log P·∑‖a_p‖² ≍ P·π(P)/log P`, with NO room for a `φ(q)`.  The saving is
bought by the CROSS-CHARACTER pairs `(χ, χ')`, `χ ≠ χ'`, whose per-pair sum is the
`ψ = χ·χ̄′`-twisted prime sum with `ψ` NON-PRINCIPAL — the residue stone of §4. -/

/-- **The fibre route (§3).**  The `(χ, t)`-pair form of the row: for a per-fibre
well-spaced `ℰ ⊆ (characters mod q) × [−T, T]`,

`∑_{(χ,t)∈ℰ} ‖∑_{n∈S} n^{−it}·χ̄(n)·aₙ‖²`
`  ≤ C·(#chars·P + |ℰ|·P·exp(−c log P/D(qT))·(log qT)²)/log P·∑_{n∈S}‖aₙ‖²`.

This is `USetChi.HalaszPrimesChi`'s conclusion with `P` replaced by
`Fintype.card (DirichletCharacter ℂ q) · P` — the HONEST fibrewise debit (`= φ(q)`).
Everything else matches byte-for-byte, including the hybrid height `qT`.  The socket
therefore reduces exactly to: *delete the character count on the diagonal term*, which is
the cross-character estimate of §4. -/
theorem halasz_primes_chi_fibres :
    ∃ (C c T₀ : ℝ), 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧
      ∀ (q : ℕ), 0 < q → ∀ (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * ((Fintype.card (DirichletCharacter ℂ q) : ℝ) * P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hrow⟩ := halasz_primes_chi_hybridHeight
  refine ⟨C, c, T₀, hC, hc, hT₀, ?_⟩
  intro q hq T P hT hP hPT ℰ hws hsub S hS a
  obtain ⟨𝒯, hmem, hfsum⟩ := exists_charFibre ℰ
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  set E : ℝ := Real.exp (-c * Real.log P
      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ))) with hEdef
  set Lsq : ℝ := (Real.log ((q : ℝ) * T)) ^ 2 with hLsqdef
  set M : ℝ := ∑ n ∈ S, ‖a n‖ ^ 2 with hMdef
  -- the fibre cardinalities add up
  have hcard : ∑ _χ : DirichletCharacter ℂ q, ((𝒯 _χ).card : ℝ) = (ℰ.card : ℝ) := by
    have h := hfsum (fun _ _ => (1 : ℝ))
    simpa using h
  -- regroup the left-hand side over fibres
  rw [← hfsum (fun χ t => ‖∑ n ∈ S, (n : ℂ) ^ (-(t : ℂ) * I) * chiBarCoeff q χ a n‖ ^ 2)]
  have hper : ∀ χ : DirichletCharacter ℂ q,
      ∑ t ∈ 𝒯 χ, ‖∑ n ∈ S, (n : ℂ) ^ (-(t : ℂ) * I) * chiBarCoeff q χ a n‖ ^ 2
        ≤ C * (P + ((𝒯 χ).card : ℝ) * P * E * Lsq) / Real.log P * M := by
    intro χ
    refine hrow q hq χ T P hT hP hPT (𝒯 χ) ?_ ?_ S hS a
    · intro t ht u hu htu
      exact hws (χ, t) ((hmem χ t).1 ht) (χ, u) ((hmem χ u).1 hu) rfl htu
    · intro t ht; exact hsub (χ, t) ((hmem χ t).1 ht)
  refine (Finset.sum_le_sum (fun χ _ => hper χ)).trans (le_of_eq ?_)
  have hexpand : ∀ χ : DirichletCharacter ℂ q,
      C * (P + ((𝒯 χ).card : ℝ) * P * E * Lsq) / Real.log P * M
        = (C * P / Real.log P * M) + (C * P * E * Lsq / Real.log P * M) * ((𝒯 χ).card : ℝ) := by
    intro χ; field_simp
  rw [Finset.sum_congr rfl (fun χ _ => hexpand χ), Finset.sum_add_distrib, Finset.sum_const,
    ← Finset.mul_sum, hcard, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-! ## §4 — RULING (i): THE HEIGHT SPLIT, assembled

The one piece of ruling (i) that is pure region arithmetic — and therefore landable here —
is the SPLIT itself: a single VK-shaped zero-free rectangle for `L(·,ψ)` over the WHOLE
contour height range `|Im ρ| ≤ 5T + 1`, glued from

* **above** the landed floor `E := exp(exp 100) + 1`: stone B
  (`LFunction_zero_free_region_vk`, `ψ² ≠ 1`) or the real arm
  (`LFunction_real_zero_free_region_vk`, `ψ² = 1`), and
* **below** `E`: the classical effective region `Salt.SW.zero_free_region_all'`
  (`c₀ = 1/126848`), whose width at bounded height is `c₀/log(q(E+2))` — a constant in `T`.

`logDeriv_Zc_compact_bound` is nowhere cited (it is a `ζ`-side object anyway; the point of
the split is that no non-effective input is used).

**The two gates, honestly.**  Stones A/B are `A`-parameterised: the `q`-scale gate
`log(20000·(vkStripConst q + 8104)) ≤ A·loglog|Im ρ|` buys the width
`(1/(10⁸(A+7)))·1/((log|Im ρ|)^{3/4}(loglog|Im ρ|)³)`.  Above the floor `loglog|Im ρ| ≥ 100`,
so `hAq` below is the gate at its worst point.  Turning the `A`-dependent width into an
absolute constant costs the ABSORPTION gate

  `A + 7 ≤ loglog(5T+1)`,

which trades the `(loglog)³` region shape for `(loglog)⁴` — and `(loglog)⁴` is EXACTLY the
socket's shape (`USetChi.HalaszPrimesChi` reads `(log qT)^{3/4}(loglog qT)⁴`), so the trade
is free downstream.  The below-floor comparison costs

  `Kq·log(q(exp(exp 100)+3)) ≤ (log(5T+1))^{3/4}(loglog(5T+1))⁴`,   `Kq = 1/(10⁸c₀)`.

At the port's parameters (`q ≤ (log H)^12`, `loglog H ∈ [173, 241]`, `T ≍ X`) the first gate
reads `log(10⁸·5000q)/100 + 7 ≲ 31 ≤ loglog X ≈ 200` and the second has ~30 orders of room.
Both are recorded in-statement; neither is absorbable into a constant (the first fails for
`log q ≳ 9300`, the second for `q` astronomically large in `T`), which corrects ruling (i)'s
"the constant absorbing the below-floor corner".

**The carve-out** is exactly `zero_free_region_all'`'s, and ONLY below the floor: a real
character's real zero of height `≤ E` with `Re ρ ≥ 1/2` is Siegel territory.  Above the
floor the real arm needs nothing (the conjugate-zero case is vacuous at `|γ| ≥ 2`).  This is
the ruled dispatch structure, instantiated rather than restated. -/

/-- Above the landed height floor, `loglog|γ| ≥ 100`. -/
lemma loglog_ge_hundred {γ : ℝ} (hγ : Real.exp (Real.exp 100) + 1 ≤ |γ|) :
    (100 : ℝ) ≤ Real.log (Real.log |γ|) := by
  have hE : Real.exp (Real.exp 100) ≤ |γ| := by
    have := Real.exp_pos (Real.exp 100); linarith
  have h2 : Real.exp 100 ≤ Real.log |γ| := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 100)) hE
    rwa [Real.log_exp] at h
  have h3 := Real.log_le_log (Real.exp_pos 100) h2
  rwa [Real.log_exp] at h3

/-- Monotonicity of the VK denominator `(log γ)^{3/4}(loglog γ)ⁿ` in the height. -/
lemma logDn_mono (n : ℕ) {γ₁ γ₂ : ℝ} (h1 : Real.exp 1 ≤ γ₁) (h12 : γ₁ ≤ γ₂) :
    (Real.log γ₁) ^ ((3 : ℝ) / 4) * (Real.log (Real.log γ₁)) ^ n
      ≤ (Real.log γ₂) ^ ((3 : ℝ) / 4) * (Real.log (Real.log γ₂)) ^ n := by
  have hγ1pos : 0 < γ₁ := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hL1 : (1 : ℝ) ≤ Real.log γ₁ := by
    have h := Real.log_le_log (Real.exp_pos 1) h1; rwa [Real.log_exp] at h
  have hL1pos : 0 < Real.log γ₁ := by linarith
  have hLle : Real.log γ₁ ≤ Real.log γ₂ := Real.log_le_log hγ1pos h12
  have hll : Real.log (Real.log γ₁) ≤ Real.log (Real.log γ₂) := Real.log_le_log hL1pos hLle
  have hA : (Real.log γ₁) ^ ((3 : ℝ) / 4) ≤ (Real.log γ₂) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hL1pos.le hLle (by norm_num)
  refine mul_le_mul hA (pow_le_pow_left₀ (Real.log_nonneg hL1) hll n)
    (pow_nonneg (Real.log_nonneg hL1) n) ?_
  exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)

/-- **RULING (i) LANDED — the assembled twisted zero-free rectangle.**  For every `q > 0`,
every `ψ mod q` with `ψ ≠ 1`, every `A ≥ 1` and every `T ≥ exp(exp 100)` satisfying the two
gates, and under the Siegel carve-out below the floor, EVERY zero of `L(·,ψ)` in the contour
box `|Im ρ| ≤ 5T + 1` obeys

  `Re ρ ≤ 1 − (1/10⁸)/((log(5T+1))^{3/4}·(loglog(5T+1))⁴)`.

Uniform in the height (the `T`-shape, not the `|Im ρ|`-shape) — which is what a contour
argument consumes — with an ABSOLUTE constant `1/10⁸`, no non-effective input, and the
`(loglog)⁴` shape the socket already reads. -/
theorem twisted_rect_zero_free_split :
    ∃ Kq : ℝ, 0 < Kq ∧
      ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ (A T : ℝ), 1 ≤ A →
      Real.exp (Real.exp 100) ≤ T →
      Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 →
      A + 7 ≤ Real.log (Real.log (5 * T + 1)) →
      Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
          ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
      (∀ ρ : ℂ, LFunction ψ ρ = 0 → 1 / 2 ≤ ρ.re →
          |ρ.im| ≤ Real.exp (Real.exp 100) + 1 →
          (ψ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0)) →
      ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - (1 / 10 ^ 8)
          / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := Salt.SW.zero_free_region_all'
  refine ⟨1 / (10 ^ 8 * c₀), by positivity, ?_⟩
  intro q hNe ψ hψ1 A T hA1 hTfloor hAq hAabs hKq hcarve ρ hρ0 hρim
  -- the `T`-scale quantities
  have hE0 : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hE0 hTfloor
  have h5T : Real.exp (Real.exp 100) ≤ 5 * T + 1 := by linarith
  have h5T0 : (0 : ℝ) < 5 * T + 1 := by linarith
  have hLg100 : Real.exp 100 ≤ Real.log (5 * T + 1) := by
    have h := Real.log_le_log hE0 h5T; rwa [Real.log_exp] at h
  have hexp100 : (1 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  have hLg1 : (1 : ℝ) ≤ Real.log (5 * T + 1) := by linarith
  have hLg0 : 0 < Real.log (5 * T + 1) := by linarith
  have hℓ100 : (100 : ℝ) ≤ Real.log (Real.log (5 * T + 1)) := by
    have h := Real.log_le_log (Real.exp_pos 100) hLg100; rwa [Real.log_exp] at h
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log (5 * T + 1)) := by linarith
  set Lg : ℝ := Real.log (5 * T + 1) with hLgdef
  set ℓ : ℝ := Real.log (Real.log (5 * T + 1)) with hℓdef
  have hLg34 : (1 : ℝ) ≤ Lg ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLg1 (by norm_num)
  have hLg34pos : 0 < Lg ^ ((3 : ℝ) / 4) := by linarith
  have hD3pos : 0 < Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) := by positivity
  have hD4pos : 0 < Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by positivity
  have hD4ge1 : (1 : ℝ) ≤ Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ℓ ^ (4 : ℕ) := one_le_pow₀ hℓ1
    nlinarith
  -- the target width is tiny
  have hWsmall : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hD4pos (by norm_num : (0:ℝ) < 2)]
    nlinarith
  by_cases hcase : Real.exp (Real.exp 100) + 1 ≤ |ρ.im|
  · -- ABOVE the floor: stones A+B
    have hβ1 : ρ.re < 1 := by
      by_contra hge
      exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (by linarith [not_lt.mp hge]) hρ0
    have hℓγ100 : (100 : ℝ) ≤ Real.log (Real.log |ρ.im|) := loglog_ge_hundred hcase
    have hgate : Real.log (20000 * (vkStripConst q + 8104))
        ≤ A * Real.log (Real.log |ρ.im|) := by
      have : A * 100 ≤ A * Real.log (Real.log |ρ.im|) :=
        mul_le_mul_of_nonneg_left hℓγ100 (by linarith)
      linarith
    -- the two arms deliver the same D₃-shaped width at the zero's own height
    have hstone : ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 7)))
        * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
      by_cases hsq : ψ ^ 2 = 1
      · refine LFunction_real_zero_free_region_vk hψ1 hsq hA1 hρ0 hβ1 hcase ?_
        exact hgate
      · refine LFunction_zero_free_region_vk hψ1 hsq hA1 hρ0 hβ1 hcase ?_
        have hvk : (1 : ℝ) ≤ vkStripConst q := one_le_vkStripConst
        exact le_trans (Real.log_le_log (by linarith) (by linarith)) hgate
      -- (both arms take the SAME gate: `vkStripConst q ≤ vkStripConst q + 8104`)
    -- compare the two widths
    have hEexp1 : Real.exp 1 ≤ |ρ.im| := by
      have h1 : Real.exp 1 ≤ Real.exp (Real.exp 100) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hmono := logDn_mono 3 hEexp1 hρim
    have hDγpos : 0 < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ) := by
      have hL1 : (1 : ℝ) ≤ Real.log |ρ.im| := by
        have h := Real.log_le_log (Real.exp_pos 1) hEexp1; rwa [Real.log_exp] at h
      have h1 : 0 < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4) :=
        Real.rpow_pos_of_pos (by linarith) _
      have h2 : 0 < (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ) := by positivity
      exact mul_pos h1 h2
    have hstep1 : (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
        ≤ (1 / (10 ^ 8 * (A + 7)) : ℝ)
          * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact one_div_le_one_div_of_le hDγpos hmono
    have hstep2 : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
        ≤ (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by
      have hA7 : (0 : ℝ) < A + 7 := by linarith
      have hL : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
          = 1 / (10 ^ 8 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))) := by rw [div_div]
      have hR : (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
          = 1 / (10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by
        rw [div_mul_div_comm, one_mul]
      have hden : (0 : ℝ) < 10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) :=
        mul_pos (mul_pos (by norm_num) hA7) hD3pos
      have hkey : (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
          ≤ Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by
        calc (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
            ≤ ℓ * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) :=
              mul_le_mul_of_nonneg_right hAabs hD3pos.le
          _ = Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by ring
      rw [hL, hR]
      refine one_div_le_one_div_of_le hden ?_
      calc 10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
          = 10 ^ 8 * ((A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by ring
        _ ≤ 10 ^ 8 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by linarith [hkey]
    linarith [hstone, hstep1, hstep2]
  · -- BELOW the floor: the classical effective region
    rw [not_le] at hcase
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
    · have hcv := hcarve ρ hρ0 hre hcase.le
      have hcl := hc₀ q ψ hψ1 hρ0 hre hcv
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
        have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
      have hEq : |ρ.im| + 2 ≤ Real.exp (Real.exp 100) + 3 := by linarith
      have hlow0 : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
        apply Real.log_pos; nlinarith [abs_nonneg ρ.im]
      have hlowle : Real.log ((q : ℝ) * (|ρ.im| + 2))
          ≤ Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
        apply Real.log_le_log (by nlinarith [abs_nonneg ρ.im])
        exact mul_le_mul_of_nonneg_left hEq (by linarith)
      have hlowE0 : 0 < Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
        linarith
      -- the gate converts the fixed classical width into the VK-shaped one
      have hkey : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
          ≤ c₀ / Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
        rw [div_le_div_iff₀ hD4pos hlowE0]
        have hgate' : Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ 10 ^ 8 * c₀ * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by
          have h := hKq
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h
          linarith
        nlinarith [hgate']
      have hshrink : c₀ / Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
          ≤ c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
        rw [div_le_div_iff₀ hlowE0 hlow0]
        exact mul_le_mul_of_nonneg_left hlowle hc₀0.le
      linarith [hcl, hkey, hshrink]
    · linarith [hWsmall, hre]

/-! ## §5 — THE RESIDUE, pinned: the cross-character twisted per-pair price

What §3 leaves is ONE analytic statement — the `ζ`-engine's `per_pair_contour`
(`HalaszPrimesCore.lean:2403`) with

* the coefficient twisted by a NON-PRINCIPAL `ψ mod q` (`ψ = χ·χ̄′` on a cross-character
  pair), and
* the pole term DELETED (`L(·,ψ)` is entire for `ψ ≠ 1`: RES and POLE-ROW have no twin),

under the region hypothesis that §4 now SUPPLIES.  `TwistedWindowPrice` below is that
statement, and its region hypothesis `hreg` is byte-exactly the conclusion of
`twisted_rect_zero_free_split` (it is antitone in `c_vk`, so the split's `1/10⁸` discharges
it at any smaller constant): instantiate, don't restate.

The shapes: the contour DEPTH is the region width, i.e. `D₄ = Lg^{3/4}ℓ⁴` at `Lg =
log(5T+1)` (the split's shape — one `loglog` coarser than `ζ`'s `D₃`, the price of the
`A`-absorption), and the EDGE price carries one further `loglog`, `D₅ = Lg^{3/4}ℓ⁵`, exactly
as the `ζ` engine's price carries `D₄` against its depth `D₃`.  Downstream this is free: the
socket already reads `(loglog qT)⁴`, and the `D₄(5T+1) → D₄(T)` absorption is the landed
`D4_5T1_le` machinery.

**What is missing is exactly one leg**: the twisted EDGE, i.e. an upper bound for
`‖L′/L(x+iγ, ψ)‖` on the near-1-line strip inside the split's rectangle.  The corpus has the
Landau/Borel–Carathéodory apparatus (`Salt.SW.landau_neg_logDeriv_re_lower`,
`three_four_one`, `LFunction_norm_logDeriv_sub_sum`) and now the REGION, but no such bound
(`ChiFloorLow.lean`'s census (a) records the same absence on the `‖L‖`-lower side).  The
`ζ`-side twin is `shifted_edge_disc_core`/`shifted_edge_price_strip` (~900 lines).

Consuming `TwistedWindowPrice` then needs the `(χ,t)`-pair twin of `dual_core`: the
fibre-split pole row — the `44π·P` mass is paid ONCE per fibre by `pole_row_sum` on the
`FibreWellSpaced` fibres, while every cross-character row goes into the `error_double_row`
slot — which is why the diagonal comes out `P` and not `φ(q)·P`.  That pairing plus the
`p ∣ q` Euler debit on the diagonal fibres (`neg_re_logDeriv_trivChar_le_zeta`, `≤ log q`)
is P-7's assembly. -/

/-- **THE RESIDUE INTERFACE — the cross-character twisted per-pair price.**  The `ψ`-twisted
twin of `per_pair_contour` with NO pole term, under the height-split region hypothesis that
`twisted_rect_zero_free_split` supplies.  `∃ c_vk C₁ C₂ C₃ T₀` outermost, as in the `ζ`
engine.  Recorded as a `def` so that P-7 consumes a fixed interface; the missing leg is the
twisted EDGE (see the section docstring). -/
def TwistedWindowPrice (c_vk C₁ C₂ C₃ T₀ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 →
  ∀ (T P u : ℝ), T₀ ≤ T → 2 ≤ P → |u| ≤ 2 * T →
    (∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))) →
    ‖∑' n : ℕ, ((ψ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
          * (primeWindow P n : ℂ)‖
      ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P
              / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)))
            * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ))
        + C₂ * P * Real.log P / T
        + C₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)) * P / T ^ 2

end Salt.MR
