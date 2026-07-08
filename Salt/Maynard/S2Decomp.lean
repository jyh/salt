/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.DiagonalS2
import Salt.Maynard.CongCount

/-!
# N5.1 — the S₂^(m) decomposition (prime-side ↔ diagonalised form)

This file connects the prime-counting side of Maynard's sieve to the S₂
diagonalisation `s2_diagonalisation` (N2.5) and the EH error `eh_error_small`
(N5.2).

## The object

`S₂^(m)` is `∑_n [n + hₘ prime] · w(n)` over the window `(N, K₀N]` with
`n ≡ ν₀ (mod W k)`, where `w(n) = (∑_d λ_d [∀i dᵢ ∣ n+hᵢ])²` is the Maynard
sieve weight. Expanding the square turns this into a double sum over the
sieve support `𝒟 × 𝒟`:

  `S₂^(m) = ∑_{d,e ∈ 𝒟} λ_d λ_e · #{n ∈ (N,K₀N] : n ≡ ν₀ (W k),
              n+hₘ prime, ∀i lcm(dᵢ,eᵢ) ∣ n+hᵢ}`.

The prime condition on `n + hₘ` forces the coordinate `m` moduli to collapse
(`lcm(dₘ,eₘ) ∣ n+hₘ` with `n+hₘ` a prime larger than any coordinate forces
`dₘ = eₘ = 1`); hence only pairs with `dₘ = eₘ = 1` contribute. We take that
`dₘ = eₘ = 1`-guarded double sum, with the joint prime count `s2PrimeCount`,
as the definition `s2Form` of `S₂^(m)`.

## What this file DELIVERS (sorry-free)

* `s2PrimeCount` — the joint prime count (the `congCountTuple` analogue with a
  prime indicator on coordinate `m`).
* `s2Form` / `s2FormMain` / `s2FormErr` — the object, its main term (density
  `Δπ/(φ(W k)·∏φ(lcm))` per pair), and the error term (count minus density).
* **`s2_decomp`** — the exact decomposition `s2Form = s2FormMain + s2FormErr`.
* **`s2Main_factor`** — `s2FormMain = (Δπ/φ(W k)) · Q_m`, where
  `Q_m = ∑_{d,e: dₘ=eₘ=1} λ_d λ_e / ∏φ(lcm)` is the `rₘ = 1` restriction of the
  quadratic form whose *unrestricted* value `s2_diagonalisation` (N2.5)
  evaluates to `∑_r y_r² / ∏ g(rᵢ)`.  This exhibits the main term as
  proportional to the (restricted) N2.5 diagonalisation RHS.
* **`s2Error_abs_le`** — `|s2FormErr| ≤ ∑_{d,e: dₘ=eₘ=1} |λ_d||λ_e|·|count − density|`,
  reducing the error to a sum of per-pair prime-count discrepancies.

The decomposition and the two reductions are genuine, non-vacuous identities:
`s2FormMain` is separately meaningful (a fixed multiple of the restricted
diagonalisation form), and each summand of the `s2Error_abs_le` bound is a
prime-count-in-progression discrepancy — exactly the quantity N5.2 controls.

## What remains (two precise PORT-BLOCKERs — see end of file)

* **P1 (restricted diagonalisation).** `Q_m = ∑_{r ∈ 𝒟, rₘ = 1} y_r² / ∏ g(rᵢ)`
  — the `rₘ = 1` analogue of `s2_diagonalisation`, requiring the N2.5 kernel
  argument re-run with coordinate `m` pinned to the single divisor `1`.
* **P2 (prime-count discrepancy).** `|s2PrimeCount − Δπ/(φ(W k)·∏φ(lcm))| ≤
  2·maxDiscrepancy` at the combined modulus `Q = W k·∏ lcm(dᵢ,eᵢ)` — the
  prime analogue of `congCountTuple_approx` (CRT-fold the `k+1` congruences and
  the prime shift into one reduced residue class mod `Q`, identify the count
  with a `primesCount` difference, and bound its deviation from `Δπ/φ(Q)`).
  Summed over `(d,e)` with the `(3k)^{ω(q)}` multiplicity this feeds
  `eh_error_small` (N5.2).
-/

namespace Salt.Maynard

open Finset

/-! ## The joint prime count -/

/-- The count of `n ∈ (N, K₀N]` with `n ≡ ν₀ (mod W k)`, with `n + hSeq k m`
prime, and with `lcm(dᵢ,eᵢ) ∣ n + hSeq k i` for every coordinate `i`.  This is
`congCountTuple` with the extra prime indicator on coordinate `m`. -/
noncomputable def s2PrimeCount (k K₀ N ν₀ : ℕ) (m : Fin k) (d e : Fin k → ℕ) : ℕ :=
  ((Finset.Ioc N (K₀ * N)).filter
    (fun n => n % W k = ν₀ % W k ∧ (n + hSeq k m).Prime ∧
      ∀ i, Nat.lcm (d i) (e i) ∣ (n + hSeq k i))).card

/-- The per-pair `φ`-of-`lcm` product `∏ᵢ φ(lcm(dᵢ,eᵢ))`, over `ℝ` — the
denominator of the S₂ quadratic form (matches `s2_diagonalisation`). -/
noncomputable def phiLcmProd {k : ℕ} (d e : Fin k → ℕ) : ℝ :=
  ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)

/-! ## The object, its main term, and its error term

`Δπ : ℝ` is the window prime-difference `π(K₀N+hₘ) − π(N+hₘ)`, carried as a
parameter (the identities below are exact in it).  The per-pair main density is
`Δπ / (φ(W k) · phiLcmProd d e)`; over reduced residues mod the combined modulus
`W k · ∏ lcm` this is the expected joint prime count (P2). -/

/-- `S₂^(m)`, in expanded (sieve-square) form: the `dₘ = eₘ = 1`-guarded double
sum of `λ_d λ_e ·` (joint prime count). -/
noncomputable def s2Form (k R K₀ N ν₀ : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
    (if d m = 1 ∧ e m = 1 then
      lamG k R (W k) y d * lamG k R (W k) y e * (s2PrimeCount k K₀ N ν₀ m d e : ℝ)
     else 0)

/-- The main term: the joint prime count replaced by its expected density
`Δπ / (φ(W k) · ∏φ(lcm))`. -/
noncomputable def s2FormMain (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (deltaPi : ℝ) : ℝ :=
  ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
    (if d m = 1 ∧ e m = 1 then
      lamG k R (W k) y d * lamG k R (W k) y e *
        (deltaPi / ((Nat.totient (W k) : ℝ) * phiLcmProd d e))
     else 0)

/-- The error term: the joint prime count minus its expected density. -/
noncomputable def s2FormErr (k R K₀ N ν₀ : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (deltaPi : ℝ) : ℝ :=
  ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
    (if d m = 1 ∧ e m = 1 then
      lamG k R (W k) y d * lamG k R (W k) y e *
        ((s2PrimeCount k K₀ N ν₀ m d e : ℝ)
          - deltaPi / ((Nat.totient (W k) : ℝ) * phiLcmProd d e))
     else 0)

/-! ## The decomposition -/

/-- **N5.1 — the S₂^(m) decomposition.** `S₂^(m) = main + error`, an exact
identity: the joint prime count splits as `density + (count − density)`. -/
theorem s2_decomp (k R K₀ N ν₀ : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (deltaPi : ℝ) :
    s2Form k R K₀ N ν₀ m y
      = s2FormMain k R m y deltaPi + s2FormErr k R K₀ N ν₀ m y deltaPi := by
  unfold s2Form s2FormMain s2FormErr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  split_ifs with h <;> ring

/-- **The main term is proportional to the (restricted) N2.5 diagonalisation.**
`s2FormMain = (Δπ / φ(W k)) · Q_m` with
`Q_m = ∑_{d,e: dₘ=eₘ=1} λ_d λ_e / ∏φ(lcm)`.  Dropping the `dₘ=eₘ=1` guard,
`Q_m` is the LHS of `s2_diagonalisation`, whose value is `∑_r y_r²/∏g(rᵢ)`;
restricting to `rₘ=1` is P1 below. -/
theorem s2Main_factor (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ) (deltaPi : ℝ) :
    s2FormMain k R m y deltaPi
      = deltaPi / (Nat.totient (W k) : ℝ) *
          ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
            (if d m = 1 ∧ e m = 1 then
              lamG k R (W k) y d * lamG k R (W k) y e / phiLcmProd d e
             else 0) := by
  unfold s2FormMain
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  split_ifs with h <;> ring

/-- **The error term is a sum of per-pair prime-count discrepancies.**
`|s2FormErr| ≤ ∑_{d,e: dₘ=eₘ=1} |λ_d| |λ_e| · |count − density|`. Each summand
is a `primesCount`-in-progression discrepancy — the quantity `eh_error_small`
(N5.2) bounds after the P2 reduction. -/
theorem s2Error_abs_le (k R K₀ N ν₀ : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (deltaPi : ℝ) :
    |s2FormErr k R K₀ N ν₀ m y deltaPi|
      ≤ ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
          (if d m = 1 ∧ e m = 1 then
            |lamG k R (W k) y d| * |lamG k R (W k) y e| *
              |(s2PrimeCount k K₀ N ν₀ m d e : ℝ)
                - deltaPi / ((Nat.totient (W k) : ℝ) * phiLcmProd d e)|
           else 0) := by
  unfold s2FormErr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun d _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun e _ => ?_)
  split_ifs with h
  · rw [abs_mul, abs_mul]
  · rw [abs_zero]

/-! ## PORT-BLOCKERs

**P1 — restricted diagonalisation.** With the `dₘ = eₘ = 1` guard,
`∑_{d,e} λ_d λ_e / ∏φ(lcm) = ∑_{r ∈ 𝒟, rₘ = 1} y_r² / ∏ g(rᵢ)`.  This is the
`rₘ = 1` analogue of `s2_diagonalisation`; the coordinate-`m` kernel collapse
`kernelG` degenerates (only the divisor `1` is summed there), so the tensor
argument in `kernelKG`/`s2_diagonalisation` must be re-run coordinate-by-
coordinate with `m` special-cased. Not attempted here (a full re-derivation of
the ~170-line N2.5 proof under the restriction). `s2Main_factor` isolates
exactly this quadratic form.

**P2 — prime-count discrepancy.**
`|(s2PrimeCount k K₀ N ν₀ m d e : ℝ) − Δπ/(φ(W k)·phiLcmProd d e)| ≤
  2·maxDiscrepancy (K₀·N + hSeq k m) Q` with `Q = W k · ∏ᵢ lcm(dᵢ,eᵢ)`.
Route (prime analogue of `congCountTuple_approx`): CRT-fold the `k+1`
congruences `n ≡ ν₀ (W k)` and `lcm(dᵢ,eᵢ) ∣ n+hᵢ` (with `dₘ=eₘ=1` making the
`m`-coordinate trivial) into a single class `p ≡ a (mod Q)` for the prime
`p = n + hₘ`; the counted `p` are `> Q` so `a` is coprime to `Q`; then
`s2PrimeCount = primesCount(K₀N+hₘ; Q, a) − primesCount(N+hₘ; Q, a)`, whose
deviation from `Δπ/φ(Q) = Δπ/(φ(W k)·∏φ(lcm))` is `≤ 2·maxDiscrepancy` at the
two endpoints (`φ(Q) = φ(W k)·∏φ(lcm)` by coprimality). Summing the
`s2Error_abs_le` bound over `(d,e)`, reorganised by the modulus `q ∣ Q` with the
`(3k)^{ω(q)}` divisor multiplicity, is bounded by the `eh_error_small` (N5.2)
sum. Not attempted here — this is the prime-side/sieve interface, the genuine
C-content of N5.1. -/

end Salt.Maynard
