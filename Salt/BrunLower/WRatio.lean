/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs

/-!
# The W-ratio bound (2.16) and its `Σ ω(p)/p` corollary (blueprint `p0`, node B3b)

Discharges the two density inputs that H-R's Théorème 2 proof consumes but that the
`p0.md` freeze had folded into the abstract carriers `Wr`, `ps` of node B3
(`Salt/BrunLower/MainTerm.lean`), see `flags.md` catch #18:

* **(2.16)** the density-ratio bound `W(z_n)/W(z) ≤ e^{2nλ}`  (H-R p.104–106);
* the per-block prime-sum `Σ_{z_n ≤ p < z} ω(p)/p ≤ 2nλ`, which H-R derive *from* (2.16).

`Halberstam–Richert, "A new look at Brun's sieve", Mém. SMF 25 (1971) 97–106`
(numdam `10.24033/msmf.39`).

## The concrete carriers (what B5 instantiates B3's `Wr`/`ps` with)

For a `BoundingSieve s`, the ladder `zLev Lam z` (B0) and a level `n`, the *window*
`[z_n, z)` is the set of sifting primes `p ∣ prodPrimes` with `z_n ≤ p` (all sifting
primes are `< z`, so this is exactly `[z_n, z)`):

* `windowPrimes s Lam z n = {p ∈ prodPrimes.primeFactors : z_n ≤ p}`;
* `windowSum  s Lam z n = Σ_{p ∈ window} ν(p)`  (`ν = ω/·`); this is H-R's `Σ ω(p)/p`;
* `Wratio    s Lam z n = (∏_{p ∈ window} (1 − ν(p)))⁻¹`, which is exactly
  `W(z_n)/W(z) = ∏_{p<z_n}(1−ν)/∏_{p<z}(1−ν) = 1/∏_{z_n ≤ p < z}(1−ν)`  (`W` as in
  `Salt/BrunLower/Defs.lean`).

## What is proved here, and what is left as the (Mertens) interface

`windowSum_le_log_Wratio` lands H-R's own one-line reduction (p.104, foot):
`Σ_{z_n ≤ p < z} ω(p)/p ≤ Σ log(1 − ω(p)/p)⁻¹ = log(W(z_n)/W(z))`.  This needs only
`ν(p) < 1` (no `(Ω₁)`), so **`ps` is obtained *from* `Wr`**, not proved independently
(the node brief's requested corollary).

The remaining content of (2.16) — the sharp Mertens estimate
`Σ_{w ≤ p < z} ω(p) log p / p ≤ A(log(z/w) + 1)` (H-R's "well-known result", p.105) fed
through `(Ω₁)` and partial summation into `W(w)/W(z) ≤ (log z/log w)^A(1+O(1/log w))`,
then the ladder (2.13)/(2.14) — collapses to the single per-level bound H-R reach just
before (2.18) (p.106, "whence"):

  `log(W(z_n)/W(z)) ≤ nΛA(1 + B₁/loglog z)`,   `n = 1,…,r`.

This is taken as the explicit hypothesis `hMert : log (Wratio …) ≤ n · κ` with the
common rate `κ = ΛA(1+B₁/loglog z)`.  **P1 discharges `hMert` at the twin instance**
(`ω(2)=1, ω(p)=2`, `A=2`) via the corpus' product-form Mertens estimates ("Maynard's
Mertens", `Salt/Brun`): note `log (Wratio s Lam z n) = Σ_{p ∈ window} −log(1 − ν(p))`
(`log_Wratio_eq`), so `hMert` is literally a windowed Mertens-product bound.

## ⚠️ (2.18) redefines the ladder scale — kept as a free parameter (Iron Rule 1)

H-R's (2.18) is  `Λ = (2λ/A)(1 + B₁/loglog z)⁻¹`  — a `z`-dependent scale strictly
*below* B0's nominal `bigLambda A lam = 2λ/A`, rising to it as `z → ∞`, and requiring
`z` large (so `0 < Λ ≤ 1`, using `λ < 1/2`).  It is **not** `2λ/A`.  Choosing `Λ` per
(2.18) is a Fable-tier ladder decision (B0's `zLev` is `Λ`-generic and B3's carriers are
`Λ`-abstract, so nothing landed depends on it).  Accordingly this node keeps `Lam` a
**free parameter** throughout and expresses (2.18)'s content as the free-parameter
inequality `hkappa : κ ≤ 2λ` — exactly what (2.18) achieves (equality, `κ = 2λ`, when
`Λ` is chosen as in (2.18)).  See `flags.md` catch #18.
-/

open Finset Nat ArithmeticFunction

namespace Salt.BrunLower

open BoundingSieve

/-! ## The windowed carriers `[z_n, z)` -/

/-- The window `[z_n, z)`: the sifting primes `p ∣ prodPrimes` with `z_n ≤ p`.  Since every
sifting prime is `< z`, this is exactly the H-R window `[z_n, z)`. -/
noncomputable def windowPrimes (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) : Finset ℕ :=
  s.prodPrimes.primeFactors.filter (fun p : ℕ => zLev Lam z n ≤ (p : ℝ))

/-- `Σ_{z_n ≤ p < z} ω(p)/p` in the sieve's density `ν = ω/·`; H-R's `ps` carrier of B3. -/
noncomputable def windowSum (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ windowPrimes s Lam z n, s.nu p

/-- `W(z_n)/W(z) = (∏_{z_n ≤ p < z} (1 − ν(p)))⁻¹`; H-R's `Wr` carrier of B3. -/
noncomputable def Wratio (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) : ℝ :=
  (∏ p ∈ windowPrimes s Lam z n, (1 - s.nu p))⁻¹

/-! ## Density facts on the window -/

/-- Sifting primes obey `0 < ν(p) < 1`. -/
lemma nu_lt_one_of_mem_window {s : BoundingSieve} {Lam z : ℝ} {n : ℕ} {p : ℕ}
    (hp : p ∈ windowPrimes s Lam z n) : s.nu p < 1 := by
  rw [windowPrimes, Finset.mem_filter] at hp
  exact s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp.1)
    (Nat.dvd_of_mem_primeFactors hp.1)

lemma nu_pos_of_mem_window {s : BoundingSieve} {Lam z : ℝ} {n : ℕ} {p : ℕ}
    (hp : p ∈ windowPrimes s Lam z n) : 0 < s.nu p := by
  rw [windowPrimes, Finset.mem_filter] at hp
  exact s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp.1)
    (Nat.dvd_of_mem_primeFactors hp.1)

/-- Each window factor `1 − ν(p)` is positive. -/
lemma one_sub_nu_pos_of_mem_window {s : BoundingSieve} {Lam z : ℝ} {n : ℕ} {p : ℕ}
    (hp : p ∈ windowPrimes s Lam z n) : 0 < 1 - s.nu p := by
  have := nu_lt_one_of_mem_window hp; linarith

/-- `W(z_n)/W(z) > 0` (a product of positive factors, inverted). -/
lemma Wratio_pos (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) : 0 < Wratio s Lam z n := by
  unfold Wratio
  exact inv_pos.mpr (Finset.prod_pos fun _p hp => one_sub_nu_pos_of_mem_window hp)

/-- `Σ_{z_n ≤ p < z} ω(p)/p ≥ 0` (a sum of positive densities) — for all `n`, matching
B3's `hps0`. -/
lemma windowSum_nonneg (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) : 0 ≤ windowSum s Lam z n :=
  Finset.sum_nonneg fun _p hp => (nu_pos_of_mem_window hp).le

/-! ## The log of the density ratio -/

/-- `log(W(z_n)/W(z)) = Σ_{z_n ≤ p < z} −log(1 − ω(p)/p)` — the product-to-sum identity
that makes the Mertens hypothesis `hMert` a windowed Mertens-*product* bound. -/
lemma log_Wratio_eq (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) :
    Real.log (Wratio s Lam z n) = - ∑ p ∈ windowPrimes s Lam z n, Real.log (1 - s.nu p) := by
  unfold Wratio
  rw [Real.log_inv, Real.log_prod]
  intro _p hp
  exact ne_of_gt (one_sub_nu_pos_of_mem_window hp)

/-! ## (2.16) ⟹ `ps`: H-R's one-line reduction (p.104)

`Σ_{z_n ≤ p < z} ω(p)/p ≤ Σ log(1 − ω(p)/p)⁻¹ = log(W(z_n)/W(z))`, from `x ≤ −log(1−x)`
(needs only `ν(p) < 1`; no `(Ω₁)`). -/

/-- **H-R p.104, foot:** `Σ_{z_n ≤ p < z} ω(p)/p ≤ log(W(z_n)/W(z))`. -/
lemma windowSum_le_log_Wratio (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) :
    windowSum s Lam z n ≤ Real.log (Wratio s Lam z n) := by
  rw [log_Wratio_eq]
  rw [← Finset.sum_neg_distrib]
  unfold windowSum
  apply Finset.sum_le_sum
  intro p hp
  have hpos : 0 < 1 - s.nu p := one_sub_nu_pos_of_mem_window hp
  -- `log(1−ν) ≤ (1−ν) − 1 = −ν`, i.e. `ν ≤ −log(1−ν)`.
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-! ## The discharge: (2.16) and `ps` from the Mertens interface + (2.18) -/

/-- **(2.16) — the W-ratio bound `W(z_n)/W(z) ≤ e^{2nλ}`** (H-R p.104–106), discharging
B3's `hWr`.

`hMert` is the sharp Mertens/`(Ω₁)`/ladder estimate H-R reach just before (2.18)
(`log (Wratio …) ≤ n·κ`, `κ = ΛA(1 + B₁/loglog z)`); `hkappa : κ ≤ 2λ` is (2.18) as a
free-parameter inequality (equality when `Λ` is chosen per (2.18)).  `Lam` stays free —
the (2.18) scale is a Fable-tier choice (see the module note). -/
theorem Wratio_le_exp (s : BoundingSieve) {Lam z lam kappa : ℝ} {r : ℕ}
    (hkappa : kappa ≤ 2 * lam)
    (hMert : ∀ n ∈ Finset.Icc 1 r, Real.log (Wratio s Lam z n) ≤ (n : ℝ) * kappa) :
    ∀ n ∈ Finset.Icc 1 r, Wratio s Lam z n ≤ Real.exp (2 * (n : ℝ) * lam) := by
  intro n hn
  have hlog : Real.log (Wratio s Lam z n) ≤ 2 * (n : ℝ) * lam := by
    calc Real.log (Wratio s Lam z n)
        ≤ (n : ℝ) * kappa := hMert n hn
      _ ≤ (n : ℝ) * (2 * lam) :=
          mul_le_mul_of_nonneg_left hkappa (Nat.cast_nonneg n)
      _ = 2 * (n : ℝ) * lam := by ring
  calc Wratio s Lam z n
      = Real.exp (Real.log (Wratio s Lam z n)) := (Real.exp_log (Wratio_pos s Lam z n)).symm
    _ ≤ Real.exp (2 * (n : ℝ) * lam) := Real.exp_le_exp.mpr hlog

/-- **`ps`: `Σ_{z_n ≤ p < z} ω(p)/p ≤ 2nλ`** (H-R p.104), discharging B3's `hps`.  Obtained
*from* (2.16) via `windowSum_le_log_Wratio`, under the same interface as `Wratio_le_exp`. -/
theorem windowSum_le (s : BoundingSieve) {Lam z lam kappa : ℝ} {r : ℕ}
    (hkappa : kappa ≤ 2 * lam)
    (hMert : ∀ n ∈ Finset.Icc 1 r, Real.log (Wratio s Lam z n) ≤ (n : ℝ) * kappa) :
    ∀ n ∈ Finset.Icc 1 r, windowSum s Lam z n ≤ 2 * (n : ℝ) * lam := by
  intro n hn
  calc windowSum s Lam z n
      ≤ Real.log (Wratio s Lam z n) := windowSum_le_log_Wratio s Lam z n
    _ ≤ (n : ℝ) * kappa := hMert n hn
    _ ≤ (n : ℝ) * (2 * lam) := mul_le_mul_of_nonneg_left hkappa (Nat.cast_nonneg n)
    _ = 2 * (n : ℝ) * lam := by ring

end Salt.BrunLower
