/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.L2cCore
import Salt.SW.TBalTall
import Salt.SW.ZeroCountNearOne

/-!
# HB 1983, Lemma 3 — the pretense sum (node N3 of the fulcrum campaign)

The symbolic slot `Salt.HB.PretenseSum` (`Salt/HB/TransferFull.lean:183`) is

    PretenseSum χ N = ∑_{p ≤ N, χ(p) = 1} log p / p,

the `χ = +1` primes that HB's (3.3) carries out of Lemma 2.  Heath-Brown's **Lemma 3**
(statement p.198, proof pp.206-207) bounds it by `≪ L·(log η)^{−1/2}` — the rate that,
balanced against `e^{A z₀}` in Lemma 2, forces `z₀ = A log log η` and hence the
`O(x(log log η)^{−1})` of his Theorem 1.

## 🔴 THE ROUTE — a design finding of this wave

The dispatch brief asked for the **explicit-formula** route: partial summation of
`ψ(y,χ)` against the sharp EF, the `−y^{β₀}/β₀` term split off, the residual zero sum
spent at the repulsion ceiling.  **That is HB's Lemma 7 route (pp.207-210), and it
cannot prove Lemma 3.**  The reason is structural and is recorded here so no later wave
re-attempts it:

`∑_{n ≤ N} χ(n)Λ(n)/n` carries genuine mass at *small* `n`, where the explicit formula
is useless (its error is `O(y·T^{−1}(log qy)²)`, worthless below `y ≍ q^{250}`).  Any
`y`-split at `Y` bounds the low part only by `+(log Y + O(1))` (Mertens, in absolute
value), while the high part supplies `−(log N − log Y)`; the cancellation that Lemma 3
lives on therefore loses `2 log Y`, i.e. `≍ L`, which is the whole quantity being
estimated.  HB's actual route (p.206) is the **Dirichlet-series** route: Davenport
ch.12 (17) for `L′/L` at `s = 1 + L^{−1}` versus `s′ = 1 + aL^{−1}`, the pole of `−ζ′/ζ`
cancelled against `−1/(s−β₀)`, with **no truncation at all** — the small-`n` mass is
handled by the analytic identity, not by an estimate.  Its three inputs are
(1) `|γ| ≥ 1` zeros, (2) **Prachar's disc count**, (3) **Deuring-Heilbronn repulsion at
`|γ| ≤ 1`** — and this τ-range is exactly the one our landed artillery covers (see the
τ-range flag at `docs/sources/hb1983-notes.md:487`, which concerns Lemma **7**, not this
node).

Also recorded: the brief asked for the rate `(log η)^{−1/4}`; the staged source gives
`(log η)^{−1/2}` (`hb1983-notes.md:429,809`, pp.198/206).  We mint at `−1/2` and derive
the `−1/4` shape as a free corollary (`pretenseSum_le_quarter_rate`).

## What this file lands

* **§1 — the arithmetic stone (unconditional).**  `two_mul_pretenseSum_le_vmPairW`:
  for any nonnegative weight `w` dominating `1/p` at the primes,

      2·PretenseSum χ N  ≤  ∑_{0 < n ≤ N} (1 + χ_ℝ(n))·Λ(n)·w(n).

  This is HB's "the `χ(p)=1` primes are where `Λ + χΛ` concentrates", in the kernel:
  every term on the right is `≥ 0` because `χ_ℝ ≥ −1`, and at a `χ(p) = +1` prime the
  weight is exactly `2`.  Two instances: the Mertens weight `1/n` (`vmPair`) and HB's
  own Dirichlet weight `n^{−s}` (`vmPairS`), the latter with the currency conversion
  `1/n ≤ N^{s−1}·n^{−s}` (`two_mul_pretenseSum_le_vmPairS`).

* **§2 — the pole cancellation (unconditional).**  `pole_cancel_le`: HB's p.207 line

      1/(s−1) − 1/(s−β₀) = (1−β₀)/((s−1)(s−β₀)) ≤ (1−β₀)/(s−1)²,

  which at `s = 1 + L^{−1}` and `1 − β₀ = (ηL)^{−1}` is exactly `L·η^{−1}`.

* **§3 — HB's optimization (unconditional).**  `hb_rate_at_optimal_a` /
  `hb_rate_optimal`: the balance `La^{−1}` against `aL(log η)^{−1}` is attained at
  `a = (log η)^{1/2}` and gives `2L(log η)^{−1/2}`; the AM-GM half proves no other `a`
  does better.

* **§4 — the two artillery consumptions (unconditional).**
  `one_sub_ceiling_le_dist_one` turns the TAU-EXT `repulsionCeiling` into HB's input (3),
  the repulsion floor `r₀ ≫ L^{−1} log η` on `|1 − ρ|`; `nearOne_multTotal_le` turns
  `LFunction_zero_count_near_one` (Prachar, unconditional) into HB's input (2) *as a
  `Finset` statement with multiplicity*, i.e. in the shape the `(4.1)` error sum wants.

* **§5 — the node.**  `pretenseSum_le` and `pretenseSum_le_hb_rate`: HB's Lemma 3 with
  the ONE carried analytic core, and at the optimal `a`.

* **§6 — the slot bridge.**  `hb_lemma2_of_pretenseSum_le` replaces the symbolic slot in
  `hb_lemma2` by any upper bound, and `hb_lemma2_at_hb_rate` fires it at Lemma 3's rate:
  the `(3.3)` target with **no `PretenseSum` left in it**.

## The carried hypotheses (what a later wave still owes)

Exactly one analytic statement is carried, in either of two equivalent currencies:

* `hchi : twistedMertens χ N ≤ −log N + Rate` (truncated currency), or
* `hcore : vmPairS χ N s ≤ 1/(s−1) − 1/(s−β₀) + Rate` (HB's own currency, `s > 1`).

This is HB (4.2) + (4.3): `−L′/L(s,χ) = −1/(s−β₀) + O(La^{−1}) + O(aL(log η)^{−1})` and
`−ζ′/ζ(s) = 1/(s−1) + O(1)`, added.  The truncated pair sum is bounded by the full
Dirichlet series for free (all terms are `≥ 0`), so the series form implies the finite
form with no loss.  Its own inputs are: the partial-fraction expansion
(`Salt.SW.LFunction_partialFraction`, landed), the `|γ| ≥ 1` tail (Davenport ch.14 (3)),
and §4's two lemmas, assembled through a dyadic decomposition of
`∑_{ρ ≠ β₀, |γ| ≤ 1} |ρ − 1|^{−2}` into the shape `≪ r₀^{−2} + L·r₀^{−1}`.  **That
dyadic sum is the residue of this wave** — §4 supplies both of its inputs in Finset
form; the shell bookkeeping is not attempted here.

Side hypotheses of the artillery (`hord`, `hreal`, `hceil`, `hN`, and the Siegel data
`L(β₀,χ) = 0`, `1/2 < β₀ < 1`) do **not** appear in this file: §4's two lemmas are stated
below the point where they are consumed, so N4/N8's assembly discharges them once, from
the F-side context, exactly as `boxZeros_re_le_at_efHeight` requires.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the arithmetic stone: the `χ(p) = +1` primes inside `Λ + χΛ` -/

/-- `∑_{0 < n ≤ N} (1 + χ_ℝ(n))·Λ(n)·w(n)` — the detector sum at a general weight `w`.
`1 + χ_ℝ` is HB's detector of the `χ(p) = +1` primes: it is `≥ 0` everywhere (a real
character has `χ_ℝ ≥ −1`), and equals `2` exactly where `χ(p) = 1`. -/
noncomputable def vmPairW (χ : DirichletCharacter ℂ q) (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, (1 + chiRe χ n) * (Λ n * w n)

/-- The detector sum at the Mertens weight `w(n) = 1/n`. -/
noncomputable def vmPair (χ : DirichletCharacter ℂ q) (N : ℕ) : ℝ :=
  vmPairW χ N (fun n => 1 / (n : ℝ))

/-- The detector sum at HB's Dirichlet weight `w(n) = n^{−s}` (he works at `s = 1 + L^{−1}`). -/
noncomputable def vmPairS (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℝ) : ℝ :=
  vmPairW χ N (fun n => (n : ℝ) ^ (-s))

/-- `∑_{0 < n ≤ N} χ_ℝ(n)·Λ(n)/n` — the χ-twisted Mertens sum, the object HB's (4.2)
prices.  In the Siegel-zero regime it is `−log N + O(L(log η)^{−1/2})`: the pretense of
`χ` for `μ` makes it cancel the untwisted `log N`. -/
noncomputable def twistedMertens (χ : DirichletCharacter ℂ q) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, chiRe χ n * Λ n / (n : ℝ)

/-- The detector is nonnegative: `1 + χ_ℝ(n) ≥ 0` for every character (no reality
hypothesis needed — `|Re χ| ≤ ‖χ‖ ≤ 1`). -/
lemma one_add_chiRe_nonneg (χ : DirichletCharacter ℂ q) (n : ℕ) : 0 ≤ 1 + chiRe χ n := by
  have h := abs_le.mp (chiRe_abs_le_one χ n)
  linarith [h.1]

/-- **THE STONE (unconditional).**  For any nonnegative weight `w` that dominates `1/p`
at the primes `p ≤ N`,

    2·PretenseSum χ N ≤ ∑_{0 < n ≤ N} (1 + χ_ℝ(n))·Λ(n)·w(n).

HB's p.207 line `∑_{p ≤ x, χ(p)=1} (log p)/p ≪ ∑_{n ≤ x, χ(n)=1} Λ(n)/n`, made exact:
the detector `1 + χ_ℝ` is nonnegative termwise, so dropping every non-`(χ=+1)`-prime
term is legitimate, and at a `χ(p) = +1` prime it is exactly `2`. -/
theorem two_mul_pretenseSum_le_vmPairW (χ : DirichletCharacter ℂ q) (N : ℕ) (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 0 ≤ w n) (hpw : ∀ p : ℕ, p.Prime → p ≤ N → (1 : ℝ) / (p : ℝ) ≤ w p) :
    2 * PretenseSum χ N ≤ vmPairW χ N w := by
  classical
  rw [PretenseSum, Finset.mul_sum, vmPairW]
  refine le_trans (Finset.sum_le_sum (g := fun p => (1 + chiRe χ p) * (Λ p * w p))
    (fun p hp => ?_)) (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hlt, hprime, hchi⟩ := hp
    have hple : p ≤ N := by omega
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hlog : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hdom := hpw p hprime hple
    calc 2 * (Real.log (p : ℝ) / (p : ℝ))
        = 2 * (Real.log (p : ℝ) * (1 / (p : ℝ))) := by ring
      _ ≤ 2 * (Real.log (p : ℝ) * w p) := by nlinarith
      _ = (1 + chiRe χ p) * (Λ p * w p) := by
          rw [hchi, ArithmeticFunction.vonMangoldt_apply_prime hprime]; ring
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact Finset.mem_Ioc.mpr ⟨hp.2.1.pos, by omega⟩
  · intro n _ _
    exact mul_nonneg (one_add_chiRe_nonneg χ n)
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n))

/-- The stone at the Mertens weight. -/
theorem two_mul_pretenseSum_le_vmPair (χ : DirichletCharacter ℂ q) (N : ℕ) :
    2 * PretenseSum χ N ≤ vmPair χ N :=
  two_mul_pretenseSum_le_vmPairW χ N _ (fun n => by positivity) (fun _ _ _ => le_rfl)

/-- The Mertens-weight detector sum splits into the untwisted and twisted halves. -/
lemma vmPair_eq_add (χ : DirichletCharacter ℂ q) (N : ℕ) :
    vmPair χ N = (∑ n ∈ Finset.Ioc 0 N, Λ n / (n : ℝ)) + twistedMertens χ N := by
  rw [vmPair, vmPairW, twistedMertens, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **The stone folded against the landed Mertens bound.**  `mertens_vonMangoldt_div_le`
(`Salt/HB/L2cCore.lean:437`, unconditional) discharges the untwisted half, leaving the
twisted half as the only analytic unknown:

    2·PretenseSum χ N ≤ log N + (log 4 + 4) + twistedMertens χ N.

The `log N` here is exactly the pole `1/(s−1)` of `−ζ′/ζ` in HB's (4.3); the Siegel zero
enters only through `twistedMertens`, which it drives to `−log N + o(L)`. -/
theorem two_mul_pretenseSum_le_mertens (χ : DirichletCharacter ℂ q) {N : ℕ} (hN : 1 ≤ N) :
    2 * PretenseSum χ N ≤ Real.log (N : ℝ) + (Real.log 4 + 4) + twistedMertens χ N := by
  have h1 := two_mul_pretenseSum_le_vmPair χ N
  rw [vmPair_eq_add] at h1
  linarith [mertens_vonMangoldt_div_le (N := N) hN]

/-- **The currency conversion `1/n ≤ N^{s−1}·n^{−s}`** (`1 ≤ s`, `0 < n ≤ N`).  This is
what lets HB read a truncated sum off a Dirichlet series at `s = 1 + L^{−1}`: the loss is
`N^{s−1} = N^{1/L}`, which is `O(1)` on the campaign window `N ≤ q^{500}`. -/
lemma inv_le_rpow_mul_rpow_neg {n N : ℕ} {s : ℝ} (hs : 1 ≤ s) (hn : 0 < n) (hnN : n ≤ N) :
    (1 : ℝ) / (n : ℝ) ≤ (N : ℝ) ^ (s - 1) * (n : ℝ) ^ (-s) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hsplit : (n : ℝ) ^ (s - 1) * (n : ℝ) ^ (-s) = 1 / (n : ℝ) := by
    rw [← Real.rpow_add hn0, show s - 1 + -s = ((-1 : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]
    simp
  have hmono : (n : ℝ) ^ (s - 1) ≤ (N : ℝ) ^ (s - 1) :=
    Real.rpow_le_rpow hn0.le hnN' (by linarith)
  calc (1 : ℝ) / (n : ℝ) = (n : ℝ) ^ (s - 1) * (n : ℝ) ^ (-s) := hsplit.symm
    _ ≤ (N : ℝ) ^ (s - 1) * (n : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hn0.le _)

/-- **The stone in HB's own currency.**  At any `s ≥ 1`,

    2·PretenseSum χ N ≤ N^{s−1}·∑_{0 < n ≤ N} (1 + χ_ℝ(n))·Λ(n)·n^{−s},

and the right-hand sum is bounded termwise by the full Dirichlet series
`−ζ′/ζ(s) − L′/L(s,χ)` (every term is `≥ 0`), which is what HB (4.2)+(4.3) prices. -/
theorem two_mul_pretenseSum_le_vmPairS (χ : DirichletCharacter ℂ q) (N : ℕ) {s : ℝ}
    (hs : 1 ≤ s) :
    2 * PretenseSum χ N ≤ (N : ℝ) ^ (s - 1) * vmPairS χ N s := by
  have hcast : (N : ℝ) ^ (s - 1) * vmPairS χ N s
      = vmPairW χ N (fun n => (N : ℝ) ^ (s - 1) * (n : ℝ) ^ (-s)) := by
    rw [vmPairS, vmPairW, vmPairW, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hcast]
  refine two_mul_pretenseSum_le_vmPairW χ N _ (fun n => by positivity) (fun p hp hpN => ?_)
  exact inv_le_rpow_mul_rpow_neg hs hp.pos hpN

/-! ## §2 — the pole cancellation (HB p.207) -/

/-- **HB's pole cancellation, p.207.**  For `s > 1` and `β₀ ≤ 1`,

    1/(s−1) − 1/(s−β₀) = (1−β₀)/((s−1)(s−β₀)) ≤ (1−β₀)/(s−1)²,

since `s − β₀ ≥ s − 1 > 0`.  At HB's operating point `s = 1 + L^{−1}` and
`1 − β₀ = (ηL)^{−1}` the right-hand side is `(ηL)^{−1}·L² = L·η^{−1}` — the term he
records as `≪ Lη^{−1} ≪ L(log η)^{−1/2}`.  The existence of the Siegel zero is spent
*here and only here* as a main term: the pole of `−ζ′/ζ` at `s = 1` is cancelled to
within `L/η` by the zero's own pole in `−L′/L`. -/
lemma pole_cancel_le {s β₀ : ℝ} (hs : 1 < s) (hβ : β₀ ≤ 1) :
    1 / (s - 1) - 1 / (s - β₀) ≤ (1 - β₀) / (s - 1) ^ 2 := by
  have h1 : (0 : ℝ) < s - 1 := by linarith
  have h2 : (0 : ℝ) < s - β₀ := by linarith
  have hu : (0 : ℝ) ≤ 1 - β₀ := by linarith
  have hkey : 1 / (s - 1) - 1 / (s - β₀) = (1 - β₀) / ((s - 1) * (s - β₀)) := by
    field_simp
    ring
  rw [hkey]
  apply div_le_div_of_nonneg_left hu (by positivity)
  nlinarith

/-! ## §3 — HB's optimization `a = (log η)^{1/2}` (p.206) -/

/-- **The balance at HB's optimal `a = (log η)^{1/2}`.**  The two error terms of (4.2),
`L·a^{−1}` and `a·L·(log η)^{−1}`, are equal at `a = (log η)^{1/2}` and their sum is
`2L(log η)^{−1/2}` — the rate of Lemma 3. -/
lemma hb_rate_at_optimal_a (Lparam ell : ℝ) (hell : 0 < ell) :
    Lparam / Real.sqrt ell + Real.sqrt ell * Lparam / ell
      = 2 * Lparam / Real.sqrt ell := by
  have hs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hell
  have hsq : Real.sqrt ell ^ 2 = ell := Real.sq_sqrt hell.le
  field_simp
  rw [hsq]
  ring

/-- **No other `a` does better** (AM-GM): for `A, B ≥ 0` and `a > 0`,
`2√(AB) ≤ A/a + B·a`, with equality at `a = √(A/B)`.  This is the honest content of
HB's word "optimal" at p.206 — the `(log η)^{−1/2}` is not an artifact of a choice. -/
lemma hb_rate_optimal {A B a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) :
    2 * Real.sqrt (A * B) ≤ A / a + B * a := by
  have h1 : (0 : ℝ) ≤ A / a := div_nonneg hA ha.le
  have h2 : (0 : ℝ) ≤ B * a := mul_nonneg hB ha.le
  have h3 : (A / a) * (B * a) = A * B := by field_simp
  have hkey : Real.sqrt (A * B) = Real.sqrt (A / a) * Real.sqrt (B * a) := by
    rw [← Real.sqrt_mul h1, h3]
  rw [hkey]
  nlinarith [sq_nonneg (Real.sqrt (A / a) - Real.sqrt (B * a)), Real.sq_sqrt h1, Real.sq_sqrt h2]

/-- `L/√ℓ` in `rpow` currency: `L·ℓ^{−1/2}`, the shape the paper prints. -/
lemma div_sqrt_eq_rpow (Lparam ell : ℝ) (hell : 0 < ell) :
    Lparam / Real.sqrt ell = Lparam * ell ^ (-(1 / 2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hell.le, div_eq_mul_inv]

/-- The `−1/2` rate implies the `−1/4` rate once `log η ≥ 1` (`Real.rpow` monotone in the
exponent at base `≥ 1`).  Recorded because the dispatch brief named `(log η)^{−1/4}`
while the staged source gives `(log η)^{−1/2}`: the two shapes are ordered, not in
conflict. -/
lemma rpow_neg_half_le_neg_quarter {ell : ℝ} (hell : 1 ≤ ell) :
    ell ^ (-(1 / 2) : ℝ) ≤ ell ^ (-(1 / 4) : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hell (by norm_num)

/-! ## §4 — the two artillery consumptions (HB's inputs (2) and (3), p.206) -/

open Salt.SW in
/-- **HB's input (3), off the landed TAU-EXT artillery: the repulsion floor.**  A zero
whose real part is capped by the Deuring-Heilbronn `repulsionCeiling` is *far from `1`*:

    |ρ − 1| ≥ 1 − Re ρ ≥ (log(1/u) − log(1/c) − k·log(log Q + 2))/(b·log Q).

At `u = 1 − β₀ = (ηL)^{−1}` and `Q ≍ q` the right-hand side is HB's
`r₀ ≫ L^{−1}·log η` (p.206, Jutila [11, Thm 2]) verbatim.  The ceiling hypothesis is
supplied by `Salt.SW.boxZeros_re_le_at_efHeight` (or, at the τ-range Lemma 3 actually
needs — `|γ| ≤ 1` — by `Salt.SW.boxZeros_re_le_unit_box`, which is off
`dh_repulsion_ordered` with no tall re-thread at all). -/
lemma one_sub_ceiling_le_dist_one {b c k Q u : ℝ} {ρ : ℂ}
    (hρ : ρ.re ≤ repulsionCeiling b c k Q u) :
    (Real.log (1 / u) - Real.log (1 / c) - k * Real.log (Real.log Q + 2)) / (b * Real.log Q)
      ≤ ‖ρ - 1‖ := by
  have habs : |(ρ - 1).re| ≤ ‖ρ - 1‖ := Complex.abs_re_le_norm _
  have hre : (ρ - 1).re = ρ.re - 1 := by simp
  rw [hre] at habs
  have hceil : ρ.re ≤ 1 - (Real.log (1 / u) - Real.log (1 / c)
      - k * Real.log (Real.log Q + 2)) / (b * Real.log Q) := by
    rw [repulsionCeiling] at hρ; exact hρ
  have hle : (1 : ℝ) - ρ.re ≤ |ρ.re - 1| := by
    rcases abs_cases (ρ.re - 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  linarith

open Salt.SW in
/-- **HB's input (2), off the landed Prachar count: the near-`1` disc count with
multiplicity, as a `Finset` statement.**  For a primitive `χ` mod `f ≥ 2` and
`0 < r < 1/2`, any finite set `Z` of zeros of `L(·,χ)` inside `|ρ − 1| ≤ r` has

    ∑_{ρ ∈ Z} m_ρ ≤ C·(1 + r·log(f + 2)),

which is Prachar [12, ch.10, Lemma 2.1] — **unconditional** — in the exact currency the
`(4.1)` error sum wants (a `Finset`, weighted by multiplicity, so it composes directly
with `efMultTotal`).  Route: `Salt.SW.efMultTotal_le_divisor` (the divisor bridge, wave
3 of N1) followed by `Salt.SW.LFunction_zero_count_near_one`.

Together with `one_sub_ceiling_le_dist_one` these are the two inputs of HB's dyadic
estimate `∑_{ρ ≠ β₀, |γ| ≤ 1} |ρ − 1|^{−2} ≪ r₀^{−2} + L·r₀^{−1}` — the shell
bookkeeping is the residue of this wave and is NOT attempted here. -/
theorem nearOne_multTotal_le : ∃ C : ℝ, 0 < C ∧
    ∀ {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → 2 ≤ f →
      ∀ {r : ℝ}, 0 < r → r < 1 / 2 → ∀ {Z : Finset ℂ},
        (∀ ρ ∈ Z, ‖ρ - 1‖ ≤ r) →
        (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) →
        efMultTotal χ Z ≤ C * (1 + r * Real.log ((f : ℝ) + 2)) := by
  obtain ⟨C, hC, hmain⟩ := LFunction_zero_count_near_one
  refine ⟨C, hC, ?_⟩
  intro f _inst χ hχ hf r hr0 hr Z hZK hZ0
  refine le_trans (efMultTotal_le_divisor (ne_one_of_isPrimitive χ hχ hf)
    (isCompact_closedBall (1 : ℂ) r) (fun ρ hρ => ?_) hZ0) (hmain χ hχ hf hr0 hr)
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hZK ρ hρ

/-- A geometric tail bound, stated where it is used. -/
lemma geom_sum_le_inv_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, x ^ j ≤ 1 / (1 - x) := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  have h2 : (∑ j ∈ Finset.range n, x ^ j) * (1 - x) = 1 - x ^ n := by
    linear_combination -(geom_sum_mul x n)
  rw [le_div_iff₀ h1, h2]
  linarith [pow_nonneg hx0 n]

open Salt.SW in
/-- **HB's (4.1) ERROR SUM — the dyadic estimate, p.206.**  Combining the two inputs above:
for zeros of `L(·,χ)` confined to the annulus `r₀ ≤ |ρ − 1| < 1/4`,

    ∑_{ρ} m_ρ·|ρ − 1|^{−2}  ≤  C·( r₀^{−2} + log(f+2)·r₀^{−1} ),

which is HB's `≪ r₀^{−2} + L·r₀^{−1}` verbatim (p.206, the `ρ ≠ β₀, |γ| ≤ 1` part of (4.1)).
The proof is the dyadic decomposition he leaves implicit: fibre the zeros by
`j = log₂⌊|ρ−1|/r₀⌋`, price each shell by Prachar at radius `r₀·2^{j+1}`
(`nearOne_multTotal_le`), and sum the two geometric series `∑4^{−j} ≤ 4/3`,
`∑2^{−j} ≤ 2`.  The shell index is a *natural* logarithm-free `Nat.log 2`, so no real
`logb` bookkeeping enters.

Fed with `one_sub_ceiling_le_dist_one`'s repulsion floor `r₀ ≫ L^{−1}·log η`, the right
side is `≪ L²(log η)^{−2} + L²(log η)^{−1} ≪ L²(log η)^{−1}`, and HB's prefactor
`a·L^{−1}` turns it into the `a·L·(log η)^{−1}` of (4.2) — the term §3 balances against
`L·a^{−1}`.  This is the last unconditional input of the carried core. -/
theorem nearOne_invSq_sum_le : ∃ C : ℝ, 0 < C ∧
    ∀ {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → 2 ≤ f →
      ∀ {r0 : ℝ}, 0 < r0 → ∀ {Z : Finset ℂ},
        (∀ ρ ∈ Z, r0 ≤ ‖ρ - 1‖) → (∀ ρ ∈ Z, ‖ρ - 1‖ < 1 / 4) →
        (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) →
        ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ - 1‖ ^ 2
          ≤ C * (1 / r0 ^ 2 + Real.log ((f : ℝ) + 2) / r0) := by
  classical
  obtain ⟨C0, hC0, hcount⟩ := nearOne_multTotal_le
  refine ⟨4 * C0, by positivity, ?_⟩
  intro f _inst χ hχ hf r0 hr0 Z hlo hhi hzero
  set Lg : ℝ := Real.log ((f : ℝ) + 2) with hLg
  have hLg0 : (0 : ℝ) ≤ Lg := by
    have hf2 : (2 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
    exact Real.log_nonneg (by linarith)
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℕ, ∀ ρ : ℂ, g ρ = Nat.log 2 ⌊‖ρ - 1‖ / r0⌋₊ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = Nat.log 2 ⌊1 / (4 * r0)⌋₊ := ⟨_, rfl⟩
  -- the shell facts, per zero
  have hkey : ∀ ρ ∈ Z, r0 * 2 ^ (g ρ) ≤ ‖ρ - 1‖ ∧ ‖ρ - 1‖ < r0 * 2 ^ (g ρ + 1) ∧ g ρ ≤ J := by
    intro ρ hρ
    have hn : r0 ≤ ‖ρ - 1‖ := hlo ρ hρ
    have hx1 : (1 : ℝ) ≤ ‖ρ - 1‖ / r0 := (one_le_div hr0).mpr hn
    have hx0 : (0 : ℝ) ≤ ‖ρ - 1‖ / r0 := by linarith
    have hk1 : 1 ≤ ⌊‖ρ - 1‖ / r0⌋₊ := Nat.le_floor (by simpa using hx1)
    have hkle : ((⌊‖ρ - 1‖ / r0⌋₊ : ℕ) : ℝ) ≤ ‖ρ - 1‖ / r0 := Nat.floor_le hx0
    have hklt : ‖ρ - 1‖ / r0 < (⌊‖ρ - 1‖ / r0⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
    have h2k : 2 ^ (Nat.log 2 ⌊‖ρ - 1‖ / r0⌋₊) ≤ ⌊‖ρ - 1‖ / r0⌋₊ :=
      Nat.pow_log_le_self 2 (by omega)
    have hlt2 : ⌊‖ρ - 1‖ / r0⌋₊ < 2 ^ (Nat.log 2 ⌊‖ρ - 1‖ / r0⌋₊ + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2kR : ((2 : ℝ)) ^ (Nat.log 2 ⌊‖ρ - 1‖ / r0⌋₊) ≤ ((⌊‖ρ - 1‖ / r0⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h2k
    have hlt2R : ((⌊‖ρ - 1‖ / r0⌋₊ : ℕ) : ℝ) + 1
        ≤ ((2 : ℝ)) ^ (Nat.log 2 ⌊‖ρ - 1‖ / r0⌋₊ + 1) := by
      exact_mod_cast Nat.succ_le_of_lt hlt2
    refine ⟨?_, ?_, ?_⟩
    · rw [hgdef ρ]
      rw [le_div_iff₀ hr0] at hkle
      nlinarith [h2kR, hr0]
    · rw [hgdef ρ]
      rw [div_lt_iff₀ hr0] at hklt
      nlinarith [hlt2R, hr0]
    · rw [hgdef ρ, hJdef]
      refine Nat.log_mono_right (Nat.floor_mono ?_)
      have hq : ‖ρ - 1‖ / r0 ≤ (1 / 4) / r0 := by
        gcongr
        exact (hhi ρ hρ).le
      calc ‖ρ - 1‖ / r0 ≤ (1 / 4) / r0 := hq
        _ = 1 / (4 * r0) := by field_simp
  have hmaps : ∀ ρ ∈ Z, g ρ ∈ Finset.range (J + 1) := fun ρ hρ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hkey ρ hρ).2.2)
  -- the per-shell estimate
  have hstep : ∀ j ∈ Finset.range (J + 1),
      ∑ ρ ∈ Z.filter (fun ρ => g ρ = j), (zeroMult χ ρ : ℝ) / ‖ρ - 1‖ ^ 2
        ≤ C0 / r0 ^ 2 * (1 / (4 : ℝ) ^ j) + 2 * C0 * Lg / r0 * (1 / (2 : ℝ) ^ j) := by
    intro j _
    have hFibsub : Z.filter (fun ρ => g ρ = j) ⊆ Z := Finset.filter_subset _ _
    have hFibg : ∀ ρ ∈ Z.filter (fun ρ => g ρ = j), g ρ = j := fun ρ hρ =>
      (Finset.mem_filter.mp hρ).2
    have h2j : (0 : ℝ) < r0 * 2 ^ j := by positivity
    have hterm : ∑ ρ ∈ Z.filter (fun ρ => g ρ = j), (zeroMult χ ρ : ℝ) / ‖ρ - 1‖ ^ 2
        ≤ ∑ ρ ∈ Z.filter (fun ρ => g ρ = j), (zeroMult χ ρ : ℝ) / (r0 * 2 ^ j) ^ 2 := by
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have hlow := (hkey ρ (hFibsub hρ)).1
      rw [hFibg ρ hρ] at hlow
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [hlow, h2j.le]
    have hsum2 : ∑ ρ ∈ Z.filter (fun ρ => g ρ = j), (zeroMult χ ρ : ℝ) / (r0 * 2 ^ j) ^ 2
        = efMultTotal χ (Z.filter (fun ρ => g ρ = j)) / (r0 * 2 ^ j) ^ 2 := by
      rw [efMultTotal, Finset.sum_div]
    have hrjpos : (0 : ℝ) < min (r0 * 2 ^ (j + 1)) (1 / 4) := lt_min (by positivity) (by norm_num)
    have hrjlt : min (r0 * 2 ^ (j + 1)) (1 / 4) < 1 / 2 :=
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hZK : ∀ ρ ∈ Z.filter (fun ρ => g ρ = j), ‖ρ - 1‖ ≤ min (r0 * 2 ^ (j + 1)) (1 / 4) := by
      intro ρ hρ
      have hh := (hkey ρ (hFibsub hρ)).2.1
      rw [hFibg ρ hρ] at hh
      exact le_min hh.le (hhi ρ (hFibsub hρ)).le
    have hcnt := hcount χ hχ hf hrjpos hrjlt hZK (fun ρ hρ => hzero ρ (hFibsub hρ))
    have hminle : min (r0 * 2 ^ (j + 1)) (1 / 4) ≤ r0 * 2 ^ (j + 1) := min_le_left _ _
    have hfinal : C0 * (1 + r0 * 2 ^ (j + 1) * Lg) / (r0 * 2 ^ j) ^ 2
        = C0 / r0 ^ 2 * (1 / (4 : ℝ) ^ j) + 2 * C0 * Lg / r0 * (1 / (2 : ℝ) ^ j) := by
      have h4 : ((4 : ℝ)) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
        rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
      have h2p : ((2 : ℝ)) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
      have hpos : ((2 : ℝ)) ^ j ≠ 0 := by positivity
      rw [h4, h2p]
      field_simp
    calc ∑ ρ ∈ Z.filter (fun ρ => g ρ = j), (zeroMult χ ρ : ℝ) / ‖ρ - 1‖ ^ 2
        ≤ efMultTotal χ (Z.filter (fun ρ => g ρ = j)) / (r0 * 2 ^ j) ^ 2 := by
          rw [← hsum2]; exact hterm
      _ ≤ C0 * (1 + min (r0 * 2 ^ (j + 1)) (1 / 4) * Lg) / (r0 * 2 ^ j) ^ 2 := by
          gcongr
      _ ≤ C0 * (1 + r0 * 2 ^ (j + 1) * Lg) / (r0 * 2 ^ j) ^ 2 := by
          gcongr
      _ = C0 / r0 ^ 2 * (1 / (4 : ℝ) ^ j) + 2 * C0 * Lg / r0 * (1 / (2 : ℝ) ^ j) := hfinal
  -- the two geometric sums
  have hg4 : ∑ j ∈ Finset.range (J + 1), 1 / (4 : ℝ) ^ j ≤ 4 / 3 := by
    calc ∑ j ∈ Finset.range (J + 1), 1 / (4 : ℝ) ^ j
        = ∑ j ∈ Finset.range (J + 1), ((1 : ℝ) / 4) ^ j :=
          Finset.sum_congr rfl fun j _ => by rw [div_pow, one_pow]
      _ ≤ 1 / (1 - 1 / 4) := geom_sum_le_inv_one_sub (by norm_num) (by norm_num) _
      _ = 4 / 3 := by norm_num
  have hg2 : ∑ j ∈ Finset.range (J + 1), 1 / (2 : ℝ) ^ j ≤ 2 := by
    calc ∑ j ∈ Finset.range (J + 1), 1 / (2 : ℝ) ^ j
        = ∑ j ∈ Finset.range (J + 1), ((1 : ℝ) / 2) ^ j :=
          Finset.sum_congr rfl fun j _ => by rw [div_pow, one_pow]
      _ ≤ 1 / (1 - 1 / 2) := geom_sum_le_inv_one_sub (by norm_num) (by norm_num) _
      _ = 2 := by norm_num
  calc ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) / ‖ρ - 1‖ ^ 2
      = ∑ j ∈ Finset.range (J + 1), ∑ ρ ∈ Z.filter (fun ρ => g ρ = j),
          (zeroMult χ ρ : ℝ) / ‖ρ - 1‖ ^ 2 := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j ∈ Finset.range (J + 1),
          (C0 / r0 ^ 2 * (1 / (4 : ℝ) ^ j) + 2 * C0 * Lg / r0 * (1 / (2 : ℝ) ^ j)) :=
        Finset.sum_le_sum hstep
    _ = C0 / r0 ^ 2 * (∑ j ∈ Finset.range (J + 1), 1 / (4 : ℝ) ^ j)
        + 2 * C0 * Lg / r0 * (∑ j ∈ Finset.range (J + 1), 1 / (2 : ℝ) ^ j) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ C0 / r0 ^ 2 * (4 / 3) + 2 * C0 * Lg / r0 * 2 := by
        have hA : (0 : ℝ) ≤ C0 / r0 ^ 2 := by positivity
        have hB : (0 : ℝ) ≤ 2 * C0 * Lg / r0 := by positivity
        gcongr
    _ ≤ 4 * C0 * (1 / r0 ^ 2 + Lg / r0) := by
        have hA : (0 : ℝ) ≤ C0 / r0 ^ 2 := by positivity
        have hE : C0 / r0 ^ 2 * (4 / 3) ≤ 4 * C0 * (1 / r0 ^ 2) := by
          rw [div_eq_mul_one_div]; nlinarith [hA, hC0, one_div_pos.mpr (pow_pos hr0 2)]
        have hF : 2 * C0 * Lg / r0 * 2 = 4 * C0 * (Lg / r0) := by ring
        rw [mul_add]
        linarith

/-! ## §5 — THE NODE: HB 1983, Lemma 3 -/

/-- `PretenseSum` is nonnegative (each `log p / p ≥ 0` at a prime `p ≥ 2`). -/
lemma pretenseSum_nonneg (χ : DirichletCharacter ℂ q) (N : ℕ) : 0 ≤ PretenseSum χ N := by
  classical
  rw [PretenseSum]
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.1.two_le
  exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)

/-- **HB 1983, LEMMA 3 (statement p.198; proof pp.206-207) — the pretense-sum bound,
truncated currency.**

    PretenseSum χ N = ∑_{p ≤ N, χ(p) = 1} (log p)/p ≤ (Rate + log 4 + 4)/2.

Everything except `hchi` is in the kernel: the detector stone (§1) plus the landed
unconditional Mertens bound.  **The carried analytic core is `hchi`**, the statement
that the χ-twisted Mertens sum cancels the untwisted `log N` to within `Rate`.  That is
HB (4.2)+(4.3): `−L′/L(s,χ) = −1/(s−β₀) + O(La^{−1}) + O(aL(log η)^{−1})` together with
`−ζ′/ζ(s) = 1/(s−1) + O(1)`, whose difference is the pole cancellation `pole_cancel_le`.
Its own inputs are the Prachar count and the Deuring-Heilbronn floor supplied in §4.

No Siegel-zero side hypothesis appears here: `β₀`'s existence, `1/2 < β₀ < 1`, and the
artillery's `hord`/`hreal`/`hceil`/`hN` all live inside `hchi`'s proof obligation, which
is where N4/N8's assembly discharges them from the F-side context. -/
theorem pretenseSum_le (χ : DirichletCharacter ℂ q) {N : ℕ} {Rate : ℝ} (hN : 1 ≤ N)
    (hchi : twistedMertens χ N ≤ -Real.log (N : ℝ) + Rate) :
    PretenseSum χ N ≤ (Rate + (Real.log 4 + 4)) / 2 := by
  have h := two_mul_pretenseSum_le_mertens χ hN
  linarith

/-- **HB 1983, Lemma 3 in HB's own currency** (the Dirichlet series at `s = 1 + L^{−1}`).
The carried core `hcore` is now literally (4.2)+(4.3) — the truncated pair sum bounded by
`1/(s−1) − 1/(s−β₀) + Rate` — and `pole_cancel_le` converts the two poles into the
`(1−β₀)/(s−1)²` that HB records as `≪ Lη^{−1}`.  The prefactor `N^{s−1}` is the honest
cost of reading a truncated sum off a Dirichlet series; on the campaign window
`N ≤ q^{500}` at `s = 1 + L^{−1}` it is `≤ e^{500}`. -/
theorem pretenseSum_le_series (χ : DirichletCharacter ℂ q) (N : ℕ) {s β₀ Rate : ℝ}
    (hs : 1 < s) (hβ : β₀ ≤ 1)
    (hcore : vmPairS χ N s ≤ 1 / (s - 1) - 1 / (s - β₀) + Rate) :
    2 * PretenseSum χ N ≤ (N : ℝ) ^ (s - 1) * ((1 - β₀) / (s - 1) ^ 2 + Rate) := by
  refine le_trans (two_mul_pretenseSum_le_vmPairS χ N hs.le) ?_
  refine mul_le_mul_of_nonneg_left (le_trans hcore ?_) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  linarith [pole_cancel_le hs hβ]

/-- **HB 1983, Lemma 3 AT THE OPTIMAL `a` — the paper's rate.**  With the (4.1) error
carried in HB's two-term shape `K·(L/a + a·L/ℓ)` and `a = ℓ^{1/2}` (`ℓ = log η`), the
rate collapses to `2K·L·ℓ^{−1/2}` and

    PretenseSum χ N ≤ K·L·(log η)^{−1/2} + (log 4 + 4)/2.

This is `≪ L(log η)^{−1/2}`, HB p.198 — the estimate that, balanced against `e^{Az₀}` in
Lemma 2, forces `z₀ = A log log η`. -/
theorem pretenseSum_le_hb_rate (χ : DirichletCharacter ℂ q) {N : ℕ} {Lparam ell K : ℝ}
    (hN : 1 ≤ N) (hell : 0 < ell)
    (hchi : twistedMertens χ N
      ≤ -Real.log (N : ℝ) + K * (Lparam / Real.sqrt ell + Real.sqrt ell * Lparam / ell)) :
    PretenseSum χ N ≤ K * Lparam / Real.sqrt ell + (Real.log 4 + 4) / 2 := by
  have hbal := hb_rate_at_optimal_a Lparam ell hell
  rw [hbal] at hchi
  have h := pretenseSum_le χ hN hchi
  have hs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hell
  calc PretenseSum χ N ≤ (K * (2 * Lparam / Real.sqrt ell) + (Real.log 4 + 4)) / 2 := h
    _ = K * Lparam / Real.sqrt ell + (Real.log 4 + 4) / 2 := by field_simp

/-- The same, printed in the paper's `rpow` shape `L·(log η)^{−1/2}`. -/
theorem pretenseSum_le_hb_rate_rpow (χ : DirichletCharacter ℂ q) {N : ℕ} {Lparam ell K : ℝ}
    (hN : 1 ≤ N) (hell : 0 < ell)
    (hchi : twistedMertens χ N
      ≤ -Real.log (N : ℝ) + K * (Lparam / Real.sqrt ell + Real.sqrt ell * Lparam / ell)) :
    PretenseSum χ N ≤ K * Lparam * ell ^ (-(1 / 2) : ℝ) + (Real.log 4 + 4) / 2 := by
  have h := pretenseSum_le_hb_rate χ hN hell hchi
  rwa [div_sqrt_eq_rpow (K * Lparam) ell hell] at h

/-- **The `(log η)^{−1/4}` shape** the dispatch brief named, derived from the source's
`−1/2` shape for free at `log η ≥ 1`.  Kept so that a consumer written against either
normalization composes. -/
theorem pretenseSum_le_quarter_rate (χ : DirichletCharacter ℂ q) {N : ℕ} {Lparam ell K : ℝ}
    (hN : 1 ≤ N) (hell : 1 ≤ ell) (hKL : 0 ≤ K * Lparam)
    (hchi : twistedMertens χ N
      ≤ -Real.log (N : ℝ) + K * (Lparam / Real.sqrt ell + Real.sqrt ell * Lparam / ell)) :
    PretenseSum χ N ≤ K * Lparam * ell ^ (-(1 / 4) : ℝ) + (Real.log 4 + 4) / 2 := by
  have h := pretenseSum_le_hb_rate_rpow χ hN (by linarith) hchi
  have hstep : K * Lparam * ell ^ (-(1 / 2) : ℝ) ≤ K * Lparam * ell ^ (-(1 / 4) : ℝ) :=
    mul_le_mul_of_nonneg_left (rpow_neg_half_le_neg_quarter hell) hKL
  linarith

/-! ## §6 — THE SLOT BRIDGE: `PretenseSum` out of `hb_lemma2` -/

/-- **THE SLOT BRIDGE.**  `hb_lemma2` (`Salt/HB/TransferFull.lean:200`) carries the
symbolic Lemma-3 slot `PretenseSum χ N` inside its (3.3)-shaped target.  Given *any*
upper bound `P` for the slot and the (automatic) nonnegativity of its coefficient, the
slot may be replaced by `P`:

    S⁽²⁾ − S⁽¹⁾ ≤ Cmain·(x/z₀) + Cmain·(x/log x)·exp(Aexp·z₀)·P + junk.

This is the exact shape TransferFull:183's slot wants — no re-normalization was needed:
the slot is consumed linearly, with a nonnegative coefficient, so an upper bound on
`PretenseSum` transports verbatim. -/
theorem hb_lemma2_of_pretenseSum_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {A : Finset ℕ} (hA : CoprimeSupport q A) (x : ℝ) (N : ℕ) (Cmain z0 Aexp junk P : ℝ)
    (hres : overshootMajorant χ A
      ≤ Cmain * (x / z0)
        + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N + junk)
    (hcoef : 0 ≤ Cmain * (x / Real.log x) * Real.exp (Aexp * z0))
    (hP : PretenseSum χ N ≤ P) :
    S2 χ A - S1 A
      ≤ Cmain * (x / z0)
        + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * P + junk := by
  have hmain := hb_lemma2 χ hsq hA x N Cmain z0 Aexp junk hres
  have hstep := mul_le_mul_of_nonneg_left hP hcoef
  linarith

/-- **THE NODE, ASSEMBLED — HB (3.3) with the Lemma-3 slot filled.**  `hb_lemma2` fired
at Lemma 3's rate: the transfer target now carries `K·L·(log η)^{−1/2} + (log 4 + 4)/2`
in place of the symbolic `PretenseSum`, i.e. **no symbolic slot remains**.  The single
analytic hypothesis is `hchi`, the carried core of §5. -/
theorem hb_lemma2_at_hb_rate (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {A : Finset ℕ} (hA : CoprimeSupport q A) (x : ℝ) {N : ℕ} (Cmain z0 Aexp junk : ℝ)
    {Lparam ell K : ℝ} (hN : 1 ≤ N) (hell : 0 < ell)
    (hres : overshootMajorant χ A
      ≤ Cmain * (x / z0)
        + Cmain * (x / Real.log x) * Real.exp (Aexp * z0) * PretenseSum χ N + junk)
    (hcoef : 0 ≤ Cmain * (x / Real.log x) * Real.exp (Aexp * z0))
    (hchi : twistedMertens χ N
      ≤ -Real.log (N : ℝ) + K * (Lparam / Real.sqrt ell + Real.sqrt ell * Lparam / ell)) :
    S2 χ A - S1 A
      ≤ Cmain * (x / z0)
        + Cmain * (x / Real.log x) * Real.exp (Aexp * z0)
          * (K * Lparam / Real.sqrt ell + (Real.log 4 + 4) / 2) + junk :=
  hb_lemma2_of_pretenseSum_le χ hsq hA x N Cmain z0 Aexp junk _ hres hcoef
    (pretenseSum_le_hb_rate χ hN hell hchi)

end Salt.HB
