/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma7
import Salt.Mertens.TwinDensity

/-!
# HB 1983, Lemma 7 — node N4b, wave **W4.5**: `κ`, `G`, `C(α)` and the rows `(4.4)`, `(4.5)`

Heath-Brown p.199 (Lemma 5) and p.207 (the `κS₁` paragraph).  Wave W4 landed the assembly
`(L2)` (`Salt/HB/Lemma7.lean`) with HB's two sieve-side rows riding as **named binders**

    (4.4)  κ S₁ = {1 + a₁} · x · C(α) · F² · ∏_{p<z}(1 − 1/p)² · 𝔖(z,χ)
    (4.5)  𝔖(z,χ) = {1 + a₂} · 𝔖

because `κ`, `G(p)` and `C(α)` had no corpus definition.  This file supplies the three
definitions and **proves both rows**, with `a₁` and `a₂` explicit — no `O(·)` anywhere.

## The three definitions (HB, verbatim)

* `hbG α d` — HB's sieve density numerator `G(d) = 2^{ω(d)} ∏_{p∣d}(2p−1)/(p+1)` with his
  convention `G(d) = 0` for `(d,α) ≠ 1` (p.199).  `hbG_le_four` is the dimension-4 fact
  (`G(p) ≤ 4`), and `one_sub_hbG_div_eq` is p.207's identity
  `1 − G(p)/p = (p−1)(p−2)/(p(p+1))` — the bridge to `hbS1`.
* `hbCalpha α` — HB's `C(α) = 2 ∏_{p∣α, p≠2}(1 − 2/p)^{−1}` (p.195, `(1.12)`).
* `hbKappa χ α x L1` — HB's `κ`
  `= x L(1,χ)² ∏_{p∣q,p∤α}(1−2/p) ∏_{p∣α}(1−χ(p)/p)² ∏_{p∤α,χ(p)=1}(1−1/p²)
      ∏_{p∤α,χ(p)=−1}(1−2/p)(1+1/p)²`,
  the value `L(1,χ)` entering as the explicit real argument `L1` (the L-value itself is
  WP2 business, not this node's).  The two infinite products are one `tprod` over the
  corpus's `PrimesGt2` index type, backed by a genuine `Multipliable` witness
  (`hbWfac_multipliable`) — never a junk default.

## Why the tails cancel exactly, and where the only error comes from

Under HB's own side condition `z > α` every prime `p ≥ z` satisfies `p ∤ α`, so the `p ≥ z`
halves of `κ`'s two infinite products are *literally* the two infinite products of `𝔖(z,χ)`.
They cancel factor-by-factor.  What is left is a **finite** identity over the primes `p ≤ ⌊z⌋`
(`hb_rear_master`), verified in five cases (`p = 2`; and for odd `p`: `p ∣ α`, `χ(p) = 0`,
`χ(p) = 1`, `χ(p) = −1`).  The *only* error in `(4.4)` is HB's own: the product
`∏_{p∣q,p∤α}(1−2/p)` runs over prime divisors of `q` that may exceed `z`, and there are at most
`z₀ = L/log z` of them (hb1983-notes:451, landed as `sum_recip_largePrimeFactors_le`).  Hence

    a₁ = 2 z₀ / z = 2 (log q / log z) / z .

For `(4.5)` the ratio `𝔖(z,χ)/𝔖` is `exp(τ − σ)` with `τ`, `σ` the two `p > ⌊z⌋` log-tails,
each `≤ 8/⌊z⌋` by `tsum_tail_inv_sq_le`; the resulting

    a₂ = 64 / z      (at `z ≥ 32`, the guard `|τ − σ| ≤ 1` the exponentiation needs).

## Binders (all named, nothing silent)

`hq` (`0 < q`), `hchi01`/`hchi0` (χ real: values in `{0,±1}`, and `χ(p) = 0 ↔ p ∣ q` — the
standard character facts, WP2's business), `hα0`/`hα2` (`0 < α`, `2 ∣ α` — forced by HB's
`(1.3)–(1.9)`: if `2 ∤ α` then `κS₁ = 0`, the `p = 2` factor vanishing on all three branches),
`hz`/`hαz` (`3 ≤ z` and HB's "assuming `z > α`"), and `hL1` — the Euler product for `L(1,χ)`
split at `z`, `L(1,χ) = (∏_{p≤⌊z⌋}(1−χ(p)/p))^{−1}·F`, which is WP2 input, not sieve algebra.
-/

open Filter Set MeasureTheory
open Salt.SW
open scoped Topology

namespace Salt.HB

/-! ## §0 — the prime cut-off -/

/-- The primes `p ≤ ⌊z⌋` — HB's "`p < z`" at the corpus's floor convention (the same index
set that `primeProdBelow` and `hbS1` already use). -/
noncomputable def Pz (z : ℝ) : Finset ℕ := (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime

lemma mem_Pz {z : ℝ} {p : ℕ} : p ∈ Pz z ↔ p ≤ ⌊z⌋₊ ∧ Nat.Prime p := by
  simp only [Pz, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

lemma primeProdBelow_eq {z : ℝ} : primeProdBelow z = ∏ p ∈ Pz z, (1 - 1 / (p : ℝ)) := rfl

/-! ## §1 — HB's `G` (p.199) and `C(α)` (p.195) -/

/-- **HB's sieve-density numerator `G`** (Lemma 5, p.199):

    G(d) = 2^{ω(d)} ∏_{p ∣ d} (2p − 1)/(p + 1),      G(d) = 0 when (d, α) ≠ 1.

The `ρ₁(d) = G(d)/d` of Lemma 6 is the sieve density whose complementary product is `S₁`. -/
noncomputable def hbG (α d : ℕ) : ℝ :=
  if Nat.Coprime d α then
    (2 : ℝ) ^ d.primeFactors.card * ∏ p ∈ d.primeFactors, (2 * (p : ℝ) - 1) / ((p : ℝ) + 1)
  else 0

/-- At a prime `p ∤ α`, `G(p) = 2(2p−1)/(p+1)` (p.199). -/
lemma hbG_prime {α p : ℕ} (hp : Nat.Prime p) (hpα : ¬ p ∣ α) :
    hbG α p = 2 * ((2 * (p : ℝ) - 1) / ((p : ℝ) + 1)) := by
  rw [hbG, if_pos ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpα), hp.primeFactors]
  simp

/-- At a prime `p ∣ α`, `G(p) = 0` (HB's convention). -/
lemma hbG_prime_dvd {α p : ℕ} (hp : Nat.Prime p) (hpα : p ∣ α) : hbG α p = 0 := by
  rw [hbG, if_neg]
  exact fun h => (Nat.Prime.coprime_iff_not_dvd hp).mp h hpα

/-- **`G(p) ≤ 4`** — HB p.200, "as `G(p) ≤ 4` we need a sieve of dimension 4". -/
lemma hbG_le_four {α p : ℕ} (hp : Nat.Prime p) : hbG α p ≤ 4 := by
  by_cases hpα : p ∣ α
  · rw [hbG_prime_dvd hp hpα]; norm_num
  · rw [hbG_prime hp hpα]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hkey : (2 * (p : ℝ) - 1) / ((p : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith

/-- **HB p.207's identity** `1 − G(p)/p = (p−1)(p−2)/(p(p+1))` — the bridge from the sieve
density `ρ₁` to the second form of `S₁` (`hbS1`). -/
lemma one_sub_hbG_div_eq {α p : ℕ} (hp : Nat.Prime p) (hpα : ¬ p ∣ α) :
    1 - hbG α p / (p : ℝ) = ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) * ((p : ℝ) + 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  rw [hbG_prime hp hpα]
  field_simp
  ring

/-- **HB's `C(α)`** (p.195, `(1.12)`): `C(α) = 2 ∏_{p ∣ α, p ≠ 2} (1 − 2/p)^{−1}`.
(`C(4) = 2`: the product is empty.) -/
noncomputable def hbCalpha (α : ℕ) : ℝ :=
  2 * ∏ p ∈ α.primeFactors.filter (fun p => p ≠ 2), (1 - 2 / (p : ℝ))⁻¹

/-! ## §2 — the `κ`-tail Euler factor and its analysis -/

/-- The Euler factor of `κ`'s two infinite products, read as one function of `p`:
`1 − p^{−2}` when `χ(p) = 1`, `(1 − 2/p)(1 + 1/p)²` when `χ(p) = −1`, and `1` when
`χ(p) = 0` (i.e. `p ∣ q` — HB's products omit those primes).  This is also the factor of the
`p ≥ z` half of `𝔖(z,χ)` (p.207). -/
noncomputable def hbSfac {q : ℕ} (χ : DirichletCharacter ℂ q) (p : ℕ) : ℝ :=
  if Salt.TwinBar.chiRe χ p = 1 then 1 - 1 / (p : ℝ) ^ 2
  else if Salt.TwinBar.chiRe χ p = -1 then (1 - 2 / (p : ℝ)) * (1 + 1 / (p : ℝ)) ^ 2
  else 1

/-- `κ`'s factor: `hbSfac` off the prime divisors of `α`, and `1` on them (HB's two products
both carry the condition `p ∤ α`). -/
noncomputable def hbWfac {q : ℕ} (χ : DirichletCharacter ℂ q) (α p : ℕ) : ℝ :=
  if p ∣ α then 1 else hbSfac χ p

lemma hbSfac_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : (3 : ℝ) ≤ (p : ℝ)) :
    hbSfac χ p ≤ 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  unfold hbSfac
  split_ifs with h1 h2
  · have : (0 : ℝ) < 1 / (p : ℝ) ^ 2 := by positivity
    linarith
  · rw [show (1 - 2 / (p : ℝ)) * (1 + 1 / (p : ℝ)) ^ 2
        = 1 - (3 / (p : ℝ) ^ 2 + 2 / (p : ℝ) ^ 3) by field_simp; ring]
    have : (0 : ℝ) < 3 / (p : ℝ) ^ 2 + 2 / (p : ℝ) ^ 3 := by positivity
    linarith
  · exact le_rfl

lemma one_sub_four_div_sq_le_hbSfac {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : (3 : ℝ) ≤ (p : ℝ)) : 1 - 4 / (p : ℝ) ^ 2 ≤ hbSfac χ p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  unfold hbSfac
  split_ifs with h1 h2
  · have : (1 : ℝ) / (p : ℝ) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
      gcongr
      norm_num
    linarith
  · rw [show (1 - 2 / (p : ℝ)) * (1 + 1 / (p : ℝ)) ^ 2
        = 1 - (3 / (p : ℝ) ^ 2 + 2 / (p : ℝ) ^ 3) by field_simp; ring]
    have hkey : 3 / (p : ℝ) ^ 2 + 2 / (p : ℝ) ^ 3 ≤ 4 / (p : ℝ) ^ 2 := by
      have h3 : (2 : ℝ) / (p : ℝ) ^ 3 ≤ 1 / (p : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (le_of_lt (pow_pos hp0 2)) (by linarith : (0:ℝ) ≤ (p : ℝ) - 2)]
      have h4 : (3 : ℝ) / (p : ℝ) ^ 2 + 1 / (p : ℝ) ^ 2 = 4 / (p : ℝ) ^ 2 := by ring
      linarith
    linarith
  · have : (0 : ℝ) < 4 / (p : ℝ) ^ 2 := by positivity
    linarith

lemma hbSfac_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : (3 : ℝ) ≤ (p : ℝ)) :
    0 < hbSfac χ p := by
  have h := one_sub_four_div_sq_le_hbSfac χ hp
  have h4 : 4 / (p : ℝ) ^ 2 ≤ 4 / 9 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  linarith

/-- **The pointwise log bound** `|log hbSfac(p)| ≤ 8/p²` for `p ≥ 3`, off
`log x ≤ x − 1` applied to `(1 − y)^{−1}` with `0 ≤ y ≤ 4/p² ≤ 4/9`. -/
lemma abs_log_hbSfac_le {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : (3 : ℝ) ≤ (p : ℝ)) :
    |Real.log (hbSfac χ p)| ≤ 8 / (p : ℝ) ^ 2 := by
  have hpos := hbSfac_pos χ hp
  have hle1 := hbSfac_le_one χ hp
  have hlow := one_sub_four_div_sq_le_hbSfac χ hp
  have hsq : (9 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have h4 : 4 / (p : ℝ) ^ 2 ≤ 4 / 9 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hlog_nonpos : Real.log (hbSfac χ p) ≤ 0 := Real.log_nonpos hpos.le hle1
  have hbnd : Real.log (hbSfac χ p)⁻¹ ≤ (hbSfac χ p)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at hbnd
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by linarith
  have hfive : (5 : ℝ) / 9 ≤ hbSfac χ p := by linarith
  have hlow' : (p : ℝ) ^ 2 - 4 ≤ hbSfac χ p * (p : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hlow (le_of_lt hp2)
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hp2)] at hmul
    linarith
  have hinv : (hbSfac χ p)⁻¹ - 1 ≤ 8 / (p : ℝ) ^ 2 := by
    rw [sub_le_iff_le_add, inv_le_iff_one_le_mul₀ hpos]
    have hu : (0 : ℝ) < 1 / (p : ℝ) ^ 2 := by positivity
    have hu9 : 1 / (p : ℝ) ^ 2 ≤ 1 / 9 := by
      rw [div_le_div_iff₀ hp2 (by norm_num)]; linarith
    have hrw4 : (4 : ℝ) / (p : ℝ) ^ 2 = 4 * (1 / (p : ℝ) ^ 2) := by ring
    have hrw8 : (8 : ℝ) / (p : ℝ) ^ 2 + 1 = 8 * (1 / (p : ℝ) ^ 2) + 1 := by ring
    rw [hrw4] at hlow
    rw [hrw8]
    nlinarith [hu, hu9, hlow,
      mul_nonneg (by linarith : (0:ℝ) ≤ 8 * (1 / (p : ℝ) ^ 2) + 1)
        (by linarith : (0:ℝ) ≤ hbSfac χ p - (1 - 4 * (1 / (p : ℝ) ^ 2)))]
  rw [abs_of_nonpos hlog_nonpos]
  linarith [hbnd, hinv]

/-! ## §3 — the tail estimate for `∑ 1/p²` over a subtype -/

/-- **The generic `p > N` tail bound.**  If a nonnegative family indexed by `ι` injects into
the naturals `> N` and is majorised by `K/(e i)²`, its `tsum` is `≤ K/N`.  (Proved through
`tsum_le_of_sum_le'`, so no `Summable` hypothesis is needed.) -/
lemma tsum_tail_inv_sq_le {ι : Type*} (e : ι → ℕ) (he : Function.Injective e) (h : ι → ℝ)
    {K : ℝ} (hK : 0 ≤ K) {N : ℕ} (hN : N ≠ 0) (hlt : ∀ i, N < e i)
    (hb : ∀ i, h i ≤ K / ((e i : ℝ)) ^ 2) :
    ∑' i, h i ≤ K / (N : ℝ) := by
  classical
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  refine tsum_le_of_sum_le' (by positivity) (fun s => ?_)
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · simpa using (by positivity : (0:ℝ) ≤ K / (N : ℝ))
  set M : ℕ := (s.image e).sup id with hM
  have hstep1 : ∑ i ∈ s, h i ≤ ∑ i ∈ s, K * (((e i : ℝ)) ^ 2)⁻¹ := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    calc h i ≤ K / ((e i : ℝ)) ^ 2 := hb i
      _ = K * (((e i : ℝ)) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
  have hinj : Set.InjOn e ↑s := fun x _ y _ hxy => he hxy
  have himg : ∑ i ∈ s, K * (((e i : ℝ)) ^ 2)⁻¹ = K * ∑ k ∈ s.image e, (((k : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.mul_sum, Finset.sum_image hinj]
  have hsub : s.image e ⊆ Finset.Ioc N M := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨i, his, rfl⟩ := hk
    rw [Finset.mem_Ioc]
    exact ⟨hlt i, Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨i, his, rfl⟩)⟩
  have hNM : N ≤ M := by
    obtain ⟨i, his⟩ := hs
    have : e i ≤ M := Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨i, his, rfl⟩)
    exact le_trans (hlt i).le this
  have htail := _root_.sum_Ioc_inv_sq_le_sub (α := ℝ) hN hNM
  have hmono : ∑ k ∈ s.image e, (((k : ℝ)) ^ 2)⁻¹ ≤ ∑ k ∈ Finset.Ioc N M, (((k : ℝ)) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
  have hMinv : (0 : ℝ) ≤ ((M : ℕ) : ℝ)⁻¹ := by positivity
  calc ∑ i ∈ s, h i ≤ K * ∑ k ∈ s.image e, (((k : ℝ)) ^ 2)⁻¹ := by rw [← himg]; exact hstep1
    _ ≤ K * ((N : ℝ)⁻¹ - (M : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_left (le_trans hmono htail) hK
    _ ≤ K / (N : ℝ) := by rw [div_eq_mul_inv]; nlinarith [hMinv, hK]

/-! ## §4 — the two log-tails are summable, and `κ`'s Euler product is genuine -/

lemma three_le_of_primesGt2 (p : Salt.TwinBar.PrimesGt2) : (3 : ℝ) ≤ (((p : ℕ)) : ℝ) := by
  have : 3 ≤ (p : ℕ) := p.2.2
  exact_mod_cast this

/-- The common majorant `∑_{p>2} 8/p²`. -/
lemma summable_eight_div_sq :
    Summable (fun p : Salt.TwinBar.PrimesGt2 => 8 / (((p : ℕ)) : ℝ) ^ 2) := by
  have hbase : Summable (fun p : Salt.TwinBar.PrimesGt2 => ((((p : ℕ)) : ℝ) ^ 2)⁻¹) :=
    ((Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)).subtype _
  simpa [div_eq_mul_inv] using hbase.mul_left 8

/-- `|log(1 − (p−1)^{−2})| ≤ 8/p²` — the twin factor's log bound, in the same `1/p²` shape as
`abs_log_hbSfac_le`, so both tails run through one majorant. -/
lemma abs_log_twinFactor_le (p : Salt.TwinBar.PrimesGt2) :
    |Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹)| ≤ 8 / (((p : ℕ)) : ℝ) ^ 2 := by
  have hp3n : 3 ≤ (p : ℕ) := p.2.2
  have hp3 : (3 : ℝ) ≤ (((p : ℕ)) : ℝ) := by exact_mod_cast hp3n
  obtain ⟨hy0, hy4⟩ := Salt.Mertens.factorN_arg_le hp3n
  have hpos := Salt.Mertens.factorN_pos hp3n
  have hnonpos : Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) ≤ 0 :=
    Real.log_nonpos hpos.le (by linarith)
  have hb := Salt.Mertens.neg_log_one_sub_le hy0 hy4
  have ht : (0 : ℝ) < (((p : ℕ)) : ℝ) ^ 2 := by positivity
  have hsq : (0 : ℝ) < ((((p : ℕ)) : ℝ) - 1) ^ 2 := by nlinarith
  have hy : ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹ ≤ 4 / (((p : ℕ)) : ℝ) ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hsq ht]
    nlinarith [hp3]
  have hchain : (4 : ℝ) / 3 * ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹ ≤ 8 / (((p : ℕ)) : ℝ) ^ 2 := by
    have h1 : (4 : ℝ) / 3 * ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹
        ≤ 4 / 3 * (4 / (((p : ℕ)) : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hy (by norm_num)
    have h2 : (4 : ℝ) / 3 * (4 / (((p : ℕ)) : ℝ) ^ 2) ≤ 8 / (((p : ℕ)) : ℝ) ^ 2 := by
      rw [show (4 : ℝ) / 3 * (4 / (((p : ℕ)) : ℝ) ^ 2) = (16 / 3) / (((p : ℕ)) : ℝ) ^ 2 by ring,
        div_le_div_iff₀ ht ht]
      nlinarith [ht]
    linarith
  rw [abs_of_nonpos hnonpos]
  linarith

theorem hbSfac_log_summable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Summable (fun p : Salt.TwinBar.PrimesGt2 => Real.log (hbSfac χ (p : ℕ))) :=
  Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun p => abs_log_hbSfac_le χ (three_le_of_primesGt2 p)) summable_eight_div_sq)

lemma hbWfac_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (α : ℕ) {p : ℕ}
    (hp : (3 : ℝ) ≤ (p : ℝ)) : 0 < hbWfac χ α p := by
  unfold hbWfac
  split_ifs
  · norm_num
  · exact hbSfac_pos χ hp

lemma abs_log_hbWfac_le {q : ℕ} (χ : DirichletCharacter ℂ q) (α : ℕ) {p : ℕ}
    (hp : (3 : ℝ) ≤ (p : ℝ)) : |Real.log (hbWfac χ α p)| ≤ 8 / (p : ℝ) ^ 2 := by
  unfold hbWfac
  split_ifs
  · rw [Real.log_one, abs_zero]
    positivity
  · exact abs_log_hbSfac_le χ hp

theorem hbWfac_log_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (α : ℕ) :
    Summable (fun p : Salt.TwinBar.PrimesGt2 => Real.log (hbWfac χ α (p : ℕ))) :=
  Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun p => abs_log_hbWfac_le χ α (three_le_of_primesGt2 p)) summable_eight_div_sq)

/-- **The `Multipliable` witness for `κ`'s Euler product** — so `hbKappaTail` is the honest
convergent product, never mathlib's junk default. -/
theorem hbWfac_multipliable {q : ℕ} (χ : DirichletCharacter ℂ q) (α : ℕ) :
    Multipliable (fun p : Salt.TwinBar.PrimesGt2 => hbWfac χ α (p : ℕ)) :=
  Real.multipliable_of_summable_log (fun p => hbWfac_pos χ α (three_le_of_primesGt2 p))
    (hbWfac_log_summable χ α)

/-! ## §5 — `κ` (HB p.199), `𝔖(z,χ)` (HB p.207), and `(4.5)` -/

/-- The convergent half of `κ`: HB's two infinite products
`∏_{p∤α,χ(p)=1}(1−1/p²) · ∏_{p∤α,χ(p)=−1}(1−2/p)(1+1/p)²`, read as one `tprod` over the primes
`> 2`.  (The `p = 2` factor is `1` whenever `2 ∣ α`, which HB's `(1.3)–(1.9)` force.) -/
noncomputable def hbKappaTail {q : ℕ} (χ : DirichletCharacter ℂ q) (α : ℕ) : ℝ :=
  ∏' p : Salt.TwinBar.PrimesGt2, hbWfac χ α (p : ℕ)

/-- **HB's `κ`** (Lemma 5, p.199):

    κ = x L(1,χ)² ∏_{p∣q,p∤α}(1−2/p) ∏_{p∣α}(1−χ(p)/p)²
          ∏_{p∤α,χ(p)=1}(1−1/p²) ∏_{p∤α,χ(p)=−1}(1−2/p)(1+1/p)² .

`L1` is the real number `L(1,χ)` (supplied by the consumer; the L-value is WP2's business). -/
noncomputable def hbKappa {q : ℕ} (χ : DirichletCharacter ℂ q) (α : ℕ) (x L1 : ℝ) : ℝ :=
  x * L1 ^ 2
    * (∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ α), (1 - 2 / (p : ℝ)))
    * (∏ p ∈ α.primeFactors, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)) ^ 2)
    * hbKappaTail χ α

/-- The `p ≥ z` half of `𝔖(z,χ)`: `∏_{p≥z,χ(p)=1}(1−p^{−2}) ∏_{p≥z,χ(p)=−1}(1−2/p)(1+1/p)²`. -/
noncomputable def hbSingTail {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) : ℝ :=
  ∏' p : Salt.TwinBar.PrimesGt2, (if ⌊z⌋₊ < (p : ℕ) then hbSfac χ (p : ℕ) else 1)

/-- **HB's `𝔖(z,χ)`** (p.207):

    𝔖(z,χ) = 2 ∏_{2<p<z}(1 − (p−1)^{−2}) ∏_{p≥z,χ(p)=1}(1 − p^{−2})
                  ∏_{p≥z,χ(p)=−1}(1 − 2/p)(1 + 1/p)² . -/
noncomputable def hbSingz {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) : ℝ :=
  2 * (∏ p ∈ Salt.Mertens.gt2Primes ⌊z⌋₊, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)) * hbSingTail χ z

/-- **`(4.5)` — the singular-series truncation**, HB p.207:

    𝔖(z,χ) = {1 + a₂} 𝔖,      |a₂| ≤ 64/z .

Both `p > ⌊z⌋` log-tails (`τ` for `𝔖(z,χ)`'s Euler factors, `σ` for `𝔖`'s) are `≤ 8/⌊z⌋` by
`tsum_tail_inv_sq_le`; the ratio is `exp(τ − σ)` and `|e^w − 1| ≤ 2|w|` closes it. -/
theorem hb_hsing {q : ℕ} (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 32 ≤ z) :
    ∃ e2 : ℝ, hbSingz χ z = (1 + e2) * Salt.HardyLittlewood.twinSingularSeries
      ∧ |e2| ≤ 64 / z := by
  classical
  set N : ℕ := ⌊z⌋₊ with hNdef
  have hN32 : 32 ≤ N := Nat.le_floor (by exact_mod_cast hz)
  have hNR : (32 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN32
  have hNz : z ≤ 2 * (N : ℝ) := by
    have h := Nat.lt_floor_add_one z
    rw [← hNdef] at h
    linarith
  set g : Salt.TwinBar.PrimesGt2 → ℝ :=
    fun p => Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) with hgdef
  set s : Salt.TwinBar.PrimesGt2 → ℝ := fun p => Real.log (hbSfac χ (p : ℕ)) with hsdef
  set tf : Salt.TwinBar.PrimesGt2 → ℝ :=
    fun p => if N < (p : ℕ) then hbSfac χ (p : ℕ) else 1 with htfdef
  have hgsum : Summable g := Salt.TwinBar.twinC2_log_summable
  have hssum : Summable s := hbSfac_log_summable χ
  have htfpos : ∀ p, 0 < tf p := by
    intro p
    rw [htfdef]
    dsimp only
    split_ifs
    · exact hbSfac_pos χ (three_le_of_primesGt2 p)
    · norm_num
  have htflog : ∀ p, Real.log (tf p) = if N < (p : ℕ) then s p else 0 := by
    intro p
    rw [htfdef]
    dsimp only
    split_ifs
    · rfl
    · exact Real.log_one
  have htfsum : Summable (fun p => Real.log (tf p)) := by
    refine Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun p => ?_)
      summable_eight_div_sq)
    rw [htflog p]
    split_ifs
    · exact abs_log_hbSfac_le χ (three_le_of_primesGt2 p)
    · rw [abs_zero]; positivity
  -- the primes `≤ N`, and their complement
  set T : Finset Salt.TwinBar.PrimesGt2 :=
    (Salt.Mertens.gt2Primes N).subtype (fun p => p.Prime ∧ 2 < p) with hT
  have hTgt : ∀ x : Salt.TwinBar.PrimesGt2, x ∉ T → N < ((x : Salt.TwinBar.PrimesGt2) : ℕ) := by
    intro x hx
    rcases Nat.lt_or_ge N ((x : Salt.TwinBar.PrimesGt2) : ℕ) with h | h
    · exact h
    · exact absurd (by rw [hT, Finset.mem_subtype, Salt.Mertens.mem_gt2Primes]
                       exact ⟨h, x.2.1, x.2.2⟩) hx
  have hTle : ∀ x ∈ T, ((x : Salt.TwinBar.PrimesGt2) : ℕ) ≤ N := by
    intro x hx
    rw [hT, Finset.mem_subtype, Salt.Mertens.mem_gt2Primes] at hx
    exact hx.1
  set σ : ℝ := ∑' x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T}, g x with hσdef
  set τ : ℝ := ∑' x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T}, s x with hτdef
  -- the two splits
  have hgsplit : ∑ p ∈ T, g p + σ = ∑' p, g p := hgsum.sum_add_tsum_subtype_compl T
  have htfsplit : ∑ p ∈ T, Real.log (tf p)
      + (∑' x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T}, Real.log (tf x))
      = ∑' p, Real.log (tf p) := htfsum.sum_add_tsum_subtype_compl T
  have hTzero : ∑ p ∈ T, Real.log (tf p) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [htflog p, if_neg (by have := hTle p hp; omega)]
  have hcompl : (∑' x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T}, Real.log (tf x)) = τ := by
    rw [hτdef]
    exact tsum_congr (fun x => by rw [htflog, if_pos (hTgt x.1 x.2)])
  -- `hbSingTail = exp τ`
  have htailexp : hbSingTail χ z = Real.exp τ := by
    rw [hbSingTail, ← Real.rexp_tsum_eq_tprod htfpos htfsum, ← htfsplit, hTzero, hcompl, zero_add]
  -- `Q = exp (∑_T g)`
  have hLsub : ∑ p ∈ T, g p
      = ∑ p ∈ Salt.Mertens.gt2Primes N, Real.log (1 - (((p : ℝ) - 1) ^ 2)⁻¹) := by
    rw [hT]
    exact Finset.sum_subtype_of_mem (fun k : ℕ => Real.log (1 - (((k : ℝ) - 1) ^ 2)⁻¹))
      (fun x hx => ⟨(Salt.Mertens.mem_gt2Primes.mp hx).2.1,
        (Salt.Mertens.mem_gt2Primes.mp hx).2.2⟩)
  have hQ : (∏ p ∈ Salt.Mertens.gt2Primes N, (1 - (((p : ℝ) - 1) ^ 2)⁻¹))
      = Real.exp (∑ p ∈ T, g p) := by
    rw [hLsub]; exact Salt.Mertens.prod_factor_eq_exp_sum N
  have htwin : Salt.TwinBar.twinC2 = Real.exp (∑ p ∈ T, g p + σ) := by
    rw [hgsplit, Salt.TwinBar.twinC2,
      ← Real.rexp_tsum_eq_tprod Salt.TwinBar.twinC2_factor_pos Salt.TwinBar.twinC2_log_summable]
  -- assemble
  have hkeyexp : Real.exp (∑ p ∈ T, g p) * Real.exp τ
      = Real.exp (∑ p ∈ T, g p + σ) * Real.exp (τ - σ) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hSform : hbSingz χ z
      = Salt.HardyLittlewood.twinSingularSeries * Real.exp (τ - σ) := by
    rw [hbSingz, hQ, htailexp, Salt.HardyLittlewood.twinSingularSeries,
      Salt.HardyLittlewood.Pi2, htwin, mul_assoc, mul_assoc, hkeyexp]
  -- the two tail bounds
  have hNne : N ≠ 0 := by omega
  have hinjc : Function.Injective (fun x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T} =>
      ((x : Salt.TwinBar.PrimesGt2) : ℕ)) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hgtc : ∀ x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T},
      N < ((x : Salt.TwinBar.PrimesGt2) : ℕ) := fun x => hTgt x.1 x.2
  have habs_g : |σ| ≤ 8 / (N : ℝ) := by
    have hsummable : Summable (fun x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T} => ‖g x‖) := by
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
        ((summable_eight_div_sq).subtype _)
      exact abs_log_twinFactor_le x.1
    have h1 : |σ| ≤ ∑' x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T}, ‖g x‖ := by
      rw [hσdef, ← Real.norm_eq_abs]
      exact norm_tsum_le_tsum_norm hsummable
    refine le_trans h1 ?_
    refine tsum_tail_inv_sq_le _ hinjc _ (by norm_num) hNne hgtc (fun x => ?_)
    rw [Real.norm_eq_abs]
    exact abs_log_twinFactor_le x.1
  have habs_s : |τ| ≤ 8 / (N : ℝ) := by
    have hsummable : Summable (fun x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T} => ‖s x‖) := by
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
        ((summable_eight_div_sq).subtype _)
      exact abs_log_hbSfac_le χ (three_le_of_primesGt2 x.1)
    have h1 : |τ| ≤ ∑' x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T}, ‖s x‖ := by
      rw [hτdef, ← Real.norm_eq_abs]
      exact norm_tsum_le_tsum_norm hsummable
    refine le_trans h1 ?_
    refine tsum_tail_inv_sq_le _ hinjc _ (by norm_num) hNne hgtc (fun x => ?_)
    rw [Real.norm_eq_abs]
    exact abs_log_hbSfac_le χ (three_le_of_primesGt2 x.1)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hdiff : |τ - σ| ≤ 16 / (N : ℝ) := by
    have hsplit : |τ - σ| ≤ |τ| + |σ| := by
      have h := abs_add_le τ (-σ)
      rw [← sub_eq_add_neg, abs_neg] at h
      exact h
    calc |τ - σ| ≤ |τ| + |σ| := hsplit
      _ ≤ 8 / (N : ℝ) + 8 / (N : ℝ) := add_le_add habs_s habs_g
      _ = 16 / (N : ℝ) := by ring
  have h16 : 16 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN0]; linarith
  have hexp : |Real.exp (τ - σ) - 1| ≤ 2 * |τ - σ| :=
    Real.abs_exp_sub_one_le (le_trans hdiff h16)
  refine ⟨Real.exp (τ - σ) - 1, by rw [hSform]; ring, ?_⟩
  have hz0 : (0 : ℝ) < z := by linarith
  calc |Real.exp (τ - σ) - 1| ≤ 2 * |τ - σ| := hexp
    _ ≤ 2 * (16 / (N : ℝ)) := by linarith
    _ = 32 / (N : ℝ) := by ring
    _ ≤ 64 / z := by
        rw [div_le_div_iff₀ hN0 hz0]
        linarith

/-! ## §6 — `(4.4)`: the finite rearrangement -/

/-- The `κ S₁`-side factor at a prime `p`: the five `p`-factors of `κ S₁` after the `L(1,χ)`
Euler product has been split at `z` — the inverse Euler factor, HB's `∏_{p∣q,p∤α}`, his
`∏_{p∣α}`, the tail factor `hbWfac`, and `S₁`'s. -/
noncomputable def hbRearL {q : ℕ} (χ : DirichletCharacter ℂ q) (α p : ℕ) : ℝ :=
  ((1 - Salt.TwinBar.chiRe χ p / (p : ℝ))⁻¹) ^ 2
    * (if p ∣ q ∧ ¬ p ∣ α then 1 - 2 / (p : ℝ) else 1)
    * (if p ∣ α then (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)) ^ 2 else 1)
    * (if 2 < p then hbWfac χ α p else 1)
    * (if Salt.TwinBar.chiRe χ p = 1 ∧ ¬ p ∣ α then
        ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) * ((p : ℝ) + 1)) else 1)

/-- The `C(α)·∏(1−1/p)²·𝔖(z,χ)`-side factor at a prime `p`. -/
noncomputable def hbRearR (α p : ℕ) : ℝ :=
  (if p ∣ α ∧ p ≠ 2 then (1 - 2 / (p : ℝ))⁻¹ else 1)
    * (1 - 1 / (p : ℝ)) ^ 2
    * (if 2 < p then 1 - (((p : ℝ) - 1) ^ 2)⁻¹ else 1)

/-- **The per-prime identity behind `(4.4)`, at an odd prime `p`.**  Four cases:
`p ∣ α` (both sides `1`), and for `p ∤ α` the three values of `χ(p)` (both sides `(p−2)/p`). -/
lemma hb_rear_factor {q : ℕ} (χ : DirichletCharacter ℂ q) {α p : ℕ}
    (hchi01 : Salt.TwinBar.chiRe χ p = 1 ∨ Salt.TwinBar.chiRe χ p = -1 ∨
      Salt.TwinBar.chiRe χ p = 0)
    (hchi0 : Salt.TwinBar.chiRe χ p = 0 ↔ p ∣ q) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    hbRearL χ α p = hbRearR α p := by
  rw [hbRearL, hbRearR]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h2p : 2 < p := by omega
  have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : ((p : ℝ) - 1) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have hpm2 : ((p : ℝ) - 2) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have hpp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
  have hp0' : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have h2ne : (1 : ℝ) - 2 / (p : ℝ) ≠ 0 := by
    intro h
    rw [sub_eq_zero, eq_div_iff hp0'] at h
    linarith
  rw [if_pos h2p, if_pos h2p, hbWfac]
  by_cases hpα : p ∣ α
  · rw [if_neg (fun h : p ∣ q ∧ ¬ p ∣ α => h.2 hpα), if_pos hpα,
      if_neg (fun h : Salt.TwinBar.chiRe χ p = 1 ∧ ¬ p ∣ α => h.2 hpα),
      if_pos (⟨hpα, hp2⟩ : p ∣ α ∧ p ≠ 2), if_pos hpα]
    have hne : (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)) ≠ 0 :=
      ne_of_gt (one_sub_chiRe_div_pos χ hp)
    simp only [mul_one]
    rw [← mul_pow, inv_mul_cancel₀ hne, one_pow, eq_comm]
    field_simp
    ring
  · rw [if_neg (fun h : p ∣ α ∧ p ≠ 2 => hpα h.1), if_neg hpα, if_neg hpα, hbSfac]
    rcases hchi01 with h1 | h1 | h1
    · have hpq : ¬ p ∣ q := by
        intro h
        rw [hchi0.mpr h] at h1
        norm_num at h1
      rw [if_neg (fun h : p ∣ q ∧ ¬ p ∣ α => hpq h.1),
        if_pos (⟨h1, hpα⟩ : Salt.TwinBar.chiRe χ p = 1 ∧ ¬ p ∣ α), if_pos h1, h1]
      have hne1 : (1 : ℝ) - 1 / (p : ℝ) ≠ 0 := by
        intro h
        rw [sub_eq_zero, eq_div_iff hp0'] at h
        linarith
      field_simp
      ring
    · have hpq : ¬ p ∣ q := by
        intro h
        rw [hchi0.mpr h] at h1
        norm_num at h1
      rw [if_neg (fun h : p ∣ q ∧ ¬ p ∣ α => hpq h.1),
        if_neg (fun h : Salt.TwinBar.chiRe χ p = 1 ∧ ¬ p ∣ α => by
          rw [h.1] at h1; norm_num at h1),
        if_neg (show ¬ Salt.TwinBar.chiRe χ p = 1 by rw [h1]; norm_num), if_pos h1, h1]
      have hne1 : (1 : ℝ) - (-1) / (p : ℝ) ≠ 0 := by
        intro h
        rw [sub_eq_zero, eq_div_iff hp0'] at h
        linarith
      field_simp
      ring
    · have hpq : p ∣ q := hchi0.mp h1
      rw [if_pos (⟨hpq, hpα⟩ : p ∣ q ∧ ¬ p ∣ α),
        if_neg (fun h : Salt.TwinBar.chiRe χ p = 1 ∧ ¬ p ∣ α => by
          rw [h.1] at h1; norm_num at h1),
        if_neg (show ¬ Salt.TwinBar.chiRe χ p = 1 by rw [h1]; norm_num),
        if_neg (show ¬ Salt.TwinBar.chiRe χ p = -1 by rw [h1]; norm_num), h1]
      field_simp
      ring

/-- **The `p = 2` factor.**  Under `2 ∣ α` (HB's `(1.3)–(1.9)`) the left factor is `1` and the
right one is `1/4`; the missing `4` is exactly `C(α)`'s leading `2` times `𝔖(z,χ)`'s. -/
lemma hb_rear_factor_two {q : ℕ} (χ : DirichletCharacter ℂ q) {α : ℕ} (hα2 : 2 ∣ α) :
    hbRearL χ α 2 = 1 ∧ hbRearR α 2 = 1 / 4 := by
  constructor
  · rw [hbRearL, if_neg (fun h : (2 : ℕ) ∣ q ∧ ¬ (2 : ℕ) ∣ α => h.2 hα2), if_pos hα2,
      if_neg (fun h : Salt.TwinBar.chiRe χ 2 = 1 ∧ ¬ (2 : ℕ) ∣ α => h.2 hα2),
      if_neg (by norm_num : ¬ (2 : ℕ) < 2)]
    have hne : (1 - Salt.TwinBar.chiRe χ 2 / ((2 : ℕ) : ℝ)) ≠ 0 :=
      ne_of_gt (one_sub_chiRe_div_pos χ Nat.prime_two)
    simp only [mul_one]
    rw [← mul_pow, inv_mul_cancel₀ hne, one_pow]
  · rw [hbRearR, if_neg (fun h : (2 : ℕ) ∣ α ∧ (2 : ℕ) ≠ 2 => h.2 rfl),
      if_neg (by norm_num : ¬ (2 : ℕ) < 2)]
    norm_num

lemma gt2Primes_eq_filter {z : ℝ} :
    Salt.Mertens.gt2Primes ⌊z⌋₊ = (Pz z).filter (fun p => 2 < p) := by
  ext p
  simp only [Finset.mem_filter, mem_Pz, Finset.mem_range, Nat.lt_succ_iff]

/-- **The product form of `(4.4)`'s exact half**: over the primes `p ≤ ⌊z⌋`,

    ∏ (κS₁-side factor)  =  4 · ∏ (C(α)·∏(1−1/p)²·𝔖(z,χ)-side factor),

the `4` being the two leading `2`s, absorbed by the `p = 2` factor. -/
lemma hb_rear_prod_identity {q : ℕ} (χ : DirichletCharacter ℂ q) {α : ℕ} {z : ℝ}
    (hchi01 : ∀ p : ℕ, Nat.Prime p → Salt.TwinBar.chiRe χ p = 1 ∨
      Salt.TwinBar.chiRe χ p = -1 ∨ Salt.TwinBar.chiRe χ p = 0)
    (hchi0 : ∀ p : ℕ, Nat.Prime p → (Salt.TwinBar.chiRe χ p = 0 ↔ p ∣ q))
    (hα2 : 2 ∣ α) (hz : 3 ≤ z) :
    (∏ p ∈ Pz z, hbRearL χ α p) = 4 * ∏ p ∈ Pz z, hbRearR α p := by
  classical
  have h2mem : (2 : ℕ) ∈ Pz z := by
    refine mem_Pz.mpr ⟨?_, Nat.prime_two⟩
    have : (3 : ℕ) ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
    omega
  have hcong : ∀ p ∈ (Pz z).erase 2, hbRearL χ α p = hbRearR α p := by
    intro p hp
    have hpm := Finset.mem_of_mem_erase hp
    have hp2 := Finset.ne_of_mem_erase hp
    obtain ⟨_, hpp⟩ := mem_Pz.mp hpm
    exact hb_rear_factor χ (hchi01 p hpp) (hchi0 p hpp) hpp hp2
  obtain ⟨hL2, hR2⟩ := hb_rear_factor_two (α := α) χ hα2
  calc (∏ p ∈ Pz z, hbRearL χ α p)
      = hbRearL χ α 2 * ∏ p ∈ (Pz z).erase 2, hbRearL χ α p :=
        (Finset.mul_prod_erase _ _ h2mem).symm
    _ = 1 * ∏ p ∈ (Pz z).erase 2, hbRearR α p := by
        rw [hL2, Finset.prod_congr rfl hcong]
    _ = 4 * (hbRearR α 2 * ∏ p ∈ (Pz z).erase 2, hbRearR α p) := by
        rw [hR2]; ring
    _ = 4 * ∏ p ∈ Pz z, hbRearR α p := by
        rw [Finset.mul_prod_erase _ _ h2mem]

/-! ### The index-set conversions -/

lemma hbCalpha_eq {α : ℕ} {z : ℝ} (hα0 : 0 < α) (hαz : (α : ℝ) < z) :
    hbCalpha α = 2 * ∏ p ∈ Pz z, (if p ∣ α ∧ p ≠ 2 then (1 - 2 / (p : ℝ))⁻¹ else 1) := by
  classical
  have hαN : α ≤ ⌊z⌋₊ := Nat.le_floor hαz.le
  have hset : α.primeFactors.filter (fun p => p ≠ 2)
      = (Pz z).filter (fun p => p ∣ α ∧ p ≠ 2) := by
    ext p
    simp only [Finset.mem_filter, mem_Pz, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hpp, hpα, -⟩, hp2⟩
      exact ⟨⟨le_trans (Nat.le_of_dvd hα0 hpα) hαN, hpp⟩, hpα, hp2⟩
    · rintro ⟨⟨-, hpp⟩, hpα, hp2⟩
      exact ⟨⟨hpp, hpα, hα0.ne'⟩, hp2⟩
  rw [hbCalpha, hset, Finset.prod_filter]

lemma alpha_primeFactors_prod_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {α : ℕ} {z : ℝ}
    (hα0 : 0 < α) (hαz : (α : ℝ) < z) :
    (∏ p ∈ α.primeFactors, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)) ^ 2)
      = ∏ p ∈ Pz z, (if p ∣ α then (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)) ^ 2 else 1) := by
  classical
  have hαN : α ≤ ⌊z⌋₊ := Nat.le_floor hαz.le
  have hset : α.primeFactors = (Pz z).filter (fun p => p ∣ α) := by
    ext p
    simp only [Finset.mem_filter, mem_Pz, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hpp, hpα, -⟩
      exact ⟨⟨le_trans (Nat.le_of_dvd hα0 hpα) hαN, hpp⟩, hpα⟩
    · rintro ⟨⟨-, hpp⟩, hpα⟩
      exact ⟨hpp, hpα, hα0.ne'⟩
  rw [hset, Finset.prod_filter]

lemma qFactors_low_prod_eq {q α : ℕ} {z : ℝ} (hq : 0 < q) :
    (∏ p ∈ (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => p ≤ ⌊z⌋₊),
        (1 - 2 / (p : ℝ)))
      = ∏ p ∈ Pz z, (if p ∣ q ∧ ¬ p ∣ α then 1 - 2 / (p : ℝ) else 1) := by
  classical
  have hset : (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => p ≤ ⌊z⌋₊)
      = (Pz z).filter (fun p => p ∣ q ∧ ¬ p ∣ α) := by
    ext p
    simp only [Finset.mem_filter, mem_Pz, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨⟨hpp, hpq, -⟩, hpα⟩, hpN⟩
      exact ⟨⟨hpN, hpp⟩, hpq, hpα⟩
    · rintro ⟨⟨hpN, hpp⟩, hpq, hpα⟩
      exact ⟨⟨⟨hpp, hpq, hq.ne'⟩, hpα⟩, hpN⟩
  rw [hset, Finset.prod_filter]

lemma hbS1_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {α : ℕ} {z : ℝ} :
    hbS1 χ α z = ∏ p ∈ Pz z, (if Salt.TwinBar.chiRe χ p = 1 ∧ ¬ p ∣ α then
      ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) * ((p : ℝ) + 1)) else 1) := by
  classical
  rw [hbS1, show (Finset.range (⌊z⌋₊ + 1)).filter
      (fun p => Nat.Prime p ∧ Salt.TwinBar.chiRe χ p = 1 ∧ ¬ (p ∣ α))
      = (Pz z).filter (fun p => Salt.TwinBar.chiRe χ p = 1 ∧ ¬ (p ∣ α)) from by
    rw [Pz, Finset.filter_filter], Finset.prod_filter]

/-! ### The `κ`-tail split at `z` -/

/-- **The tails cancel.**  Under HB's `z > α`, every prime `p > ⌊z⌋` is coprime to `α`, so
`κ`'s Euler product factors as its `p ≤ ⌊z⌋` part times *exactly* `𝔖(z,χ)`'s tail. -/
lemma hbKappaTail_split {q : ℕ} (χ : DirichletCharacter ℂ q) {α : ℕ} {z : ℝ}
    (hα0 : 0 < α) (hαz : (α : ℝ) < z) :
    hbKappaTail χ α
      = (∏ p ∈ Pz z, (if 2 < p then hbWfac χ α p else 1)) * hbSingTail χ z := by
  classical
  set N : ℕ := ⌊z⌋₊ with hNdef
  have hαN : α ≤ N := Nat.le_floor hαz.le
  set W : Salt.TwinBar.PrimesGt2 → ℝ := fun p => hbWfac χ α (p : ℕ) with hWdef
  set tf : Salt.TwinBar.PrimesGt2 → ℝ :=
    fun p => if N < (p : ℕ) then hbSfac χ (p : ℕ) else 1 with htfdef
  have hWpos : ∀ p, 0 < W p := fun p => hbWfac_pos χ α (three_le_of_primesGt2 p)
  have hWsum : Summable (fun p => Real.log (W p)) := hbWfac_log_summable χ α
  have htfpos : ∀ p, 0 < tf p := by
    intro p
    rw [htfdef]
    dsimp only
    split_ifs
    · exact hbSfac_pos χ (three_le_of_primesGt2 p)
    · norm_num
  have htfsum : Summable (fun p => Real.log (tf p)) := by
    refine Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun p => ?_)
      summable_eight_div_sq)
    rw [htfdef]
    dsimp only
    split_ifs
    · exact abs_log_hbSfac_le χ (three_le_of_primesGt2 p)
    · rw [Real.log_one, abs_zero]; positivity
  set T : Finset Salt.TwinBar.PrimesGt2 :=
    (Salt.Mertens.gt2Primes N).subtype (fun p => p.Prime ∧ 2 < p) with hT
  have hTgt : ∀ x : Salt.TwinBar.PrimesGt2, x ∉ T → N < ((x : Salt.TwinBar.PrimesGt2) : ℕ) := by
    intro x hx
    rcases Nat.lt_or_ge N ((x : Salt.TwinBar.PrimesGt2) : ℕ) with h | h
    · exact h
    · exact absurd (by rw [hT, Finset.mem_subtype, Salt.Mertens.mem_gt2Primes]
                       exact ⟨h, x.2.1, x.2.2⟩) hx
  have hTle : ∀ x ∈ T, ((x : Salt.TwinBar.PrimesGt2) : ℕ) ≤ N := by
    intro x hx
    rw [hT, Finset.mem_subtype, Salt.Mertens.mem_gt2Primes] at hx
    exact hx.1
  have hnd : ∀ x : Salt.TwinBar.PrimesGt2, N < ((x : Salt.TwinBar.PrimesGt2) : ℕ) →
      ¬ ((x : Salt.TwinBar.PrimesGt2) : ℕ) ∣ α := by
    intro x hx hdvd
    have := Nat.le_of_dvd hα0 hdvd
    omega
  have h1 := hWsum.sum_add_tsum_subtype_compl T
  have h2 := htfsum.sum_add_tsum_subtype_compl T
  have hTz : ∑ p ∈ T, Real.log (tf p) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [htfdef]
    dsimp only
    rw [if_neg (by have := hTle p hp; omega), Real.log_one]
  have heq : (∑' x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T}, Real.log (W x))
      = ∑' x : {p : Salt.TwinBar.PrimesGt2 // p ∉ T}, Real.log (tf x) := by
    refine tsum_congr (fun x => ?_)
    have hgt := hTgt x.1 x.2
    rw [hWdef, htfdef]
    dsimp only
    rw [if_pos hgt, hbWfac, if_neg (hnd x.1 hgt)]
  have hKT : hbKappaTail χ α = Real.exp (∑' p, Real.log (W p)) :=
    (Real.rexp_tsum_eq_tprod hWpos hWsum).symm
  have hST : hbSingTail χ z = Real.exp (∑' p, Real.log (tf p)) :=
    (Real.rexp_tsum_eq_tprod htfpos htfsum).symm
  have hfin : (∏ p ∈ Pz z, (if 2 < p then hbWfac χ α p else 1))
      = Real.exp (∑ p ∈ T, Real.log (W p)) := by
    rw [Real.exp_sum]
    have hstep : ∏ p ∈ T, Real.exp (Real.log (W p)) = ∏ p ∈ T, W p :=
      Finset.prod_congr rfl (fun p _ => Real.exp_log (hWpos p))
    rw [hstep, hT]
    rw [Finset.prod_subtype_of_mem (fun k : ℕ => hbWfac χ α k)
      (fun x hx => ⟨(Salt.Mertens.mem_gt2Primes.mp hx).2.1,
        (Salt.Mertens.mem_gt2Primes.mp hx).2.2⟩)]
    rw [← Finset.prod_filter, ← gt2Primes_eq_filter, hNdef]
  rw [hKT, hST, hfin, ← h1, ← h2, hTz, heq, zero_add, Real.exp_add]

/-! ### The one error: HB's `p ∣ q, p > z` truncation -/

lemma one_sub_sum_le_prod_one_sub (g : ℕ → ℝ) :
    ∀ S : Finset ℕ, (∀ p ∈ S, 0 ≤ g p) → (∀ p ∈ S, g p ≤ 1) →
      1 - ∑ p ∈ S, g p ≤ ∏ p ∈ S, (1 - g p) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
      intro h0 h1
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hga0 : 0 ≤ g a := h0 a (Finset.mem_insert_self a s)
      have hga1 : g a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have h0s : ∀ p ∈ s, 0 ≤ g p := fun p hp => h0 p (Finset.mem_insert_of_mem hp)
      have h1s : ∀ p ∈ s, g p ≤ 1 := fun p hp => h1 p (Finset.mem_insert_of_mem hp)
      have hih := ih h0s h1s
      have hprod1 : ∏ p ∈ s, (1 - g p) ≤ 1 :=
        Finset.prod_le_one (fun p hp => by linarith [h0s p hp, h1s p hp])
          (fun p hp => by linarith [h0s p hp])
      have hsum0 : 0 ≤ ∑ p ∈ s, g p := Finset.sum_nonneg h0s
      nlinarith [hih, hprod1, hga0, hga1, hsum0,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - g a)
          (by linarith : (0 : ℝ) ≤ (∏ p ∈ s, (1 - g p)) - (1 - ∑ p ∈ s, g p)),
        mul_nonneg hga0 hsum0]

/-- **The truncation error, explicitly.**  For a finite set of primes,
`|∏ (1 − 2/p) − 1| ≤ 2 ∑ 1/p` — the Weierstrass bound, one-sided in each direction. -/
lemma abs_prod_one_sub_two_div_sub_one_le {S : Finset ℕ} (hS : ∀ p ∈ S, (2 : ℝ) ≤ (p : ℝ)) :
    |(∏ p ∈ S, (1 - 2 / (p : ℝ))) - 1| ≤ 2 * ∑ p ∈ S, 1 / (p : ℝ) := by
  classical
  have h0 : ∀ p ∈ S, (0 : ℝ) ≤ 2 / (p : ℝ) := by
    intro p hp; have := hS p hp; positivity
  have h1 : ∀ p ∈ S, (2 : ℝ) / (p : ℝ) ≤ 1 := by
    intro p hp
    have h := hS p hp
    rw [div_le_one (by linarith)]
    linarith
  have hlow := one_sub_sum_le_prod_one_sub (fun p => 2 / (p : ℝ)) S h0 h1
  have hhigh : ∏ p ∈ S, (1 - 2 / (p : ℝ)) ≤ 1 :=
    Finset.prod_le_one (fun p hp => by linarith [h0 p hp, h1 p hp])
      (fun p hp => by linarith [h0 p hp])
  have hsumeq : ∑ p ∈ S, 2 / (p : ℝ) = 2 * ∑ p ∈ S, 1 / (p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hsum0 : (0 : ℝ) ≤ ∑ p ∈ S, 1 / (p : ℝ) :=
    Finset.sum_nonneg (fun p hp => by have := hS p hp; positivity)
  rw [abs_le]
  constructor <;> linarith [hlow, hhigh, hsumeq]

/-! ### `(4.4)` -/

/-- **`(4.4)` — HB's rearrangement of `κ S₁`** (p.207):

    κ S₁ = {1 + a₁} · x · C(α) · F² · ∏_{p≤⌊z⌋}(1 − 1/p)² · 𝔖(z,χ),
    |a₁| ≤ 2 (log q / log z) / z = 2 z₀ / z .

Everything except `a₁` is an *exact* identity: the `p ≥ z` halves of `κ`'s Euler product are
literally `𝔖(z,χ)`'s (HB's `z > α`), and the `p ≤ ⌊z⌋` factors match one by one
(`hb_rear_prod_identity`).  `a₁` is HB's own truncation of `∏_{p∣q,p∤α}(1−2/p)` at `z`, priced by
`sum_recip_largePrimeFactors_le` (hb1983-notes:451).

`hL1` is the Euler product for `L(1,χ)` split at `z` — WP2 input, not sieve algebra. -/
theorem hb_hrear {q : ℕ} (χ : DirichletCharacter ℂ q) {α : ℕ} {z x L1 : ℝ}
    (hq : 0 < q)
    (hchi01 : ∀ p : ℕ, Nat.Prime p → Salt.TwinBar.chiRe χ p = 1 ∨
      Salt.TwinBar.chiRe χ p = -1 ∨ Salt.TwinBar.chiRe χ p = 0)
    (hchi0 : ∀ p : ℕ, Nat.Prime p → (Salt.TwinBar.chiRe χ p = 0 ↔ p ∣ q))
    (hα0 : 0 < α) (hα2 : 2 ∣ α) (hz : 3 ≤ z) (hαz : (α : ℝ) < z)
    (hL1 : L1 = (∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹ * hbF χ z) :
    ∃ e1 : ℝ,
      hbKappa χ α x L1 * hbS1 χ α z
        = (1 + e1) * (x * hbCalpha α * hbF χ z ^ 2 * primeProdBelow z ^ 2 * hbSingz χ z)
      ∧ |e1| ≤ 2 * (Real.log q / Real.log z) / z := by
  classical
  have hAsplit :
      (∏ p ∈ (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => p ≤ ⌊z⌋₊),
        (1 - 2 / (p : ℝ)))
      * (∏ p ∈ (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => ¬ p ≤ ⌊z⌋₊),
        (1 - 2 / (p : ℝ)))
      = ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ α), (1 - 2 / (p : ℝ)) :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  -- the exact half
  have hmaster : ((∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹) ^ 2
        * (∏ p ∈ (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => p ≤ ⌊z⌋₊),
            (1 - 2 / (p : ℝ)))
        * (∏ p ∈ α.primeFactors, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)) ^ 2)
        * (∏ p ∈ Pz z, (if 2 < p then hbWfac χ α p else 1))
        * hbS1 χ α z
      = hbCalpha α * primeProdBelow z ^ 2
          * (2 * ∏ p ∈ Salt.Mertens.gt2Primes ⌊z⌋₊, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)) := by
    have hL : ((∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹) ^ 2
        = ∏ p ∈ Pz z, ((1 - Salt.TwinBar.chiRe χ p / (p : ℝ))⁻¹) ^ 2 := by
      rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]
    have hP : primeProdBelow z ^ 2 = ∏ p ∈ Pz z, (1 - 1 / (p : ℝ)) ^ 2 := by
      rw [primeProdBelow_eq, ← Finset.prod_pow]
    have hT2 : (∏ p ∈ Salt.Mertens.gt2Primes ⌊z⌋₊, (1 - (((p : ℝ) - 1) ^ 2)⁻¹))
        = ∏ p ∈ Pz z, (if 2 < p then 1 - (((p : ℝ) - 1) ^ 2)⁻¹ else 1) := by
      rw [gt2Primes_eq_filter, Finset.prod_filter]
    have hEq := hb_rear_prod_identity χ hchi01 hchi0 hα2 hz (α := α) (z := z)
    simp only [hbRearL, hbRearR, Finset.prod_mul_distrib] at hEq
    rw [hL, qFactors_low_prod_eq (α := α) (z := z) hq,
      alpha_primeFactors_prod_eq χ hα0 hαz, hbS1_eq χ (α := α) (z := z),
      hbCalpha_eq hα0 hαz, hP, hT2]
    rw [hEq]
    ring
  refine ⟨(∏ p ∈ (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => ¬ p ≤ ⌊z⌋₊),
      (1 - 2 / (p : ℝ))) - 1, ?_, ?_⟩
  · rw [hbKappa, hL1, hbKappaTail_split χ hα0 hαz, hbSingz, ← hAsplit]
    linear_combination (x * hbF χ z ^ 2 * hbSingTail χ z
      * (∏ p ∈ (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => ¬ p ≤ ⌊z⌋₊),
        (1 - 2 / (p : ℝ)))) * hmaster
  · have hprime : ∀ p ∈ (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter
        (fun p => ¬ p ≤ ⌊z⌋₊), (2 : ℝ) ≤ (p : ℝ) := by
      intro p hp
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
      exact_mod_cast hp.1.1.1.two_le
    have hb := abs_prod_one_sub_two_div_sub_one_le hprime
    have hsub : (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => ¬ p ≤ ⌊z⌋₊)
        ⊆ q.primeFactors.filter (fun p => ⌊z⌋₊ < p) := by
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1.1, by omega⟩
    have hmono : ∑ p ∈ (q.primeFactors.filter (fun p => ¬ p ∣ α)).filter (fun p => ¬ p ≤ ⌊z⌋₊),
        1 / (p : ℝ) ≤ ∑ p ∈ q.primeFactors.filter (fun p => ⌊z⌋₊ < p), 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    have hkey := sum_recip_largePrimeFactors_le hq hz (by exact_mod_cast hq.ne')
    have hfin : 2 * (Real.log q / Real.log z) / z = 2 * ((Real.log q / Real.log z) / z) := by
      ring
    rw [hfin]
    linarith

/-! ## §7 — the capstone: `(L2)` with **no** free sieve binders -/

/-- **`(L2)` at the split point, fully discharged** — W4's `hb_L2_at_split_point` with its two
sieve-side binders `hrear`/`hsing` supplied by this file, so that `κ`, `C(α)` and `𝔖(z,χ)` are
now the corpus's own objects and the error is fully numeric:

    κ·S₁ = (1 + δ)·x·𝔖·C(α)/(ηL)²,
    |δ| ≤ 4(Ecorr + Eseg + Etail + 500(1 + 2 log ηL)/η) + 8·E_P
            + 2·(2 z₀/z) + 2·(64/z),      z₀ = log q / log z .

This is HB's `{1 + O(z₀(log η)^{−1/2})}` with every constant on the page. -/
theorem hb_L2_at_split_point_concrete {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {α : ℕ} {β₀ L η z x X L1 Ecorr Eseg Etail EP : ℝ} {Stail : ℂ}
    (hq : 0 < q)
    (hchi01 : ∀ p : ℕ, Nat.Prime p → Salt.TwinBar.chiRe χ p = 1 ∨
      Salt.TwinBar.chiRe χ p = -1 ∨ Salt.TwinBar.chiRe χ p = 0)
    (hchi0 : ∀ p : ℕ, Nat.Prime p → (Salt.TwinBar.chiRe χ p = 0 ↔ p ∣ q))
    (hα0 : 0 < α) (hα2 : 2 ∣ α)
    (hβ₀1 : β₀ < 1) (hL : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hz : 32 ≤ z) (hαz : (α : ℝ) < z)
    (hX : 3 ≤ X) (hwin : Real.log X ≤ 500 * L) (hηlarge : 500 ≤ η)
    (hm1 : zeroMult χ (β₀ : ℂ) = 1)
    (htail : ‖Stail + ((zeroMult χ (β₀ : ℂ) : ℕ) : ℂ)
        * ((∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v : ℝ) : ℂ)‖ ≤ Etail)
    (hseg : |(logChiSum χ z X).re
        - (Real.log (Real.log z) - Real.log (Real.log X))| ≤ Eseg)
    (hcorr : |Real.log (hbF χ z) - ((logChiSum χ z X).re + Stail.re)| ≤ Ecorr)
    (hP : |Real.log (primeProdBelow z) + Real.log (Real.log z)
        + Real.eulerMascheroniConstant| ≤ EP)
    (hL1 : L1 = (∏ p ∈ Pz z, (1 - Salt.TwinBar.chiRe χ p / (p : ℝ)))⁻¹ * hbF χ z)
    (hsmall : 4 * (Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η)
        + 8 * EP + 2 * (64 / z) ≤ 1) :
    ∃ δ : ℝ,
      hbKappa χ α x L1 * hbS1 χ α z
        = (1 + δ) * (x * Salt.HardyLittlewood.twinSingularSeries * hbCalpha α / (η * L) ^ 2)
      ∧ |δ| ≤ 4 * (Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η)
          + 8 * EP + 2 * (2 * (Real.log q / Real.log z) / z) + 2 * (64 / z) := by
  obtain ⟨e1, hrear, he1⟩ :=
    hb_hrear χ (x := x) hq hchi01 hchi0 hα0 hα2 (by linarith) hαz hL1
  obtain ⟨e2, hsing, he2⟩ := hb_hsing χ hz
  exact hb_L2_at_split_point χ hβ₀1 hL hη (by linarith) hαz hX hwin hηlarge hm1 htail hseg
    hcorr hP hrear hsing he1 he2 hsmall

end Salt.HB
