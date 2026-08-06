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

open Filter
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

end Salt.HB
