/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.TwinA1
import Salt.BrunLower.MertensDischarge

/-!
# C4b — the prime-power strip, the `x^{2/3}` weight-validity threshold, and Chen's weight
inequality (Tao Lemma 11)

Design: `docs/blueprints/chen.md`, the C4b row.  This file assembles the "weight-validity trivia"
of the Chen razor so that the C5 capstone is pure composition.  Three deliverables:

## 1. The window-threshold trivia (Part A)

On the twin window `[x/2, x−2]` the value `n + 2` always exceeds `x^{2/3}` (for `x ≥ 8`), so
Chen's weights (valid for `x^{2/3} < m ≤ x`) apply automatically at every window point.  The
governing arithmetic fact is `x^{2/3} ≤ x/2` for `x ≥ 8` (`rpow_two_thirds_le_half`), and then
`n + 2 > x/2 ≥ x^{2/3}`.  Also packaged: the crude `2·x^{7/8} + x^{1/3}`-loss bookkeeping
(`switch_loss_le`, the Lemma-37 losses of the S7 ledger row — bounded by `3·x^{7/8}` for `x ≥ 1`,
which C5 subtracts).

## 2. The prime-power strip (Part B)

The `½Σ_{p} 1_{p²∣n+2}` term of Chen's weight, **with the coprimality restriction** (only primes
`p ≥ z = x^{1/8}` contribute, since the sifted `n + 2` has no prime factor `< z`).  Summed against
the window `Λ`-mass:

  `Σ_{x/2 ≤ n ≤ x−2} Λ(n)·#{p : z ≤ p ≤ y, p²∣n+2}  ≤  log x · x / (z − 1)`,

which is `≈ x^{7/8} log x` — genuinely `o(x/log x)`, so C5 discards it.  The coprimality restriction
is essential: without the `p ≥ z` cut the same sum is `Θ(x log x)`.  The bridge
`sqStrip_eq_sqStripZ` lets C5 rewrite the weight's native `#{p ≤ y}` count as the `z`-restricted
`#{z ≤ p ≤ y}` count on the sifted sequence.

## 3. Chen's weight inequality (Part C)

The pointwise Tao Lemma 11: with `y = ⌊x^{1/3}⌋` and the P₂ carrier

  `IsP2 z m  :=  m.Prime  ∨  ∃ p q, p.Prime ∧ q.Prime ∧ m = p·q ∧ z ≤ p ∧ z ≤ q`

(the coprimality already forces `z ≤ p, q`, so this is exactly Tao's native semiprime-with-large-
factors form), the real-valued weight

  `chenWeight y m  :=  1 − ½·ω_{≤y}(m) − ½·1_{T}(m) − ½·S(m)`

(`ω_{≤y}` = distinct prime factors `≤ y`, `T` = the `p₁≤y<p₂≤p₃` triple pattern, `S` = the
prime-power strip count `#{p ≤ y : p²∣m}`) satisfies

  `chenWeight y m  ≤  1_{IsP2 z m}`

whenever every prime factor of `m` is `≥ z` and `m < (y+1)³` (i.e. `m ≤ x` with `y = ⌊x^{1/3}⌋`).
The content is the structural dichotomy `chen_weight_struct`: a non-`P₂` such `m` has
`ω_{≤y}(m) + 1_T(m) + S(m) ≥ 2`, by elementary casework on `Ω(m)` and the sizes of the factors.
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the `x^{2/3}` weight-validity threshold on the twin window -/

/-- `x^{2/3} ≤ x/2` for `x ≥ 8`.  Since `x = x^{2/3}·x^{1/3}` and `x^{1/3} ≥ 8^{1/3} = 2`, we get
`x/2 = x^{2/3}·(x^{1/3}/2) ≥ x^{2/3}·1`. -/
theorem rpow_two_thirds_le_half {x : ℕ} (hx : 8 ≤ x) :
    (x : ℝ) ^ ((2 : ℝ) / 3) ≤ (x : ℝ) / 2 := by
  have hx8 : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hX : (0 : ℝ) < (x : ℝ) := by linarith
  -- x = x^{2/3}·x^{1/3}
  have hsplit : (x : ℝ) = (x : ℝ) ^ ((2 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hX]; norm_num
  -- x^{1/3} ≥ 2
  have h8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num,
        show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  have h13 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    calc (2 : ℝ) = (8 : ℝ) ^ ((1 : ℝ) / 3) := h8.symm
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by norm_num) hx8 (by norm_num)
  have h23nn : (0 : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hX.le _
  calc (x : ℝ) ^ ((2 : ℝ) / 3) = (x : ℝ) ^ ((2 : ℝ) / 3) * 1 := by ring
    _ ≤ (x : ℝ) ^ ((2 : ℝ) / 3) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 2) := by
        apply mul_le_mul_of_nonneg_left _ h23nn; linarith
    _ = (x : ℝ) ^ ((2 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) / 2 := by ring
    _ = (x : ℝ) / 2 := by rw [← hsplit]

/-- **The weight-validity threshold.**  For `x ≥ 8` and `n` in the twin window `[x/2, x−2]`, the
weight argument `m = n + 2` satisfies `x^{2/3} < m ≤ x`, so Chen's weights (Lemma 11) apply at
every window point. -/
theorem window_two_thirds_lt {x : ℕ} (hx : 8 ≤ x) {n : ℕ} (hn : n ∈ twinWindow x) :
    (x : ℝ) ^ ((2 : ℝ) / 3) < (n : ℝ) + 2 ∧ (n : ℝ) + 2 ≤ (x : ℝ) := by
  rw [twinWindow, Finset.mem_Icc] at hn
  obtain ⟨hlo, hhi⟩ := hn
  have hx2 : 2 ≤ x := by omega
  constructor
  · -- x^{2/3} ≤ x/2 < x/2 + 3/2 ≤ n + 2
    have hhalf := rpow_two_thirds_le_half hx
    -- (x/2 : ℕ) ≥ (x - 1)/2 as reals: 2·(x/2) ≥ x − 1
    have hdiv : (x : ℝ) - 1 ≤ 2 * ((x / 2 : ℕ) : ℝ) := by
      have h2 : ((x - 1 : ℕ) : ℝ) ≤ ((2 * (x / 2) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : x - 1 ≤ 2 * (x / 2))
      rw [Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_mul] at h2
      push_cast at h2; linarith
    have hnlo : ((x / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
    linarith
  · -- n ≤ x − 2 ⟹ n + 2 ≤ x
    have : (n : ℝ) ≤ ((x - 2 : ℕ) : ℝ) := by exact_mod_cast hhi
    have hcast : ((x - 2 : ℕ) : ℝ) = (x : ℝ) - 2 := by
      have : (2 : ℕ) ≤ x := hx2
      push_cast [Nat.cast_sub this]; ring
    rw [hcast] at this; linarith

/-- **The Lemma-37 switch losses, crude form.**  The `2·N^{7/8} + N^{1/3}` drift of the switching
step (S7 ledger row) is bounded by `3·N^{7/8}` for `N ≥ 1` (since `N^{1/3} ≤ N^{7/8}`).  C5
subtracts this explicit `o(x/log x)` quantity. -/
theorem switch_loss_le {N : ℕ} (hN : 1 ≤ N) :
    2 * (N : ℝ) ^ ((7 : ℝ) / 8) + (N : ℝ) ^ ((1 : ℝ) / 3) ≤ 3 * (N : ℝ) ^ ((7 : ℝ) / 8) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmono : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  linarith

/-! ## Part B — the prime-power strip (with the coprimality restriction) -/

/-- The primes in the interval `[z, y]` — the effective range of the strip after the coprimality
cut removes all primes `< z`. -/
def primeItv (z y : ℕ) : Finset ℕ := (Finset.Icc z y).filter Nat.Prime

/-- The weight's native prime-power strip count `S(m) = #{p ≤ y : p²∣m}` (no lower cut). -/
def sqStrip (y m : ℕ) : ℕ := (m.primeFactors.filter (fun p => p ≤ y ∧ p ^ 2 ∣ m)).card

/-- The coprimality-restricted strip count `#{p : z ≤ p ≤ y, p²∣m}` — the count that actually
appears when `m` is sifted coprime to `P(z)`. -/
def sqStripZ (z y m : ℕ) : ℕ := ((primeItv z y).filter (fun p => p ^ 2 ∣ m)).card

/-- **The strip bridge.**  On the sifted sequence — every prime factor of `m` is `≥ z` — the
weight's native count equals the `z`-restricted count, because no prime `< z` divides `m`. -/
theorem sqStrip_eq_sqStripZ {z y m : ℕ} (hm : m ≠ 0)
    (hcop : ∀ p ∈ m.primeFactors, z ≤ p) :
    sqStrip y m = sqStripZ z y m := by
  unfold sqStrip sqStripZ
  apply congrArg Finset.card
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hpd, _⟩, hpy, hsq⟩ := hp
    rw [Finset.mem_filter, primeItv, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨hcop p (Nat.mem_primeFactors.mpr ⟨hpp, hpd, hm⟩), hpy⟩, hpp⟩, hsq⟩
  · intro hp
    rw [Finset.mem_filter, primeItv, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨_hzp, hpy⟩, hpp⟩, hsq⟩ := hp
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    have hpd : p ∣ m := dvd_trans (dvd_pow_self p (by norm_num)) hsq
    exact ⟨⟨hpp, hpd, hm⟩, hpy, hsq⟩

/-- Per-prime interval count: the number of window points `n` with `d ∣ n+2` is at most `x/d`
(the multiples of `d` in `(0, x]` upper-bound it via the injection `n ↦ n+2`). -/
theorem card_window_dvd_le {x d : ℕ} (hx : 2 ≤ x) :
    (((twinWindow x).filter (fun n => d ∣ (n + 2))).card : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  have hcard : ((twinWindow x).filter (fun n => d ∣ (n + 2))).card
      ≤ ((Finset.Ioc 0 x).filter (fun m => d ∣ m)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n + 2)
    · intro n hn
      rw [Finset.mem_coe, Finset.mem_filter] at hn
      rw [Finset.mem_coe, Finset.mem_filter]
      obtain ⟨hnw, hnd⟩ := hn
      rw [twinWindow, Finset.mem_Icc] at hnw
      obtain ⟨hlo, hhi⟩ := hnw
      have hub : n + 2 ≤ x := by
        calc n + 2 ≤ (x - 2) + 2 := Nat.add_le_add_right hhi 2
          _ = x := Nat.sub_add_cancel hx
      exact ⟨Finset.mem_Ioc.mpr ⟨by positivity, hub⟩, hnd⟩
    · intro a _ b _ h; simpa using h
  have hdiv : ((Finset.Ioc 0 x).filter (fun m => d ∣ m)).card = x / d :=
    Nat.Ioc_filter_dvd_card_eq_div x d
  calc (((twinWindow x).filter (fun n => d ∣ (n + 2))).card : ℝ)
      ≤ (((Finset.Ioc 0 x).filter (fun m => d ∣ m)).card : ℝ) := by exact_mod_cast hcard
    _ = ((x / d : ℕ) : ℝ) := by rw [hdiv]
    _ ≤ (x : ℝ) / (d : ℝ) := Nat.cast_div_le

/-- **The prime-power strip bound.**  With the coprimality restriction (`z ≤ p`), the window
`Λ`-mass weighted by the strip count is `≤ log x · x/(z−1) ≈ x^{7/8} log x`, hence `o(x/log x)`.
-/
theorem stripSum_le {x z y : ℕ} (hx : 2 ≤ x) (hz : 2 ≤ z) :
    ∑ n ∈ twinWindow x, vonMangoldt n * (sqStripZ z y (n + 2) : ℝ)
      ≤ Real.log x * (x : ℝ) / ((z : ℝ) - 1) := by
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  -- rewrite the count as a sum of indicators over primeItv
  have hcount : ∀ n, (sqStripZ z y (n + 2) : ℝ)
      = ∑ p ∈ primeItv z y, (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0) := by
    intro n
    unfold sqStripZ
    rw [Finset.card_filter]
    push_cast
    rfl
  -- expand, swap the order of summation
  have hexpand : ∑ n ∈ twinWindow x, vonMangoldt n * (sqStripZ z y (n + 2) : ℝ)
      = ∑ p ∈ primeItv z y,
          ∑ n ∈ twinWindow x, vonMangoldt n * (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0) := by
    have hstep : ∑ n ∈ twinWindow x, vonMangoldt n * (sqStripZ z y (n + 2) : ℝ)
        = ∑ n ∈ twinWindow x,
            ∑ p ∈ primeItv z y, vonMangoldt n * (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hcount n, Finset.mul_sum]
    rw [hstep, Finset.sum_comm]
  rw [hexpand]
  -- per-prime bound
  have hper : ∀ p ∈ primeItv z y,
      ∑ n ∈ twinWindow x, vonMangoldt n * (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0)
        ≤ Real.log x * ((x : ℝ) / ((p : ℝ) ^ 2)) := by
    intro p hp
    have hstep1 : ∑ n ∈ twinWindow x, vonMangoldt n * (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0)
        ≤ ∑ n ∈ twinWindow x, Real.log x * (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hd : p ^ 2 ∣ (n + 2)
      · simp only [hd, if_true, mul_one]
        refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
        · exact_mod_cast (by rw [twinWindow, Finset.mem_Icc] at hn; omega : 1 ≤ n)
        · rw [twinWindow, Finset.mem_Icc] at hn
          have hle : (n : ℝ) ≤ ((x - 2 : ℕ) : ℝ) := by exact_mod_cast hn.2
          have hc : ((x - 2 : ℕ) : ℝ) = (x : ℝ) - 2 := by
            push_cast [Nat.cast_sub (by omega : 2 ≤ x)]; ring
          rw [hc] at hle; linarith
      · simp [hd]
    have hstep2 : ∑ n ∈ twinWindow x, Real.log x * (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0)
        = Real.log x * (((twinWindow x).filter (fun n => p ^ 2 ∣ (n + 2))).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.card_filter]
      push_cast
      rfl
    have hstep3 : (((twinWindow x).filter (fun n => p ^ 2 ∣ (n + 2))).card : ℝ)
        ≤ (x : ℝ) / ((p : ℝ) ^ 2) := by
      have := card_window_dvd_le (x := x) (d := p ^ 2) hx
      calc (((twinWindow x).filter (fun n => p ^ 2 ∣ (n + 2))).card : ℝ)
          ≤ (x : ℝ) / ((p ^ 2 : ℕ) : ℝ) := this
        _ = (x : ℝ) / ((p : ℝ) ^ 2) := by push_cast; ring
    calc ∑ n ∈ twinWindow x, vonMangoldt n * (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0)
        ≤ Real.log x * (((twinWindow x).filter (fun n => p ^ 2 ∣ (n + 2))).card : ℝ) := by
          rw [← hstep2]; exact hstep1
      _ ≤ Real.log x * ((x : ℝ) / ((p : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep3 hlogx
  -- assemble the per-prime bounds and the 1/p² telescope
  calc ∑ p ∈ primeItv z y,
          ∑ n ∈ twinWindow x, vonMangoldt n * (if p ^ 2 ∣ (n + 2) then (1 : ℝ) else 0)
      ≤ ∑ p ∈ primeItv z y, Real.log x * ((x : ℝ) / ((p : ℝ) ^ 2)) := Finset.sum_le_sum hper
    _ = Real.log x * (x : ℝ) * ∑ p ∈ primeItv z y, (1 : ℝ) / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ Real.log x * (x : ℝ) * (1 / ((z : ℝ) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsub : ∑ p ∈ primeItv z y, (1 : ℝ) / ((p : ℝ) ^ 2)
            ≤ ∑ m ∈ Finset.Icc z y, (1 : ℝ) / ((m : ℝ) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; rw [primeItv, Finset.mem_filter] at hp; exact hp.1
          · intro _ _ _; positivity
        exact le_trans hsub (Salt.BrunLower.sum_one_div_sq_le hz)
    _ = Real.log x * (x : ℝ) / ((z : ℝ) - 1) := by ring

/-! ## Part C — Chen's weight inequality (Tao Lemma 11) -/

/-- **The P₂ carrier.**  `m` is `P₂` when it is prime or a product of two primes, both `≥ z`.
Since the sifted sequence forces every prime factor of `m` to be `≥ z`, the size decorations are
automatic — this is exactly Tao's native "prime, or semiprime with both factors large" form. -/
def IsP2 (z m : ℕ) : Prop :=
  m.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q ∧ z ≤ p ∧ z ≤ q

/-- `1_{P₂}(m)` — the `P₂` indicator, the LHS Chen's weight lower-bounds. -/
noncomputable def p2Ind (z m : ℕ) : ℝ := by
  classical exact if IsP2 z m then 1 else 0

/-- `ω_{≤y}(m)` — the number of distinct prime factors of `m` that are `≤ y`. -/
def omegaLe (y m : ℕ) : ℕ := (m.primeFactors.filter (· ≤ y)).card

/-- The Chen triple pattern `m = p₁p₂p₃`, `p₁ ≤ y < p₂ ≤ p₃`. -/
def TripleP (y m : ℕ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ m = p₁ * p₂ * p₃
    ∧ p₁ ≤ y ∧ y < p₂ ∧ p₂ ≤ p₃

/-- `1_T(m)` — the indicator of Chen's triple pattern. -/
noncomputable def tripleT (y m : ℕ) : ℝ := by
  classical exact if TripleP y m then 1 else 0

/-- `tripleT` is `0` or `1`, hence nonnegative. -/
theorem tripleT_nonneg (y m : ℕ) : 0 ≤ tripleT y m := by
  unfold tripleT; split_ifs <;> norm_num

/-- `tripleT` equals `1` once the triple pattern holds. -/
theorem tripleT_eq_one {y m : ℕ} (h : TripleP y m) : tripleT y m = 1 := by
  unfold tripleT; rw [if_pos h]

/-- **Chen's real-valued weight** `1 − ½ω_{≤y} − ½·1_T − ½S`, the RHS of Tao's Lemma 11. -/
noncomputable def chenWeight (y m : ℕ) : ℝ :=
  1 - (1 / 2) * (omegaLe y m : ℝ) - (1 / 2) * tripleT y m - (1 / 2) * (sqStrip y m : ℝ)

/-- `Ω(m) = 2` forces `m` to be a product of two primes (no ordering needed). -/
theorem exists_two_primes_of_cardFactors_eq_two {m : ℕ} (h : cardFactors m = 2) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q := by
  rw [cardFactors_apply] at h
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp h
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.primeFactorsList_zero] at hpq
    exact (List.cons_ne_nil p [q]) hpq.symm
  have hprod : m = p * q := by
    have hp := Nat.prod_primeFactorsList hm0
    rw [hpq] at hp
    simpa using hp.symm
  have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hpq]; simp)
  have hqp : q.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hpq]; simp)
  exact ⟨p, q, hpp, hqp, hprod⟩

/-- `Ω(n) = ∑_{p ∣ n} v_p(n)` over the distinct prime factors (the `Finset.sum` form of
`cardFactors_eq_sum_factorization`). -/
theorem cardFactors_eq_sum_pf (n : ℕ) :
    cardFactors n = ∑ p ∈ n.primeFactors, n.factorization p := by
  rw [cardFactors_eq_sum_factorization]; rfl

/-- **The size lemma.**  If `n < (y+1)³` then `n` has at most two prime factors `> y` (counted with
multiplicity): three such factors would force `n ≥ (y+1)³`.  This is the only size input Lemma 11
needs. -/
theorem large_mult_le_two {y n : ℕ} (hn : n ≠ 0) (hny : n < (y + 1) ^ 3) :
    (∑ p ∈ n.primeFactors.filter (fun p => y < p), n.factorization p) ≤ 2 := by
  by_contra hcon
  rw [not_le] at hcon
  have h3 : 3 ≤ ∑ p ∈ n.primeFactors.filter (fun p => y < p), n.factorization p := hcon
  set S := n.primeFactors.filter (fun p => y < p) with hSdef
  have hpow : (y + 1) ^ 3 ≤ (y + 1) ^ (∑ p ∈ S, n.factorization p) :=
    Nat.pow_le_pow_right (by omega) h3
  have hchain : (y + 1) ^ (∑ p ∈ S, n.factorization p) ≤ n := by
    calc (y + 1) ^ (∑ p ∈ S, n.factorization p)
        = ∏ p ∈ S, (y + 1) ^ n.factorization p :=
          (Finset.prod_pow_eq_pow_sum S (fun p => n.factorization p) (y + 1)).symm
      _ ≤ ∏ p ∈ S, p ^ n.factorization p := by
          gcongr with p hp
          have : y < p := (Finset.mem_filter.mp hp).2
          omega
      _ ≤ ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
          apply Finset.prod_le_prod_of_subset_of_one_le'
          · exact Finset.filter_subset _ _
          · intro p hp _
            exact Nat.one_le_pow _ _ (Nat.pos_of_mem_primeFactors hp)
      _ = n := Nat.prod_factorization_pow_eq_self hn
  omega

/-- **Non-`P₂` ⟹ `Ω(m) ≥ 3`.**  A number in the sifted range (`2 ≤ m`, all prime factors `≥ z`)
that is neither prime nor a product of two primes has at least three prime factors. -/
theorem not_isP2_cardFactors_ge_three {z m : ℕ} (hm2 : 2 ≤ m)
    (hcop : ∀ p ∈ m.primeFactors, z ≤ p) (hp2 : ¬ IsP2 z m) :
    3 ≤ cardFactors m := by
  have hm0 : m ≠ 0 := by omega
  by_contra hlt
  rw [not_le] at hlt
  have h0 : cardFactors m ≠ 0 := by
    rw [Ne, cardFactors_eq_zero_iff_eq_zero_or_one]
    simp only [not_or]; omega
  rcases (by omega : cardFactors m = 1 ∨ cardFactors m = 2) with h1 | h2
  · exact hp2 (Or.inl (cardFactors_eq_one_iff_prime.mp h1))
  · obtain ⟨p, q, hpp, hqp, hpq⟩ := exists_two_primes_of_cardFactors_eq_two h2
    have hpd : p ∣ m := by rw [hpq]; exact dvd_mul_right p q
    have hqd : q ∣ m := by rw [hpq]; exact dvd_mul_left q p
    exact hp2 (Or.inr ⟨p, q, hpp, hqp, hpq,
      hcop p (Nat.mem_primeFactors.mpr ⟨hpp, hpd, hm0⟩),
      hcop q (Nat.mem_primeFactors.mpr ⟨hqp, hqd, hm0⟩)⟩)

/-- **The reduction (C5-facing).**  Given the structural dichotomy `hstruct` (a non-`P₂` `m` has
`ω_{≤y} + 1_T + S ≥ 2`), Chen's weight is dominated by the `P₂` indicator. -/
theorem chen_weight_le_indicator {z y m : ℕ}
    (hstruct : ¬ IsP2 z m → 2 ≤ (omegaLe y m : ℝ) + tripleT y m + (sqStrip y m : ℝ)) :
    chenWeight y m ≤ p2Ind z m := by
  have hTnn : 0 ≤ tripleT y m := tripleT_nonneg y m
  unfold p2Ind
  by_cases hp2 : IsP2 z m
  · rw [if_pos hp2, chenWeight]
    have ho : 0 ≤ (omegaLe y m : ℝ) := by positivity
    have hs : 0 ≤ (sqStrip y m : ℝ) := by positivity
    linarith
  · rw [if_neg hp2, chenWeight]
    have := hstruct hp2
    linarith

/-- **Chen's weight inequality (Tao Lemma 11), structural core.**  For `m` in the sifted range
(`2 ≤ m`, every prime factor `≥ z`, `m < (y+1)³`), if `m` is not `P₂` then
`ω_{≤y}(m) + 1_T(m) + S(m) ≥ 2`.  Elementary casework on the number and sizes of the prime
factors. -/
theorem chen_weight_struct {z y m : ℕ} (hm2 : 2 ≤ m)
    (hcop : ∀ p ∈ m.primeFactors, z ≤ p) (hmy : m < (y + 1) ^ 3) (hp2 : ¬ IsP2 z m) :
    2 ≤ (omegaLe y m : ℝ) + tripleT y m + (sqStrip y m : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  have hΩ3 : 3 ≤ cardFactors m := not_isP2_cardFactors_ge_three hm2 hcop hp2
  have hTnn : 0 ≤ tripleT y m := tripleT_nonneg y m
  have hSnn : 0 ≤ (sqStrip y m : ℝ) := by positivity
  rcases (by omega : omegaLe y m = 0 ∨ omegaLe y m = 1 ∨ 2 ≤ omegaLe y m)
    with hol0 | hol1 | hol2
  · -- ω = 0: all prime factors > y, so Ω(m) ≤ 2, contradicting Ω ≥ 3
    exfalso
    rw [omegaLe, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hol0
    have hall : ∀ p ∈ m.primeFactors, y < p := fun p hp => not_le.mp (hol0 hp)
    have hfilter : m.primeFactors.filter (fun p => y < p) = m.primeFactors :=
      Finset.filter_true_of_mem hall
    have hbig := large_mult_le_two hm0 hmy
    rw [hfilter, ← cardFactors_eq_sum_pf] at hbig
    omega
  · -- ω = 1: the unique small prime p₀
    have hol1' : (m.primeFactors.filter (· ≤ y)).card = 1 := hol1
    obtain ⟨p₀, hp₀set⟩ := Finset.card_eq_one.mp hol1'
    have hp₀mem : p₀ ∈ m.primeFactors.filter (· ≤ y) := by
      rw [hp₀set]; exact Finset.mem_singleton_self p₀
    rw [Finset.mem_filter] at hp₀mem
    obtain ⟨hp₀pf, hp₀le⟩ := hp₀mem
    have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀pf
    have hp₀dvd : p₀ ∣ m := Nat.dvd_of_mem_primeFactors hp₀pf
    have hsmall : ∀ s ∈ m.primeFactors, s ≤ y → s = p₀ := by
      intro s hs hsle
      have : s ∈ m.primeFactors.filter (· ≤ y) := Finset.mem_filter.mpr ⟨hs, hsle⟩
      rw [hp₀set, Finset.mem_singleton] at this; exact this
    have ho1 : (omegaLe y m : ℝ) = 1 := by rw [omegaLe]; exact_mod_cast hol1'
    by_cases hsq : p₀ ^ 2 ∣ m
    · -- B1: p₀² ∣ m ⟹ S ≥ 1
      have hsqpos : 0 < sqStrip y m := by
        rw [sqStrip, Finset.card_pos]
        exact ⟨p₀, Finset.mem_filter.mpr ⟨hp₀pf, hp₀le, hsq⟩⟩
      have h1 : (1 : ℝ) ≤ (sqStrip y m : ℝ) := by exact_mod_cast hsqpos
      linarith
    · -- B2: ¬ p₀² ∣ m ⟹ the triple pattern fires
      set L := m / p₀ with hLdef
      have hmL : m = p₀ * L := (Nat.mul_div_cancel' hp₀dvd).symm
      have hL0 : L ≠ 0 := by
        rintro hL0'
        rw [hL0', mul_zero] at hmL; exact hm0 hmL
      have hp₀0 : p₀ ≠ 0 := hp₀prime.ne_zero
      have hΩmul : cardFactors m = 1 + cardFactors L := by
        rw [hmL, cardFactors_mul hp₀0 hL0, cardFactors_apply_prime hp₀prime]
      have hΩL2 : 2 ≤ cardFactors L := by omega
      have hLm_dvd : L ∣ m := by rw [hmL]; exact dvd_mul_left L p₀
      have hp₀nL : ¬ p₀ ∣ L := by
        intro hdvd
        apply hsq
        rw [hmL]
        obtain ⟨k, hk⟩ := hdvd
        rw [hk]; exact ⟨k, by ring⟩
      have hLlarge : ∀ s ∈ L.primeFactors, y < s := by
        intro s hs
        have hsp : s.Prime := Nat.prime_of_mem_primeFactors hs
        have hsL : s ∣ L := Nat.dvd_of_mem_primeFactors hs
        have hsm : s ∣ m := hsL.trans hLm_dvd
        have hspf : s ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hsp, hsm, hm0⟩
        by_contra hsle
        rw [not_lt] at hsle
        have hs0 : s = p₀ := hsmall s hspf hsle
        rw [hs0] at hsL; exact hp₀nL hsL
      have hLm : L ≤ m := by rw [hmL]; exact Nat.le_mul_of_pos_left L hp₀prime.pos
      have hLy : L < (y + 1) ^ 3 := lt_of_le_of_lt hLm hmy
      have hbigL := large_mult_le_two hL0 hLy
      have hfilterL : L.primeFactors.filter (fun s => y < s) = L.primeFactors :=
        Finset.filter_true_of_mem hLlarge
      rw [hfilterL, ← cardFactors_eq_sum_pf] at hbigL
      have hΩLeq : cardFactors L = 2 := le_antisymm hbigL hΩL2
      obtain ⟨q, r, hqp, hrp, hLqr⟩ := exists_two_primes_of_cardFactors_eq_two hΩLeq
      have hqmem : q ∈ L.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp, by rw [hLqr]; exact dvd_mul_right q r, hL0⟩
      have hrmem : r ∈ L.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hrp, by rw [hLqr]; exact dvd_mul_left r q, hL0⟩
      have hqy : y < q := hLlarge q hqmem
      have hry : y < r := hLlarge r hrmem
      have htp : TripleP y m := by
        rcases le_total q r with hqr | hrq
        · exact ⟨p₀, q, r, hp₀prime, hqp, hrp, by rw [hmL, hLqr]; ring, hp₀le, hqy, hqr⟩
        · exact ⟨p₀, r, q, hp₀prime, hrp, hqp, by rw [hmL, hLqr]; ring, hp₀le, hry, hrq⟩
      rw [tripleT_eq_one htp]; linarith
  · -- ω ≥ 2: two distinct small prime factors already give ≥ 2
    have h2 : (2 : ℝ) ≤ (omegaLe y m : ℝ) := by exact_mod_cast hol2
    linarith

end Salt.Chen
