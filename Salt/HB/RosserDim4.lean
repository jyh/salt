/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs
import Salt.BrunLower.WRatio
import Salt.BrunLower.MertensWindow
import Salt.BrunLower.MertensDischarge
import Salt.BrunLower.Pair

/-!
# The dimension-4 instantiation of the H-R block-Brun sieve (N5 wave 1)

Heath-Brown's 1983 "Prime twins and Siegel zeros" (Acta Arith. 42) sifts, at its
Lemma 6, a set whose density is `G(p) = 2(2p−1)/(p+1) ≤ 4` — "as `G(p) ≤ 4` we
need a sieve of dimension 4".  `Salt/BrunLower` already carries Halberstam–Richert's
Théorème 2 (`brun_lower`/`brun_upper`) in **dimension-general** form: the sieve
dimension `A` is a free real, the main-term relative error is `A`-free, and `A`
enters at exactly two places — the ladder scale `Λ = 2λ/A` (through `hMert`) and the
remainder-side uniform density bound `hωA : ω(p) ≤ A`.

This file is the `A = 4` instantiation, in two independent parts.

## a1 — the level bound (the wave's one C-class stone)

`chi_log_le_level` / `chi_le_rpow_level`: every `d` kept by the block predicate
`chi Λ z ν b` (H-R (2.10), the restricted-count form of `Salt/BrunLower/Defs.lean`)
that is squarefree with all prime factors below `z` satisfies

  `log d ≤ log z · (2b − ν − 1 + 2·e^Λ/(e^Λ − 1))`,  i.e.  `d ≤ z^{2b−ν−1+2e^Λ/(e^Λ−1)}`.

This is the block-Brun analogue of the Iwaniec `S`-set support bound
`δ ≤ Max(D, z²)` that HB's decomposition identity (p. 199) carries: it says the
kept set lives below an explicit power of `z`, uniformly in `d`.

The proof is Abel summation over the ladder against the restricted counts.  Write
`c_n = #{p ∣ d : p ≥ z_n}` (`bigOmegaGe`), `q = e^{−Λ}`, `r = minLevel Λ z`.  The
ladder windows `[z_{n+1}, z_n)` partition the prime factors of `d` (`c_0 = 0`
because every `p < z = z_0`; `c_r = ω(d)` because `z_r ≤ 2`), and every prime in the
`n`-th window has `log p ≤ log z_n = q^n log z`, so

  `log d ≤ log z · Σ_{n<r} (c_{n+1} − c_n) q^n`.

Summation by parts (`abel_ladder_identity`) turns the increment sum into
`q·Σ = c_r q^r + (1−q)Σ_{n<r} c_n q^n`; feeding the block bounds
`c_n ≤ 2b − ν + 2n − 1` and the exact geometric identity `ladder_geom_identity`
gives `Σ ≤ (2b − ν − 1) + 2/(1 − q)`, and `2/(1 − e^{−Λ}) = 2e^Λ/(e^Λ − 1)`.

**The constant is the true one.**  The ROSSER-SCOPE derivation sketch
(`log d ≤ log z·(e^Λ−1)·Σ_{n≥1}(2b−ν+2n−1)e^{−nΛ}`, geometric series in closed form)
was re-derived here at the bytes of `Defs.lean`'s ladder and is confirmed:
`(e^Λ−1)·Σ_{n≥1}(c+2n)q^n = c + 2/(1−q)` with `c = 2b−ν−1`, `q = e^{−Λ}`.  No delta.
(The finite ladder contributes a boundary term `c_r q^{r−1}`, which the infinite
tail of the majorant absorbs exactly; `ladder_geom_identity` records the finite
closed form with its `−2q^{r+1}/(1−q)` deficit, so the bound is *not* tight at
finite `r` — it is the `r → ∞` envelope, which is what a uniform statement needs.)

## a3 — the dimension-4 Mertens package

`hMert_dim4`, `kappa_dim4`, `Gdens_le_four`: the three hypotheses of
`Salt.BrunLower.brun_lower`/`brun_upper` that carry the sieve dimension, discharged
at `A = 4`, `Λ = 2λ/A = λ/2`, `κ = A·Λ = 2λ`, for HB's sifting data: an arbitrary
(sparse) set of odd sifting primes with density `ω(p) = G(p) = 2(2p−1)/(p+1) ≤ 4`.

The `A = 2` precedent is `Salt.BrunLower.hMert_twin`; the chain is the same four
steps at the `4/p` density, with the constants re-derived:

* `neg_log_one_sub_nu_le_dim4`: `−log(1 − ν(p)) ≤ 4/p + 33/p²` for `p ≥ 3` at
  `ν(p) ≤ G(p)/p` (the constant `33` is *exact* at `p = 3`: the difference
  polynomial is `23p² − 91p + 66 = 23(p−3)(p−66/69)`);
* `log_Wratio_le_ladder_dim4`: `log(W(z_n)/W(z)) ≤ 4nΛ + 109·e^{nΛ}/log z`
  (`109 = 4·19 + 33`, PM1's `C₃ = 19` scaled by the density plus the tail);
* `M_bound_gen`: `M·loglog z ≤ 5λ·log z` for the endpoint constant
  `M = max(e^Λ, e^{rΛ}/r)`, generic in `Λ ∈ (0, min(λ,1)]` — the twin `M_bound`
  with the `Λ`-specialisation removed;
* `Lam4 λ z = (λ/2)(1 − 300/loglog z)`: the (2.18) scale at `A = 4`.  The gap
  budget closes with room: `4nΛ + 545nλ/loglog z ≤ 2nλ − 55nλ/loglog z`.

`Salt.BrunLower.zThresh λ = exp(exp(100/λ))` is reused verbatim as the threshold.
-/

open Finset Nat

namespace Salt.HB

open Salt.BrunLower

/-! ## a1 — the block-Brun level bound

### Summation by parts over the ladder -/

/-- **Summation by parts.**  For any real sequence `a` with `a 0 = 0` and any `q`,
`q·Σ_{n<r} (a_{n+1} − a_n)q^n = a_r q^r + (1−q)·Σ_{n<r} a_n q^n`. -/
lemma abel_ladder_identity (a : ℕ → ℝ) (q : ℝ) (ha0 : a 0 = 0) (r : ℕ) :
    q * ∑ n ∈ Finset.range r, (a (n + 1) - a n) * q ^ n
      = a r * q ^ r + (1 - q) * ∑ n ∈ Finset.range r, a n * q ^ n := by
  induction r with
  | zero => simp [ha0]
  | succ r ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]
    ring

/-- **The exact finite geometric closed form** for the block-count majorant
`B_n = c + 2n` against the ladder weight `q^n` (cleared of denominators):
`(1−q)·[(c + 2r)q^r + (1−q)Σ_{1≤n<r} (c+2n)q^n] = (1−q)qc + 2q − 2q^{r+1}`  (`r ≥ 1`),
i.e. `T(r) = q(c + 2/(1−q)) − 2q^{r+1}/(1−q)`.  The `−2q^{r+1}/(1−q)` deficit is what
makes the `r → ∞` envelope a genuine upper bound at every finite ladder depth. -/
lemma ladder_geom_identity {q c : ℝ} :
    ∀ r : ℕ, 1 ≤ r →
      (1 - q) * ((c + 2 * r) * q ^ r + (1 - q) * ∑ n ∈ Finset.Ico 1 r, (c + 2 * n) * q ^ n)
        = (1 - q) * q * c + 2 * q - 2 * q ^ (r + 1) := by
  intro r
  induction r with
  | zero => omega
  | succ r ih =>
    intro _
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0
      norm_num
      ring
    · have hsum : ∑ n ∈ Finset.Ico 1 (r + 1), (c + 2 * (n : ℝ)) * q ^ n
          = (∑ n ∈ Finset.Ico 1 r, (c + 2 * (n : ℝ)) * q ^ n) + (c + 2 * (r : ℝ)) * q ^ r :=
        Finset.sum_Ico_succ_top hrpos _
      have hih := ih hrpos
      rw [hsum]
      push_cast
      linear_combination hih

/-- **The Abel ladder bound.**  If `a 0 = 0` and `a n ≤ c + 2n` for `n ≥ 1`, then for
`0 < q < 1` and any depth `r ≥ 1` the increment sum obeys the `r`-free envelope
`Σ_{n<r} (a_{n+1} − a_n)q^n ≤ c + 2/(1−q)`. -/
lemma ladder_abel_le {q c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {a : ℕ → ℝ} (ha0 : a 0 = 0)
    (hab : ∀ n : ℕ, 1 ≤ n → a n ≤ c + 2 * n) {r : ℕ} (hr : 1 ≤ r) :
    ∑ n ∈ Finset.range r, (a (n + 1) - a n) * q ^ n ≤ c + 2 / (1 - q) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hkey := abel_ladder_identity a q ha0 r
  -- drop the `n = 0` term (`a 0 = 0`)
  have hbot : ∑ n ∈ Finset.range r, a n * q ^ n = ∑ n ∈ Finset.Ico 1 r, a n * q ^ n := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hr]
    simp [ha0]
  -- majorise the counts
  have hmaj : ∑ n ∈ Finset.Ico 1 r, a n * q ^ n
      ≤ ∑ n ∈ Finset.Ico 1 r, (c + 2 * n) * q ^ n := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact mul_le_mul_of_nonneg_right (hab n hn.1) (by positivity)
  have hend : a r * q ^ r ≤ (c + 2 * r) * q ^ r :=
    mul_le_mul_of_nonneg_right (hab r hr) (by positivity)
  have hgeom := ladder_geom_identity (q := q) (c := c) r hr
  have htail : (0 : ℝ) ≤ 2 * q ^ (r + 1) := by positivity
  have hRHS : (1 - q) * (q * (c + 2 / (1 - q))) = (1 - q) * q * c + 2 * q := by
    field_simp
  have hmul : (1 - q) * (q * ∑ n ∈ Finset.range r, (a (n + 1) - a n) * q ^ n)
      ≤ (1 - q) * (q * (c + 2 / (1 - q))) := by
    rw [hRHS, hkey, hbot]
    have hm := mul_le_mul_of_nonneg_left hmaj h1q.le
    nlinarith [hgeom, hend, hm, htail, h1q]
  exact le_of_mul_le_mul_left (le_of_mul_le_mul_left hmul h1q) hq0

/-! ### The level bound proper -/

/-- The block-Brun **level exponent** `2b − ν − 1 + 2e^Λ/(e^Λ − 1)`: every `d` kept by
`chi Λ z ν b` obeys `d ≤ z^{levelExp}`. -/
noncomputable def levelExp (Lam : ℝ) (side b : ℕ) : ℝ :=
  2 * b - side - 1 + 2 * Real.exp Lam / (Real.exp Lam - 1)

/-- `2/(1 − e^{−Λ}) = 2e^Λ/(e^Λ − 1)` for `Λ > 0` — the two forms of the level constant. -/
lemma two_div_one_sub_exp_neg {Lam : ℝ} (hLam : 0 < Lam) :
    2 / (1 - Real.exp (-Lam)) = 2 * Real.exp Lam / (Real.exp Lam - 1) := by
  have hexp1 : (1 : ℝ) < Real.exp Lam := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]; exact Real.exp_lt_exp.mpr hLam
  have hpos : (0 : ℝ) < Real.exp Lam := Real.exp_pos _
  rw [Real.exp_neg]
  field_simp

/-- **a1 — THE LEVEL BOUND (log form).**  Every squarefree `d` with all prime factors
below `z` that is kept by the H-R block predicate `chi Λ z ν b` satisfies
`log d ≤ log z · (2b − ν − 1 + 2e^Λ/(e^Λ − 1))`.

Abel summation over the ladder `zLev Λ z` against the restricted counts
`bigOmegaGe Λ z n d ≤ 2b − ν + 2n − 1`; the ladder bottoms at `minLevel Λ z`
(`z_r ≤ 2`), which is where the finite sum closes. -/
theorem chi_log_le_level {Lam z : ℝ} {side b d : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hsq : Squarefree d)
    (hdz : ∀ p ∈ d.primeFactors, (p : ℝ) < z)
    (hchi : chi Lam z side b d) :
    Real.log d ≤ Real.log z * levelExp Lam side b := by
  classical
  have hzpos : (0 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz
  set q : ℝ := Real.exp (-Lam) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hqdef, show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith)
  set r : ℕ := minLevel Lam z with hrdef
  have hr1 : 1 ≤ r := (minLevel_mem hLam hz).1
  -- the ladder-window filtration of `d`'s prime factors
  set F : ℕ → Finset ℕ :=
    fun n => d.primeFactors.filter (fun p : ℕ => zLev Lam z n ≤ (p : ℝ)) with hFdef
  set g : ℕ → ℝ := fun n => ∑ p ∈ F n, Real.log p with hgdef
  set a : ℕ → ℝ := fun n => ((bigOmegaGe Lam z n d : ℕ) : ℝ) with hadef
  have hcard : ∀ n, ((F n).card : ℝ) = a n := by intro n; rfl
  have hmono : ∀ n, F n ⊆ F (n + 1) := by
    intro n p hp
    rw [hFdef, Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, le_trans ?_ hp.2⟩
    exact zLev_antitone hLam.le hz.le (Nat.le_succ n)
  -- `F 0 = ∅`: every prime factor of `d` is `< z = z₀`
  have hF0 : F 0 = ∅ := by
    rw [hFdef, Finset.filter_eq_empty_iff]
    intro p hp
    rw [zLev_zero Lam z hzpos]
    exact not_le.mpr (hdz p hp)
  have hg0 : g 0 = 0 := by rw [hgdef]; simp [hF0]
  have ha0 : a 0 = 0 := by rw [← hcard 0, hF0]; simp
  -- `F r = d.primeFactors`: `z_r ≤ 2 ≤ p`
  have hFr : F r = d.primeFactors := by
    apply Finset.filter_true_of_mem
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact le_trans (zLev_minLevel_le_two hLam hz) hp2
  have hgr : g r = Real.log d := by
    have hne : ∀ p ∈ d.primeFactors, ((p : ℕ) : ℝ) ≠ 0 := fun p hp =>
      Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hval : g r = ∑ p ∈ F r, Real.log (p : ℝ) := rfl
    rw [hval, hFr, ← Real.log_prod hne, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hsq]
  -- the block bounds
  have hab : ∀ n : ℕ, 1 ≤ n → a n ≤ (2 * b - side - 1 : ℝ) + 2 * n := by
    intro n hn
    have h := hchi n hn
    rw [blockBound] at h
    have : ((bigOmegaGe Lam z n d : ℕ) : ℝ) ≤ 2 * (b : ℝ) - (side : ℝ) + 2 * (n : ℝ) - 1 := by
      exact_mod_cast h
    rw [hadef]; linarith
  -- the per-window step
  have hstep : ∀ n, g (n + 1) - g n ≤ (a (n + 1) - a n) * (q ^ n * Real.log z) := by
    intro n
    have hsub := hmono n
    have hsd : ∑ p ∈ F (n + 1) \ F n, Real.log p = g (n + 1) - g n :=
      Finset.sum_sdiff_eq_sub hsub
    have hlogzn : Real.log (zLev Lam z n) = q ^ n * Real.log z := by
      rw [zLev, Real.log_exp, hqdef, show -((n : ℝ) * Lam) = (n : ℝ) * (-Lam) by ring,
        Real.exp_nat_mul]
    have hbnd : ∀ p ∈ F (n + 1) \ F n, Real.log p ≤ q ^ n * Real.log z := by
      intro p hp
      rw [Finset.mem_sdiff, hFdef] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Finset.mem_filter] at hp1 hp2
      have hpmem : p ∈ d.primeFactors := hp1.1
      have hlt : (p : ℝ) < zLev Lam z n := by
        by_contra hcon
        exact hp2 ⟨hpmem, not_lt.mp hcon⟩
      have hppos : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hpmem).pos
      rw [← hlogzn]
      exact Real.log_le_log hppos hlt.le
    have hcards : ((F (n + 1) \ F n).card : ℝ) = a (n + 1) - a n := by
      have h := Finset.card_sdiff_add_card_eq_card hsub
      have h' : ((F (n + 1) \ F n).card : ℝ) + ((F n).card : ℝ) = ((F (n + 1)).card : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
      rw [hcard, hcard] at h'
      linarith
    calc g (n + 1) - g n = ∑ p ∈ F (n + 1) \ F n, Real.log p := hsd.symm
      _ ≤ ((F (n + 1) \ F n).card : ℝ) * (q ^ n * Real.log z) := by
          have := Finset.sum_le_card_nsmul (F (n + 1) \ F n) (fun p => Real.log p)
            (q ^ n * Real.log z) hbnd
          simpa [nsmul_eq_mul] using this
      _ = (a (n + 1) - a n) * (q ^ n * Real.log z) := by rw [hcards]
  -- assemble
  have htele : Real.log d = ∑ n ∈ Finset.range r, (g (n + 1) - g n) := by
    rw [Finset.sum_range_sub g r, hg0, hgr, sub_zero]
  have hsum : Real.log d
      ≤ Real.log z * ∑ n ∈ Finset.range r, (a (n + 1) - a n) * q ^ n := by
    rw [htele, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have := hstep n
    calc g (n + 1) - g n ≤ (a (n + 1) - a n) * (q ^ n * Real.log z) := this
      _ = Real.log z * ((a (n + 1) - a n) * q ^ n) := by ring
  have habel := ladder_abel_le (q := q) (c := (2 * b - side - 1 : ℝ)) hq0 hq1 ha0 hab hr1
  have : Real.log d ≤ Real.log z * ((2 * b - side - 1 : ℝ) + 2 / (1 - q)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left habel hlogz.le)
  rwa [hqdef, two_div_one_sub_exp_neg hLam, ← levelExp] at this

/-- **a1 — THE LEVEL BOUND (support form).**  `d ≤ z^{2b−ν−1+2e^Λ/(e^Λ−1)}` for every
`d` kept by `chi Λ z ν b` (squarefree, all prime factors `< z`).  This is the block-Brun
analogue of the Iwaniec `S`-set support bound `δ ≤ Max(D, z²)`; the wave-2 first-failure
decomposition consumes it in this shape. -/
theorem chi_le_rpow_level {Lam z : ℝ} {side b d : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hd : d ≠ 0) (hsq : Squarefree d)
    (hdz : ∀ p ∈ d.primeFactors, (p : ℝ) < z)
    (hchi : chi Lam z side b d) :
    (d : ℝ) ≤ z ^ levelExp Lam side b := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  have hzpos : (0 : ℝ) < z := by linarith
  rw [Real.le_rpow_iff_log_le hdpos hzpos]
  have := chi_log_le_level hLam hz hsq hdz hchi
  linarith [this, mul_comm (Real.log z) (levelExp Lam side b)]

/-! ## a3 — the dimension-4 Mertens package

### HB's Lemma 5 density `G(p) = 2(2p−1)/(p+1)` -/

/-- **HB's Lemma 5 density** `G(p) = 2(2p−1)/(p+1)` — the local density of the sifted
set at the sparse sifting prime `p` (the `χ(p) = 1` primes, `2 < p < z`). -/
noncomputable def Gdens (p : ℕ) : ℝ := 2 * (2 * p - 1) / (p + 1)

/-- **`hωA` at `A = 4`** — `G(p) ≤ 4` uniformly in `p`.  This is HB's "as `G(p) ≤ 4` we
need a sieve of dimension 4": the whole reason the instantiation is at dimension four. -/
lemma Gdens_le_four (p : ℕ) : Gdens p ≤ 4 := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [Gdens, div_le_iff₀ (by linarith)]
  linarith

/-- `G(p) ≥ 0` for `p ≥ 1`. -/
lemma Gdens_nonneg {p : ℕ} (hp : 1 ≤ p) : 0 ≤ Gdens p := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [Gdens]
  apply div_nonneg <;> linarith

/-- The multiplicative extension of `G` to squarefree moduli — the `ω` that the
remainder-side hypotheses of `brun_lower`/`brun_upper` consume. -/
noncomputable def omegaG (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, Gdens p

/-- `ω(p) = G(p)` at a prime. -/
lemma omegaG_prime {p : ℕ} (hp : p.Prime) : omegaG p = Gdens p := by
  rw [omegaG, hp.primeFactors, Finset.prod_singleton]

/-- **`hωprod`** — `ω` is multiplicative on squarefree moduli (by construction). -/
lemma omegaG_prod (d : ℕ) : omegaG d = ∏ p ∈ d.primeFactors, omegaG p := by
  rw [omegaG]
  exact Finset.prod_congr rfl fun p hp =>
    (omegaG_prime (Nat.prime_of_mem_primeFactors hp)).symm

/-- **`hωA`** at `A = 4` in the form `brun_lower` consumes. -/
lemma omegaG_le_four {p : ℕ} (hp : p.Prime) : omegaG p ≤ 4 := by
  rw [omegaG_prime hp]; exact Gdens_le_four p

/-- **`hωnn`** at the `G`-density. -/
lemma omegaG_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ omegaG p := by
  rw [omegaG_prime hp]; exact Gdens_nonneg hp.one_lt.le

/-! ### Step 1 — the pointwise bound `−log(1−ν(p)) ≤ 4/p + 33/p²` -/

/-- **Pointwise bound at the `G`-density.**  For an odd sifting prime `p` with
`ν(p) ≤ G(p)/p = 2(2p−1)/(p(p+1))`: `−log(1 − ν(p)) ≤ 4/p + 33/p²`.

The constant `33` is exact at `p = 3`: the difference is
`(23p² − 91p + 66)/(p²(p−1)(p−2)) = (p−3)(23(p−3)+47)/(p²(p−1)(p−2))`. -/
lemma neg_log_one_sub_nu_le_dim4 (s : BoundingSieve) {p : ℕ}
    (hmem : p ∈ s.prodPrimes.primeFactors) (hp2 : p ≠ 2)
    (hnuG : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ Gdens q / q) :
    - Real.log (1 - s.nu p) ≤ 4 / (p : ℝ) + 33 / (p : ℝ) ^ 2 := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hnu : s.nu p ≤ Gdens p / p := hnuG p hmem
  set x : ℝ := Gdens p / p with hxdef
  have h1x : 1 - x = ((p : ℝ) - 1) * ((p : ℝ) - 2) / ((p : ℝ) * ((p : ℝ) + 1)) := by
    rw [hxdef, Gdens]; field_simp; ring
  have hpne : (p : ℝ) ≠ 0 := by linarith
  have hp1ne : ((p : ℝ) + 1) ≠ 0 := by linarith
  have hpm1ne : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hpm2ne : ((p : ℝ) - 2) ≠ 0 := by linarith
  have hprodne : ((p : ℝ) - 1) * ((p : ℝ) - 2) ≠ 0 := mul_ne_zero hpm1ne hpm2ne
  have h1xpos : (0 : ℝ) < 1 - x := by
    rw [h1x]; apply _root_.div_pos <;> nlinarith [hpR]
  have hmono : - Real.log (1 - s.nu p) ≤ - Real.log (1 - x) := by
    have := Real.log_le_log h1xpos (by linarith : 1 - x ≤ 1 - s.nu p)
    linarith
  have hquad : - Real.log (1 - x) ≤ (4 * (p : ℝ) - 2) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 - x)⁻¹ by positivity)
    rw [Real.log_inv] at h
    have he : (1 - x)⁻¹ - 1 = (4 * (p : ℝ) - 2) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
      rw [h1x, inv_div, div_sub_one hprodne,
        show (p : ℝ) * ((p : ℝ) + 1) - ((p : ℝ) - 1) * ((p : ℝ) - 2) = 4 * (p : ℝ) - 2 by ring]
    linarith [he ▸ h]
  have hden : (0 : ℝ) < (p : ℝ) ^ 2 * (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
    apply mul_pos (by positivity); nlinarith [hpR]
  have hkey : 4 / (p : ℝ) + 33 / (p : ℝ) ^ 2 - (4 * (p : ℝ) - 2) / (((p : ℝ) - 1) * ((p : ℝ) - 2))
      = (23 * (p : ℝ) ^ 2 - 91 * (p : ℝ) + 66)
        / ((p : ℝ) ^ 2 * (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
    field_simp
    ring
  have hnum : (0 : ℝ) ≤ 23 * (p : ℝ) ^ 2 - 91 * (p : ℝ) + 66 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 3)
      (by linarith : (0 : ℝ) ≤ 23 * ((p : ℝ) - 3) + 47)]
  have hdivnn : (0 : ℝ) ≤ (23 * (p : ℝ) ^ 2 - 91 * (p : ℝ) + 66)
      / ((p : ℝ) ^ 2 * (((p : ℝ) - 1) * ((p : ℝ) - 2))) := div_nonneg hnum hden.le
  linarith [hmono, hquad, hkey, hdivnn]

/-! ### Step 2 — the dimension-4 ladder bound -/

/-- **The dimension-4 uniform ladder bound.**  `log(W(z_n)/W(z)) ≤ 4nΛ + 109·e^{nΛ}/log z`
for all `n ≥ 1`, at the `G`-density on odd sifting primes.  `109 = 4·19 + 33`: PM1's
`C₃ = 19` scaled by the density `4`, plus the quadratic tail.  Generic in `Λ ≥ 0`. -/
lemma log_Wratio_le_ladder_dim4 (s : BoundingSieve) {Lam z : ℝ} {n : ℕ}
    (hLam : 0 ≤ Lam) (hz2 : 2 ≤ z)
    (hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2)
    (hnuG : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ Gdens q / q) :
    Real.log (Wratio s Lam z n)
      ≤ 4 * (n : ℝ) * Lam + 109 * Real.exp ((n : ℝ) * Lam) / Real.log z := by
  set W := max (zLev Lam z n) 2 with hW
  have hz1 : (1 : ℝ) < z := by linarith
  have hzpos : (0 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hznpos : 0 < zLev Lam z n := Real.exp_pos _
  have hW2 : (2 : ℝ) ≤ W := le_max_right _ _
  have hWzn : zLev Lam z n ≤ W := le_max_left _ _
  have hWpos : (0 : ℝ) < W := by linarith
  have hlogW : 0 < Real.log W := Real.log_pos (by linarith)
  have hznz : zLev Lam z n ≤ z := by
    have := (zLev_antitone hLam (by linarith : (1 : ℝ) ≤ z)) (Nat.zero_le n)
    rwa [zLev_zero Lam z hzpos] at this
  have hWz : W ≤ z := max_le hznz hz2
  have hlogzn : Real.log (zLev Lam z n) = Real.exp (-((n : ℝ) * Lam)) * Real.log z := by
    rw [zLev, Real.log_exp]
  have hlogWge : Real.log (zLev Lam z n) ≤ Real.log W := Real.log_le_log hznpos hWzn
  have hinvW : 1 / Real.log W ≤ Real.exp ((n : ℝ) * Lam) / Real.log z := by
    have hb : Real.exp (-((n : ℝ) * Lam)) * Real.log z ≤ Real.log W := by
      rw [← hlogzn]; exact hlogWge
    have hbpos : 0 < Real.exp (-((n : ℝ) * Lam)) * Real.log z := by positivity
    have h1 : 1 / Real.log W ≤ 1 / (Real.exp (-((n : ℝ) * Lam)) * Real.log z) :=
      one_div_le_one_div_of_le hbpos hb
    have h2 : 1 / (Real.exp (-((n : ℝ) * Lam)) * Real.log z)
        = Real.exp ((n : ℝ) * Lam) / Real.log z := by
      rw [Real.exp_neg]; field_simp
    rwa [h2] at h1
  have hlog_ratio : Real.log (Real.log z / Real.log W) ≤ (n : ℝ) * Lam := by
    have hratio_pos : 0 < Real.log z / Real.log W := by positivity
    have hle : Real.log z / Real.log W ≤ Real.exp ((n : ℝ) * Lam) := by
      rw [div_le_iff₀ hlogW]
      have hge : Real.exp ((n : ℝ) * Lam) * Real.log W ≥ Real.exp ((n : ℝ) * Lam)
          * (Real.exp (-((n : ℝ) * Lam)) * Real.log z) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [← hlogzn]; exact hlogWge
      have hcancel : Real.exp ((n : ℝ) * Lam) * (Real.exp (-((n : ℝ) * Lam)) * Real.log z)
          = Real.log z := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [hcancel] at hge
      linarith
    calc Real.log (Real.log z / Real.log W)
        ≤ Real.log (Real.exp ((n : ℝ) * Lam)) := Real.log_le_log hratio_pos hle
      _ = (n : ℝ) * Lam := Real.log_exp _
  have hwindow_sub : ∀ q ∈ windowPrimes s Lam z n, Nat.Prime q ∧ W ≤ (q : ℝ) ∧ (q : ℝ) < z := by
    intro q hq
    rw [windowPrimes, Finset.mem_filter] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    refine ⟨hqp, ?_, hp q hq.1⟩
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
    exact max_le hq.2 hq2
  -- MAIN TERM: 4·Σ 1/p ≤ 4nΛ + 76/log W
  have hmain : ∑ p ∈ windowPrimes s Lam z n, (4 : ℝ) / p
      ≤ 4 * (n : ℝ) * Lam + 76 / Real.log W := by
    have hpm1 := sum_inv_le_of_prime_window (w := W) (z := z) hW2 hWz hwindow_sub
    have hrw : ∑ p ∈ windowPrimes s Lam z n, (4 : ℝ) / p
        = 4 * ∑ p ∈ windowPrimes s Lam z n, (1 : ℝ) / p := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    rw [hrw]
    calc 4 * ∑ p ∈ windowPrimes s Lam z n, (1 : ℝ) / p
        ≤ 4 * (Real.log (Real.log z / Real.log W) + 19 / Real.log W) := by
          apply mul_le_mul_of_nonneg_left hpm1 (by norm_num)
      _ ≤ 4 * ((n : ℝ) * Lam + 19 / Real.log W) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [hlog_ratio]
      _ = 4 * (n : ℝ) * Lam + 76 / Real.log W := by ring
  -- TAIL: 33·Σ 1/p² ≤ 33/(W−1) ≤ 33/log W
  have htail : ∑ p ∈ windowPrimes s Lam z n, (33 : ℝ) / (p : ℝ) ^ 2 ≤ 33 / Real.log W := by
    set M := ⌈W⌉₊ with hMdef
    have hMge : 2 ≤ M := by
      have : ⌈(2 : ℝ)⌉₊ ≤ ⌈W⌉₊ := Nat.ceil_mono hW2
      simpa using this
    have hsub : windowPrimes s Lam z n ⊆ Finset.Icc M ⌊z⌋₊ := by
      intro q hq
      obtain ⟨_, hWq, hqz⟩ := hwindow_sub q hq
      rw [Finset.mem_Icc]
      exact ⟨Nat.ceil_le.mpr hWq, Nat.le_floor hqz.le⟩
    have hstep : ∑ p ∈ windowPrimes s Lam z n, (33 : ℝ) / (p : ℝ) ^ 2
        ≤ ∑ p ∈ Finset.Icc M ⌊z⌋₊, (33 : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _; positivity
    have hfactor : ∑ p ∈ Finset.Icc M ⌊z⌋₊, (33 : ℝ) / (p : ℝ) ^ 2
        = 33 * ∑ p ∈ Finset.Icc M ⌊z⌋₊, (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    have htel := sum_one_div_sq_le (M := M) (K := ⌊z⌋₊) hMge
    have hMreal : W ≤ (M : ℝ) := Nat.le_ceil W
    have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMge
      linarith
    have hWm1 : (0 : ℝ) < W - 1 := by linarith
    have hinv : 1 / ((M : ℝ) - 1) ≤ 1 / (W - 1) := by
      apply one_div_le_one_div_of_le hWm1; linarith
    have hlogWsub : Real.log W ≤ W - 1 := Real.log_le_sub_one_of_pos hWpos
    have hinv2 : 1 / (W - 1) ≤ 1 / Real.log W := one_div_le_one_div_of_le hlogW hlogWsub
    calc ∑ p ∈ windowPrimes s Lam z n, (33 : ℝ) / (p : ℝ) ^ 2
        ≤ ∑ p ∈ Finset.Icc M ⌊z⌋₊, (33 : ℝ) / (p : ℝ) ^ 2 := hstep
      _ = 33 * ∑ p ∈ Finset.Icc M ⌊z⌋₊, (1 : ℝ) / (p : ℝ) ^ 2 := hfactor
      _ ≤ 33 * (1 / ((M : ℝ) - 1)) := by apply mul_le_mul_of_nonneg_left htel (by norm_num)
      _ ≤ 33 * (1 / Real.log W) := by
          apply mul_le_mul_of_nonneg_left (le_trans hinv hinv2) (by norm_num)
      _ = 33 / Real.log W := by ring
  have hsum_le : Real.log (Wratio s Lam z n)
      ≤ ∑ p ∈ windowPrimes s Lam z n, ((4 : ℝ) / p + 33 / (p : ℝ) ^ 2) := by
    rw [log_Wratio_eq, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro p hp'
    rw [windowPrimes, Finset.mem_filter] at hp'
    exact neg_log_one_sub_nu_le_dim4 s hp'.1 (hodd p hp'.1) hnuG
  have hsplit_sum : ∑ p ∈ windowPrimes s Lam z n, ((4 : ℝ) / p + 33 / (p : ℝ) ^ 2)
      = (∑ p ∈ windowPrimes s Lam z n, (4 : ℝ) / p)
        + ∑ p ∈ windowPrimes s Lam z n, (33 : ℝ) / (p : ℝ) ^ 2 := Finset.sum_add_distrib
  have hcombine : Real.log (Wratio s Lam z n)
      ≤ 4 * (n : ℝ) * Lam + 109 * (1 / Real.log W) := by
    calc Real.log (Wratio s Lam z n)
        ≤ (∑ p ∈ windowPrimes s Lam z n, (4 : ℝ) / p)
            + ∑ p ∈ windowPrimes s Lam z n, (33 : ℝ) / (p : ℝ) ^ 2 := hsum_le.trans_eq hsplit_sum
      _ ≤ (4 * (n : ℝ) * Lam + 76 / Real.log W) + 33 / Real.log W := add_le_add hmain htail
      _ = 4 * (n : ℝ) * Lam + 109 * (1 / Real.log W) := by ring
  have hfinal : 109 * (1 / Real.log W) ≤ 109 * Real.exp ((n : ℝ) * Lam) / Real.log z := by
    have h := mul_le_mul_of_nonneg_left hinvW (by norm_num : (0 : ℝ) ≤ 109)
    calc 109 * (1 / Real.log W) ≤ 109 * (Real.exp ((n : ℝ) * Lam) / Real.log z) := h
      _ = 109 * Real.exp ((n : ℝ) * Lam) / Real.log z := by ring
  linarith [hcombine, hfinal]

/-! ### Step 3 — the endpoint constant, generic in the ladder scale -/

/-- **The generic `M`-bound.**  For any ladder scale `Λ ∈ (0, λ]` (with `0 < λ ≤ 1/4`,
`z ≥ z₀`), the endpoint constant `M = max(e^Λ, e^{rΛ}/r)` of `exp_mul_le_max_mul` obeys
`M·loglog z ≤ 5λ·log z`.  This is `Salt.BrunLower.M_bound` with the `Λ = LamTwin`
specialisation removed — the dimension-4 scale `Lam4` needs the same estimate. -/
lemma M_bound_gen {lam Lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : zThresh lam ≤ z) (hLampos : 0 < Lam) (hLamle : Lam ≤ lam) :
    (max (Real.exp Lam) (Real.exp ((minLevel Lam z : ℝ) * Lam) / (minLevel Lam z : ℝ)))
        * Real.log (Real.log z)
      ≤ 5 * lam * Real.log z := by
  obtain ⟨_, h400, hlz_pos, hllz_pos, _, hkey, hz2⟩ := zThresh_facts hlam hlam' hz
  have hLam1 : Lam ≤ 1 := by linarith
  have hz1 : (1 : ℝ) < z := by linarith
  set r := minLevel Lam z with hr
  have hr1 : 1 ≤ r := (minLevel_mem hLampos hz1).1
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hexpLam3 : Real.exp Lam ≤ 3 := by
    calc Real.exp Lam ≤ Real.exp 1 := Real.exp_le_exp.mpr hLam1
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ge : (0.6931 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hll2 : Real.log (Real.log 2) < 0 :=
    Real.log_neg hlog2pos (by have := Real.log_two_lt_d9; linarith)
  -- BRANCH A
  have hbranchA : Real.exp Lam * Real.log (Real.log z) ≤ 5 * lam * Real.log z := by
    have h1 : Real.exp Lam * Real.log (Real.log z) ≤ 3 * Real.log (Real.log z) := by
      nlinarith [hexpLam3, hllz_pos]
    nlinarith [hkey, hllz_pos]
  -- BRANCH B
  have hbranchB : (Real.exp ((r : ℝ) * Lam) / (r : ℝ)) * Real.log (Real.log z)
      ≤ 5 * lam * Real.log z := by
    have hexpr_ub : Real.exp ((r : ℝ) * Lam) ≤ Real.exp Lam * (Real.log z / Real.log 2) := by
      rcases Nat.lt_or_ge 1 r with hr2 | hr2
      · have hrm1 : 1 ≤ r - 1 := by omega
        have hlt : zLev Lam z (r - 1) > 2 := by
          by_contra h
          have := minLevel_le (Lam := Lam) (z := z) (n := r - 1) hrm1 (not_lt.mp h)
          omega
        have hkey2 : Real.exp (((r - 1 : ℕ) : ℝ) * Lam) < Real.log z / Real.log 2 := by
          by_contra h
          have := (zLev_le_two_iff Lam z (r - 1) hz1).2 (not_lt.mp h)
          linarith
        have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
          push_cast [Nat.cast_sub hr1]; ring
        rw [hcast] at hkey2
        have hsplit : Real.exp ((r : ℝ) * Lam) = Real.exp Lam * Real.exp (((r : ℝ) - 1) * Lam) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left hkey2.le (Real.exp_pos _).le
      · have hre : r = 1 := by omega
        rw [hre]
        simp only [Nat.cast_one, one_mul]
        have hlogzlog2 : (1 : ℝ) ≤ Real.log z / Real.log 2 := by
          rw [le_div_iff₀ hlog2pos]
          have : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) (by linarith)
          linarith
        nlinarith [Real.exp_pos Lam, hlogzlog2]
    have hr_lb : Real.log (Real.log z) - Real.log (Real.log 2) ≤ (r : ℝ) * Lam := by
      have h := exp_minLevel_ge (Lam := Lam) (z := z) hLampos hz1
      have hlogdiv : Real.log (Real.log z / Real.log 2)
          = Real.log (Real.log z) - Real.log (Real.log 2) :=
        Real.log_div hlz_pos.ne' hlog2pos.ne'
      have hdivpos : 0 < Real.log z / Real.log 2 := by positivity
      have := Real.log_le_log hdivpos h
      rwa [hlogdiv, Real.log_exp] at this
    have hdiffpos : 0 < Real.log (Real.log z) - Real.log (Real.log 2) := by linarith
    have hinv_r : (1 : ℝ) / (r : ℝ) ≤ Lam / (Real.log (Real.log z) - Real.log (Real.log 2)) := by
      rw [div_le_div_iff₀ hrpos hdiffpos, one_mul]
      linarith [hr_lb]
    have hexppos : 0 < Real.exp ((r : ℝ) * Lam) := Real.exp_pos _
    have hchain : Real.exp ((r : ℝ) * Lam) / (r : ℝ)
        ≤ (Real.exp Lam * (Real.log z / Real.log 2))
          * (Lam / (Real.log (Real.log z) - Real.log (Real.log 2))) := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul hexpr_ub hinv_r (by positivity) (by positivity)
    have hratio1 : Real.log (Real.log z) / (Real.log (Real.log z) - Real.log (Real.log 2)) ≤ 1 := by
      rw [div_le_one hdiffpos]; linarith
    have hstep : ((Real.exp Lam * (Real.log z / Real.log 2))
          * (Lam / (Real.log (Real.log z) - Real.log (Real.log 2)))) * Real.log (Real.log z)
        ≤ 5 * lam * Real.log z := by
      have hexpr : ((Real.exp Lam * (Real.log z / Real.log 2))
            * (Lam / (Real.log (Real.log z) - Real.log (Real.log 2)))) * Real.log (Real.log z)
          = (Real.exp Lam * Lam * (Real.log z / Real.log 2))
            * (Real.log (Real.log z) / (Real.log (Real.log z) - Real.log (Real.log 2))) := by
        ring
      rw [hexpr]
      have hfac_nonneg : 0 ≤ Real.exp Lam * Lam * (Real.log z / Real.log 2) := by positivity
      have h1 : (Real.exp Lam * Lam * (Real.log z / Real.log 2))
            * (Real.log (Real.log z) / (Real.log (Real.log z) - Real.log (Real.log 2)))
          ≤ (Real.exp Lam * Lam * (Real.log z / Real.log 2)) * 1 :=
        mul_le_mul_of_nonneg_left hratio1 hfac_nonneg
      have h2 : (Real.exp Lam * Lam * (Real.log z / Real.log 2)) * 1 ≤ 5 * lam * Real.log z := by
        rw [mul_one]
        have hbound : Real.exp Lam * Lam ≤ 3 * lam := by
          nlinarith [hexpLam3, hLamle, hLampos.le, hlam.le]
        have hlogz_div : Real.log z / Real.log 2 ≤ Real.log z / 0.6931 :=
          div_le_div_of_nonneg_left hlz_pos.le (by norm_num) hlog2ge
        calc (Real.exp Lam * Lam) * (Real.log z / Real.log 2)
            ≤ (3 * lam) * (Real.log z / 0.6931) := by
              apply mul_le_mul hbound hlogz_div (by positivity) (by positivity)
          _ ≤ 5 * lam * Real.log z := by
              rw [div_eq_mul_inv]
              nlinarith [hlz_pos.le, hlam.le, mul_nonneg hlam.le hlz_pos.le]
      linarith [h1, h2]
    linarith [mul_le_mul_of_nonneg_right hchain hllz_pos.le, hstep]
  rcases max_cases (Real.exp Lam) (Real.exp ((r : ℝ) * Lam) / (r : ℝ)) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact hbranchA
  · rw [he]; exact hbranchB

/-! ### Step 4 — the dimension-4 ladder scale and the `hMert` discharge -/

/-- **The (2.18) ladder scale at `A = 4`**: `Λ(z) = (λ/2)(1 − 300/loglog z)`, strictly
below the nominal `2λ/A = λ/2` and rising to it.  The gap constant is `300` (against the
twin instance's `120`) because the dimension-4 error budget carries `109` instead of `50`. -/
noncomputable def Lam4 (lam z : ℝ) : ℝ := (lam / 2) * (1 - 300 / Real.log (Real.log z))

/-- `Lam4 > 0` for `z ≥ z₀` (`loglog z ≥ 400 > 300`). -/
lemma Lam4_pos {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : zThresh lam ≤ z) : 0 < Lam4 lam z := by
  obtain ⟨_, h400, _, hllz_pos, _, _, _⟩ := zThresh_facts hlam hlam' hz
  rw [Lam4]
  apply mul_pos (by linarith)
  have hlt : 300 / Real.log (Real.log z) < 1 := by
    rw [div_lt_one hllz_pos]; linarith
  linarith

/-- `Lam4 ≤ λ/2 ≤ λ`. -/
lemma Lam4_le_lam {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : zThresh lam ≤ z) : Lam4 lam z ≤ lam := by
  obtain ⟨_, _, _, hllz_pos, _, _, _⟩ := zThresh_facts hlam hlam' hz
  rw [Lam4]
  have h : 0 ≤ 300 / Real.log (Real.log z) := by positivity
  nlinarith [hlam.le]

/-- The exact gap: `2λ − 4·Λ₄ = 600λ/loglog z`. -/
lemma two_lam_sub_four_Lam4 {lam z : ℝ} :
    2 * lam - 4 * Lam4 lam z = 600 * lam / Real.log (Real.log z) := by
  rw [Lam4]; ring

/-- **`hkappa` at `A = 4`**: `κ = A·Λ = 4·(2λ/4) = 2λ`, so `κ ≤ 2λ` holds with equality —
the dimension cancels exactly, which is why the `A`-free main term of H-R's Théorème 2
is untouched by the move from dimension 2 to dimension 4. -/
lemma kappa_dim4 (lam : ℝ) : 2 * lam ≤ 2 * lam := le_refl _

/-- **a3 — THE DIMENSION-4 `hMert` DISCHARGE.**  For `z ≥ z₀ = exp(exp(100/λ))`,
`0 < λ ≤ 1/4`, a `BoundingSieve` whose sifting primes are all odd, all `< z`, and carry
the HB density `ν(p) ≤ G(p)/p = 2(2p−1)/(p(p+1))` (an *arbitrary* — in HB's application
sparse — set of such primes), the dimension-4 ladder scale `Λ = Lam4 λ z` gives
`log(W(z_n)/W(z)) ≤ n·(2λ)` for every `n ∈ [1, r]`.

This is `hMert` at `κ = 2λ` for `brun_lower`/`brun_upper` at `A = 4`; `hkappa` is then
`le_refl`.  The budget: `4nΛ = 2nλ − 600nλ/loglog z` against the error
`109·e^{nΛ}/log z ≤ 545nλ/loglog z`, closing with `55nλ/loglog z` to spare. -/
theorem hMert_dim4 (s : BoundingSieve) {lam z : ℝ}
    (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) (hz : zThresh lam ≤ z)
    (hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2)
    (hnuG : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ Gdens q / q) :
    ∀ n ∈ Finset.Icc 1 (minLevel (Lam4 lam z) z),
      Real.log (Wratio s (Lam4 lam z) z n) ≤ (n : ℝ) * (2 * lam) := by
  intro n hn
  obtain ⟨_, h400, hlz_pos, hllz_pos, _, hkey, hz2⟩ := zThresh_facts hlam hlam' hz
  set Lam := Lam4 lam z with hLdef
  have hLampos : 0 < Lam := Lam4_pos hlam hlam' hz
  have hLamle : Lam ≤ lam := Lam4_le_lam hlam hlam' hz
  have hz1 : (1 : ℝ) < z := by linarith
  set r := minLevel Lam z with hr
  set M := max (Real.exp Lam) (Real.exp ((r : ℝ) * Lam) / (r : ℝ)) with hM
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hladder := log_Wratio_le_ladder_dim4 s (Lam := Lam) (z := z) (n := n)
    hLampos.le hz2 hp hodd hnuG
  have hendpoint := exp_mul_le_max_mul (Lam := Lam) (z := z) hLampos hz1 hn
  have hMbound := M_bound_gen (Lam := Lam) hlam hlam' hz hLampos hLamle
  -- `109·M/log z ≤ 600·λ/loglog z`
  have hMdivz : 109 * M / Real.log z ≤ 600 * lam / Real.log (Real.log z) := by
    rw [div_le_div_iff₀ hlz_pos hllz_pos]
    nlinarith [hMbound, hlz_pos.le]
  have hexp_bound : 109 * Real.exp ((n : ℝ) * Lam) / Real.log z
      ≤ 109 * (M * (n : ℝ)) / Real.log z := by
    have hnum : 109 * Real.exp ((n : ℝ) * Lam) ≤ 109 * (M * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hendpoint (by norm_num)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hlz_pos.le)
  have hMn : 109 * (M * (n : ℝ)) / Real.log z
      ≤ (n : ℝ) * (600 * lam / Real.log (Real.log z)) := by
    rw [show 109 * (M * (n : ℝ)) / Real.log z = (109 * M / Real.log z) * (n : ℝ) by ring]
    calc (109 * M / Real.log z) * (n : ℝ)
        ≤ (600 * lam / Real.log (Real.log z)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hMdivz hnpos.le
      _ = (n : ℝ) * (600 * lam / Real.log (Real.log z)) := by ring
  have hgap : 4 * (n : ℝ) * Lam
      = (n : ℝ) * (2 * lam) - (n : ℝ) * (600 * lam / Real.log (Real.log z)) := by
    have := two_lam_sub_four_Lam4 (lam := lam) (z := z)
    rw [hLdef]
    nlinarith [this]
  calc Real.log (Wratio s Lam z n)
      ≤ 4 * (n : ℝ) * Lam + 109 * Real.exp ((n : ℝ) * Lam) / Real.log z := hladder
    _ ≤ 4 * (n : ℝ) * Lam + 109 * (M * (n : ℝ)) / Real.log z := by linarith [hexp_bound]
    _ ≤ 4 * (n : ℝ) * Lam + (n : ℝ) * (600 * lam / Real.log (Real.log z)) := by linarith [hMn]
    _ = (n : ℝ) * (2 * lam) := by rw [hgap]; ring

/-! ### The packaged dimension-4 endpoints (what wave 2 consumes) -/

/-- H-R's `(2.15)` side condition `λ e^{1+λ} < 1` holds throughout `0 < λ ≤ 1/4`
(`e^{5/4} ≤ e·(4/3) < 4`). -/
lemma lam_exp_lt_one {lam : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) :
    lam * Real.exp (1 + lam) < 1 := by
  have hpos : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
  have hq : Real.exp (1 / 4) ≤ 4 / 3 := by
    have hh := Real.add_one_le_exp (-(1 / 4) : ℝ)
    rw [Real.exp_neg] at hh
    have hinv : Real.exp (1 / 4) * (Real.exp (1 / 4))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    nlinarith [hh, hpos, hinv]
  have he : Real.exp (5 / 4) = Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add]; norm_num
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : Real.exp (1 + lam) < 4 := by
    have hmono : Real.exp (1 + lam) ≤ Real.exp (5 / 4) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [hmono, he, h1, hq, hpos, Real.exp_pos (1 : ℝ)]
  nlinarith [h4, hlam, hlam']

/-- **`brun_lower` AT DIMENSION 4** — H-R Théorème 2 (lower bound) instantiated at HB's
sifting data: sieve dimension `A = 4`, ladder scale `Λ = Lam4 λ z = (λ/2)(1 − 300/loglog z)`,
`κ = 2λ`, density `ω = ω_G` (the multiplicative extension of `G(p) = 2(2p−1)/(p+1)`).

The three dimension-carrying hypotheses are discharged internally (`hMert_dim4`,
`kappa_dim4`, `omegaG_le_four`); what remains for the caller is exactly the *instance*
data: the sifting primes are odd and `< z`, their densities are `≤ G(p)/p`, `z ≥ z₀`,
and the remainder bound `(R)`. -/
theorem brun_lower_dim4 (s : BoundingSieve) {lam z : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) (hz : zThresh lam ≤ z)
    (htotalMass : 0 ≤ s.totalMass)
    (hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2)
    (hnuG : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ Gdens q / q)
    (hR : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ omegaG d) :
    s.totalMass * W s * (1 - 2 * lam ^ (2 * b) * Real.exp (2 * lam)
          / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
        - (1 + 4 * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ (2 * b - 1)
          * ∏ n ∈ Finset.Ico 1 (minLevel (Lam4 lam z) z),
              (1 + 4 * (Nat.primeCounting ⌊zLev (Lam4 lam z) z n⌋₊ : ℝ)) ^ 2
      ≤ s.siftedSum := by
  obtain ⟨_, _, _, _, _, _, hz2⟩ := zThresh_facts hlam hlam' hz
  exact brun_lower s (A := 4) (kappa := 2 * lam) omegaG hb hlam
    (lam_exp_lt_one hlam hlam') (Lam4_pos hlam hlam' hz) (by linarith) htotalMass hp
    (kappa_dim4 lam) (hMert_dim4 s hlam hlam' hz hp hodd hnuG) (by norm_num)
    (fun p hp' => omegaG_nonneg hp') (fun p hp' => omegaG_le_four hp')
    (fun d _ => omegaG_prod d) hR

/-- **`brun_upper` AT DIMENSION 4** — the mirror of `brun_lower_dim4`. -/
theorem brun_upper_dim4 (s : BoundingSieve) {lam z : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4) (hz : zThresh lam ≤ z)
    (htotalMass : 0 ≤ s.totalMass)
    (hp : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hodd : ∀ q ∈ s.prodPrimes.primeFactors, q ≠ 2)
    (hnuG : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ Gdens q / q)
    (hR : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ omegaG d) :
    s.siftedSum
      ≤ s.totalMass * W s * (1 + 2 * lam ^ (2 * b + 1) * Real.exp (2 * lam)
            / (1 - lam ^ 2 * Real.exp (2 + 2 * lam)))
        + (1 + 4 * (Nat.primeCounting ⌊z⌋₊ : ℝ)) ^ (2 * b)
          * ∏ n ∈ Finset.Ico 1 (minLevel (Lam4 lam z) z),
              (1 + 4 * (Nat.primeCounting ⌊zLev (Lam4 lam z) z n⌋₊ : ℝ)) ^ 2 := by
  obtain ⟨_, _, _, _, _, _, hz2⟩ := zThresh_facts hlam hlam' hz
  exact brun_upper s (A := 4) (kappa := 2 * lam) omegaG hb hlam
    (lam_exp_lt_one hlam hlam') (Lam4_pos hlam hlam' hz) (by linarith) htotalMass hp
    (kappa_dim4 lam) (hMert_dim4 s hlam hlam' hz hp hodd hnuG) (by norm_num)
    (fun p hp' => omegaG_nonneg hp') (fun p hp' => omegaG_le_four hp')
    (fun d _ => omegaG_prod d) hR

end Salt.HB
