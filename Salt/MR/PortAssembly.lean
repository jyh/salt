/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TwistedEdge
import Salt.MR.USetChi
import Salt.MR.M4Chars
import Salt.SW.SiegelClose

/-!
# WAVE P-7 — THE ASSEMBLY: the `(χ,t)`-pair dual and the Siegel fold

The KMT port's closing wave.  Two deliverables:

* **A1 — THE PAIR DUAL** (§§1–6): stone C's residue, i.e. the `(χ,t)`-pair twin of
  `dual_core`.  `USetChi.HalaszPrimesChi`'s conclusion — the socket with the diagonal term
  `P`, **not** `φ(q)·P` — from the landed twisted edge price
  (`TwistedWindowPriceGated`, `TwistedEdge.lean`) at the cross-character rows, the landed
  untwisted price (`per_pair_contour`) at the diagonal fibres, the fibre-split pole row
  (`pole_row_sum` once per fibre) and the `p ∣ q` Euler debit (§1).
* **A2 — THE SIEGEL FOLD** (§§7–8): the real-zero carve-out at the width the region
  actually needs, folded through the landed ε-quantified `Salt.SW.siegel_theorem`, and the
  resulting carve-free twisted zero-free rectangle.
* **§9 — THE COMPOSITION**: A1's socket with A2's region substituted in, leaving FOUR
  `q`-vs-`T` gates and nothing else in front of the socket's conclusion.

**NOT built here (the wave's honest STOP):** A3 (the 𝒰-exit compose) and A4
(`M4ChiSummedFreeRow`).  §7's docstring states why the rate chain's own `hxi` is still open —
it is stated in a shape (`Re < 1/2`) that no Siegel fold reaches, and the repair is a
statement change in landed files, i.e. Fable/human tier.

## THE FINDING that shapes A1 (why the `φ(q)` disappears)

`halasz_primes_chi_fibres` (landed, stone C §3) is the fibrewise route and pays `φ(q)·P` on
the diagonal.  The reason is *not* slack: on the PRIMAL side each fibre's bound reads the
FULL coefficient mass `∑_{n∈S}‖aₙ‖²`, so summing `φ(q)` fibres multiplies the diagonal by
`φ(q)`.  On the DUAL side the pole row is charged against the FIBRE's mass
`∑_{t∈𝒯_χ}‖b_{(χ,t)}‖²`, and the fibre masses ADD UP to the total — so the pole term comes
out `44π·P·∑_{r∈ℰ}‖b_r‖²` with no character count anywhere.  That is the whole content of
"the `44π·P` mass is paid ONCE per fibre": it is a statement about which side of the duality
the pole row is priced on.  The cross-character pairs then have `ψ = χ_r·χ̄_{r'} ≠ 1`, where
`L(·,ψ)` is entire and the twisted edge price has NO pole term — they go into the
`error_double_row` slot at the EDGE price.

## THE DIAGONAL FIBRES' EULER DEBIT (§1)

On a diagonal pair the character is `ψ = χ·χ⁻¹ = 1`, the PRINCIPAL character mod `q` — not
the trivial character of modulus 1.  So the diagonal window sum is
`∑_{(n,q)=1} Λ(n)n^{iu}w(n)`, and comparing it with `per_pair_contour`'s untwisted
`∑_n Λ(n)n^{iu}w(n)` costs the `p ∣ q` mass.  §1 prices that at `(log₂⌊3P⌋+1)·log q` by the
divisor route (`ArithmeticFunction.vonMangoldt_sum` on the divisors of `q^K`,
`K = log₂⌊3P⌋+1`) — the cheapest available derivation, and `P`-cheap enough that the
`P·exp(−c log P/D₄)·(log qT)²` term absorbs it with a full `√P` to spare.  The alternative
route through `neg_re_logDeriv_trivChar_le_zeta` (the `≤ log q` half-plane debit) prices the
same object but only for `Re s > 1`, i.e. it is a statement about the Euler product, not
about the window sum; the window sum needs the finite-sum form derived here.

## THE GATES (law: they ride in-statement, never absorbed)

`HalaszPrimesChiGated` (§6) is the socket's conclusion plus exactly two hypotheses:

1. the twisted edge's `q`-scale gate `8·log(40000·vkStripConst q) ≤ loglog(5T+1)`
   (`TwistedEdge.lean`'s D3 deviation; `twisted_gate_of_height` turns it into one `T`-floor
   per modulus);
2. the region hypothesis at the edge's own `c_vk` — byte-exactly
   `twisted_rect_zero_free_split`'s conclusion, for EVERY non-principal `ψ mod q`.

Both constants coincide at `1/10⁸` (the edge's `c_vk` is literally `1/10^8`,
`twisted_edge_price_strip`; the split's width is `1/10⁸`), so §8 discharges (2) outright.

## Scale and convention traps honoured here

* `σ = 1` sign convention throughout (`chiBarCoeff`, `USetChi.ramQ_chiBar_eq_halaszSum`); the
  dual side carries `n^{+it}·χ(n)`, the primal `n^{−it}·χ̄(n)`;
* the four log scales: the edge and the pole row are read at `5T+1`, the socket's decay at
  the HYBRID height `qT`; `logDn_mono` (stone C) and `D4_5T1_le` (`HalaszPrimesCore`) are the
  two absorptions, and `q ≥ 1` makes `D₄(qT) ≥ D₄(T)` free;
* `Cq = vkStripConst q = 5000·q` and `CE` stay symbolic.
-/

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-! ## §1 — the `p ∣ q` EULER DEBIT on the diagonal fibres

The principal character mod `q` kills the `n` with `(n,q) > 1`; the window sum therefore
differs from the untwisted one by the von Mangoldt mass of the non-units below `3P`.  That
mass is `≤ (log₂⌊3P⌋+1)·log q`: every non-unit `n ≤ N` with `Λ(n) ≠ 0` is a prime power
`p^k` with `p ∣ q` and `2^k ≤ N`, hence divides `q^{log₂ N + 1}`, and
`∑_{d ∣ M} Λ(d) = log M`. -/

/-- The non-unit von Mangoldt mass below `N` is at most `(log₂ N + 1)·log q`. -/
lemma sum_vonMangoldt_nonunit_le (q : ℕ) [NeZero q] (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => ¬ IsUnit ((n : ZMod q))), vonMangoldt n
      ≤ ((Nat.log 2 N : ℝ) + 1) * Real.log q := by
  classical
  set K : ℕ := Nat.log 2 N + 1 with hKdef
  set M : ℕ := q ^ K with hMdef
  have hq0 : q ≠ 0 := NeZero.ne q
  have hM0 : M ≠ 0 := by rw [hMdef]; exact pow_ne_zero _ hq0
  set F : Finset ℕ := (Finset.Icc 1 N).filter (fun n : ℕ => ¬ IsUnit ((n : ZMod q))) with hFdef
  have hsub : F.filter (fun n => vonMangoldt n ≠ 0) ⊆ M.divisors := by
    intro n hn
    rw [Finset.mem_filter, hFdef, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨_hn1, hnN⟩, hnu⟩, hΛ⟩ := hn
    obtain ⟨p, k, hp, hk, hpk⟩ := vonMangoldt_ne_zero_iff.mp hΛ
    have hpnat : p.Prime := Nat.prime_iff.mpr hp
    -- `p ∣ q`
    have hncop : ¬ Nat.Coprime n q := fun h => hnu ((ZMod.isUnit_iff_coprime n q).mpr h)
    have hpcop : ¬ Nat.Coprime p q := by
      intro h
      exact hncop (by rw [← hpk]; exact Nat.Coprime.pow_left k h)
    have hpq : p ∣ q := by
      by_contra hnd
      exact hpcop ((Nat.Prime.coprime_iff_not_dvd hpnat).mpr hnd)
    -- `k ≤ log₂ N`
    have h2k : 2 ^ k ≤ N := by
      calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hpnat.two_le k
        _ = n := hpk
        _ ≤ N := hnN
    have hkK : k ≤ K := by
      have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h2k
      omega
    -- `n = p^k ∣ q^k ∣ q^K = M`
    have hdvd : n ∣ M := by
      rw [← hpk, hMdef]
      exact dvd_trans (pow_dvd_pow_of_dvd hpq k) (pow_dvd_pow q hkK)
    exact Nat.mem_divisors.mpr ⟨hdvd, hM0⟩
  have hstep : ∑ n ∈ F, vonMangoldt n
      = ∑ n ∈ F.filter (fun n => vonMangoldt n ≠ 0), vonMangoldt n := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hn hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hn, hne⟩)
  have hle : ∑ n ∈ F.filter (fun n => vonMangoldt n ≠ 0), vonMangoldt n
      ≤ ∑ d ∈ M.divisors, vonMangoldt d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
  have hval : ∑ d ∈ M.divisors, vonMangoldt d = Real.log M := vonMangoldt_sum
  have hMlog : Real.log M = (K : ℝ) * Real.log q := by
    rw [hMdef, Nat.cast_pow, Real.log_pow]
  calc ∑ n ∈ F, vonMangoldt n
      = ∑ n ∈ F.filter (fun n => vonMangoldt n ≠ 0), vonMangoldt n := hstep
    _ ≤ ∑ d ∈ M.divisors, vonMangoldt d := hle
    _ = (K : ℝ) * Real.log q := hval.trans hMlog
    _ = ((Nat.log 2 N : ℝ) + 1) * Real.log q := by rw [hKdef]; push_cast; ring

/-- Support of the window-weighted von Mangoldt series: it vanishes past `3P`. -/
lemma window_lambda_support {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {P : ℝ}
    (hP0 : 0 < P) (u : ℝ) {n : ℕ} (hn : n ∉ Finset.range (⌊3 * P⌋₊ + 1)) :
    ((ψ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
        * (primeWindow P n : ℂ) = 0 := by
  rw [Finset.mem_range, not_lt] at hn
  have hge : 3 * P ≤ (n : ℝ) := by
    have h1 : (3 * P : ℝ) < (⌊3 * P⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (3 * P)
    have h2 : ((⌊3 * P⌋₊ : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [primeWindow_eq_zero_upper hP0 hge, Complex.ofReal_zero, mul_zero]

lemma summable_window_lambda_chi {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {P : ℝ}
    (hP0 : 0 < P) (u : ℝ) :
    Summable (fun n : ℕ => ((ψ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
      * (primeWindow P n : ℂ)) :=
  summable_of_ne_finset_zero (s := Finset.range (⌊3 * P⌋₊ + 1))
    (fun _n hn => window_lambda_support ψ hP0 u hn)

/-- **THE EULER DEBIT.**  The principal-character window sum differs from the untwisted one
by at most `(log₂⌊3P⌋ + 1)·log q`. -/
lemma norm_principal_sub_untwisted_le {q : ℕ} [NeZero q] {P : ℝ} (hP : 2 ≤ P) (u : ℝ) :
    ‖(∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
            * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
        - (∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))
            * (primeWindow P n : ℂ))‖
      ≤ ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) * Real.log q := by
  classical
  have hP0 : (0 : ℝ) < P := by linarith
  set N : ℕ := ⌊3 * P⌋₊ with hNdef
  have hsA := summable_window_lambda_chi (1 : DirichletCharacter ℂ q) hP0 u
  have hsB : Summable (fun n : ℕ => ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))
      * (primeWindow P n : ℂ)) := summable_window_pair hP0 u
  rw [← hsA.tsum_sub hsB]
  set g : ℕ → ℂ := fun n =>
    ((((1 : DirichletCharacter ℂ q) (n : ZMod q) - 1) * (vonMangoldt n : ℂ))
      * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ) with hgdef
  have hcongr : ∀ n : ℕ,
      (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
          * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ)
        - ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ) = g n := by
    intro n; rw [hgdef]; ring
  rw [tsum_congr hcongr]
  -- the difference is finitely supported
  have hgsupp : ∀ n ∉ Finset.range (N + 1), g n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hge : 3 * P ≤ (n : ℝ) := by
      have h1 : (3 * P : ℝ) < (N : ℝ) + 1 := by rw [hNdef]; exact Nat.lt_floor_add_one (3 * P)
      have h2 : ((N : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    simp only [hgdef]
    rw [primeWindow_eq_zero_upper hP0 hge, Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => hgsupp n hn)]
  -- termwise bound by the non-unit indicator
  have hterm : ∀ n ∈ Finset.range (N + 1),
      ‖g n‖ ≤ (if ¬ IsUnit ((n : ZMod q)) then vonMangoldt n else 0) := by
    intro n _
    have hw1 : ‖(primeWindow P n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (primeWindow_nonneg hP0 n)]
      exact primeWindow_le_one hP0 n
    have hw0 : (0 : ℝ) ≤ ‖(primeWindow P n : ℂ)‖ := norm_nonneg _
    have hcp : ‖(n : ℂ) ^ ((u : ℂ) * I)‖ ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [Nat.cast_zero]
        rcases eq_or_ne ((u : ℂ) * I) 0 with h | h
        · rw [h, Complex.cpow_zero]; norm_num
        · rw [Complex.zero_cpow h, norm_zero]; norm_num
      · have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        rw [← Complex.ofReal_natCast (n := n), Complex.norm_cpow_eq_rpow_re_of_pos hn0R]
        simp
    by_cases hu : IsUnit ((n : ZMod q))
    · have h1 : (1 : DirichletCharacter ℂ q) (n : ZMod q) = 1 := MulChar.one_apply hu
      have hg0 : g n = 0 := by
        simp only [hgdef, h1, sub_self, zero_mul]
      rw [hg0, norm_zero, if_neg (by simpa using hu)]
    · have h1 : (1 : DirichletCharacter ℂ q) (n : ZMod q) = 0 := MulChar.map_nonunit _ hu
      rw [if_pos hu]
      have heq : ‖g n‖
          = ‖(((0 : ℂ) - 1) * (vonMangoldt n : ℂ))‖ * ‖(n : ℂ) ^ ((u : ℂ) * I)‖
              * ‖(primeWindow P n : ℂ)‖ := by
        simp only [hgdef, h1]
        rw [norm_mul, norm_mul]
      have hval : ‖(((0 : ℂ) - 1) * (vonMangoldt n : ℂ))‖ = vonMangoldt n := by
        rw [zero_sub, neg_mul, norm_neg, one_mul, Complex.norm_real,
          Real.norm_of_nonneg vonMangoldt_nonneg]
      rw [heq, hval]
      have hAx : (0 : ℝ) ≤ vonMangoldt n * ‖(n : ℂ) ^ ((u : ℂ) * I)‖ :=
        mul_nonneg vonMangoldt_nonneg (norm_nonneg _)
      calc vonMangoldt n * ‖(n : ℂ) ^ ((u : ℂ) * I)‖ * ‖(primeWindow P n : ℂ)‖
          ≤ vonMangoldt n * ‖(n : ℂ) ^ ((u : ℂ) * I)‖ * 1 :=
            mul_le_mul_of_nonneg_left hw1 hAx
        _ = vonMangoldt n * ‖(n : ℂ) ^ ((u : ℂ) * I)‖ := mul_one _
        _ ≤ vonMangoldt n * 1 := mul_le_mul_of_nonneg_left hcp vonMangoldt_nonneg
        _ = vonMangoldt n := mul_one _
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  -- drop `n = 0` and rewrite as a filtered sum
  have hzero : ∑ n ∈ Finset.range (N + 1), (if ¬ IsUnit ((n : ZMod q)) then vonMangoldt n else 0)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => ¬ IsUnit ((n : ZMod q))), vonMangoldt n := by
    rw [Finset.sum_filter]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]; omega
    · intro n hn hnot
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Icc] at hnot
      have hn0 : n = 0 := by omega
      subst hn0
      have hz : vonMangoldt 0 = 0 := by rw [ArithmeticFunction.map_zero]
      simp [hz]
  rw [hzero]
  exact sum_vonMangoldt_nonunit_le q N

/-! ## §2 — the error double row over an ARBITRARY index set

`error_double_row`'s proof is index-agnostic; this is the same statement over a
`Finset ι`, which is what the `(χ,t)`-pair expansion needs. -/

/-- **Error double-row, generic index.**  `error_double_row` with `Finset ℝ` replaced by
`Finset ι`. -/
lemma error_double_row_gen {ι : Type*} {ℰ : Finset ι} {ε : ℝ} (b : ι → ℂ)
    (K : ι → ι → ℂ) (hK : ∀ r ∈ ℰ, ∀ r' ∈ ℰ, ‖K r r'‖ ≤ ε) :
    ‖∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r') * K r r'‖
      ≤ ε * (ℰ.card : ℝ) * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by
  have h1 : ‖∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r') * K r r'‖
      ≤ ∑ r ∈ ℰ, ∑ r' ∈ ℰ, (‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2 * ε := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r' hr' => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc ‖b r‖ * ‖b r'‖ * ‖K r r'‖
        ≤ (‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2 * ‖K r r'‖ :=
          mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (‖b r‖ - ‖b r'‖)]) (norm_nonneg _)
      _ ≤ (‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2 * ε :=
          mul_le_mul_of_nonneg_left (hK r hr r' hr') (by positivity)
  refine h1.trans ?_
  have hAe : ∑ r ∈ ℰ, ∑ _r' ∈ ℰ, ‖b r‖ ^ 2 * ε = ε * (ℰ.card : ℝ) * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by
    simp_rw [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
  have hBe : ∑ _r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r'‖ ^ 2 * ε = ε * (ℰ.card : ℝ) * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by
    have hin : ∑ r' ∈ ℰ, ‖b r'‖ ^ 2 * ε = (∑ r' ∈ ℰ, ‖b r'‖ ^ 2) * ε :=
      (Finset.sum_mul _ _ _).symm
    rw [Finset.sum_congr rfl (fun _ _ => hin), Finset.sum_const, nsmul_eq_mul]; ring
  have hide : ∑ r ∈ ℰ, ∑ r' ∈ ℰ, (‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2 * ε
      = (∑ r ∈ ℰ, ∑ _r' ∈ ℰ, ‖b r‖ ^ 2 * ε + ∑ _r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r'‖ ^ 2 * ε) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r' _ => ?_)
    ring
  rw [hide]; linarith [hAe, hBe]

/-! ## §3 — the FIBRE-SPLIT pole row

The `44π·P` mass, once per fibre.  The kernel is carried abstractly (`W`) with its two
defining properties, so no decidable equality on characters appears in the statement. -/

/-- Each character fibre of a `FibreWellSpaced` set is `WellSpaced`. -/
lemma wellSpaced_fibre {q : ℕ} {ℰ : Finset (DirichletCharacter ℂ q × ℝ)}
    (hws : FibreWellSpaced ℰ) {𝒯 : DirichletCharacter ℂ q → Finset ℝ}
    (hmem : ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ∈ 𝒯 χ ↔ (χ, t) ∈ ℰ)
    (χ : DirichletCharacter ℂ q) : WellSpaced (𝒯 χ) := by
  intro t ht u hu htu
  exact hws (χ, t) ((hmem χ t).1 ht) (χ, u) ((hmem χ u).1 hu) rfl htu

/-- **The fibre-split pole double row.**  `pole_double_row` over `(χ,t)`-pairs with the
kernel supported on the diagonal fibres: the bound is `44π·P` times the TOTAL mass — no
character count, because each fibre's row is charged against that fibre's own mass. -/
lemma pole_double_row_fibre {q : ℕ} {P T : ℝ} (hP : 2 ≤ P) (hT : 0 ≤ T)
    {ℰ : Finset (DirichletCharacter ℂ q × ℝ)} (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (b : DirichletCharacter ℂ q × ℝ → ℂ)
    (W : (DirichletCharacter ℂ q × ℝ) → (DirichletCharacter ℂ q × ℝ) → ℂ)
    (hWdiag : ∀ r r', r.1 = r'.1 → W r r' = windowKernel P 1 (r.2 - r'.2))
    (hWoff : ∀ r r', r.1 ≠ r'.1 → W r r' = 0) :
    ‖∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r') * W r r'‖
      ≤ 44 * Real.pi * P * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by
  classical
  have hP0 : 0 < P := by linarith
  obtain ⟨𝒯, hmem, hfsum⟩ := exists_charFibre ℰ
  have hfibsub : ∀ χ : DirichletCharacter ℂ q, ∀ t ∈ 𝒯 χ, t ∈ Set.Icc (-T) T := by
    intro χ t ht; exact hsub (χ, t) ((hmem χ t).1 ht)
  -- the two rows
  have hrowA : ∀ r ∈ ℰ, ∑ r' ∈ ℰ, ‖W r r'‖ ≤ 44 * Real.pi * P := by
    intro r _
    have hre : ∑ r' ∈ ℰ, ‖W r r'‖
        = ∑ χ' : DirichletCharacter ℂ q, ∑ t' ∈ 𝒯 χ', ‖W r (χ', t')‖ :=
      (hfsum (fun χ' t' => ‖W r (χ', t')‖)).symm
    rw [hre]
    have hsingle : ∑ χ' : DirichletCharacter ℂ q, ∑ t' ∈ 𝒯 χ', ‖W r (χ', t')‖
        = ∑ t' ∈ 𝒯 r.1, ‖W r (r.1, t')‖ := by
      refine Finset.sum_eq_single_of_mem r.1 (Finset.mem_univ _) (fun χ' _ hne => ?_)
      refine Finset.sum_eq_zero (fun t' _ => ?_)
      rw [hWoff r (χ', t') (by exact fun h => hne h.symm), norm_zero]
    rw [hsingle]
    have hflip : ∑ t' ∈ 𝒯 r.1, ‖W r (r.1, t')‖
        = ∑ t' ∈ 𝒯 r.1, ‖windowKernel P 1 (t' - r.2)‖ := by
      refine Finset.sum_congr rfl (fun t' _ => ?_)
      rw [hWdiag r (r.1, t') rfl, ← neg_sub t' r.2, norm_windowKernel_neg hP0]
    rw [hflip]
    exact pole_row_sum hP hT (𝒯 r.1) (wellSpaced_fibre hws hmem r.1) (hfibsub r.1) r.2
  have hrowB : ∀ r' ∈ ℰ, ∑ r ∈ ℰ, ‖W r r'‖ ≤ 44 * Real.pi * P := by
    intro r' _
    have hre : ∑ r ∈ ℰ, ‖W r r'‖
        = ∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ, ‖W (χ, t) r'‖ :=
      (hfsum (fun χ t => ‖W (χ, t) r'‖)).symm
    rw [hre]
    have hsingle : ∑ χ : DirichletCharacter ℂ q, ∑ t ∈ 𝒯 χ, ‖W (χ, t) r'‖
        = ∑ t ∈ 𝒯 r'.1, ‖W (r'.1, t) r'‖ := by
      refine Finset.sum_eq_single_of_mem r'.1 (Finset.mem_univ _) (fun χ _ hne => ?_)
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [hWoff (χ, t) r' (by exact hne), norm_zero]
    rw [hsingle]
    have hid : ∑ t ∈ 𝒯 r'.1, ‖W (r'.1, t) r'‖
        = ∑ t ∈ 𝒯 r'.1, ‖windowKernel P 1 (t - r'.2)‖ :=
      Finset.sum_congr rfl (fun t _ => by rw [hWdiag (r'.1, t) r' rfl])
    rw [hid]
    exact pole_row_sum hP hT (𝒯 r'.1) (wellSpaced_fibre hws hmem r'.1) (hfibsub r'.1) r'.2
  -- the symmetrisation
  set Mc : ℝ := 44 * Real.pi * P with hMc
  have h1 : ‖∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r') * W r r'‖
      ≤ ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r‖ * ‖b r'‖ * ‖W r r'‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r' _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have h2 : ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r‖ * ‖b r'‖ * ‖W r r'‖
      ≤ ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ((‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2) * ‖W r r'‖ := by
    refine Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun r' _ => ?_))
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith [sq_nonneg (‖b r‖ - ‖b r'‖)]
  have hA : ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r‖ ^ 2 * ‖W r r'‖ ≤ Mc * ∑ r ∈ ℰ, ‖b r‖ ^ 2 :=
    calc ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r‖ ^ 2 * ‖W r r'‖
        = ∑ r ∈ ℰ, ‖b r‖ ^ 2 * ∑ r' ∈ ℰ, ‖W r r'‖ :=
          Finset.sum_congr rfl (fun r _ => (Finset.mul_sum _ _ _).symm)
      _ ≤ ∑ r ∈ ℰ, ‖b r‖ ^ 2 * Mc :=
          Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hrowA r hr) (sq_nonneg _))
      _ = Mc * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by rw [← Finset.sum_mul, mul_comm]
  have hB : ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r'‖ ^ 2 * ‖W r r'‖ ≤ Mc * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc ∑ r' ∈ ℰ, ∑ r ∈ ℰ, ‖b r'‖ ^ 2 * ‖W r r'‖
        = ∑ r' ∈ ℰ, ‖b r'‖ ^ 2 * ∑ r ∈ ℰ, ‖W r r'‖ :=
          Finset.sum_congr rfl (fun r' _ => (Finset.mul_sum _ _ _).symm)
      _ ≤ ∑ r' ∈ ℰ, ‖b r'‖ ^ 2 * Mc :=
          Finset.sum_le_sum (fun r' hr' => mul_le_mul_of_nonneg_left (hrowB r' hr') (sq_nonneg _))
      _ = Mc * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by rw [← Finset.sum_mul, mul_comm]
  have hid : ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ((‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2) * ‖W r r'‖
      = (∑ r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r‖ ^ 2 * ‖W r r'‖
         + ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r'‖ ^ 2 * ‖W r r'‖) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r' _ => ?_)
    ring
  calc ‖∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r') * W r r'‖
      ≤ ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ‖b r‖ * ‖b r'‖ * ‖W r r'‖ := h1
    _ ≤ ∑ r ∈ ℰ, ∑ r' ∈ ℰ, ((‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2) * ‖W r r'‖ := h2
    _ = _ := hid
    _ ≤ Mc * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by linarith [hA, hB]

/-! ## §4 — THE PAIR DUAL CORE

The `(χ,t)`-pair twin of `dual_core`.  The pole row is the fibre-split one (§3), the error
row the generic one (§2), and the per-pair character is `ψ = χ_r·χ̄_{r'}`, principal exactly
on the diagonal fibres. -/

/-- The pairing identity behind the expansion: `(n^{it}χ(n))·conj(n^{it'}χ'(n))
= (χ·χ'⁻¹)(n)·n^{i(t−t')}`. -/
lemma pair_phase_conj {q : ℕ} [NeZero q] (χ χ' : DirichletCharacter ℂ q) (t t' : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    ((n : ℂ) ^ ((t : ℂ) * I) * χ (n : ZMod q))
        * (starRingEnd ℂ) ((n : ℂ) ^ ((t' : ℂ) * I) * χ' (n : ZMod q))
      = (χ * χ'⁻¹) (n : ZMod q) * (n : ℂ) ^ (((t - t' : ℝ) : ℂ) * I) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : 0 < n := hn
    exact_mod_cast this.ne'
  rw [map_mul, conj_ncast_cpow hn, conj_chi_eq_invChar, MulChar.mul_apply,
    show (starRingEnd ℂ) ((t' : ℂ) * I) = -((t' : ℂ) * I) by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring,
    show ((t - t' : ℝ) : ℂ) * I = (t : ℂ) * I + -((t' : ℂ) * I) by push_cast; ring,
    Complex.cpow_add _ _ hn0]
  ring

set_option maxHeartbeats 1600000 in
-- The pair expansion carries four large in-statement expressions (the kernel, its pole and
-- error pieces, and the coefficient mass); the unifier needs headroom past the default.
/-- **A1's core — the `(χ,t)`-pair dual bound.**  `dual_core` over pairs: the pole row is paid
`44π·P` ONCE (against the total mass), every pair's remaining kernel at `ε`. -/
lemma dual_core_pair {q : ℕ} [NeZero q] {P : ℝ} (hP : 2 ≤ P) {T : ℝ} (hT : 0 ≤ T)
    {ℰ : Finset (DirichletCharacter ℂ q × ℝ)} (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    {S : Finset ℕ} (hSprime : ∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P)
    {ε : ℝ}
    (hcross : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ u : ℝ, |u| ≤ 2 * T →
        ‖∑' n : ℕ, ((ψ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
            * (primeWindow P n : ℂ)‖ ≤ ε)
    (hdiag : ∀ u : ℝ, |u| ≤ 2 * T →
        ‖(∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
              * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ)) - windowKernel P 1 u‖ ≤ ε)
    (b : DirichletCharacter ℂ q × ℝ → ℂ) :
    ∑ n ∈ S, ‖∑ r ∈ ℰ, ((n : ℂ) ^ ((r.2 : ℂ) * I) * r.1 (n : ZMod q)) * b r‖ ^ 2
      ≤ (44 * Real.pi * P + ε * (ℰ.card : ℝ)) / Real.log P * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by
  classical
  have hP0 : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  set G : ℕ → ℝ := fun n =>
    ‖∑ r ∈ ℰ, ((n : ℂ) ^ ((r.2 : ℂ) * I) * r.1 (n : ZMod q)) * b r‖ ^ 2 with hGdef
  have hG0 : ∀ n, 0 ≤ G n := fun n => sq_nonneg _
  have htt' : ∀ r ∈ ℰ, ∀ r' ∈ ℰ, |r.2 - r'.2| ≤ 2 * T := by
    intro r hr r' hr'
    have h1 := Set.mem_Icc.mp (hsub r hr)
    have h2 := Set.mem_Icc.mp (hsub r' hr')
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hwd := window_dominates hP hG0 hSprime
  set RHSr : ℝ := ∑' n, vonMangoldt n * primeWindow P n * G n with hRHSr
  have hRHSr0 : 0 ≤ RHSr :=
    tsum_nonneg fun n =>
      mul_nonneg (mul_nonneg vonMangoldt_nonneg (primeWindow_nonneg hP0 n)) (hG0 n)
  -- the per-pair kernel and its two pieces
  set W : (DirichletCharacter ℂ q × ℝ) → (DirichletCharacter ℂ q × ℝ) → ℂ := fun r r' =>
    ∑' n : ℕ, (((r.1 * r'.1⁻¹) (n : ZMod q) * (vonMangoldt n : ℂ))
      * (n : ℂ) ^ (((r.2 - r'.2 : ℝ) : ℂ) * I)) * (primeWindow P n : ℂ) with hWdef
  set Wp : (DirichletCharacter ℂ q × ℝ) → (DirichletCharacter ℂ q × ℝ) → ℂ := fun r r' =>
    if r.1 = r'.1 then windowKernel P 1 (r.2 - r'.2) else 0 with hWpdef
  set Wk : (DirichletCharacter ℂ q × ℝ) → (DirichletCharacter ℂ q × ℝ) → ℂ := fun r r' =>
    W r r' - Wp r r' with hWkdef
  -- the expansion
  have hterm : ∀ (r r' : DirichletCharacter ℂ q × ℝ) (n : ℕ),
      ((vonMangoldt n : ℂ) * (primeWindow P n : ℂ))
        * ((((n : ℂ) ^ ((r.2 : ℂ) * I) * r.1 (n : ZMod q)) * b r)
            * (starRingEnd ℂ) (((n : ℂ) ^ ((r'.2 : ℂ) * I) * r'.1 (n : ZMod q)) * b r'))
        = b r * (starRingEnd ℂ) (b r')
            * ((((r.1 * r'.1⁻¹) (n : ZMod q) * (vonMangoldt n : ℂ))
                * (n : ℂ) ^ (((r.2 - r'.2 : ℝ) : ℂ) * I)) * (primeWindow P n : ℂ)) := by
    intro r r' n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [show (vonMangoldt 0 : ℂ) = 0 by rw [ArithmeticFunction.map_zero]; norm_num]
      ring_nf
    · have hk := pair_phase_conj r.1 r'.1 r.2 r'.2 (n := n) hn
      rw [map_mul]
      linear_combination ((vonMangoldt n : ℂ) * (primeWindow P n : ℂ) * b r
        * (starRingEnd ℂ) (b r')) * hk
  have hsummstep : ∀ r : DirichletCharacter ℂ q × ℝ,
      Summable (fun n : ℕ => ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r')
        * ((((r.1 * r'.1⁻¹) (n : ZMod q) * (vonMangoldt n : ℂ))
            * (n : ℂ) ^ (((r.2 - r'.2 : ℝ) : ℂ) * I)) * (primeWindow P n : ℂ))) := by
    intro r
    apply summable_of_ne_finset_zero (s := Finset.range (⌊3 * P⌋₊ + 1))
    intro n hn
    refine Finset.sum_eq_zero (fun r' _ => ?_)
    rw [window_lambda_support (r.1 * r'.1⁻¹) hP0 (r.2 - r'.2) hn, mul_zero]
  have hexp : (RHSr : ℂ) = ∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r') * W r r' := by
    rw [hRHSr, Complex.ofReal_tsum]
    have hstep : ∀ n, ((vonMangoldt n * primeWindow P n * G n : ℝ) : ℂ)
        = ∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r')
            * ((((r.1 * r'.1⁻¹) (n : ZMod q) * (vonMangoldt n : ℂ))
                * (n : ℂ) ^ (((r.2 - r'.2 : ℝ) : ℂ) * I)) * (primeWindow P n : ℂ)) := by
      intro n
      simp only [hGdef]
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow,
        ← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r' _ => hterm r r' n)
    rw [tsum_congr hstep, Summable.tsum_finsetSum (fun r _ => hsummstep r)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Summable.tsum_finsetSum
      (fun r' _ => (summable_window_lambda_chi (r.1 * r'.1⁻¹) hP0 (r.2 - r'.2)).mul_left _)]
    refine Finset.sum_congr rfl (fun r' _ => ?_)
    simp only [hWdef]
    rw [tsum_mul_left]
  -- the kernel bound
  have hWbound : ∀ r ∈ ℰ, ∀ r' ∈ ℰ, ‖Wk r r'‖ ≤ ε := by
    intro r hr r' hr'
    by_cases hchi : r.1 = r'.1
    · have h1 : r.1 * r'.1⁻¹ = 1 := mul_inv_eq_one.mpr hchi
      have hWp : Wp r r' = windowKernel P 1 (r.2 - r'.2) := by
        simp only [hWpdef, if_pos hchi]
      simp only [hWkdef, hWdef, h1, hWp]
      exact hdiag (r.2 - r'.2) (htt' r hr r' hr')
    · have h1 : r.1 * r'.1⁻¹ ≠ 1 := fun h => hchi (mul_inv_eq_one.mp h)
      have hWp : Wp r r' = 0 := by
        simp only [hWpdef, if_neg hchi]
      simp only [hWkdef, hWp, sub_zero, hWdef]
      exact hcross (r.1 * r'.1⁻¹) h1 (r.2 - r'.2) (htt' r hr r' hr')
  have hsplit : (RHSr : ℂ)
      = (∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r') * Wp r r')
        + (∑ r ∈ ℰ, ∑ r' ∈ ℰ, b r * (starRingEnd ℂ) (b r') * Wk r r') := by
    rw [hexp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r' _ => ?_)
    simp only [hWkdef]; ring
  have hnorm : RHSr ≤ 44 * Real.pi * P * (∑ r ∈ ℰ, ‖b r‖ ^ 2)
      + ε * (ℰ.card : ℝ) * (∑ r ∈ ℰ, ‖b r‖ ^ 2) := by
    have hcast : RHSr = ‖(RHSr : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hRHSr0]
    rw [hcast, hsplit]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ?_ (error_double_row_gen b Wk hWbound)
    refine pole_double_row_fibre hP hT hws hsub b Wp ?_ ?_
    · intro r r' h; simp only [hWpdef, if_pos h]
    · intro r r' h; simp only [hWpdef, if_neg h]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlogP]
  have hfin : (∑ p ∈ S, G p) * Real.log P
      ≤ (44 * Real.pi * P + ε * (ℰ.card : ℝ)) * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by
    calc (∑ p ∈ S, G p) * Real.log P = Real.log P * ∑ p ∈ S, G p := by ring
      _ ≤ RHSr := hwd
      _ ≤ _ := hnorm
      _ = (44 * Real.pi * P + ε * (ℰ.card : ℝ)) * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by ring
  simpa only [hGdef] using hfin

/-! ## §5 — the DUALITY GATEWAY at the `(χ,t)`-pair matrix

`l2_duality` at `φ(r, n) = n^{−i r.2}·χ̄_{r.1}(n)`: the primal side is the socket's own
left-hand side (`chiBarCoeff`, `σ = 1`, no reflection), the dual side is §4's. -/

/-- The pair matrix's adjoint entry: `conj(n^{−it}·χ̄(n)) = n^{it}·χ(n)` for `n ≥ 1`. -/
lemma conj_pairMatrix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-(t : ℂ) * I) * (starRingEnd ℂ) (χ (n : ZMod q)))
      = (n : ℂ) ^ ((t : ℂ) * I) * χ (n : ZMod q) := by
  rw [map_mul, conj_ncast_cpow hn, Complex.conj_conj]
  congr 1
  congr 1
  rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; ring

/-- **The primal socket bound from the dual one.** -/
lemma primal_of_dual_pair {q : ℕ} [NeZero q] {ℰ : Finset (DirichletCharacter ℂ q × ℝ)}
    {S : Finset ℕ} (hS1 : ∀ n ∈ S, 1 ≤ n) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hdual : ∀ b : DirichletCharacter ℂ q × ℝ → ℂ,
      ∑ n ∈ S, ‖∑ r ∈ ℰ, ((n : ℂ) ^ ((r.2 : ℂ) * I) * r.1 (n : ZMod q)) * b r‖ ^ 2
        ≤ Δ * ∑ r ∈ ℰ, ‖b r‖ ^ 2) :
    ∀ a : ℕ → ℂ, ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * I) * chiBarCoeff q r.1 a n‖ ^ 2
      ≤ Δ * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  set φ : (DirichletCharacter ℂ q × ℝ) → ℕ → ℂ := fun r n =>
    (n : ℂ) ^ (-(r.2 : ℂ) * I) * (starRingEnd ℂ) (r.1 (n : ZMod q)) with hφ
  have hdual' : ∀ b : DirichletCharacter ℂ q × ℝ → ℂ,
      ∑ n ∈ S, ‖∑ r ∈ ℰ, (starRingEnd ℂ) (φ r n) * b r‖ ^ 2 ≤ Δ * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := by
    intro b
    have heq : ∀ n ∈ S, ∑ r ∈ ℰ, (starRingEnd ℂ) (φ r n) * b r
        = ∑ r ∈ ℰ, ((n : ℂ) ^ ((r.2 : ℂ) * I) * r.1 (n : ZMod q)) * b r := by
      intro n hn
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [hφ, conj_pairMatrix r.1 r.2 (hS1 n hn)]
    calc ∑ n ∈ S, ‖∑ r ∈ ℰ, (starRingEnd ℂ) (φ r n) * b r‖ ^ 2
        = ∑ n ∈ S, ‖∑ r ∈ ℰ, ((n : ℂ) ^ ((r.2 : ℂ) * I) * r.1 (n : ZMod q)) * b r‖ ^ 2 :=
          Finset.sum_congr rfl (fun n hn => by rw [heq n hn])
      _ ≤ Δ * ∑ r ∈ ℰ, ‖b r‖ ^ 2 := hdual b
  have hprimal := (l2_duality ℰ S φ hΔ).mpr hdual'
  intro a
  have heq : ∀ r : DirichletCharacter ℂ q × ℝ,
      ∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * I) * chiBarCoeff q r.1 a n = ∑ n ∈ S, φ r n * a n := by
    intro r
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hφ, chiBarCoeff_apply, mul_assoc]
  calc ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * I) * chiBarCoeff q r.1 a n‖ ^ 2
      = ∑ r ∈ ℰ, ‖∑ n ∈ S, φ r n * a n‖ ^ 2 :=
        Finset.sum_congr rfl (fun r _ => by rw [heq r])
    _ ≤ Δ * ∑ n ∈ S, ‖a n‖ ^ 2 := hprimal a

/-! ## §6 — the absorption and THE GATED SOCKET

The three prices (edge, untwisted, Euler debit) are absorbed into the socket's own shape
`P·exp(−c·log P/D₄(qT))·(log qT)²`.  The two new absorption constants (`K₄` for
`D₄(5T+1) ≤ K₄·D₄(T)`, `K₅` for `D₅(5T+1) ≤ K₅·(log T)²`) are the `HalaszPrimesCore`
pattern with the extra `loglog` priced by `log u ≤ u^{1/4}·4`. -/

/-- `(loglog T)^5 ≤ 4^5·(log T)^{5/4}` once `log T ≥ 1` (`loglog4_le` at one more power). -/
lemma loglog5_le {T : ℝ} (hLT : 1 ≤ Real.log T) :
    (Real.log (Real.log T)) ^ (5 : ℕ)
      ≤ (4 : ℝ) ^ (5 : ℕ) * (Real.log T) ^ ((5 : ℝ) / 4) := by
  have hLT0 : 0 < Real.log T := by linarith
  have hll0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hLT
  have hll : Real.log (Real.log T) ≤ 4 * (Real.log T) ^ ((1 : ℝ) / 4) := by
    have h := log_le_rpow_div hLT0 (by norm_num : (0 : ℝ) < 1 / 4)
    calc Real.log (Real.log T) ≤ (Real.log T) ^ ((1 : ℝ) / 4) / (1 / 4) := h
      _ = 4 * (Real.log T) ^ ((1 : ℝ) / 4) := by ring
  calc (Real.log (Real.log T)) ^ (5 : ℕ)
      ≤ (4 * (Real.log T) ^ ((1 : ℝ) / 4)) ^ (5 : ℕ) := pow_le_pow_left₀ hll0 hll 5
    _ = (4 : ℝ) ^ (5 : ℕ) * ((Real.log T) ^ ((1 : ℝ) / 4)) ^ (5 : ℕ) := by rw [mul_pow]
    _ = (4 : ℝ) ^ (5 : ℕ) * (Real.log T) ^ ((5 : ℝ) / 4) := by
        rw [← Real.rpow_natCast ((Real.log T) ^ ((1 : ℝ) / 4)) 5, ← Real.rpow_mul hLT0.le]
        norm_num

/-- `K₄ = 2^{3/4}·16`; the constant in `D₄(5T+1) ≤ K₄·D₄(T)`. -/
noncomputable def K₄ : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 4) * 16

/-- `D₄(5T+1) ≤ K₄·D₄(T)` — the `D3_5T1_le` pattern with the power unchanged. -/
lemma D4_5T1_le_D4 {T : ℝ} (hT : 6 ≤ T) (hLT1 : 1 ≤ Real.log T)
    (hll1 : 1 ≤ Real.log (Real.log T)) :
    (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)
      ≤ K₄ * ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)) := by
  have hT0 : 0 < T := by linarith
  have hlog5 : Real.log (5 * T + 1) ≤ 2 * Real.log T := log5T1_le_two_logT hT
  have hlog5nn : 0 ≤ Real.log (5 * T + 1) := Real.log_nonneg (by linarith)
  have hlog5ge1 : 1 ≤ Real.log (5 * T + 1) :=
    le_trans hLT1 (Real.log_le_log hT0 (by linarith : T ≤ 5 * T + 1))
  have hloglog5 : Real.log (Real.log (5 * T + 1)) ≤ 2 * Real.log (Real.log T) :=
    loglog5T1_le hT hLT1 hll1
  have hloglog5nn : 0 ≤ Real.log (Real.log (5 * T + 1)) := Real.log_nonneg hlog5ge1
  have hllTnn : 0 ≤ Real.log (Real.log T) := by linarith
  have hrp : (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
      ≤ (2 : ℝ) ^ ((3 : ℝ) / 4) * (Real.log T) ^ ((3 : ℝ) / 4) := by
    calc (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
        ≤ (2 * Real.log T) ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow hlog5nn hlog5 (by norm_num)
      _ = (2 : ℝ) ^ ((3 : ℝ) / 4) * (Real.log T) ^ ((3 : ℝ) / 4) :=
          Real.mul_rpow (by norm_num) (by linarith)
  have hpw : (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)
      ≤ 16 * (Real.log (Real.log T)) ^ (4 : ℕ) := by
    calc (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)
        ≤ (2 * Real.log (Real.log T)) ^ (4 : ℕ) := pow_le_pow_left₀ hloglog5nn hloglog5 4
      _ = 16 * (Real.log (Real.log T)) ^ (4 : ℕ) := by ring
  have hcombine := mul_le_mul hrp hpw (pow_nonneg hloglog5nn 4)
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _))
  calc (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)
      ≤ ((2 : ℝ) ^ ((3 : ℝ) / 4) * (Real.log T) ^ ((3 : ℝ) / 4))
          * (16 * (Real.log (Real.log T)) ^ (4 : ℕ)) := hcombine
    _ = K₄ * ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ)) := by
        rw [K₄]; ring

/-- `K₅ = 2^{3/4}·32·4^5`; the constant in `D₅(5T+1) ≤ K₅·(log T)²`. -/
noncomputable def K₅ : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 4) * 32 * (4 : ℝ) ^ (5 : ℕ)

/-- `D₅(5T+1) ≤ K₅·(log T)²` — the `D4_5T1_le` pattern at one more `loglog`. -/
lemma D5_5T1_le {T : ℝ} (hT : 6 ≤ T) (hLT1 : 1 ≤ Real.log T)
    (hll1 : 1 ≤ Real.log (Real.log T)) :
    (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)
      ≤ K₅ * (Real.log T) ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hLT0 : 0 < Real.log T := by linarith
  have hlog5 : Real.log (5 * T + 1) ≤ 2 * Real.log T := log5T1_le_two_logT hT
  have hlog5nn : 0 ≤ Real.log (5 * T + 1) := Real.log_nonneg (by linarith)
  have hlog5ge1 : 1 ≤ Real.log (5 * T + 1) :=
    le_trans hLT1 (Real.log_le_log hT0 (by linarith : T ≤ 5 * T + 1))
  have hloglog5 : Real.log (Real.log (5 * T + 1)) ≤ 2 * Real.log (Real.log T) :=
    loglog5T1_le hT hLT1 hll1
  have hloglog5nn : 0 ≤ Real.log (Real.log (5 * T + 1)) := Real.log_nonneg hlog5ge1
  have hllTnn : 0 ≤ Real.log (Real.log T) := by linarith
  have hrp : (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
      ≤ (2 : ℝ) ^ ((3 : ℝ) / 4) * (Real.log T) ^ ((3 : ℝ) / 4) := by
    calc (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
        ≤ (2 * Real.log T) ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow hlog5nn hlog5 (by norm_num)
      _ = (2 : ℝ) ^ ((3 : ℝ) / 4) * (Real.log T) ^ ((3 : ℝ) / 4) :=
          Real.mul_rpow (by norm_num) (by linarith)
  have hpw5 : (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)
      ≤ 32 * (4 : ℝ) ^ (5 : ℕ) * (Real.log T) ^ ((5 : ℝ) / 4) := by
    calc (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)
        ≤ (2 * Real.log (Real.log T)) ^ (5 : ℕ) := pow_le_pow_left₀ hloglog5nn hloglog5 5
      _ = 32 * (Real.log (Real.log T)) ^ (5 : ℕ) := by ring
      _ ≤ 32 * ((4 : ℝ) ^ (5 : ℕ) * (Real.log T) ^ ((5 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (loglog5_le hLT1) (by norm_num)
      _ = 32 * (4 : ℝ) ^ (5 : ℕ) * (Real.log T) ^ ((5 : ℝ) / 4) := by ring
  have hrpnn : 0 ≤ (2 : ℝ) ^ ((3 : ℝ) / 4) * (Real.log T) ^ ((3 : ℝ) / 4) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLT0.le _)
  have hcombine := mul_le_mul hrp hpw5 (pow_nonneg hloglog5nn 5) hrpnn
  calc (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)
      ≤ ((2 : ℝ) ^ ((3 : ℝ) / 4) * (Real.log T) ^ ((3 : ℝ) / 4))
          * (32 * (4 : ℝ) ^ (5 : ℕ) * (Real.log T) ^ ((5 : ℝ) / 4)) := hcombine
    _ = K₅ * ((Real.log T) ^ ((3 : ℝ) / 4) * (Real.log T) ^ ((5 : ℝ) / 4)) := by rw [K₅]; ring
    _ = K₅ * (Real.log T) ^ 2 := by
        rw [← Real.rpow_add hLT0]
        norm_num

/-- The Euler debit's `P`-side, crudely: `log₂⌊3P⌋ + 1 ≤ 9√P` for `P ≥ 2`. -/
lemma natLog2_floor_le_sqrt {P : ℝ} (hP : 2 ≤ P) :
    ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) ≤ 9 * Real.sqrt P := by
  have hP0 : (0 : ℝ) < P := by linarith
  set N : ℕ := ⌊3 * P⌋₊ with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    have : (1 : ℝ) ≤ 3 * P := by linarith
    exact Nat.le_floor (by exact_mod_cast this)
  have hN0 : N ≠ 0 := by omega
  have hNle : (N : ℝ) ≤ 3 * P := by rw [hNdef]; exact Nat.floor_le (by linarith)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  -- `2^{log₂ N} ≤ N`
  have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
    have h := Nat.pow_log_le_self 2 hN0
    exact_mod_cast h
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hkey : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  have hlogN : Real.log N ≤ 4 * Real.sqrt P := by
    have h1 : Real.log N ≤ Real.log (3 * P) := Real.log_le_log (by linarith) hNle
    have h2 : Real.log (3 * P) ≤ 2 * Real.sqrt (3 * P) :=
      Salt.SW.log_le_two_sqrt (by linarith)
    have h3 : Real.sqrt (3 * P) ≤ 2 * Real.sqrt P := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      have h4 : Real.sqrt 3 ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      exact mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg P)
    linarith
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt P := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hnl : (Nat.log 2 N : ℝ) ≤ 8 * Real.sqrt P := by
    have h0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) := by positivity
    nlinarith [hkey, hlogN, hlog2, h0]
  linarith

/-- **THE GATED SOCKET** — `USetChi.HalaszPrimesChi`'s conclusion under the two gates the
twisted machinery genuinely demands (see the module docstring): the `q`-scale height gate of
the twisted edge, and the twisted zero-free rectangle at `c_vk` for every non-principal
`ψ mod q`.  Both are `q`-dependent, so neither can be absorbed into the socket's uniform
`T₀` — that is the honest shape of the port's `(χ,t)`-pair row. -/
def HalaszPrimesChiGated (c_vk C c T₀ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
    (∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - c_vk / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))) →
  ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
    (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
  ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
  ∀ (a : ℕ → ℂ),
    ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
      ≤ C * (P + (ℰ.card : ℝ) * P
              * Real.exp (-c * Real.log P
                  / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                      * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
              * (Real.log ((q : ℝ) * T)) ^ 2)
          / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2
/-- The uniform absorption step (`absorb_arith`'s `hεA` shape, isolated): a decaying factor
against a `K·Lv`-dominated cofactor.  (`L` is unavailable as a binder name — the `LSeries`
notation is open in this file.) -/
lemma absorb_exp_term {Cc Pv x e D K Lv : ℝ} (hCc : 0 ≤ Cc) (hPv : 0 ≤ Pv)
    (hx : x ≤ e) (hD : D ≤ K * Lv) (hD0 : 0 ≤ D) (he0 : 0 ≤ e) :
    Cc * Pv * x * D ≤ Cc * K * (Pv * e * Lv) := by
  have h1 : x * D ≤ e * (K * Lv) := mul_le_mul hx hD hD0 he0
  calc Cc * Pv * x * D = (Cc * Pv) * (x * D) := by ring
    _ ≤ (Cc * Pv) * (e * (K * Lv)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCc hPv)
    _ = Cc * K * (Pv * e * Lv) := by ring

set_option maxHeartbeats 3200000 in
-- The assembly threads seven absorption bounds against one `∃`-packaged constant; the
-- elaborator needs headroom past the default.
/-- **A1 — THE PAIR DUAL, ASSEMBLED.**  `HalaszPrimesChiGated` from the twisted edge price
(`TwistedWindowPriceGated`, at any admissible constants) and the landed untwisted per-pair
price (`per_pair_contour`).  This is stone C's residue discharged: the socket's diagonal term
is `P`, not `φ(q)·P`.

The decay constant is `c = min(c_vk/(2K₄), c₀/(2Cκ), 1/10)`: the first two match the two
prices' contour depths against the socket's `D₄(qT)` (via `D4_5T1_le_D4` and `D3_5T1_le`,
then `logDn_mono` for `D₄(T) ≤ D₄(qT)`), the third is what makes `1/T ≤ exp(−c log P/D₄(qT))`
at `P ≤ T^10`.  The `(log qT)²` factor absorbs `D₅(5T+1)` and `D₄(5T+1)` (`D5_5T1_le`,
`D4_5T1_le`) and — through `√P ≤ P·exp(−c log P/D₄(qT))` — the Euler debit. -/
theorem halaszPrimesChiGated_of_price {c_vk C₁ C₂ C₃ T₀e : ℝ}
    (hc_vk : 0 < c_vk) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hT₀e : Real.exp (Real.exp 100) ≤ T₀e)
    (hprice : TwistedWindowPriceGated c_vk C₁ C₂ C₃ T₀e) :
    ∃ C c T₀ : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧ HalaszPrimesChiGated c_vk C c T₀ := by
  obtain ⟨c₀, E₁, E₂, E₃, T₀z, hc₀, hE₁, hE₂, hE₃, hT₀z, hpp⟩ := per_pair_contour
  have hK₂0 : 0 < K₂ := by rw [K₂]; positivity
  have hK₄0 : 0 < K₄ := by rw [K₄]; positivity
  have hK₅0 : 0 < K₅ := by rw [K₅]; positivity
  have hCκ0 : 0 < Cκ := by rw [Cκ]; positivity
  set c : ℝ := min (min (c_vk / (2 * K₄)) (c₀ / (2 * Cκ))) (1 / 10) with hcdef
  have hc0 : 0 < c := by
    rw [hcdef]
    exact lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hcK₄ : c * K₄ ≤ c_vk / 2 := by
    have h : c ≤ c_vk / (2 * K₄) := by
      rw [hcdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : c * (2 * K₄) ≤ c_vk := (le_div_iff₀ (by positivity)).mp h
    linarith
  have hcCκ : c * Cκ ≤ c₀ / 2 := by
    have h : c ≤ c₀ / (2 * Cκ) := by
      rw [hcdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have h2 : c * (2 * Cκ) ≤ c₀ := (le_div_iff₀ (by positivity)).mp h
    linarith
  have hc10 : c ≤ 1 / 10 := by rw [hcdef]; exact min_le_right _ _
  set Cε : ℝ := C₁ * K₅ + C₂ * 10 + C₃ * K₅ + E₁ * K₂ + E₂ * 10 + E₃ * K₂ + 9 with hCεdef
  have hCε0 : 0 < Cε := by rw [hCεdef]; positivity
  refine ⟨44 * Real.pi + Cε, c, max T₀e T₀z, by positivity, hc0,
    le_trans hT₀z (le_max_right _ _), ?_⟩
  intro q hq T P hT hP hPT10 hgate hregion ℰ hws hsub S hS a
  -- ⟦the scales⟧
  have hT₀e' : T₀e ≤ T := le_trans (le_max_left _ _) hT
  have hT₀z' : T₀z ≤ T := le_trans (le_max_right _ _) hT
  have hE101 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hEbig : (101 : ℝ) ≤ Real.exp (Real.exp 100) := by
    have h2 : Real.exp 100 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hTE : Real.exp (Real.exp 100) ≤ T := le_trans hT₀e hT₀e'
  have hT6 : (6 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hP0 : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hLT100 : Real.exp 100 ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp 100)]; exact Real.log_le_log (Real.exp_pos _) hTE
  have hLT1 : (1 : ℝ) ≤ Real.log T := by linarith
  have hllT100 : (100 : ℝ) ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hLT100
  have hllT1 : (1 : ℝ) ≤ Real.log (Real.log T) := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqT : T ≤ (q : ℝ) * T := by nlinarith
  have hlogq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hlogP10 : Real.log P ≤ 10 * Real.log T := by
    have h := Real.log_le_log (by positivity) hPT10
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  -- ⟦the three prices, pulled BEFORE the abbreviations so that `set` folds them⟧
  have hedgeB : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ u : ℝ, |u| ≤ 2 * T →
      ‖∑' n : ℕ, ((ψ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
          * (primeWindow P n : ℂ)‖
        ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P
                / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                    * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)))
              * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ))
          + C₂ * P * Real.log P / T
          + C₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (5 : ℕ)) * P / T ^ 2 :=
    fun ψ hψ1 u hu => hprice q ψ hψ1 T P u hT₀e' hP hu hgate (hregion ψ hψ1)
  have hppB : ∀ u : ℝ, |u| ≤ 2 * T →
      ‖(∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
            - windowKernel P 1 u‖
        ≤ E₁ * P * Real.exp (-(c₀ / 2) * Real.log P
                / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                    * (Real.log (Real.log (5 * T + 1))) ^ (3 : ℕ)))
              * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                  * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ))
          + E₂ * P * Real.log P / T
          + E₃ * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) * P / T ^ 2 :=
    fun u hu => hpp T P u hT₀z' hP hu
  have hdebitB : ∀ u : ℝ,
      ‖(∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
              * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
          - (∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))
              * (primeWindow P n : ℂ))‖
        ≤ ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) * Real.log q :=
    fun u => norm_principal_sub_untwisted_le hP u
  -- ⟦the four log-scale abbreviations⟧
  set Lg : ℝ := Real.log (5 * T + 1) with hLgdef
  set ℓ : ℝ := Real.log (Real.log (5 * T + 1)) with hℓdef
  set Lq : ℝ := Real.log ((q : ℝ) * T) with hLqdef
  set ℓq : ℝ := Real.log (Real.log ((q : ℝ) * T)) with hℓqdef
  have hLqT : Real.log T ≤ Lq := by rw [hLqdef]; exact Real.log_le_log hT0 hqT
  have hLq1 : (1 : ℝ) ≤ Lq := by linarith
  have hLqsq : Lq ≤ Lq ^ 2 := by nlinarith
  have hLg100 : Real.exp 100 ≤ Lg := by
    rw [hLgdef]
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hLg1 : (1 : ℝ) ≤ Lg := by linarith
  have hℓ100 : (100 : ℝ) ≤ ℓ := by
    rw [hℓdef, ← hLgdef, ← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hLg100
  set D4g : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) with hD4gdef
  set D5g : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (5 : ℕ) with hD5gdef
  set D3g : ℝ := Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) with hD3gdef
  set D4q : ℝ := Lq ^ ((3 : ℝ) / 4) * ℓq ^ (4 : ℕ) with hD4qdef
  have hLgrp : (0 : ℝ) < Lg ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
  have hD4gpos : (0 : ℝ) < D4g := by rw [hD4gdef]; positivity
  have hD5gpos : (0 : ℝ) < D5g := by rw [hD5gdef]; positivity
  have hD3gpos : (0 : ℝ) < D3g := by rw [hD3gdef]; positivity
  have hD4T1 : (1 : ℝ) ≤ (Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ) := by
    have h1 : (1 : ℝ) ≤ (Real.log T) ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLT1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (Real.log (Real.log T)) ^ (4 : ℕ) := one_le_pow₀ hllT1
    nlinarith
  have hD4Tq : (Real.log T) ^ ((3 : ℝ) / 4) * (Real.log (Real.log T)) ^ (4 : ℕ) ≤ D4q := by
    rw [hD4qdef, hLqdef, hℓqdef]
    exact logDn_mono 4 (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ T) hqT
  have hD4q1 : (1 : ℝ) ≤ D4q := le_trans hD4T1 hD4Tq
  have hD4qpos : (0 : ℝ) < D4q := by linarith
  -- ⟦the decay factor⟧
  set expc : ℝ := Real.exp (-c * Real.log P / D4q) with hexpcdef
  have hexpc0 : (0 : ℝ) < expc := by rw [hexpcdef]; exact Real.exp_pos _
  -- ⟦the four decay/height comparisons⟧
  have hcmp_edge : Real.exp (-(c_vk / 2) * Real.log P / D4g) ≤ expc := by
    rw [hexpcdef]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff, div_le_div_iff₀ hD4qpos hD4gpos]
    have h1 : D4g ≤ K₄ * D4q := by
      rw [hD4gdef, hLgdef, hℓdef]
      refine le_trans (D4_5T1_le_D4 hT6 hLT1 hllT1) ?_
      exact mul_le_mul_of_nonneg_left hD4Tq hK₄0.le
    have h2 : c * Real.log P * D4g ≤ c * Real.log P * (K₄ * D4q) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : c * K₄ * (Real.log P * D4q) ≤ (c_vk / 2) * (Real.log P * D4q) :=
      mul_le_mul_of_nonneg_right hcK₄ (by positivity)
    nlinarith [h2, h3]
  have hcmp_pp : Real.exp (-(c₀ / 2) * Real.log P / D3g) ≤ expc := by
    rw [hexpcdef]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff, div_le_div_iff₀ hD4qpos hD3gpos]
    have h1 : D3g ≤ Cκ * D4q := by
      rw [hD3gdef, hLgdef, hℓdef]
      refine le_trans (D3_5T1_le hT6 hLT1 hllT1) ?_
      exact mul_le_mul_of_nonneg_left hD4Tq hCκ0.le
    have h2 : c * Real.log P * D3g ≤ c * Real.log P * (Cκ * D4q) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : c * Cκ * (Real.log P * D4q) ≤ (c₀ / 2) * (Real.log P * D4q) :=
      mul_le_mul_of_nonneg_right hcCκ (by positivity)
    nlinarith [h2, h3]
  have hD5Lq : D5g ≤ K₅ * Lq ^ 2 := by
    have h1 : D5g ≤ K₅ * (Real.log T) ^ 2 := by
      rw [hD5gdef, hLgdef, hℓdef]; exact D5_5T1_le hT6 hLT1 hllT1
    have h2 : K₅ * (Real.log T) ^ 2 ≤ K₅ * Lq ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hK₅0.le
      nlinarith [hLqT, hLT1]
    linarith
  have hD4Lq : D4g ≤ K₂ * Lq ^ 2 := by
    have h1 : D4g ≤ K₂ * (Real.log T) ^ 2 := by
      rw [hD4gdef, hLgdef, hℓdef]; exact D4_5T1_le hT6 hLT1 hllT1
    have h2 : K₂ * (Real.log T) ^ 2 ≤ K₂ * Lq ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hK₂0.le
      nlinarith [hLqT, hLT1]
    linarith
  have hlogPLq : Real.log P ≤ 10 * Lq ^ 2 := by nlinarith [hlogP10, hLqT, hLqsq]
  have hTinv : 1 / T ≤ expc := by
    rw [hexpcdef, show (1 : ℝ) / T = Real.exp (-Real.log T) by
      rw [Real.exp_neg, Real.exp_log hT0, one_div]]
    refine Real.exp_le_exp.mpr ?_
    rw [neg_mul, neg_div, neg_le_neg_iff, div_le_iff₀ hD4qpos]
    have s1 : c * Real.log P ≤ (1 / 10) * Real.log P :=
      mul_le_mul_of_nonneg_right hc10 hlogP.le
    have s2 : (1 / 10 : ℝ) * Real.log P ≤ Real.log T := by linarith
    have s3 : Real.log T ≤ Real.log T * D4q := by nlinarith [hD4q1, hLT1]
    linarith
  have hT2inv : 1 / T ^ 2 ≤ expc := by
    have h : 1 / T ^ 2 ≤ 1 / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]; nlinarith
    linarith [hTinv]
  have hsqrtP : Real.sqrt P ≤ P * expc := by
    have hs : Real.sqrt P = Real.exp (Real.log P / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hP0]
      congr 1; ring
    have hPe : P * expc = Real.exp (Real.log P + -c * Real.log P / D4q) := by
      rw [Real.exp_add, Real.exp_log hP0, hexpcdef]
    rw [hs, hPe]
    refine Real.exp_le_exp.mpr ?_
    have h1 : c * Real.log P / D4q ≤ Real.log P / 2 := by
      rw [div_le_div_iff₀ hD4qpos (by norm_num : (0:ℝ) < 2)]
      have s1 : c * Real.log P * 2 ≤ (1 / 5) * Real.log P := by nlinarith [hc10, hlogP]
      have s2 : (1 / 5 : ℝ) * Real.log P ≤ Real.log P * D4q := by nlinarith [hD4q1, hlogP]
      linarith
    have h2 : -c * Real.log P / D4q = -(c * Real.log P / D4q) := by ring
    rw [h2]
    linarith
  -- ⟦the single error level `ε`⟧
  set εE : ℝ := C₁ * P * Real.exp (-(c_vk / 2) * Real.log P / D4g) * D5g
      + C₂ * P * Real.log P / T + C₃ * D5g * P / T ^ 2 with hεEdef
  set εZ : ℝ := E₁ * P * Real.exp (-(c₀ / 2) * Real.log P / D3g) * D4g
      + E₂ * P * Real.log P / T + E₃ * D4g * P / T ^ 2 with hεZdef
  set εD : ℝ := ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) * Real.log q with hεDdef
  have hεE0 : (0 : ℝ) ≤ εE := by
    rw [hεEdef]
    have h1 : (0:ℝ) ≤ C₁ * P * Real.exp (-(c_vk / 2) * Real.log P / D4g) * D5g := by positivity
    have h2 : (0:ℝ) ≤ C₂ * P * Real.log P / T := by positivity
    have h3 : (0:ℝ) ≤ C₃ * D5g * P / T ^ 2 := by positivity
    linarith
  have hεZ0 : (0 : ℝ) ≤ εZ := by
    rw [hεZdef]
    have h1 : (0:ℝ) ≤ E₁ * P * Real.exp (-(c₀ / 2) * Real.log P / D3g) * D4g := by positivity
    have h2 : (0:ℝ) ≤ E₂ * P * Real.log P / T := by positivity
    have h3 : (0:ℝ) ≤ E₃ * D4g * P / T ^ 2 := by positivity
    linarith
  have hεD0 : (0 : ℝ) ≤ εD := by rw [hεDdef]; positivity
  set ε : ℝ := εE + εZ + εD with hεdef
  have hε0 : (0 : ℝ) ≤ ε := by rw [hεdef]; linarith
  -- ⟦the two price hypotheses of the pair dual⟧
  have hcross : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ u : ℝ, |u| ≤ 2 * T →
      ‖∑' n : ℕ, ((ψ (n : ZMod q) * (vonMangoldt n : ℂ)) * (n : ℂ) ^ ((u : ℂ) * I))
          * (primeWindow P n : ℂ)‖ ≤ ε := by
    intro ψ hψ1 u hu
    have h := hedgeB ψ hψ1 u hu
    rw [hεdef]
    linarith [h, hεZ0, hεD0]
  have hdiag : ∀ u : ℝ, |u| ≤ 2 * T →
      ‖(∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
            * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ)) - windowKernel P 1 u‖ ≤ ε := by
    intro u hu
    have h1 := hdebitB u
    have h2 := hppB u hu
    have hid : (∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
            * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ)) - windowKernel P 1 u
        = ((∑' n : ℕ, (((1 : DirichletCharacter ℂ q) (n : ZMod q) * (vonMangoldt n : ℂ))
              * (n : ℂ) ^ ((u : ℂ) * I)) * (primeWindow P n : ℂ))
            - (∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))
              * (primeWindow P n : ℂ)))
          + ((∑' n : ℕ, ((vonMangoldt n : ℂ) * (n : ℂ) ^ ((u : ℂ) * I))
              * (primeWindow P n : ℂ)) - windowKernel P 1 u) := by ring
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    rw [hεdef]
    linarith [h1, h2, hεE0]
  -- ⟦the dual bound, then the duality gateway⟧
  have hdual := dual_core_pair hP hT0.le hws hsub hS hcross hdiag
  have hΔ0 : (0 : ℝ) ≤ (44 * Real.pi * P + ε * (ℰ.card : ℝ)) / Real.log P := by
    have h1 : (0:ℝ) ≤ 44 * Real.pi * P := by positivity
    have h2 : (0:ℝ) ≤ ε * (ℰ.card : ℝ) := mul_nonneg hε0 (by positivity)
    exact div_nonneg (by linarith) hlogP.le
  have hS1 : ∀ n ∈ S, 1 ≤ n := fun n hn => le_trans (by norm_num) (hS n hn).1.two_le
  have hprim := primal_of_dual_pair hS1 hΔ0 hdual a
  -- ⟦the absorption: `ε ≤ Cε·P·expc·(log qT)²`⟧
  have b1 : C₁ * P * Real.exp (-(c_vk / 2) * Real.log P / D4g) * D5g
      ≤ C₁ * K₅ * (P * expc * Lq ^ 2) :=
    absorb_exp_term hC₁.le hP0.le hcmp_edge hD5Lq hD5gpos.le hexpc0.le
  have b2 : C₂ * P * Real.log P / T ≤ C₂ * 10 * (P * expc * Lq ^ 2) := by
    have h := absorb_exp_term (Cc := C₂) (Pv := P) (x := 1 / T) (e := expc)
      (D := Real.log P) (K := 10) (Lv := Lq ^ 2) hC₂.le hP0.le hTinv hlogPLq hlogP.le hexpc0.le
    calc C₂ * P * Real.log P / T = C₂ * P * (1 / T) * Real.log P := by ring
      _ ≤ C₂ * 10 * (P * expc * Lq ^ 2) := h
  have b3 : C₃ * D5g * P / T ^ 2 ≤ C₃ * K₅ * (P * expc * Lq ^ 2) := by
    have h := absorb_exp_term (Cc := C₃) (Pv := P) (x := 1 / T ^ 2) (e := expc)
      (D := D5g) (K := K₅) (Lv := Lq ^ 2) hC₃.le hP0.le hT2inv hD5Lq hD5gpos.le hexpc0.le
    calc C₃ * D5g * P / T ^ 2 = C₃ * P * (1 / T ^ 2) * D5g := by ring
      _ ≤ C₃ * K₅ * (P * expc * Lq ^ 2) := h
  have b4 : E₁ * P * Real.exp (-(c₀ / 2) * Real.log P / D3g) * D4g
      ≤ E₁ * K₂ * (P * expc * Lq ^ 2) :=
    absorb_exp_term hE₁.le hP0.le hcmp_pp hD4Lq hD4gpos.le hexpc0.le
  have b5 : E₂ * P * Real.log P / T ≤ E₂ * 10 * (P * expc * Lq ^ 2) := by
    have h := absorb_exp_term (Cc := E₂) (Pv := P) (x := 1 / T) (e := expc)
      (D := Real.log P) (K := 10) (Lv := Lq ^ 2) hE₂.le hP0.le hTinv hlogPLq hlogP.le hexpc0.le
    calc E₂ * P * Real.log P / T = E₂ * P * (1 / T) * Real.log P := by ring
      _ ≤ E₂ * 10 * (P * expc * Lq ^ 2) := h
  have b6 : E₃ * D4g * P / T ^ 2 ≤ E₃ * K₂ * (P * expc * Lq ^ 2) := by
    have h := absorb_exp_term (Cc := E₃) (Pv := P) (x := 1 / T ^ 2) (e := expc)
      (D := D4g) (K := K₂) (Lv := Lq ^ 2) hE₃.le hP0.le hT2inv hD4Lq hD4gpos.le hexpc0.le
    calc E₃ * D4g * P / T ^ 2 = E₃ * P * (1 / T ^ 2) * D4g := by ring
      _ ≤ E₃ * K₂ * (P * expc * Lq ^ 2) := h
  have b7 : εD ≤ 9 * (P * expc * Lq ^ 2) := by
    rw [hεDdef]
    have hd1 : ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) ≤ 9 * Real.sqrt P := natLog2_floor_le_sqrt hP
    have hd2 : Real.log q ≤ Lq ^ 2 := by
      have h : Real.log q ≤ Lq := by
        rw [hLqdef]; exact Real.log_le_log (by linarith) (by nlinarith)
      linarith [hLqsq]
    have hstep : ((Nat.log 2 ⌊3 * P⌋₊ : ℝ) + 1) * Real.log q ≤ (9 * Real.sqrt P) * Lq ^ 2 :=
      mul_le_mul hd1 hd2 hlogq0 (by positivity)
    refine hstep.trans ?_
    have h9 : (9 : ℝ) * Real.sqrt P ≤ 9 * (P * expc) := by linarith [hsqrtP]
    calc (9 * Real.sqrt P) * Lq ^ 2 ≤ (9 * (P * expc)) * Lq ^ 2 :=
          mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = 9 * (P * expc * Lq ^ 2) := by ring
  have habs : ε ≤ Cε * (P * expc * Lq ^ 2) := by
    have hsum : εE + εZ + εD
        ≤ C₁ * K₅ * (P * expc * Lq ^ 2) + C₂ * 10 * (P * expc * Lq ^ 2)
          + C₃ * K₅ * (P * expc * Lq ^ 2) + E₁ * K₂ * (P * expc * Lq ^ 2)
          + E₂ * 10 * (P * expc * Lq ^ 2) + E₃ * K₂ * (P * expc * Lq ^ 2)
          + 9 * (P * expc * Lq ^ 2) := by
      rw [hεEdef, hεZdef]
      linarith [b1, b2, b3, b4, b5, b6, b7]
    have heq : C₁ * K₅ * (P * expc * Lq ^ 2) + C₂ * 10 * (P * expc * Lq ^ 2)
          + C₃ * K₅ * (P * expc * Lq ^ 2) + E₁ * K₂ * (P * expc * Lq ^ 2)
          + E₂ * 10 * (P * expc * Lq ^ 2) + E₃ * K₂ * (P * expc * Lq ^ 2)
          + 9 * (P * expc * Lq ^ 2)
        = Cε * (P * expc * Lq ^ 2) := by rw [hCεdef]; ring
    calc ε = εE + εZ + εD := hεdef
      _ ≤ _ := hsum
      _ = Cε * (P * expc * Lq ^ 2) := heq
  -- ⟦the final repackaging⟧
  refine hprim.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [div_le_div_iff₀ hlogP hlogP]
  have hmass : (0 : ℝ) ≤ (ℰ.card : ℝ) := by positivity
  have hstep1 : ε * (ℰ.card : ℝ) ≤ Cε * (P * expc * Lq ^ 2) * (ℰ.card : ℝ) :=
    mul_le_mul_of_nonneg_right habs hmass
  have hgoal : 44 * Real.pi * P + ε * (ℰ.card : ℝ)
      ≤ (44 * Real.pi + Cε) * (P + (ℰ.card : ℝ) * P * expc * Lq ^ 2) := by
    have hexpand : (44 * Real.pi + Cε) * (P + (ℰ.card : ℝ) * P * expc * Lq ^ 2)
        = 44 * Real.pi * P + Cε * P + 44 * Real.pi * ((ℰ.card : ℝ) * P * expc * Lq ^ 2)
          + Cε * (P * expc * Lq ^ 2) * (ℰ.card : ℝ) := by ring
    have h1 : (0 : ℝ) ≤ Cε * P := by positivity
    have h2 : (0 : ℝ) ≤ 44 * Real.pi * ((ℰ.card : ℝ) * P * expc * Lq ^ 2) := by positivity
    rw [hexpand]
    linarith [hstep1]
  exact mul_le_mul_of_nonneg_right hgoal hlogP.le


/-! ## §7 — A2: THE SIEGEL FOLD, at the width the region actually needs

⟦THE FINDING, stated before the theorem because it is the wave's main adjudication.⟧

The rate chain's named hypothesis (`mmuChiRate_of_carve`, `lambdaChiSummatory_of_carve`,
`carve_of_half`, and the landed `twisted_rect_zero_free_split`'s `hcarve`) is the STRONG form

  `∀ q, ∀ χ ≠ 1, ∀ ρ, L(ρ,χ) = 0 → Im ρ = 0 → Re ρ < 1/2`.

**That form is NOT a Siegel statement and cannot be folded into an `∃ H₀`.**  It asserts that
`L(s,χ)` has no real zero anywhere in `[1/2, 1)` — a fragment of GRH (Chowla's conjecture for
real `χ`), open at every modulus, and no threshold in `H` or restriction of the `q`-range
weakens it: a hypothetical real zero at `β = 0.9` for one fixed small `q` refutes it for every
`H₀`.  Siegel's theorem bounds real zeros away from `1`, never below `1 − o(1)`.

**What IS foldable — and what every consumer actually needs — is the WIDTH form.**  Each
consumer uses the carve-out only through a tiny width: `carve_of_half` immediately weakens
`Re < 1/2` to `Re ρ ≤ 1 − vkShallowWidth (10⁻⁶) q H`, and the region uses it at
`1 − 10⁻⁸/D₄(5T+1)`.  Both widths are `≍ (log H)^{−3/4−o(1)}` at the port's parameters, and at
`q ≤ (log H)^{12}` Siegel with `ε = 1/16` beats them: `q^{−1/16} ≥ (log H)^{−3/4}`, with the
`(loglog)`-factors giving the margin and the ineffective `C(1/16)` absorbed by ONE existential.
`16 = 12/(3/4)` is the exact exponent arithmetic, and it is why the arc's `12` forces Siegel
(an effective Page-type bound gives `q^{−1/2}`, i.e. `(log H)^{−6}`, which loses by
`(log H)^{5.25}`).

So the honest deliverable is `siegel_real_carve` below: the real-zero carve at ANY width `W`
obeying the single gate `q^{1/16}·W ≤ K`, `K > 0` ineffective.  §8 consumes it to discharge
the region hypothesis of §6's socket outright.

⟦THE RESIDUAL, named exactly⟧ the rate chain's `hxi` is stated at `Re < 1/2` and therefore
still open; the repair is a ONE-LINE hypothesis weakening in the landed files (state `hxi` at
`ρ.re ≤ 1 − vkShallowWidth (1/10^6) q H` instead of `ρ.re < 1/2`, which is what
`mmuChiRate_nonprincipal` already consumes through `carve_of_half`), plus the `q ≤ (log x)^{12}`
gate that `MmuChiRate` already carries.  That is a statement change in landed files —
Fable/human tier, iron rule 5 — so this wave does not make it; it names it.

The two arms of the fold: non-real characters need NO Siegel (the effective classical region
`zero_free_region_all'` fires, its carve-out satisfied by the left disjunct), and real
characters go through the landed ε-quantified `Salt.SW.siegel_theorem` on the primitive
character. -/

/-- **A2 — THE SIEGEL FOLD (the real-zero carve at the width).**  There is an INEFFECTIVE
`K > 0` — the port's single ineffective constant, Siegel's — such that for every modulus,
every non-principal `χ` and every width `W > 0` with `q^{1/16}·W ≤ K`, no real zero of
`L(·,χ)` reaches `1 − W`.

Real characters: `Salt.SW.siegel_theorem` at `ε = 1/16` on `χ.primitiveCharacter` (the zero
transfers by `LFunction_eq_zero_iff_primitive`, legitimate since `Re ρ ≥ 1/2 > 0`), then
`conductor ≤ q`.  Non-real characters: `zero_free_region_all'` with its carve-out discharged by
the left disjunct — effective, no Siegel, at the cost of `log(2q) ≤ 32·q^{1/16}`
(`log_le_rpow_div`).  `Re ρ < 1/2` is trivial since the gate forces `W ≤ 1/2`. -/
theorem siegel_real_carve :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ W : ℝ, 0 < W → (q : ℝ) ^ ((1 : ℝ) / 16) * W ≤ K →
      ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 → ρ.re ≤ 1 - W := by
  obtain ⟨Cs, hCs0, hsieg⟩ := Salt.SW.siegel_theorem ((1 : ℝ) / 16) (by norm_num)
  obtain ⟨c₀, hc₀0, hc₀⟩ := Salt.SW.zero_free_region_all'
  refine ⟨min (min Cs (c₀ / 32)) (1 / 2), by positivity, ?_⟩
  intro q hq χ hχ1 W hW hgate ρ hρ0 hρim
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqe1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) := Real.one_le_rpow hq1 (by norm_num)
  have hqe0 : (0 : ℝ) < (q : ℝ) ^ ((1 : ℝ) / 16) := by linarith
  have hWK : W ≤ min (min Cs (c₀ / 32)) (1 / 2) := by
    refine le_trans ?_ hgate
    nlinarith [hW, hqe1]
  have hWhalf : W ≤ 1 / 2 := le_trans hWK (min_le_right _ _)
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
  · have hρeq : ρ = ((ρ.re : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im, hρim]
    have hβ1 : ρ.re < 1 := by
      by_contra hge
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by linarith [not_lt.mp hge]) hρ0
    by_cases hsq : χ.primitiveCharacter ^ 2 = 1
    · -- REAL character: THE one ineffective input
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have hprim : χ.primitiveCharacter.IsPrimitive := primitiveCharacter_isPrimitive χ
      have hχ1' : χ.primitiveCharacter ≠ 1 := fun h =>
        hχ1 (by rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one])
      have hzero1 : LFunction χ.primitiveCharacter ρ = 0 :=
        (Salt.SW.LFunction_eq_zero_iff_primitive χ (by linarith) (Or.inl hχ1)).mp hρ0
      have hzero1' : LFunction χ.primitiveCharacter ((ρ.re : ℝ) : ℂ) = 0 := by
        rw [← hρeq]; exact hzero1
      have hs := hsieg χ.conductor χ.primitiveCharacter hprim hsq hχ1' hzero1' hβ1
      have hcond1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
      have hcondq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (conductor_dvd_level χ)
      have hce : (χ.conductor : ℝ) ^ ((1 : ℝ) / 16) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) :=
        Real.rpow_le_rpow (by linarith) hcondq (by norm_num)
      have hce0 : (0 : ℝ) < (χ.conductor : ℝ) ^ ((1 : ℝ) / 16) :=
        Real.rpow_pos_of_pos (by linarith) _
      have hWCs : W ≤ Cs / (χ.conductor : ℝ) ^ ((1 : ℝ) / 16) := by
        rw [le_div_iff₀ hce0]
        have h1 : W * (χ.conductor : ℝ) ^ ((1 : ℝ) / 16) ≤ W * (q : ℝ) ^ ((1 : ℝ) / 16) :=
          mul_le_mul_of_nonneg_left hce hW.le
        have h2 : (q : ℝ) ^ ((1 : ℝ) / 16) * W ≤ Cs :=
          le_trans hgate (le_trans (min_le_left _ _) (min_le_left _ _))
        nlinarith [h1, h2]
      linarith [hs, hWCs]
    · -- NON-REAL character: the effective classical region, no Siegel
      have hcl : ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * 2) := by
        have h := hc₀ q χ hχ1 hρ0 hre (Or.inl hsq)
        rw [hρim, abs_zero, zero_add] at h
        exact h
      have hlog2q : (0 : ℝ) < Real.log ((q : ℝ) * 2) := by
        apply Real.log_pos; linarith
      have hlogle : Real.log ((q : ℝ) * 2) ≤ 32 * (q : ℝ) ^ ((1 : ℝ) / 16) := by
        have h := log_le_rpow_div (u := (q : ℝ) * 2) (ε := (1 : ℝ) / 16)
          (by linarith) (by norm_num)
        have hsplit : ((q : ℝ) * 2) ^ ((1 : ℝ) / 16)
            = (q : ℝ) ^ ((1 : ℝ) / 16) * (2 : ℝ) ^ ((1 : ℝ) / 16) :=
          Real.mul_rpow (by linarith) (by norm_num)
        have h2 : (2 : ℝ) ^ ((1 : ℝ) / 16) ≤ 2 := by
          have hh : (2 : ℝ) ^ ((1 : ℝ) / 16) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          rwa [Real.rpow_one] at hh
        rw [hsplit] at h
        have h3 : ((q : ℝ) ^ ((1 : ℝ) / 16) * (2 : ℝ) ^ ((1 : ℝ) / 16)) / ((1 : ℝ) / 16)
            = 16 * ((q : ℝ) ^ ((1 : ℝ) / 16) * (2 : ℝ) ^ ((1 : ℝ) / 16)) := by ring
        rw [h3] at h
        nlinarith [h, h2, hqe0]
      have hgate' : (q : ℝ) ^ ((1 : ℝ) / 16) * W ≤ c₀ / 32 :=
        le_trans hgate (le_trans (min_le_left _ _) (min_le_right _ _))
      have hWc : W ≤ c₀ / Real.log ((q : ℝ) * 2) := by
        rw [le_div_iff₀ hlog2q]
        have h1 : W * Real.log ((q : ℝ) * 2) ≤ W * (32 * (q : ℝ) ^ ((1 : ℝ) / 16)) :=
          mul_le_mul_of_nonneg_left hlogle hW.le
        nlinarith [h1, hgate']
      linarith [hcl, hWc]
  · linarith

/-! ## §8 — A2: the twisted zero-free rectangle WITHOUT the `Re < 1/2` carve-out

`twisted_rect_zero_free_split`'s conclusion with its `hcarve` hypothesis REPLACED by §7's
Siegel gate.  The re-derivation is cheap and legitimate because the landed split applies
`hcarve` to exactly ONE zero — the `ρ` it is handed — and `zero_free_region_all'` is itself
stated per-`ρ`: for `Im ρ ≠ 0` the carve-out's right disjunct is free, and the only genuinely
carved corner is the REAL zero, which is what §7 kills.  Above the height floor the VK arms
take no carve-out at all (a real zero has `|Im ρ| = 0`, so it never reaches that branch).
Everything else — the two VK arms, the `A`-absorption, the width comparisons — is the landed
proof re-run verbatim. -/

set_option maxHeartbeats 1600000 in
-- The re-derivation carries §7's fold in context; `linarith`'s preprocessing on the
-- `Real.rpow` gate needs headroom past the default.
/-- **A2's DELIVERABLE — the carve-free twisted rectangle.**  Same conclusion as
`twisted_rect_zero_free_split`, with the `(prim² ≠ 1 ∨ Im ρ ≠ 0)` hypothesis replaced by ONE
`q`-vs-`T` gate whose constant `Ks` carries Siegel's ineffectivity (§7) — the port's single
ineffective constant, and nothing else. -/
theorem twisted_rect_zero_free_siegel :
    ∃ Kq Ks : ℝ, 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ (A T : ℝ), 1 ≤ A →
      Real.exp (Real.exp 100) ≤ T →
      Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 →
      A + 7 ≤ Real.log (Real.log (5 * T + 1)) →
      Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
          ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
      (q : ℝ) ^ ((1 : ℝ) / 16)
          ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - (1 / 10 ^ 8)
          / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := Salt.SW.zero_free_region_all'
  obtain ⟨Ks, hKs0, hsg⟩ := siegel_real_carve
  refine ⟨1 / (10 ^ 8 * c₀), 10 ^ 8 * Ks, by positivity, by positivity, ?_⟩
  intro q hNe ψ hψ1 A T hA1 hTfloor hAq hAabs hKq hSg ρ hρ0 hρim
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
    · by_cases him : ρ.im = 0
      · -- THE REAL-ZERO CORNER: §7's Siegel arm gives the conclusion outright
        have hW0 : (0 : ℝ) < (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) :=
          div_pos (by norm_num) hD4pos
        have hgate : (q : ℝ) ^ ((1 : ℝ) / 16)
            * ((1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))) ≤ Ks := by
          have heq : (q : ℝ) ^ ((1 : ℝ) / 16)
              * ((1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)))
              = ((q : ℝ) ^ ((1 : ℝ) / 16) * (1 / 10 ^ 8 : ℝ))
                / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by ring
          rw [heq, div_le_iff₀ hD4pos]
          nlinarith [hSg, hD4pos, hKs0]
        exact hsg q ψ hψ1 _ hW0 hgate ρ hρ0 him
      · have hcv : ψ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := Or.inr him
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


/-! ## §9 — THE COMPOSITION: the `(χ,t)`-pair socket at the GATES ONLY

A1's socket (§6) with its region hypothesis DISCHARGED by A2 (§8).  What remains in front of
the socket's conclusion is four `q`-vs-`T` gates and nothing else:

* **G1** the twisted edge's `q`-scale gate (`TwistedEdge.lean`'s D3 deviation);
* **G2** the region's `A`-absorption gate at `A := 1 + log(20000(Cq+8104))/100` — the
  instantiation that makes stone C's `hAq` free;
* **G3** the region's below-floor comparison (constant `Kq`, effective);
* **G4** the Siegel gate (constant `Ks`, the port's ONE ineffective constant).

At the port's parameters (`q ≤ (log H)^{12}`, `loglog H ∈ [173, 241]`, `T ≍ X`) all four hold
with the margins stone C's §4 docstring records (G1/G2 read `≈ 31 ≤ loglog X ≈ 200`; G3 has
~30 orders; G4 reads `(log H)^{3/4} ≤ Ks·(log X)^{3/4}(loglog X)^4`, i.e. the exponent
arithmetic `16 = 12/(3/4)` with the whole `(loglog)^4` as margin).

⟦THE ONE HYPOTHESIS THAT REMAINS, and why it is a one-line exposure⟧ the theorem takes the
twisted edge price at the LITERAL width `1/10⁸`.  `TwistedEdge.twisted_edge_price_strip`
proves exactly that (`refine ⟨1 / 10 ^ 8, …⟩`, TwistedEdge.lean:895) and
`twisted_window_price_gated_holds` passes the same constant through — but both package it
behind `∃ c_vk`, and the region (§8, like stone C's split) delivers its width at the literal
`1/10⁸`, so the kernel cannot see that the two match.  Exposing the numeral in either `∃`
(or adding `c_vk ≤ 1/10^8` to the edge's conclusion) closes this composition
unconditionally; it is a statement change in a landed file, hence Fable/human tier. -/

/-- **THE PORT'S `(χ,t)`-PAIR ROW, at the gates only.**  `USetChi.HalaszPrimesChi`'s
conclusion from the twisted edge price at the literal width `1/10⁸`, with the region
discharged by A2's carve-free rectangle.  Four in-statement gates (see the section
docstring); no carve-out, no region hypothesis, no `φ(q)` on the diagonal. -/
theorem halasz_primes_chi_pair_of_gates {C₁ C₂ C₃ T₀e : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hT₀e : Real.exp (Real.exp 100) ≤ T₀e)
    (hprice : TwistedWindowPriceGated (1 / 10 ^ 8) C₁ C₂ C₃ T₀e) :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hT₀, hgated⟩ :=
    halaszPrimesChiGated_of_price (by norm_num) hC₁ hC₂ hC₃ hT₀e hprice
  obtain ⟨Kq, Ks, hKq, hKs, hreg⟩ := twisted_rect_zero_free_siegel
  refine ⟨C, c, max T₀ T₀e, Kq, Ks, hC, hc, le_trans hT₀ (le_max_left _ _), hKq, hKs, ?_⟩
  intro q hq T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTfloor : Real.exp (Real.exp 100) ≤ T := le_trans hT₀e (le_trans (le_max_right _ _) hT)
  -- the `A`-instantiation that makes stone C's own `hAq` free
  set A : ℝ := 1 + Real.log (20000 * (vkStripConst q + 8104)) / 100 with hAdef
  have hCq1 : (1 : ℝ) ≤ vkStripConst q := one_le_vkStripConst
  have hlogA0 : (0 : ℝ) ≤ Real.log (20000 * (vkStripConst q + 8104)) :=
    Real.log_nonneg (by linarith)
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hAq : Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 := by
    rw [hAdef]; linarith
  have hAabs : A + 7 ≤ Real.log (Real.log (5 * T + 1)) := by rw [hAdef]; linarith [hG2]
  exact hgated q T P hTT₀ hP hPT10 hG1
    (fun ψ hψ1 => hreg q ψ hψ1 A T hA1 hTfloor hAq hAabs hG3 hG4) ℰ hws hsub S hS a

end Salt.MR
