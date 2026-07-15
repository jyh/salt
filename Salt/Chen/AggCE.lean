/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PDiag

/-!
# AggCE — the `blockConvErrW` conversion-error crumb (node HCE)

Design: `docs/blueprints/flags.md`, the `2026-07-14 GLU-2 re-run → ★ CATCH #65` entry,
**Finding 5 (hCE route)**, and the `2026-07-14 fin8b` entry (the four-node re-scope:
`SYMLOW ∥ HSUM ∥ HCE ∥ HDIAG`).  This file discharges **HCE**: the estimate of the `hCE`
hypothesis of `hBVblocksW_discharge'` (`Salt/Chen/PDiag.lean`).

## The `hCE` hypothesis (verbatim, from `hBVblocksW_discharge'`)

```
(hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
    if (d : ℝ) < QR * Dlev then blockConvErrW x z y ε₀ j Q d else 0) ≤ RCE)
```

with (`Salt/Chen/SwitchW.lean:602`)

```
blockConvErrW x z y ε₀ j Q d = nuChen (Q * d) * blockNonUnitCountM x z y ε₀ j (Q * d)
```

and (`Salt/Chen/SwitchW.lean:489`)

```
blockNonUnitCountM x z y ε₀ j m
  = #{ t ∈ tripleSet x z y : blockIdx z ε₀ t.1 = j ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod m) }.
```

So the crumb weights, by `ν(Q·d) = 1/φ(Q·d)`, the count of block-`j` admissible triples whose
product `prod3 t = p₁·p₂·p₃` is **not** coprime to `Q·d`.

## The finding-5 mechanism (formalized here)

A triple `t = (p₁, p₂, p₃) ∈ tripleSet` with `prod3 t` non-coprime to `Q·d` shares a prime
`p` with `Q·d`.  Since `p | p₁p₂p₃` and each `pᵢ` is prime, `p ∈ {p₁, p₂, p₃}`.  Because
`p | Q·d`, `p` divides `Q` (so `p < w' ≤ z ≤ p₁ ≤ y`) or `p | d | Ps` (so `p < y`); either
way `p < y < p₂ ≤ p₃`, forcing `p = p₁`.  And `p₁ ≥ z ≥ w' >` every prime of `Q` rules out
`p₁ | Q`, so `p₁ | d` — **`nonunit_forces_fst_dvd`**.

Summing the crumb over `d | Ps` and (after collapsing the single operating-point block
`ε₀ := x`) over the triples then gives, with `ν(Q·d) = ν(Q)·ν(d)` and the divisor reindex
`Σ_{d | Ps, p | d} ν(d) ≤ ν(p)·Σ_{d' | Ps} ν(d')` (**`nuChen_sum_dvd_le`**) and
`ν(p₁) = 1/(p₁−1) ≤ 1/(z−1)`:

```
Σ_j Σ_d [d < QR·Dlev] blockConvErrW  ≤  ν(Q) · (Σ_{d | Ps} ν(d)) · tripleSum x z y / (z − 1)
```

(**`hCE_at_op`**).  The honest scale: `Σ_{d | Ps} ν(d) ≤ (1+ε)·log y / log(w0R ε)` (a landed
bound, `nuChen_sum_divisors_le`) is `polylog`, `tripleSum x z y` is the main term `≍ x·polylog`,
and `ν(Q) ≤ 1`, so the whole crumb is `≍ x·polylog / z`.  At the operating cutoff
`z ≍ x^{1/8}` this is `x^{7/8}·polylog ≪ x/(log x)^{11}` — the finding-5 `x^{1/8}` room.

No `sorry`, no `native_decide`, no new axioms; NEW file, no landed file touched, `All.lean`
NOT wired.
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the finding-5 forcing lemma -/

/-- **`nonunit_forces_fst_dvd` — the finding-5 prime forcing.**  A block triple whose product
is non-coprime to `Q·d` has its narrow prime `p₁ = t.1` dividing `d`.  The shared prime cannot
be `p₂` or `p₃` (both `> y >` every prime of `Q` and of `Ps ⊇ d`), so it is `p₁`; and
`p₁ ≥ z ≥ w' >` every prime of `Q` forbids `p₁ | Q`, leaving `p₁ | d`. -/
theorem nonunit_forces_fst_dvd {x z y Q Ps w' d : ℕ}
    (hQ1 : 1 ≤ Q)
    (hQfac : ∀ p ∈ Q.primeFactors, p < w') (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hw'z : w' ≤ z) (hd : d ∈ Nat.divisors Ps)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ tripleSet x z y)
    (hnu : ¬ IsUnit ((prod3 t : ℕ) : ZMod (Q * d))) :
    t.1 ∣ d := by
  -- unpack the divisor and the triple
  obtain ⟨hdPs, hPs0⟩ := Nat.mem_divisors.mp hd
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  haveI : NeZero (Q * d) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, hz_le, _, hy21, h2122, hp1, hp21, hp22, _, _⟩ := ht
  -- ¬ IsUnit  ⇒  ¬ Coprime  ⇒  a shared prime p
  have hnc : ¬ Nat.Coprime (prod3 t) (Q * d) := fun hc =>
    hnu ((ZMod.isUnit_iff_coprime (prod3 t) (Q * d)).mpr hc)
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (show Nat.gcd (prod3 t) (Q * d) ≠ 1 from hnc)
  have hp_pt : p ∣ prod3 t := hpg.trans (Nat.gcd_dvd_left _ _)
  have hp_Qd : p ∣ Q * d := hpg.trans (Nat.gcd_dvd_right _ _)
  -- p | Q ∨ p | d, and in either case p ≤ y
  have hpQd : p ∣ Q ∨ p ∣ d := hp.dvd_mul.mp hp_Qd
  have hp_le_y : p ≤ y := by
    rcases hpQd with hQ | hdd
    · have : p ∈ Q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hQ, by omega⟩
      have := hQfac p this
      omega
    · have : p ∈ Ps.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdd.trans hdPs, hPs0⟩
      have := hPy p this
      omega
  -- p divides one of the three primes; the size p ≤ y < p₂ ≤ p₃ rules out p₂, p₃
  rw [prod3] at hp_pt
  have hp_eq_t1 : p = t.1 := by
    rcases (hp.dvd_mul.mp hp_pt) with h12 | h3
    · rcases (hp.dvd_mul.mp h12) with h1 | h2
      · exact (Nat.prime_dvd_prime_iff_eq hp hp1).mp h1
      · have := (Nat.prime_dvd_prime_iff_eq hp hp21).mp h2
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hp hp22).mp h3
      omega
  -- p = p₁ ≥ z ≥ w' >  every prime of Q, so ¬ p | Q; hence p | d, i.e. t.1 | d
  rcases hpQd with hQ | hdd
  · exfalso
    have : p ∈ Q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hQ, by omega⟩
    have hpw' := hQfac p this
    omega
  · rw [hp_eq_t1] at hdd
    exact hdd

/-! ## Part B — the divisor reindex `Σ_{d | Ps, p | d} ν(d) ≤ ν(p)·Σ_{d' | Ps} ν(d')` -/

/-- **`nuChen_sum_dvd_le` — the finding-5 divisor reindex.**  For `Ps` squarefree and `p`
prime, the `ν`-mass over the divisors of `Ps` that are multiples of `p` factors a single
`ν(p)` out of the full divisor mass (via `d ↦ d/p`, a bijection onto a subset of the
divisors, with `ν(d) = ν(p)·ν(d/p)` by squarefreeness). -/
theorem nuChen_sum_dvd_le {Ps : ℕ} (hPs : Squarefree Ps) {p : ℕ} (hp : p.Prime) :
    ∑ d ∈ (Nat.divisors Ps).filter (fun d => p ∣ d), nuChen d
      ≤ nuChen p * ∑ d ∈ Nat.divisors Ps, nuChen d := by
  classical
  set F := (Nat.divisors Ps).filter (fun d => p ∣ d) with hF
  have hnn : ∀ d : ℕ, 0 ≤ nuChen d := fun d => by rw [nuChen_apply]; positivity
  -- (1) per `d ∈ F`: `ν(d) = ν(p)·ν(d/p)`
  have hstep : ∀ d ∈ F, nuChen d = nuChen p * nuChen (d / p) := by
    intro d hdF
    rw [hF, Finset.mem_filter] at hdF
    obtain ⟨hd, hpd⟩ := hdF
    have hdPs : d ∣ Ps := (Nat.mem_divisors.mp hd).1
    have hdsf : Squarefree d := hPs.squarefree_of_dvd hdPs
    have hpe : p * (d / p) = d := Nat.mul_div_cancel' hpd
    have hpnd : ¬ p ∣ (d / p) := by
      intro hdvd
      have hsq : p * p ∣ d := by rw [← hpe]; exact mul_dvd_mul_left p hdvd
      have hp1 := Nat.isUnit_iff.mp (hdsf p hsq)
      have := hp.two_le
      omega
    have hcop : Nat.Coprime p (d / p) := (hp.coprime_iff_not_dvd).mpr hpnd
    conv_lhs => rw [← hpe]
    exact nuChen_mult.map_mul_of_coprime hcop
  -- (2) the map `d ↦ d/p` is injective on `F` and lands in `Ps.divisors`
  have hinj : ∀ d₁ ∈ F, ∀ d₂ ∈ F, d₁ / p = d₂ / p → d₁ = d₂ := by
    intro d₁ h₁ d₂ h₂ heq
    rw [hF, Finset.mem_filter] at h₁ h₂
    rw [← Nat.mul_div_cancel' h₁.2, ← Nat.mul_div_cancel' h₂.2, heq]
  have himg : F.image (fun d => d / p) ⊆ Nat.divisors Ps := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨d, hdF, rfl⟩ := he
    rw [hF, Finset.mem_filter] at hdF
    obtain ⟨hd, hpd⟩ := hdF
    obtain ⟨hdPs, hPs0⟩ := Nat.mem_divisors.mp hd
    have hdvd : d / p ∣ Ps := (Nat.div_dvd_of_dvd hpd).trans hdPs
    exact Nat.mem_divisors.mpr ⟨hdvd, hPs0⟩
  -- (3) assemble
  calc ∑ d ∈ F, nuChen d
      = ∑ d ∈ F, nuChen p * nuChen (d / p) := Finset.sum_congr rfl hstep
    _ = nuChen p * ∑ d ∈ F, nuChen (d / p) := by rw [Finset.mul_sum]
    _ = nuChen p * ∑ e ∈ F.image (fun d => d / p), nuChen e := by
          rw [Finset.sum_image hinj]
    _ ≤ nuChen p * ∑ e ∈ Nat.divisors Ps, nuChen e :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg himg (fun e _ _ => hnn e)) (hnn p)

/-! ## Part C — the operating point: `ε₀ := x` collapses the block sum -/

/-- **`maxBlock_op_eq_zero`.**  At the operating scale `ε₀ := x` the narrow blocks collapse to
a single block `j = 0`: `Real.log(x/z)/Real.log(1+x) < 1` since `x/z ≤ x < 1+x` (Finding 4). -/
theorem maxBlock_op_eq_zero {x z : ℕ} (hz1 : 1 ≤ z) (hx2 : 2 ≤ x) :
    maxBlock x z (x : ℝ) = 0 := by
  unfold maxBlock blockIdx
  rw [Nat.floor_eq_zero]
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  have hxpos : (0 : ℝ) < x := by linarith
  have hden : 0 < Real.log (1 + (x : ℝ)) := Real.log_pos (by linarith)
  rw [div_lt_one hden]
  have h1 : Real.log ((x : ℝ) / z) ≤ Real.log x :=
    Real.log_le_log (div_pos hxpos (by linarith)) (div_le_self hxpos.le hzR)
  have h2 : Real.log (x : ℝ) < Real.log (1 + x) := Real.log_lt_log hxpos (by linarith)
  linarith

/-! ## Part D — the crumb estimate at the operating point -/

/-- **`hCE_at_op` — the `blockConvErrW` conversion-error crumb (node HCE).**  At the operating
point `ε₀ := x` (single block, `maxBlock_op_eq_zero`) the `hCE` double sum of
`hBVblocksW_discharge'` is bounded by the finding-5 product

  `ν(Q) · (Σ_{d | Ps} ν(d)) · tripleSum x z y / (z − 1)`.

Route: `nonunit_forces_fst_dvd` caps each `d`-crumb by `ν(Q)·ν(d)·#{t : p₁ | d}`; the double
sum is reindexed (Fubini over triples, then `nuChen_sum_dvd_le` per triple) to
`ν(Q)·(Σ ν(d'))·Σ_t ν(p₁)`, and `ν(p₁) = 1/(p₁−1) ≤ 1/(z−1)` gives the `tripleSum/(z−1)`
factor.  The `QR·Dlev` cutoff is discarded (every crumb is `≥ 0`), so the bound is uniform in
`QR, Dlev` — in particular it holds at the operating cutoff `QR = 1`, `Dlev = opDlev x`.

Honest scale: `Σ ν(d') ≤ (1+ε)·log y / log(w0R ε)` (`nuChen_sum_divisors_le`) is polylog,
`tripleSum x z y ≍ x·polylog` is the main term, `ν(Q) ≤ 1`; at `z ≍ x^{1/8}` the whole crumb
is `x^{7/8}·polylog ≪ x/(log x)^{11}`. -/
theorem hCE_at_op (x z y Q Ps w' : ℕ) (QR : ℝ) (Dlev : ℕ)
    (hPs : Squarefree Ps) (hz2 : 2 ≤ z) (hx2 : 2 ≤ x) (hQ1 : 1 ≤ Q)
    (hQPs : Nat.Coprime Q Ps) (hQfac : ∀ p ∈ Q.primeFactors, p < w')
    (hPy : ∀ p ∈ Ps.primeFactors, p < y) (hw'z : w' ≤ z) :
    (∑ j ∈ Finset.range (maxBlock x z (x : ℝ) + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then blockConvErrW x z y (x : ℝ) j Q d else 0)
      ≤ nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * tripleSum x z y / ((z : ℝ) - 1) := by
  classical
  have hnn : ∀ d : ℕ, 0 ≤ nuChen d := fun d => by rw [nuChen_apply]; positivity
  have hconv_nn : ∀ d, 0 ≤ blockConvErrW x z y (x : ℝ) 0 Q d := by
    intro d
    unfold blockConvErrW blockNonUnitCountM
    apply mul_nonneg
    · rw [nuChen_apply]; positivity
    · positivity
  have hnu_t1 : ∀ t ∈ tripleSet x z y, nuChen t.1 ≤ 1 / ((z : ℝ) - 1) := by
    intro t ht
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, hz_le, _, _, _, hp1, _, _, _, _⟩ := ht
    rw [nuChen_prime hp1]
    have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz2
    have ht1R : (z : ℝ) ≤ t.1 := by exact_mod_cast hz_le
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  -- per `d ∈ Ps.divisors`: the crumb ≤ ν(Q)·ν(d)·#{t : p₁ | d}
  have hbcd : ∀ d ∈ Nat.divisors Ps,
      blockConvErrW x z y (x : ℝ) 0 Q d
        ≤ nuChen Q * nuChen d * (((tripleSet x z y).filter (fun t => t.1 ∣ d)).card : ℝ) := by
    intro d hd
    have hcopQd : Nat.Coprime Q d := hQPs.coprime_dvd_right (Nat.mem_divisors.mp hd).1
    have hmul : nuChen (Q * d) = nuChen Q * nuChen d := nuChen_mult.map_mul_of_coprime hcopQd
    unfold blockConvErrW blockNonUnitCountM
    rw [hmul]
    have hsub : (tripleSet x z y).filter
          (fun t => blockIdx z (x : ℝ) t.1 = 0 ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod (Q * d)))
        ⊆ (tripleSet x z y).filter (fun t => t.1 ∣ d) := by
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, nonunit_forces_fst_dvd hQ1 hQfac hPy hw'z hd ht.1 ht.2.2⟩
    have hcard : (((tripleSet x z y).filter
          (fun t => blockIdx z (x : ℝ) t.1 = 0 ∧ ¬ IsUnit ((prod3 t : ℕ) : ZMod (Q * d)))).card : ℝ)
        ≤ (((tripleSet x z y).filter (fun t => t.1 ∣ d)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact mul_le_mul_of_nonneg_left hcard (mul_nonneg (hnn Q) (hnn d))
  -- the cardinality-as-sum identity
  have hBd : ∀ d : ℕ, (((tripleSet x z y).filter (fun t => t.1 ∣ d)).card : ℝ)
      = ∑ t ∈ tripleSet x z y, (if t.1 ∣ d then (1 : ℝ) else 0) := by
    intro d
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun t _ => by by_cases h : t.1 ∣ d <;> simp [h])
  -- collapse the single operating-point block, then chain the finding-5 estimate
  rw [maxBlock_op_eq_zero (by omega) hx2, zero_add, Finset.sum_range_one]
  calc (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < QR * Dlev
          then blockConvErrW x z y (x : ℝ) 0 Q d else 0)
      ≤ ∑ d ∈ Nat.divisors Ps, blockConvErrW x z y (x : ℝ) 0 Q d := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        split_ifs with h
        · exact le_refl _
        · exact hconv_nn d
    _ ≤ ∑ d ∈ Nat.divisors Ps,
          nuChen Q * nuChen d * (((tripleSet x z y).filter (fun t => t.1 ∣ d)).card : ℝ) :=
        Finset.sum_le_sum hbcd
    _ = nuChen Q * ∑ d ∈ Nat.divisors Ps,
          ∑ t ∈ tripleSet x z y, (if t.1 ∣ d then nuChen d else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [hBd d, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by by_cases h : t.1 ∣ d <;> simp [h])
    _ = nuChen Q * ∑ t ∈ tripleSet x z y,
          ∑ d ∈ (Nat.divisors Ps).filter (fun d => t.1 ∣ d), nuChen d := by
        rw [Finset.sum_comm]
        refine congrArg _ (Finset.sum_congr rfl (fun t _ => ?_))
        rw [Finset.sum_filter]
    _ ≤ nuChen Q * ∑ t ∈ tripleSet x z y, nuChen t.1 * (∑ d ∈ Nat.divisors Ps, nuChen d) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t ht => ?_)) (hnn Q)
        rw [tripleSet, Finset.mem_filter] at ht
        obtain ⟨_, _, _, _, _, hp1, _, _, _, _⟩ := ht
        exact nuChen_sum_dvd_le hPs hp1
    _ = nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * (∑ t ∈ tripleSet x z y, nuChen t.1) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * (tripleSum x z y / ((z : ℝ) - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (hnn Q) (Finset.sum_nonneg (fun d _ => hnn d)))
        calc ∑ t ∈ tripleSet x z y, nuChen t.1
            ≤ ∑ _t ∈ tripleSet x z y, (1 / ((z : ℝ) - 1)) :=
              Finset.sum_le_sum (fun t ht => hnu_t1 t ht)
          _ = ((tripleSet x z y).card : ℝ) * (1 / ((z : ℝ) - 1)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = tripleSum x z y / ((z : ℝ) - 1) := by rw [tripleSum_eq_card]; ring
    _ = nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * tripleSum x z y / ((z : ℝ) - 1) := by
        ring

/-! ## Part E — the slot match: `hCE_at_op` fills the `hCE` position of the consumer

`hBVblocksW_of_generalBV` (`Salt/Chen/SwitchW.lean`) is the direct consumer of the `hCE`
hypothesis — `hBVblocksW_discharge'` threads `hCE` into it unchanged.  The example below
compiles `hCE_at_op` character-for-character into that `hCE` slot (at `ε₀ := x`, with
`RCE :=` the finding-5 product inferred), leaving only the honest-discrepancy row `hHD`
(node HSUM/HDIAG) and the numeric closure `hNum` (node fin8c) as the surviving inputs. -/

section SlotMatch

/-- **The HCE slot match.**  `hCE_at_op` lands in the `hCE` argument of `hBVblocksW_of_generalBV`
(the ultimate `hCE` consumer), yielding the W block-remainder close at the operating point. -/
example (x z y Q a Ps w' : ℕ) (QR : ℝ) (Dlev : ℕ)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hQPs : Nat.Coprime Q Ps)
    (hz2 : 2 ≤ z) (hx2 : 2 ≤ x) (hQ1 : 1 ≤ Q)
    (hQfac : ∀ p ∈ Q.primeFactors, p < w') (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hw'z : w' ≤ z) (RHD : ℝ)
    (hHD : (∑ j ∈ Finset.range (maxBlock x z (x : ℝ) + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then |blockHonestDiscW x z y (x : ℝ) j Q a d| else 0) ≤ RHD)
    (hNum : RHD + nuChen Q * (∑ d ∈ Nat.divisors Ps, nuChen d) * tripleSum x z y / ((z : ℝ) - 1)
        ≤ (x : ℝ) / (Real.log x) ^ 10) :
    (∑ j ∈ Finset.range (maxBlock x z (x : ℝ) + 1),
        rosserRemainder (blockSwitchSieveW x z y (x : ℝ) j Q a Ps hPs hPodd) (QR * Dlev))
      ≤ (x : ℝ) / (Real.log x) ^ 10 :=
  hBVblocksW_of_generalBV x z y (x : ℝ) Q a Ps hPs hPodd hQPs QR Dlev hHD
    (hCE_at_op x z y Q Ps w' QR Dlev hPs hz2 hx2 hQ1 hQPs hQfac hPy hw'z)
    hNum

end SlotMatch

end Salt.Chen
