/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.PpFold
import Salt.Maynard.PpRootGeneral
import Salt.Maynard.PpSums
import Salt.Maynard.GehPp

/-!
# The three-regime `k ≥ 3` prime-power tail (node PP3-ASSEMBLY)

Discharges `PpFold`'s named residual — the summed sequence discrepancy of the
cube-and-higher prime-power correction `pp3Term` — and, as the stretch prize,
`ppLevel_holds : PpLevel (3999/4000)`, closing the GEH door's `PpLevel`
obligation.

## The crossover (constant form)

The design (`docs/exploration/s3-a3-design.md`, PP3-DESIGN) suggests the sharp
crossover `k* = ⌈√(log x / loglog x)⌉`.  Because `θ = 3999/4000` sits a full
`1/4000` below `1`, a **constant** crossover `k* = 8000` already closes both
regimes — no loglog machinery is needed:

* **`3 ≤ k ≤ 8000`** (root-count regime): the per-class count carries the `/q`
  saving via `card_primePow_class_le` (general-`k` mirror of
  `card_primeSq_class_le`), summed over `q` with `PpSums`.  The freight is
  `x^{1/3}·(1+log x)^{8000} + x^θ·(1+log x)^{8000}` = poly-below-`x` × polylog.
* **`k > 8000`** (crude regime): drop the congruence; per class the mass is
  `∑_{k>8000} x^{1/k} ≤ (log₂ x)·x^{1/8000}`, `q`-independent, so summing over
  the `≤ x^θ` moduli gives `x^{7999/8000}·log₂ x`.

Both are `≤ x/(log x)^A` eventually (`eventually_poly_beats_polylog`); the
small-`x` corner folds into the constant via the crude ℓ¹ bound.
-/

open Finset

namespace Salt.Maynard

/-! ## §1  The general-`k` root-residue count -/

/-- **Units bridge: residue-form `k`-th-root count.**  For `q ≥ 1`, `k ≥ 1` and a
reduced residue `a` (`Coprime a q`, `a < q`), the number of residues `r ∈ [0,q)`
coprime to `q` with `r^k ≡ a (mod q)` is `≤ 2k·k^{ω(q)}`.  The map
`r ↦ ZMod.unitOfCoprime r` injects the residue set into the `(ZMod q)ˣ` `k`-th-root
fiber of `â`, whose card is the landed `card_pow_eq_units_le_general`. -/
lemma card_pow_residues_le {q : ℕ} (hq : 1 ≤ q) (k : ℕ) (hk : 1 ≤ k) {a : ℕ}
    (ha : Nat.Coprime a q) (ha2 : a < q) :
    (((Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ k % q = a)).card : ℝ)
      ≤ 2 * k * k ^ q.primeFactors.card := by
  classical
  rcases lt_or_ge q 2 with hq1 | hq2
  · -- `q = 1`: the residue set sits inside `range 1`, so has ≤ 1 element.
    interval_cases q
    · have hle : (((Finset.range 1).filter
          (fun r => Nat.Coprime r 1 ∧ r ^ k % 1 = a)).card : ℝ) ≤ 1 := by
        calc (((Finset.range 1).filter (fun r => Nat.Coprime r 1 ∧ r ^ k % 1 = a)).card : ℝ)
            ≤ ((Finset.range 1).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
          _ = 1 := by rw [Finset.card_range]; norm_num
      have hone : (1 : ℝ) ≤ 2 * (k : ℝ) * (k : ℝ) ^ (1 : ℕ).primeFactors.card := by
        rw [Nat.primeFactors_one, Finset.card_empty, pow_zero, mul_one]
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        nlinarith [hk1]
      exact hle.trans hone
  haveI : NeZero q := ⟨by omega⟩
  set â : (ZMod q)ˣ := ZMod.unitOfCoprime a ha with hâ
  set f : ℕ → (ZMod q)ˣ :=
    fun r => if h : Nat.Coprime r q then ZMod.unitOfCoprime r h else 1 with hf
  have hmaps : ∀ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ k % q = a),
      f r ∈ Finset.univ.filter (fun u : (ZMod q)ˣ => u ^ k = â) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨_hrq, hcop, hrk⟩ := hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hf]
    rw [dif_pos hcop]
    apply Units.ext
    have hpow : ((ZMod.unitOfCoprime r hcop ^ k : (ZMod q)ˣ) : ZMod q) = (r : ZMod q) ^ k := by
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
    rw [hpow, hâ, ZMod.coe_unitOfCoprime, ← Nat.cast_pow]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by rw [hrk, Nat.mod_eq_of_lt ha2])
  have hinj : Set.InjOn f
      ↑((Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ k % q = a)) := by
    intro r hr r' hr' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hr hr'
    obtain ⟨hrq, hcop, _⟩ := hr
    obtain ⟨hrq', hcop', _⟩ := hr'
    simp only [hf] at heq
    rw [dif_pos hcop, dif_pos hcop'] at heq
    have hcast : (r : ZMod q) = (r' : ZMod q) := by
      rw [← ZMod.coe_unitOfCoprime r hcop, ← ZMod.coe_unitOfCoprime r' hcop', heq]
    have hmod := (ZMod.natCast_eq_natCast_iff' r r' q).mp hcast
    rwa [Nat.mod_eq_of_lt hrq, Nat.mod_eq_of_lt hrq'] at hmod
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  have hunits := card_pow_eq_units_le_general q hq2 k hk â
  calc (((Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ k % q = a)).card : ℝ)
      ≤ ((Finset.univ.filter (fun u : (ZMod q)ˣ => u ^ k = â)).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ 2 * (k : ℝ) * (k : ℝ) ^ q.primeFactors.card := by exact_mod_cast hunits

/-! ## §2  The prime `k`-th-power residue-class count -/

/-- **The prime-power residue-class count.**  For `q ≥ 1`, `k ≥ 1` and a reduced
residue `a`, the number of primes `p` with `p^k ≤ x` and `p^k ≡ a (mod q)` is
`≤ 2k·k^{ω(q)}·(x^{1/k}/q + 1)`.  General-`k` mirror of `card_primeSq_class_le`:
fibers `{p : p^k ≡ a}` over the `≤ 2k·k^{ω}` root residues (`card_pow_residues_le`),
each fiber contributing `≤ x^{1/k}/q + 1` primes (`card_ap_le`, with `p ≤ ⌊x^{1/k}⌋`
from `p^k ≤ x`). -/
lemma card_primePow_class_le {x k q a : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (ha : Nat.Coprime a q) (ha2 : a < q) :
    (((Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ^ k ≤ x ∧ p ^ k % q = a)).card : ℝ)
      ≤ 2 * k * k ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / q + 1) := by
  classical
  set M : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊ with hM
  set R := (Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ k % q = a) with hR
  set P := (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ^ k ≤ x ∧ p ^ k % q = a) with hP
  have hq0 : 0 < q := hq
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkR.ne'
  -- `p^k ≤ x ⟹ p ≤ M = ⌊x^{1/k}⌋`.
  have hpM : ∀ p : ℕ, p ^ k ≤ x → p ≤ M := by
    intro p hpk
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hpkR : (p : ℝ) ^ k ≤ (x : ℝ) := by exact_mod_cast hpk
    have hstep : ((p : ℝ) ^ k) ^ ((1 : ℝ) / (k : ℝ)) = (p : ℝ) := by
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp0, mul_one_div, div_self hkne,
        Real.rpow_one]
    have hple : (p : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
      calc (p : ℝ) = ((p : ℝ) ^ k) ^ ((1 : ℝ) / (k : ℝ)) := hstep.symm
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := Real.rpow_le_rpow (by positivity) hpkR (by positivity)
    exact Nat.le_floor hple
  have hmaps : ∀ p ∈ P, p % q ∈ R := by
    intro p hp
    simp only [hP, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨_hpI, _hpprime, _hpkle, hpmod⟩ := hp
    have hcop2 : Nat.Coprime (p ^ k) q := by
      have h := ha
      unfold Nat.Coprime at h ⊢
      rw [Nat.gcd_comm, Nat.gcd_rec, hpmod]; exact h
    have hcopp : Nat.Coprime p q :=
      Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by omega)) hcop2
    have hcoppmod : Nat.Coprime (p % q) q := by
      unfold Nat.Coprime
      rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hcopp
    simp only [hR, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hq0, hcoppmod, by rw [← Nat.pow_mod]; exact hpmod⟩
  have hcard : P.card = ∑ r ∈ R, (P.filter (fun p => p % q = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ r ∈ R, ((P.filter (fun p => p % q = r)).card : ℝ)
      ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / q + 1 := by
    intro r _
    have hsub : P.filter (fun p => p % q = r)
        ⊆ (Finset.Icc 1 M).filter (fun n => n % q = r) := by
      intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1.1, hpM p hp.1.2.2.1⟩, hp.2⟩
    have hle1 : ((P.filter (fun p => p % q = r)).card : ℝ) ≤ (M : ℝ) / q + 1 :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) (card_ap_le hq r)
    have hMle : (M : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := Nat.floor_le (by positivity)
    have hmono : (M : ℝ) / q ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / q := by gcongr
    linarith [hle1, hmono]
  have hRcard : (R.card : ℝ) ≤ 2 * k * k ^ q.primeFactors.card :=
    card_pow_residues_le hq k hk ha ha2
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / q + 1 := by positivity
  calc (P.card : ℝ)
      = ∑ r ∈ R, ((P.filter (fun p => p % q = r)).card : ℝ) := by rw [hcard, Nat.cast_sum]
    _ ≤ ∑ _r ∈ R, ((x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / q + 1) := Finset.sum_le_sum hbound
    _ = (R.card : ℝ) * ((x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / q + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * k * k ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / q + 1) :=
        mul_le_mul_of_nonneg_right hRcard hnn

/-! ## §3  The `pp3Term` value on prime powers and the pointwise decomposition -/

/-- On a proper prime power `p^j` (`j ≥ 2`), `ppTerm = 1/j`. -/
lemma ppTerm_prime_pow_val {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    Salt.BV.ppTerm (p ^ j) = 1 / (j : ℝ) := by
  have hplog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hΛ : ArithmeticFunction.vonMangoldt (p ^ j) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : j ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hnp : ¬ (p ^ j).Prime := Nat.Prime.not_prime_pow (by omega : 2 ≤ j)
  unfold Salt.BV.ppTerm
  rw [hΛ, if_neg hnp, sub_zero, Nat.cast_pow, Real.log_pow, mul_comm,
    ← div_div, div_self hplog.ne']

/-- On a prime `p`, `pp2Term = 0` (a prime is not a prime *square*). -/
lemma pp2Term_prime {p : ℕ} (hp : p.Prime) : pp2Term p = 0 := by
  unfold pp2Term
  rw [if_neg]
  rintro ⟨-, hs2⟩
  rw [← hs2] at hp
  exact absurd hp (Nat.Prime.not_prime_pow (by norm_num))

/-- On a prime square `p²`, `pp2Term = 1/2`. -/
lemma pp2Term_prime_sq {p : ℕ} (hp : p.Prime) : pp2Term (p ^ 2) = 1 / 2 := by
  have hsq : isPrimeSq (p ^ 2) := ⟨by rw [Nat.sqrt_eq']; exact hp, by rw [Nat.sqrt_eq']⟩
  unfold pp2Term; rw [if_pos hsq]

/-- On a cube-or-higher prime power `p^j` (`j ≥ 3`), `pp3Term = 1/j`. -/
lemma pp3Term_prime_pow_ge3 {p j : ℕ} (hp : p.Prime) (hj : 3 ≤ j) :
    pp3Term (p ^ j) = 1 / (j : ℝ) := by
  have hpp2 : pp2Term (p ^ j) = 0 := by
    unfold pp2Term
    rw [if_neg]
    rintro ⟨hs, hs2⟩
    -- `s := √(p^j)` prime with `s² = p^j`; then `s = p` and `j = 2`, contra `j ≥ 3`.
    have hsdvd : Nat.sqrt (p ^ j) ∣ p ^ j := by
      have h1 : Nat.sqrt (p ^ j) ∣ (Nat.sqrt (p ^ j)) ^ 2 :=
        dvd_pow_self (Nat.sqrt (p ^ j)) (by norm_num : (2 : ℕ) ≠ 0)
      rwa [hs2] at h1
    have hsp : Nat.sqrt (p ^ j) = p :=
      (Nat.prime_dvd_prime_iff_eq hs hp).mp (hs.dvd_of_dvd_pow hsdvd)
    rw [hsp] at hs2
    exact absurd (Nat.pow_right_injective hp.two_le hs2) (by omega)
  unfold pp3Term
  rw [ppTerm_prime_pow_val hp (by omega), hpp2, sub_zero]

/-- On a prime power `p^j` with `j ≤ 2`, `pp3Term = 0`. -/
lemma pp3Term_prime_pow_le2 {p j : ℕ} (hp : p.Prime) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
    pp3Term (p ^ j) = 0 := by
  interval_cases j
  · rw [pow_one]; unfold pp3Term; rw [Salt.BV.ppTerm_prime hp, pp2Term_prime hp, sub_zero]
  · unfold pp3Term; rw [ppTerm_pow_two hp, pp2Term_prime_sq hp, sub_self]

/-- Off the prime powers, `pp3Term = 0`. -/
lemma pp3Term_eq_zero_of_not_ppow {n : ℕ} (h : ¬ IsPrimePow n) : pp3Term n = 0 := by
  have hΛ0 : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h
  have hnp : ¬ n.Prime := fun hpr =>
    h ((isPrimePow_nat_iff n).mpr ⟨n, 1, hpr, one_pos, pow_one n⟩)
  have hnsq : ¬ isPrimeSq n := by
    rintro ⟨hs, hs2⟩
    exact h ((isPrimePow_nat_iff n).mpr ⟨Nat.sqrt n, 2, hs, by norm_num, hs2⟩)
  have hppTerm : Salt.BV.ppTerm n = 0 := by
    unfold Salt.BV.ppTerm; rw [hΛ0, zero_div, if_neg hnp, sub_zero]
  have hpp2 : pp2Term n = 0 := by unfold pp2Term; rw [if_neg hnsq]
  unfold pp3Term; rw [hppTerm, hpp2, sub_zero]

/-- `minFac (p^j) = p` for prime `p`, `j ≥ 1`: the smallest prime factor of a prime
power is its base. -/
lemma minFac_prime_pow {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) : Nat.minFac (p ^ j) = p := by
  have hne : p ^ j ≠ 1 := by
    have : 2 ≤ p ^ j := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
    omega
  have hm := Nat.minFac_prime hne
  exact (Nat.prime_dvd_prime_iff_eq hm hp).mp (hm.dvd_of_dvd_pow (Nat.minFac_dvd _))

/-- The decidable form of "`n` is a prime `j`-th power": its minimal prime factor is
prime and its `j`-th power recovers `n`.  Equivalent to `∃ p, p.Prime ∧ n = p^j` but
`Decidable`, so it can index `if`/`filter` without `Classical`. -/
def isPrimePowExp (j n : ℕ) : Prop := (Nat.minFac n).Prime ∧ (Nat.minFac n) ^ j = n

instance (j n : ℕ) : Decidable (isPrimePowExp j n) := by unfold isPrimePowExp; infer_instance

/-- A single `(1/m)`-weighted indicator term is nonnegative. -/
private lemma ppKsum_term_nonneg (m : ℕ) (P : Prop) [Decidable P] :
    (0 : ℝ) ≤ (1 / (m : ℝ)) * (if P then (1 : ℝ) else 0) := by
  refine mul_nonneg (by positivity) ?_; split_ifs <;> norm_num

/-- **The pointwise decomposition.**  For `1 ≤ n ≤ x`, `pp3Term n` is bounded by the
`k`-indexed sum of `(1/j)`-weighted `isPrimePowExp j` indicators, `j` ranging over
`[3, log₂ x]` — every exponent that can occur (`p^j ≤ x`, `p ≥ 2` forces
`j ≤ log₂ x`). -/
lemma pp3Term_le_ksum {x n : ℕ} (hn1 : 1 ≤ n) (hnx : n ≤ x) :
    pp3Term n ≤ ∑ j ∈ Finset.Icc 3 (Nat.log 2 x),
      (1 / (j : ℝ)) * (if isPrimePowExp j n then (1 : ℝ) else 0) := by
  have hSnonneg : 0 ≤ ∑ j ∈ Finset.Icc 3 (Nat.log 2 x),
      (1 / (j : ℝ)) * (if isPrimePowExp j n then (1 : ℝ) else 0) :=
    Finset.sum_nonneg (fun j _ => ppKsum_term_nonneg j (isPrimePowExp j n))
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, e, hp, hepos, hpe⟩ := (isPrimePow_nat_iff n).1 hpp
    subst hpe
    rcases lt_or_ge e 3 with he3 | he3
    · rw [pp3Term_prime_pow_le2 hp hepos (by omega)]; exact hSnonneg
    · have h2e : 2 ^ e ≤ x := le_trans (Nat.pow_le_pow_left hp.two_le e) hnx
      have heK : e ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) h2e
      have hemem : e ∈ Finset.Icc 3 (Nat.log 2 x) := Finset.mem_Icc.mpr ⟨by omega, heK⟩
      have hind : (if isPrimePowExp e (p ^ e) then (1 : ℝ) else 0) = 1 := by
        rw [if_pos]; unfold isPrimePowExp; rw [minFac_prime_pow hp (by omega)]; exact ⟨hp, rfl⟩
      rw [pp3Term_prime_pow_ge3 hp (by omega)]
      calc (1 / (e : ℝ))
          = (1 / (e : ℝ)) * (if isPrimePowExp e (p ^ e) then (1 : ℝ) else 0) := by
            rw [hind, mul_one]
        _ ≤ _ := Finset.single_le_sum
            (fun i _ => ppKsum_term_nonneg i (isPrimePowExp i (p ^ e))) hemem
  · rw [pp3Term_eq_zero_of_not_ppow hpp]; exact hSnonneg

/-- **The count reindex `F_j → G_j`.**  The `n`-indexed prime-`j`-th-power residue
class `{n ≤ x : n ≡ a, isPrimePowExp j n}` has card at most the `p`-indexed
`{p : p^j ≤ x, p^j ≡ a}` (its image under `p ↦ p^j`). -/
lemma card_Fj_le_Gj {x q a j : ℕ} (hj : 1 ≤ j) :
    ((Finset.Icc 1 x).filter (fun n => n % q = a ∧ isPrimePowExp j n)).card
      ≤ ((Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ^ j ≤ x ∧ p ^ j % q = a)).card := by
  set G := (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ^ j ≤ x ∧ p ^ j % q = a) with hG
  have hsub : (Finset.Icc 1 x).filter (fun n => n % q = a ∧ isPrimePowExp j n)
      ⊆ G.image (fun p => p ^ j) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_hn1, hnx⟩, hnmod, hpp, hnpj⟩ := hn
    -- `p := minFac n` is prime with `p^j = n`.
    set p := Nat.minFac n with hp
    rw [Finset.mem_image]
    refine ⟨p, ?_, hnpj⟩
    rw [hG, Finset.mem_filter, Finset.mem_Icc]
    have hple : p ≤ p ^ j := le_self_pow hpp.one_lt.le (by omega : j ≠ 0)
    have hpjx : p ^ j ≤ x := by rw [hnpj]; exact hnx
    exact ⟨⟨hpp.one_lt.le, le_trans hple hpjx⟩, hpp, hpjx, by rw [hnpj]; exact hnmod⟩
  calc ((Finset.Icc 1 x).filter (fun n => n % q = a ∧ isPrimePowExp j n)).card
      ≤ (G.image (fun p => p ^ j)).card := Finset.card_le_card hsub
    _ ≤ G.card := Finset.card_image_le

/-- **The crude (congruence-free) count.**  Dropping the residue condition,
`#{p : p^j ≤ x} ≤ x^{1/j}` (the primes sit in `[1, ⌊x^{1/j}⌋]`). -/
lemma card_Gj_crude_le {x q a j : ℕ} (hj : 1 ≤ j) :
    (((Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ^ j ≤ x ∧ p ^ j % q = a)).card : ℝ)
      ≤ (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := by
  set M : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / (j : ℝ))⌋₊ with hM
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hjne : (j : ℝ) ≠ 0 := hjR.ne'
  have hpM : ∀ p : ℕ, p ^ j ≤ x → p ≤ M := by
    intro p hpk
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hpkR : (p : ℝ) ^ j ≤ (x : ℝ) := by exact_mod_cast hpk
    have hstep : ((p : ℝ) ^ j) ^ ((1 : ℝ) / (j : ℝ)) = (p : ℝ) := by
      rw [← Real.rpow_natCast (p : ℝ) j, ← Real.rpow_mul hp0, mul_one_div, div_self hjne,
        Real.rpow_one]
    refine Nat.le_floor ?_
    calc (p : ℝ) = ((p : ℝ) ^ j) ^ ((1 : ℝ) / (j : ℝ)) := hstep.symm
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := Real.rpow_le_rpow (by positivity) hpkR (by positivity)
  have hsub : (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ^ j ≤ x ∧ p ^ j % q = a)
      ⊆ Finset.Icc 1 M := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.1.1, hpM p hp.2.2.1⟩
  calc (((Finset.Icc 1 x).filter (fun p => p.Prime ∧ p ^ j ≤ x ∧ p ^ j % q = a)).card : ℝ)
      ≤ ((Finset.Icc 1 M).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (M : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := Nat.floor_le (by positivity)

/-! ## §4  The per-reduced-class regime-split bound -/

/-- **The per-reduced-class bound.**  For a reduced residue `a` (`Coprime a q`,
`a < q`), the `pp3Term` residue-class sum splits into the root-count regime
(`3 ≤ j ≤ 8000`, carrying the `/q` saving) and the crude regime (`j > 8000`). -/
lemma classSum_pp3_le {x q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q) (ha2 : a < q) :
    |∑ n ∈ Finset.Icc 1 x, if n % q = a then pp3Term n else 0|
      ≤ (∑ j ∈ Finset.Icc (3 : ℕ) 8000,
            2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1))
        + (∑ j ∈ Finset.Icc 8001 (Nat.log 2 x), (x : ℝ) ^ ((1 : ℝ) / (j : ℝ))) := by
  set K := Nat.log 2 x with hK
  -- abbreviations
  set F' := (Finset.Icc 1 x).filter (fun n => n % q = a) with hF'
  set cardF : ℕ → ℕ := fun j =>
    ((Finset.Icc 1 x).filter (fun n => n % q = a ∧ isPrimePowExp j n)).card with hcardF
  -- Step 1: the class sum is nonnegative, over the filtered set.
  have hSeq : ∑ n ∈ Finset.Icc 1 x, (if n % q = a then pp3Term n else 0)
      = ∑ n ∈ F', pp3Term n := (Finset.sum_filter _ _).symm
  have hSnn : 0 ≤ ∑ n ∈ F', pp3Term n := Finset.sum_nonneg (fun n _ => pp3Term_nonneg n)
  rw [hSeq, abs_of_nonneg hSnn]
  -- Step 2: pointwise decomposition, swap, count.
  have hstep2 : ∑ n ∈ F', pp3Term n
      ≤ ∑ j ∈ Finset.Icc 3 K, (1 / (j : ℝ)) * (cardF j : ℝ) := by
    calc ∑ n ∈ F', pp3Term n
        ≤ ∑ n ∈ F', ∑ j ∈ Finset.Icc 3 K,
            (1 / (j : ℝ)) * (if isPrimePowExp j n then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [hF', Finset.mem_filter, Finset.mem_Icc] at hn
          exact pp3Term_le_ksum hn.1.1 hn.1.2
      _ = ∑ j ∈ Finset.Icc 3 K, ∑ n ∈ F',
            (1 / (j : ℝ)) * (if isPrimePowExp j n then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ j ∈ Finset.Icc 3 K, (1 / (j : ℝ)) * (cardF j : ℝ) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← Finset.mul_sum, Finset.sum_boole, hcardF, hF', Finset.filter_filter]
  refine le_trans hstep2 ?_
  -- Step 3: split the `j`-range at 8000.
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 3 K) (fun j => j ≤ 8000)]
  refine add_le_add ?_ ?_
  · -- root-count regime `j ≤ 8000`
    have hsub : (Finset.Icc 3 K).filter (fun j => j ≤ 8000) ⊆ Finset.Icc (3 : ℕ) 8000 := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      exact Finset.mem_Icc.mpr ⟨hj.1.1, hj.2⟩
    refine le_trans (Finset.sum_le_sum (fun j hj => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity))
    -- termwise: `(1/j)·cardF j ≤ 2 j^ω (x^{1/j}/q + 1)`
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := by omega
    have hjne : (j : ℝ) ≠ 0 := by positivity
    have h1 : (cardF j : ℝ)
        ≤ 2 * j * j ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1) :=
      le_trans (by exact_mod_cast card_Fj_le_Gj hj1) (card_primePow_class_le hq hj1 ha ha2)
    calc (1 / (j : ℝ)) * (cardF j : ℝ)
        ≤ (1 / (j : ℝ))
            * (2 * j * j ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1) := by
          field_simp
  · -- crude regime `j > 8000`
    have hset : (Finset.Icc 3 K).filter (fun j => ¬ j ≤ 8000) = Finset.Icc 8001 K := by
      ext j; rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]; omega
    rw [hset]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := by omega
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have h1 : (cardF j : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) :=
      le_trans (by exact_mod_cast card_Fj_le_Gj hj1) (card_Gj_crude_le hj1)
    calc (1 / (j : ℝ)) * (cardF j : ℝ)
        ≤ (1 / (j : ℝ)) * (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 * (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) :=
          mul_le_mul_of_nonneg_right ((div_le_one hjR).mpr (by exact_mod_cast hj1)) (by positivity)
      _ = (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := one_mul _

/-! ## §5  The crude fallback (small-`x` corner) -/

/-- The `ℓ¹` mass of `pp3Term` is dominated by that of `ppTerm`. -/
lemma sum_abs_pp3Term_le (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, |pp3Term n| ≤ Real.sqrt x * Real.log x / Real.log 2 := by
  refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (sum_abs_ppTerm_le x)
  rw [abs_of_nonneg (pp3Term_nonneg n), abs_of_nonneg (Salt.BV.ppTerm_nonneg n)]
  unfold pp3Term
  linarith [pp2Term_nonneg n]

/-- **Crude uniform per-`q` bound** for `pp3Term` (the small-`x` corner engine). -/
lemma seqDiscrepancy_pp3_crude (x q : ℕ) :
    seqDiscrepancy (fun n => pp3Term n) x q ≤ 2 * (Real.sqrt x * Real.log x / Real.log 2) :=
  (seqDiscrepancy_le_two_mul_sum_abs (fun n => pp3Term n) x q).trans
    (mul_le_mul_of_nonneg_left (sum_abs_pp3Term_le x) (by norm_num))

/-! ## §6  The per-`q` sum via `PpSums`, and the assembled bound -/

/-- **The `q`-sum of one exponent's root-count term**, closed with the two `PpSums`
lemmas: `∑_q j^{ω(q)}/q ≤ (1+log Q)^j` and `∑_q j^{ω(q)} ≤ Q(1+log Q)^{j-1}`. -/
lemma innerQ_bound (x Q j : ℕ) (hj : 1 ≤ j) :
    ∑ q ∈ Finset.Icc 1 Q,
        2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1)
      ≤ 2 * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) * (1 + Real.log Q) ^ j
              + (Q : ℝ) * (1 + Real.log Q) ^ (j - 1)) := by
  have heq : ∀ q ∈ Finset.Icc 1 Q,
      2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1)
        = 2 * (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) * ((j : ℝ) ^ q.primeFactors.card / q)
          + 2 * (j : ℝ) ^ q.primeFactors.card := fun q _ => by ring
  rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ q ∈ Finset.Icc 1 Q, (j : ℝ) ^ q.primeFactors.card / q ≤ (1 + Real.log Q) ^ j :=
    sum_k_pow_omega_div_le Q j
  have h2 : ∑ q ∈ Finset.Icc 1 Q, (j : ℝ) ^ q.primeFactors.card
      ≤ (Q : ℝ) * (1 + Real.log Q) ^ (j - 1) := sum_k_pow_omega_le Q j hj
  have hxnn : (0 : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := by positivity
  calc 2 * (x : ℝ) ^ ((1 : ℝ) / (j : ℝ))
          * (∑ q ∈ Finset.Icc 1 Q, (j : ℝ) ^ q.primeFactors.card / q)
        + 2 * (∑ q ∈ Finset.Icc 1 Q, (j : ℝ) ^ q.primeFactors.card)
      ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) * (1 + Real.log Q) ^ j
          + 2 * ((Q : ℝ) * (1 + Real.log Q) ^ (j - 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hxnn) (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = 2 * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) * (1 + Real.log Q) ^ j
              + (Q : ℝ) * (1 + Real.log Q) ^ (j - 1)) := by ring

/-- **Per-exponent bound in the root regime.**  Each `j ∈ [3,8000]` term is bounded
by the `j`-free `4·x^θ·(1+log x)^{8000}` (`x^{1/j} ≤ x^θ` since `1/j ≤ 1/3 ≤ θ`;
`(1+log Q)^j ≤ (1+log x)^{8000}`; `Q ≤ x^θ`). -/
lemma perJ_root_bound (x Q j : ℕ) (hx : 2 ≤ x) (hj3 : 3 ≤ j) (hj8000 : j ≤ 8000)
    (hQx : (Q : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ)) (hlogQ0 : 0 ≤ Real.log Q)
    (hlogQL : Real.log Q ≤ Real.log x) :
    2 * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) * (1 + Real.log Q) ^ j
          + (Q : ℝ) * (1 + Real.log Q) ^ (j - 1))
      ≤ 4 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) ^ 8000 := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hbaseLnn : (0 : ℝ) ≤ 1 + Real.log Q := by linarith
  have hbaseL : 1 + Real.log Q ≤ 1 + Real.log x := by linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hLxpos : (0 : ℝ) ≤ Real.log x := le_trans hlogQ0 hlogQL
  have hxj : (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    rw [div_le_iff₀ hjpos]
    have hj3R : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
    nlinarith [hj3R]
  have h1Lx : (1 : ℝ) ≤ 1 + Real.log x := by linarith
  have hpowj : (1 + Real.log Q) ^ j ≤ (1 + Real.log x) ^ 8000 := by
    calc (1 + Real.log Q) ^ j ≤ (1 + Real.log x) ^ j := pow_le_pow_left₀ hbaseLnn hbaseL j
      _ ≤ (1 + Real.log x) ^ 8000 := pow_le_pow_right₀ h1Lx hj8000
  have hpowj1 : (1 + Real.log Q) ^ (j - 1) ≤ (1 + Real.log x) ^ 8000 := by
    calc (1 + Real.log Q) ^ (j - 1) ≤ (1 + Real.log x) ^ (j - 1) :=
          pow_le_pow_left₀ hbaseLnn hbaseL (j - 1)
      _ ≤ (1 + Real.log x) ^ 8000 := pow_le_pow_right₀ h1Lx (by omega)
  have hA : (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) * (1 + Real.log Q) ^ j
      ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) ^ 8000 :=
    mul_le_mul hxj hpowj (pow_nonneg hbaseLnn j) hxθnn
  have hB : (Q : ℝ) * (1 + Real.log Q) ^ (j - 1)
      ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) ^ 8000 :=
    mul_le_mul hQx hpowj1 (pow_nonneg hbaseLnn (j - 1)) hxθnn
  calc 2 * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) * (1 + Real.log Q) ^ j
              + (Q : ℝ) * (1 + Real.log Q) ^ (j - 1))
      ≤ 2 * ((x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) ^ 8000
              + (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) ^ 8000) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
    _ = 4 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) ^ 8000 := by
        rw [← two_mul, ← mul_assoc, ← mul_assoc]; norm_num

/-- **The assembled `q`-sum bound.**  The full `pp3Term` discrepancy sum over the
haircut moduli splits into `64000·x^θ·(1+log x)^{8000}` (root regime, `PpSums`) plus
`4·log x·x^{7999/8000}` (crude regime). -/
lemma sum_seqDiscrepancy_pp3_qbound (x : ℕ) (hx : 2 ≤ x) :
    ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
        seqDiscrepancy (fun n => pp3Term n) x q
      ≤ 64000 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) ^ 8000
        + 4 * Real.log x * (x : ℝ) ^ (7999 / 8000 : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  set L := Real.log x with hLdef
  set K := Nat.log 2 x with hKdef
  set Q := ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ with hQdef
  -- `x^θ` facts
  have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Real.rpow_nonneg hxpos.le _
  have hxθ1 : (1 : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (3999 / 4000 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Real.rpow_le_rpow (by norm_num) hx1 (by norm_num)
  have hxθlex : (x : ℝ) ^ (3999 / 4000 : ℝ) ≤ (x : ℝ) := by
    calc (x : ℝ) ^ (3999 / 4000 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _
  have hQ1 : 1 ≤ Q := Nat.le_floor (by rw [Nat.cast_one]; exact hxθ1)
  have hQxθ : (Q : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Nat.floor_le hxθnn
  have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1R
  have hlogQL : Real.log Q ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by positivity) (le_trans hQxθ hxθlex)
  have hL0 : (0 : ℝ) ≤ L := le_trans hlogQ0 hlogQL
  -- `K ≤ 2 L`
  have hK2L : (K : ℝ) ≤ 2 * L := by
    have hpow : (2 : ℝ) ^ K ≤ (x : ℝ) := by
      rw [hKdef]; exact_mod_cast Nat.pow_log_le_self 2 (by omega : x ≠ 0)
    have hKlog : (K : ℝ) * Real.log 2 ≤ L := by
      rw [hLdef, ← Real.log_pow]
      exact Real.log_le_log (by positivity) hpow
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hprod : (K : ℝ) * (1 / 2) ≤ (K : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2 hKnn
    linarith [hKlog, hprod]
  -- the per-`q` connector
  have hconn : ∀ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => pp3Term n) x q
      ≤ 2 * ((∑ j ∈ Finset.Icc (3 : ℕ) 8000,
                2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1))
             + (∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)))) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    refine seqDiscrepancy_le_two_classBd (by omega) (fun a ha => ?_)
    rw [Finset.mem_filter, Finset.mem_range] at ha
    exact classSum_pp3_le hq1 ha.2 ha.1
  -- the crude-regime sum is `q`-independent; bound its `Q`-multiple
  have hCrudeSum : ∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ))
      ≤ (K : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8000) := by
    calc ∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ))
        ≤ ∑ _j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / 8000) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [Finset.mem_Icc] at hj
          refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
          apply one_div_le_one_div_of_le (by norm_num)
          exact_mod_cast (by omega : (8000 : ℕ) ≤ j)
      _ = ((Finset.Icc 8001 K).card : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8000) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (K : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8000) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxpos.le _)
          rw [Nat.card_Icc]; exact_mod_cast (show K + 1 - 8001 ≤ K by omega)
  have hQCrude : (Q : ℝ) * (∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)))
      ≤ 2 * L * (x : ℝ) ^ (7999 / 8000 : ℝ) := by
    have hCS2L : ∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ))
        ≤ 2 * L * (x : ℝ) ^ ((1 : ℝ) / 8000) :=
      le_trans hCrudeSum (mul_le_mul_of_nonneg_right hK2L (Real.rpow_nonneg hxpos.le _))
    have hCSnn : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) :=
      Finset.sum_nonneg (fun j _ => Real.rpow_nonneg hxpos.le _)
    calc (Q : ℝ) * (∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)))
        ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) * (2 * L * (x : ℝ) ^ ((1 : ℝ) / 8000)) :=
          mul_le_mul hQxθ hCS2L hCSnn hxθnn
      _ = 2 * L * ((x : ℝ) ^ (3999 / 4000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8000)) := by ring
      _ = 2 * L * (x : ℝ) ^ (7999 / 8000 : ℝ) := by
          rw [← Real.rpow_add hxpos,
            show (3999 / 4000 + (1 : ℝ) / 8000 : ℝ) = 7999 / 8000 by norm_num]
  set P := (1 + L) ^ 8000 with hP
  clear_value P
  -- the root-regime sum, via `sum_comm` + `innerQ_bound` + `perJ_root_bound`
  have hRoot : ∑ q ∈ Finset.Icc 1 Q,
        (∑ j ∈ Finset.Icc (3 : ℕ) 8000,
          2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1))
      ≤ 32000 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P := by
    rw [Finset.sum_comm]
    calc ∑ j ∈ Finset.Icc (3 : ℕ) 8000, ∑ q ∈ Finset.Icc 1 Q,
            2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1)
        ≤ ∑ j ∈ Finset.Icc (3 : ℕ) 8000,
            2 * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) * (1 + Real.log Q) ^ j
                 + (Q : ℝ) * (1 + Real.log Q) ^ (j - 1)) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [Finset.mem_Icc] at hj
          exact innerQ_bound x Q j (by omega)
      _ ≤ ∑ _j ∈ Finset.Icc (3 : ℕ) 8000,
            4 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + L) ^ 8000 := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [Finset.mem_Icc] at hj
          rw [hLdef]
          exact perJ_root_bound x Q j hx hj.1 hj.2 hQxθ hlogQ0 hlogQL
      _ = ((Finset.Icc (3 : ℕ) 8000).card : ℝ)
            * (4 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P) := by
          rw [Finset.sum_const, nsmul_eq_mul, hP]
      _ ≤ 32000 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P := by
          rw [Nat.card_Icc]
          have hcard : (((8000 + 1 - 3 : ℕ)) : ℝ) ≤ 8000 := by norm_num
          have hPnn : (0 : ℝ) ≤ 4 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P := by
            rw [hP]; positivity
          calc (((8000 + 1 - 3 : ℕ)) : ℝ) * (4 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P)
              ≤ 8000 * (4 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P) :=
                mul_le_mul_of_nonneg_right hcard hPnn
            _ = 32000 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P := by ring
  -- assemble
  calc ∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => pp3Term n) x q
      ≤ ∑ q ∈ Finset.Icc 1 Q,
          2 * ((∑ j ∈ Finset.Icc (3 : ℕ) 8000,
                  2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1))
               + (∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)))) :=
        Finset.sum_le_sum hconn
    _ = 2 * ((∑ q ∈ Finset.Icc 1 Q, ∑ j ∈ Finset.Icc (3 : ℕ) 8000,
                2 * (j : ℝ) ^ q.primeFactors.card * ((x : ℝ) ^ ((1 : ℝ) / (j : ℝ)) / q + 1))
             + (Q : ℝ) * (∑ j ∈ Finset.Icc 8001 K, (x : ℝ) ^ ((1 : ℝ) / (j : ℝ)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
            Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ 2 * (32000 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P + 2 * L * (x : ℝ) ^ (7999 / 8000 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (add_le_add hRoot hQCrude) (by norm_num)
    _ = 64000 * (x : ℝ) ^ (3999 / 4000 : ℝ) * P + 4 * L * (x : ℝ) ^ (7999 / 8000 : ℝ) := by
          ring

/-! ## §7  The `pp2` part (for Milestone 2) -/

/-- **The `pp2` `q`-sum**, via `GehPp2`'s `2^{ω}` sums: `∑_q 2^{ω+1}(√x/q+1)
≤ 2√x(1+log x)² + 2·x^θ(1+log x)`. -/
lemma sum_pp2part_qbound (x : ℕ) (hx : 2 ≤ x) :
    ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
        2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1)
      ≤ 2 * Real.sqrt x * (1 + Real.log x) ^ 2
        + 2 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) := by
  set Q := ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ with hQdef
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Real.rpow_nonneg hxpos.le _
  have hxθ1 : (1 : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (3999 / 4000 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Real.rpow_le_rpow (by norm_num) hx1 (by norm_num)
  have hxθlex : (x : ℝ) ^ (3999 / 4000 : ℝ) ≤ (x : ℝ) := by
    calc (x : ℝ) ^ (3999 / 4000 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _
  have hQ1 : 1 ≤ Q := Nat.le_floor (by rw [Nat.cast_one]; exact hxθ1)
  have hQxθ : (Q : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Nat.floor_le hxθnn
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ1)
  have hlogQL : Real.log Q ≤ Real.log x :=
    Real.log_le_log (by positivity) (le_trans hQxθ hxθlex)
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
  -- split the summand
  have heq : ∀ q ∈ Finset.Icc 1 Q,
      (2 : ℝ) ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1)
        = 2 * Real.sqrt x * ((2 : ℝ) ^ q.primeFactors.card / q)
          + 2 * (2 : ℝ) ^ q.primeFactors.card := fun q _ => by rw [pow_succ]; ring
  rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card / q ≤ (1 + Real.log Q) ^ 2 :=
    sum_two_pow_omega_div_le Q hQ1
  have h2 : ∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card ≤ (Q : ℝ) * (1 + Real.log Q) :=
    sum_two_pow_omega_le Q hQ1
  have hlogQ1nn : (0 : ℝ) ≤ 1 + Real.log Q := by linarith
  have hlogQ1L : 1 + Real.log Q ≤ 1 + Real.log x := by linarith
  calc 2 * Real.sqrt x * (∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card / q)
          + 2 * (∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card)
      ≤ 2 * Real.sqrt x * (1 + Real.log Q) ^ 2 + 2 * ((Q : ℝ) * (1 + Real.log Q)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ ≤ 2 * Real.sqrt x * (1 + Real.log x) ^ 2
          + 2 * ((x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x)) := by
        gcongr
    _ = 2 * Real.sqrt x * (1 + Real.log x) ^ 2
          + 2 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + Real.log x) := by ring

/-! ## §8  Milestone 1 — the summed `pp3Term` discrepancy bound -/

/-- Arithmetic helper: `Pg` is an abstract variable, so the internal `ring` never
expands the concrete `(1+log x)^{8000}` it is instantiated with (which would blow up
the elaborator). -/
private lemma term_fold {K xθ Pg LA bnd xval : ℝ} (hxθ : 0 ≤ xθ)
    (hcomb : K * Pg * LA ≤ bnd) (hx : xθ * bnd = xval) :
    K * xθ * Pg * LA ≤ xval := by
  calc K * xθ * Pg * LA = xθ * (K * Pg * LA) := by ring
    _ ≤ xθ * bnd := mul_le_mul_of_nonneg_left hcomb hxθ
    _ = xval := hx

/-- **Milestone 1.**  The core of node PP3-ASSEMBLY: the summed sequence discrepancy
of the `k ≥ 3` prime-power tail over the GEH haircut range is `≤ C·x/(log x)^A`.
The root and crude regimes each land `≤ x/(log x)^A` eventually
(`eventually_poly_beats_polylog`); the small-`x` corner folds into `C` via the crude
ℓ¹ bound. -/
theorem sum_seqDiscrepancy_pp3_le : ∀ A : ℝ, 0 < A → ∃ C, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
    ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
        seqDiscrepancy (fun n => pp3Term n) x q
      ≤ C * x / Real.log x ^ A := by
  intro A hA
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually
    (eventually_poly_beats_polylog (8000 + ⌈A⌉₊) (1 / 4000) 64000 (by norm_num)))
  obtain ⟨X2, hX2⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually
    (eventually_poly_beats_polylog ⌈(1 : ℝ) + A⌉₊ (1 / 8000) 4 (by norm_num)))
  set X0 : ℕ := max (max X1 X2) 3 with hX0def
  have hX03 : 3 ≤ X0 := le_max_right _ _
  have hX0R1 : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by omega : 1 < X0)
  have hlogX0 : 0 < Real.log X0 := Real.log_pos hX0R1
  set Kc : ℝ := 2 * Real.sqrt X0 * Real.log X0 ^ ((1 : ℝ) + A) / Real.log 2 with hKcdef
  refine ⟨max 2 Kc, lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  set L := Real.log x with hLdef
  have hLpos : (0 : ℝ) < L := Real.log_pos (by exact_mod_cast hx)
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hLApos : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos A
  set Q := ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ with hQdef
  have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Real.rpow_nonneg hxpos.le _
  rcases lt_or_ge x X0 with hlt | hxge
  · -- corner: `2 ≤ x < X0`, crude ℓ¹ bound.
    have hxX0 : (x : ℝ) < (X0 : ℝ) := by exact_mod_cast hlt
    have hQxle : (Q : ℝ) ≤ (x : ℝ) := by
      calc (Q : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Nat.floor_le hxθnn
        _ ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = (x : ℝ) := Real.rpow_one _
    have hcrude : ∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => pp3Term n) x q
        ≤ (Q : ℝ) * (2 * (Real.sqrt x * L / Real.log 2)) := by
      calc ∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => pp3Term n) x q
          ≤ ∑ _q ∈ Finset.Icc 1 Q, 2 * (Real.sqrt x * L / Real.log 2) :=
            Finset.sum_le_sum (fun q _ => seqDiscrepancy_pp3_crude x q)
        _ = (Q : ℝ) * (2 * (Real.sqrt x * L / Real.log 2)) := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    refine hcrude.trans ?_
    rw [le_div_iff₀ hLApos]
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hLLX0 : L * L ^ A ≤ Real.log X0 ^ ((1 : ℝ) + A) := by
      have heq : L * L ^ A = L ^ ((1 : ℝ) + A) := by
        rw [Real.rpow_add hLpos, Real.rpow_one]
      rw [heq]
      exact Real.rpow_le_rpow hL0 (Real.log_le_log hxpos hxX0.le) (by linarith)
    have hsqrt : Real.sqrt x ≤ Real.sqrt X0 := Real.sqrt_le_sqrt hxX0.le
    have hkey : (Q : ℝ) * (2 * (Real.sqrt x * L / Real.log 2)) * L ^ A
        ≤ Kc * (x : ℝ) := by
      rw [hKcdef]
      have hexp : (Q : ℝ) * (2 * (Real.sqrt x * L / Real.log 2)) * L ^ A
          = (Q : ℝ) * (Real.sqrt x) * (L * L ^ A) * (2 / Real.log 2) := by ring
      have hexp2 : 2 * Real.sqrt X0 * Real.log X0 ^ ((1 : ℝ) + A) / Real.log 2 * (x : ℝ)
          = (x : ℝ) * Real.sqrt X0 * Real.log X0 ^ ((1 : ℝ) + A) * (2 / Real.log 2) := by ring
      rw [hexp, hexp2]
      gcongr
    refine hkey.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hxpos.le
  · -- main: `x ≥ X0`, the two-regime eventual bounds.
    have hqb := sum_seqDiscrepancy_pp3_qbound x hx
    have hX1x : X1 ≤ x := le_trans (le_trans (le_max_left X1 X2) (le_max_left _ _)) hxge
    have hX2x : X2 ≤ x := le_trans (le_trans (le_max_right X1 X2) (le_max_left _ _)) hxge
    -- Term 1 ≤ x / L^A
    have hT1 : 64000 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + L) ^ 8000 ≤ (x : ℝ) / L ^ A := by
      have hkey : 64000 * (1 + L) ^ (8000 + ⌈A⌉₊) ≤ (x : ℝ) ^ ((1 : ℝ) / 4000) := by
        have h := hX1 x hX1x; rw [← hLdef] at h; exact h
      have hLApoly : (1 + L) ^ 8000 * L ^ A ≤ (1 + L) ^ (8000 + ⌈A⌉₊) := by
        rw [pow_add]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith only [hL0]) 8000)
        calc L ^ A ≤ (1 + L) ^ A := Real.rpow_le_rpow hL0 (by linarith only [hL0]) hA.le
          _ ≤ (1 + L) ^ ((⌈A⌉₊ : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith only [hL0]) (Nat.le_ceil A)
          _ = (1 + L) ^ ⌈A⌉₊ := by rw [Real.rpow_natCast]
      have hcomb : 64000 * (1 + L) ^ 8000 * L ^ A ≤ (x : ℝ) ^ ((1 : ℝ) / 4000) := by
        rw [mul_assoc]
        exact le_trans (mul_le_mul_of_nonneg_left hLApoly (by norm_num)) hkey
      have hxeq : (x : ℝ) ^ (3999 / 4000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 4000) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos, show (3999 / 4000 + (1 : ℝ) / 4000 : ℝ) = 1 by norm_num,
          Real.rpow_one]
      rw [le_div_iff₀ hLApos]
      exact term_fold hxθnn hcomb hxeq
    -- Term 2 ≤ x / L^A
    have hT2 : 4 * L * (x : ℝ) ^ (7999 / 8000 : ℝ) ≤ (x : ℝ) / L ^ A := by
      have hkey : 4 * (1 + L) ^ ⌈(1 : ℝ) + A⌉₊ ≤ (x : ℝ) ^ ((1 : ℝ) / 8000) := by
        have h := hX2 x hX2x; rw [← hLdef] at h; exact h
      have hLL : L * L ^ A ≤ (1 + L) ^ ⌈(1 : ℝ) + A⌉₊ := by
        have heq : L * L ^ A = L ^ ((1 : ℝ) + A) := by rw [Real.rpow_add hLpos, Real.rpow_one]
        rw [heq]
        calc L ^ ((1 : ℝ) + A) ≤ (1 + L) ^ ((1 : ℝ) + A) :=
              Real.rpow_le_rpow hL0 (by linarith only [hL0, hA.le]) (by linarith only [hL0, hA.le])
          _ ≤ (1 + L) ^ ((⌈(1 : ℝ) + A⌉₊ : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith only [hL0, hA.le]) (Nat.le_ceil _)
          _ = (1 + L) ^ ⌈(1 : ℝ) + A⌉₊ := by rw [Real.rpow_natCast]
      rw [le_div_iff₀ hLApos]
      calc 4 * L * (x : ℝ) ^ (7999 / 8000 : ℝ) * L ^ A
          = (x : ℝ) ^ (7999 / 8000 : ℝ) * (4 * (L * L ^ A)) := by ring
        _ ≤ (x : ℝ) ^ (7999 / 8000 : ℝ) * (4 * (1 + L) ^ ⌈(1 : ℝ) + A⌉₊) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hLL (by norm_num : (0 : ℝ) ≤ 4))
              (Real.rpow_nonneg hxpos.le _)
        _ ≤ (x : ℝ) ^ (7999 / 8000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8000) :=
            mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hxpos.le _)
        _ = (x : ℝ) := by
            rw [← Real.rpow_add hxpos, show (7999 / 8000 + (1 : ℝ) / 8000 : ℝ) = 1 by norm_num,
              Real.rpow_one]
    -- combine
    calc ∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => pp3Term n) x q
        ≤ 64000 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + L) ^ 8000
            + 4 * L * (x : ℝ) ^ (7999 / 8000 : ℝ) := hqb
      _ ≤ (x : ℝ) / L ^ A + (x : ℝ) / L ^ A := add_le_add hT1 hT2
      _ = 2 * (x : ℝ) / L ^ A := by ring
      _ ≤ max 2 Kc * (x : ℝ) / L ^ A := by
          rw [div_le_div_iff_of_pos_right hLApos]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxpos.le

/-! ## §9  Milestone 2 — `PpLevel (3999/4000)` -/

/-- **The `pp2` summed bound.**  The prime-square part of the correction sums to
`≤ C·x/(log x)^A` over the haircut moduli (`√x·polylog` and `x^θ·polylog`, both
beaten eventually; small-`x` corner folds in). -/
theorem sum_pp2part_le : ∀ A : ℝ, 0 < A → ∃ C, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
        2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1))
      ≤ C * x / Real.log x ^ A := by
  intro A hA
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually
    (eventually_poly_beats_polylog (2 + ⌈A⌉₊) (1 / 2) 2 (by norm_num)))
  obtain ⟨X2, hX2⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually
    (eventually_poly_beats_polylog (1 + ⌈A⌉₊) (1 / 4000) 2 (by norm_num)))
  set X0 : ℕ := max (max X1 X2) 3 with hX0def
  have hX03 : 3 ≤ X0 := le_max_right _ _
  have hX0R1 : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by omega : 1 < X0)
  have hlogX0 : 0 < Real.log X0 := Real.log_pos hX0R1
  set Kb : ℝ := 2 * Real.sqrt X0 * (1 + Real.log X0) ^ 2 + 2 * (X0 : ℝ) * (1 + Real.log X0)
    with hKbdef
  have hKbnn : 0 ≤ Kb := by rw [hKbdef]; positivity
  set Kc : ℝ := Kb * Real.log X0 ^ A / 2 with hKcdef
  refine ⟨max 2 Kc, lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  set L := Real.log x with hLdef
  have hLpos : (0 : ℝ) < L := Real.log_pos (by exact_mod_cast hx)
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hLApos : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos A
  have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := Real.rpow_nonneg hxpos.le _
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hqb := sum_pp2part_qbound x hx
  rcases lt_or_ge x X0 with hlt | hxge
  · -- corner
    have hxX0 : (x : ℝ) < (X0 : ℝ) := by exact_mod_cast hlt
    have hLlogX0 : L ≤ Real.log X0 := by rw [hLdef]; exact Real.log_le_log hxpos hxX0.le
    have hxθX0 : (x : ℝ) ^ (3999 / 4000 : ℝ) ≤ (X0 : ℝ) := by
      calc (x : ℝ) ^ (3999 / 4000 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = (x : ℝ) := Real.rpow_one _
        _ ≤ (X0 : ℝ) := hxX0.le
    have hKb : 2 * Real.sqrt x * (1 + L) ^ 2 + 2 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + L) ≤ Kb := by
      rw [hKbdef]; gcongr
    refine (hqb.trans hKb).trans ?_
    rw [le_div_iff₀ hLApos]
    have hLAX0 : L ^ A ≤ Real.log X0 ^ A := Real.rpow_le_rpow hL0 hLlogX0 hA.le
    calc Kb * L ^ A ≤ Kb * Real.log X0 ^ A := mul_le_mul_of_nonneg_left hLAX0 hKbnn
      _ = 2 * Kc := by rw [hKcdef]; ring
      _ ≤ max 2 Kc * (x : ℝ) := by
          have h1 : (2 : ℝ) * Kc ≤ max 2 Kc * 2 := by
            rw [mul_comm (max 2 Kc) 2]
            exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
          have h2 : max 2 Kc * 2 ≤ max 2 Kc * (x : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hx)
              (le_trans (by norm_num) (le_max_left _ _))
          linarith
  · -- main regime
    have hX1x : X1 ≤ x := le_trans (le_trans (le_max_left X1 X2) (le_max_left _ _)) hxge
    have hX2x : X2 ≤ x := le_trans (le_trans (le_max_right X1 X2) (le_max_left _ _)) hxge
    -- Term a: `2√x(1+L)² ≤ x/L^A`
    have hTa : 2 * Real.sqrt x * (1 + L) ^ 2 ≤ (x : ℝ) / L ^ A := by
      have hkey : 2 * (1 + L) ^ (2 + ⌈A⌉₊) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
        have h := hX1 x hX1x; rw [← hLdef] at h; exact h
      have hLApoly : (1 + L) ^ 2 * L ^ A ≤ (1 + L) ^ (2 + ⌈A⌉₊) := by
        rw [pow_add]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith only [hL0]) 2)
        calc L ^ A ≤ (1 + L) ^ A := Real.rpow_le_rpow hL0 (by linarith only [hL0]) hA.le
          _ ≤ (1 + L) ^ ((⌈A⌉₊ : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith only [hL0]) (Nat.le_ceil A)
          _ = (1 + L) ^ ⌈A⌉₊ := by rw [Real.rpow_natCast]
      have hcomb : 2 * (1 + L) ^ 2 * L ^ A ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [mul_assoc]
        exact le_trans (mul_le_mul_of_nonneg_left hLApoly (by norm_num)) hkey
      have hxeq : Real.sqrt x * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos,
          show ((1 : ℝ) / 2 + 1 / 2) = 1 by norm_num, Real.rpow_one]
      rw [le_div_iff₀ hLApos]
      exact term_fold hsqrtnn hcomb hxeq
    -- Term b: `2·x^θ(1+L) ≤ x/L^A`
    have hTb : 2 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + L) ≤ (x : ℝ) / L ^ A := by
      have hkey : 2 * (1 + L) ^ (1 + ⌈A⌉₊) ≤ (x : ℝ) ^ ((1 : ℝ) / 4000) := by
        have h := hX2 x hX2x; rw [← hLdef] at h; exact h
      have hLApoly : (1 + L) ^ 1 * L ^ A ≤ (1 + L) ^ (1 + ⌈A⌉₊) := by
        rw [pow_add]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith only [hL0]) 1)
        calc L ^ A ≤ (1 + L) ^ A := Real.rpow_le_rpow hL0 (by linarith only [hL0]) hA.le
          _ ≤ (1 + L) ^ ((⌈A⌉₊ : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith only [hL0]) (Nat.le_ceil A)
          _ = (1 + L) ^ ⌈A⌉₊ := by rw [Real.rpow_natCast]
      have hcomb : 2 * (1 + L) ^ 1 * L ^ A ≤ (x : ℝ) ^ ((1 : ℝ) / 4000) := by
        rw [mul_assoc]
        exact le_trans (mul_le_mul_of_nonneg_left hLApoly (by norm_num)) hkey
      have hxeq : (x : ℝ) ^ (3999 / 4000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 4000) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos, show (3999 / 4000 + (1 : ℝ) / 4000 : ℝ) = 1 by norm_num,
          Real.rpow_one]
      rw [le_div_iff₀ hLApos]
      rw [pow_one] at hcomb
      exact term_fold hxθnn hcomb hxeq
    calc ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
            2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1)
        ≤ 2 * Real.sqrt x * (1 + L) ^ 2 + 2 * (x : ℝ) ^ (3999 / 4000 : ℝ) * (1 + L) := hqb
      _ ≤ (x : ℝ) / L ^ A + (x : ℝ) / L ^ A := add_le_add hTa hTb
      _ = 2 * (x : ℝ) / L ^ A := by ring
      _ ≤ max 2 Kc * (x : ℝ) / L ^ A := by
          rw [div_le_div_iff_of_pos_right hLApos]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxpos.le

/-- **Milestone 2 (the stretch prize).**  `PpLevel (3999/4000)` — the GEH door's
prime-power obligation.  Splits `ppTerm = pp2 + pp3`
(`seqDiscrepancy_ppTerm_le_pp2_add_tail`); the square part is `sum_pp2part_le`, the
`k ≥ 3` tail is Milestone 1.  Haircut `B = 0`. -/
theorem ppLevel_holds : PpLevel (3999 / 4000) := by
  intro A hA
  obtain ⟨C1, hC1pos, hC1⟩ := sum_seqDiscrepancy_pp3_le A hA
  obtain ⟨C2, hC2pos, hC2⟩ := sum_pp2part_le A hA
  refine ⟨0, C1 + C2, le_refl 0, fun x hx => ?_⟩
  have hrange : ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ (0 : ℝ)⌋₊
      = ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ := by rw [Real.rpow_zero, div_one]
  rw [hrange]
  calc ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
          seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q
      ≤ ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
          (2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1)
            + seqDiscrepancy pp3Term x q) :=
        Finset.sum_le_sum (fun q hq =>
          seqDiscrepancy_ppTerm_le_pp2_add_tail x q (Finset.mem_Icc.mp hq).1)
    _ = (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
            2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1))
          + ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊,
              seqDiscrepancy (fun n => pp3Term n) x q := Finset.sum_add_distrib
    _ ≤ C2 * x / Real.log x ^ A + C1 * x / Real.log x ^ A := add_le_add (hC2 x hx) (hC1 x hx)
    _ = (C1 + C2) * x / Real.log x ^ A := by ring

end Salt.Maynard
