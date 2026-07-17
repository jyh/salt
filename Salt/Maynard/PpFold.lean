/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.ShiuBlocks
import Salt.Maynard.PpRootCrt
import Salt.Maynard.GehPp

/-!
# The per-`q` `ppTerm` discrepancy bound — folding the root counts (node N-PP-FOLD)

Fourth link of the GEH door's `PpLevel` chain. Folds the landed composite-modulus
square-root count (`Salt.Maynard.card_sq_eq_units_le`, `2^{ω(q)+1}` roots of a unit)
and the trivial interval count (`Salt.Maynard.card_ap_le`, `≤ z/q+1` integers of
`[1,z]` in a residue class) into a per-`q` bound on `seqDiscrepancy` of the
prime-power correction, in the shape the `PpLevel` assembly sums.

## What lands here (the `k = 2` / prime-square part, dominant)

`ppTerm n = Λ(n)/log n − 1_{n prime}` is supported on proper prime powers `p^k`
(`k ≥ 2`), value `1/k`. The **`k = 2` piece** — the weight `pp2Term`, value `1/2`
on prime squares `p²` and `0` elsewhere — carries the mass. Its per-`q` discrepancy
is bounded sorry-free by

  `seqDiscrepancy pp2Term x q ≤ 2^{ω(q)+1}·(√x/q + 1)`      (`seqDiscrepancy_pp2Term_le`)

and hence, matching the assembly's target shape,

  `∃ C > 0, seqDiscrepancy pp2Term x q`
    `≤ C·(2^{ω(q)}·(√x/q + 1)·log x + √x·log x/φ(q))`  (`seqDiscrepancy_pp2Term_bound`).

Summed over `q ≤ x^θ` with the landed `GehPp2` sums (`Σ 2^{ω}/q ≪ log²`,
`Σ 2^{ω} ≪ Q·log`), the residue part is `≪ √x·log²x + x^θ·log x`, i.e. the
`≪ √x·polylog + x^θ·polylog` the door consumes. **No separate mean term is
needed**: `seqDiscrepancy_le_two_classBd` bounds the coprime mean by the same
per-class bound (the mean is the average of the `φ(q)` reduced-class sums).

### The mechanics of the `k = 2` bound

For a reduced residue `a` (`Coprime a q`, `a < q`), a prime `p` with `p² ≡ a
(mod q)` has `p` coprime to `q` (as `a` is a unit), so `p mod q` is one of the
`≤ 2^{ω(q)+1}` square roots of `a` in `(ZMod q)ˣ` (`card_sq_eq_units_le`, bridged
to the residue count in `card_sq_residues_le`). Each such root class contributes
`≤ √x/q + 1` primes `p ≤ √x` (`card_ap_le`). Fibering `{p : p² ≤ x, p² ≡ a}` over
its `≤ 2^{ω+1}` root residues gives `≤ 2^{ω+1}·(√x/q + 1)` primes, i.e.
`classSum(a) = (1/2)·#{…} ≤ 2^{ω}·(√x/q + 1)`.

## The `k ≥ 3` tail (named residual, NOT landed here — see the closing section)

`ppTerm = pp2Term + pp3Term` with `pp3Term ≥ 0` the cube-and-higher tail
(`pp3Term_nonneg`, `ppTerm_eq_pp2_add_pp3`), and `seqDiscrepancy` is subadditive
(`seqDiscrepancy_add_le`), so

  `seqDiscrepancy ppTerm x q ≤ seqDiscrepancy pp2Term x q + seqDiscrepancy pp3Term x q`.

The first summand is the landed bound above. The **second — the `k ≥ 3` tail — is
the named residual**, and it is a Fable/human-tier obligation, not a floor that a
same-tier attempt can close:

  The tail `∑_{k≥3}(1/k)·#{p^k ≤ x, p^k ≡ a}` needs, per class, the `/q` saving.
  A bare additive `x^{1/3}·polylog` per `q` sums to `x^{θ+1/3} ≫ x` (the assembly
  breaks), so the tail MUST carry `#{k-th roots of a mod q}·(x^{1/k}/q + 1)` for
  EVERY `k ≥ 3` — a general-`k` composite-modulus root count. `PpRootCyc`'s
  `card_pow_eq_le_gcd` gives the per-cyclic-factor count `gcd(k, φ)` for general
  `k`, but (i) there is no landed general-`k` CRT fold (`crt_sq_step` is `k = 2`
  only), and (ii) summing the resulting `∏ gcd(k, φ(p^e)) ≤ k^{ω(q)}` root counts
  needs `Σ_{q≤Q} 3^{ω(q)}/q` (and higher), which the landed `GehPp2` sums (`2^{ω}`,
  `τ`, `1/φ` only) do NOT provide. Both gaps are recorded in the `GehPp2` obstruction
  ledger as the Fable-tier `ppLevel_holds` assembly obligation. This node discharges
  the `k = 2` mass and names the tail precisely; per the Zeno discipline that is the
  in-tier success condition.
-/

open Finset

namespace Salt.Maynard

/-- `n` is a prime square: its integer square root is prime and squares back to `n`.
Decidable (both conjuncts are), and equivalent to `∃ p, p.Prime ∧ n = p^2`. -/
def isPrimeSq (n : ℕ) : Prop := (Nat.sqrt n).Prime ∧ (Nat.sqrt n) ^ 2 = n

instance (n : ℕ) : Decidable (isPrimeSq n) := by unfold isPrimeSq; infer_instance

@[simp] lemma isPrimeSq_iff (n : ℕ) :
    isPrimeSq n ↔ (Nat.sqrt n).Prime ∧ (Nat.sqrt n) ^ 2 = n := Iff.rfl

/-- The `k = 2` (prime-square) part of the prime-power correction: value `1/2` on
prime squares, `0` elsewhere. Equal to `ppTerm` on prime squares (both `1/2`) and
dominated by it everywhere (`pp2Term_le_ppTerm`). -/
noncomputable def pp2Term (n : ℕ) : ℝ := if isPrimeSq n then (1 / 2 : ℝ) else 0

/-- `pp2Term ≥ 0`. -/
lemma pp2Term_nonneg (n : ℕ) : 0 ≤ pp2Term n := by
  unfold pp2Term; split <;> norm_num

/-- **Units bridge: residue-form square-root count.** For `q ≥ 2` and a reduced
residue `a` (`Coprime a q`, `a < q`), the number of residues `r ∈ [0,q)` coprime to
`q` with `r² ≡ a (mod q)` is `≤ 2^{ω(q)+1}`. The map `r ↦ ZMod.unitOfCoprime r`
injects this residue set into the `(ZMod q)ˣ` square-root fiber of `â`, whose card is
bounded by the landed `card_sq_eq_units_le`. -/
lemma card_sq_residues_le {q : ℕ} (hq : 1 ≤ q) {a : ℕ} (ha : Nat.Coprime a q)
    (ha2 : a < q) :
    (((Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ 2 % q = a)).card : ℝ)
      ≤ 2 ^ (q.primeFactors.card + 1) := by
  rcases lt_or_ge q 2 with hq1 | hq
  · -- `q = 1`: the residue set sits inside `range 1`, so has ≤ 1 element ≤ 2.
    interval_cases q
    · have hle : (((Finset.range 1).filter
          (fun r => Nat.Coprime r 1 ∧ r ^ 2 % 1 = a)).card : ℝ) ≤ 1 := by
        calc (((Finset.range 1).filter (fun r => Nat.Coprime r 1 ∧ r ^ 2 % 1 = a)).card : ℝ)
            ≤ ((Finset.range 1).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
          _ = 1 := by rw [Finset.card_range]; norm_num
      exact hle.trans (one_le_pow₀ (by norm_num))
  haveI : NeZero q := ⟨by omega⟩
  set â : (ZMod q)ˣ := ZMod.unitOfCoprime a ha with hâ
  -- the (partial) map into units
  set f : ℕ → (ZMod q)ˣ :=
    fun r => if h : Nat.Coprime r q then ZMod.unitOfCoprime r h else 1 with hf
  have hmaps : ∀ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ 2 % q = a),
      f r ∈ Finset.univ.filter (fun u : (ZMod q)ˣ => u ^ 2 = â) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨_hrq, hcop, hr2⟩ := hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hf]
    rw [dif_pos hcop]
    apply Units.ext
    have hpow : ((ZMod.unitOfCoprime r hcop ^ 2 : (ZMod q)ˣ) : ZMod q) = (r : ZMod q) ^ 2 := by
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
    rw [hpow, hâ, ZMod.coe_unitOfCoprime, ← Nat.cast_pow]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by rw [hr2, Nat.mod_eq_of_lt ha2])
  have hinj : Set.InjOn f
      ↑((Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ 2 % q = a)) := by
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
  have hunits := card_sq_eq_units_le q hq â
  calc (((Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ 2 % q = a)).card : ℝ)
      ≤ ((Finset.univ.filter (fun u : (ZMod q)ˣ => u ^ 2 = â)).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (2 : ℝ) ^ (q.primeFactors.card + 1) := by exact_mod_cast hunits

/-- `(Nat.sqrt x : ℝ) ≤ Real.sqrt x`. -/
lemma natSqrt_le_realSqrt (x : ℕ) : (Nat.sqrt x : ℝ) ≤ Real.sqrt x := by
  rw [show (Nat.sqrt x : ℝ) = Real.sqrt ((Nat.sqrt x : ℝ) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have h : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' x
  exact_mod_cast h

/-- **The prime-square residue-class count.** For `q ≥ 1` and a reduced residue `a`
(`Coprime a q`, `a < q`), the number of primes `p ≤ √x` with `p² ≡ a (mod q)` is
`≤ 2^{ω(q)+1}·(√x/q + 1)`. Fibers `{p : p² ≡ a}` over the `≤ 2^{ω(q)+1}` root
residues `r` with `r² ≡ a`; each fiber contributes `≤ √x/q + 1` primes `p ≡ r`. -/
lemma card_primeSq_class_le {x q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q) (ha2 : a < q) :
    (((Finset.Icc 1 (Nat.sqrt x)).filter (fun p => p.Prime ∧ p ^ 2 % q = a)).card : ℝ)
      ≤ 2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1) := by
  classical
  set R := (Finset.range q).filter (fun r => Nat.Coprime r q ∧ r ^ 2 % q = a) with hR
  set P := (Finset.Icc 1 (Nat.sqrt x)).filter (fun p => p.Prime ∧ p ^ 2 % q = a) with hP
  have hq0 : 0 < q := hq
  -- every `p ∈ P` lands in a root residue class `p % q ∈ R`
  have hmaps : ∀ p ∈ P, p % q ∈ R := by
    intro p hp
    simp only [hP, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨_hpI, _hpprime, hpmod⟩ := hp
    -- `p` is coprime to `q` (as `a = p² mod q` is a unit)
    have hcop2 : Nat.Coprime (p ^ 2) q := by
      have h := ha
      unfold Nat.Coprime at h ⊢
      rw [Nat.gcd_comm, Nat.gcd_rec, hpmod]; exact h
    have hcopp : Nat.Coprime p q :=
      Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by norm_num)) hcop2
    have hcoppmod : Nat.Coprime (p % q) q := by
      unfold Nat.Coprime
      rw [← Nat.gcd_rec, Nat.gcd_comm]; exact hcopp
    simp only [hR, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hq0, hcoppmod, by rw [← Nat.pow_mod]; exact hpmod⟩
  -- fiber decomposition
  have hcard : P.card = ∑ r ∈ R, (P.filter (fun p => p % q = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  -- per-fiber interval bound
  have hbound : ∀ r ∈ R, ((P.filter (fun p => p % q = r)).card : ℝ)
      ≤ (Nat.sqrt x : ℝ) / q + 1 := by
    intro r _
    refine le_trans ?_ (card_ap_le (z := Nat.sqrt x) hq r)
    have hsub : P.filter (fun p => p % q = r)
        ⊆ (Finset.Icc 1 (Nat.sqrt x)).filter (fun n => n % q = r) := by
      intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.1.1, hp.2⟩
    exact_mod_cast Finset.card_le_card hsub
  have hRcard : (R.card : ℝ) ≤ 2 ^ (q.primeFactors.card + 1) := card_sq_residues_le hq ha ha2
  have hnn : (0 : ℝ) ≤ (Nat.sqrt x : ℝ) / q + 1 := by positivity
  calc (P.card : ℝ)
      = ∑ r ∈ R, ((P.filter (fun p => p % q = r)).card : ℝ) := by rw [hcard, Nat.cast_sum]
    _ ≤ ∑ _r ∈ R, ((Nat.sqrt x : ℝ) / q + 1) := Finset.sum_le_sum hbound
    _ = (R.card : ℝ) * ((Nat.sqrt x : ℝ) / q + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (q.primeFactors.card + 1) * ((Nat.sqrt x : ℝ) / q + 1) :=
        mul_le_mul_of_nonneg_right hRcard hnn
    _ ≤ 2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        gcongr
        exact natSqrt_le_realSqrt x

/-- **Per-reduced-class bound.** For `q ≥ 1` and a reduced residue `a`, the residue
class sum of `pp2Term` is `≤ 2^{ω(q)}·(√x/q + 1)`. Rewrites the sum as
`(1/2)·#{prime squares `p² ≤ x` with `p² ≡ a`}`, injects `n ↦ Nat.sqrt n` into the
prime count `card_primeSq_class_le`, and halves the `2^{ω+1}` bound to `2^{ω}`. -/
lemma classSum_pp2_le {x q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q) (ha2 : a < q) :
    |∑ n ∈ Finset.Icc 1 x, if n % q = a then pp2Term n else 0|
      ≤ 2 ^ q.primeFactors.card * (Real.sqrt x / q + 1) := by
  classical
  set T := (Finset.Icc 1 x).filter (fun n => n % q = a ∧ isPrimeSq n) with hT
  set P := (Finset.Icc 1 (Nat.sqrt x)).filter (fun p => p.Prime ∧ p ^ 2 % q = a) with hP
  -- the class sum equals `(1/2)·|T|`
  have hsum : (∑ n ∈ Finset.Icc 1 x, if n % q = a then pp2Term n else 0)
      = (1 / 2 : ℝ) * (T.card : ℝ) := by
    have hcongr : ∀ n ∈ Finset.Icc 1 x, (if n % q = a then pp2Term n else 0)
        = (1 / 2 : ℝ) * (if (n % q = a ∧ isPrimeSq n) then (1 : ℝ) else 0) := by
      intro n _
      unfold pp2Term
      by_cases h1 : n % q = a
      · by_cases h2 : isPrimeSq n <;> simp_all
      · simp [h1]
    rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, Finset.sum_boole, hT]
  -- `|T| ≤ |P|` via `n ↦ Nat.sqrt n`
  have hTP : T.card ≤ P.card := by
    apply Finset.card_le_card_of_injOn Nat.sqrt
    · intro n hn
      rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨_hn1, hnx⟩, hnmod, hps⟩ := hn
      obtain ⟨hpprime, hpsq⟩ := (isPrimeSq_iff n).mp hps
      rw [Finset.mem_coe, hP, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hpprime.one_lt.le, ?_⟩, hpprime, ?_⟩
      · exact Nat.le_sqrt'.mpr (by rw [hpsq]; exact hnx)
      · rw [hpsq]; exact hnmod
    · intro n hn n' hn' heq
      rw [Finset.mem_coe, hT, Finset.mem_filter] at hn hn'
      have e1 : (Nat.sqrt n) ^ 2 = n := ((isPrimeSq_iff n).mp hn.2.2).2
      have e2 : (Nat.sqrt n') ^ 2 = n' := ((isPrimeSq_iff n').mp hn'.2.2).2
      rw [← e1, ← e2, heq]
  -- assemble
  have hkey : (T.card : ℝ) ≤ 2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1) :=
    le_trans (by exact_mod_cast hTP) (card_primeSq_class_le hq ha ha2)
  rw [hsum, abs_of_nonneg (by positivity)]
  calc (1 / 2 : ℝ) * (T.card : ℝ)
      ≤ (1 / 2 : ℝ) * (2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1)) := by
        apply mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ = 2 ^ q.primeFactors.card * (Real.sqrt x / q + 1) := by
        rw [pow_succ]; ring

/-- **The `k = 2` per-`q` discrepancy bound (clean form).** For `q ≥ 1`,
`seqDiscrepancy pp2Term x q ≤ 2^{ω(q)+1}·(√x/q + 1)`. The coprime mean is absorbed
into the same per-class bound by `seqDiscrepancy_le_two_classBd` (the mean is the
average of the `φ(q)` reduced-class sums), so no separate mean term appears. -/
theorem seqDiscrepancy_pp2Term_le (x q : ℕ) (hq : 1 ≤ q) :
    seqDiscrepancy pp2Term x q
      ≤ 2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1) := by
  have hclass : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      |∑ n ∈ Finset.Icc 1 x, if n % q = a then pp2Term n else 0|
        ≤ 2 ^ q.primeFactors.card * (Real.sqrt x / q + 1) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    exact classSum_pp2_le hq ha.2 ha.1
  have h := seqDiscrepancy_le_two_classBd (f := pp2Term) (by omega : q ≠ 0) hclass
  refine h.trans_eq ?_
  rw [pow_succ]; ring

/-- **The `k = 2` per-`q` discrepancy bound (assembly shape).** There is a positive
constant `C` such that for `x ≥ 2`, `q ≥ 1`,

  `seqDiscrepancy pp2Term x q`
    `≤ C·(2^{ω(q)}·(√x/q + 1)·log x + √x·log x/φ(q))`.

Summed over `q ≤ x^θ` with the landed `GehPp2` sums this is `≪ √x·log²x + x^θ·log x`.
`C = 2/log 2`; the `√x·log x/φ(q)` term rides free (the clean bound needs only the
residue part). -/
theorem seqDiscrepancy_pp2Term_bound :
    ∃ C, 0 < C ∧ ∀ x q : ℕ, 2 ≤ x → 1 ≤ q →
      seqDiscrepancy pp2Term x q
        ≤ C * (2 ^ q.primeFactors.card * (Real.sqrt x / q + 1) * Real.log x
               + Real.sqrt x * Real.log x / q.totient) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 / Real.log 2, by positivity, ?_⟩
  intro x q hx hq
  have hlogx : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hlogxpos : 0 ≤ Real.log x := le_trans hlog2.le hlogx
  have hCpos : (0 : ℝ) ≤ 2 / Real.log 2 := (div_pos (by norm_num) hlog2).le
  set A : ℝ := 2 ^ q.primeFactors.card * (Real.sqrt x / q + 1) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hbase : seqDiscrepancy pp2Term x q ≤ 2 * A := by
    have h2A : (2 : ℝ) ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1) = 2 * A := by
      rw [hA, pow_succ]; ring
    rw [← h2A]; exact seqDiscrepancy_pp2Term_le x q hq
  have hstep1 : 2 * A ≤ (2 / Real.log 2) * A * Real.log x := by
    have h1 : (1 : ℝ) ≤ Real.log x / Real.log 2 := (one_le_div hlog2).mpr hlogx
    have h2 : (2 / Real.log 2) * A * Real.log x = 2 * A * (Real.log x / Real.log 2) := by ring
    rw [h2]; exact le_mul_of_one_le_right (by positivity) h1
  have hextra : 0 ≤ (2 / Real.log 2) * (Real.sqrt x * Real.log x / q.totient) :=
    mul_nonneg hCpos (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlogxpos) (Nat.cast_nonneg _))
  calc seqDiscrepancy pp2Term x q
      ≤ 2 * A := hbase
    _ ≤ (2 / Real.log 2) * A * Real.log x := hstep1
    _ ≤ (2 / Real.log 2) * (A * Real.log x + Real.sqrt x * Real.log x / q.totient) := by
        rw [mul_add, mul_assoc]; exact le_add_of_nonneg_right hextra

/-! ## Folding into `ppTerm`: the subadditive split and the named `k ≥ 3` tail -/

/-- On a prime square, the prime-power correction is exactly `1/2`:
`Λ(p²)/log(p²) = log p/(2 log p) = 1/2`, and `p²` is not prime. -/
lemma ppTerm_pow_two {p : ℕ} (hp : p.Prime) : Salt.BV.ppTerm (p ^ 2) = 1 / 2 := by
  have hplog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hΛ : ArithmeticFunction.vonMangoldt (p ^ 2) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hnp : ¬ (p ^ 2).Prime := Nat.Prime.not_prime_pow (by norm_num)
  have hne : Real.log p ≠ 0 := hplog.ne'
  unfold Salt.BV.ppTerm
  rw [hΛ, if_neg hnp, sub_zero, Nat.cast_pow, Real.log_pow]
  push_cast
  field_simp

/-- `pp2Term ≤ ppTerm`: equality (`= 1/2`) on prime squares, and `pp2Term = 0 ≤
ppTerm` elsewhere. -/
lemma pp2Term_le_ppTerm (n : ℕ) : pp2Term n ≤ Salt.BV.ppTerm n := by
  unfold pp2Term
  by_cases h : isPrimeSq n
  · rw [if_pos h]
    obtain ⟨hprime, hsq⟩ := (isPrimeSq_iff n).mp h
    rw [← hsq]
    exact le_of_eq (ppTerm_pow_two hprime).symm
  · rw [if_neg h]; exact Salt.BV.ppTerm_nonneg n

/-- The `k ≥ 3` (cube-and-higher prime power) tail of the prime-power correction:
`ppTerm − pp2Term`. Nonnegative (`pp3Term_nonneg`); `ppTerm = pp2Term + pp3Term`. -/
noncomputable def pp3Term (n : ℕ) : ℝ := Salt.BV.ppTerm n - pp2Term n

/-- The tail weight is nonnegative. -/
lemma pp3Term_nonneg (n : ℕ) : 0 ≤ pp3Term n := sub_nonneg.mpr (pp2Term_le_ppTerm n)

/-- The correction splits into its square part and its `k ≥ 3` tail. -/
lemma ppTerm_eq_pp2_add_pp3 (n : ℕ) : Salt.BV.ppTerm n = pp2Term n + pp3Term n := by
  unfold pp3Term; ring

/-- **The fold into `ppTerm` (the shape `PpLevel` sums), with the tail named.** By
subadditivity of `seqDiscrepancy` (`seqDiscrepancy_add_le`, landed) applied to
`ppTerm = pp2Term + pp3Term`, the full prime-power-correction discrepancy is the
landed `k = 2` bound plus the `seqDiscrepancy` of the `k ≥ 3` tail `pp3Term`.

The `pp3Term` summand is the **named residual** flagged in the module docstring:
closing it needs general-`k` composite-modulus root counts and the `Σ 3^{ω(q)}/q`
sums, neither landed — a Fable/human-tier obligation. The assembly consumes the
first summand here for the dominant mass; the tail is carried explicitly. -/
theorem seqDiscrepancy_ppTerm_le_pp2_add_tail (x q : ℕ) (hq : 1 ≤ q) :
    seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q
      ≤ 2 ^ (q.primeFactors.card + 1) * (Real.sqrt x / q + 1)
        + seqDiscrepancy pp3Term x q := by
  have hsplit : (fun n => Salt.BV.ppTerm n) = (fun n => pp2Term n + pp3Term n) := by
    funext n; exact ppTerm_eq_pp2_add_pp3 n
  rw [hsplit]
  refine (seqDiscrepancy_add_le pp2Term pp3Term x q).trans ?_
  gcongr
  exact seqDiscrepancy_pp2Term_le x q hq

end Salt.Maynard
