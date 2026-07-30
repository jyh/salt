/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MobiusChiRamare

/-!
# ⟦D3 — CARRIER PAGE 2⟧ THE UNION-MASK TWIN of the `g_r` perturbation

Design: the 0730 council's item **C5** (`docs/blueprints/flags.md`, ⟦THE 0730 COUNCIL⟧) and
`docs/exploration/a4-bridge-freeze-0730.md` §"D3 re-priced".  `MobiusChiRamare.lean` (⟦O6⟧)
lands the Ramaré-damped twisted Möbius rate at a SINGLE window `[P,Q]`.  D3's consumer runs
at `𝒥 = {1,2}` — **two disjoint blocks** `[P₁,Q₁]`, `[P₂,Q₂]` with `Q₁ < P₂`
(`Sec9Glue.MemS`/`gJ`, `CofactorSupplier.pieceDatum`) — and the union of two disjoint
intervals **is not an interval**, so no instantiation of O6 reaches it.  This file mints the
twins.  Purely ADDITIVE: no landed declaration is touched.

## THE SHAPE OF THE GENERALIZATION (and why it is the honest one)

O6's argument never uses that `[P,Q]` is an *interval*; it uses only that the damping
exponent `ω(·)` counts the distinct prime factors lying in some fixed SET of primes.  So this
file carries a **prime mask** `mask : ℕ → Bool` and re-runs O6 verbatim at

  `ω(n; mask) = #{p ∣ n : mask p}`,  `g_r(n) = r^{ω(n;mask)}`,

with the Euler product

  `D(μ·g_r)(s) = (1/ζ(s)) · ∏_{mask p} (1 − r·p^{−s})/(1 − p^{−s})`

and the same closed-form carrier `w_r(n) = (1−r)^{ω(n;mask)}` on the mask-smooth support.
The refuter's local factor `(1 − g₁g₂(p)p^{−s})/(1 − p^{−s})` is this file's window factor at
`mask = mask₁ ∨ mask₂`: **the two-block mask is the product of the two disjoint-interval
indicators**, and §7 proves the corresponding statement on the damping exponent,

  `ω(n; [P₁,Q₁] ∪ [P₂,Q₂]) = ω(n;P₁,Q₁) + ω(n;P₂,Q₂)`  when `Q₁ < P₂`
  (`unionOmega_eq_add_of_lt`), hence  `r^{ω(n;∪)} = r^{ω₁(n)}·r^{ω₂(n)}`
  (`unionDamp_eq_mul`),

which is the bridge to the corpus's own `blockOmega` — the exponent `RamWeight.ramRdamp` and
`Decomp.ramareWeight` read.  Generalizing to a mask (rather than duplicating O6 for a bespoke
two-interval carrier) is what makes any `𝒥` free later: `𝒥 = {1,…,J}` is one more
instantiation, at zero further bytes.

§7 also proves that the LANDED single-window carriers are literally the `blockMask P Q`
instance of this file's (`maskOmega_blockMask`, `maskTailWeight_blockMask`,
`muGrMask_blockMask`, `MmuGrChiMask_blockMask`, `MmuRamChiMask_blockMask`) — the twin-fidelity
check: nothing here is a *different* object dressed up.

## WHAT IS A HYPOTHESIS (unchanged from O6, at the union window)

Exactly as in O6, the `b > √y` row is the heart and is NOT discharged here: the mass and the
tail are NAMED IN-STATEMENT hypotheses, now at the UNION window,

* `hmass : ∑_{b ≤ √y} w_r(b)/b ≤ M`  — the ℓ¹(1/n) mask mass;
* `htail : ∑_{√y < b ≤ y} w_r(b)/b ≤ (log y)^{−A}` — the Rankin residue.

At `r = 0` the mass is `∏_{mask p}(1 − 1/p)^{−1}`; over two disjoint blocks that is the
PRODUCT of the two single-block masses, so the landed Mertens window page
`Salt.MR.blockWindow_mertens_const` (`CofactorDist.lean:139`) prices it as
`≍ (log Q₁/log P₁)·(log Q₂/log P₂)` — the union window's own genre.  That Euler-product
evaluation is NOT performed here (`CofactorDist` sits outside this file's import cone); it is
named as the consumer's route, and `maskTailWeight_le_zero_param` makes `r = 0` the worst
case so both hypotheses are `r`-free.

⟦the four log scales⟧ `log y`, `log⌊y/b⌋` (where the μ-rate fires — the `4^A` and the one
conductor exponent are paid there), `log √y ≥ (log y)/4`, and the WINDOW scale
`log Q_i/log P_i` (confined to `M, ε`).  `P₁,Q₁,P₂,Q₂` appear nowhere else.

## Prices — IDENTICAL to O6's (the mask costs nothing)

Conductor `q ≤ (log y)^12 → (log y)^11`; height `|t| ≤ y → |t| ≤ ⌊√y⌋` sharply; log-scale
factor `4^A`.  One fold, one exponent, one halving: the mask enters only through `M` and `ε`.

## Contents

* **§1** `MaskPrimeDivs`, `maskOmega`, `MaskSmooth` — the mask window count and smoothness,
  with the O6 facts they need (`maskOmega_one`, `maskOmega_mul_coprime`,
  `maskOmega_prime_pow`).
* **§2** `muGrMask` — the damped Möbius datum, and its multiplicativity.
* **§3** `maskTailWeight` (`= w_r`), positivity, support, the `r = 0` indicator, antitonicity
  in `r`, multiplicativity, the prime-power coefficients, THE VERIFICATION
  `maskTailWeight_eq_zeta_mul_muGrMask`, and the convolution identity.
* **§4** `MmuGrChiMask` and the twisted hyperbola fold `MmuGrChiMask_eq_sum` (UNCONDITIONAL).
* **§5** `norm_MmuGrChiMask_le_split` and the deliverable `MmuGrChiMask_rate`.
* **§6** `MmuRamChiMask`, `MmuRamChiMask_eq_integral`, `norm_MmuRamChiMask_le_of_uniform`, and
  the Ramaré-WEIGHTED deliverable `MmuRamChiMask_rate`.
* **§7** THE TWO-BLOCK INSTANCE: `blockMask`, `unionMask`, `unionOmega`, `UnionSmooth`,
  `muGrU`, `ramTailWeightU`, `MmuGrChiU`, `MmuRamChiU`, the disjointness additivity
  `unionOmega_eq_add_of_lt` / `unionDamp_eq_mul`, the single-window bridges, and the terminal
  twins `MmuGrChiU_rate`, `MmuRamChiU_rate`.

Explicit constants throughout; no `O(·)` in any statement.
-/

open scoped BigOperators

namespace Salt.MR

/-! ## §1 — the prime mask, its window count and its smooth numbers -/

/-- **The masked prime divisors of `n`** — the distinct primes `p ∣ n` with `mask p`.  The
mask generalization of `Salt.MR.BlockPrimeDivs`: `[P,Q]` is replaced by an arbitrary
decidable set of primes, which is what the `𝒥 = {1,2}` union of two disjoint blocks needs
(§7). -/
def MaskPrimeDivs (mask : ℕ → Bool) (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => mask p = true)

/-- `ω(n; mask)` — the number of distinct masked primes dividing `n`; the mask twin of
`Salt.MR.blockOmega`. -/
def maskOmega (mask : ℕ → Bool) (n : ℕ) : ℕ := (MaskPrimeDivs mask n).card

/-- **Mask smoothness**: every prime factor of `n` is masked.  Vacuously true at `n = 0` and
`n = 1` (`Nat.primeFactors 0 = Nat.primeFactors 1 = ∅`), which is why `maskTailWeight`
carries an explicit `n ≠ 0` guard — exactly as `WindowSmooth`/`ramTailWeight` do. -/
def MaskSmooth (mask : ℕ → Bool) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, mask p = true

instance decidableMaskSmooth (mask : ℕ → Bool) (n : ℕ) : Decidable (MaskSmooth mask n) := by
  unfold MaskSmooth; infer_instance

@[simp] lemma maskOmega_one (mask : ℕ → Bool) : maskOmega mask 1 = 0 := by
  simp [maskOmega, MaskPrimeDivs]

lemma maskSmooth_one (mask : ℕ → Bool) : MaskSmooth mask 1 := by
  intro p hp; simp at hp

/-- The masked prime divisors of a coprime product split as a disjoint union — the mask twin
of `Salt.MR.blockPrimeDivs_mul_coprime`. -/
lemma maskPrimeDivs_mul_coprime (mask : ℕ → Bool) {m n : ℕ} (hco : m.Coprime n) :
    MaskPrimeDivs mask (m * n) = MaskPrimeDivs mask m ∪ MaskPrimeDivs mask n := by
  unfold MaskPrimeDivs
  rw [Nat.Coprime.primeFactors_mul hco, Finset.filter_union]

/-- **Additivity on coprimes** — the fact `μ·g_r`'s multiplicativity rests on, and the one
the Ramaré weight `1/(ω+1)` itself lacks.  The mask twin of
`Salt.MR.blockOmega_mul_coprime`. -/
theorem maskOmega_mul_coprime (mask : ℕ → Bool) {m n : ℕ} (hco : m.Coprime n) :
    maskOmega mask (m * n) = maskOmega mask m + maskOmega mask n := by
  unfold maskOmega
  rw [maskPrimeDivs_mul_coprime mask hco]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hco.disjoint_primeFactors)

/-- `ω(p^k; mask)` is `1` or `0` according as `p` is masked or not (`k ≥ 1`). -/
theorem maskOmega_prime_pow {mask : ℕ → Bool} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    maskOmega mask (p ^ k) = if mask p = true then 1 else 0 := by
  unfold maskOmega MaskPrimeDivs
  rw [Nat.primeFactors_prime_pow hk hp, Finset.filter_singleton]
  by_cases h : mask p = true
  · rw [if_pos h, if_pos h, Finset.card_singleton]
  · rw [if_neg h, if_neg h, Finset.card_empty]

theorem maskSmooth_prime_pow_iff {mask : ℕ → Bool} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    MaskSmooth mask (p ^ k) ↔ mask p = true := by
  unfold MaskSmooth
  rw [Nat.primeFactors_prime_pow hk hp]
  simp

/-! ## §2 — the damped Möbius datum `μ·g_r` at the mask -/

/-- **The masked damped Möbius datum** `(μ·g_r)(m) = μ(m)·r^{ω(m;mask)}` — the mask twin of
`Salt.MR.muGr`.  Unconditional: at `m = 0` the value is `0` because `μ 0 = 0`. -/
noncomputable def muGrMask (mask : ℕ → Bool) (r : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => ((ArithmeticFunction.moebius m : ℤ) : ℝ) * r ^ maskOmega mask m, by simp⟩

@[simp] lemma muGrMask_apply (mask : ℕ → Bool) (r : ℝ) (m : ℕ) :
    muGrMask mask r m = ((ArithmeticFunction.moebius m : ℤ) : ℝ) * r ^ maskOmega mask m := rfl

/-- **`μ·g_r` is multiplicative** — `μ` is, and `ω(·;mask)` is additive on coprimes. -/
theorem muGrMask_isMultiplicative (mask : ℕ → Bool) (r : ℝ) :
    (muGrMask mask r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, ?_⟩
  intro m n _ _ hmn
  simp only [muGrMask_apply]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
    maskOmega_mul_coprime mask hmn, pow_add]
  push_cast
  ring

/-! ## §3 — the tail weight `w_r` at the mask, and the convolution identity -/

/-- **THE TAIL WEIGHT `w_r` AT THE MASK** — the multiplicative function with local factor
`(1 − r p^{−s})/(1 − p^{−s}) = 1 + (1−r)∑_{k≥1}p^{−ks}` at masked primes and local factor `1`
elsewhere, carried by its CLOSED FORM

  `w_r(n) = (1−r)^{ω(n;mask)}` if `n ≠ 0` and every prime factor of `n` is masked,
  `w_r(n) = 0` otherwise.

Verified against the Euler factor in `maskTailWeight_eq_zeta_mul_muGrMask`.  The mask twin of
`Salt.MR.ramTailWeight` — and, at `mask = blockMask P Q`, literally it
(`maskTailWeight_blockMask`). -/
noncomputable def maskTailWeight (mask : ℕ → Bool) (r : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ MaskSmooth mask n then (1 - r) ^ maskOmega mask n else 0, by simp⟩

@[simp] lemma maskTailWeight_apply (mask : ℕ → Bool) (r : ℝ) (n : ℕ) :
    maskTailWeight mask r n
      = if n ≠ 0 ∧ MaskSmooth mask n then (1 - r) ^ maskOmega mask n else 0 := rfl

lemma maskTailWeight_apply_of {mask : ℕ → Bool} (r : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hs : MaskSmooth mask n) : maskTailWeight mask r n = (1 - r) ^ maskOmega mask n := by
  simp [hn, hs]

lemma maskTailWeight_eq_zero_of_not_smooth {mask : ℕ → Bool} (r : ℝ) {n : ℕ}
    (hs : ¬ MaskSmooth mask n) : maskTailWeight mask r n = 0 := by
  simp [hs]

/-- **KEY POSITIVITY.**  For `r ≤ 1` every value of `w_r` is `≥ 0` — what lets the mass
hypotheses be stated on `w_r` itself rather than on `|w_r|`. -/
theorem maskTailWeight_nonneg {mask : ℕ → Bool} {r : ℝ} (hr1 : r ≤ 1) (n : ℕ) :
    0 ≤ maskTailWeight mask r n := by
  rw [maskTailWeight_apply]
  split_ifs with h
  · exact pow_nonneg (by linarith) _
  · exact le_refl 0

/-- **THE SUPPORT.**  `w_r` vanishes off the mask-smooth numbers — the fact that makes the
`∑_b w_r(b)/b` mass a WINDOW quantity rather than a `log y` quantity. -/
theorem maskTailWeight_support {mask : ℕ → Bool} {r : ℝ} {n : ℕ}
    (h : maskTailWeight mask r n ≠ 0) : n ≠ 0 ∧ MaskSmooth mask n := by
  by_contra hc
  rw [maskTailWeight_apply, if_neg hc] at h
  exact h rfl

/-- **The `r = 0` value is the mask-smooth INDICATOR**; by `maskTailWeight_le_zero_param` it
dominates every `w_r`, `r ∈ [0,1]`, so all mass/tail hypotheses can be discharged once, at
`r = 0`, uniformly in `r`. -/
theorem maskTailWeight_zero_param (mask : ℕ → Bool) (n : ℕ) :
    maskTailWeight mask 0 n = if n ≠ 0 ∧ MaskSmooth mask n then 1 else 0 := by
  rw [maskTailWeight_apply]
  split_ifs with h
  · norm_num
  · rfl

/-- **ANTITONICITY IN THE DAMPING.**  For `r ∈ [0,1]`, `w_r ≤ w_0` pointwise — the uniformity
that makes §6's `∫₀¹ dr` composition free. -/
theorem maskTailWeight_le_zero_param {mask : ℕ → Bool} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) : maskTailWeight mask r n ≤ maskTailWeight mask 0 n := by
  rw [maskTailWeight_apply, maskTailWeight_apply]
  split_ifs with h
  · have h1 : (1 - r) ^ maskOmega mask n ≤ (1 : ℝ) :=
      pow_le_one₀ (by linarith) (by linarith)
    simpa using h1
  · exact le_refl 0

/-- **`w_r` is multiplicative.**  Mask smoothness is multiplicative (`Nat.primeFactors_mul`)
and `ω(·;mask)` is additive on coprimes; off the smooth support both sides vanish. -/
theorem maskTailWeight_isMultiplicative (mask : ℕ → Bool) (r : ℝ) :
    (maskTailWeight mask r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [maskTailWeight_apply_of r one_ne_zero (maskSmooth_one mask), maskOmega_one, pow_zero]
  · intro m n hm hn hmn
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
      Nat.primeFactors_mul hm hn
    by_cases hsm : MaskSmooth mask m
    · by_cases hsn : MaskSmooth mask n
      · have hsmn : MaskSmooth mask (m * n) := by
          intro p hp
          rw [hpf, Finset.mem_union] at hp
          rcases hp with h | h
          · exact hsm p h
          · exact hsn p h
        rw [maskTailWeight_apply_of r hmn0 hsmn, maskTailWeight_apply_of r hm hsm,
          maskTailWeight_apply_of r hn hsn, maskOmega_mul_coprime mask hmn, pow_add]
      · have hnot : ¬ MaskSmooth mask (m * n) := fun hc =>
          hsn (fun p hp => hc p (by rw [hpf]; exact Finset.mem_union_right _ hp))
        rw [maskTailWeight_eq_zero_of_not_smooth r hnot,
          maskTailWeight_eq_zero_of_not_smooth r hsn, mul_zero]
    · have hnot : ¬ MaskSmooth mask (m * n) := fun hc =>
        hsm (fun p hp => hc p (by rw [hpf]; exact Finset.mem_union_left _ hp))
      rw [maskTailWeight_eq_zero_of_not_smooth r hnot,
        maskTailWeight_eq_zero_of_not_smooth r hsm, zero_mul]

/-- **THE CLOSED FORM'S PRIME-POWER VALUES — the auditable half of the verification.**  For
`k ≥ 1`, `w_r(p^k) = 1 − r` at a masked prime and `0` elsewhere: exactly the coefficients of
`(1 − r p^{−s})/(1 − p^{−s}) = 1 + (1−r)∑_{k≥1}p^{−ks}` (masked) and `1` (unmasked). -/
theorem maskTailWeight_prime_pow {mask : ℕ → Bool} {p k : ℕ} (r : ℝ) (hp : p.Prime)
    (hk : k ≠ 0) :
    maskTailWeight mask r (p ^ k) = if mask p = true then 1 - r else 0 := by
  by_cases hm : mask p = true
  · rw [maskTailWeight_apply_of r (pow_ne_zero _ hp.ne_zero)
      ((maskSmooth_prime_pow_iff hp hk).mpr hm), maskOmega_prime_pow hp hk,
      if_pos hm, pow_one, if_pos hm]
  · rw [maskTailWeight_eq_zero_of_not_smooth r
      (fun hc => hm ((maskSmooth_prime_pow_iff hp hk).mp hc)), if_neg hm]

/-- **THE VERIFICATION OF THE CLOSED FORM** (the mask twin of
`ramTailWeight_eq_zeta_mul_muGr`):

  `w_r = ζ ∗ (μ·g_r)`.

Both sides are multiplicative, so `IsMultiplicative.eq_iff_eq_on_prime_powers` reduces to
prime powers, where `(ζ ∗ (μ·g_r))(p^k) = 1 − r^{1_{mask}(p)}` (the `j ≥ 2` terms vanish with
`μ(p^j)`) — `1 − r` at a masked prime and `0` elsewhere, i.e. the closed form.  This is the
reading-off of the local factor announced in the header, and it is where the union of two
disjoint blocks is no harder than one block: the argument never inspects the mask. -/
theorem maskTailWeight_eq_zeta_mul_muGrMask (mask : ℕ → Bool) (r : ℝ) :
    maskTailWeight mask r
      = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
          * muGrMask mask r := by
  have hmulti :
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
        * muGrMask mask r).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul (muGrMask_isMultiplicative mask r)
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (maskTailWeight_isMultiplicative mask r) _ hmulti]
  intro p k hp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, (maskTailWeight_isMultiplicative mask r).map_one, hmulti.map_one]
  have hk0 : k ≠ 0 := by omega
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  have hsub : Finset.range 2 ⊆ Finset.range (k + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hzero : ∀ i ∈ Finset.range (k + 1), i ∉ Finset.range 2 →
      muGrMask mask r (p ^ i) = 0 := by
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [muGrMask_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega),
      if_neg (by omega)]
    simp
  rw [← Finset.sum_subset hsub hzero, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
    pow_one, muGrMask_apply, muGrMask_apply, maskOmega_one,
    ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one]
  have hmo : maskOmega mask p = if mask p = true then 1 else 0 := by
    have := maskOmega_prime_pow (mask := mask) (p := p) (k := 1) hp one_ne_zero
    rwa [pow_one] at this
  rw [maskTailWeight_prime_pow r hp hk0, hmo]
  by_cases hm : mask p = true
  · rw [if_pos hm, if_pos hm]
    push_cast
    ring
  · rw [if_neg hm, if_neg hm]
    push_cast
    ring

/-- **THE MÖBIUS-TRANSFORM CARRIER**: `w_r(n) = ∑_{d ∣ n} μ(d)·r^{ω(d;mask)}` — the
alternative form, free from the verification. -/
theorem maskTailWeight_eq_sum_divisors (mask : ℕ → Bool) (r : ℝ) (n : ℕ) :
    maskTailWeight mask r n
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * r ^ maskOmega mask d := by
  rw [maskTailWeight_eq_zeta_mul_muGrMask, ArithmeticFunction.coe_zeta_mul_apply]
  exact Finset.sum_congr rfl fun d _ => muGrMask_apply mask r d

/-- **THE CONVOLUTION IDENTITY, `ArithmeticFunction`-level**: `μ ∗ w_r = μ·g_r` at the mask.
Immediate from the verification and `μ ∗ ζ = 1`; UNCONDITIONAL. -/
theorem mu_mul_maskTailWeight (mask : ℕ → Bool) (r : ℝ) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * maskTailWeight mask r = muGrMask mask r := by
  rw [maskTailWeight_eq_zeta_mul_muGrMask, ← mul_assoc,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]

/-- **THE CONVOLUTION IDENTITY, pointwise** (the form the fold consumes):
`μ(m)·r^{ω(m;mask)} = ∑_{ab = m} μ(a)·w_r(b)`.  Holds at `m = 0` too. -/
theorem muGrMask_eq_sum_divisorsAntidiagonal (mask : ℕ → Bool) (r : ℝ) (m : ℕ) :
    ((ArithmeticFunction.moebius m : ℤ) : ℝ) * r ^ maskOmega mask m
      = ∑ ab ∈ m.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius ab.1 : ℤ) : ℝ) * maskTailWeight mask r ab.2 := by
  rw [← muGrMask_apply, ← mu_mul_maskTailWeight, ArithmeticFunction.mul_apply]
  exact Finset.sum_congr rfl fun ab _ => by rw [ArithmeticFunction.intCoe_apply]

/-! ## §4 — the twisted damped summatory function and the hyperbola fold -/

/-- **The masked twisted damped Möbius summatory function**
`M_{μg_rχ̄}(y) = ∑_{m ≤ y} μ(m)r^{ω(m;mask)}χ̄(m)m^{it}`, ℂ-valued.  ⟦barred χ⟧ the twist is
the corpus's `chiBarTwist`. -/
noncomputable def MmuGrChiMask {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (mask : ℕ → Bool)
    (r : ℝ) (y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 y, ((muGrMask mask r m : ℝ) : ℂ) * chiBarTwist χ t m

/-- **The twist distributes over `μ·g_r = μ ∗ w_r`** (for `m ≠ 0`), through `chiBarTwist_mul`.
⟦DEVIATION, inherited from `MobiusChiRamare`⟧ `LambdaRateTwisted.mul_apply_mul_twist` is
CITED, not instantiated: its `f g h` live in ONE ring while the carriers here are
`ArithmeticFunction ℝ` and the twist is ℂ-valued. -/
theorem muGrMask_twist_eq_sum_divisorsAntidiagonal {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (mask : ℕ → Bool) (r : ℝ) {m : ℕ} (hm : m ≠ 0) :
    ((muGrMask mask r m : ℝ) : ℂ) * chiBarTwist χ t m
      = ∑ ab ∈ m.divisorsAntidiagonal,
          (((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ) * chiBarTwist χ t ab.1)
            * (((maskTailWeight mask r ab.2 : ℝ) : ℂ) * chiBarTwist χ t ab.2) := by
  have hR := muGrMask_eq_sum_divisorsAntidiagonal mask r m
  have hC : ((muGrMask mask r m : ℝ) : ℂ)
      = ∑ ab ∈ m.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ)
            * ((maskTailWeight mask r ab.2 : ℝ) : ℂ) := by
    rw [muGrMask_apply, hR]
    push_cast
    rfl
  rw [hC, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ab hab => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hab
  obtain ⟨hprod, _⟩ := hab
  have ha : ab.1 ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hprod
    exact hm hprod.symm
  have hb : ab.2 ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hprod
    exact hm hprod.symm
  rw [← hprod, chiBarTwist_mul χ t ab.1 ab.2 ha hb]
  ring

/-- **THE TWISTED HYPERBOLA FOLD (UNCONDITIONAL)** at the mask:

  `∑_{m ≤ y} μ(m)g_r(m)χ̄(m)m^{it} = ∑_{b ≤ y} w_r(b)χ̄(b)b^{it} · M_{μχ̄}(⌊y/b⌋)`.

The mask twin of `Salt.MR.MmuGrChi_eq_sum`; the inner collapse is the LANDED
`Salt.MR.MmuChi_inner_dvd` (mask-blind, hence reused verbatim).  No hypothesis on `r` or the
mask. -/
theorem MmuGrChiMask_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (mask : ℕ → Bool)
    (r : ℝ) (y : ℕ) :
    MmuGrChiMask χ t mask r y
      = ∑ b ∈ Finset.Icc 1 y,
          (((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b) := by
  have hdivfilter : ∀ m : ℕ, 1 ≤ m → m ≤ y →
      (Finset.Icc 1 y).filter (fun b => b ∣ m) = m.divisors := by
    intro m h1 h2
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · exact fun h => ⟨h.2, by omega⟩
    · intro ⟨hb, _⟩
      have hbm : b ≤ m := Nat.le_of_dvd (by omega) hb
      have hb1 : 1 ≤ b := by
        rcases Nat.eq_zero_or_pos b with rfl | h
        · exact absurd (Nat.eq_zero_of_zero_dvd hb) (by omega)
        · exact h
      exact ⟨⟨hb1, by omega⟩, hb⟩
  have hpt : ∀ m ∈ Finset.Icc 1 y,
      ((muGrMask mask r m : ℝ) : ℂ) * chiBarTwist χ t m
        = ∑ b ∈ Finset.Icc 1 y,
            (if b ∣ m then
              (((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
                * (((ArithmeticFunction.moebius (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
             else 0) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    rw [muGrMask_twist_eq_sum_divisorsAntidiagonal χ t mask r hm0]
    rw [Nat.sum_divisorsAntidiagonal' (n := m)
      (f := fun a b => (((ArithmeticFunction.moebius a : ℤ) : ℂ) * chiBarTwist χ t a)
        * (((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b))]
    rw [← hdivfilter m hm.1 hm.2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · ring
    · rfl
  rw [MmuGrChiMask, Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  have hpull : ∀ m : ℕ,
      (if b ∣ m then
        (((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
          * (((ArithmeticFunction.moebius (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
       else 0)
      = (((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
          * (if b ∣ m then
              (((ArithmeticFunction.moebius (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
             else 0) := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => hpull m), ← Finset.mul_sum, ← Finset.sum_filter,
    MmuChi_inner_dvd χ t y b hb.1]

/-! ## §5 — the rate transfer -/

/-- **THE TWO-ROW SPLIT (UNCONDITIONAL)** at the mask — the mask twin of
`Salt.MR.norm_MmuGrChi_le_split`.  On the tail row only the crude `norm_MmuChi_le` is used;
`ε` is the honest name of that row's cost. -/
theorem norm_MmuGrChiMask_le_split {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (mask : ℕ → Bool) (r : ℝ) (y : ℕ) (hr1 : r ≤ 1) {B M ε : ℝ} (hB : 0 ≤ B)
    (hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y), ‖MmuChi χ t (y / b)‖ ≤ B * (y : ℝ) / (b : ℝ))
    (hmass : ∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask r b / (b : ℝ) ≤ M)
    (htail : ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask r b / (b : ℝ) ≤ ε) :
    ‖MmuGrChiMask χ t mask r y‖ ≤ B * M * (y : ℝ) + ε * (y : ℝ) := by
  have hwnn : ∀ n : ℕ, 0 ≤ maskTailWeight mask r n := fun n => maskTailWeight_nonneg hr1 n
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hsqle : Nat.sqrt y ≤ y := Nat.sqrt_le_self y
  have hcoef : ∀ b : ℕ,
      ‖((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b‖ ≤ maskTailWeight mask r b := by
    intro b
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hwnn b)]
    exact mul_le_of_le_one_right (hwnn b) (norm_chiBarTwist_le_one χ t b)
  have hIcc : Finset.Icc 1 y
      = Finset.Icc 1 (Nat.sqrt y) ∪ Finset.Ioc (Nat.sqrt y) y := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (Nat.sqrt y)) (Finset.Ioc (Nat.sqrt y) y) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_Ioc] at hb
    omega
  rw [MmuGrChiMask_eq_sum, hIcc, Finset.sum_union hdisj]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖(((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
          ≤ (B * (y : ℝ)) * (maskTailWeight mask r b / (b : ℝ)) := by
      intro b hb
      calc ‖(((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
          = ‖((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b‖
              * ‖MmuChi χ t (y / b)‖ := norm_mul _ _
        _ ≤ maskTailWeight mask r b * (B * (y : ℝ) / (b : ℝ)) :=
            mul_le_mul (hcoef b) (hsmall b hb) (norm_nonneg _) (hwnn b)
        _ = (B * (y : ℝ)) * (maskTailWeight mask r b / (b : ℝ)) := by ring
    calc ∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
            ‖(((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
        ≤ ∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
            (B * (y : ℝ)) * (maskTailWeight mask r b / (b : ℝ)) := Finset.sum_le_sum hterm
      _ = (B * (y : ℝ))
            * ∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask r b / (b : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (B * (y : ℝ)) * M := mul_le_mul_of_nonneg_left hmass (mul_nonneg hB hy0)
      _ = B * M * (y : ℝ) := by ring
  · refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ Finset.Ioc (Nat.sqrt y) y,
        ‖(((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
          ≤ (y : ℝ) * (maskTailWeight mask r b / (b : ℝ)) := by
      intro b _
      have hcrude : ‖MmuChi χ t (y / b)‖ ≤ (y : ℝ) / (b : ℝ) :=
        le_trans (norm_MmuChi_le χ t (y / b)) (Nat.cast_div_le (m := y) (n := b) (α := ℝ))
      calc ‖(((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
          = ‖((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b‖
              * ‖MmuChi χ t (y / b)‖ := norm_mul _ _
        _ ≤ maskTailWeight mask r b * ((y : ℝ) / (b : ℝ)) :=
            mul_le_mul (hcoef b) hcrude (norm_nonneg _) (hwnn b)
        _ = (y : ℝ) * (maskTailWeight mask r b / (b : ℝ)) := by ring
    calc ∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
            ‖(((maskTailWeight mask r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
        ≤ ∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
            (y : ℝ) * (maskTailWeight mask r b / (b : ℝ)) := Finset.sum_le_sum hterm
      _ = (y : ℝ)
            * ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask r b / (b : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (y : ℝ) * ε := mul_le_mul_of_nonneg_left htail hy0
      _ = ε * (y : ℝ) := by ring

/-- `log y → ∞` along ℕ, in eventual form (the mask-side twin of the private ones in
`LambdaRateTwisted` / `MobiusChiRamare`). -/
private lemma eventually_log_ge_mask (c : ℝ) : ∀ᶠ y : ℕ in Filter.atTop, c ≤ Real.log y := by
  have h : Filter.Tendsto (fun y : ℕ => Real.log (y : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- **THE DELIVERABLE — the masked damped twisted Möbius rate**, the mask twin of
`Salt.MR.MmuGrChi_rate`:

  `‖∑_{m ≤ y} μ(m)r^{ω(m;mask)}χ̄(m)m^{it}‖ ≤ C'·y/(log y)^A`,

uniformly over `q ≤ (log y)^11`, `|t| ≤ ⌊√y⌋`, the MASK, and `r ∈ [0,1]`.

Prices, unchanged from the single-window case (the mask is invisible to every one of them):
the conductor gate moves `(log y)^12 → (log y)^11` (the rate fires at `⌊y/b⌋ ≥ √y`, so one
exponent is spent at `log y ≥ 4^12`); the height gate transfers SHARPLY
(`⌊√y⌋ ≤ ⌊y/b⌋`); the log-scale price is `4^A`; `M` enters `C' = C·4^A·M + 1` linearly.
The mask enters ONLY through `M` and the tail — at a two-block union `M` is the product of
the two block masses (see the header).

`C'` and `x₀` do **not** depend on `r`, the mask, `q`, `χ` or `t`. -/
theorem MmuGrChiMask_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ, |t| ≤ (Nat.sqrt y : ℝ) →
          ∀ (mask : ℕ → Bool) (r : ℝ), 0 ≤ r → r ≤ 1 →
            (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask r b / (b : ℝ)) ≤ M →
            (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask r b / (b : ℝ))
                ≤ 1 / (Real.log y) ^ A →
            ‖MmuGrChiMask χ t mask r y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C, x₀mu, hCpos, hMmuBound⟩ := hMmu A hA
  have h4A : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hC'pos : (0 : ℝ) < C * (4 : ℝ) ^ A * M + 1 := by
    have h : (0 : ℝ) ≤ C * (4 : ℝ) ^ A * M :=
      mul_nonneg (mul_nonneg hCpos.le h4A.le) hM
    linarith
  have key : ∀ᶠ y : ℕ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ, |t| ≤ (Nat.sqrt y : ℝ) →
          ∀ (mask : ℕ → Bool) (r : ℝ), 0 ≤ r → r ≤ 1 →
            (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask r b / (b : ℝ)) ≤ M →
            (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask r b / (b : ℝ))
                ≤ 1 / (Real.log y) ^ A →
            ‖MmuGrChiMask χ t mask r y‖ ≤ (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
    filter_upwards [Filter.eventually_ge_atTop 16, Filter.eventually_ge_atTop (x₀mu ^ 2),
        eventually_log_ge_mask ((4 : ℝ) ^ (12 : ℕ))] with y hy16 hyx0 hlog4
    intro q _ χ hq t ht mask r hr0 hr1 hmass htail
    have hLpos : 0 < Real.log y := lt_of_lt_of_le (by positivity) hlog4
    have hL0 : (0 : ℝ) ≤ Real.log y := hLpos.le
    have hLApos : (0 : ℝ) < (Real.log y) ^ A := Real.rpow_pos_of_pos hLpos A
    have hs1 : 1 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by nlinarith [hy16])
    have hs_ge_x0 : x₀mu ≤ Nat.sqrt y := by
      rw [Nat.le_sqrt]
      calc x₀mu * x₀mu = x₀mu ^ 2 := by ring
        _ ≤ y := hyx0
    have hlogs : Real.log y / 4 ≤ Real.log (Nat.sqrt y) := Salt.TwinBar.log_natSqrt_ge hy16
    have hL4pos : 0 < Real.log y / 4 := by linarith
    have hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖MmuChi χ t (y / b)‖ ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * (y : ℝ) / (b : ℝ) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      obtain ⟨hb1, hbs⟩ := hb
      have hbpos : 0 < b := hb1
      have hts : Nat.sqrt y ≤ y / b := by
        rw [Nat.le_div_iff_mul_le hbpos]
        calc Nat.sqrt y * b ≤ Nat.sqrt y * Nat.sqrt y := by gcongr
          _ ≤ y := Nat.sqrt_le y
      have htx : x₀mu ≤ y / b := le_trans hs_ge_x0 hts
      have hlogt : Real.log y / 4 ≤ Real.log ((y / b : ℕ) : ℝ) := by
        refine le_trans hlogs ?_
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt y))
        exact_mod_cast hts
      have hgate : (q : ℝ) ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ (12 : ℕ) := by
        have hratio : (1 : ℝ) ≤ Real.log y / (4 : ℝ) ^ (12 : ℕ) :=
          (one_le_div (by positivity)).mpr hlog4
        have h11 : (Real.log y) ^ (11 : ℕ) ≤ (Real.log y / 4) ^ (12 : ℕ) := by
          calc (Real.log y) ^ (11 : ℕ) = (Real.log y) ^ (11 : ℕ) * 1 := by ring
            _ ≤ (Real.log y) ^ (11 : ℕ) * (Real.log y / (4 : ℝ) ^ (12 : ℕ)) :=
                mul_le_mul_of_nonneg_left hratio (pow_nonneg hL0 11)
            _ = (Real.log y / 4) ^ (12 : ℕ) := by rw [div_pow]; ring
        have h12 : (Real.log y / 4) ^ (12 : ℕ)
            ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ (12 : ℕ) := by
          have h04 : (0 : ℝ) ≤ Real.log y / 4 := by linarith
          gcongr
        linarith
      have hht : |t| ≤ ((y / b : ℕ) : ℝ) := le_trans ht (by exact_mod_cast hts)
      have hMt := hMmuBound (y / b) htx q χ hgate t hht
      have hrpow : (Real.log y / 4) ^ A ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ A :=
        Real.rpow_le_rpow hL4pos.le hlogt hA.le
      have hcast : ((y / b : ℕ) : ℝ) ≤ (y : ℝ) / (b : ℝ) :=
        Nat.cast_div_le (m := y) (n := b) (α := ℝ)
      calc ‖MmuChi χ t (y / b)‖
          ≤ C * ((y / b : ℕ) : ℝ) / (Real.log ((y / b : ℕ) : ℝ)) ^ A := hMt
        _ ≤ C * ((y / b : ℕ) : ℝ) / (Real.log y / 4) ^ A :=
              div_le_div_of_nonneg_left (mul_nonneg hCpos.le (Nat.cast_nonneg _))
                (Real.rpow_pos_of_pos hL4pos A) hrpow
        _ = C * (4 : ℝ) ^ A * ((y / b : ℕ) : ℝ) / (Real.log y) ^ A := by
              rw [Real.div_rpow hL0 (by norm_num), div_div_eq_mul_div]; ring
        _ ≤ C * (4 : ℝ) ^ A * ((y : ℝ) / (b : ℝ)) / (Real.log y) ^ A := by
              have hCoef : (0 : ℝ) ≤ C * (4 : ℝ) ^ A := mul_nonneg hCpos.le h4A.le
              gcongr
        _ = (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * (y : ℝ) / (b : ℝ) := by ring
    have hBnn : (0 : ℝ) ≤ C * (4 : ℝ) ^ A / (Real.log y) ^ A :=
      div_nonneg (mul_nonneg hCpos.le h4A.le) hLApos.le
    have hsplit := norm_MmuGrChiMask_le_split χ t mask r y hr1 hBnn hsmall hmass htail
    calc ‖MmuGrChiMask χ t mask r y‖
        ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * M * (y : ℝ)
            + (1 / (Real.log y) ^ A) * (y : ℝ) := hsplit
      _ = (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
          field_simp
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨C * (4 : ℝ) ^ A * M + 1, N, hC'pos, hN⟩

/-! ## §6 — the `∫₀¹ dr` composition at the mask -/

/-- **The Ramaré-WEIGHTED masked twisted Möbius summatory function**
`∑_{m ≤ y} μ(m)·(ω(m;mask)+1)^{−1}·χ̄(m)m^{it}` — the mask twin of `Salt.MR.MmuRamChi`. -/
noncomputable def MmuRamChiMask {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (mask : ℕ → Bool)
    (y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 y, ((ArithmeticFunction.moebius m : ℤ) : ℂ)
      * ((maskOmega mask m : ℂ) + 1)⁻¹ * chiBarTwist χ t m

/-- **The weight as a `[0,1]` average of the dampings** — the LANDED `RamWeight` device
(`integral_cpow_unit`) at the mask: `M_{μ/(ω+1)χ̄}(y) = ∫₀¹ M_{μg_rχ̄}(y) dr`. -/
theorem MmuRamChiMask_eq_integral {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (mask : ℕ → Bool) (y : ℕ) :
    MmuRamChiMask χ t mask y = ∫ r in (0:ℝ)..1, MmuGrChiMask χ t mask r y := by
  have hMG : ∀ r : ℝ, MmuGrChiMask χ t mask r y
      = ∑ m ∈ Finset.Icc 1 y,
          (((ArithmeticFunction.moebius m : ℤ) : ℂ) * chiBarTwist χ t m)
            * ((r : ℝ) : ℂ) ^ maskOmega mask m := by
    intro r
    rw [MmuGrChiMask]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [muGrMask_apply]
    push_cast
    ring
  simp only [hMG]
  rw [intervalIntegral.integral_finsetSum (fun m _ => (by fun_prop : Continuous
    (fun r : ℝ => (((ArithmeticFunction.moebius m : ℤ) : ℂ) * chiBarTwist χ t m)
      * ((r : ℝ) : ℂ) ^ maskOmega mask m)).intervalIntegrable _ _)]
  rw [MmuRamChiMask]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cpow_unit]
  ring

/-- **THE EXIT SHAPE** (the mask twin of `norm_MmuRamChi_le_of_uniform`): a bound uniform over
`r ∈ [0,1]` is a bound on the Ramaré-WEIGHTED masked datum itself. -/
theorem norm_MmuRamChiMask_le_of_uniform {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (mask : ℕ → Bool) (y : ℕ) {B : ℝ}
    (h : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖MmuGrChiMask χ t mask r y‖ ≤ B) :
    ‖MmuRamChiMask χ t mask y‖ ≤ B := by
  rw [MmuRamChiMask_eq_integral]
  have hbd : ∀ r ∈ Set.uIoc (0 : ℝ) 1, ‖MmuGrChiMask χ t mask r y‖ ≤ B := by
    intro r hr
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    exact h r ⟨hr.1.le, hr.2⟩
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- **THE RAMARÉ-WEIGHTED MASKED DELIVERABLE** — the mask twin of `Salt.MR.MmuRamChi_rate`.
The hypotheses are the WORST-CASE (`r = 0`) mask-window quantities; `r`-uniformity of
`MmuGrChiMask_rate`'s constants plus `maskTailWeight_le_zero_param` make the `∫₀¹ dr`
composition free. -/
theorem MmuRamChiMask_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ, |t| ≤ (Nat.sqrt y : ℝ) →
          ∀ mask : ℕ → Bool,
            (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask 0 b / (b : ℝ)) ≤ M →
            (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask 0 b / (b : ℝ))
                ≤ 1 / (Real.log y) ^ A →
            ‖MmuRamChiMask χ t mask y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C', x₀, hC'pos, hbound⟩ := MmuGrChiMask_rate hMmu A hA hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro y hy q _ χ hq t ht mask hmass0 htail0
  refine norm_MmuRamChiMask_le_of_uniform χ t mask y ?_
  intro r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hmono : ∀ b : ℕ, maskTailWeight mask r b / (b : ℝ) ≤ maskTailWeight mask 0 b / (b : ℝ) := by
    intro b
    have h := maskTailWeight_le_zero_param (mask := mask) hr0 hr1 b
    gcongr
  exact hbound y hy q χ hq t ht mask r hr0 hr1
    (le_trans (Finset.sum_le_sum fun b _ => hmono b) hmass0)
    (le_trans (Finset.sum_le_sum fun b _ => hmono b) htail0)

/-! ## §7 — THE TWO-BLOCK INSTANCE `𝒥 = {1,2}` -/

/-- The single-block mask `1_{[P,Q]}` on primes — the mask that reproduces
`MobiusChiRamare`'s carriers (`maskOmega_blockMask` and friends). -/
def blockMask (P Q : ℕ) : ℕ → Bool := fun p => decide (P ≤ p ∧ p ≤ Q)

/-- **THE UNION MASK** `1_{[P₁,Q₁] ∪ [P₂,Q₂]}` — the `𝒥 = {1,2}` mask of MR p. 15's `g_𝒥`
read on the DAMPING side: a prime is masked iff it lies in either block.  For `Q₁ < P₂` the
two blocks are disjoint and the mask is the product of the two disjoint-interval indicators
in the sense of `unionDamp_eq_mul`; it is NOT `blockMask` for any single `(P,Q)`. -/
def unionMask (P₁ Q₁ P₂ Q₂ : ℕ) : ℕ → Bool :=
  fun p => blockMask P₁ Q₁ p || blockMask P₂ Q₂ p

/-- `ω(n; [P₁,Q₁] ∪ [P₂,Q₂])` — the union window's prime count. -/
def unionOmega (P₁ Q₁ P₂ Q₂ n : ℕ) : ℕ := maskOmega (unionMask P₁ Q₁ P₂ Q₂) n

/-- Union-window smoothness: every prime factor lies in one of the two blocks. -/
def UnionSmooth (P₁ Q₁ P₂ Q₂ n : ℕ) : Prop := MaskSmooth (unionMask P₁ Q₁ P₂ Q₂) n

@[simp] lemma blockMask_iff {P Q p : ℕ} : blockMask P Q p = true ↔ (P ≤ p ∧ p ≤ Q) := by
  simp [blockMask]

@[simp] lemma unionMask_iff {P₁ Q₁ P₂ Q₂ p : ℕ} :
    unionMask P₁ Q₁ P₂ Q₂ p = true ↔ ((P₁ ≤ p ∧ p ≤ Q₁) ∨ (P₂ ≤ p ∧ p ≤ Q₂)) := by
  simp [unionMask]

/-! ### The single-window bridges — the LANDED carriers are the `blockMask` instance -/

theorem maskOmega_blockMask (P Q n : ℕ) : maskOmega (blockMask P Q) n = blockOmega P Q n := by
  unfold maskOmega MaskPrimeDivs blockOmega BlockPrimeDivs
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  simp [blockMask]

theorem maskSmooth_blockMask_iff (P Q n : ℕ) :
    MaskSmooth (blockMask P Q) n ↔ WindowSmooth P Q n := by
  unfold MaskSmooth WindowSmooth
  constructor
  · intro h p hp
    exact blockMask_iff.mp (h p hp)
  · intro h p hp
    exact blockMask_iff.mpr (h p hp)

theorem muGrMask_blockMask (P Q : ℕ) (r : ℝ) : muGrMask (blockMask P Q) r = muGr P Q r := by
  ext n
  rw [muGrMask_apply, muGr_apply, maskOmega_blockMask]

theorem maskTailWeight_blockMask (P Q : ℕ) (r : ℝ) :
    maskTailWeight (blockMask P Q) r = ramTailWeight P Q r := by
  ext n
  rw [maskTailWeight_apply, ramTailWeight_apply, maskOmega_blockMask]
  exact if_congr (and_congr_right' (maskSmooth_blockMask_iff P Q n)) rfl rfl

theorem MmuGrChiMask_blockMask {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ) (r : ℝ)
    (y : ℕ) : MmuGrChiMask χ t (blockMask P Q) r y = MmuGrChi χ t P Q r y := by
  rw [MmuGrChiMask, MmuGrChi, muGrMask_blockMask]

theorem MmuRamChiMask_blockMask {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q y : ℕ) :
    MmuRamChiMask χ t (blockMask P Q) y = MmuRamChi χ t P Q y := by
  rw [MmuRamChiMask, MmuRamChi]
  exact Finset.sum_congr rfl fun m _ => by rw [maskOmega_blockMask]

/-! ### The disjointness arithmetic — the two-block additivity -/

/-- **THE TWO-BLOCK ADDITIVITY.**  For DISJOINT blocks (`Q₁ < P₂`),

  `ω(n; [P₁,Q₁] ∪ [P₂,Q₂]) = ω(n;P₁,Q₁) + ω(n;P₂,Q₂)`.

This is the bridge from the union carrier to the corpus's own `blockOmega` — the exponent
`RamWeight.ramRdamp` and `Decomp.ramareWeight` read at each block.  Disjointness is used
exactly once, to make the two masked prime-divisor sets disjoint. -/
theorem unionOmega_eq_add_of_lt {P₁ Q₁ P₂ Q₂ : ℕ} (hQP : Q₁ < P₂) (n : ℕ) :
    unionOmega P₁ Q₁ P₂ Q₂ n = blockOmega P₁ Q₁ n + blockOmega P₂ Q₂ n := by
  have hsplit : MaskPrimeDivs (unionMask P₁ Q₁ P₂ Q₂) n
      = BlockPrimeDivs P₁ Q₁ n ∪ BlockPrimeDivs P₂ Q₂ n := by
    ext p
    simp only [MaskPrimeDivs, BlockPrimeDivs, Finset.mem_filter, Finset.mem_union, unionMask_iff]
    tauto
  have hdisj : Disjoint (BlockPrimeDivs P₁ Q₁ n) (BlockPrimeDivs P₂ Q₂ n) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [BlockPrimeDivs, Finset.mem_filter] at h1 h2
    omega
  unfold unionOmega maskOmega blockOmega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]

/-- **THE MASK AS A PRODUCT OF THE TWO DISJOINT-INTERVAL INDICATORS** (the refuter's local
factor, on the damping side): `r^{ω(n;∪)} = r^{ω(n;P₁,Q₁)}·r^{ω(n;P₂,Q₂)}` for `Q₁ < P₂`. -/
theorem unionDamp_eq_mul {P₁ Q₁ P₂ Q₂ : ℕ} (hQP : Q₁ < P₂) (r : ℝ) (n : ℕ) :
    r ^ unionOmega P₁ Q₁ P₂ Q₂ n
      = r ^ blockOmega P₁ Q₁ n * r ^ blockOmega P₂ Q₂ n := by
  rw [unionOmega_eq_add_of_lt hQP n, pow_add]

/-! ### The union carriers and THE TERMINAL TWINS -/

/-- The damped Möbius datum at the union window, `μ(m)·r^{ω(m;∪)}`. -/
noncomputable def muGrU (P₁ Q₁ P₂ Q₂ : ℕ) (r : ℝ) : ArithmeticFunction ℝ :=
  muGrMask (unionMask P₁ Q₁ P₂ Q₂) r

/-- The tail weight at the union window, `w_r(n) = (1−r)^{ω(n;∪)}` on the union-smooth
support. -/
noncomputable def ramTailWeightU (P₁ Q₁ P₂ Q₂ : ℕ) (r : ℝ) : ArithmeticFunction ℝ :=
  maskTailWeight (unionMask P₁ Q₁ P₂ Q₂) r

/-- The twisted damped Möbius summatory function at the union window. -/
noncomputable def MmuGrChiU {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (P₁ Q₁ P₂ Q₂ : ℕ) (r : ℝ) (y : ℕ) : ℂ :=
  MmuGrChiMask χ t (unionMask P₁ Q₁ P₂ Q₂) r y

/-- The Ramaré-WEIGHTED twisted Möbius summatory function at the union window,
`∑_{m ≤ y} μ(m)/(ω(m;∪)+1)·χ̄(m)m^{it}`. -/
noncomputable def MmuRamChiU {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (P₁ Q₁ P₂ Q₂ : ℕ) (y : ℕ) : ℂ :=
  MmuRamChiMask χ t (unionMask P₁ Q₁ P₂ Q₂) y

/-- The union carriers ARE the mask carriers, spelled out: `μ·g_r` at the union window is
`μ(m)·r^{ω₁(m)}·r^{ω₂(m)}` for disjoint blocks. -/
theorem muGrU_apply_of_lt {P₁ Q₁ P₂ Q₂ : ℕ} (hQP : Q₁ < P₂) (r : ℝ) (m : ℕ) :
    muGrU P₁ Q₁ P₂ Q₂ r m
      = ((ArithmeticFunction.moebius m : ℤ) : ℝ)
          * (r ^ blockOmega P₁ Q₁ m * r ^ blockOmega P₂ Q₂ m) := by
  rw [muGrU, muGrMask_apply, ← unionDamp_eq_mul hQP, unionOmega]

/-- The fold at the union window (UNCONDITIONAL) — `MmuGrChiMask_eq_sum` instantiated. -/
theorem MmuGrChiU_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P₁ Q₁ P₂ Q₂ : ℕ)
    (r : ℝ) (y : ℕ) :
    MmuGrChiU χ t P₁ Q₁ P₂ Q₂ r y
      = ∑ b ∈ Finset.Icc 1 y,
          (((ramTailWeightU P₁ Q₁ P₂ Q₂ r b : ℝ) : ℂ) * chiBarTwist χ t b)
            * MmuChi χ t (y / b) :=
  MmuGrChiMask_eq_sum χ t (unionMask P₁ Q₁ P₂ Q₂) r y

/-- **⟦D3 carrier page 2⟧ THE UNION-WINDOW DELIVERABLE (damped).**  The `𝒥 = {1,2}` twin of
`Salt.MR.MmuGrChi_rate`: the Ramaré-damped twisted Möbius datum at the union of two blocks
inherits the rate, uniformly over `q ≤ (log y)^11`, `|t| ≤ ⌊√y⌋`, the two blocks and
`r ∈ [0,1]`.  The mass hypothesis is the union window's own ℓ¹(1/n) mass — for `Q₁ < P₂` the
product of the two block masses (header). -/
theorem MmuGrChiU_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ, |t| ≤ (Nat.sqrt y : ℝ) →
          ∀ (P₁ Q₁ P₂ Q₂ : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
            (∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
                ramTailWeightU P₁ Q₁ P₂ Q₂ r b / (b : ℝ)) ≤ M →
            (∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
                ramTailWeightU P₁ Q₁ P₂ Q₂ r b / (b : ℝ)) ≤ 1 / (Real.log y) ^ A →
            ‖MmuGrChiU χ t P₁ Q₁ P₂ Q₂ r y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C', x₀, hC'pos, hbound⟩ := MmuGrChiMask_rate hMmu A hA hM
  exact ⟨C', x₀, hC'pos, fun y hy q _ χ hq t ht P₁ Q₁ P₂ Q₂ r hr0 hr1 hmass htail =>
    hbound y hy q χ hq t ht (unionMask P₁ Q₁ P₂ Q₂) r hr0 hr1 hmass htail⟩

/-- **⟦D3 carrier page 2⟧ THE UNION-WINDOW RAMARÉ-WEIGHTED DELIVERABLE.**  The `𝒥 = {1,2}`
twin of `Salt.MR.MmuRamChi_rate`: `μ(m)/(ω(m;∪)+1)·χ̄(m)m^{it}` inherits the rate from
`MmuChiRate` plus the two named union-window hypotheses at `r = 0`. -/
theorem MmuRamChiU_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ, |t| ≤ (Nat.sqrt y : ℝ) →
          ∀ P₁ Q₁ P₂ Q₂ : ℕ,
            (∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
                ramTailWeightU P₁ Q₁ P₂ Q₂ 0 b / (b : ℝ)) ≤ M →
            (∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
                ramTailWeightU P₁ Q₁ P₂ Q₂ 0 b / (b : ℝ)) ≤ 1 / (Real.log y) ^ A →
            ‖MmuRamChiU χ t P₁ Q₁ P₂ Q₂ y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C', x₀, hC'pos, hbound⟩ := MmuRamChiMask_rate hMmu A hA hM
  exact ⟨C', x₀, hC'pos, fun y hy q _ χ hq t ht P₁ Q₁ P₂ Q₂ hmass htail =>
    hbound y hy q χ hq t ht (unionMask P₁ Q₁ P₂ Q₂) hmass htail⟩

end Salt.MR
