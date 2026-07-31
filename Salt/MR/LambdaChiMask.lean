/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LambdaChiRamare
import Salt.MR.MobiusChiRamareUnion

/-!
# ⟦D3 — THE λ-AT-MASK TWIN⟧ the damped Liouville rate at an ARBITRARY prime mask

Design: the 0730 council's **C5** (`docs/blueprints/flags.md`, ⟦THE 0730 COUNCIL⟧), executed
at D3-DISCHARGE.  ⟦THE GAP THIS FILE CLOSES, NAMED IN THE FIRST-BANK LEDGER⟧
`LambdaChiRamare` landed the λ-side rate at a SINGLE window `[P,Q]`
(`MlamGrChi_rate`); `MobiusChiRamareUnion` landed the μ-side rate at a GENERAL mask
(`MmuGrChiMask_rate`).  The door's `hpiece` slot (`M4T0Datum.m4_hT0band_at_door`) reads
`pieceDatum χ 𝒥 = liouChi χ · g_𝒥`, i.e. the LIOUVILLE datum at the mask
`⋃_{j ∈ 𝒥}[P_j,Q_j]` — which for `𝒥 = {1,2}` is not an interval, so no instantiation of
`MlamGrChi_rate` reaches it.  **The λ-at-mask combination was genuinely missing.**  This file
is it: purely ADDITIVE, no landed declaration touched.

## THE ROUTE — the two landed templates, composed at their intersection

Every step below is `LambdaChiRamare`'s §1–§5 with `blockOmega P Q → maskOmega mask`,
`WindowSmooth P Q → MaskSmooth mask`, `ramTailWeight P Q → maskTailWeight mask`; equivalently
it is `MobiusChiRamareUnion`'s §2–§5 with `(μ, w_r) → (λ, v_r = μ²·w_r)` and the twisted
Möbius inner rate replaced by the twisted **Liouville** rate `MlambdaChi_rate`.  Both
substitutions are mechanical because neither template ever inspects the interval structure and
neither ever inspects the datum beyond multiplicativity.

The mathematics is `LambdaChiRamare`'s, restated at the mask.  Reading the Euler factors,
`λ·g_r` is multiplicative with `(λ·g_r)(p^k) = (−1)^k r^{1_{mask}(p)}`, so

  `D(λ·g_r)(s) = D(λ)(s) · ∏_{mask p} (1 + (1−r)p^{−s})`,

and the coefficients — `(1−r)` at `p¹`, **`0` at every `p^k`, `k ≥ 2`** — give the carrier as
the SQUAREFREE RESTRICTION of the mask tail weight:

  `v_r(n) = μ(n)²·w_r(n)`,  **`λ·g_r = λ ∗ v_r`**  (`lamTailWeightMask_mul_liouville`).

⟦THE `d²`-FOLD STAYS REFUTED⟧ `LambdaChiRamare`'s header records why REF-A4-4's mechanism
`(λ·g)(n) = ∑_{d²∣n}(μ·g)(n/d²)·g(d)²` is false (`g_r` is not completely multiplicative:
`g_r(p²) = r ≠ r²`).  Nothing about passing to a mask repairs that; the same convolution
device is what runs here.

## PRICES — IDENTICAL to `MlamGrChi_rate`'s; the mask is invisible to every gate

| slot | conductor gate | height gate |
|---|---|---|
| `MmuChiRate` (landed) | `q ≤ (log y)^12` | `|t| ≤ y` |
| `MlambdaChi_rate` (landed) | `q ≤ (log y)^11` | `|t| ≤ ⌊√y⌋` |
| `MlamGrChiMask_rate` (**here**) | `q ≤ (log y)^10` | `|t| ≤ ⌊√⌊√y⌋⌋ ≈ y^{1/4}` |

The mask enters ONLY through the two window rows `M` (the ℓ¹(1/n) mass) and `ε` (the Rankin
tail) — exactly as in both templates.  ⟦the four log scales, kept apart⟧ `log y` (the
statement), `log⌊y/b⌋` (where the λ-rate fires — the `4^A` and the exponent are spent there),
`log √y ≥ (log y)/4` (the absorbed floor), and the WINDOW scale (confined to `M`, `ε`).
`mask` appears nowhere else.

## TWIN FIDELITY — the landed single-window page IS the `blockMask` instance

§6 proves it rather than asserting it: `lamGrMask_blockMask`, `lamTailWeightMask_blockMask`,
`MlamGrChiMask_blockMask`.  So `LambdaChiRamare`'s `MlamGrChi` is a corollary of this page,
and `𝒥 = {1,…,J}` is one more instantiation at zero further bytes.

## Contents

* **§1** `lamGrMask` — the damped Liouville datum `λ·g_r` at the mask, and multiplicativity.
* **§2** `lamTailWeightMask` — the carrier `v_r = μ²·w_r`, positivity, support, domination
  `v_r ≤ w_r`, antitonicity in `r`, multiplicativity, prime-power coefficients.
* **§3** THE VERIFICATION `lamTailWeightMask_mul_liouville` (`λ ∗ v_r = λ·g_r`, at prime
  powers) with its pointwise and twisted antidiagonal forms.
* **§4** `MlamGrChiMask` and the twisted hyperbola fold `MlamGrChiMask_eq_sum`
  (UNCONDITIONAL), through the LANDED datum-generic `sum_filter_dvd_div_eq`.
* **§5** `norm_MlamGrChiMask_le_split` and THE DELIVERABLE `MlamGrChiMask_rate`.
* **§6** the `blockMask` fidelity bridges.

Explicit constants throughout; no `O(·)` in any statement.  The only hypothesis anywhere is
the corpus's standing slot `MmuChiRate`.
-/

open scoped BigOperators

namespace Salt.MR

/-! ## §1 — the damped Liouville datum `λ·g_r` at the mask -/

/-- **The masked damped Liouville datum** `(λ·g_r)(m) = λ(m)·r^{ω(m;mask)}` as an
`ArithmeticFunction ℝ` — the mask twin of `Salt.MR.lamGr` and the λ-twin of
`Salt.MR.muGrMask`.  At `m = 0` the value is `0` because `λ 0 = 0`. -/
noncomputable def lamGrMask (mask : ℕ → Bool) (r : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => ((ArithmeticFunction.liouville m : ℤ) : ℝ) * r ^ maskOmega mask m, by simp⟩

@[simp] lemma lamGrMask_apply (mask : ℕ → Bool) (r : ℝ) (m : ℕ) :
    lamGrMask mask r m = ((ArithmeticFunction.liouville m : ℤ) : ℝ) * r ^ maskOmega mask m := rfl

/-- **`λ·g_r` is multiplicative at the mask.**  `λ` is (`isMultiplicative_liouville`; it is even
completely multiplicative) and `ω(·;mask)` is additive on coprimes (the LANDED
`maskOmega_mul_coprime`).  `λ·g_r` is **not** completely multiplicative — `g_r` is not. -/
theorem lamGrMask_isMultiplicative (mask : ℕ → Bool) (r : ℝ) :
    (lamGrMask mask r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [lamGrMask_apply, maskOmega_one, pow_zero, ArithmeticFunction.liouville_apply_one]
    norm_num
  · intro m n _ _ hmn
    simp only [lamGrMask_apply]
    rw [ArithmeticFunction.isMultiplicative_liouville.map_mul_of_coprime hmn,
      maskOmega_mul_coprime mask hmn, pow_add]
    push_cast
    ring

/-! ## §2 — the λ-side carrier `v_r = μ²·w_r` at the mask -/

/-- **THE λ-SIDE CARRIER `v_r` AT THE MASK** — the multiplicative function with local factor
`1 + (1−r)p^{−s}` at masked primes and local factor `1` elsewhere, carried as the SQUAREFREE
RESTRICTION of the mask tail weight `maskTailWeight`:

  `v_r(n) = μ(n)²·w_r(n)`,  i.e. `(1−r)^{ω(n;mask)}` on squarefree mask-smooth `n`, `0` else.

The `μ²` factor is exactly the "`0` at every `p^k`, `k ≥ 2`" of the local factor — the ONE
structural difference from the Möbius side.  Carrying `v_r` as `μ²·w_r` (rather than as a
fresh closed form) is what makes positivity, the support, antitonicity in `r` and — decisively
— the DOMINATION `v_r ≤ w_r` one-liners, so that no new mass or tail hypothesis is created. -/
noncomputable def lamTailWeightMask (mask : ℕ → Bool) (r : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 * maskTailWeight mask r n, by simp⟩

@[simp] lemma lamTailWeightMask_apply (mask : ℕ → Bool) (r : ℝ) (n : ℕ) :
    lamTailWeightMask mask r n
      = ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 * maskTailWeight mask r n := rfl

/-- The closed form on the support: `v_r(n) = (1−r)^{ω(n;mask)}` for squarefree mask-smooth
`n`. -/
theorem lamTailWeightMask_apply_of {mask : ℕ → Bool} (r : ℝ) {n : ℕ} (hn : Squarefree n)
    (hs : MaskSmooth mask n) :
    lamTailWeightMask mask r n = (1 - r) ^ maskOmega mask n := by
  rw [lamTailWeightMask_apply, maskTailWeight_apply_of r hn.ne_zero hs,
    ArithmeticFunction.moebius_apply_of_squarefree hn]
  push_cast
  have hsq : ((-1 : ℝ) ^ ArithmeticFunction.cardFactors n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hsq, one_mul]

theorem lamTailWeightMask_eq_zero_of_not_squarefree {mask : ℕ → Bool} (r : ℝ) {n : ℕ}
    (hn : ¬ Squarefree n) : lamTailWeightMask mask r n = 0 := by
  rw [lamTailWeightMask_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  norm_num

theorem lamTailWeightMask_eq_zero_of_not_smooth {mask : ℕ → Bool} (r : ℝ) {n : ℕ}
    (hs : ¬ MaskSmooth mask n) : lamTailWeightMask mask r n = 0 := by
  rw [lamTailWeightMask_apply, maskTailWeight_eq_zero_of_not_smooth r hs, mul_zero]

/-- **KEY POSITIVITY**: for `r ≤ 1` every value of `v_r` is `≥ 0`. -/
theorem lamTailWeightMask_nonneg {mask : ℕ → Bool} {r : ℝ} (hr1 : r ≤ 1) (n : ℕ) :
    0 ≤ lamTailWeightMask mask r n := by
  rw [lamTailWeightMask_apply]
  exact mul_nonneg (sq_nonneg _) (maskTailWeight_nonneg hr1 n)

/-- **THE DOMINATION — the reason this page costs the consumer nothing.**  `v_r ≤ w_r`
pointwise (`μ² ≤ 1`, `w_r ≥ 0`), so every mass/tail hypothesis stated on the mask carrier
`maskTailWeight` implies its `lamTailWeightMask` counterpart.  The deliverable of §5 is stated
at the mask carrier's hypotheses because of this lemma. -/
theorem lamTailWeightMask_le_maskTailWeight {mask : ℕ → Bool} {r : ℝ} (hr1 : r ≤ 1) (n : ℕ) :
    lamTailWeightMask mask r n ≤ maskTailWeight mask r n := by
  rw [lamTailWeightMask_apply]
  refine mul_le_of_le_one_left (maskTailWeight_nonneg hr1 n) ?_
  have hcast : ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
      = (((ArithmeticFunction.moebius n ^ 2 : ℤ)) : ℝ) := by push_cast; ring
  rw [hcast, ArithmeticFunction.moebius_sq]
  split_ifs <;> norm_num

/-- **THE SUPPORT.**  `v_r` vanishes off the SQUAREFREE mask-smooth numbers. -/
theorem lamTailWeightMask_support {mask : ℕ → Bool} {r : ℝ} {n : ℕ}
    (h : lamTailWeightMask mask r n ≠ 0) : Squarefree n ∧ MaskSmooth mask n := by
  have h2 : maskTailWeight mask r n ≠ 0 := fun h0 => h (by
    rw [lamTailWeightMask_apply, h0, mul_zero])
  refine ⟨?_, (maskTailWeight_support h2).2⟩
  by_contra hc
  exact h (lamTailWeightMask_eq_zero_of_not_squarefree r hc)

/-- **ANTITONICITY IN THE DAMPING**: for `r ∈ [0,1]`, `v_r ≤ v_0` pointwise. -/
theorem lamTailWeightMask_le_zero_param {mask : ℕ → Bool} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) : lamTailWeightMask mask r n ≤ lamTailWeightMask mask 0 n := by
  rw [lamTailWeightMask_apply, lamTailWeightMask_apply]
  exact mul_le_mul_of_nonneg_left (maskTailWeight_le_zero_param hr0 hr1 n) (sq_nonneg _)

/-- **`v_r` is multiplicative** — `μ` is, `w_r` is (the LANDED
`maskTailWeight_isMultiplicative`), and a pointwise product of multiplicative functions is
multiplicative. -/
theorem lamTailWeightMask_isMultiplicative (mask : ℕ → Bool) (r : ℝ) :
    (lamTailWeightMask mask r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [lamTailWeightMask_apply, (maskTailWeight_isMultiplicative mask r).map_one,
      ArithmeticFunction.moebius_apply_one]
    norm_num
  · intro m n _ _ hmn
    simp only [lamTailWeightMask_apply]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
      (maskTailWeight_isMultiplicative mask r).map_mul_of_coprime hmn]
    push_cast
    ring

/-- **THE LOCAL FACTOR'S COEFFICIENTS — the auditable half of the verification.**  For
`k ≥ 1`,

  `v_r(p^k) = 1 − r` if `k = 1` and `p` is masked,   `v_r(p^k) = 0` otherwise,

i.e. exactly the coefficients of `1 + (1−r)p^{−s}` (masked) and `1` (unmasked).  Contrast
`maskTailWeight_prime_pow`, where the coefficient is `(1−r)` for EVERY `k ≥ 1`. -/
theorem lamTailWeightMask_prime_pow {mask : ℕ → Bool} {p k : ℕ} (r : ℝ) (hp : p.Prime)
    (hk : k ≠ 0) :
    lamTailWeightMask mask r (p ^ k)
      = if k = 1 then (if mask p = true then 1 - r else 0) else 0 := by
  rw [lamTailWeightMask_apply, maskTailWeight_prime_pow r hp hk,
    ArithmeticFunction.moebius_apply_prime_pow hp hk]
  by_cases hk1 : k = 1
  · simp only [if_pos hk1]
    norm_num
  · simp only [if_neg hk1]
    norm_num

/-! ## §3 — THE CONVOLUTION IDENTITY `λ·g_r = λ ∗ v_r` AT THE MASK -/

private lemma liouville_prime_pow_real_mask {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((ArithmeticFunction.liouville (p ^ j) : ℤ) : ℝ) = (-1) ^ j := by
  rw [ArithmeticFunction.liouville_apply (pow_ne_zero j hp.ne_zero),
    ArithmeticFunction.cardFactors_apply_prime_pow hp]
  push_cast
  ring

/-- **THE VERIFICATION OF THE CARRIER**, in the orientation the prime-power check likes:

  `v_r ∗ λ = λ·g_r`.

Both sides are multiplicative, so `IsMultiplicative.eq_iff_eq_on_prime_powers` reduces to
`p^k`, `k = j+1 ≥ 1`, where only `i ∈ {0,1}` survives in `∑_{i≤k} v_r(p^i)·λ(p^{k−i})` (that
is the `μ²` factor at work):

  `λ(p^{j+1}) + 1_{mask}(p)·(1−r)·λ(p^j) = (−1)^{j+1}·r^{1_{mask}(p)}`,

since `(−1)^{j+1} + (1−r)(−1)^j = (−1)^j(−1 + 1 − r) = (−1)^{j+1}r` at a masked prime and
`(−1)^{j+1}` off it — precisely reading off `1 + (1−r)p^{−s}`.  The argument never inspects
the mask, which is why the union of two disjoint blocks is no harder than one block. -/
theorem lamTailWeightMask_mul_liouville (mask : ℕ → Bool) (r : ℝ) :
    lamTailWeightMask mask r
        * ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
      = lamGrMask mask r := by
  have hliou : (((ArithmeticFunction.liouville : ArithmeticFunction ℤ) :
      ArithmeticFunction ℝ)).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_liouville.intCast
  have hmulti : (lamTailWeightMask mask r
      * ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) :
        ArithmeticFunction ℝ)).IsMultiplicative :=
    (lamTailWeightMask_isMultiplicative mask r).mul hliou
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmulti _
    (lamGrMask_isMultiplicative mask r)]
  intro p k hp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, hmulti.map_one, (lamGrMask_isMultiplicative mask r).map_one]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.intCoe_apply]
  rw [Nat.sum_divisorsAntidiagonal
      (fun a b => lamTailWeightMask mask r a * ((ArithmeticFunction.liouville b : ℤ) : ℝ)),
    Nat.sum_divisors_prime_pow hp]
  have hcong : ∀ i ∈ Finset.range (j + 1 + 1),
      lamTailWeightMask mask r (p ^ i)
          * ((ArithmeticFunction.liouville (p ^ (j + 1) / p ^ i) : ℤ) : ℝ)
        = lamTailWeightMask mask r (p ^ i)
          * ((ArithmeticFunction.liouville (p ^ (j + 1 - i)) : ℤ) : ℝ) := by
    intro i hi
    have hi' : i ≤ j + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [Nat.pow_div hi' hp.pos]
  rw [Finset.sum_congr rfl hcong]
  have hsub : Finset.range 2 ⊆ Finset.range (j + 1 + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hzero : ∀ i ∈ Finset.range (j + 1 + 1), i ∉ Finset.range 2 →
      lamTailWeightMask mask r (p ^ i)
          * ((ArithmeticFunction.liouville (p ^ (j + 1 - i)) : ℤ) : ℝ) = 0 := by
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [lamTailWeightMask_prime_pow r hp (by omega : i ≠ 0), if_neg (by omega : ¬ i = 1),
      zero_mul]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
    (lamTailWeightMask_isMultiplicative mask r).map_one]
  simp only [Nat.sub_zero, Nat.add_sub_cancel]
  rw [lamTailWeightMask_prime_pow r hp one_ne_zero, if_pos rfl, lamGrMask_apply,
    maskOmega_prime_pow hp (Nat.succ_ne_zero j), liouville_prime_pow_real_mask hp,
    liouville_prime_pow_real_mask hp]
  by_cases hm : mask p = true
  · simp only [if_pos hm]
    ring
  · simp only [if_neg hm]
    ring

/-- **THE CONVOLUTION IDENTITY, `ArithmeticFunction`-level**: `λ ∗ v_r = λ·g_r` at the mask.
UNCONDITIONAL. -/
theorem liouville_mul_lamTailWeightMask (mask : ℕ → Bool) (r : ℝ) :
    ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * lamTailWeightMask mask r = lamGrMask mask r := by
  rw [mul_comm]
  exact lamTailWeightMask_mul_liouville mask r

/-- **THE CONVOLUTION IDENTITY, pointwise** (the form the fold consumes): for every `m`,
`λ(m)·r^{ω(m;mask)} = ∑_{ab = m} λ(a)·v_r(b)`.  Holds at `m = 0` too. -/
theorem lamGrMask_eq_sum_divisorsAntidiagonal (mask : ℕ → Bool) (r : ℝ) (m : ℕ) :
    ((ArithmeticFunction.liouville m : ℤ) : ℝ) * r ^ maskOmega mask m
      = ∑ ab ∈ m.divisorsAntidiagonal,
          ((ArithmeticFunction.liouville ab.1 : ℤ) : ℝ) * lamTailWeightMask mask r ab.2 := by
  rw [← lamGrMask_apply, ← liouville_mul_lamTailWeightMask, ArithmeticFunction.mul_apply]
  exact Finset.sum_congr rfl fun ab _ => by rw [ArithmeticFunction.intCoe_apply]

/-- **The twist distributes over `λ·g_r = λ ∗ v_r`** (for `m ≠ 0`) — the ℂ-side of the
pointwise identity, through `chiBarTwist_mul`.  ⟦DEVIATION, inherited from both templates⟧
`LambdaRateTwisted.mul_apply_mul_twist` is CITED, not instantiated: its `f g h` live in ONE
ring while the carriers here are `ArithmeticFunction ℝ` and the twist is ℂ-valued. -/
theorem lamGrMask_twist_eq_sum_divisorsAntidiagonal {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (mask : ℕ → Bool) (r : ℝ) {m : ℕ} (hm : m ≠ 0) :
    ((lamGrMask mask r m : ℝ) : ℂ) * chiBarTwist χ t m
      = ∑ ab ∈ m.divisorsAntidiagonal,
          (((ArithmeticFunction.liouville ab.1 : ℤ) : ℂ) * chiBarTwist χ t ab.1)
            * (((lamTailWeightMask mask r ab.2 : ℝ) : ℂ) * chiBarTwist χ t ab.2) := by
  have hR := lamGrMask_eq_sum_divisorsAntidiagonal mask r m
  have hC : ((lamGrMask mask r m : ℝ) : ℂ)
      = ∑ ab ∈ m.divisorsAntidiagonal,
          ((ArithmeticFunction.liouville ab.1 : ℤ) : ℂ)
            * ((lamTailWeightMask mask r ab.2 : ℝ) : ℂ) := by
    rw [lamGrMask_apply, hR]
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

/-! ## §4 — the twisted damped summatory function and the hyperbola fold -/

/-- **The masked twisted damped Liouville summatory function**
`M_{λg_rχ̄}(y) = ∑_{m ≤ y} λ(m)r^{ω(m;mask)}χ̄(m)m^{it}`, ℂ-valued. -/
noncomputable def MlamGrChiMask {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (mask : ℕ → Bool)
    (r : ℝ) (y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 y, ((lamGrMask mask r m : ℝ) : ℂ) * chiBarTwist χ t m

/-- **THE TWISTED HYPERBOLA FOLD (UNCONDITIONAL)** at the mask:

  `∑_{m ≤ y} λ(m)g_r(m)χ̄(m)m^{it} = ∑_{b ≤ y} v_r(b)χ̄(b)b^{it} · M_{λχ̄}(⌊y/b⌋)`.

The inner collapse is the LANDED `MlambdaChi_inner_dvd` (mask-blind, reused verbatim).  No
hypothesis on `r` or the mask. -/
theorem MlamGrChiMask_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (mask : ℕ → Bool)
    (r : ℝ) (y : ℕ) :
    MlamGrChiMask χ t mask r y
      = ∑ b ∈ Finset.Icc 1 y,
          (((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
            * MlambdaChi χ t (y / b) := by
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
      ((lamGrMask mask r m : ℝ) : ℂ) * chiBarTwist χ t m
        = ∑ b ∈ Finset.Icc 1 y,
            (if b ∣ m then
              (((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
                * (((ArithmeticFunction.liouville (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
             else 0) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    rw [lamGrMask_twist_eq_sum_divisorsAntidiagonal χ t mask r hm0]
    rw [Nat.sum_divisorsAntidiagonal' (n := m)
      (f := fun a b => (((ArithmeticFunction.liouville a : ℤ) : ℂ) * chiBarTwist χ t a)
        * (((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b))]
    rw [← hdivfilter m hm.1 hm.2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · ring
    · rfl
  rw [MlamGrChiMask, Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  have hpull : ∀ m : ℕ,
      (if b ∣ m then
        (((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
          * (((ArithmeticFunction.liouville (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
       else 0)
      = (((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
          * (if b ∣ m then
              (((ArithmeticFunction.liouville (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
             else 0) := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => hpull m), ← Finset.mul_sum, ← Finset.sum_filter,
    MlambdaChi_inner_dvd χ t y b hb.1]

/-! ## §5 — the rate transfer -/

/-- **THE TWO-ROW SPLIT (UNCONDITIONAL)** at the mask.  Given
* a per-`b` bound `‖M_{λχ̄}(⌊y/b⌋)‖ ≤ B·y/b` on the SMALL range `b ≤ √y`,
* the window mass `∑_{b ≤ √y} v_r(b)/b ≤ M`,
* the tail `∑_{√y < b ≤ y} v_r(b)/b ≤ ε`,

the damped twisted Liouville datum obeys `‖M_{λg_rχ̄}(y)‖ ≤ B·M·y + ε·y`.  On the tail row
only the crude `norm_MlambdaChi_le` is used — that row is where the transposition can fail,
and `ε` is the honest name of the failure. -/
theorem norm_MlamGrChiMask_le_split {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (mask : ℕ → Bool) (r : ℝ) (y : ℕ) (hr1 : r ≤ 1) {B M ε : ℝ} (hB : 0 ≤ B)
    (hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
      ‖MlambdaChi χ t (y / b)‖ ≤ B * (y : ℝ) / (b : ℝ))
    (hmass : ∑ b ∈ Finset.Icc 1 (Nat.sqrt y), lamTailWeightMask mask r b / (b : ℝ) ≤ M)
    (htail : ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, lamTailWeightMask mask r b / (b : ℝ) ≤ ε) :
    ‖MlamGrChiMask χ t mask r y‖ ≤ B * M * (y : ℝ) + ε * (y : ℝ) := by
  have hwnn : ∀ n : ℕ, 0 ≤ lamTailWeightMask mask r n := fun n =>
    lamTailWeightMask_nonneg hr1 n
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hsqle : Nat.sqrt y ≤ y := Nat.sqrt_le_self y
  have hcoef : ∀ b : ℕ,
      ‖((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b‖
        ≤ lamTailWeightMask mask r b := by
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
  rw [MlamGrChiMask_eq_sum, hIcc, Finset.sum_union hdisj]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖(((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
            * MlambdaChi χ t (y / b)‖
          ≤ (B * (y : ℝ)) * (lamTailWeightMask mask r b / (b : ℝ)) := by
      intro b hb
      calc ‖(((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
              * MlambdaChi χ t (y / b)‖
          = ‖((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b‖
              * ‖MlambdaChi χ t (y / b)‖ := norm_mul _ _
        _ ≤ lamTailWeightMask mask r b * (B * (y : ℝ) / (b : ℝ)) :=
            mul_le_mul (hcoef b) (hsmall b hb) (norm_nonneg _) (hwnn b)
        _ = (B * (y : ℝ)) * (lamTailWeightMask mask r b / (b : ℝ)) := by ring
    calc ∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
            ‖(((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
              * MlambdaChi χ t (y / b)‖
        ≤ ∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
            (B * (y : ℝ)) * (lamTailWeightMask mask r b / (b : ℝ)) := Finset.sum_le_sum hterm
      _ = (B * (y : ℝ))
            * ∑ b ∈ Finset.Icc 1 (Nat.sqrt y), lamTailWeightMask mask r b / (b : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (B * (y : ℝ)) * M := mul_le_mul_of_nonneg_left hmass (mul_nonneg hB hy0)
      _ = B * M * (y : ℝ) := by ring
  · refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ Finset.Ioc (Nat.sqrt y) y,
        ‖(((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
            * MlambdaChi χ t (y / b)‖
          ≤ (y : ℝ) * (lamTailWeightMask mask r b / (b : ℝ)) := by
      intro b _
      have hcrude : ‖MlambdaChi χ t (y / b)‖ ≤ (y : ℝ) / (b : ℝ) :=
        le_trans (norm_MlambdaChi_le χ t (y / b)) (Nat.cast_div_le (m := y) (n := b) (α := ℝ))
      calc ‖(((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
              * MlambdaChi χ t (y / b)‖
          = ‖((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b‖
              * ‖MlambdaChi χ t (y / b)‖ := norm_mul _ _
        _ ≤ lamTailWeightMask mask r b * ((y : ℝ) / (b : ℝ)) :=
            mul_le_mul (hcoef b) hcrude (norm_nonneg _) (hwnn b)
        _ = (y : ℝ) * (lamTailWeightMask mask r b / (b : ℝ)) := by ring
    calc ∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
            ‖(((lamTailWeightMask mask r b : ℝ) : ℂ) * chiBarTwist χ t b)
              * MlambdaChi χ t (y / b)‖
        ≤ ∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
            (y : ℝ) * (lamTailWeightMask mask r b / (b : ℝ)) := Finset.sum_le_sum hterm
      _ = (y : ℝ)
            * ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, lamTailWeightMask mask r b / (b : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (y : ℝ) * ε := mul_le_mul_of_nonneg_left htail hy0
      _ = ε * (y : ℝ) := by ring

/-- `log y → ∞` along ℕ, in eventual form. -/
private lemma eventually_log_ge_lamMask (c : ℝ) :
    ∀ᶠ y : ℕ in Filter.atTop, c ≤ Real.log y := by
  have h : Filter.Tendsto (fun y : ℕ => Real.log (y : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- **⟦D3⟧ THE DELIVERABLE — the damped twisted LIOUVILLE rate AT AN ARBITRARY MASK.**

From the twisted μ-rate slot `MmuChiRate` through the landed fold `MlambdaChi_rate`, plus the
two named window hypotheses stated on the MASK carrier `maskTailWeight`, the Ramaré-damped
twisted Liouville datum at the mask inherits the rate at every saving `A > 0`:

  `‖∑_{m ≤ y} λ(m)r^{ω(m;mask)}χ̄(m)m^{it}‖ ≤ C'·y/(log y)^A`,

uniformly over `q ≤ (log y)^10`, `|t| ≤ ⌊√⌊√y⌋⌋`, the mask, and `r ∈ [0,1]`.

Gates and prices — IDENTICAL to `MlamGrChi_rate`'s, the mask is invisible to all of them:
* the CONDUCTOR gate moves from `MlambdaChi_rate`'s `q ≤ (log y)^11` to `q ≤ (log y)^10`, the
  λ-rate being invoked at `⌊y/b⌋` where only `log⌊y/b⌋ ≥ (log y)/4` is available (`log y ≥ 4^11`,
  an eventual threshold absorbed into `x₀`);
* the HEIGHT gate transfers sharply: `⌊√⌊√y⌋⌋ ≤ ⌊√⌊y/b⌋⌋` for `b ≤ √y`;
* the log-scale price is `4^A`, and `M` enters `C' = C·4^A·M + 1` LINEARLY;
* the hypotheses are stated on `maskTailWeight`, NOT on `lamTailWeightMask` — legitimate and
  strictly weaker to assume, by `lamTailWeightMask_le_maskTailWeight`.

`C'` and `x₀` do **not** depend on `r`, the mask, `q`, `χ` or `t`. -/
theorem MlamGrChiMask_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) →
            ∀ (mask : ℕ → Bool) (r : ℝ), 0 ≤ r → r ≤ 1 →
              (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask r b / (b : ℝ)) ≤ M →
              (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask r b / (b : ℝ))
                  ≤ 1 / (Real.log y) ^ A →
              ‖MlamGrChiMask χ t mask r y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C, x₀lam, hCpos, hLamBound⟩ := MlambdaChi_rate hMmu A hA
  have h4A : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hC'pos : (0 : ℝ) < C * (4 : ℝ) ^ A * M + 1 := by
    have h : (0 : ℝ) ≤ C * (4 : ℝ) ^ A * M :=
      mul_nonneg (mul_nonneg hCpos.le h4A.le) hM
    linarith
  have key : ∀ᶠ y : ℕ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) →
            ∀ (mask : ℕ → Bool) (r : ℝ), 0 ≤ r → r ≤ 1 →
              (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask r b / (b : ℝ)) ≤ M →
              (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask r b / (b : ℝ))
                  ≤ 1 / (Real.log y) ^ A →
              ‖MlamGrChiMask χ t mask r y‖
                ≤ (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
    filter_upwards [Filter.eventually_ge_atTop 16, Filter.eventually_ge_atTop (x₀lam ^ 2),
        eventually_log_ge_lamMask ((4 : ℝ) ^ (11 : ℕ))] with y hy16 hyx0 hlog4
    intro q _ χ hq t ht mask r hr0 hr1 hmass htail
    have hLpos : 0 < Real.log y := lt_of_lt_of_le (by positivity) hlog4
    have hL0 : (0 : ℝ) ≤ Real.log y := hLpos.le
    have hLApos : (0 : ℝ) < (Real.log y) ^ A := Real.rpow_pos_of_pos hLpos A
    have hs1 : 1 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by nlinarith [hy16])
    have hs_ge_x0 : x₀lam ≤ Nat.sqrt y := by
      rw [Nat.le_sqrt]
      calc x₀lam * x₀lam = x₀lam ^ 2 := by ring
        _ ≤ y := hyx0
    have hlogs : Real.log y / 4 ≤ Real.log (Nat.sqrt y) := Salt.TwinBar.log_natSqrt_ge hy16
    have hL4pos : 0 < Real.log y / 4 := by linarith
    have hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖MlambdaChi χ t (y / b)‖
          ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * (y : ℝ) / (b : ℝ) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      obtain ⟨hb1, hbs⟩ := hb
      have hbpos : 0 < b := hb1
      have hts : Nat.sqrt y ≤ y / b := by
        rw [Nat.le_div_iff_mul_le hbpos]
        calc Nat.sqrt y * b ≤ Nat.sqrt y * Nat.sqrt y := by gcongr
          _ ≤ y := Nat.sqrt_le y
      have htx : x₀lam ≤ y / b := le_trans hs_ge_x0 hts
      have hlogt : Real.log y / 4 ≤ Real.log ((y / b : ℕ) : ℝ) := by
        refine le_trans hlogs ?_
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt y))
        exact_mod_cast hts
      have hgate : (q : ℝ) ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ (11 : ℕ) := by
        have hratio : (1 : ℝ) ≤ Real.log y / (4 : ℝ) ^ (11 : ℕ) :=
          (one_le_div (by positivity)).mpr hlog4
        have h10 : (Real.log y) ^ (10 : ℕ) ≤ (Real.log y / 4) ^ (11 : ℕ) := by
          calc (Real.log y) ^ (10 : ℕ) = (Real.log y) ^ (10 : ℕ) * 1 := by ring
            _ ≤ (Real.log y) ^ (10 : ℕ) * (Real.log y / (4 : ℝ) ^ (11 : ℕ)) :=
                mul_le_mul_of_nonneg_left hratio (pow_nonneg hL0 10)
            _ = (Real.log y / 4) ^ (11 : ℕ) := by rw [div_pow]; ring
        have h11 : (Real.log y / 4) ^ (11 : ℕ)
            ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ (11 : ℕ) := by
          have h04 : (0 : ℝ) ≤ Real.log y / 4 := by linarith
          gcongr
        linarith
      have hht : |t| ≤ (Nat.sqrt (y / b) : ℝ) :=
        le_trans ht (by exact_mod_cast Nat.sqrt_le_sqrt hts)
      have hMt := hLamBound (y / b) htx q χ hgate t hht
      have hrpow : (Real.log y / 4) ^ A ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ A :=
        Real.rpow_le_rpow hL4pos.le hlogt hA.le
      have hcast : ((y / b : ℕ) : ℝ) ≤ (y : ℝ) / (b : ℝ) :=
        Nat.cast_div_le (m := y) (n := b) (α := ℝ)
      calc ‖MlambdaChi χ t (y / b)‖
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
    have hmono : ∀ b : ℕ,
        lamTailWeightMask mask r b / (b : ℝ) ≤ maskTailWeight mask r b / (b : ℝ) := by
      intro b
      have h := lamTailWeightMask_le_maskTailWeight (mask := mask) hr1 b
      gcongr
    have hsplit := norm_MlamGrChiMask_le_split χ t mask r y hr1 hBnn hsmall
      (le_trans (Finset.sum_le_sum fun b _ => hmono b) hmass)
      (le_trans (Finset.sum_le_sum fun b _ => hmono b) htail)
    calc ‖MlamGrChiMask χ t mask r y‖
        ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * M * (y : ℝ)
            + (1 / (Real.log y) ^ A) * (y : ℝ) := hsplit
      _ = (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
          field_simp
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨C * (4 : ℝ) ^ A * M + 1, N, hC'pos, hN⟩

/-! ## §6 — TWIN FIDELITY: the LANDED single-window λ page IS the `blockMask` instance -/

theorem lamGrMask_blockMask (P Q : ℕ) (r : ℝ) :
    lamGrMask (blockMask P Q) r = lamGr P Q r := by
  ext n
  rw [lamGrMask_apply, lamGr_apply, maskOmega_blockMask]

theorem lamTailWeightMask_blockMask (P Q : ℕ) (r : ℝ) :
    lamTailWeightMask (blockMask P Q) r = lamTailWeight P Q r := by
  ext n
  rw [lamTailWeightMask_apply, lamTailWeight_apply, maskTailWeight_blockMask]

theorem MlamGrChiMask_blockMask {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ) (r : ℝ)
    (y : ℕ) : MlamGrChiMask χ t (blockMask P Q) r y = MlamGrChi χ t P Q r y := by
  rw [MlamGrChiMask, MlamGrChi, lamGrMask_blockMask]

/-! ## §7 — ⟦THE SPLIT-HOIST⟧ (R3, 2026-07-30): THE THRESHOLD IS BORN BEFORE THE MASS

⟦K4-CENSUS's MOVE 1, link 1⟧  `MlamGrChiMask_rate` delivers `∃ C' x₀` as ONE block after the
mass budget `M`.  The census's byte-warrant is that only `C' = C·4^A·M + 1` reads `M`: the
threshold `x₀` is the `Filter.eventually_atTop` witness of a block whose three
`filter_upwards` arguments (`y ≥ 16`, `y ≥ x₀lam²`, `log y ≥ 4^11`) mention neither `M` nor
the mask, the modulus, the character, the height or `r` — it is `Aexp`-ONLY, i.e. a function
of `hMmu` and `A` alone.

So the `∀ M` may be moved INSIDE the eventual block and the two constants split:

  `∃ x₀, ∀ M ≥ 0, ∃ C' > 0, ∀ y ≥ x₀, …`

This is the head of the seven-link chain that carries the split all the way to the capstone
(`piece_partial_sum_rate_split` → `m4_hpiece_at_door_split` →
`m4_hT0band_at_door_discharged_split` → `M4SocketDischarge.m4_hband_at_door_slot_split` →
`S11Hoist`'s two split terminals → `S12Compose.logChowla2_capstone_final`).  PURELY ADDITIVE
and analytically EMPTY: the proof is the landed one with the `intro M` moved. -/

/-- **⟦D3, SPLIT-HOISTED⟧ THE RATE AT AN ARBITRARY MASK, THRESHOLD FIRST**
(`MlamGrChiMask_rate_split`) — `MlamGrChiMask_rate` with `x₀` quantified BEFORE the mass
budget `M` and `C'` left after it.  Conclusion, gates and constants byte-identical
(`C' = C·4^A·M + 1`, `x₀ = N`); no hypothesis is added or weakened. -/
theorem MlamGrChiMask_rate_split (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℕ, ∀ M : ℝ, 0 ≤ M → ∃ C' : ℝ, 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) →
            ∀ (mask : ℕ → Bool) (r : ℝ), 0 ≤ r → r ≤ 1 →
              (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask r b / (b : ℝ)) ≤ M →
              (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask r b / (b : ℝ))
                  ≤ 1 / (Real.log y) ^ A →
              ‖MlamGrChiMask χ t mask r y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C, x₀lam, hCpos, hLamBound⟩ := MlambdaChi_rate hMmu A hA
  have h4A : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have key : ∀ᶠ y : ℕ in Filter.atTop,
      ∀ M : ℝ, 0 ≤ M →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) →
            ∀ (mask : ℕ → Bool) (r : ℝ), 0 ≤ r → r ≤ 1 →
              (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), maskTailWeight mask r b / (b : ℝ)) ≤ M →
              (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, maskTailWeight mask r b / (b : ℝ))
                  ≤ 1 / (Real.log y) ^ A →
              ‖MlamGrChiMask χ t mask r y‖
                ≤ (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
    filter_upwards [Filter.eventually_ge_atTop 16, Filter.eventually_ge_atTop (x₀lam ^ 2),
        eventually_log_ge_lamMask ((4 : ℝ) ^ (11 : ℕ))] with y hy16 hyx0 hlog4
    intro M hM q _ χ hq t ht mask r hr0 hr1 hmass htail
    have hLpos : 0 < Real.log y := lt_of_lt_of_le (by positivity) hlog4
    have hL0 : (0 : ℝ) ≤ Real.log y := hLpos.le
    have hLApos : (0 : ℝ) < (Real.log y) ^ A := Real.rpow_pos_of_pos hLpos A
    have hs1 : 1 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by nlinarith [hy16])
    have hs_ge_x0 : x₀lam ≤ Nat.sqrt y := by
      rw [Nat.le_sqrt]
      calc x₀lam * x₀lam = x₀lam ^ 2 := by ring
        _ ≤ y := hyx0
    have hlogs : Real.log y / 4 ≤ Real.log (Nat.sqrt y) := Salt.TwinBar.log_natSqrt_ge hy16
    have hL4pos : 0 < Real.log y / 4 := by linarith
    have hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖MlambdaChi χ t (y / b)‖
          ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * (y : ℝ) / (b : ℝ) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      obtain ⟨hb1, hbs⟩ := hb
      have hbpos : 0 < b := hb1
      have hts : Nat.sqrt y ≤ y / b := by
        rw [Nat.le_div_iff_mul_le hbpos]
        calc Nat.sqrt y * b ≤ Nat.sqrt y * Nat.sqrt y := by gcongr
          _ ≤ y := Nat.sqrt_le y
      have htx : x₀lam ≤ y / b := le_trans hs_ge_x0 hts
      have hlogt : Real.log y / 4 ≤ Real.log ((y / b : ℕ) : ℝ) := by
        refine le_trans hlogs ?_
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt y))
        exact_mod_cast hts
      have hgate : (q : ℝ) ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ (11 : ℕ) := by
        have hratio : (1 : ℝ) ≤ Real.log y / (4 : ℝ) ^ (11 : ℕ) :=
          (one_le_div (by positivity)).mpr hlog4
        have h10 : (Real.log y) ^ (10 : ℕ) ≤ (Real.log y / 4) ^ (11 : ℕ) := by
          calc (Real.log y) ^ (10 : ℕ) = (Real.log y) ^ (10 : ℕ) * 1 := by ring
            _ ≤ (Real.log y) ^ (10 : ℕ) * (Real.log y / (4 : ℝ) ^ (11 : ℕ)) :=
                mul_le_mul_of_nonneg_left hratio (pow_nonneg hL0 10)
            _ = (Real.log y / 4) ^ (11 : ℕ) := by rw [div_pow]; ring
        have h11 : (Real.log y / 4) ^ (11 : ℕ)
            ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ (11 : ℕ) := by
          have h04 : (0 : ℝ) ≤ Real.log y / 4 := by linarith
          gcongr
        linarith
      have hht : |t| ≤ (Nat.sqrt (y / b) : ℝ) :=
        le_trans ht (by exact_mod_cast Nat.sqrt_le_sqrt hts)
      have hMt := hLamBound (y / b) htx q χ hgate t hht
      have hrpow : (Real.log y / 4) ^ A ≤ (Real.log ((y / b : ℕ) : ℝ)) ^ A :=
        Real.rpow_le_rpow hL4pos.le hlogt hA.le
      have hcast : ((y / b : ℕ) : ℝ) ≤ (y : ℝ) / (b : ℝ) :=
        Nat.cast_div_le (m := y) (n := b) (α := ℝ)
      calc ‖MlambdaChi χ t (y / b)‖
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
    have hmono : ∀ b : ℕ,
        lamTailWeightMask mask r b / (b : ℝ) ≤ maskTailWeight mask r b / (b : ℝ) := by
      intro b
      have h := lamTailWeightMask_le_maskTailWeight (mask := mask) hr1 b
      gcongr
    have hsplit := norm_MlamGrChiMask_le_split χ t mask r y hr1 hBnn hsmall
      (le_trans (Finset.sum_le_sum fun b _ => hmono b) hmass)
      (le_trans (Finset.sum_le_sum fun b _ => hmono b) htail)
    calc ‖MlamGrChiMask χ t mask r y‖
        ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * M * (y : ℝ)
            + (1 / (Real.log y) ^ A) * (y : ℝ) := hsplit
      _ = (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
          field_simp
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  refine ⟨N, ?_⟩
  intro M hM
  refine ⟨C * (4 : ℝ) ^ A * M + 1, ?_, fun y hy => hN y hy M hM⟩
  have h : (0 : ℝ) ≤ C * (4 : ℝ) ^ A * M := mul_nonneg (mul_nonneg hCpos.le h4A.le) hM
  linarith

end Salt.MR
