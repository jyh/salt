/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MobiusChiRamare

/-!
# ⟦D3 — CARRIER PAGE 1⟧ THE λ-TRANSPOSITION of the `g_r` perturbation

Design: the 0730 council's item **C5** (`docs/blueprints/flags.md`, ⟦THE 0730 COUNCIL⟧) and
`docs/exploration/a4-bridge-freeze-0730.md` §"D3 re-priced".  `MobiusChiRamare.lean` (⟦O6⟧)
lands the Ramaré-damped rate at the **Möbius** datum; D3's consumer sums the **Liouville**
datum (`m4_hT0band_at_door`'s `hpiece` reads `pieceDatum χ 𝒥 … = liouChi χ · g_𝒥`,
`CofactorSupplier.lean:71`).  This file is O6's λ-twin: purely ADDITIVE, no landed
declaration touched.

## THE MATHEMATICS — and ⟦THE ONE PLACE THE BRIEF'S MECHANISM IS FALSE⟧

The brief (REF-A4-4) proposed transposing through
`(λ·g)(n) = ∑_{d²∣n} (μ·g)(n/d²)·g(d)²`.  **That identity needs `g` COMPLETELY
multiplicative, and `g_r(n) = r^{ω(n;P,Q)}` is NOT** (`g_r(p²) = r ≠ r² = g_r(p)²`;
the counterexample `P = Q = p`, `n = p²`, `d = p` reads `r` on the left and `r²` on the
right).  So the λ-side fold is NOT the `d²`-fold of `MlambdaChi_eq_sum_MmuChi` with a damped
inner sum — that route is closed.

The honest transposition is O6's OWN device (a Dirichlet convolution against a window
carrier), run at `λ` instead of `μ`.  Reading the Euler factors: `λ·g_r` is multiplicative
with `(λ·g_r)(p^k) = (−1)^k r^{1_{[P,Q]}(p)}`, so

  `D(λ·g_r)(s) = D(λ)(s) · ∏_{P≤p≤Q} (1 + (1−r)p^{−s})`,

because at a window prime `[1 + r∑_{k≥1}(−1)^kp^{−ks}]/[1/(1+p^{−s})] = 1 + (1−r)p^{−s}` and
off the window the ratio is `1`.  Reading off the coefficients — `(1−r)` at `p¹`, **`0` at
every `p^k`, `k ≥ 2`** — gives the λ-side carrier as the SQUAREFREE RESTRICTION of O6's
`w_r`:

  `v_r(n) = μ(n)²·w_r(n) = (1−r)^{ω(n;P,Q)}` on squarefree window-smooth `n`, `0` otherwise,

and the identity this file proves is

  **`λ·g_r = λ ∗ v_r`**  (`liouville_mul_lamTailWeight`, verified at prime powers).

Everything downstream is then O6's §4–§6, verbatim, with `(μ, w_r) → (λ, v_r)` and the
twisted Möbius rate replaced by the twisted **Liouville** rate `MlambdaChi_rate` — which is
where the price is paid (below).

## WHY THE CONSUMER PAYS NOTHING NEW FOR THE CARRIER SWAP

`v_r ≤ w_r` pointwise (`lamTailWeight_le_ramTailWeight`: `μ² ≤ 1` and `w_r ≥ 0` for
`r ≤ 1`), so **both deliverables below carry O6's OWN mass/tail hypotheses, on
`ramTailWeight`, byte-identical to `MmuGrChi_rate`/`MmuRamChi_rate`'s**.  D3's mass page and
Rankin-tail page (the other two owed carrier pages) are therefore discharged ONCE and serve
the μ-side and the λ-side together.  Nothing about the squarefree restriction leaks into the
hypotheses; it only ever helps.

## THE PRICE, STATED HONESTLY (the composed range fit)

The λ-side rate is reached by TWO sequential folds — `MmuChiRate → MlambdaChi_rate`
(`LambdaRateTwisted`, LANDED) and then `MlambdaChi_rate → MlamGrChi_rate` (here) — and each
fold spends exactly one conductor exponent and one height halving, because each invokes its
input rate at `⌊y/·⌋ ≥ √y` where only `log⌊y/·⌋ ≥ (log y)/4` and `√y ≤ ⌊y/·⌋` are available:

| slot | conductor gate | height gate |
|---|---|---|
| `MmuChiRate` (landed) | `q ≤ (log y)^12` | `|t| ≤ y` |
| `MlambdaChi_rate` (landed) | `q ≤ (log y)^11` | `|t| ≤ ⌊√y⌋` |
| `MlamGrChi_rate` / `MlamRamChi_rate` (**here**) | `q ≤ (log y)^10` | `|t| ≤ ⌊√⌊√y⌋⌋ ≈ y^{1/4}` |

Both survivals are wide, and the file says where they are paid:

* **conductor.**  The consumer's gate is `q ≤ arcDen 12 H ≍ (log H)^12` at the door, read at
  `y ≍ X_d` (REF-A4-4's range fit, checked at the small-`k` corner).  `(log H)^12 ≤ (log y)^10`
  as soon as `log H ≤ (log y)^{5/6}`, i.e. `ℓ ≥ 1.2·loglog H`-genre — the fit REF-A4-4
  confirmed at `ℓ ≥ 1.09λ` with two exponents to spare.  Paid in `hgate` inside
  `MlamGrChi_rate` (`log y ≥ 4^11`, an eventual threshold folded into `x₀`).
* **height.**  The consumer's band is `|t| ≤ seamT0 X = (log X)^{1/45}` (`SeamSplit.lean:92`);
  `y^{1/4}` beats `(log y)^{1/45}` beyond words.  Paid in `hht` (`Nat.sqrt_le_sqrt` against
  `√y ≤ ⌊y/b⌋`).
* **log scale.**  One factor `4^A`, from the landed `Salt.TwinBar.log_natSqrt_ge`.

⟦the four log scales, kept apart⟧ `log y` (the statement), `log⌊y/b⌋` (where the λ-rate
fires — the `4^A` and the exponent are spent there), `log √y = (log y)/2 ≥ (log y)/4` (the
absorbed floor), and `log Q/log P` (the WINDOW scale, confined to the named hypotheses `M, ε`
exactly as in O6).  `P, Q` appear nowhere else.

## Contents

* **§1** `lamGr` — the damped Liouville datum `λ·g_r` (`ArithmeticFunction ℝ`) and its
  multiplicativity.
* **§2** `lamTailWeight` — the carrier `v_r = μ²·w_r`, its closed form, positivity, support
  (squarefree ∧ window-smooth), the domination `v_r ≤ w_r`, antitonicity in `r`,
  multiplicativity, and the prime-power coefficients (`(1−r)` at `p¹`, `0` above).
* **§3** THE VERIFICATION `lamTailWeight_mul_liouville` / `liouville_mul_lamTailWeight`
  (`λ ∗ v_r = λ·g_r`, checked at prime powers) and its pointwise/twisted antidiagonal forms.
* **§4** `sum_filter_dvd_div_eq` (the datum-GENERIC multiples bijection — O6's
  `MmuChi_inner_dvd` with the coefficient freed), `MlambdaChi_inner_dvd`, `MlamGrChi`, and
  the twisted hyperbola fold `MlamGrChi_eq_sum` (UNCONDITIONAL).
* **§5** `norm_MlambdaChi_le` (the crude tail bound), `norm_MlamGrChi_le_split` (the
  unconditional two-row split) and THE DELIVERABLE `MlamGrChi_rate`.
* **§6** `MlamRamChi`, `MlamRamChi_eq_integral` (the `∫₀¹ dr` composition through the LANDED
  `integral_cpow_unit`), `norm_MlamRamChi_le_of_uniform`, and the Ramaré-WEIGHTED deliverable
  `MlamRamChi_rate` — hypotheses at `r = 0`, identical to `MmuRamChi_rate`'s.

Explicit constants throughout; no `O(·)` in any statement.  The only hypothesis anywhere is
the landed slot `MmuChiRate`.
-/

open scoped BigOperators

namespace Salt.MR

/-! ## §1 — the damped Liouville datum `λ·g_r` -/

private lemma blockOmega_one_lam (P Q : ℕ) : blockOmega P Q 1 = 0 := by
  simp [blockOmega, BlockPrimeDivs]

private lemma blockOmega_prime_pow_lam {P Q p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    blockOmega P Q (p ^ k) = if P ≤ p ∧ p ≤ Q then 1 else 0 := by
  unfold blockOmega BlockPrimeDivs
  rw [Nat.primeFactors_prime_pow hk hp, Finset.filter_singleton]
  by_cases h : P ≤ p ∧ p ≤ Q
  · rw [if_pos h, if_pos h, Finset.card_singleton]
  · rw [if_neg h, if_neg h, Finset.card_empty]

/-- **The damped Liouville datum** `(λ·g_r)(m) = λ(m)·r^{ω(m;P,Q)}` as an
`ArithmeticFunction ℝ` — the λ-twin of `Salt.MR.muGr`.  `ω(·;P,Q)` is the corpus's window
prime count `Salt.MR.blockOmega`; `RamWeight` writes the damping parameter `x`, the freeze and
this file write `r`.  At `m = 0` the value is `0` because `λ 0 = 0`. -/
noncomputable def lamGr (P Q : ℕ) (r : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => ((ArithmeticFunction.liouville m : ℤ) : ℝ) * r ^ blockOmega P Q m, by simp⟩

@[simp] lemma lamGr_apply (P Q : ℕ) (r : ℝ) (m : ℕ) :
    lamGr P Q r m = ((ArithmeticFunction.liouville m : ℤ) : ℝ) * r ^ blockOmega P Q m := rfl

/-- **`λ·g_r` is multiplicative.**  `λ` is (`ArithmeticFunction.isMultiplicative_liouville`;
it is even completely multiplicative) and `ω(·;P,Q)` is additive on coprimes — the LANDED
`Salt.MR.blockOmega_mul_coprime`.  Note `λ·g_r` is **not** completely multiplicative: `g_r`
is not (see the header's refutation of the `g(d)²` mechanism). -/
theorem lamGr_isMultiplicative (P Q : ℕ) (r : ℝ) : (lamGr P Q r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [lamGr_apply, blockOmega_one_lam, pow_zero, ArithmeticFunction.liouville_apply_one]
    norm_num
  · intro m n _ _ hmn
    simp only [lamGr_apply]
    rw [ArithmeticFunction.isMultiplicative_liouville.map_mul_of_coprime hmn,
      blockOmega_mul_coprime hmn, pow_add]
    push_cast
    ring

/-! ## §2 — the λ-side window carrier `v_r = μ²·w_r` -/

/-- **THE λ-SIDE CARRIER `v_r`** — the multiplicative function with local factor
`1 + (1−r)p^{−s}` at window primes `p ∈ [P,Q]` and local factor `1` off the window, carried
as the SQUAREFREE RESTRICTION of O6's `ramTailWeight`:

  `v_r(n) = μ(n)²·w_r(n)`,  i.e. `(1−r)^{ω(n;P,Q)}` on squarefree window-smooth `n` and `0`
  otherwise.

The `μ²` factor is exactly the "`0` at every `p^k`, `k ≥ 2`" of the local factor — the ONE
structural difference from the Möbius side, where the local factor
`(1 − rp^{−s})/(1 − p^{−s})` has the coefficient `(1−r)` at EVERY `p^k`.  Carrying `v_r` as
`μ² · w_r` (rather than as a fresh closed form) is what makes positivity, the support, the
antitonicity in `r` and — decisively — the DOMINATION `v_r ≤ w_r` one-liners over the landed
O6 facts, so that no new mass or tail hypothesis is created. -/
noncomputable def lamTailWeight (P Q : ℕ) (r : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 * ramTailWeight P Q r n, by simp⟩

@[simp] lemma lamTailWeight_apply (P Q : ℕ) (r : ℝ) (n : ℕ) :
    lamTailWeight P Q r n
      = ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 * ramTailWeight P Q r n := rfl

/-- The closed form on the support: `v_r(n) = (1−r)^{ω(n;P,Q)}` for squarefree window-smooth
`n`.  (`Squarefree n` forces `n ≠ 0`, so O6's explicit nonvanishing guard is discharged
here.) -/
theorem lamTailWeight_apply_of {P Q : ℕ} (r : ℝ) {n : ℕ} (hn : Squarefree n)
    (hs : WindowSmooth P Q n) : lamTailWeight P Q r n = (1 - r) ^ blockOmega P Q n := by
  rw [lamTailWeight_apply, ramTailWeight_apply_of r hn.ne_zero hs,
    ArithmeticFunction.moebius_apply_of_squarefree hn]
  push_cast
  have hsq : ((-1 : ℝ) ^ ArithmeticFunction.cardFactors n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hsq, one_mul]

theorem lamTailWeight_eq_zero_of_not_squarefree {P Q : ℕ} (r : ℝ) {n : ℕ}
    (hn : ¬ Squarefree n) : lamTailWeight P Q r n = 0 := by
  rw [lamTailWeight_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  norm_num

theorem lamTailWeight_eq_zero_of_not_smooth {P Q : ℕ} (r : ℝ) {n : ℕ}
    (hs : ¬ WindowSmooth P Q n) : lamTailWeight P Q r n = 0 := by
  rw [lamTailWeight_apply, ramTailWeight_eq_zero_of_not_smooth r hs, mul_zero]

/-- **KEY POSITIVITY** (the λ-twin of `ramTailWeight_nonneg`): for `r ≤ 1` every value of
`v_r` is `≥ 0`, so the ℓ¹(1/n) mass hypotheses may be stated on `v_r` itself. -/
theorem lamTailWeight_nonneg {P Q : ℕ} {r : ℝ} (hr1 : r ≤ 1) (n : ℕ) :
    0 ≤ lamTailWeight P Q r n := by
  rw [lamTailWeight_apply]
  exact mul_nonneg (sq_nonneg _) (ramTailWeight_nonneg hr1 n)

/-- **THE DOMINATION — the reason this page costs the consumer nothing.**  `v_r ≤ w_r`
pointwise (`μ² ≤ 1`, `w_r ≥ 0`), so every mass/tail hypothesis stated on O6's
`ramTailWeight` implies its `lamTailWeight` counterpart.  Both deliverables of §5–§6 are
stated at O6's hypotheses because of this lemma. -/
theorem lamTailWeight_le_ramTailWeight {P Q : ℕ} {r : ℝ} (hr1 : r ≤ 1) (n : ℕ) :
    lamTailWeight P Q r n ≤ ramTailWeight P Q r n := by
  rw [lamTailWeight_apply]
  refine mul_le_of_le_one_left (ramTailWeight_nonneg hr1 n) ?_
  have hcast : ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2
      = (((ArithmeticFunction.moebius n ^ 2 : ℤ)) : ℝ) := by push_cast; ring
  rw [hcast, ArithmeticFunction.moebius_sq]
  split_ifs <;> norm_num

/-- **THE SUPPORT.**  `v_r` vanishes off the SQUAREFREE `[P,Q]`-window-smooth numbers — the
squarefree half is the new content (O6's `w_r` is supported on all window-smooth `n`). -/
theorem lamTailWeight_support {P Q : ℕ} {r : ℝ} {n : ℕ} (h : lamTailWeight P Q r n ≠ 0) :
    Squarefree n ∧ WindowSmooth P Q n := by
  have h2 : ramTailWeight P Q r n ≠ 0 := fun h0 => h (by rw [lamTailWeight_apply, h0, mul_zero])
  refine ⟨?_, (ramTailWeight_support h2).2⟩
  by_contra hc
  exact h (lamTailWeight_eq_zero_of_not_squarefree r hc)

/-- **ANTITONICITY IN THE DAMPING** (the λ-twin of `ramTailWeight_le_zero_param`): for
`r ∈ [0,1]`, `v_r ≤ v_0` pointwise.  With the domination above this is what makes §6's
`∫₀¹ dr` composition free at hypotheses pinned at `r = 0`. -/
theorem lamTailWeight_le_zero_param {P Q : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    lamTailWeight P Q r n ≤ lamTailWeight P Q 0 n := by
  rw [lamTailWeight_apply, lamTailWeight_apply]
  exact mul_le_mul_of_nonneg_left (ramTailWeight_le_zero_param hr0 hr1 n) (sq_nonneg _)

/-- **`v_r` is multiplicative** — `μ` is, `w_r` is (the LANDED
`ramTailWeight_isMultiplicative`), and a pointwise product of multiplicative functions is
multiplicative. -/
theorem lamTailWeight_isMultiplicative (P Q : ℕ) (r : ℝ) :
    (lamTailWeight P Q r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [lamTailWeight_apply, (ramTailWeight_isMultiplicative P Q r).map_one,
      ArithmeticFunction.moebius_apply_one]
    norm_num
  · intro m n _ _ hmn
    simp only [lamTailWeight_apply]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
      (ramTailWeight_isMultiplicative P Q r).map_mul_of_coprime hmn]
    push_cast
    ring

/-- **THE LOCAL FACTOR'S COEFFICIENTS — the auditable half of the verification.**  For
`k ≥ 1`,

  `v_r(p^k) = 1 − r` if `k = 1` and `P ≤ p ≤ Q`,   `v_r(p^k) = 0` otherwise,

i.e. exactly the coefficients of `1 + (1−r)p^{−s}` (window) and `1` (off window).  Contrast
`ramTailWeight_prime_pow`, where the coefficient is `(1−r)` for EVERY `k ≥ 1`: the difference
is the `ζ(s)` that the Möbius side's local factor carries in its denominator and the
Liouville side's does not. -/
theorem lamTailWeight_prime_pow {P Q p k : ℕ} (r : ℝ) (hp : p.Prime) (hk : k ≠ 0) :
    lamTailWeight P Q r (p ^ k)
      = if k = 1 then (if P ≤ p ∧ p ≤ Q then 1 - r else 0) else 0 := by
  rw [lamTailWeight_apply, ramTailWeight_prime_pow r hp hk,
    ArithmeticFunction.moebius_apply_prime_pow hp hk]
  by_cases hk1 : k = 1
  · simp only [if_pos hk1]
    norm_num
  · simp only [if_neg hk1]
    norm_num

/-! ## §3 — THE CONVOLUTION IDENTITY `λ·g_r = λ ∗ v_r` -/

private lemma liouville_prime_pow_real {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((ArithmeticFunction.liouville (p ^ j) : ℤ) : ℝ) = (-1) ^ j := by
  rw [ArithmeticFunction.liouville_apply (pow_ne_zero j hp.ne_zero),
    ArithmeticFunction.cardFactors_apply_prime_pow hp]
  push_cast
  ring

/-- **THE VERIFICATION OF THE CARRIER** (the one genuinely new arithmetic page of the
λ-transposition), in the orientation the prime-power check likes:

  `v_r ∗ λ = λ·g_r`.

Both sides are multiplicative, so `IsMultiplicative.eq_iff_eq_on_prime_powers` reduces to
`p^k`, `k = j+1 ≥ 1`, where only `i ∈ {0,1}` survives in
`∑_{i≤k} v_r(p^i)·λ(p^{k−i})` (that is the `μ²` factor of `v_r` at work):

  `λ(p^{j+1}) + 1_{[P,Q]}(p)·(1−r)·λ(p^j) = (−1)^{j+1}·r^{1_{[P,Q]}(p)}`,

since `(−1)^{j+1} + (1−r)(−1)^j = (−1)^j(−1 + 1 − r) = (−1)^{j+1}r` at a window prime and
`(−1)^{j+1}` off it — which is precisely reading off `1 + (1−r)p^{−s}`. -/
theorem lamTailWeight_mul_liouville (P Q : ℕ) (r : ℝ) :
    lamTailWeight P Q r
        * ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
      = lamGr P Q r := by
  have hliou : (((ArithmeticFunction.liouville : ArithmeticFunction ℤ) :
      ArithmeticFunction ℝ)).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_liouville.intCast
  have hmulti : (lamTailWeight P Q r
      * ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) :
        ArithmeticFunction ℝ)).IsMultiplicative :=
    (lamTailWeight_isMultiplicative P Q r).mul hliou
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmulti _
    (lamGr_isMultiplicative P Q r)]
  intro p k hp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, hmulti.map_one, (lamGr_isMultiplicative P Q r).map_one]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  -- the convolution at `p^(j+1)`, in divisors form
  rw [ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.intCoe_apply]
  rw [Nat.sum_divisorsAntidiagonal
      (fun a b => lamTailWeight P Q r a * ((ArithmeticFunction.liouville b : ℤ) : ℝ)),
    Nat.sum_divisors_prime_pow hp]
  -- reduce `p^(j+1)/p^i` to `p^(j+1-i)`
  have hcong : ∀ i ∈ Finset.range (j + 1 + 1),
      lamTailWeight P Q r (p ^ i)
          * ((ArithmeticFunction.liouville (p ^ (j + 1) / p ^ i) : ℤ) : ℝ)
        = lamTailWeight P Q r (p ^ i)
          * ((ArithmeticFunction.liouville (p ^ (j + 1 - i)) : ℤ) : ℝ) := by
    intro i hi
    have hi' : i ≤ j + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [Nat.pow_div hi' hp.pos]
  rw [Finset.sum_congr rfl hcong]
  -- trim to `i ∈ {0,1}`: `v_r(p^i) = 0` for `i ≥ 2` (the squarefree restriction)
  have hsub : Finset.range 2 ⊆ Finset.range (j + 1 + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hzero : ∀ i ∈ Finset.range (j + 1 + 1), i ∉ Finset.range 2 →
      lamTailWeight P Q r (p ^ i)
          * ((ArithmeticFunction.liouville (p ^ (j + 1 - i)) : ℤ) : ℝ) = 0 := by
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [lamTailWeight_prime_pow r hp (by omega : i ≠ 0), if_neg (by omega : ¬ i = 1), zero_mul]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
    (lamTailWeight_isMultiplicative P Q r).map_one]
  simp only [Nat.sub_zero, Nat.add_sub_cancel]
  rw [lamTailWeight_prime_pow r hp one_ne_zero, if_pos rfl, lamGr_apply,
    blockOmega_prime_pow_lam hp (Nat.succ_ne_zero j), liouville_prime_pow_real hp,
    liouville_prime_pow_real hp]
  by_cases hwin : P ≤ p ∧ p ≤ Q
  · simp only [if_pos hwin]
    ring
  · simp only [if_neg hwin]
    ring

/-- **THE CONVOLUTION IDENTITY, `ArithmeticFunction`-level**: `λ ∗ v_r = λ·g_r`.  The λ-twin
of `Salt.MR.mu_mul_ramTailWeight`; UNCONDITIONAL. -/
theorem liouville_mul_lamTailWeight (P Q : ℕ) (r : ℝ) :
    ((ArithmeticFunction.liouville : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * lamTailWeight P Q r = lamGr P Q r := by
  rw [mul_comm]
  exact lamTailWeight_mul_liouville P Q r

/-- **THE CONVOLUTION IDENTITY, pointwise** (the form the fold consumes): for every `m`,

  `λ(m)·r^{ω(m;P,Q)} = ∑_{ab = m} λ(a)·v_r(b)`.

Holds at `m = 0` too (both sides `0`). -/
theorem lamGr_eq_sum_divisorsAntidiagonal (P Q : ℕ) (r : ℝ) (m : ℕ) :
    ((ArithmeticFunction.liouville m : ℤ) : ℝ) * r ^ blockOmega P Q m
      = ∑ ab ∈ m.divisorsAntidiagonal,
          ((ArithmeticFunction.liouville ab.1 : ℤ) : ℝ) * lamTailWeight P Q r ab.2 := by
  rw [← lamGr_apply, ← liouville_mul_lamTailWeight, ArithmeticFunction.mul_apply]
  exact Finset.sum_congr rfl fun ab _ => by rw [ArithmeticFunction.intCoe_apply]

/-- **The twist distributes over `λ·g_r = λ ∗ v_r`** (for `m ≠ 0`) — the ℂ-side of the
pointwise identity, through `chiBarTwist_mul` (complete multiplicativity of the twist on
nonzero arguments).  ⟦DEVIATION, inherited from `MobiusChiRamare`⟧
`LambdaRateTwisted.mul_apply_mul_twist` is CITED, not instantiated: its `f g h` live in ONE
ring while the carriers here are `ArithmeticFunction ℝ` (so `v_r ≥ 0` is first-class) and the
twist is ℂ-valued. -/
theorem lamGr_twist_eq_sum_divisorsAntidiagonal {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (P Q : ℕ) (r : ℝ) {m : ℕ} (hm : m ≠ 0) :
    ((lamGr P Q r m : ℝ) : ℂ) * chiBarTwist χ t m
      = ∑ ab ∈ m.divisorsAntidiagonal,
          (((ArithmeticFunction.liouville ab.1 : ℤ) : ℂ) * chiBarTwist χ t ab.1)
            * (((lamTailWeight P Q r ab.2 : ℝ) : ℂ) * chiBarTwist χ t ab.2) := by
  have hR := lamGr_eq_sum_divisorsAntidiagonal P Q r m
  have hC : ((lamGr P Q r m : ℝ) : ℂ)
      = ∑ ab ∈ m.divisorsAntidiagonal,
          ((ArithmeticFunction.liouville ab.1 : ℤ) : ℂ)
            * ((lamTailWeight P Q r ab.2 : ℝ) : ℂ) := by
    rw [lamGr_apply, hR]
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

/-- **The multiples bijection, DATUM-GENERIC**: `∑_{m ≤ y, b ∣ m} c(m/b) = ∑_{a ≤ ⌊y/b⌋} c(a)`
by `m = b·a`, for any coefficient `c` in any `AddCommMonoid`.  This is
`Salt.MR.MmuChi_inner_dvd`'s bijection with the coefficient freed — stated once here so the
λ-side does not re-run it (and available to any later carrier page). -/
theorem sum_filter_dvd_div_eq {M : Type*} [AddCommMonoid M] (c : ℕ → M) (y b : ℕ)
    (hb : 1 ≤ b) :
    ∑ m ∈ (Finset.Icc 1 y).filter (fun m => b ∣ m), c (m / b)
      = ∑ a ∈ Finset.Icc 1 (y / b), c a := by
  have hb0 : 0 < b := hb
  refine Finset.sum_bij' (fun m _ => m / b) (fun a _ => b * a) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmy⟩, hdvd⟩ := hm
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hb0).mpr (Nat.le_of_dvd (by omega) hdvd),
      Nat.div_le_div_right hmy⟩
  · intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨ha1, hay⟩ := ha
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Nat.mul_pos hb0 (by omega)
    · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hb0).mp hay
  · intro m hm
    rw [Finset.mem_filter] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro a _
    exact Nat.mul_div_cancel_left a hb0
  · intro m _
    rfl

/-- **The inner multiples bijection at a general divisor `b`, λ-side**:
`∑_{m ≤ y, b ∣ m} λ(m/b)χ̄(m/b)(m/b)^{it} = M_{λχ̄}(⌊y/b⌋)` — the λ-twin of
`Salt.MR.MmuChi_inner_dvd`, now an instance of the generic bijection. -/
theorem MlambdaChi_inner_dvd {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y b : ℕ)
    (hb : 1 ≤ b) :
    ∑ m ∈ (Finset.Icc 1 y).filter (fun m => b ∣ m),
        (((ArithmeticFunction.liouville (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
      = MlambdaChi χ t (y / b) := by
  rw [MlambdaChi]
  exact sum_filter_dvd_div_eq
    (fun a => ((ArithmeticFunction.liouville a : ℤ) : ℂ) * chiBarTwist χ t a) y b hb

/-- **The twisted damped Liouville summatory function**
`M_{λg_rχ̄}(y) = ∑_{m ≤ y} λ(m)r^{ω(m;P,Q)}χ̄(m)m^{it}`, ℂ-valued — the λ-twin of
`Salt.MR.MmuGrChi`.  ⟦barred χ⟧ the twist is the corpus's `chiBarTwist`. -/
noncomputable def MlamGrChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ) (r : ℝ)
    (y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 y, ((lamGr P Q r m : ℝ) : ℂ) * chiBarTwist χ t m

/-- **THE TWISTED HYPERBOLA FOLD (UNCONDITIONAL)**:

  `∑_{m ≤ y} λ(m)g_r(m)χ̄(m)m^{it} = ∑_{b ≤ y} v_r(b)χ̄(b)b^{it} · M_{λχ̄}(⌊y/b⌋)`.

The λ-twin of `Salt.MR.MmuGrChi_eq_sum`, at the carrier `v_r` and the twisted **Liouville**
inner sum.  No hypothesis on `r`, `P`, `Q`. -/
theorem MlamGrChi_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ) (r : ℝ)
    (y : ℕ) :
    MlamGrChi χ t P Q r y
      = ∑ b ∈ Finset.Icc 1 y,
          (((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MlambdaChi χ t (y / b) := by
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
  -- STEP A: the pointwise identity, reindexed by the `v_r`-argument `b`
  have hpt : ∀ m ∈ Finset.Icc 1 y,
      ((lamGr P Q r m : ℝ) : ℂ) * chiBarTwist χ t m
        = ∑ b ∈ Finset.Icc 1 y,
            (if b ∣ m then
              (((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b)
                * (((ArithmeticFunction.liouville (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
             else 0) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    rw [lamGr_twist_eq_sum_divisorsAntidiagonal χ t P Q r hm0]
    rw [Nat.sum_divisorsAntidiagonal' (n := m)
      (f := fun a b => (((ArithmeticFunction.liouville a : ℤ) : ℂ) * chiBarTwist χ t a)
        * (((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b))]
    rw [← hdivfilter m hm.1 hm.2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · ring
    · rfl
  -- STEP B: swap the sums, pull out the `b`-factor, collapse the inner sum
  rw [MlamGrChi, Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  have hpull : ∀ m : ℕ,
      (if b ∣ m then
        (((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b)
          * (((ArithmeticFunction.liouville (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
       else 0)
      = (((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b)
          * (if b ∣ m then
              (((ArithmeticFunction.liouville (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
             else 0) := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => hpull m), ← Finset.mul_sum, ← Finset.sum_filter,
    MlambdaChi_inner_dvd χ t y b hb.1]

/-! ## §5 — the rate transfer -/

/-- **Crude bound** `‖M_{λχ̄}(y)‖ ≤ y` — the λ-twin of `Salt.MR.norm_MmuChi_le`
(`|λ(n)| = 1` for `n ≥ 1` and `‖χ̄(n)n^{it}‖ ≤ 1`).  This is the ONLY bound available on the
`b > √y` row of the split below. -/
theorem norm_MlambdaChi_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ) :
    ‖MlambdaChi χ t y‖ ≤ (y : ℝ) := by
  unfold MlambdaChi
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ n ∈ Finset.Icc 1 y,
          ‖((ArithmeticFunction.liouville n : ℤ) : ℂ) * chiBarTwist χ t n‖
      ≤ ∑ _n ∈ Finset.Icc 1 y, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hn0 : n ≠ 0 := by omega
        have hlam : ((ArithmeticFunction.liouville n : ℤ) : ℂ)
            = (-1) ^ ArithmeticFunction.cardFactors n := by
          rw [ArithmeticFunction.liouville_apply hn0]
          push_cast
          ring
        rw [norm_mul, hlam, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact norm_chiBarTwist_le_one χ t n
    _ = (y : ℝ) := by rw [Finset.sum_const, Nat.card_Icc]; simp

/-- **THE TWO-ROW SPLIT (UNCONDITIONAL).**  Given
* a per-`b` bound `‖M_{λχ̄}(⌊y/b⌋)‖ ≤ B·y/b` on the SMALL range `b ≤ √y` (in the deliverable
  this is the twisted λ-rate with `B = C·4^A/(log y)^A`),
* the window mass `∑_{b ≤ √y} v_r(b)/b ≤ M`,
* the tail `∑_{√y < b ≤ y} v_r(b)/b ≤ ε`,

the damped twisted Liouville datum obeys `‖M_{λg_rχ̄}(y)‖ ≤ B·M·y + ε·y`.  On the tail row
only the crude `norm_MlambdaChi_le` is used — that row is where the transposition, like O6,
can fail, and `ε` is the honest name of the failure.  Nothing here depends on `r` beyond
`r ≤ 1` (positivity of `v_r`).  The λ-twin of `Salt.MR.norm_MmuGrChi_le_split`. -/
theorem norm_MlamGrChi_le_split {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ) (r : ℝ)
    (y : ℕ) (hr1 : r ≤ 1) {B M ε : ℝ} (hB : 0 ≤ B)
    (hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y), ‖MlambdaChi χ t (y / b)‖ ≤ B * (y : ℝ) / (b : ℝ))
    (hmass : ∑ b ∈ Finset.Icc 1 (Nat.sqrt y), lamTailWeight P Q r b / (b : ℝ) ≤ M)
    (htail : ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, lamTailWeight P Q r b / (b : ℝ) ≤ ε) :
    ‖MlamGrChi χ t P Q r y‖ ≤ B * M * (y : ℝ) + ε * (y : ℝ) := by
  have hwnn : ∀ n : ℕ, 0 ≤ lamTailWeight P Q r n := fun n => lamTailWeight_nonneg hr1 n
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hsqle : Nat.sqrt y ≤ y := Nat.sqrt_le_self y
  have hcoef : ∀ b : ℕ,
      ‖((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b‖ ≤ lamTailWeight P Q r b := by
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
  rw [MlamGrChi_eq_sum, hIcc, Finset.sum_union hdisj]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · -- SMALL: the λ-rate row, priced by the window mass `M`
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖(((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MlambdaChi χ t (y / b)‖
          ≤ (B * (y : ℝ)) * (lamTailWeight P Q r b / (b : ℝ)) := by
      intro b hb
      calc ‖(((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MlambdaChi χ t (y / b)‖
          = ‖((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b‖
              * ‖MlambdaChi χ t (y / b)‖ := norm_mul _ _
        _ ≤ lamTailWeight P Q r b * (B * (y : ℝ) / (b : ℝ)) :=
            mul_le_mul (hcoef b) (hsmall b hb) (norm_nonneg _) (hwnn b)
        _ = (B * (y : ℝ)) * (lamTailWeight P Q r b / (b : ℝ)) := by ring
    calc ∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
            ‖(((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MlambdaChi χ t (y / b)‖
        ≤ ∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
            (B * (y : ℝ)) * (lamTailWeight P Q r b / (b : ℝ)) := Finset.sum_le_sum hterm
      _ = (B * (y : ℝ))
            * ∑ b ∈ Finset.Icc 1 (Nat.sqrt y), lamTailWeight P Q r b / (b : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (B * (y : ℝ)) * M := mul_le_mul_of_nonneg_left hmass (mul_nonneg hB hy0)
      _ = B * M * (y : ℝ) := by ring
  · -- TAIL: only the crude bound is available — the honest cost `ε·y`
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ Finset.Ioc (Nat.sqrt y) y,
        ‖(((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MlambdaChi χ t (y / b)‖
          ≤ (y : ℝ) * (lamTailWeight P Q r b / (b : ℝ)) := by
      intro b _
      have hcrude : ‖MlambdaChi χ t (y / b)‖ ≤ (y : ℝ) / (b : ℝ) :=
        le_trans (norm_MlambdaChi_le χ t (y / b)) (Nat.cast_div_le (m := y) (n := b) (α := ℝ))
      calc ‖(((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MlambdaChi χ t (y / b)‖
          = ‖((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b‖
              * ‖MlambdaChi χ t (y / b)‖ := norm_mul _ _
        _ ≤ lamTailWeight P Q r b * ((y : ℝ) / (b : ℝ)) :=
            mul_le_mul (hcoef b) hcrude (norm_nonneg _) (hwnn b)
        _ = (y : ℝ) * (lamTailWeight P Q r b / (b : ℝ)) := by ring
    calc ∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
            ‖(((lamTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MlambdaChi χ t (y / b)‖
        ≤ ∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
            (y : ℝ) * (lamTailWeight P Q r b / (b : ℝ)) := Finset.sum_le_sum hterm
      _ = (y : ℝ)
            * ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, lamTailWeight P Q r b / (b : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (y : ℝ) * ε := mul_le_mul_of_nonneg_left htail hy0
      _ = ε * (y : ℝ) := by ring

/-- `log y → ∞` along ℕ, in eventual form (the λ-side twin of the private ones in
`LambdaRateTwisted` / `MobiusChiRamare`). -/
private lemma eventually_log_ge_lam (c : ℝ) : ∀ᶠ y : ℕ in Filter.atTop, c ≤ Real.log y := by
  have h : Filter.Tendsto (fun y : ℕ => Real.log (y : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- **THE DELIVERABLE — the damped twisted LIOUVILLE rate.**

From the twisted μ-rate slot `MmuChiRate` (⟦LANDED 2026-07-30⟧,
`PortClose.mmuChiRate_holds_gated`) through the landed fold `MlambdaChi_rate`, plus O6's OWN
two named window hypotheses, the RAMARÉ-DAMPED twisted Liouville datum inherits the rate at
every saving `A > 0`:

  `‖∑_{m ≤ y} λ(m)r^{ω(m;P,Q)}χ̄(m)m^{it}‖ ≤ C'·y/(log y)^A`,

uniformly over `q ≤ (log y)^10`, `|t| ≤ ⌊√⌊√y⌋⌋`, `P`, `Q`, and **`r ∈ [0,1]`**.

Gates and prices (the header's table, at the bytes):
* the CONDUCTOR gate moves from `MlambdaChi_rate`'s `q ≤ (log y)^11` to `q ≤ (log y)^10`:
  the λ-rate is invoked at `⌊y/b⌋` where only `log⌊y/b⌋ ≥ (log y)/4` is available, so one
  exponent is spent (`log y ≥ 4^11`, an eventual threshold absorbed into `x₀`);
* the HEIGHT gate transfers SHARPLY: `⌊√⌊√y⌋⌋ ≤ ⌊√⌊y/b⌋⌋` for `b ≤ √y` (`Nat.sqrt_le_sqrt`
  against `√y ≤ ⌊y/b⌋`), i.e. one further halving of the exponent — `y^{1/4}`, still
  enormous against the consumers' `seamT0 X = (log X)^{1/45}`;
* the log-scale price is `4^A` (`Salt.TwinBar.log_natSqrt_ge`);
* `M` is the window ℓ¹(1/n) mass and enters `C' = C·4^A·M + 1` LINEARLY; `M` is `P,Q`-genre
  (`≍ log Q/log P`) and carries no `y`;
* the mass and tail hypotheses are stated on O6's carrier `ramTailWeight`, NOT on
  `lamTailWeight` — legitimate and strictly weaker to assume, by
  `lamTailWeight_le_ramTailWeight`.  So D3's mass page and Rankin-tail page serve this
  deliverable and `MmuGrChi_rate` with the same bytes.

`C'` and `x₀` do **not** depend on `r`, `P`, `Q`, `q`, `χ` or `t` — that uniformity is what
§6's `∫₀¹ dr` composition consumes. -/
theorem MlamGrChi_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) →
            ∀ (P Q : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
              (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), ramTailWeight P Q r b / (b : ℝ)) ≤ M →
              (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q r b / (b : ℝ))
                  ≤ 1 / (Real.log y) ^ A →
              ‖MlamGrChi χ t P Q r y‖ ≤ C' * y / (Real.log y) ^ A := by
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
            ∀ (P Q : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
              (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), ramTailWeight P Q r b / (b : ℝ)) ≤ M →
              (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q r b / (b : ℝ))
                  ≤ 1 / (Real.log y) ^ A →
              ‖MlamGrChi χ t P Q r y‖
                ≤ (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
    filter_upwards [Filter.eventually_ge_atTop 16, Filter.eventually_ge_atTop (x₀lam ^ 2),
        eventually_log_ge_lam ((4 : ℝ) ^ (11 : ℕ))] with y hy16 hyx0 hlog4
    intro q _ χ hq t ht P Q r hr0 hr1 hmass htail
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
    -- the λ-rate on the small range, in the `B·y/b` shape
    have hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖MlambdaChi χ t (y / b)‖ ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * (y : ℝ) / (b : ℝ) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      obtain ⟨hb1, hbs⟩ := hb
      have hbpos : 0 < b := hb1
      -- `√y ≤ ⌊y/b⌋` (this is what transfers BOTH gates)
      have hts : Nat.sqrt y ≤ y / b := by
        rw [Nat.le_div_iff_mul_le hbpos]
        calc Nat.sqrt y * b ≤ Nat.sqrt y * Nat.sqrt y := by gcongr
          _ ≤ y := Nat.sqrt_le y
      have htx : x₀lam ≤ y / b := le_trans hs_ge_x0 hts
      have hlogt : Real.log y / 4 ≤ Real.log ((y / b : ℕ) : ℝ) := by
        refine le_trans hlogs ?_
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt y))
        exact_mod_cast hts
      -- THE CONDUCTOR GATE UPGRADE: `q ≤ (log y)^10 ≤ (log y/4)^11 ≤ (log⌊y/b⌋)^11`
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
      -- THE HEIGHT GATE TRANSFER: `|t| ≤ ⌊√⌊√y⌋⌋ ≤ ⌊√⌊y/b⌋⌋`
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
    -- O6's hypotheses dominate the λ-side ones (`v_r ≤ w_r`)
    have hmono : ∀ b : ℕ, lamTailWeight P Q r b / (b : ℝ) ≤ ramTailWeight P Q r b / (b : ℝ) := by
      intro b
      have h := lamTailWeight_le_ramTailWeight (P := P) (Q := Q) hr1 b
      gcongr
    have hsplit := norm_MlamGrChi_le_split χ t P Q r y hr1 hBnn hsmall
      (le_trans (Finset.sum_le_sum fun b _ => hmono b) hmass)
      (le_trans (Finset.sum_le_sum fun b _ => hmono b) htail)
    calc ‖MlamGrChi χ t P Q r y‖
        ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * M * (y : ℝ)
            + (1 / (Real.log y) ^ A) * (y : ℝ) := hsplit
      _ = (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
          field_simp
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨C * (4 : ℝ) ^ A * M + 1, N, hC'pos, hN⟩

/-! ## §6 — the `∫₀¹ dr` composition: the RAMARÉ-WEIGHTED Liouville datum -/

/-- **The Ramaré-WEIGHTED twisted Liouville summatory function**
`∑_{m ≤ y} λ(m)·(ω(m;P,Q)+1)^{−1}·χ̄(m)m^{it}` — the λ-twin of `Salt.MR.MmuRamChi`, and the
datum the door's co-factor polynomial carries at `pieceDatum`'s Liouville factor, read on the
`σ = 0` summatory side. -/
noncomputable def MlamRamChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ)
    (y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 y, ((ArithmeticFunction.liouville m : ℤ) : ℂ)
      * ((blockOmega P Q m : ℂ) + 1)⁻¹ * chiBarTwist χ t m

/-- **The weight as a `[0,1]` average of the dampings** — the LANDED `RamWeight` device
(`integral_cpow_unit`) applied to the twisted Liouville summatory function:
`M_{λ/(ω+1)χ̄}(y) = ∫₀¹ M_{λg_rχ̄}(y) dr`.  Finite sum against interval integral; every
summand is a polynomial in `r`. -/
theorem MlamRamChi_eq_integral {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q y : ℕ) :
    MlamRamChi χ t P Q y = ∫ r in (0:ℝ)..1, MlamGrChi χ t P Q r y := by
  have hMG : ∀ r : ℝ, MlamGrChi χ t P Q r y
      = ∑ m ∈ Finset.Icc 1 y,
          (((ArithmeticFunction.liouville m : ℤ) : ℂ) * chiBarTwist χ t m)
            * ((r : ℝ) : ℂ) ^ blockOmega P Q m := by
    intro r
    rw [MlamGrChi]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [lamGr_apply]
    push_cast
    ring
  simp only [hMG]
  rw [intervalIntegral.integral_finsetSum (fun m _ => (by fun_prop : Continuous
    (fun r : ℝ => (((ArithmeticFunction.liouville m : ℤ) : ℂ) * chiBarTwist χ t m)
      * ((r : ℝ) : ℂ) ^ blockOmega P Q m)).intervalIntegrable _ _)]
  rw [MlamRamChi]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cpow_unit]
  ring

/-- **THE EXIT SHAPE** (the λ-twin of `Salt.MR.norm_MmuRamChi_le_of_uniform`): a bound on the
damped twisted Liouville datum that is *uniform over `r ∈ [0,1]`* is a bound on the
Ramaré-WEIGHTED datum itself.  The unit interval has length `1`, so no constant is lost and
no integrability side condition reaches the consumer. -/
theorem norm_MlamRamChi_le_of_uniform {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q y : ℕ)
    {B : ℝ} (h : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖MlamGrChi χ t P Q r y‖ ≤ B) :
    ‖MlamRamChi χ t P Q y‖ ≤ B := by
  rw [MlamRamChi_eq_integral]
  have hbd : ∀ r ∈ Set.uIoc (0 : ℝ) 1, ‖MlamGrChi χ t P Q r y‖ ≤ B := by
    intro r hr
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    exact h r ⟨hr.1.le, hr.2⟩
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- **⟦D3 carrier page 1⟧ THE RAMARÉ-WEIGHTED λ-DELIVERABLE.**  The Ramaré-weighted twisted
Liouville datum `λ(m)/(ω(m;P,Q)+1)·χ̄(m)m^{it}` inherits the rate `C'·y/(log y)^A` from
`MmuChiRate` plus the two named window hypotheses **stated at `r = 0` only** — and those
hypotheses are `MmuRamChi_rate`'s, verbatim (same carrier `ramTailWeight P Q 0`, same
ranges).  One mass page and one Rankin-tail page discharge both deliverables.

Two things make this free once `MlamGrChi_rate` is in hand:
* `MlamGrChi_rate`'s `C'` and `x₀` are independent of `r` (`r` is quantified INSIDE);
* `ramTailWeight_le_zero_param` (LANDED): `w_r ≤ w_0 = 1_{[P,Q]-smooth}` for `r ∈ [0,1]`, so
  the `r = 0` hypotheses imply their `r`-general forms, uniformly.

Gates: `q ≤ (log y)^10` and `|t| ≤ ⌊√⌊√y⌋⌋` — two conductor exponents and two height
halvings below `MmuChiRate`, both free at the door (see the header's table). -/
theorem MlamRamChi_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) →
            ∀ P Q : ℕ,
              (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), ramTailWeight P Q 0 b / (b : ℝ)) ≤ M →
              (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q 0 b / (b : ℝ))
                  ≤ 1 / (Real.log y) ^ A →
              ‖MlamRamChi χ t P Q y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C', x₀, hC'pos, hbound⟩ := MlamGrChi_rate hMmu A hA hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro y hy q _ χ hq t ht P Q hmass0 htail0
  refine norm_MlamRamChi_le_of_uniform χ t P Q y ?_
  intro r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hmono : ∀ b : ℕ, ramTailWeight P Q r b / (b : ℝ) ≤ ramTailWeight P Q 0 b / (b : ℝ) := by
    intro b
    have h := ramTailWeight_le_zero_param (P := P) (Q := Q) hr0 hr1 b
    gcongr
  exact hbound y hy q χ hq t ht P Q r hr0 hr1
    (le_trans (Finset.sum_le_sum fun b _ => hmono b) hmass0)
    (le_trans (Finset.sum_le_sum fun b _ => hmono b) htail0)

end Salt.MR
