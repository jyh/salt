/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LambdaRateTwisted
import Salt.MR.RamWeight

/-!
# ⟦O6⟧ — THE `g_r` PERTURBATION (the KMT port, wave P-5, node D3)

Design: `docs/exploration/port-freeze-0729.md`, §"What the refuters changed" item 3
(the obligation register O1–O7), and the `⟦THE PORT REFUTER PASS + FREEZE v2⟧` entry of
`docs/blueprints/flags.md`.  This file discharges the port's obligation **O6**:

> transfer the `χ,t`-twisted Möbius rate from the PLAIN twisted datum
> `μ(m)·χ̄(m)m^{it}` to the RAMARÉ-DAMPED one `μ(m)·r^{ω(m;P,Q)}·χ̄(m)m^{it}`,
> uniformly in the damping parameter `r ∈ [0,1]`, and hence to the Ramaré-WEIGHTED
> datum `μ(m)/(ω(m;P,Q)+1)·χ̄(m)m^{it}`.

The freeze calls O6 "a genuine new convolution argument".  The argument is
`μ·g_r = μ ∗ w_r`, and this file proves it.

## The mathematics, in one screen

The damped datum is `g_r(m) = r^{ω(m;P,Q)}` with `ω(·;P,Q)` the corpus's window
prime-count `Salt.MR.blockOmega` (`Salt/MR/Decomp.lean:57`).  `μ·g_r` is multiplicative
with `(μ·g_r)(p) = −r` for `p` in the window `[P,Q]` and `−1` off it, and
`(μ·g_r)(p^k) = 0` for `k ≥ 2`, so its Dirichlet series factors as

  `D(μ·g_r)(s) = (1/ζ(s)) · ∏_{P≤p≤Q} (1 − r·p^{−s})/(1 − p^{−s})`,

i.e. `μ·g_r = μ ∗ w_r` where `w_r` is multiplicative with local factor
`(1 − r p^{−s})/(1 − p^{−s}) = 1 + (1−r)·∑_{k≥1} p^{−ks}`.  Reading off the `p^k`
coefficient — `(1−r)` for EVERY `k ≥ 1` — gives the closed form used here as the
DEFINITION (§2):

  `w_r(n) = (1−r)^{ω(n;P,Q)}` for `n ≥ 1` all of whose prime factors lie in `[P,Q]`,
  `w_r(n) = 0` otherwise.

(The equivalent "Möbius-transform" carrier `w_r(n) = ∑_{d ∣ n} μ(d)·r^{ω(d;P,Q)}` is the
same function: over squarefree `d ∣ n` the sum is `∏_{p ∣ n} (1 − r^{1_{window}(p)})`, which
is `(1−r)^{ω(n;P,Q)}` when every `p ∣ n` is in the window and has a vanishing factor `1−1`
otherwise.  §3 proves the identification in the form actually needed:
`w_r = ζ ∗ (μ·g_r)`, hence `μ ∗ w_r = (μ ∗ ζ) ∗ (μ·g_r) = μ·g_r`.)

Twisting: `chiBarTwist χ t` is completely multiplicative on nonzero arguments
(`Salt.MR.chiBarTwist_mul`), so the twist distributes over the convolution and the
hyperbola fold (§4) reads

  `∑_{m ≤ y} μ(m)g_r(m)χ̄(m)m^{it} = ∑_{b ≤ y} w_r(b)χ̄(b)b^{it} · M_{μχ̄}(⌊y/b⌋)`.

Splitting at `b ≤ √y` (§5): on the small range the twisted μ-rate applies at `⌊y/b⌋ ≥ √y`,
costing `4^A` of `log`-scale and one exponent of conductor range; on the tail only the crude
`‖M_{μχ̄}(z)‖ ≤ z` is available, so the tail costs `y·∑_{b>√y} w_r(b)/b`.

## THE ONE PLACE THE ARGUMENT CAN FAIL — and what is a hypothesis here

**The `b > √y` row is the heart of O6 and it is NOT discharged here.**  The honest device
is a Rankin/log-moment tail, `∑_{b>z} w_r(b)/b ≤ (log z)^{−A}·∑_b w_r(b)(log b)^A/b`, whose
right side is the window mass times an `((1−r)·log(Q/P))^A·A!`-genre factor — FINE when
`log Q ≪ (log y)^{1−δ}` and NOT fine when `log Q ≍ log y`.  Since the consumer, not this
file, knows the `P,Q` scales, **both the mass and the tail are EXPLICIT NAMED IN-STATEMENT
HYPOTHESES** here:

* `hmass : ∑_{b ≤ √y} w_r(b)/b ≤ M`   — the ℓ¹(1/n) window mass;
* `htail : ∑_{√y < b ≤ y} w_r(b)/b ≤ ε` (deliverable form: `ε = (log y)^{−A}`).

Everything else in this file is UNCONDITIONAL except the single slot `MmuChiRate`
(`Salt/MR/LambdaRateTwisted.lean`), the port's open centerpiece (obligations O4 + O5),
consumed as a hypothesis.

**Why the hypotheses stay inside the freeze's `log Q/log P` genre.**  §2's
`ramTailWeight_le_zero_param` shows `w_r` is ANTITONE in `r` on `[0,1]`, so
`w_r(n) ≤ w_0(n) = 1_{[P,Q]-smooth}(n)` and BOTH hypotheses may be discharged once, at
`r = 0`, uniformly in `r` — which is exactly what §6's `∫₀¹ dr` composition needs.  At
`r = 0` the mass is the window-smooth count
`∑_{n [P,Q]-smooth} 1/n = ∏_{P≤p≤Q}(1 − 1/p)^{−1}`, whose logarithm is the landed Mertens
window sum `Salt.MR.blockWindow_mertens_const` (`Salt/MR/CofactorDist.lean:139`):
`∑_{P≤p≤Q} 1/p ≤ loglog Q − loglog P + 25`.  So the mass is `exp(loglog Q − loglog P + O(1))`
`≍ log Q/log P` — the freeze's O6 shape.  **That Euler-product evaluation is NOT performed
here** (it needs `∑ 1/(p−1)` and the product expansion, and `CofactorDist` sits outside this
file's import cone); it is named as the consumer's route and the mass is carried abstractly.
`r = 0` is also the WORST case, so nothing is lost by the reduction.

## The traps crossed (house rule: name them)

* **⟦the barred-χ convention⟧** `chiBarTwist χ t n = χ̄(n)·exp((t·log n)i)` — the CORPUS
  orientation (conjugate on the datum, unconjugated character on the coefficient; see
  `Salt/MR/LambdaRateTwisted.lean`'s header and `Salt/MR/M4Chars.lean:29–60`).  KMT print the
  twist unbarred with `n^{−it}`; every statement below is `∀ t : ℝ`, so the sign is immaterial
  and the bar is inherited, not chosen.
* **⟦the damping letter⟧** `RamWeight` calls the damping parameter `x` (`gxDatum g P Q x`,
  `ramRdamp … x t`); the freeze and this file call it `r` to keep `x` for scales.  Same
  object: `r^{ω(m;P,Q)}` here is `RamWeight`'s `x ^ blockOmega P Q m`.
* **⟦σ = 1 vs σ = 0⟧** NOT crossed.  This file never touches `spoly`/`dpolyChi`/`ramR`: its
  sums are *summatory functions* (`∑_{m ≤ y}`, no `m^{-s}`), i.e. the `σ = 0` side.  The
  bridge to the `σ = 1` Dirichlet-polynomial side is `RamWeight`'s `ramRdamp`, and it is a
  consumer's Abel step, not this file's.
* **⟦the four log scales⟧** `log y` (the statement's scale), `log⌊y/b⌋` (where the μ-rate is
  actually invoked — the `4^A` and the one conductor exponent are paid here),
  `log √y = (log y)/2` (bounded below by `(log y)/4` through the landed
  `Salt.TwinBar.log_natSqrt_ge`, which absorbs the floor), and `log Q/log P` (the WINDOW
  scale, the only place `P,Q` enter — it appears solely inside the named hypotheses `M, ε`).
* **⟦ℝ-valued carriers, ℂ-valued sums⟧** `muGr` and `ramTailWeight` are
  `ArithmeticFunction ℝ` (so that positivity of `w_r` is a first-class fact); the twisted
  summatory functions are ℂ-valued with `‖·‖` in the rate, matching
  `Salt/MR/LambdaRateTwisted.lean`.  Because of the ring mismatch the ℂ-side twist step is
  taken directly from `chiBarTwist_mul` (which is the entire analytic content of
  `mul_apply_mul_twist`) rather than by instantiating `mul_apply_mul_twist`, whose `f g h`
  all live in ONE ring; duplicating ℂ-valued carriers to force the citation would have cost
  two more definitions for no content.  See `muGr_twist_eq_sum_divisorsAntidiagonal`.

## Contents

* **§1** `muGr` — the damped Möbius datum `μ·g_r` as an `ArithmeticFunction ℝ`, and its
  multiplicativity (from `isMultiplicative_moebius` + the LANDED `blockOmega_mul_coprime`).
* **§2** `WindowSmooth`, `ramTailWeight` (`= w_r`, the closed-form carrier), its
  multiplicativity, positivity, support, the `r = 0` indicator form and the antitonicity in
  `r`.
* **§3** `ramTailWeight_prime_pow` (the local factor's coefficients, read off the closed form)
  and `ramTailWeight_eq_zeta_mul_muGr` (THE VERIFICATION: equality of two multiplicative
  functions checked at prime powers), with the alternative carrier
  `ramTailWeight_eq_sum_divisors` as a corollary; then the convolution identity
  `mu_mul_ramTailWeight` / `muGr_eq_sum_divisorsAntidiagonal`.
* **§4** `MmuGrChi` and the twisted hyperbola fold `MmuGrChi_eq_sum` (UNCONDITIONAL).
* **§5** `norm_MmuGrChi_le_split` (the unconditional two-row split) and THE DELIVERABLE
  `MmuGrChi_rate` (from `MmuChiRate` + `M` + the tail hypothesis).
* **§6** `MmuRamChi`, `MmuRamChi_eq_integral` (the `∫₀¹ dr` composition through the LANDED
  `Salt.MR.integral_cpow_unit`), `norm_MmuRamChi_le_of_uniform` (the LANDED
  `ramR_norm_le_of_damp_le` pattern) and the Ramaré-WEIGHTED deliverable `MmuRamChi_rate`.
  **Every constant here is independent of `r`** — that independence is what makes §6 free.

Explicit constants throughout; no `O(·)` in any statement.
-/

open scoped BigOperators

namespace Salt.MR

/-! ## §1 — the damped Möbius datum `μ·g_r` -/

private lemma blockOmega_one_eq_zero (P Q : ℕ) : blockOmega P Q 1 = 0 := by
  simp [blockOmega, BlockPrimeDivs]

/-- **The damped Möbius datum** `(μ·g_r)(m) = μ(m)·r^{ω(m;P,Q)}` as an
`ArithmeticFunction ℝ`.  `ω(·;P,Q)` is the corpus's window prime count
`Salt.MR.blockOmega`; `RamWeight` writes the damping parameter `x`, the freeze and this file
write `r`.  Unconditional: at `m = 0` the value is `0` because `μ 0 = 0`. -/
noncomputable def muGr (P Q : ℕ) (r : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun m => ((ArithmeticFunction.moebius m : ℤ) : ℝ) * r ^ blockOmega P Q m, by simp⟩

@[simp] lemma muGr_apply (P Q : ℕ) (r : ℝ) (m : ℕ) :
    muGr P Q r m = ((ArithmeticFunction.moebius m : ℤ) : ℝ) * r ^ blockOmega P Q m := rfl

/-- **`μ·g_r` is multiplicative.**  `μ` is (`ArithmeticFunction.isMultiplicative_moebius`) and
`ω(·;P,Q)` is additive on coprimes — the LANDED `Salt.MR.blockOmega_mul_coprime`
(`Salt/MR/RamWeight.lean`), which is exactly the fact the Ramaré weight `1/(ω+1)` lacks and
the monomial `r^ω` supplies. -/
theorem muGr_isMultiplicative (P Q : ℕ) (r : ℝ) : (muGr P Q r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [blockOmega_one_eq_zero], ?_⟩
  intro m n _ _ hmn
  simp only [muGr_apply]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
    blockOmega_mul_coprime hmn, pow_add]
  push_cast
  ring

/-! ## §2 — the tail weight `w_r` -/

/-- **`[P,Q]`-window smoothness**: every prime factor of `n` lies in the window `[P,Q]`.
Vacuously true at `n = 0` and `n = 1` (`Nat.primeFactors 0 = Nat.primeFactors 1 = ∅`), which
is why `ramTailWeight` carries an explicit `n ≠ 0` guard. -/
def WindowSmooth (P Q n : ℕ) : Prop := ∀ p ∈ n.primeFactors, P ≤ p ∧ p ≤ Q

instance decidableWindowSmooth (P Q n : ℕ) : Decidable (WindowSmooth P Q n) := by
  unfold WindowSmooth; infer_instance

/-- **THE TAIL WEIGHT `w_r`** — the multiplicative function with local factor
`(1 − r p^{−s})/(1 − p^{−s}) = 1 + (1−r)∑_{k≥1}p^{−ks}` at window primes `p ∈ [P,Q]` and
local factor `1` off the window, carried by its CLOSED FORM:

  `w_r(n) = (1−r)^{ω(n;P,Q)}` if `n ≠ 0` and every prime factor of `n` is in `[P,Q]`,
  `w_r(n) = 0` otherwise.

The closed form is *verified* against the Euler factor in §3
(`ramTailWeight_eq_zeta_mul_muGr`): the `p^k` coefficient of the local factor is `(1−r)` for
every `k ≥ 1`, so on `n = ∏ p_i^{k_i}` the coefficient is `(1−r)^{#distinct primes}`, and on
the support `#distinct primes = ω(n;P,Q)`.  Choosing the closed form as the DEFINITION (and
not an Euler product) is what keeps this file short and makes positivity, support and
antitonicity in `r` one-liners. -/
noncomputable def ramTailWeight (P Q : ℕ) (r : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ WindowSmooth P Q n then (1 - r) ^ blockOmega P Q n else 0, by simp⟩

@[simp] lemma ramTailWeight_apply (P Q : ℕ) (r : ℝ) (n : ℕ) :
    ramTailWeight P Q r n
      = if n ≠ 0 ∧ WindowSmooth P Q n then (1 - r) ^ blockOmega P Q n else 0 := rfl

lemma ramTailWeight_apply_of {P Q : ℕ} (r : ℝ) {n : ℕ} (hn : n ≠ 0) (hs : WindowSmooth P Q n) :
    ramTailWeight P Q r n = (1 - r) ^ blockOmega P Q n := by
  simp [hn, hs]

lemma ramTailWeight_eq_zero_of_not_smooth {P Q : ℕ} (r : ℝ) {n : ℕ}
    (hs : ¬ WindowSmooth P Q n) : ramTailWeight P Q r n = 0 := by
  simp [hs]

lemma windowSmooth_one (P Q : ℕ) : WindowSmooth P Q 1 := by
  intro p hp; simp at hp

/-- **KEY POSITIVITY.**  For `r ≤ 1` every value of `w_r` is `≥ 0`.  This is the fact that
lets the ℓ¹(1/n) mass hypotheses of §5 be stated on `w_r` itself rather than on `|w_r|`, and
it is where `r ∈ [0,1]` (rather than an arbitrary complex damping) earns its keep. -/
theorem ramTailWeight_nonneg {P Q : ℕ} {r : ℝ} (hr1 : r ≤ 1) (n : ℕ) :
    0 ≤ ramTailWeight P Q r n := by
  rw [ramTailWeight_apply]
  split_ifs with h
  · exact pow_nonneg (by linarith) _
  · exact le_refl 0

/-- **THE SUPPORT.**  `w_r` vanishes off the `[P,Q]`-window-smooth numbers — the fact that
makes the `∑_b w_r(b)/b` mass of §5 a *window* quantity (genre `log Q/log P`) rather than a
`log y` quantity. -/
theorem ramTailWeight_support {P Q : ℕ} {r : ℝ} {n : ℕ} (h : ramTailWeight P Q r n ≠ 0) :
    n ≠ 0 ∧ WindowSmooth P Q n := by
  by_contra hc
  rw [ramTailWeight_apply, if_neg hc] at h
  exact h rfl

/-- **The `r = 0` value is the window-smooth INDICATOR.**  `w_0 = 1_{[P,Q]-smooth}`; by
`ramTailWeight_le_zero_param` it dominates every `w_r`, `r ∈ [0,1]`, so all the mass/tail
hypotheses of §5–§6 can be discharged once, at `r = 0`, uniformly in `r`. -/
theorem ramTailWeight_zero_param (P Q : ℕ) (n : ℕ) :
    ramTailWeight P Q 0 n = if n ≠ 0 ∧ WindowSmooth P Q n then 1 else 0 := by
  rw [ramTailWeight_apply]
  split_ifs with h
  · norm_num
  · rfl

/-- **ANTITONICITY IN THE DAMPING.**  For `r ∈ [0,1]`, `w_r ≤ w_0 = 1_{[P,Q]-smooth}`
pointwise.  This is the uniformity that makes §6's `∫₀¹ dr` composition free: an `r`-free
mass/tail hypothesis at `r = 0` implies the hypothesis at every `r ∈ [0,1]`, and no constant
below depends on `r`. -/
theorem ramTailWeight_le_zero_param {P Q : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    ramTailWeight P Q r n ≤ ramTailWeight P Q 0 n := by
  rw [ramTailWeight_apply, ramTailWeight_apply]
  split_ifs with h
  · have h1 : (1 - r) ^ blockOmega P Q n ≤ (1 : ℝ) :=
      pow_le_one₀ (by linarith) (by linarith)
    simpa using h1
  · exact le_refl 0

/-- **`w_r` is multiplicative.**  `[P,Q]`-smoothness is multiplicative
(`Nat.primeFactors_mul` splits the prime factors of a product of nonzero numbers) and
`ω(·;P,Q)` is additive on coprimes (the LANDED `blockOmega_mul_coprime`); off the smooth
support both sides vanish. -/
theorem ramTailWeight_isMultiplicative (P Q : ℕ) (r : ℝ) :
    (ramTailWeight P Q r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [ramTailWeight_apply_of r one_ne_zero (windowSmooth_one P Q), blockOmega_one_eq_zero,
      pow_zero]
  · intro m n hm hn hmn
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
    have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
      Nat.primeFactors_mul hm hn
    by_cases hsm : WindowSmooth P Q m
    · by_cases hsn : WindowSmooth P Q n
      · have hsmn : WindowSmooth P Q (m * n) := by
          intro p hp
          rw [hpf, Finset.mem_union] at hp
          rcases hp with h | h
          · exact hsm p h
          · exact hsn p h
        rw [ramTailWeight_apply_of r hmn0 hsmn, ramTailWeight_apply_of r hm hsm,
          ramTailWeight_apply_of r hn hsn, blockOmega_mul_coprime hmn, pow_add]
      · have hnot : ¬ WindowSmooth P Q (m * n) := fun hc =>
          hsn (fun p hp => hc p (by rw [hpf]; exact Finset.mem_union_right _ hp))
        rw [ramTailWeight_eq_zero_of_not_smooth r hnot,
          ramTailWeight_eq_zero_of_not_smooth r hsn, mul_zero]
    · have hnot : ¬ WindowSmooth P Q (m * n) := fun hc =>
        hsm (fun p hp => hc p (by rw [hpf]; exact Finset.mem_union_left _ hp))
      rw [ramTailWeight_eq_zero_of_not_smooth r hnot,
        ramTailWeight_eq_zero_of_not_smooth r hsm, zero_mul]

/-! ## §3 — THE CONVOLUTION IDENTITY `μ·g_r = μ ∗ w_r` -/

private lemma blockOmega_prime_pow {P Q p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    blockOmega P Q (p ^ k) = if P ≤ p ∧ p ≤ Q then 1 else 0 := by
  unfold blockOmega BlockPrimeDivs
  rw [Nat.primeFactors_prime_pow hk hp, Finset.filter_singleton]
  by_cases h : P ≤ p ∧ p ≤ Q
  · rw [if_pos h, if_pos h, Finset.card_singleton]
  · rw [if_neg h, if_neg h, Finset.card_empty]

private lemma windowSmooth_prime_pow_iff {P Q p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    WindowSmooth P Q (p ^ k) ↔ (P ≤ p ∧ p ≤ Q) := by
  unfold WindowSmooth
  rw [Nat.primeFactors_prime_pow hk hp]
  simp

/-- **THE CLOSED FORM'S PRIME-POWER VALUES — the auditable half of the verification.**
For `k ≥ 1`,

  `w_r(p^k) = 1 − r` if `P ≤ p ≤ Q`,   `w_r(p^k) = 0` otherwise,

i.e. the `p^k`-coefficient is `(1−r)` for EVERY `k ≥ 1` at a window prime and `0` off the
window — exactly the coefficients of the local factor
`(1 − r p^{−s})/(1 − p^{−s}) = 1 + (1−r)·∑_{k≥1} p^{−ks}` (window) and `1` (off window).
Read directly off the definition; `ramTailWeight_eq_zeta_mul_muGr` then matches these against
`ζ ∗ (μ·g_r)`, which is the other half. -/
theorem ramTailWeight_prime_pow {P Q p k : ℕ} (r : ℝ) (hp : p.Prime) (hk : k ≠ 0) :
    ramTailWeight P Q r (p ^ k) = if P ≤ p ∧ p ≤ Q then 1 - r else 0 := by
  by_cases hwin : P ≤ p ∧ p ≤ Q
  · rw [ramTailWeight_apply_of r (pow_ne_zero _ hp.ne_zero)
      ((windowSmooth_prime_pow_iff hp hk).mpr hwin), blockOmega_prime_pow hp hk,
      if_pos hwin, pow_one, if_pos hwin]
  · rw [ramTailWeight_eq_zero_of_not_smooth r
      (fun hc => hwin ((windowSmooth_prime_pow_iff hp hk).mp hc)), if_neg hwin]

/-- **THE VERIFICATION OF THE CLOSED FORM** (the one genuinely new arithmetic page of O6):

  `w_r = ζ ∗ (μ·g_r)`.

Both sides are multiplicative, so by `IsMultiplicative.eq_iff_eq_on_prime_powers` it suffices
to check prime powers.  At `p^k`, `k ≥ 1`,

  `(ζ ∗ (μ·g_r))(p^k) = ∑_{j=0}^{k} μ(p^j)r^{ω(p^j;P,Q)} = 1 − r^{1_{[P,Q]}(p)}`

(the `j ≥ 2` terms vanish because `μ(p^j) = 0`), which is `1 − r` for `p` in the window and
`1 − 1 = 0` off it — exactly the closed form's `(1−r)^1` on the smooth support and `0` off
it.  This is the reading-off of the local factor `1 + (1−r)∑_{k≥1}p^{−ks}` announced in the
header. -/
theorem ramTailWeight_eq_zeta_mul_muGr (P Q : ℕ) (r : ℝ) :
    ramTailWeight P Q r
      = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
          * muGr P Q r := by
  have hmulti :
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
        * muGr P Q r).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul (muGr_isMultiplicative P Q r)
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (ramTailWeight_isMultiplicative P Q r) _ hmulti]
  intro p k hp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, (ramTailWeight_isMultiplicative P Q r).map_one, hmulti.map_one]
  have hk0 : k ≠ 0 := by omega
  -- the right side: sum over the divisors of `p^k`, trimmed to `j ∈ {0,1}`
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  have hsub : Finset.range 2 ⊆ Finset.range (k + 1) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have hzero : ∀ i ∈ Finset.range (k + 1), i ∉ Finset.range 2 → muGr P Q r (p ^ i) = 0 := by
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [muGr_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [← Finset.sum_subset hsub hzero, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
    pow_one, muGr_apply, muGr_apply, blockOmega_one_eq_zero,
    ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one]
  have hbo : blockOmega P Q p = if P ≤ p ∧ p ≤ Q then 1 else 0 := by
    have := blockOmega_prime_pow (P := P) (Q := Q) (p := p) (k := 1) hp one_ne_zero
    rwa [pow_one] at this
  rw [ramTailWeight_prime_pow r hp hk0, hbo]
  by_cases hwin : P ≤ p ∧ p ≤ Q
  · rw [if_pos hwin, if_pos hwin]
    push_cast
    ring
  · rw [if_neg hwin, if_neg hwin]
    push_cast
    ring

/-- **THE MÖBIUS-TRANSFORM CARRIER, identified with the closed form**:

  `w_r(n) = ∑_{d ∣ n} μ(d)·r^{ω(d;P,Q)}`.

The alternative carrier mentioned in the header, now a corollary of the verification: over
squarefree `d ∣ n` the right side is `∏_{p ∣ n}(1 − r^{1_{[P,Q]}(p)})`, which is
`(1−r)^{ω(n;P,Q)}` on the window-smooth support and carries a vanishing factor `1 − 1` off it.
Recorded so a consumer may use whichever form is cheaper at the point of use. -/
theorem ramTailWeight_eq_sum_divisors (P Q : ℕ) (r : ℝ) (n : ℕ) :
    ramTailWeight P Q r n
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * r ^ blockOmega P Q d := by
  rw [ramTailWeight_eq_zeta_mul_muGr, ArithmeticFunction.coe_zeta_mul_apply]
  exact Finset.sum_congr rfl fun d _ => muGr_apply P Q r d

/-- **⟦O6⟧ THE CONVOLUTION IDENTITY, `ArithmeticFunction`-level**: `μ ∗ w_r = μ·g_r`.

Immediate from `ramTailWeight_eq_zeta_mul_muGr` and mathlib's `μ ∗ ζ = 1`
(`ArithmeticFunction.coe_moebius_mul_coe_zeta`), by associativity.  This is the freeze's
"`μ·g_r = μ ∗ w_r`, a genuine new convolution argument"; UNCONDITIONAL. -/
theorem mu_mul_ramTailWeight (P Q : ℕ) (r : ℝ) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * ramTailWeight P Q r = muGr P Q r := by
  rw [ramTailWeight_eq_zeta_mul_muGr, ← mul_assoc,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]

/-- **⟦O6⟧ THE CONVOLUTION IDENTITY, pointwise** (the form the fold consumes): for every `m`,

  `μ(m)·r^{ω(m;P,Q)} = ∑_{ab = m} μ(a)·w_r(b)`.

Holds at `m = 0` too (both sides `0`: `μ 0 = 0` and `Nat.divisorsAntidiagonal 0 = ∅`). -/
theorem muGr_eq_sum_divisorsAntidiagonal (P Q : ℕ) (r : ℝ) (m : ℕ) :
    ((ArithmeticFunction.moebius m : ℤ) : ℝ) * r ^ blockOmega P Q m
      = ∑ ab ∈ m.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius ab.1 : ℤ) : ℝ) * ramTailWeight P Q r ab.2 := by
  rw [← muGr_apply, ← mu_mul_ramTailWeight, ArithmeticFunction.mul_apply]
  exact Finset.sum_congr rfl fun ab _ => by rw [ArithmeticFunction.intCoe_apply]

/-! ## §4 — the twisted damped summatory function and the hyperbola fold -/

/-- **The twisted damped Möbius summatory function**
`M_{μg_rχ̄}(y) = ∑_{m ≤ y} μ(m)r^{ω(m;P,Q)}χ̄(m)m^{it}`, ℂ-valued.  ⟦barred χ⟧ the twist is
the corpus's `chiBarTwist` (conjugate on the datum). -/
noncomputable def MmuGrChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ) (r : ℝ)
    (y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 y, ((muGr P Q r m : ℝ) : ℂ) * chiBarTwist χ t m

/-- **The twist distributes over `μ·g_r = μ ∗ w_r`** (for `m ≠ 0`).  The ℂ-side of §3's
pointwise identity: `chiBarTwist` is completely multiplicative on nonzero arguments
(`chiBarTwist_mul`), which is the entire analytic content of
`LambdaRateTwisted.mul_apply_mul_twist`; that lemma is not instantiated here only because its
`f g h` live in ONE ring while our carriers are ℝ-valued and the twist is ℂ-valued. -/
theorem muGr_twist_eq_sum_divisorsAntidiagonal {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (P Q : ℕ) (r : ℝ) {m : ℕ} (hm : m ≠ 0) :
    ((muGr P Q r m : ℝ) : ℂ) * chiBarTwist χ t m
      = ∑ ab ∈ m.divisorsAntidiagonal,
          (((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ) * chiBarTwist χ t ab.1)
            * (((ramTailWeight P Q r ab.2 : ℝ) : ℂ) * chiBarTwist χ t ab.2) := by
  have hR := muGr_eq_sum_divisorsAntidiagonal P Q r m
  have hC : ((muGr P Q r m : ℝ) : ℂ)
      = ∑ ab ∈ m.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ)
            * ((ramTailWeight P Q r ab.2 : ℝ) : ℂ) := by
    rw [muGr_apply, hR]
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

/-- **The inner multiples bijection at a general divisor `b`** (the twisted
`Salt.MR.MmuChi_inner` with `d^2` replaced by `b`):
`∑_{m ≤ y, b ∣ m} μ(m/b)χ̄(m/b)(m/b)^{it} = M_{μχ̄}(⌊y/b⌋)`, by `m = b·a`. -/
theorem MmuChi_inner_dvd {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (y b : ℕ) (hb : 1 ≤ b) :
    ∑ m ∈ (Finset.Icc 1 y).filter (fun m => b ∣ m),
        (((ArithmeticFunction.moebius (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
      = MmuChi χ t (y / b) := by
  have hb0 : 0 < b := hb
  unfold MmuChi
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

/-- **⟦O6⟧ THE TWISTED HYPERBOLA FOLD (UNCONDITIONAL)**:

  `∑_{m ≤ y} μ(m)g_r(m)χ̄(m)m^{it} = ∑_{b ≤ y} w_r(b)χ̄(b)b^{it} · M_{μχ̄}(⌊y/b⌋)`.

The same fold as `Salt.MR.MlambdaChi_eq_sum_MmuChi`, at `w_r` instead of `1_sq` — so the
`d`-shaped square reindex of that proof is replaced by the general divisor reindex
`Nat.sum_divisorsAntidiagonal'` plus `MmuChi_inner_dvd`.  No hypothesis on `r`, `P`, `Q`. -/
theorem MmuGrChi_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ) (r : ℝ)
    (y : ℕ) :
    MmuGrChi χ t P Q r y
      = ∑ b ∈ Finset.Icc 1 y,
          (((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b) := by
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
  -- STEP A: the pointwise identity, reindexed by the `w_r`-argument `b`
  have hpt : ∀ m ∈ Finset.Icc 1 y,
      ((muGr P Q r m : ℝ) : ℂ) * chiBarTwist χ t m
        = ∑ b ∈ Finset.Icc 1 y,
            (if b ∣ m then
              (((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b)
                * (((ArithmeticFunction.moebius (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
             else 0) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    rw [muGr_twist_eq_sum_divisorsAntidiagonal χ t P Q r hm0]
    rw [Nat.sum_divisorsAntidiagonal' (n := m)
      (f := fun a b => (((ArithmeticFunction.moebius a : ℤ) : ℂ) * chiBarTwist χ t a)
        * (((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b))]
    rw [← hdivfilter m hm.1 hm.2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · ring
    · rfl
  -- STEP B: swap the sums, pull out the `b`-factor, collapse the inner sum
  rw [MmuGrChi, Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  have hpull : ∀ m : ℕ,
      (if b ∣ m then
        (((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b)
          * (((ArithmeticFunction.moebius (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
       else 0)
      = (((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b)
          * (if b ∣ m then
              (((ArithmeticFunction.moebius (m / b) : ℤ) : ℂ) * chiBarTwist χ t (m / b))
             else 0) := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => hpull m), ← Finset.mul_sum, ← Finset.sum_filter,
    MmuChi_inner_dvd χ t y b hb.1]

/-! ## §5 — the rate transfer -/

/-- **THE TWO-ROW SPLIT (UNCONDITIONAL).**  Given
* a per-`b` bound `‖M_{μχ̄}(⌊y/b⌋)‖ ≤ B·y/b` on the SMALL range `b ≤ √y` (in the deliverable
  this is the twisted μ-rate with `B = C·4^A/(log y)^A`),
* the window mass `∑_{b ≤ √y} w_r(b)/b ≤ M`,
* the tail `∑_{√y < b ≤ y} w_r(b)/b ≤ ε`,

the damped twisted datum obeys `‖M_{μg_rχ̄}(y)‖ ≤ B·M·y + ε·y`.  On the tail row only the
crude `norm_MmuChi_le` is used — **that row is where O6 can fail, and `ε` is the honest
name of the failure**; see the file header.  Nothing here depends on `r` beyond `r ≤ 1`
(positivity of `w_r`). -/
theorem norm_MmuGrChi_le_split {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ) (r : ℝ)
    (y : ℕ) (hr1 : r ≤ 1) {B M ε : ℝ} (hB : 0 ≤ B)
    (hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y), ‖MmuChi χ t (y / b)‖ ≤ B * (y : ℝ) / (b : ℝ))
    (hmass : ∑ b ∈ Finset.Icc 1 (Nat.sqrt y), ramTailWeight P Q r b / (b : ℝ) ≤ M)
    (htail : ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q r b / (b : ℝ) ≤ ε) :
    ‖MmuGrChi χ t P Q r y‖ ≤ B * M * (y : ℝ) + ε * (y : ℝ) := by
  have hwnn : ∀ n : ℕ, 0 ≤ ramTailWeight P Q r n := fun n => ramTailWeight_nonneg hr1 n
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hsqle : Nat.sqrt y ≤ y := Nat.sqrt_le_self y
  -- the per-`b` coefficient is `1`-bounded against `w_r(b)`
  have hcoef : ∀ b : ℕ,
      ‖((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b‖ ≤ ramTailWeight P Q r b := by
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
  rw [MmuGrChi_eq_sum, hIcc, Finset.sum_union hdisj]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · -- SMALL: the μ-rate row, priced by the window mass `M`
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖(((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
          ≤ (B * (y : ℝ)) * (ramTailWeight P Q r b / (b : ℝ)) := by
      intro b hb
      calc ‖(((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
          = ‖((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b‖
              * ‖MmuChi χ t (y / b)‖ := norm_mul _ _
        _ ≤ ramTailWeight P Q r b * (B * (y : ℝ) / (b : ℝ)) :=
            mul_le_mul (hcoef b) (hsmall b hb) (norm_nonneg _) (hwnn b)
        _ = (B * (y : ℝ)) * (ramTailWeight P Q r b / (b : ℝ)) := by ring
    calc ∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
            ‖(((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
        ≤ ∑ b ∈ Finset.Icc 1 (Nat.sqrt y),
            (B * (y : ℝ)) * (ramTailWeight P Q r b / (b : ℝ)) := Finset.sum_le_sum hterm
      _ = (B * (y : ℝ))
            * ∑ b ∈ Finset.Icc 1 (Nat.sqrt y), ramTailWeight P Q r b / (b : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (B * (y : ℝ)) * M := mul_le_mul_of_nonneg_left hmass (mul_nonneg hB hy0)
      _ = B * M * (y : ℝ) := by ring
  · -- TAIL: only the crude bound is available — the honest cost `ε·y`
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ Finset.Ioc (Nat.sqrt y) y,
        ‖(((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
          ≤ (y : ℝ) * (ramTailWeight P Q r b / (b : ℝ)) := by
      intro b _
      have hcrude : ‖MmuChi χ t (y / b)‖ ≤ (y : ℝ) / (b : ℝ) :=
        le_trans (norm_MmuChi_le χ t (y / b)) (Nat.cast_div_le (m := y) (n := b) (α := ℝ))
      calc ‖(((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
          = ‖((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b‖
              * ‖MmuChi χ t (y / b)‖ := norm_mul _ _
        _ ≤ ramTailWeight P Q r b * ((y : ℝ) / (b : ℝ)) :=
            mul_le_mul (hcoef b) hcrude (norm_nonneg _) (hwnn b)
        _ = (y : ℝ) * (ramTailWeight P Q r b / (b : ℝ)) := by ring
    calc ∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
            ‖(((ramTailWeight P Q r b : ℝ) : ℂ) * chiBarTwist χ t b) * MmuChi χ t (y / b)‖
        ≤ ∑ b ∈ Finset.Ioc (Nat.sqrt y) y,
            (y : ℝ) * (ramTailWeight P Q r b / (b : ℝ)) := Finset.sum_le_sum hterm
      _ = (y : ℝ)
            * ∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q r b / (b : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (y : ℝ) * ε := mul_le_mul_of_nonneg_left htail hy0
      _ = ε * (y : ℝ) := by ring

/-- `log y → ∞` along ℕ, in eventual form (the twin of `LambdaRateTwisted`'s private one). -/
private lemma eventually_log_ge' (c : ℝ) : ∀ᶠ y : ℕ in Filter.atTop, c ≤ Real.log y := by
  have h : Filter.Tendsto (fun y : ℕ => Real.log (y : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop c

/-- **⟦O6⟧ THE DELIVERABLE — the damped twisted Möbius rate.**

From the twisted μ-rate slot `MmuChiRate` (**NOT LANDED** — it is the port's obligations O4 +
O5, see its docstring in `Salt/MR/LambdaRateTwisted.lean`) plus the two NAMED window
hypotheses, the RAMARÉ-DAMPED twisted datum inherits the rate at every saving `A > 0`:

  `‖∑_{m ≤ y} μ(m)r^{ω(m;P,Q)}χ̄(m)m^{it}‖ ≤ C'·y/(log y)^A`,

uniformly over `q ≤ (log y)^11`, `|t| ≤ ⌊√y⌋`, `P`, `Q`, and **`r ∈ [0,1]`**.

Gates and prices, spelled out:
* the CONDUCTOR gate moves from `MmuChiRate`'s `q ≤ (log y)^12` to `q ≤ (log y)^11`: the
  μ-rate is invoked at `⌊y/b⌋` where only `log⌊y/b⌋ ≥ (log y)/4` is available, so one of the
  twelve exponents is spent (`log y ≥ 4^12`, an eventual threshold in `x₀`) — the same 15-line
  pattern as `MlambdaChi_rate`;
* the HEIGHT gate transfers SHARPLY: `|t| ≤ ⌊√y⌋ ≤ ⌊y/b⌋` for `b ≤ √y` (`Nat.le_div_iff_mul_le`
  against `Nat.sqrt_le`), so half of `MmuChiRate`'s `|t| ≤ y` range is spent — exactly as in
  `MlambdaChi_rate`;
* the log-scale price is `4^A`, from `Salt.TwinBar.log_natSqrt_ge`;
* `M` is the window ℓ¹(1/n) mass and enters `C' = C·4^A·M + 1` LINEARLY; `M` is `P,Q`-genre
  (`≍ log Q/log P`, see the header) and carries no `y`;
* the tail hypothesis is the honest residue of O6: it demands `∑_{√y<b≤y} w_r(b)/b ≤
  (log y)^{−A}`, which a consumer discharges by Rankin at its own `P,Q` scales.  It is stated,
  not proved, here.

`C'` and `x₀` do **not** depend on `r`, `P`, `Q`, `q`, `χ` or `t` — that uniformity is what
§6's `∫₀¹ dr` composition consumes. -/
theorem MmuGrChi_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ, |t| ≤ (Nat.sqrt y : ℝ) →
          ∀ (P Q : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
            (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), ramTailWeight P Q r b / (b : ℝ)) ≤ M →
            (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q r b / (b : ℝ))
                ≤ 1 / (Real.log y) ^ A →
            ‖MmuGrChi χ t P Q r y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C, x₀mu, hCpos, hMmuBound⟩ := hMmu A hA
  have h4A : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hC'pos : (0 : ℝ) < C * (4 : ℝ) ^ A * M + 1 := by
    have h : (0 : ℝ) ≤ C * (4 : ℝ) ^ A * M :=
      mul_nonneg (mul_nonneg hCpos.le h4A.le) hM
    linarith
  have key : ∀ᶠ y : ℕ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ, |t| ≤ (Nat.sqrt y : ℝ) →
          ∀ (P Q : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
            (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), ramTailWeight P Q r b / (b : ℝ)) ≤ M →
            (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q r b / (b : ℝ))
                ≤ 1 / (Real.log y) ^ A →
            ‖MmuGrChi χ t P Q r y‖ ≤ (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
    filter_upwards [Filter.eventually_ge_atTop 16, Filter.eventually_ge_atTop (x₀mu ^ 2),
        eventually_log_ge' ((4 : ℝ) ^ (12 : ℕ))] with y hy16 hyx0 hlog4
    intro q _ χ hq t ht P Q r hr0 hr1 hmass htail
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
    -- the μ-rate on the small range, in the `B·y/b` shape
    have hsmall : ∀ b ∈ Finset.Icc 1 (Nat.sqrt y),
        ‖MmuChi χ t (y / b)‖ ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * (y : ℝ) / (b : ℝ) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      obtain ⟨hb1, hbs⟩ := hb
      have hbpos : 0 < b := hb1
      -- `√y ≤ ⌊y/b⌋` (this is what transfers BOTH gates)
      have hts : Nat.sqrt y ≤ y / b := by
        rw [Nat.le_div_iff_mul_le hbpos]
        calc Nat.sqrt y * b ≤ Nat.sqrt y * Nat.sqrt y := by gcongr
          _ ≤ y := Nat.sqrt_le y
      have htx : x₀mu ≤ y / b := le_trans hs_ge_x0 hts
      have hlogt : Real.log y / 4 ≤ Real.log ((y / b : ℕ) : ℝ) := by
        refine le_trans hlogs ?_
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt y))
        exact_mod_cast hts
      -- THE CONDUCTOR GATE UPGRADE: `q ≤ (log y)^11 ≤ (log y/4)^12 ≤ (log⌊y/b⌋)^12`
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
      -- THE HEIGHT GATE TRANSFER: `|t| ≤ ⌊√y⌋ ≤ ⌊y/b⌋`
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
    have hsplit := norm_MmuGrChi_le_split χ t P Q r y hr1 hBnn hsmall hmass htail
    calc ‖MmuGrChi χ t P Q r y‖
        ≤ (C * (4 : ℝ) ^ A / (Real.log y) ^ A) * M * (y : ℝ)
            + (1 / (Real.log y) ^ A) * (y : ℝ) := hsplit
      _ = (C * (4 : ℝ) ^ A * M + 1) * y / (Real.log y) ^ A := by
          field_simp
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨C * (4 : ℝ) ^ A * M + 1, N, hC'pos, hN⟩

/-! ## §6 — the `∫₀¹ dr` composition: the RAMARÉ-WEIGHTED twisted datum -/

/-- **The Ramaré-WEIGHTED twisted Möbius summatory function**
`∑_{m ≤ y} μ(m)·(ω(m;P,Q)+1)^{−1}·χ̄(m)m^{it}` — the datum the co-factor polynomial `ramR`
carries (`Salt/MR/RamareWindows.lean:74`), read on the `σ = 0` summatory side. -/
noncomputable def MmuRamChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q : ℕ)
    (y : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 y, ((ArithmeticFunction.moebius m : ℤ) : ℂ)
      * ((blockOmega P Q m : ℂ) + 1)⁻¹ * chiBarTwist χ t m

/-- **The weight as a `[0,1]` average of the dampings** — the LANDED `RamWeight` device
(`integral_cpow_unit` / `inv_blockOmega_succ_eq_integral`) applied to the twisted summatory
function:  `M_{μ/(ω+1)χ̄}(y) = ∫₀¹ M_{μg_rχ̄}(y) dr`.  Finite sum against interval integral;
every summand is a polynomial in `r`. -/
theorem MmuRamChi_eq_integral {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q y : ℕ) :
    MmuRamChi χ t P Q y = ∫ r in (0:ℝ)..1, MmuGrChi χ t P Q r y := by
  have hMG : ∀ r : ℝ, MmuGrChi χ t P Q r y
      = ∑ m ∈ Finset.Icc 1 y,
          (((ArithmeticFunction.moebius m : ℤ) : ℂ) * chiBarTwist χ t m)
            * ((r : ℝ) : ℂ) ^ blockOmega P Q m := by
    intro r
    rw [MmuGrChi]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [muGr_apply]
    push_cast
    ring
  simp only [hMG]
  rw [intervalIntegral.integral_finsetSum (fun m _ => (by fun_prop : Continuous
    (fun r : ℝ => (((ArithmeticFunction.moebius m : ℤ) : ℂ) * chiBarTwist χ t m)
      * ((r : ℝ) : ℂ) ^ blockOmega P Q m)).intervalIntegrable _ _)]
  rw [MmuRamChi]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cpow_unit]
  ring

/-- **THE EXIT SHAPE** (the twisted twin of the LANDED `RamWeight.ramR_norm_le_of_damp_le`):
a bound on the damped twisted datum that is *uniform over `r ∈ [0,1]`* is a bound on the
Ramaré-WEIGHTED twisted datum itself.  The unit interval has length `1`, so no constant is
lost and no integrability side condition reaches the consumer. -/
theorem norm_MmuRamChi_le_of_uniform {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (P Q y : ℕ)
    {B : ℝ} (h : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖MmuGrChi χ t P Q r y‖ ≤ B) :
    ‖MmuRamChi χ t P Q y‖ ≤ B := by
  rw [MmuRamChi_eq_integral]
  have hbd : ∀ r ∈ Set.uIoc (0 : ℝ) 1, ‖MmuGrChi χ t P Q r y‖ ≤ B := by
    intro r hr
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    exact h r ⟨hr.1.le, hr.2⟩
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- **⟦O6⟧ THE RAMARÉ-WEIGHTED DELIVERABLE.**  The Ramaré-weighted twisted Möbius datum
`μ(m)/(ω(m;P,Q)+1)·χ̄(m)m^{it}` inherits the rate `C'·y/(log y)^A`, from `MmuChiRate` plus the
two named window hypothesis stated **at `r = 0` only**.

Two things make this free once `MmuGrChi_rate` is in hand:
* `MmuGrChi_rate`'s `C'` and `x₀` are independent of `r` (stated and true — `r` is universally
  quantified INSIDE);
* `ramTailWeight_le_zero_param`: `w_r ≤ w_0 = 1_{[P,Q]-smooth}` for `r ∈ [0,1]`, so the
  `r = 0` mass/tail hypotheses imply their `r`-general forms, uniformly.

So the hypotheses here are the *worst-case* (`r = 0`) window quantities: the mass is
`∑_{n ≤ √y, [P,Q]-smooth} 1/n`, of genre `∏_{P≤p≤Q}(1−1/p)^{−1} ≍ log Q/log P` by the landed
Mertens window page `Salt.MR.blockWindow_mertens_const` (cited, not invoked — see the header),
and the tail is the Rankin residue that the consumer pays at its own `P,Q` scales. -/
theorem MmuRamChi_rate (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧ ∀ y : ℕ, x₀ ≤ y →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q : ℝ) ≤ (Real.log y) ^ (11 : ℕ) → ∀ t : ℝ, |t| ≤ (Nat.sqrt y : ℝ) →
          ∀ P Q : ℕ,
            (∑ b ∈ Finset.Icc 1 (Nat.sqrt y), ramTailWeight P Q 0 b / (b : ℝ)) ≤ M →
            (∑ b ∈ Finset.Ioc (Nat.sqrt y) y, ramTailWeight P Q 0 b / (b : ℝ))
                ≤ 1 / (Real.log y) ^ A →
            ‖MmuRamChi χ t P Q y‖ ≤ C' * y / (Real.log y) ^ A := by
  obtain ⟨C', x₀, hC'pos, hbound⟩ := MmuGrChi_rate hMmu A hA hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro y hy q _ χ hq t ht P Q hmass0 htail0
  refine norm_MmuRamChi_le_of_uniform χ t P Q y ?_
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
