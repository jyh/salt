/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.TransferFull

/-!
# The `S⁽²⁾ → S⁽³⁾` star-condition step (HB-ENGINE, WP1, node HB-L4)

The twin-specialized transfer half of Heath-Brown 1983, Lemma 4 (the `S⁽²⁾ − S⁽³⁾`
display, p.198): replacing the twisted von Mangoldt `Λ̃` by its sieve-truncated
partner `Λ*` costs only a `p²`-exceptional error.  With `l₁ = n`, `l₂ = n + 2`,

* `S⁽²⁾ = Σ_{n∈A} Λ̃(n)·Λ̃(n+2)`  (`Salt.HB.S2`), and
* `S⁽³⁾ = Σ_{n∈A} Λ*(n)·Λ*(n+2)` (`S3`, mirroring `S2`).

## The mechanism (and the honest ADMISSIBLE-DIRECTION finding)

Both are read off the divisor sums of `Salt.HB.TwistChain`:
`Λ̃(m) = Σ_{d∣m} μ²(d)χ(d)log(m/d)` and `Λ*(m) = Σ*_{d∣m} χ(d)log(m/d)`, where the star
keeps `d` with `Admissible χ z d` — the landed predicate
`∀ p prime, p < z → χ(p) = −1 → ¬ p²∣d`.  **Note the two objects differ in TWO
places:** `Λ̃` caps at squarefree `d` (the `μ²`), while `Λ*` drops only the squares of
*small `χ(p) = −1`* primes.  Their difference is therefore carried exactly by the
**non-squarefree admissible** divisors:

`Λ*(m) − Λ̃(m) = starDiff χ z m := Σ_{d∣m, ¬sqfree d ∧ admissible d} χ(d)log(m/d)`.

A term needs a prime `p` with `p²∣d∣m` that is *not* removed by the star, i.e.
`p ≥ z ∨ χ(p) ≠ −1` (`HasExcSq`).  So:

* `LamStar_sub_LamTilde_eq_starDiff` — the exact identity;
* `LamTilde_eq_LamStar_of_no_exc_sq` — `Λ̃(m) = Λ*(m)` when every prime square
  dividing `m` comes from a *small `χ(p) = −1`* prime (Lemma-4's pointwise heart);
* `abs_starDiff_le_starErrBound` — `|Λ*−Λ̃|(m) ≤ [HasExcSq m]·τ(m)log m`, the crude
  weight supported on the exceptional `m`.

**The finding (documented, cross-noting the paper).**  HB's display phrases the
exceptional set as "`p² ∣ lᵢ` for some `p ≥ z`".  The *landed* `Admissible`
truncates at small `χ(p) = −1` primes (correct for Lemma 1(a)'s `f* ≥ 0`), so the
honest exceptional set here is `{p ≥ z} ∪ {p < z : χ(p) ≠ −1}` — it *also* contains
the small `χ(p) = +1` prime squares (e.g. `Λ*−Λ̃ (p²r) = +log r` for `p<z`, `χ(p)=1`,
`r` prime).  Over `p ≥ z` the tail `Σ 1/p²` gives the paper's `x·z⁻¹` grade
(`sq_dvd_count_le` + `excSum_ge_z_le`); the small `+1` squares are an `O(x)` residual
that the landed `Λ*` does not kill at this step — recovering the clean `z⁻¹` grade
needs `Λ*`'s truncation widened to *all* small primes (a def change, flagged, not
done here).  The assembled bound is therefore stated parametrically over the honest
exceptional sum.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the exceptional divisor sum `starDiff` and the identity `Λ* − Λ̃` -/

open Classical in
/-- The exceptional-divisor sum: the terms of `Λ*` carried by the **non-squarefree
    admissible** divisors, exactly the divisors where `Λ*` and `Λ̃` disagree. -/
noncomputable def starDiff (χ : DirichletCharacter ℂ q) (z m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors,
    if ¬ Squarefree d ∧ Admissible χ z d then chiRe χ d * Real.log ((m / d : ℕ) : ℝ) else 0

/-- `m` has an *exceptional square*: a prime `p` with `p² ∣ m` that the star does NOT
    remove (`p ≥ z ∨ χ(p) ≠ −1`).  This is the support of `Λ* − Λ̃`. -/
def HasExcSq (χ : DirichletCharacter ℂ q) (z m : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ m ∧ ¬ (p < z ∧ chiRe χ p = -1)

noncomputable instance instDecidableHasExcSq (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    Decidable (HasExcSq χ z m) := Classical.propDecidable _

/-- A squarefree divisor is always admissible (no prime square divides it). -/
lemma admissible_of_squarefree (χ : DirichletCharacter ℂ q) (z : ℕ) {d : ℕ}
    (hd : Squarefree d) : Admissible χ z d := by
  intro p hp _ _ hpd
  exact hp.ne_one (Nat.isUnit_iff.mp (hd p (by rw [← pow_two]; exact hpd)))

/-- **The exact identity.**  `Λ*(m) − Λ̃(m) = starDiff χ z m`: the two twisted von
    Mangoldt functions differ precisely on the non-squarefree admissible divisors
    (squarefree `d` cancel; small `χ = −1` prime squares are dropped by both). -/
theorem LamStar_sub_LamTilde_eq_starDiff (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    LamStar χ z m - LamTilde χ m = starDiff χ z m := by
  rw [LamStar, LamTilde, starDiff, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hSF : Squarefree d
  · have hμ : ((μ d : ℝ)) ^ 2 = 1 := by
      have : (μ d) ^ 2 = 1 := moebius_sq_eq_one_of_squarefree hSF
      have hcast : ((μ d : ℝ)) ^ 2 = (((μ d) ^ 2 : ℤ) : ℝ) := by push_cast; ring
      rw [hcast, this]; norm_num
    rw [if_pos (admissible_of_squarefree χ z hSF),
        if_neg (fun h => h.1 hSF), hμ]
    ring
  · have hμ : ((μ d : ℝ)) ^ 2 = 0 := by
      rw [moebius_eq_zero_of_not_squarefree hSF]; norm_num
    by_cases hAdm : Admissible χ z d
    · rw [if_pos hAdm, if_pos ⟨hSF, hAdm⟩, hμ]; ring
    · rw [if_neg hAdm, if_neg (fun h => hAdm h.2), hμ]; ring

/-! ## §2 — the pointwise characterization (Lemma-4's heart) -/

/-- **The characterization stone.**  `starDiff = 0` whenever every prime square
    dividing `m` comes from a *small `χ(p) = −1`* prime — then no admissible
    non-squarefree divisor exists. -/
theorem starDiff_eq_zero_of_no_exc_sq (χ : DirichletCharacter ℂ q) (z m : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ^ 2 ∣ m → p < z ∧ chiRe χ p = -1) :
    starDiff χ z m = 0 := by
  rw [starDiff]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [if_neg]
  rintro ⟨hnsf, hadm⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hnsf
  simp only [not_forall, not_not] at hnsf
  obtain ⟨p, hp, hpd⟩ := hnsf
  have hpnat : p.Prime := hp
  have hpd2 : p ^ 2 ∣ d := by rw [pow_two]; exact hpd
  have hpm : p ^ 2 ∣ m := hpd2.trans (Nat.dvd_of_mem_divisors hd)
  obtain ⟨hpz, hpc⟩ := h p hpnat hpm
  exact hadm p hpnat hpz hpc hpd2

/-- **Lemma 4, pointwise heart.**  `Λ̃(m) = Λ*(m)` when no exceptional square divides
    `m` (every `p²∣m` is a small `χ(p) = −1` prime square). -/
theorem LamTilde_eq_LamStar_of_no_exc_sq (χ : DirichletCharacter ℂ q) (z m : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ^ 2 ∣ m → p < z ∧ chiRe χ p = -1) :
    LamTilde χ m = LamStar χ z m := by
  have hid := LamStar_sub_LamTilde_eq_starDiff χ z m
  rw [starDiff_eq_zero_of_no_exc_sq χ z m h] at hid
  linarith

/-! ## §3 — crude weights and the exceptional majorant `starErrBound` -/

/-- The single-term crude bound: `|if P then χ(d)log(m/d) else 0| ≤ log m` for `d ∣ m`. -/
lemma abs_ite_chi_log_le (χ : DirichletCharacter ℂ q) {m d : ℕ} (hd : d ∈ m.divisors)
    (P : Prop) [Decidable P] :
    |if P then chiRe χ d * Real.log ((m / d : ℕ) : ℝ) else 0| ≤ Real.log m := by
  obtain ⟨hdvd, hm0⟩ := Nat.mem_divisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hnd : 1 ≤ m / d := (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hdvd)
  have hLnn : 0 ≤ Real.log ((m / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hnd)
  have hLle : Real.log ((m / d : ℕ) : ℝ) ≤ Real.log m :=
    Real.log_le_log (by exact_mod_cast hnd) (by exact_mod_cast Nat.div_le_self m d)
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  by_cases hP : P
  · rw [if_pos hP, abs_mul, abs_of_nonneg hLnn]
    calc |chiRe χ d| * Real.log ((m / d : ℕ) : ℝ)
        ≤ 1 * Real.log ((m / d : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (chiRe_abs_le_one χ d) hLnn
      _ = Real.log ((m / d : ℕ) : ℝ) := one_mul _
      _ ≤ Real.log m := hLle
  · rw [if_neg hP, abs_zero]; exact hlogm

/-- `|Λ*(m)| ≤ τ(m)·log m` (the crude divisor weight). -/
lemma abs_LamStar_le_tauLog (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    |LamStar χ z m| ≤ tauLog m := by
  rw [LamStar]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (le_trans (Finset.sum_le_sum fun d hd => abs_ite_chi_log_le χ hd (Admissible χ z d)) ?_)
  rw [tauLog, Finset.sum_const, nsmul_eq_mul]

/-- `Λ*(m) ≤ τ(m)·log m`. -/
lemma LamStar_le_tauLog (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    LamStar χ z m ≤ tauLog m :=
  le_trans (le_abs_self _) (abs_LamStar_le_tauLog χ z m)

/-- `|starDiff(m)| ≤ τ(m)·log m` (the crude weight before restricting to `HasExcSq`). -/
lemma abs_starDiff_le_tauLog (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    |starDiff χ z m| ≤ tauLog m := by
  rw [starDiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (le_trans (Finset.sum_le_sum fun d hd =>
      abs_ite_chi_log_le χ hd (¬ Squarefree d ∧ Admissible χ z d)) ?_)
  rw [tauLog, Finset.sum_const, nsmul_eq_mul]

/-- `tauLog n ≥ 0`. -/
lemma tauLog_nonneg (n : ℕ) : 0 ≤ tauLog n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [tauLog]
  · rw [tauLog]
    exact mul_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))

open Classical in
/-- The **exceptional majorant** `starErrBound χ z m = [HasExcSq m]·τ(m)log m`: the
    crude weight `τ(m)log m`, supported only on the exceptional `m` (`= 0` otherwise,
    by the characterization stone). -/
noncomputable def starErrBound (χ : DirichletCharacter ℂ q) (z m : ℕ) : ℝ :=
  if HasExcSq χ z m then (m.divisors.card : ℝ) * Real.log m else 0

lemma starErrBound_nonneg (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    0 ≤ starErrBound χ z m := by
  rw [starErrBound]
  by_cases hE : HasExcSq χ z m
  · rw [if_pos hE]; exact tauLog_nonneg m
  · rw [if_neg hE]

/-- **The pointwise error bound.**  `|Λ*(m) − Λ̃(m)| ≤ starErrBound χ z m`: off the
    exceptional set the difference vanishes (characterization stone), on it the crude
    `τ(m)log m` weight applies. -/
theorem abs_starDiff_le_starErrBound (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    |starDiff χ z m| ≤ starErrBound χ z m := by
  rw [starErrBound]
  by_cases hE : HasExcSq χ z m
  · rw [if_pos hE]; exact abs_starDiff_le_tauLog χ z m
  · rw [if_neg hE]
    have h : ∀ p : ℕ, p.Prime → p ^ 2 ∣ m → p < z ∧ chiRe χ p = -1 := by
      intro p hp hpm
      by_contra hcon
      exact hE ⟨p, hp, hpm, hcon⟩
    rw [starDiff_eq_zero_of_no_exc_sq χ z m h, abs_zero]

/-! ## §4 — the sum `S⁽³⁾` -/

/-- `S⁽³⁾ = Σ_{n∈A} Λ*(n)·Λ*(n+2)` — the sieve-truncated twin sum (mirrors `S2`). -/
noncomputable def S3 (χ : DirichletCharacter ℂ q) (z : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, LamStar χ z n * LamStar χ z (n + 2)

/-! ## §5 — the termwise product bound and the summed transfer inequality -/

/-- **Termwise product bound.**  Bracketing `Λ̃Λ̃ − Λ*Λ*` by the two crude/exceptional
    weights via `Λ̃Λ̃ − Λ*Λ* = (Λ̃−Λ*)Λ̃ + Λ*(Λ̃−Λ*)`, `Λ̃,Λ* ≥ 0`, and the pointwise
    error bound `|Λ̃−Λ*| ≤ starErrBound`. -/
lemma abs_twin_termwise_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z n : ℕ) :
    |LamTilde χ n * LamTilde χ (n + 2) - LamStar χ z n * LamStar χ z (n + 2)|
      ≤ starErrBound χ z n * tauLog (n + 2) + tauLog n * starErrBound χ z (n + 2) := by
  have hid : LamTilde χ n * LamTilde χ (n + 2) - LamStar χ z n * LamStar χ z (n + 2)
      = (LamTilde χ n - LamStar χ z n) * LamTilde χ (n + 2)
        + LamStar χ z n * (LamTilde χ (n + 2) - LamStar χ z (n + 2)) := by ring
  rw [hid]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · rw [abs_mul]
    have e1 : |LamTilde χ n - LamStar χ z n| ≤ starErrBound χ z n := by
      rw [abs_sub_comm, LamStar_sub_LamTilde_eq_starDiff]
      exact abs_starDiff_le_starErrBound χ z n
    have e2 : |LamTilde χ (n + 2)| ≤ tauLog (n + 2) := by
      rw [abs_of_nonneg (LamTilde_nonneg χ hsq (n + 2))]
      exact LamTilde_le_tau_log χ (by omega)
    exact mul_le_mul e1 e2 (abs_nonneg _) (starErrBound_nonneg χ z n)
  · rw [abs_mul]
    have e3 : |LamStar χ z n| ≤ tauLog n := abs_LamStar_le_tauLog χ z n
    have e4 : |LamTilde χ (n + 2) - LamStar χ z (n + 2)| ≤ starErrBound χ z (n + 2) := by
      rw [abs_sub_comm, LamStar_sub_LamTilde_eq_starDiff]
      exact abs_starDiff_le_starErrBound χ z (n + 2)
    exact mul_le_mul e3 e4 (abs_nonneg _) (tauLog_nonneg n)

/-- **The summed star-step inequality (rung, honest master form).**  Replacing `Λ̃` by
    `Λ*` in the twin sum costs at most the exceptional majorant sum; no coprimality
    needed (pure triangle inequality + crude weights + `Λ̃,Λ* ≥ 0`).  The RHS vanishes
    off the `HasExcSq` set, so it is genuinely an exceptional-`n` sum. -/
theorem S2_sub_S3_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) (A : Finset ℕ) :
    |S2 χ A - S3 χ z A|
      ≤ ∑ n ∈ A, (starErrBound χ z n * tauLog (n + 2)
        + tauLog n * starErrBound χ z (n + 2)) := by
  have hdiff : S2 χ A - S3 χ z A
      = ∑ n ∈ A, (LamTilde χ n * LamTilde χ (n + 2)
          - LamStar χ z n * LamStar χ z (n + 2)) := by
    rw [S2, S3, ← Finset.sum_sub_distrib]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact Finset.sum_le_sum fun n _ => abs_twin_termwise_le χ hsq z n

/-! ## §6 — the exceptional prime-square count -/

/-- **The square-multiple count.**  In a dyadic window `(x, 2x]` at most `x/p² + 1`
    integers are divisible by `p²` (the two dyadic floors differ by `≤ x/p² + 1`). -/
lemma sq_dvd_count_le (x p : ℕ) (hp : 0 < p) :
    (((Finset.Ioc x (2 * x)).filter (fun n => p ^ 2 ∣ n)).card : ℝ)
      ≤ (x : ℝ) / (p : ℝ) ^ 2 + 1 := by
  set k := p ^ 2 with hk
  have hk0 : 0 < k := pow_pos hp 2
  have hdisj : Disjoint (Finset.Ioc 0 x) (Finset.Ioc x (2 * x)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_Ioc] at hn1 hn2; omega
  have hdisjf : Disjoint ((Finset.Ioc 0 x).filter (fun m => k ∣ m))
      ((Finset.Ioc x (2 * x)).filter (fun m => k ∣ m)) :=
    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj
  have hcardunion : ((Finset.Ioc 0 (2 * x)).filter (fun m => k ∣ m)).card
      = ((Finset.Ioc 0 x).filter (fun m => k ∣ m)).card
        + ((Finset.Ioc x (2 * x)).filter (fun m => k ∣ m)).card := by
    rw [← Finset.card_union_of_disjoint hdisjf, ← Finset.filter_union,
        Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) (by omega)]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hcardunion
  have h2 : 2 * x / k < 2 * (x / k) + 2 := by
    rw [Nat.div_lt_iff_lt_mul hk0]
    nlinarith [Nat.div_add_mod x k, Nat.mod_lt x hk0]
  have hcard : ((Finset.Ioc x (2 * x)).filter (fun m => k ∣ m)).card ≤ x / k + 1 := by omega
  have hcast : ((((Finset.Ioc x (2 * x)).filter (fun m => k ∣ m)).card : ℕ) : ℝ)
      ≤ ((x / k : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  have hdiv : ((x / k : ℕ) : ℝ) ≤ (x : ℝ) / (k : ℝ) := Nat.cast_div_le
  have hkcast : ((k : ℕ) : ℝ) = (p : ℝ) ^ 2 := by rw [hk]; push_cast; ring
  rw [hkcast] at hdiv
  linarith

/-- **The reciprocal prime-square tail.**  Any finite set of naturals bounded below by
    `z ≥ 1` (and above by any `M`) has `Σ 1/p² ≤ 2/z`.  This is the convergent tail
    (mathlib's `sum_Ioo_inv_sq_le`) that, fed the per-prime `sq_dvd_count_le`, produces
    the paper's `x·z⁻¹` grade for the `p ≥ z` exceptional squares. -/
lemma sq_recip_tail_le {z M : ℕ} (hz : 1 ≤ z) (P : Finset ℕ)
    (hlo : ∀ p ∈ P, z ≤ p) (hhi : ∀ p ∈ P, p < M) :
    ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 / (z : ℝ) := by
  have hsub : P ⊆ Finset.Ioo (z - 1) M := fun p hp =>
    Finset.mem_Ioo.mpr ⟨by have := hlo p hp; omega, hhi p hp⟩
  have hstep : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ i ∈ Finset.Ioo (z - 1) M, ((i : ℝ) ^ 2)⁻¹ := by
    rw [show (∑ i ∈ Finset.Ioo (z - 1) M, ((i : ℝ) ^ 2)⁻¹)
        = ∑ i ∈ Finset.Ioo (z - 1) M, (1 : ℝ) / (i : ℝ) ^ 2 by simp only [one_div]]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  refine le_trans hstep (le_trans (sum_Ioo_inv_sq_le (z - 1) M) (le_of_eq ?_))
  rw [Nat.cast_sub hz]; push_cast; ring

/-! ## §7 — the assembled star-step bound (the node, parametric) -/

/-- **Node HB-L4 — the assembled `S⁽²⁾ − S⁽³⁾` bound (parametric).**  Composing the
    master inequality `S2_sub_S3_le` with the residual `p ≥ z` tail estimate `hres` on
    the exceptional majorant sum yields the HB-Lemma-4-shaped error
    `Cerr·(x/z) + junk`.

    The single named input `hres` is the honest residual: the union bound of the
    exceptional-`n` sum over the witness prime squares, then per prime `sq_dvd_count_le`
    (`≤ x/p² + 1`), the reciprocal-square tail over `p ≥ z` (the `x·z⁻¹` grade), and the
    `π(2x)·log²`-grade junk from the `+1` counts.  Exactly analogous to `hb_lemma2`'s
    reduction to its named resisting sum. -/
theorem S2_sub_S3_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ)
    (A : Finset ℕ) (x Cerr junk : ℝ)
    (hres : ∑ n ∈ A, (starErrBound χ z n * tauLog (n + 2)
        + tauLog n * starErrBound χ z (n + 2)) ≤ Cerr * (x / (z : ℝ)) + junk) :
    |S2 χ A - S3 χ z A| ≤ Cerr * (x / (z : ℝ)) + junk :=
  le_trans (S2_sub_S3_le χ hsq z A) hres

/-! ## §8 — (stretch) the composed `S⁽¹⁾ → S⁽³⁾` transfer -/

/-- **The composed transfer (stretch).**  Chaining the Lemma-2 lower half `S⁽¹⁾ ≤ S⁽²⁾`
    with the star step: the genuine-to-sieve-truncated twin-sum error splits as the
    Lemma-2 overshoot gap `S⁽²⁾ − S⁽¹⁾` plus the star-step exceptional majorant. -/
theorem abs_S1_sub_S3_le (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ)
    (A : Finset ℕ) :
    |S1 A - S3 χ z A|
      ≤ (S2 χ A - S1 A) + ∑ n ∈ A, (starErrBound χ z n * tauLog (n + 2)
        + tauLog n * starErrBound χ z (n + 2)) := by
  have h1 : S1 A ≤ S2 χ A := S1_le_S2 χ hsq A
  have h2 := S2_sub_S3_le χ hsq z A
  have hsplit : S1 A - S3 χ z A = (S1 A - S2 χ A) + (S2 χ A - S3 χ z A) := by ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_sub_comm (S1 A), abs_of_nonneg (by linarith : (0 : ℝ) ≤ S2 χ A - S1 A)]
  linarith

/-- **The composed transfer, assembled (stretch, parametric).**  Feeding both the
    Lemma-2 overshoot estimate (`hovs`, HB (3.3)-grade) and the star-step residual
    (`hstar`, the `p ≥ z` tail) bounds the full `S⁽¹⁾ → S⁽³⁾` transfer error. -/
theorem S1_sub_S3_bound (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ)
    (A : Finset ℕ) (B C : ℝ)
    (hovs : S2 χ A - S1 A ≤ B)
    (hstar : ∑ n ∈ A, (starErrBound χ z n * tauLog (n + 2)
        + tauLog n * starErrBound χ z (n + 2)) ≤ C) :
    |S1 A - S3 χ z A| ≤ B + C :=
  le_trans (abs_S1_sub_S3_le χ hsq z A) (add_le_add hovs hstar)

end Salt.HB
