/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TwinA1W
import Salt.Chen.WLower
import Salt.Goldbach.Density

/-!
# G-A1 (base) — the Goldbach `A₁` sieve layer under `n + 2 ↦ N − n`

Design: `docs/exploration/q1-design.md`, node **G-A1** (wave W2).  The mechanical mirror of the
twin `A₁` sieve (`Salt/Chen/TwinA1.lean`) under the Goldbach substitution: the paired value is
`N − n` (the `P₂` side of `N = p + q`) instead of the twin partner `n + 2`, and the sifted
residue class becomes `N mod d` instead of `d − 2`.  The window finset is unchanged
(`Salt.Chen.twinWindow N = Icc (N/2) (N−2)`); only the value map reflects.

The key structural differences from the twin (all handled here):

* **The reflection `n ↦ N − n` is only `InjOn` the window** (ℕ-subtraction collapses above `N`);
  the `multSum`/`siftedSum` `Finset.sum_image` steps consume the membership bound `n ≤ N`.
* **The coprimality is uniform**: the divisor coprimality `Coprime d N` (threaded as
  `Coprime P N`, discharged downstream by `goldPs_coprime_N`) holds for *every* `d ∣ P`
  — including `d = 1` — so the twin's `d = 1 ∨ (3 ≤ d ∧ Odd d)` `divisor_cases` split and the
  separate `rem 1 = 0` case **both vanish** (the `{q ∣ N}` seam of the gate).  The base
  remainder split `goldBVSum_le_split` is a single uniform branch.

## Reuse

`nuChen`, `apDiscW`/`apDiscW_le`, `convTerm`/`convSum_le`, `dispDisc_filtered_le_Icc`,
`sum_inv_totient_le_Winv`, `vratio_prod_le`, `sum_Icc_window`, the linear-sieve keystones
(`hlevel_w_lower`, `hlevel_wpc_lower`, `linear_sieve_lower_rosser_assembled_final`),
`twinA1_hnu`/`twinA1_hguard`, and the unconditional BV `psi_BV_of_siegelWalfisz'` are all reused
verbatim (the sieve engine is support-agnostic; `nu = nuChen` and `totalMass` are the twin's).
`coprime_mod_of_coprime` (Density) supplies the reduced residue `Coprime d (N mod d)`.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.LS Salt.BV Salt.Chen

namespace Salt.Goldbach

/-! ## Part A — the Goldbach `A₁` `BoundingSieve` (`goldA1Sieve`) -/

/-- **The Goldbach `A₁` `BoundingSieve`.**  Support = the reflected window values `N − n`, weight
`Λ(n)` at `N − n` (via `m ↦ Λ(N − m)`, inverting the reflection on the window), `totalMass` the
exact window Λ-mass, density `ν = nuChen = 1/φ`, sifting modulus `P` (all prime factors `≥ 3`).
Mirrors `twinA1Sieve` with the paired value `n + 2 ↦ N − n`. -/
noncomputable def goldA1Sieve (N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : BoundingSieve where
  support := (twinWindow N).image (fun n => N - n)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun m => vonMangoldt (N - m)
  weights_nonneg := fun _ => vonMangoldt_nonneg
  totalMass := ∑ n ∈ twinWindow N, vonMangoldt n
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hP.ne_zero⟩))

section Facts

@[simp] lemma goldA1Sieve_prodPrimes (N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : (goldA1Sieve N P hP hPodd).prodPrimes = P := rfl

@[simp] lemma goldA1Sieve_nu (N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : (goldA1Sieve N P hP hPodd).nu = nuChen := rfl

@[simp] lemma goldA1Sieve_totalMass (N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (goldA1Sieve N P hP hPodd).totalMass = ∑ n ∈ twinWindow N, vonMangoldt n := rfl

/-- **`multSum d` = the window Λ-mass at the residue `n ≡ N (mod d)`.**  The sieve sifts the
reflected value `N − n` by `d ∣ N − n`; the `Finset.sum_image` step consumes the reflection's
window-`InjOn` (`n ≤ N`). -/
lemma goldA1Sieve_multSum (N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (d : ℕ) :
    (goldA1Sieve N P hP hPodd).multSum d
      = ∑ n ∈ twinWindow N, if d ∣ (N - n) then vonMangoldt n else 0 := by
  change (∑ m ∈ (twinWindow N).image (fun n => N - n),
      if d ∣ m then vonMangoldt (N - m) else 0) = _
  rw [Finset.sum_image (fun a ha b hb h => by
    rw [Finset.mem_coe, twinWindow, Finset.mem_Icc] at ha hb
    have h' : N - a = N - b := h
    omega)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [twinWindow, Finset.mem_Icc] at hn
  rw [show N - (N - n) = n from by omega]

/-- **`siftedSum` = the Goldbach `A₁` carrier.**  The Λ-weighted count of `n` in the window with
`N − n` coprime to `P`. -/
lemma goldA1Sieve_siftedSum (N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (goldA1Sieve N P hP hPodd).siftedSum
      = ∑ n ∈ twinWindow N, if Nat.Coprime P (N - n) then vonMangoldt n else 0 := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ (twinWindow N).image (fun n => N - n),
      if Nat.Coprime P m then vonMangoldt (N - m) else 0) = _
  rw [Finset.sum_image (fun a ha b hb h => by
    rw [Finset.mem_coe, twinWindow, Finset.mem_Icc] at ha hb
    have h' : N - a = N - b := h
    omega)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [twinWindow, Finset.mem_Icc] at hn
  rw [show N - (N - n) = n from by omega]

/-- **`rem d`** — the AP-remainder, `rem d = multSum d − ν(d)·totalMass`. -/
lemma goldA1Sieve_rem (N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (d : ℕ) :
    (goldA1Sieve N P hP hPodd).rem d
      = (∑ n ∈ twinWindow N, if d ∣ (N - n) then vonMangoldt n else 0)
        - nuChen d * ∑ n ∈ twinWindow N, vonMangoldt n := by
  rw [BoundingSieve.rem, goldA1Sieve_multSum, goldA1Sieve_nu, goldA1Sieve_totalMass]

end Facts

/-! ## Part B — the divisibility bridge and the cumulative AP-sum -/

/-- **The Goldbach divisibility bridge.**  For `n ≤ N`, `d ∣ (N − n) ↔ n ≡ N (mod d)` (as
`n % d = (N % d) % d`).  Replaces the twin `dvd_add_two_iff` (`d ∣ n + 2 ↔ n ≡ d − 2`).  Mind
the ℕ-subtraction: the equivalence needs `n ≤ N` (below `N` the reflection is honest), which the
window supplies. -/
theorem dvd_sub_iff {d N n : ℕ} (hn : n ≤ N) :
    (d ∣ (N - n)) ↔ (n % d = (N % d) % d) := by
  rw [Nat.mod_mod_of_dvd N (dvd_refl d)]
  exact (Nat.modEq_iff_dvd' hn).symm

/-- The cumulative window AP-sum equals `psiAP` at the reflected residue `N mod d`
(for `y ≤ N`, so every `n ∈ [1, y]` is below `N`). -/
theorem apSum_eq_psiAP {d N : ℕ} (y : ℕ) (hy : y ≤ N) :
    (∑ n ∈ Finset.Icc 1 y, if d ∣ (N - n) then vonMangoldt n else 0) = psiAP y d (N % d) := by
  rw [psiAP, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_Icc] at hn
  exact dvd_sub_iff (le_trans hn.2 hy)

/-! ## Part C — the two-endpoint (39) remainder reduction

The Goldbach `A₁` discrepancy at divisor `d` sits at the reduced class `N mod d` of modulus `d`.
The base discrepancy carrier is the landed `apDiscW · d (N mod d)` (`Salt/Chen/TwinA1W.lean`, the
class-parametric mirror of the twin `apDisc`), so `apDiscW_le` supplies the per-endpoint BV bound
verbatim once the class is shown reduced (`coprime_mod_of_coprime`). -/

/-- **The two-endpoint window subtraction.**  `rem d = apDiscW (N−2) d (N mod d) −
apDiscW (N/2−1) d (N mod d)`: the window `[N/2, N−2] = [1, N−2] ∖ [1, N/2−1]`, so the
AP-remainder splits into the two cumulative-endpoint discrepancies.  Mirrors `twinA1_rem_eq`. -/
theorem goldA1_rem_eq (N P : ℕ) (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (d : ℕ) (hN : 4 ≤ N) :
    (goldA1Sieve N P hP hPodd).rem d
      = apDiscW (N - 2) d (N % d) - apDiscW (N / 2 - 1) d (N % d) := by
  rw [goldA1Sieve_rem, twinWindow,
    sum_Icc_window (fun n => if d ∣ (N - n) then vonMangoldt n else 0) (N / 2) (N - 2)
      (by omega) (by omega),
    sum_Icc_window (fun n => vonMangoldt n) (N / 2) (N - 2) (by omega) (by omega)]
  rw [apSum_eq_psiAP (N - 2) (by omega), apSum_eq_psiAP (N / 2 - 1) (by omega)]
  have hpt : ∀ y, (∑ n ∈ Finset.Icc 1 y, vonMangoldt n) = psiTot y := fun _ => rfl
  rw [hpt (N - 2), hpt (N / 2 - 1), apDiscW, apDiscW, nuChen_apply]
  ring

/-- **The pointwise (39) bound.**  For every `d` with `Coprime d N` (uniform over `d ∣ P` when
`Coprime P N`, including `d = 1`), `|rem d| ≤ dispDisc (N−2) d + dispDisc (N/2−1) d +
convTerm N d`.  The reduced class `N mod d` is a unit via `coprime_mod_of_coprime`; the endpoint
bounds are `apDiscW_le`.  Mirrors `twinA1_abs_rem_le` — no oddness, no `d = 1` special case. -/
theorem goldA1_abs_rem_le (N P : ℕ) (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (d : ℕ) (hd1 : 1 ≤ d) (hdN : Nat.Coprime d N) (hN : 4 ≤ N) :
    |(goldA1Sieve N P hP hPodd).rem d|
      ≤ dispDisc (N - 2) d + dispDisc (N / 2 - 1) d + convTerm N d := by
  rw [goldA1_rem_eq N P hP hPodd d hN]
  have hcop : Nat.Coprime d (N % d) := coprime_mod_of_coprime hdN
  have h1 := apDiscW_le (N - 2) d (N % d) hd1 hcop (by omega)
  have h2 := apDiscW_le (N / 2 - 1) d (N % d) hd1 hcop (by omega)
  have htri : |apDiscW (N - 2) d (N % d) - apDiscW (N / 2 - 1) d (N % d)|
      ≤ |apDiscW (N - 2) d (N % d)| + |apDiscW (N / 2 - 1) d (N % d)| := abs_sub _ _
  unfold convTerm
  linarith [htri, h1, h2]

/-! ## Part D — the assembled `A₁` lower bound (`gold_A1_lower`, `gold_A1_lower_B`) -/

/-- **`gold_A1_lower` — the Goldbach `A₁` lower bound.**  `twin_A1_lower` at `goldA1Sieve`: the
assembled lower linear-sieve bound for the Goldbach `A₁` carrier, feeding the generic keystones
`hlevel_w_lower` + `linear_sieve_lower_rosser_assembled_final` (both support-agnostic), with the
(39) BV remainder folded in as `hBV`.  The sifted sum is `Σ Λ(n)·1_{gcd(N−n, P)=1}`. -/
theorem gold_A1_lower (N z D P : ℕ) (ε K C₂ Q : ℝ) (tau : ℕ → ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hz2 : 2 ≤ z) (hzD : z ≤ D) (hD : 1 ≤ D)
    (hStop : 2 ≤ logRatio z D)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hKe : K ≤ 1 + ε)
    (htau1 : tau 1 = 3) (hτ0 : ∀ n, 0 ≤ tau n)
    (hτrec : ∀ n, cf_const n ε + ε * Real.exp 2 * ch_const n ε * tau n
        ≤ ε * Real.exp 2 * tau (n + 1))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (htau : ∑ n ∈ (Finset.range (maxDepth (goldA1Sieve N P hP hPodd) + 1)).filter
        (fun n => Even n), tau n ≤ C₂)
    (hQ : 1 ≤ Q)
    (hBV : rosserRemainder (goldA1Sieve N P hP hPodd) (Q * D) ≤ (N : ℝ) / (Real.log N) ^ 10) :
    (goldA1Sieve N P hP hPodd).totalMass *
        (Salt.BrunLower.W (goldA1Sieve N P hP hPodd) *
          (fchain (maxDepth (goldA1Sieve N P hP hPodd)) (logRatio z D)
            - ε * C₂ * Real.exp 2 * hBJS (logRatio z D)))
      - (N : ℝ) / (Real.log N) ^ 10
    ≤ ∑ n ∈ twinWindow N, if Nat.Coprime P (N - n) then vonMangoldt n else 0 := by
  set s := goldA1Sieve N P hP hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < z := hPz
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := twinA1_hnu P
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    twinA1_hguard hε hw0 hPodd hPlow
  have htm : 0 ≤ s.totalMass := by
    rw [hs, goldA1Sieve_totalMass]; exact Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  have hlevel := hlevel_w_lower s z D ε K tau hD hzTop hguard hnu hε.le hKe htau1 hτ0 hτrec h4 hStop
  have hassembled := linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hzTop htm
    (logRatio z D) ε C₂ Q hQ hε.le tau hlevel htau
  rw [hs, goldA1Sieve_siftedSum] at hassembled
  linarith [hassembled, hBV]

/-- **`gold_A1_lower_B` — the sharp (cB) Goldbach `A₁` lower bound** (the `twin_A1_lower_B`
mirror).  The numeric τ-layer is discharged at the FREEZE-V2 boundary-padded coefficients; the
single per-step slot `hstepWPC` + contraction gate `ε < 1/249`; slack constant `CsharpB ε`. -/
theorem gold_A1_lower_B (N z D P : ℕ) (ε K Q : ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hz2 : 2 ≤ z) (hzD : z ≤ D) (hD : 1 ≤ D)
    (hStop : 2 ≤ logRatio z D)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hKe : K ≤ 1 + ε)
    (hε49B : ε < 1 / 249)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hQ : 1 ≤ Q)
    (hBV : rosserRemainder (goldA1Sieve N P hP hPodd) (Q * D) ≤ (N : ℝ) / (Real.log N) ^ 10) :
    (goldA1Sieve N P hP hPodd).totalMass *
        (Salt.BrunLower.W (goldA1Sieve N P hP hPodd) *
          (fchain (maxDepth (goldA1Sieve N P hP hPodd)) (logRatio z D)
            - ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z D)))
      - (N : ℝ) / (Real.log N) ^ 10
    ≤ ∑ n ∈ twinWindow N, if Nat.Coprime P (N - n) then vonMangoldt n else 0 := by
  set s := goldA1Sieve N P hP hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < z := hPz
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := twinA1_hnu P
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    twinA1_hguard hε hw0 hPodd hPlow
  have htm : 0 ≤ s.totalMass := by
    rw [hs, goldA1Sieve_totalMass]; exact Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)
  have hlevel := hlevel_wpc_lower s z D ε K (fun n => cfSharpB n ε) (fun _ => chSharpB ε)
    (tauSharpB ε) hD hzTop hguard hnu hε.le hKe (tauSharpB_one ε) (tauSharpB_nonneg hε.le)
    hstepWPC (fun n => tauSharpB_hτrec n) h4 hStop
  have hassembled := linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hzTop htm
    (logRatio z D) ε (CsharpB ε) Q hQ hε.le (tauSharpB ε) hlevel
    (tauSharpB_sum_even_le hε.le hε49B (maxDepth s + 1))
  rw [hs, goldA1Sieve_siftedSum] at hassembled
  linarith [hassembled, hBV]

/-! ## Part E — the summed BV remainder (`goldBVSum_le_split`, `goldBVSum`)

The Goldbach split has NO `divisor_cases`: `goldA1_abs_rem_le` needs only `Coprime d N`
(uniform over `d ∣ P` from `Coprime P N`, `d = 1` included), so the twin's odd/`d = 1`
disjunction dissolves.  Everything else — `dispDisc_filtered_le_Icc`, `convSum_le`,
`sum_inv_totient_le_Winv`, `vratio_prod_le`, `psi_BV_of_siegelWalfisz'` — is reused. -/

/-- **The base split.**  The Rosser remainder is bounded termwise (uniformly via
`goldA1_abs_rem_le`, no `divisor_cases`) by the two endpoint BV discrepancy sums plus the
conversion sum, over the level-restricted divisors `d < bound`. -/
lemma goldBVSum_le_split (N P : ℕ) (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPN : Nat.Coprime P N) (hN : 4 ≤ N) (bound : ℝ) :
    rosserRemainder (goldA1Sieve N P hP hPodd) bound
      ≤ (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (N - 2) d else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (N / 2 - 1) d else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then convTerm N d else 0) := by
  rw [rosserRemainder]
  simp only [goldA1Sieve_prodPrimes]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdN : Nat.Coprime d N :=
    Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd) hPN
  by_cases hlt : (d : ℝ) < bound
  · simp only [if_pos hlt]
    have h := goldA1_abs_rem_le N P hP hPodd d (by omega) hdN hN
    unfold convTerm at h ⊢
    linarith [h]
  · simp only [if_neg hlt]
    simp

/-- **G-A1 base — the summed remainder bound `goldBVSum`.**  Instantiating the unconditional
Bombieri–Vinogradov keystone `psi_BV_of_siegelWalfisz' siegelWalfisz_holds` at saving `11`, the
Rosser remainder of the Goldbach `A₁` sieve is `≤ N/(log N)^10`, given the two consumer
obligations (the level check `Q·D ≤ √N/(log N)^B` and the numeric closing) — both hold at the
frozen operating point for `N` large.  Mirrors `twinA1_hBV`; consumes the threaded
`Coprime P N`. -/
theorem goldBVSum (N z D P : ℕ) (ε Q : ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ)) (hPN : Nat.Coprime P N)
    (hx : 4 ≤ N) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
    (hwz : w0R ε ≤ (z : ℝ)) (hQ : 1 ≤ Q) (hD : 1 ≤ D) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ( (Q : ℝ) * D ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B →
        C * (N : ℝ) / (Real.log N) ^ (11 : ℝ) + C * (N : ℝ) / (Real.log N) ^ (11 : ℝ)
          + 2 * Real.log N * (Real.log ((Q : ℝ) * D) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          ≤ (N : ℝ) / (Real.log N) ^ 10 →
        rosserRemainder (goldA1Sieve N P hP hPodd) (Q * D) ≤ (N : ℝ) / (Real.log N) ^ 10 ) := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, fun hlevel hclose => ?_⟩
  have hx2 : 2 ≤ N := by omega
  have hsplit := goldBVSum_le_split N P hP hPodd hPN hx (Q * (D : ℝ))
  have hbv1 := hbv N (N - 2) hx2 (by omega : N - 2 ≤ N)
  have hbv2 := hbv N (N / 2 - 1) hx2 (by omega : N / 2 - 1 ≤ N)
  have hS1 : (∑ d ∈ P.divisors, if (d : ℝ) < Q * (D : ℝ) then dispDisc (N - 2) d else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (dispDisc_filtered_le_Icc (N - 2) hlevel) hbv1
  have hS2 : (∑ d ∈ P.divisors, if (d : ℝ) < Q * (D : ℝ) then dispDisc (N / 2 - 1) d else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (dispDisc_filtered_le_Icc (N / 2 - 1) hlevel) hbv2
  have hb1 : (1 : ℝ) ≤ Q * (D : ℝ) := by
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    nlinarith [hQ, hD1]
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (goldA1Sieve N P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hPlow p hp,
        by exact_mod_cast hPz p hp, twinA1_hnu P p hp⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  have hlogQD : 0 ≤ Real.log (Q * (D : ℝ)) := Real.log_nonneg hb1
  have hconvfac : 0 ≤ 2 * Real.log N * (Real.log (Q * (D : ℝ)) / Real.log 3) := by
    have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  have hConv : (∑ d ∈ P.divisors, if (d : ℝ) < Q * (D : ℝ) then convTerm N d else 0)
      ≤ 2 * Real.log N * (Real.log (Q * (D : ℝ)) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε)) :=
    le_trans (convSum_le hP hPodd hx hb1) (mul_le_mul_of_nonneg_left hMbound hconvfac)
  linarith [hsplit, hS1, hS2, hConv, hclose]

/-! ## Part F — the crude `W`-lower (`W_goldA1_ge`) -/

/-- **`W_goldA1_ge`** — the crude `W`-lower for the Goldbach `A₁` sieve.  `W` reads only
`prodPrimes` and `nu`, both identical to the twin instance (`P`, `nuChen`), so the bound is the
twin's `W_twinA1_ge` after an `rfl` transfer: `W(z) ≥ exp(−35)/log z`. -/
theorem W_goldA1_ge {N P : ℕ} (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    {z : ℝ} (hz2 : 2 ≤ z) (hpz : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    Real.exp (-35) / Real.log z ≤ Salt.BrunLower.W (goldA1Sieve N P hP hPodd) := by
  have heq : Salt.BrunLower.W (goldA1Sieve N P hP hPodd)
      = Salt.BrunLower.W (twinA1Sieve N P hP hPodd) := rfl
  rw [heq]; exact W_twinA1_ge hP hPodd hz2 hpz

end Salt.Goldbach
