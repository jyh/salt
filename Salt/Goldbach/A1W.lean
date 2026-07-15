/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.A1

/-!
# G-A1 (W-layer) — the AP-restricted Goldbach `A₁` sieve

Design: `docs/exploration/q1-design.md`, node **G-A1** (wave W2), the W/AP-class half.  Mirrors
`Salt/Chen/TwinA1W.lean` (the W-trick repair of catch #65) under `n + 2 ↦ N − n`: the razor
carrier is restricted to the residue class `n ≡ a (mod Q)`, and the sifted `d`-class becomes
`N mod d` instead of `d − 2`.

## The `n`-side class

The ψ-ledger counts `n` (the `Λ`-weights sit at `n`), so the fused CRT class of the divisor `d`
is the **`n`-side** class

  `c ≡ a (mod Q)`  and  `c ≡ N (mod d)`

(from `n ≡ a (mod Q)` and `d ∣ N − n ⟺ n ≡ N (mod d)`).  Reducedness `gcd(c, Q·d) = 1` comes
from `Coprime Q a` (the witness) and `Coprime d N` (uniform on the punctured modulus) via
`crtClass_coprime_gold` (`Salt/Goldbach/Density.lean`, which consumes `coprime_mod_of_coprime`).

> NOTE (deviation from the node sketch, reported): this is the mirror of the twin's `crtClass`
> (fusing `a`, `d − 2`), **not** `Salt.Goldbach.crtClassG` (Residue.lean), which fuses `N − a`
> with `N` — that is the *switch/A₂* class (ledger at `N − n`).  The A₁ `n`-side needs `a` on
> the `Q`-side, so a local `crtClassA1` (`= chineseRemainder h a (N mod d)`) is defined here.

## Uniform-`d` (no `divisor_cases`)

`crtClass_coprime_gold` takes `Coprime d N` directly, so — exactly as in the base layer — the
twin's `d = 1 ∨ (3 ≤ d ∧ Odd d)` split dissolves; `goldRosserRemainderW_le_split` is a single
uniform branch.  Everything downstream of the split (`dispDiscW_filtered_le_Icc`, `convSumW_le`,
`sum_inv_totient_le_Winv`, `vratio_prod_le`, `psi_BV_of_siegelWalfisz'`) is reused verbatim.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.LS Salt.BV Salt.Chen

namespace Salt.Goldbach

/-! ## Part A — the AP-restricted `BoundingSieve` (`goldA1SieveW`) -/

/-- **The AP-restricted Goldbach `A₁` `BoundingSieve`** (W-trick).  Support = the reflected
values `N − n` of the AP-restricted window `{n ∈ [N/2, N−2] : n ≡ a (mod Q)}`, weight `Λ(n)` at
`N − n`, density `ν = nuChen` (UNCHANGED — the AP density cancels in the ν-ratio), sifting
modulus `P`, and the SMOOTH total mass `(Σ Λ(n))/φ(Q)`.  Mirrors `twinA1SieveW`. -/
noncomputable def goldA1SieveW (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) : BoundingSieve where
  support := ((twinWindow N).filter (fun n => n % Q = a % Q)).image (fun n => N - n)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun m => vonMangoldt (N - m)
  weights_nonneg := fun _ => vonMangoldt_nonneg
  totalMass := (∑ n ∈ twinWindow N, vonMangoldt n) / (Q.totient : ℝ)
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _p hp _ => nuChen_pos hp
  nu_lt_one_of_prime := fun p hp hpd =>
    nuChen_lt_one hp (hPodd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hP.ne_zero⟩))

section FactsW

@[simp] lemma goldA1SieveW_prodPrimes (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (goldA1SieveW Q a N P hP hPodd).prodPrimes = P := rfl

@[simp] lemma goldA1SieveW_nu (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (goldA1SieveW Q a N P hP hPodd).nu = nuChen := rfl

@[simp] lemma goldA1SieveW_totalMass (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (goldA1SieveW Q a N P hP hPodd).totalMass
      = (∑ n ∈ twinWindow N, vonMangoldt n) / (Q.totient : ℝ) := rfl

/-- **`multSum d` = the window `Λ`-mass at the joint residue** `n ≡ a (mod Q)`, `d ∣ N − n`. -/
lemma goldA1SieveW_multSum (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (d : ℕ) :
    (goldA1SieveW Q a N P hP hPodd).multSum d
      = ∑ n ∈ twinWindow N, if n % Q = a % Q ∧ d ∣ (N - n) then vonMangoldt n else 0 := by
  change (∑ m ∈ ((twinWindow N).filter (fun n => n % Q = a % Q)).image (fun n => N - n),
      if d ∣ m then vonMangoldt (N - m) else 0) = _
  rw [Finset.sum_image (fun a' ha' b' hb' h => by
      rw [Finset.mem_coe, Finset.mem_filter, twinWindow, Finset.mem_Icc] at ha' hb'
      have h' : N - a' = N - b' := h
      omega), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [twinWindow, Finset.mem_Icc] at hn
  simp only [show N - (N - n) = n from by omega, ite_and]

/-- **`siftedSum` = the AP-restricted Goldbach `A₁` carrier.** -/
lemma goldA1SieveW_siftedSum (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    (goldA1SieveW Q a N P hP hPodd).siftedSum
      = ∑ n ∈ twinWindow N,
          if n % Q = a % Q ∧ Nat.Coprime P (N - n) then vonMangoldt n else 0 := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ ((twinWindow N).filter (fun n => n % Q = a % Q)).image (fun n => N - n),
      if Nat.Coprime P m then vonMangoldt (N - m) else 0) = _
  rw [Finset.sum_image (fun a' ha' b' hb' h => by
      rw [Finset.mem_coe, Finset.mem_filter, twinWindow, Finset.mem_Icc] at ha' hb'
      have h' : N - a' = N - b' := h
      omega), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [twinWindow, Finset.mem_Icc] at hn
  simp only [show N - (N - n) = n from by omega, ite_and]

/-- **`rem d`** — the sieve-equation remainder at the smooth totalMass. -/
lemma goldA1SieveW_rem (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (d : ℕ) :
    (goldA1SieveW Q a N P hP hPodd).rem d
      = (∑ n ∈ twinWindow N, if n % Q = a % Q ∧ d ∣ (N - n) then vonMangoldt n else 0)
        - nuChen d * ((∑ n ∈ twinWindow N, vonMangoldt n) / (Q.totient : ℝ)) := by
  rw [BoundingSieve.rem, goldA1SieveW_multSum, goldA1SieveW_nu, goldA1SieveW_totalMass]

end FactsW

/-! ## Part B — the CRT class `c(d)` and the `Q·d`-discrepancy identification -/

/-- **The Goldbach `A₁` `n`-side CRT class** `c ≡ a (mod Q)`, `c ≡ N (mod d)` (`gcd(Q, d) = 1`).
Mirror of the twin `crtClass` (`= chineseRemainder h a (d − 2)`) with the sifted residue
`d − 2 ↦ N mod d`. -/
def crtClassA1 (Q a d N : ℕ) (h : Nat.Coprime Q d) : ℕ :=
  (Nat.chineseRemainder h a (N % d) : ℕ)

lemma crtClassA1_mod_left (Q a d N : ℕ) (h : Nat.Coprime Q d) :
    crtClassA1 Q a d N h % Q = a % Q :=
  (Nat.chineseRemainder h a (N % d)).2.1

lemma crtClassA1_mod_right (Q a d N : ℕ) (h : Nat.Coprime Q d) :
    crtClassA1 Q a d N h % d = (N % d) % d :=
  (Nat.chineseRemainder h a (N % d)).2.2

/-- **The joint-residue equivalence.**  Membership in the AP class mod `Q` together with
`d ∣ N − n` is exactly membership in the single class `c` mod `Q·d` (CRT at `gcd(Q,d) = 1`), for
`n ≤ N` (the reflection is honest below `N`). -/
theorem apW_class_iff {Q a d c N n : ℕ} (hn : n ≤ N) (hQd : Nat.Coprime Q d)
    (hcQ : c % Q = a % Q) (hcd : c % d = (N % d) % d) :
    (n % Q = a % Q ∧ d ∣ (N - n)) ↔ n % (Q * d) = c % (Q * d) := by
  have h1 : (n % Q = a % Q) ↔ (n % Q = c % Q) := by rw [hcQ]
  have h2 : (d ∣ (N - n)) ↔ (n % d = c % d) := by rw [dvd_sub_iff hn, hcd]
  rw [h1, h2]
  exact Nat.modEq_and_modEq_iff_modEq_mul hQd

/-- The cumulative joint-residue window sum equals `psiAP` at `(Q·d, c)` (for `y ≤ N`). -/
theorem apSumW_eq_psiAP {Q a d c N : ℕ} (hQd : Nat.Coprime Q d)
    (hcQ : c % Q = a % Q) (hcd : c % d = (N % d) % d) (y : ℕ) (hy : y ≤ N) :
    (∑ n ∈ Finset.Icc 1 y, if n % Q = a % Q ∧ d ∣ (N - n) then vonMangoldt n else 0)
      = psiAP y (Q * d) c := by
  rw [psiAP, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_Icc] at hn
  exact apW_class_iff (le_trans hn.2 hy) hQd hcQ hcd

/-- **The W remainder identification** (`twinA1W_rem_eq` mirrored at `(Q·d, c(d))`).  With the
smooth `totalMass`, `rem d` is exactly the two-endpoint difference of the modulus-`Q·d`
discrepancies at the class `c`: `φ(Qd) = φ(Q)φ(d)` by coprimality. -/
theorem goldA1W_rem_eq (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) {d c : ℕ}
    (hQ1 : 1 ≤ Q) (hd1 : 1 ≤ d) (hQd : Nat.Coprime Q d) (hN : 4 ≤ N)
    (hcQ : c % Q = a % Q) (hcd : c % d = (N % d) % d) :
    (goldA1SieveW Q a N P hP hPodd).rem d
      = apDiscW (N - 2) (Q * d) c - apDiscW (N / 2 - 1) (Q * d) c := by
  rw [goldA1SieveW_rem, twinWindow,
    sum_Icc_window (fun n => if n % Q = a % Q ∧ d ∣ (N - n) then vonMangoldt n else 0)
      (N / 2) (N - 2) (by omega) (by omega),
    sum_Icc_window (fun n => vonMangoldt n) (N / 2) (N - 2) (by omega) (by omega)]
  rw [apSumW_eq_psiAP hQd hcQ hcd (N - 2) (by omega),
    apSumW_eq_psiAP hQd hcQ hcd (N / 2 - 1) (by omega)]
  have hpt : ∀ y, (∑ n ∈ Finset.Icc 1 y, vonMangoldt n) = psiTot y := fun _ => rfl
  rw [hpt (N - 2), hpt (N / 2 - 1), apDiscW, apDiscW, nuChen_apply]
  have hφ : ((Q * d).totient : ℝ) = (Q.totient : ℝ) * (d.totient : ℝ) := by
    rw [Nat.totient_mul hQd]; push_cast; ring
  have hQt : (Q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < Q)).ne'
  have hdt : (d.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < d)).ne'
  rw [hφ]
  field_simp
  ring

/-- **The pointwise W (39) bound** (`twinA1W_abs_rem_le` mirrored): for a reduced class `c` of
`d`, `|rem d| ≤ dispDisc (N−2) (Qd) + dispDisc (N/2−1) (Qd) + convTerm N (Qd)`. -/
theorem goldA1W_abs_rem_le (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) {d c : ℕ}
    (hQ1 : 1 ≤ Q) (hd1 : 1 ≤ d) (hQd : Nat.Coprime Q d) (hN : 4 ≤ N)
    (hcQ : c % Q = a % Q) (hcd : c % d = (N % d) % d)
    (hccop : Nat.Coprime (Q * d) c) :
    |(goldA1SieveW Q a N P hP hPodd).rem d|
      ≤ dispDisc (N - 2) (Q * d) + dispDisc (N / 2 - 1) (Q * d) + convTerm N (Q * d) := by
  have hQd1 : 1 ≤ Q * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [goldA1W_rem_eq Q a N P hP hPodd hQ1 hd1 hQd hN hcQ hcd]
  have h1 := apDiscW_le (N - 2) (Q * d) c hQd1 hccop (by omega)
  have h2 := apDiscW_le (N / 2 - 1) (Q * d) c hQd1 hccop (by omega)
  have htri : |apDiscW (N - 2) (Q * d) c - apDiscW (N / 2 - 1) (Q * d) c|
      ≤ |apDiscW (N - 2) (Q * d) c| + |apDiscW (N / 2 - 1) (Q * d) c| := abs_sub _ _
  unfold convTerm
  linarith [htri, h1, h2]

/-! ## Part C — the supplier mirrors (`gold_A1_lower_W`, `gold_A1_lower_B_W`)

The generic keystones are support-agnostic; only the instance facts re-prove
(`siftedSum` rfl-level, `htm` the smooth mass `≥ 0`, `hnu`/`hguard` delegating to the landed
`twinA1_hnu`/`twinA1_hguard`). -/

/-- **`gold_A1_lower_W` — the AP-restricted Goldbach `A₁` endpoint** (`twin_A1_lower_W` mirror). -/
theorem gold_A1_lower_W (Qm a N z D P : ℕ) (ε K C₂ Qlev : ℝ) (tau : ℕ → ℝ)
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
    (htau : ∑ n ∈ (Finset.range (maxDepth (goldA1SieveW Qm a N P hP hPodd) + 1)).filter
        (fun n => Even n), tau n ≤ C₂)
    (hQlev : 1 ≤ Qlev)
    (hBV : rosserRemainder (goldA1SieveW Qm a N P hP hPodd) (Qlev * D)
        ≤ (N : ℝ) / (Real.log N) ^ 10) :
    (goldA1SieveW Qm a N P hP hPodd).totalMass *
        (Salt.BrunLower.W (goldA1SieveW Qm a N P hP hPodd) *
          (fchain (maxDepth (goldA1SieveW Qm a N P hP hPodd)) (logRatio z D)
            - ε * C₂ * Real.exp 2 * hBJS (logRatio z D)))
      - (N : ℝ) / (Real.log N) ^ 10
    ≤ ∑ n ∈ twinWindow N,
        if n % Qm = a % Qm ∧ Nat.Coprime P (N - n) then vonMangoldt n else 0 := by
  set s := goldA1SieveW Qm a N P hP hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < z := hPz
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := twinA1_hnu P
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    twinA1_hguard hε hw0 hPodd hPlow
  have htm : 0 ≤ s.totalMass := by
    rw [hs, goldA1SieveW_totalMass]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg) (Nat.cast_nonneg _)
  have hlevel := hlevel_w_lower s z D ε K tau hD hzTop hguard hnu hε.le hKe htau1 hτ0 hτrec
    h4 hStop
  have hassembled := linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hzTop htm
    (logRatio z D) ε C₂ Qlev hQlev hε.le tau hlevel htau
  rw [hs, goldA1SieveW_siftedSum] at hassembled
  linarith [hassembled, hBV]

/-- **`gold_A1_lower_B_W` — the sharp (cB) AP-restricted Goldbach `A₁` lower bound** (the
`twin_A1_lower_B_W` mirror).  Numeric τ-layer discharged at the FREEZE-V2 coefficients; single
per-step slot `hstepWPC` + contraction gate `ε < 1/249`; slack constant `CsharpB ε`. -/
theorem gold_A1_lower_B_W (Qm a N z D P : ℕ) (ε K Qlev : ℝ)
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
    (hQlev : 1 ≤ Qlev)
    (hBV : rosserRemainder (goldA1SieveW Qm a N P hP hPodd) (Qlev * D)
        ≤ (N : ℝ) / (Real.log N) ^ 10) :
    (goldA1SieveW Qm a N P hP hPodd).totalMass *
        (Salt.BrunLower.W (goldA1SieveW Qm a N P hP hPodd) *
          (fchain (maxDepth (goldA1SieveW Qm a N P hP hPodd)) (logRatio z D)
            - ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z D)))
      - (N : ℝ) / (Real.log N) ^ 10
    ≤ ∑ n ∈ twinWindow N,
        if n % Qm = a % Qm ∧ Nat.Coprime P (N - n) then vonMangoldt n else 0 := by
  set s := goldA1SieveW Qm a N P hP hPodd with hs
  have hzTop : ∀ q ∈ s.prodPrimes.primeFactors, q < z := hPz
  have hnu : ∀ q ∈ s.prodPrimes.primeFactors, s.nu q ≤ 1 / ((q : ℝ) - 1) := twinA1_hnu P
  have hguard : ∀ q ∈ s.prodPrimes.primeFactors,
      3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε) :=
    twinA1_hguard hε hw0 hPodd hPlow
  have htm : 0 ≤ s.totalMass := by
    rw [hs, goldA1SieveW_totalMass]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg) (Nat.cast_nonneg _)
  have hlevel := hlevel_wpc_lower s z D ε K (fun n => cfSharpB n ε) (fun _ => chSharpB ε)
    (tauSharpB ε) hD hzTop hguard hnu hε.le hKe (tauSharpB_one ε) (tauSharpB_nonneg hε.le)
    hstepWPC (fun n => tauSharpB_hτrec n) h4 hStop
  have hassembled := linear_sieve_lower_rosser_assembled_final s D z hz2 hzD hzTop htm
    (logRatio z D) ε (CsharpB ε) Qlev hQlev hε.le (tauSharpB ε) hlevel
    (tauSharpB_sum_even_le hε.le hε49B (maxDepth s + 1))
  rw [hs, goldA1SieveW_siftedSum] at hassembled
  linarith [hassembled, hBV]

/-! ## Part D — the W BV discharge (`goldRosserRemainderW_le_split`, `goldBVSum_W`)

The a-fortiori route through `d ↦ Q·d`: each `|rem d|` sits at modulus `Q·d`; the injection
lands the family inside the BV index range under the W-LEVEL row, and `dispDisc ≥ 0` pays for the
over-count.  `dispDiscW_filtered_le_Icc` and `convSumW_le` are reused verbatim (both generic in
`x`, `P`, `Q`). -/

/-- **The W split.**  The Rosser remainder of the AP-restricted sieve is bounded termwise — via
`goldA1W_abs_rem_le` at the class `crtClassA1 Q a d N` (UNIFORM in `d ∣ P`, no `divisor_cases`) —
by the two endpoint `dispDisc` sums at moduli `Q·d` plus the conversion sum. -/
lemma goldRosserRemainderW_le_split (Q a N P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) (hQ1 : 1 ≤ Q)
    (hQa : Nat.Coprime Q a) (hQP : Nat.Coprime Q P) (hPN : Nat.Coprime P N) (hN : 4 ≤ N)
    (bound : ℝ) :
    rosserRemainder (goldA1SieveW Q a N P hP hPodd) bound
      ≤ (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (N - 2) (Q * d) else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (N / 2 - 1) (Q * d) else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then convTerm N (Q * d) else 0) := by
  rw [rosserRemainder]
  simp only [goldA1SieveW_prodPrimes]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hQd : Nat.Coprime Q d :=
    Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hd) hQP
  have hdN : Nat.Coprime d N :=
    Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd) hPN
  by_cases hlt : (d : ℝ) < bound
  · simp only [if_pos hlt]
    have hcQ := crtClassA1_mod_left Q a d N hQd
    have hcd := crtClassA1_mod_right Q a d N hQd
    have hccop : Nat.Coprime (Q * d) (crtClassA1 Q a d N hQd) :=
      crtClass_coprime_gold hQa hdN hcQ hcd
    exact goldA1W_abs_rem_le Q a N P hP hPodd hQ1 hdpos hQd hN hcQ hcd hccop
  · simp only [if_neg hlt]
    have h1 := dispDisc_nonneg (N - 2) (Q * d)
    have h2 := dispDisc_nonneg (N / 2 - 1) (Q * d)
    have h3 := convTerm_nonneg N (Q * d)
    linarith

/-- **G-A1 W-layer — the W BV discharge `goldBVSum_W`** (`twinA1_hBV_W` mirrored through the
`d ↦ Q·d` a-fortiori).  Instantiating `psi_BV_of_siegelWalfisz' siegelWalfisz_holds` at saving
`11`, the Rosser remainder of the AP-restricted `A₁` sieve is `≤ N/(log N)^10`, given the two
named GLU-2W rows (the W-LEVEL and W-CLOSE rows).  `hQmP`/`hQma` are the disjoint-support and
witness coprimalities; `hPN` is the punctured `Coprime P N`. -/
theorem goldBVSum_W (Qm a N z D P : ℕ) (ε Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPz : ∀ p ∈ P.primeFactors, p < z)
    (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 4 ≤ N) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
    (hwz : w0R ε ≤ (z : ℝ)) (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P)
    (hQma : Nat.Coprime Qm a) (hPN : Nat.Coprime P N) (hQlev : 1 ≤ Qlev) (hD : 1 ≤ D) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ( (Qm : ℝ) * (Qlev * D) ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B →
        C * (N : ℝ) / (Real.log N) ^ (11 : ℝ) + C * (N : ℝ) / (Real.log N) ^ (11 : ℝ)
          + 2 * Real.log N
              * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * D) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          ≤ (N : ℝ) / (Real.log N) ^ 10 →
        rosserRemainder (goldA1SieveW Qm a N P hP hPodd) (Qlev * D)
          ≤ (N : ℝ) / (Real.log N) ^ 10 ) := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, fun hlevel hclose => ?_⟩
  have hx2 : 2 ≤ N := by omega
  have hsplit := goldRosserRemainderW_le_split Qm a N P hP hPodd hQm1 hQma hQmP hPN hx
    (Qlev * (D : ℝ))
  have hbv1 := hbv N (N - 2) hx2 (by omega : N - 2 ≤ N)
  have hbv2 := hbv N (N / 2 - 1) hx2 (by omega : N / 2 - 1 ≤ N)
  have hS1 : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then dispDisc (N - 2) (Qm * d) else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (dispDiscW_filtered_le_Icc Qm (N - 2) hQm1 hlevel) hbv1
  have hS2 : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then dispDisc (N / 2 - 1) (Qm * d) else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (dispDiscW_filtered_le_Icc Qm (N / 2 - 1) hQm1 hlevel) hbv2
  have hb1 : (1 : ℝ) ≤ Qlev * (D : ℝ) := by
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    nlinarith [hQlev, hD1]
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (goldA1SieveW Qm a N P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hPlow p hp,
        by exact_mod_cast hPz p hp, twinA1_hnu P p hp⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  have hlogQD : 0 ≤ Real.log (Qlev * (D : ℝ)) := Real.log_nonneg hb1
  have hconvfac : 0 ≤ 2 * Real.log N
      * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3) := by
    have h0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hq : 0 ≤ Real.log (Qlev * (D : ℝ)) / Real.log 3 := div_nonneg hlogQD h3.le
    have hω : (0 : ℝ) ≤ (Qm.primeFactors.card : ℝ) := by positivity
    have hsum : 0 ≤ (Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3 := by
      linarith
    exact mul_nonneg (by positivity) hsum
  have hConv : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then convTerm N (Qm * d) else 0)
      ≤ 2 * Real.log N
          * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε)) :=
    le_trans (convSumW_le Qm hP hPodd hQm1 hQmP hx hb1)
      (mul_le_mul_of_nonneg_left hMbound hconvfac)
  linarith [hsplit, hS1, hS2, hConv, hclose]

end Salt.Goldbach
