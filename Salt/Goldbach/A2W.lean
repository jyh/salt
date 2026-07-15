/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.TwinA2W
import Salt.Goldbach.Density
import Salt.Goldbach.Residue
import Salt.Goldbach.WeightWindow

/-!
# G-A2 (wave W2) — the Goldbach `A₂` weighted-sieve layer

Design: `docs/exploration/q1-design.md`, node **G-A2** (D3).  This file mirrors the twin
per-prime `A₂` W-layer (`Salt/Chen/TwinA2W.lean`) under the frozen Goldbach substitution

  `p ∣ (n + 2)  ↦  p ∣ (N − n)`,   `class d − 2  ↦  N mod d`,   `modulus P ↦ goldPs`.

## The load-bearing simplification (vs twin)

For Goldbach the paired value is the **reflection** `N − n` (bottom half `[2, N/2]` as `n`
sweeps `[N/2, N−2]`), not the translation `n + 2`.  Since every window point has `n ≤ N − 2`,
ℕ-subtraction is exact and

  `d ∣ (N − n)  ↔  n ≡ N (mod d)`   (`Nat.modEq_iff_dvd'`, guarded by `n ≤ N`).

So the divisibility condition on `N − n` becomes an AP-membership of `n` **directly** — the
weight stays `Λ(n)` with NO `−2` shift, and the fused class is `c ≡ a (Q)`, `c ≡ N (mod p·d)`.
The whole twin `apDiscW`/`dispDisc`/`convTerm`/BV machinery (class-parametric, N-agnostic) is
consumed VERBATIM at this class; the only Goldbach-shaped re-derivations are:

* `goldApW_class_iff` / `goldApSumW_eq_psiAP` — the class equivalence, carrying an explicit
  `y ≤ N` guard (the reflection needs `n ≤ N`; the twin translation never did);
* the reflection injectivity `N − · ` on the window (set-restricted, unlike the twin's global
  `· + 2`), paid in `goldA2SieveW_multSum`/`_siftedSum` with an explicit `N − (N − n) = n`;
* the class-coprimality obligation, discharged through `crt_class_coprimeG` (Residue.lean, the
  Goldbach mirror of `crt_class_coprime`) fed `Coprime (p·d) N` — needing `p ∤ N` (the A₂
  window prime is punctured, exactly as `goldPs` punctures its sifting primes).

## Deliverables

1. `goldA2SieveW` — the `twinA2SieveW` mirror (`p ∣ (N − n)` support, smooth totalMass).
2. `goldA2pW` + `gold_A2_per_prime_W` — the per-prime weighted count and its bound.  The
   abstract `twin_A2_per_prime_B` engine is consumed as-is (all instance hypotheses pass
   verbatim; only the sieve symbol and the `0 ≤ totalMass` witness are Goldbach-shaped).
3. `goldRosserRemainderW2_le_split` — the A₂-side remainder split, consuming
   `crt_class_coprimeG` (via `Coprime P N`) where the twin used `crt_class_coprime`.
4. `goldA2_hBVagg_W` — the aggregated BV discharge.  Residues are free (`r d := N % d`); the
   windowed-BV engine (`dispDiscW2_double_le_Icc`, `convSumW2_le`, `psi_BV_of_siegelWalfisz'`)
   is reused verbatim on the full prime window, the punctured remainder sum majorised into it
   by nonnegativity.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.LS Salt.BV Salt.Chen

namespace Salt.Goldbach

/-! ## Part A — the A₂-side CRT class (`a (Q)` fused with `N (mod M)`) -/

/-- **The Goldbach A₂ fused residue.**  The class `c ≡ a (mod Q)`, `c ≡ N (mod M)` — the AP
membership of `n` (the sieve filters `n ≡ a (Q)`) fused with the reflected divisibility
`M ∣ (N − n) ↔ n ≡ N (mod M)`.  Distinct from `crtClassG` (the switch side, `N − a (Q)`). -/
def crtClassGA (Q a M N : ℕ) (h : Nat.Coprime Q M) : ℕ :=
  (Nat.chineseRemainder h a N : ℕ)

lemma crtClassGA_mod_left (Q a M N : ℕ) (h : Nat.Coprime Q M) :
    crtClassGA Q a M N h % Q = a % Q :=
  (Nat.chineseRemainder h a N).2.1

lemma crtClassGA_mod_right (Q a M N : ℕ) (h : Nat.Coprime Q M) :
    crtClassGA Q a M N h % M = N % M :=
  (Nat.chineseRemainder h a N).2.2

/-! ## Part B — the reflected joint-class equivalence (the `y ≤ N` guard) -/

/-- **The joint-residue equivalence, Goldbach mirror** (`apW_class_iff` at `N − n`).  With
`n ≤ N` the reflected divisibility `d ∣ (N − n)` is `n ≡ N (mod d)`, so the AP class mod `Q`
together with `d ∣ (N − n)` is the single class `c` mod `Q·d`. -/
theorem goldApW_class_iff {Q a d c N : ℕ} (hQd : Nat.Coprime Q d)
    (hcQ : c % Q = a % Q) (hcd : c % d = N % d) {n : ℕ} (hn : n ≤ N) :
    (n % Q = a % Q ∧ d ∣ (N - n)) ↔ n % (Q * d) = c % (Q * d) := by
  have h1 : (n % Q = a % Q) ↔ (n % Q = c % Q) := by rw [hcQ]
  have h2 : (d ∣ (N - n)) ↔ (n % d = c % d) := by
    rw [← Nat.modEq_iff_dvd' hn]
    change n % d = N % d ↔ n % d = c % d
    rw [hcd]
  rw [h1, h2]
  exact Nat.modEq_and_modEq_iff_modEq_mul hQd

/-- The cumulative joint-residue window sum equals `psiAP` at `(Q·d, c)` (`apSumW_eq_psiAP`
mirror).  The `hyN : y ≤ N` guard is the price of the reflection: every counted `n ≤ y ≤ N`. -/
theorem goldApSumW_eq_psiAP {Q a d c N : ℕ} (hQd : Nat.Coprime Q d)
    (hcQ : c % Q = a % Q) (hcd : c % d = N % d) (y : ℕ) (hyN : y ≤ N) :
    (∑ n ∈ Finset.Icc 1 y, if n % Q = a % Q ∧ d ∣ (N - n) then vonMangoldt n else 0)
      = psiAP y (Q * d) c := by
  rw [psiAP, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro n hn
  exact goldApW_class_iff hQd hcQ hcd (le_trans (Finset.mem_Icc.mp hn).2 hyN)

/-! ## Part C — the per-prime W-instance (deliverable 1) -/

/-- **The per-prime AP-restricted Goldbach `A₂` `BoundingSieve`** (`twinA2SieveW` mirror).
Support = the reflected values `N − n` of the doubly-restricted window
`{n ∈ [N/2, N−2] : n ≡ a (Q), p ∣ (N − n)}`, weight `Λ(n)` at `N − n` (the reflection
`weights m = Λ(N − m)` reads back to `Λ(n)` since `n ≤ N`), density `ν = nuChen` (UNCHANGED;
N-independent — the singular-series invariance), sifting modulus `P`, smooth totalMass
`(Σ Λ)/(φ(Q)·(p − 1))`. -/
noncomputable def goldA2SieveW (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) : BoundingSieve where
  support := ((twinWindow N).filter (fun n => n % Q = a % Q ∧ p ∣ (N - n))).image (fun n => N - n)
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun m => vonMangoldt (N - m)
  weights_nonneg := fun _ => vonMangoldt_nonneg
  totalMass := (∑ n ∈ twinWindow N, vonMangoldt n) / ((Q.totient : ℝ) * ((p : ℝ) - 1))
  nu := nuChen
  nu_mult := nuChen_mult
  nu_pos_of_prime := fun _q hq _ => nuChen_pos hq
  nu_lt_one_of_prime := fun q hq hqd =>
    nuChen_lt_one hq (hPodd q (Nat.mem_primeFactors.mpr ⟨hq, hqd, hP.ne_zero⟩))

section FactsW2

@[simp] lemma goldA2SieveW_prodPrimes (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (goldA2SieveW Q a N P p hP hPodd).prodPrimes = P := rfl

@[simp] lemma goldA2SieveW_nu (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (goldA2SieveW Q a N P p hP hPodd).nu = nuChen := rfl

@[simp] lemma goldA2SieveW_totalMass (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (goldA2SieveW Q a N P p hP hPodd).totalMass
      = (∑ n ∈ twinWindow N, vonMangoldt n) / ((Q.totient : ℝ) * ((p : ℝ) - 1)) := rfl

/-- The reflection `N − ·` is injective on the window (every `n ≤ N − 2`) — unlike the twin's
global `· + 2`, so it is set-restricted. -/
lemma goldWindow_reflect_injOn (Q a N p : ℕ) :
    ∀ n₁ ∈ (twinWindow N).filter (fun n => n % Q = a % Q ∧ p ∣ (N - n)),
      ∀ n₂ ∈ (twinWindow N).filter (fun n => n % Q = a % Q ∧ p ∣ (N - n)),
        N - n₁ = N - n₂ → n₁ = n₂ := by
  intro n₁ h₁ n₂ h₂ heq
  rw [Finset.mem_filter, twinWindow, Finset.mem_Icc] at h₁ h₂
  omega

/-- **`multSum d`** = the window `Λ`-mass at the triple condition `n ≡ a (Q)`, `p ∣ (N − n)`,
`d ∣ (N − n)`. -/
lemma goldA2SieveW_multSum (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) (d : ℕ) :
    (goldA2SieveW Q a N P p hP hPodd).multSum d
      = ∑ n ∈ twinWindow N,
          if (n % Q = a % Q ∧ p ∣ (N - n)) ∧ d ∣ (N - n) then vonMangoldt n else 0 := by
  change (∑ m ∈ ((twinWindow N).filter (fun n => n % Q = a % Q ∧ p ∣ (N - n))).image
      (fun n => N - n), if d ∣ m then vonMangoldt (N - m) else 0) = _
  rw [Finset.sum_image (goldWindow_reflect_injOn Q a N p), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [twinWindow, Finset.mem_Icc] at hn
  have hred : N - (N - n) = n := by omega
  simp only [hred, ite_and]

/-- **`siftedSum`** = the per-prime AP-restricted `A₂` carrier: the `Λ`-weighted count of
`n ≡ a (Q)` in the window with `p ∣ (N − n)` and `N − n` coprime to `P`. -/
lemma goldA2SieveW_siftedSum (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    (goldA2SieveW Q a N P p hP hPodd).siftedSum
      = ∑ n ∈ twinWindow N,
          if (n % Q = a % Q ∧ p ∣ (N - n)) ∧ Nat.Coprime P (N - n)
          then vonMangoldt n else 0 := by
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ ((twinWindow N).filter (fun n => n % Q = a % Q ∧ p ∣ (N - n))).image
      (fun n => N - n), if Nat.Coprime P m then vonMangoldt (N - m) else 0) = _
  rw [Finset.sum_image (goldWindow_reflect_injOn Q a N p), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [twinWindow, Finset.mem_Icc] at hn
  have hred : N - (N - n) = n := by omega
  simp only [hred, ite_and]

/-- **`rem d`** — the sieve-equation remainder at the smooth per-prime totalMass. -/
lemma goldA2SieveW_rem (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) (d : ℕ) :
    (goldA2SieveW Q a N P p hP hPodd).rem d
      = (∑ n ∈ twinWindow N,
          if (n % Q = a % Q ∧ p ∣ (N - n)) ∧ d ∣ (N - n) then vonMangoldt n else 0)
        - nuChen d * ((∑ n ∈ twinWindow N, vonMangoldt n)
            / ((Q.totient : ℝ) * ((p : ℝ) - 1))) := by
  rw [BoundingSieve.rem, goldA2SieveW_multSum, goldA2SieveW_nu, goldA2SieveW_totalMass]

end FactsW2

/-! ## Part D — the `(Q·p·d)`-discrepancy identification -/

/-- The condition fusion at `gcd(p, d) = 1` (`twinA2W_cond_iff` mirror at `N − n`). -/
lemma goldA2W_cond_iff {Q a p d N : ℕ} (hpd : Nat.Coprime p d) (n : ℕ) :
    ((n % Q = a % Q ∧ p ∣ (N - n)) ∧ d ∣ (N - n))
      ↔ (n % Q = a % Q ∧ (p * d) ∣ (N - n)) := by
  constructor
  · rintro ⟨⟨hm, hpdvd⟩, hddvd⟩
    exact ⟨hm, hpd.mul_dvd_of_dvd_of_dvd hpdvd hddvd⟩
  · rintro ⟨hm, hpddvd⟩
    exact ⟨⟨hm, (dvd_mul_right p d).trans hpddvd⟩, (dvd_mul_left d p).trans hpddvd⟩

/-- **The per-prime W remainder identification** (`twinA2W_rem_eq` at the fused divisor `p·d`).
With the smooth totalMass, `rem d` is EXACTLY the two-endpoint difference of the
modulus-`(Q·p·d)` discrepancies at the class `c` — the reflected class `c ≡ N (mod p·d)`
replacing the twin's `p·d − 2`.  The totient algebra `φ(Q·p·d) = φ(Q)·(p−1)·φ(d)` is
verbatim. -/
theorem goldA2W_rem_eq (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) {d c : ℕ}
    (hQ1 : 1 ≤ Q) (hpp : p.Prime) (hd1 : 1 ≤ d) (hpd : Nat.Coprime p d)
    (hQpd : Nat.Coprime Q (p * d)) (hN : 4 ≤ N)
    (hcQ : c % Q = a % Q) (hcd : c % (p * d) = N % (p * d)) :
    (goldA2SieveW Q a N P p hP hPodd).rem d
      = apDiscW (N - 2) (Q * (p * d)) c - apDiscW (N / 2 - 1) (Q * (p * d)) c := by
  have hppos : 0 < p := hpp.pos
  have hpd1 : 1 ≤ p * d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [goldA2SieveW_rem]
  have hfuse : (∑ n ∈ twinWindow N,
        if (n % Q = a % Q ∧ p ∣ (N - n)) ∧ d ∣ (N - n) then vonMangoldt n else 0)
      = ∑ n ∈ twinWindow N,
        if n % Q = a % Q ∧ (p * d) ∣ (N - n) then vonMangoldt n else 0 :=
    Finset.sum_congr rfl (fun n _ => if_congr (goldA2W_cond_iff hpd n) rfl rfl)
  rw [hfuse, twinWindow,
    sum_Icc_window (fun n => if n % Q = a % Q ∧ (p * d) ∣ (N - n) then vonMangoldt n else 0)
      (N / 2) (N - 2) (by omega) (by omega),
    sum_Icc_window (fun n => vonMangoldt n) (N / 2) (N - 2) (by omega) (by omega)]
  rw [goldApSumW_eq_psiAP hQpd hcQ hcd (N - 2) (by omega),
    goldApSumW_eq_psiAP hQpd hcQ hcd (N / 2 - 1) (by omega)]
  have hpt : ∀ y, (∑ n ∈ Finset.Icc 1 y, vonMangoldt n) = psiTot y := fun _ => rfl
  rw [hpt (N - 2), hpt (N / 2 - 1), apDiscW, apDiscW, nuChen_apply]
  have hφ : ((Q * (p * d)).totient : ℝ)
      = (Q.totient : ℝ) * (((p : ℝ) - 1) * (d.totient : ℝ)) := by
    rw [Nat.totient_mul hQpd, Nat.totient_mul hpd, Nat.totient_prime hpp]
    push_cast [Nat.cast_sub hpp.one_lt.le]
    ring
  have hQt : (Q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < Q)).ne'
  have hp1ne : ((p : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    linarith
  have hdt : (d.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < d)).ne'
  rw [hφ]
  field_simp
  ring

/-- **The pointwise per-prime (39) bound** (`twinA2W_abs_rem_le` mirror): for a reduced class
`c` of `p·d`, `|rem d| ≤ dispDisc(N−2)(Q·p·d) + dispDisc(N/2−1)(Q·p·d) + convTerm N (Q·p·d)`.
The `dispDisc`/`convTerm`/`apDiscW_le` machinery is consumed VERBATIM. -/
theorem goldA2W_abs_rem_le (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) {d c : ℕ}
    (hQ1 : 1 ≤ Q) (hpp : p.Prime) (hd1 : 1 ≤ d) (hpd : Nat.Coprime p d)
    (hQpd : Nat.Coprime Q (p * d)) (hN : 4 ≤ N)
    (hcQ : c % Q = a % Q) (hcd : c % (p * d) = N % (p * d))
    (hccop : Nat.Coprime (Q * (p * d)) c) :
    |(goldA2SieveW Q a N P p hP hPodd).rem d|
      ≤ dispDisc (N - 2) (Q * (p * d)) + dispDisc (N / 2 - 1) (Q * (p * d))
        + convTerm N (Q * (p * d)) := by
  have hppos : 0 < p := hpp.pos
  have hQpd1 : 1 ≤ Q * (p * d) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by omega)))
  rw [goldA2W_rem_eq Q a N P p hP hPodd hQ1 hpp hd1 hpd hQpd hN hcQ hcd]
  have h1 := apDiscW_le (N - 2) (Q * (p * d)) c hQpd1 hccop (by omega)
  have h2 := apDiscW_le (N / 2 - 1) (Q * (p * d)) c hQpd1 hccop (by omega)
  have htri : |apDiscW (N - 2) (Q * (p * d)) c - apDiscW (N / 2 - 1) (Q * (p * d)) c|
      ≤ |apDiscW (N - 2) (Q * (p * d)) c| + |apDiscW (N / 2 - 1) (Q * (p * d)) c| :=
    abs_sub _ _
  unfold convTerm
  linarith [htri, h1, h2]

/-! ## Part E — the per-prime weighted count + supplier bound (deliverable 2) -/

/-- **The `p`-restricted Goldbach `Λ`-sum** (`A2pW` mirror at `N − n`).  The keep condition is
inlined (the Goldbach carrier keep `keepG` lives in a later wave); `p ∣ (N − n)` selects the
`p`-fibre.  Dominated by the instance's `siftedSum` (`goldA2pW_le_siftedSumW`). -/
noncomputable def goldA2pW (Q a N P p : ℕ) : ℝ :=
  ∑ n ∈ twinWindow N,
    vonMangoldt n
      * (if Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q then (1 : ℝ) else 0)
      * (if p ∣ (N - n) then 1 else 0)

/-- **The prime-restriction drop** (`A2pW_le_siftedSumW` mirror).  Dropping the `[n prime]`
restriction is free for an upper carrier (`Λ ≥ 0`). -/
lemma goldA2pW_le_siftedSumW (Q a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) :
    goldA2pW Q a N P p ≤ (goldA2SieveW Q a N P p hP hPodd).siftedSum := by
  rw [goldA2SieveW_siftedSum]
  unfold goldA2pW
  apply Finset.sum_le_sum
  intro n _
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q
  · rw [if_pos hk, mul_one]
    by_cases hpdvd : p ∣ (N - n)
    · rw [if_pos hpdvd, mul_one, if_pos ⟨⟨hk.2.2, hpdvd⟩, hk.2.1⟩]
    · rw [if_neg hpdvd, mul_zero]
      split_ifs <;> simp [vonMangoldt_nonneg]
  · rw [if_neg hk, mul_zero, zero_mul]
    split_ifs <;> simp [vonMangoldt_nonneg]

/-- **`gold_A2_per_prime_W`** — `twin_A2_per_prime_B` applied at the per-prime W-instance.  ALL
keystone hypotheses pass VERBATIM (`hzTop = hPz`; `hguard`/`hnu` = the landed
`twinA1_hguard`/`twinA1_hnu`, generic in the modulus; the H4C `h4` and FREEZE-V2 `hstepWPC`
slots threaded unchanged).  The only Goldbach-shaped step is `htm` (`0 ≤ totalMass`, the same
`/(φ(Q)·(p−1))` smooth shape). -/
theorem gold_A2_per_prime_W (Qm a N P p z Dlev : ℕ) (ε K Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q)
    (hPz : ∀ q ∈ P.primeFactors, q < z)
    (hPlow : ∀ q ∈ P.primeFactors, w0R ε ≤ (q : ℝ))
    (hp1 : 1 ≤ p) (hD2 : 2 ≤ Dlev) (hQlev : 1 ≤ Qlev)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hKe : K ≤ 1 + ε) (h249 : ε < 1 / 249)
    (hstepWPC : StepHypWPC (fun n => cfSharpB n ε) (fun _ => chSharpB ε) ε (tauSharpB ε))
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio z Dlev) :
    (goldA2SieveW Qm a N P p hP hPodd).siftedSum
      ≤ ((goldA2SieveW Qm a N P p hP hPodd).totalMass
            * Salt.BrunLower.W (goldA2SieveW Qm a N P p hP hPodd))
          * (Fchain (maxDepth (goldA2SieveW Qm a N P p hP hPodd)) (logRatio z Dlev)
              + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio z Dlev))
        + rosserRemainder (goldA2SieveW Qm a N P p hP hPodd) (Qlev * Dlev) := by
  set s := goldA2SieveW Qm a N P p hP hPodd with hs
  have htm : 0 ≤ s.totalMass := by
    rw [hs, goldA2SieveW_totalMass]
    apply div_nonneg (Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg)
    apply mul_nonneg (Nat.cast_nonneg _)
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    linarith
  exact twin_A2_per_prime_B s z Dlev ε K Qlev hD2 htm hQlev hPz
    (twinA1_hguard hε hw0 hPodd hPlow) (twinA1_hnu P) hε.le h249 hKe hstepWPC h4 hStop

/-! ## Part F — the A₂-side remainder split (deliverable 3) -/

/-- **The per-prime split** (`rosserRemainderW2_le_split` mirror).  The class-coprimality
obligation is discharged through `crt_class_coprimeG` (Residue.lean) fed `Coprime (p·d) N` —
where the twin used `crt_class_coprime` + `divisor_cases` oddness.  `Coprime d N` is free from
`Coprime P N` (`goldPs_coprime_N` at instantiation); `Coprime p N` needs `p ∤ N` (`hpN`), the
punctured A₂ window prime. -/
lemma goldRosserRemainderW2_le_split (Qm a N P p : ℕ) (hP : Squarefree P)
    (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q) (hQ1 : 1 ≤ Qm)
    (hQa : Nat.Coprime Qm a) (hQP : Nat.Coprime Qm P) (hQp : Nat.Coprime Qm p)
    (hpp : p.Prime) (_hp3 : 3 ≤ p) (hpP : Nat.Coprime p P)
    (hPcopN : Nat.Coprime P N) (hpN : ¬ p ∣ N) (hN : 4 ≤ N) (bound : ℝ) :
    rosserRemainder (goldA2SieveW Qm a N P p hP hPodd) bound
      ≤ (∑ d ∈ P.divisors, if (d : ℝ) < bound then dispDisc (N - 2) (Qm * (p * d)) else 0)
        + (∑ d ∈ P.divisors,
            if (d : ℝ) < bound then dispDisc (N / 2 - 1) (Qm * (p * d)) else 0)
        + (∑ d ∈ P.divisors, if (d : ℝ) < bound then convTerm N (Qm * (p * d)) else 0) := by
  rw [rosserRemainder]
  simp only [goldA2SieveW_prodPrimes]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hQd : Nat.Coprime Qm d :=
    Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hd) hQP
  have hpd : Nat.Coprime p d :=
    Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hd) hpP
  have hQpd : Nat.Coprime Qm (p * d) := Nat.Coprime.mul_right hQp hQd
  have hdN : Nat.Coprime d N :=
    Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hd) hPcopN
  have hpNc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpN
  have hpdN : Nat.Coprime (p * d) N := Nat.Coprime.mul_left hpNc hdN
  by_cases hlt : (d : ℝ) < bound
  · simp only [if_pos hlt]
    have hcQ := crtClassGA_mod_left Qm a (p * d) N hQpd
    have hcd := crtClassGA_mod_right Qm a (p * d) N hQpd
    have hccop : Nat.Coprime (Qm * (p * d)) (crtClassGA Qm a (p * d) N hQpd) :=
      crt_class_coprimeG hQa hpdN hcQ hcd
    exact goldA2W_abs_rem_le Qm a N P p hP hPodd hQ1 hpp hdpos hpd hQpd hN hcQ hcd hccop
  · simp only [if_neg hlt]
    have h1 := dispDisc_nonneg (N - 2) (Qm * (p * d))
    have h2 := dispDisc_nonneg (N / 2 - 1) (Qm * (p * d))
    have h3 := convTerm_nonneg N (Qm * (p * d))
    linarith

/-! ## Part G — the aggregated BV discharge (deliverable 4)

The remainder is summed over the **punctured** A₂ window
`{p prime ∈ [z, y] : p ∤ N}` — the same puncture `goldPs` applies to its sifting primes, and
the natural summation set (the `p ∣ N` fibres of the carrier are empty: `p ∣ N ∧ p ∣ (N − n)
⟹ p ∣ n`, impossible for the window prime `n > y ≥ p`).  The generic engines
(`dispDiscW2_double_le_Icc`, `convSumW2_le`, `psi_BV_of_siegelWalfisz'`) are class/N-agnostic
and run VERBATIM on the FULL prime window; the punctured remainder sum is majorised into them
by `dispDisc, convTerm ≥ 0`.  Residues enter only through the fused class `c ≡ N (mod p·d)`
(`goldRosserRemainderW2_le_split`) — the free-residue `r d := N % d` form; nothing twin-shaped
survives. -/

/-- **`goldA2_hBVagg_W`** — the aggregated Goldbach A₂ BV discharge (`twinA2_hBVagg_W` mirror).
Instantiating `psi_BV_of_siegelWalfisz'` at saving `11`, the SUM of the per-prime Rosser
remainders over the punctured window is `≤ N/(log N)^10`, given the two named GLU-2W rows (the
W2-LEVEL and W2-CLOSE rows, stated over the FULL prime window `1/(p−1)` mass — a looser, hence
downstream-identical, close row).  The extra hypothesis vs the twin is `hPcopN : Coprime P N`
(`goldPs_coprime_N` at instantiation). -/
theorem goldA2_hBVagg_W (Qm a N z y Dtot P : ℕ) (ε Qlev : ℝ)
    (hP : Squarefree P) (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q)
    (hPz : ∀ q ∈ P.primeFactors, q < z)
    (hPlow : ∀ q ∈ P.primeFactors, w0R ε ≤ (q : ℝ))
    (hPcopN : Nat.Coprime P N)
    (hN : 4 ≤ N) (hz3 : 3 ≤ z) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hwz : w0R ε ≤ (z : ℝ))
    (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P) (hQma : Nat.Coprime Qm a)
    (hQmPr : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, Nat.Coprime Qm p)
    (hQlev : 1 ≤ Qlev) (hD1 : 1 ≤ Dtot) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ( (Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B →
        C * (N : ℝ) / (Real.log N) ^ (11 : ℝ) + C * (N : ℝ) / (Real.log N) ^ (11 : ℝ)
          + 2 * Real.log N
              * ((Qm.primeFactors.card : ℝ)
                  + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
              * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1))
          ≤ (N : ℝ) / (Real.log N) ^ 10 →
        ∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N),
            rosserRemainder (goldA2SieveW Qm a N P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ))
          ≤ (N : ℝ) / (Real.log N) ^ 10 ) := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, fun hlevel hclose => ?_⟩
  classical
  have hN2 : 2 ≤ N := by omega
  have hQlev0 : (0 : ℝ) ≤ Qlev := by linarith
  have hBND1 : (1 : ℝ) ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
    have hD1R : (1 : ℝ) ≤ (Dtot : ℝ) := by exact_mod_cast hD1
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    nlinarith [hQlev, hD1R, hy0]
  -- the collapsed level bound: in-cut pairs satisfy p·d ≤ Qlev·(Dtot + y)
  have hpdB : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
      (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) →
      (p : ℝ) * (d : ℝ) ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
    intro p hpR d _hd hlt
    rw [Finset.mem_filter, Finset.mem_Icc] at hpR
    obtain ⟨⟨_hzp, hpy⟩, hpp⟩ := hpR
    have hppos : 0 < p := hpp.pos
    have hpposR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
    have hcd : p * cdiv Dtot p ≤ Dtot + p := by
      have h1 : (Dtot - 1) / p * p ≤ Dtot - 1 := Nat.div_mul_le_self _ _
      unfold cdiv
      calc p * ((Dtot - 1) / p + 1) = (Dtot - 1) / p * p + p := by ring
        _ ≤ Dtot + p := by omega
    have hcdR : (p : ℝ) * (cdiv Dtot p : ℝ) ≤ (Dtot : ℝ) + (p : ℝ) := by
      calc (p : ℝ) * (cdiv Dtot p : ℝ) = ((p * cdiv Dtot p : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((Dtot + p : ℕ) : ℝ) := by exact_mod_cast hcd
        _ = (Dtot : ℝ) + (p : ℝ) := by push_cast; ring
    have hpyR : (p : ℝ) ≤ (y : ℝ) := by exact_mod_cast hpy
    calc (p : ℝ) * (d : ℝ)
        ≤ (p : ℝ) * (Qlev * (cdiv Dtot p : ℝ)) :=
          mul_le_mul_of_nonneg_left hlt.le hpposR.le
      _ = Qlev * ((p : ℝ) * (cdiv Dtot p : ℝ)) := by ring
      _ ≤ Qlev * ((Dtot : ℝ) + (p : ℝ)) := mul_le_mul_of_nonneg_left hcdR hQlev0
      _ ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hQlev0
          linarith
  -- the modulus-level bound for the injection
  have hlev' : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
      (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) →
      ((Qm * (p * d) : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B := by
    intro p hpR d hd hlt
    have h1 := hpdB p hpR d hd hlt
    have hQm0 : (0 : ℝ) ≤ (Qm : ℝ) := Nat.cast_nonneg _
    calc ((Qm * (p * d) : ℕ) : ℝ) = (Qm : ℝ) * ((p : ℝ) * (d : ℝ)) := by push_cast; ring
      _ ≤ (Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) := mul_le_mul_of_nonneg_left h1 hQm0
      _ ≤ Real.sqrt (N : ℝ) / (Real.log N) ^ B := hlevel
  -- the punctured window is a subset of the full prime window
  have hGsub : (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N)
      ⊆ (Finset.Icc z y).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  -- per-prime split, summed over the punctured window
  have hsum : (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N),
        rosserRemainder (goldA2SieveW Qm a N P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ)))
      ≤ (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then dispDisc (N - 2) (Qm * (p * d)) else 0)
        + (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then dispDisc (N / 2 - 1) (Qm * (p * d)) else 0)
        + (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then convTerm N (Qm * (p * d)) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hpG
    have hpG' := hpG
    rw [Finset.mem_filter, Finset.mem_Icc] at hpG'
    obtain ⟨⟨hzp, _hpy⟩, hpp, hpN⟩ := hpG'
    have hp3 : 3 ≤ p := by omega
    have hpP : Nat.Coprime p P := (Nat.Prime.coprime_iff_not_dvd hpp).mpr (fun hpdvd =>
      absurd (hPz p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, hP.ne_zero⟩)) (by omega))
    exact goldRosserRemainderW2_le_split Qm a N P p hP hPodd hQm1 hQma hQmP
      (hQmPr p (hGsub hpG)) hpp hp3 hpP hPcopN hpN hN _
  -- the two dispDisc double sums: punctured ⊆ full, then the injection + unconditional BV
  have hbv1 := hbv N (N - 2) hN2 (by omega : N - 2 ≤ N)
  have hbv2 := hbv N (N / 2 - 1) hN2 (by omega : N / 2 - 1 ≤ N)
  have hnnD : ∀ (y' : ℕ) p, (0 : ℝ) ≤ ∑ d ∈ P.divisors,
      if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) then dispDisc y' (Qm * (p * d)) else 0 := by
    intro y' p
    apply Finset.sum_nonneg
    intro d _
    split_ifs
    · exact dispDisc_nonneg _ _
    · exact le_refl 0
  have hnnC : ∀ p, (0 : ℝ) ≤ ∑ d ∈ P.divisors,
      if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) then convTerm N (Qm * (p * d)) else 0 := by
    intro p
    apply Finset.sum_nonneg
    intro d _
    split_ifs
    · exact convTerm_nonneg _ _
    · exact le_refl 0
  have hS1 : (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
        then dispDisc (N - 2) (Qm * (p * d)) else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun p _ _ => hnnD (N - 2) p))
      (le_trans (dispDiscW2_double_le_Icc Qm (N - 2) hQm1 hP.ne_zero hPz hlev') hbv1)
  have hS2 : (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
        then dispDisc (N / 2 - 1) (Qm * (p * d)) else 0)
      ≤ C * N / (Real.log N) ^ (11 : ℝ) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun p _ _ => hnnD (N / 2 - 1) p))
      (le_trans (dispDiscW2_double_le_Icc Qm (N / 2 - 1) hQm1 hP.ne_zero hPz hlev') hbv2)
  -- the conversion double sum, then the `Σ 1/φ(d)` V-ratio bound (the A1W route)
  have hconv := convSumW2_le Qm hP hPodd hQm1 hPz hz3 hN hBND1 hpdB
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (twinA1SieveW Qm a N P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun q hq => ⟨Nat.prime_of_mem_primeFactors hq, hPlow q hq,
        by exact_mod_cast hPz q hq, twinA1_hnu P q hq⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1) := by
    apply Finset.sum_nonneg
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hK0 : 0 ≤ 2 * Real.log N
      * ((Qm.primeFactors.card : ℝ)
          + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3) := by
    have h0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlogB : 0 ≤ Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) := Real.log_nonneg hBND1
    have : 0 ≤ (Qm.primeFactors.card : ℝ)
        + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3 := by positivity
    exact mul_nonneg (by positivity) this
  have hconv2 : (∑ p ∈ (Finset.Icc z y).filter (fun p => p.Prime ∧ ¬ p ∣ N), ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) then convTerm N (Qm * (p * d)) else 0)
      ≤ 2 * Real.log N
          * ((Qm.primeFactors.card : ℝ)
              + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun p _ _ => hnnC p)) ?_
    refine le_trans hconv ?_
    apply mul_le_mul_of_nonneg_right _ hSp0
    exact mul_le_mul_of_nonneg_left hMbound hK0
  linarith [hsum, hS1, hS2, hconv2, hclose]

end Salt.Goldbach
