/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Asm3
import Salt.Goldbach.Omega

/-!
# G-ASM §4 — the Goldbach W-carrier razor chain (`goldbach_of_hypotheses_W`)

The `Salt.Chen.Assembly` Parts H–K mirrored at the reflected value `N − n`:

* the keep indicator `keepG` and the five carriers (the A₂ carrier is the landed
  `goldOmegaPrimeSum`, which inlines the same keep);
* the split sifting bridge `factors_ge_z_of_sift_G` — the mod-`Q` transfer runs through
  `N − a` (the reflected residue), so the coprimality row is `Coprime Q (N − a)`;
* the razor reduction (Tao's Lemma 11 at `m := N − n`, via the generic
  `chen_weight_struct`/`chen_weight_le_indicator`);
* the prime-power strip bound (the reflected window count `#{n : d ∣ N − n} ≤ N/d`);
* the positivity, the survivor (`IsP2 2 (N − n)` via `isP2_mono`), and the headline
  consumer `goldbach_of_hypotheses_W` — the `chen_of_hypotheses_W` mirror in the
  `∃ N₀, ∀ N ≥ N₀, Even N → …` form of the frozen D0 statement.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset Salt.Chen ArithmeticFunction

namespace Salt.Goldbach

/-! ## Part A — the keep indicator and the five carriers -/

/-- The Goldbach W-keep indicator `1_{n prime ∧ (P, N−n) = 1 ∧ n ≡ a (mod Q)}`.  Matches the
inlined keep of `goldOmegaPrimeSum` character-for-character. -/
noncomputable def keepG (Q a P N n : ℕ) : ℝ :=
  if Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q then 1 else 0

lemma keepG_nonneg (Q a P N n : ℕ) : 0 ≤ keepG Q a P N n := by
  unfold keepG; split_ifs <;> norm_num

lemma keepG_eq_one_iff {Q a P N n : ℕ} :
    keepG Q a P N n = 1 ↔ Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q := by
  unfold keepG
  by_cases hh : Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q
  · rw [if_pos hh]; exact ⟨fun _ => hh, fun _ => rfl⟩
  · rw [if_neg hh]; exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hh⟩

/-- The Goldbach W-restricted A₁ carrier (the sifted, AP-restricted window `Λ`-mass). -/
noncomputable def goldA1PrimeSumW (Q a N P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n

/-- The Goldbach W-restricted A₃ switch carrier `Σ Λ(n)·keepG·1_T(N − n)`. -/
noncomputable def goldTriplePrimeSumW (Q a N P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n * tripleT y (N - n)

/-- The Goldbach W-restricted prime-power strip carrier. -/
noncomputable def goldStripPrimeSumW (Q a N P y : ℕ) : ℝ :=
  ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n * (sqStrip y (N - n) : ℝ)

/-- The Goldbach W-restricted P₂ carrier — the quantity the razor lower-bounds. -/
noncomputable def goldP2PrimeSumW (Q a N z P : ℕ) : ℝ :=
  ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n * p2Ind z (N - n)

/-- The landed A₂ carrier `goldOmegaPrimeSum` is the `keepG` carrier (definitional). -/
lemma goldOmegaPrimeSum_eq_keepG (Q a N P y : ℕ) :
    goldOmegaPrimeSum Q a N P y
      = ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n * (omegaLe y (N - n) : ℝ) := rfl

/-! ## Part B — the split sifting bridge at the reflected value -/

/-- **The Goldbach split sifting bridge (punctured).**  At a kept point — `n` PRIME,
`(P, N−n) = 1`, `n ≡ a (mod Q)` — every prime factor of `N − n` is `≥ z`.  The small range
`[2, w')` runs through the mod-`Q` transfer to the REFLECTED residue: `p ∣ Q` and
`n ≡ a (mod p)` put `p ∣ N − a` (via `Nat.ModEq`), against `Coprime Q (N − a)`.  The sieve
range `[w', z)` is PUNCTURED (`goldOpP` omits the primes dividing `N`): a factor `p ∣ N`
with `p ∣ N − n` forces `p ∣ n`, hence `p = n ≥ z` — impossible below `z`. -/
theorem factors_ge_z_of_sift_G {Q a P w' z N n : ℕ} (haN : a ≤ N) (hnN : n ≤ N)
    (hnp : n.Prime) (hzn : z ≤ n)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P)
    (hQNa : Nat.Coprime Q (N - a))
    (hcop : Nat.Coprime P (N - n)) (hmod : n % Q = a % Q) :
    ∀ p ∈ (N - n).primeFactors, z ≤ p := by
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ (N - n) := Nat.dvd_of_mem_primeFactors hp
  by_contra hlt
  rw [not_le] at hlt
  by_cases hw : p < w'
  · -- small range: p ∣ Q; transfer n ≡ a (mod p) into p ∣ N − a
    have hpQ : p ∣ Q := hQfull p hpp hw
    have hnN' : n ≡ N [MOD p] := (Nat.modEq_iff_dvd' hnN).mpr hpd
    have hna : n ≡ a [MOD p] := Nat.ModEq.of_dvd hpQ hmod
    have haN' : a ≡ N [MOD p] := hna.symm.trans hnN'
    have hpNa : p ∣ (N - a) := (Nat.modEq_iff_dvd' haN).mp haN'
    have hdvd1 : p ∣ Nat.gcd Q (N - a) := Nat.dvd_gcd hpQ hpNa
    rw [Nat.Coprime] at hQNa
    rw [hQNa] at hdvd1
    exact hpp.ne_one (Nat.dvd_one.mp hdvd1)
  · -- sieve range [w', z): punctured split on p ∣ N
    rw [not_lt] at hw
    by_cases hpN : p ∣ N
    · -- p ∣ N and p ∣ N − n force p ∣ n = prime, so p = n ≥ z: impossible below z
      have hpn : p ∣ n := by
        have hsub : N - (N - n) = n := by omega
        have := Nat.dvd_sub hpN hpd
        rwa [hsub] at this
      have hpeq : p = n := (Nat.prime_dvd_prime_iff_eq hpp hnp).mp hpn
      omega
    · have hpP : p ∣ P := hPfull' p hpp hw hlt hpN
      have hdvd1 : p ∣ Nat.gcd P (N - n) := Nat.dvd_gcd hpP hpd
      rw [Nat.Coprime] at hcop
      rw [hcop] at hdvd1
      exact hpp.ne_one (Nat.dvd_one.mp hdvd1)

/-! ## Part C — the razor reduction (Tao Lemma 11 at `m := N − n`) -/

/-- **The Goldbach W-razor reduction.**  `razor_reduction_W` at the reflected value:
Chen's weight is dominated by the P₂ indicator at every AP-restricted kept point of the
window, so the four carriers fold. -/
theorem gold_razor_reduction_W {N z P y Q a w' : ℕ} (hN2 : 2 ≤ N) (hyx : N < (y + 1) ^ 3)
    (haN : a ≤ N) (hzN : 2 * z ≤ N)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P)
    (hQNa : Nat.Coprime Q (N - a)) :
    goldA1PrimeSumW Q a N P - goldOmegaPrimeSum Q a N P y / 2
      - goldTriplePrimeSumW Q a N P y / 2 - goldStripPrimeSumW Q a N P y / 2
    ≤ goldP2PrimeSumW Q a N z P := by
  have hpt : ∀ n ∈ twinWindow N,
      vonMangoldt n * keepG Q a P N n * chenWeight y (N - n)
        ≤ vonMangoldt n * keepG Q a P N n * p2Ind z (N - n) := by
    intro n hn
    by_cases hk : Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q
    · rw [twinWindow, Finset.mem_Icc] at hn
      have hnN : n ≤ N := by omega
      have hzn : z ≤ n := by omega
      have hcop := factors_ge_z_of_sift_G haN hnN hk.1 hzn hQfull hPfull' hQNa hk.2.1 hk.2.2
      have hn2 : 2 ≤ N - n := by omega
      have hmy : N - n < (y + 1) ^ 3 := lt_of_le_of_lt (by omega) hyx
      have hstruct : ¬ IsP2 z (N - n) →
          2 ≤ (omegaLe y (N - n) : ℝ) + tripleT y (N - n) + (sqStrip y (N - n) : ℝ) :=
        fun hnp2 => chen_weight_struct hn2 hcop hmy hnp2
      have hle := chen_weight_le_indicator hstruct
      exact mul_le_mul_of_nonneg_left hle
        (mul_nonneg vonMangoldt_nonneg (keepG_nonneg Q a P N n))
    · have hkeep0 : keepG Q a P N n = 0 := by unfold keepG; rw [if_neg hk]
      simp [hkeep0]
  have hsum := Finset.sum_le_sum hpt
  have hRHS : ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n * p2Ind z (N - n)
      = goldP2PrimeSumW Q a N z P := rfl
  have hterm : ∀ n, vonMangoldt n * keepG Q a P N n * chenWeight y (N - n)
      = vonMangoldt n * keepG Q a P N n
        - vonMangoldt n * keepG Q a P N n * (omegaLe y (N - n) : ℝ) / 2
        - vonMangoldt n * keepG Q a P N n * tripleT y (N - n) / 2
        - vonMangoldt n * keepG Q a P N n * (sqStrip y (N - n) : ℝ) / 2 := by
    intro n; rw [chenWeight]; ring
  rw [Finset.sum_congr rfl (fun n _ => hterm n)] at hsum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_div] at hsum
  rw [hRHS] at hsum
  exact hsum

/-! ## Part D — the prime-power strip bound at the reflected window -/

/-- The reflected per-divisor window count: `#{n ∈ twinWindow N : d ∣ N − n} ≤ N/d`, via the
injection `n ↦ N − n` into the multiples of `d` in `(0, N]`. -/
theorem gold_card_window_dvd_le {N d : ℕ} (hN : 2 ≤ N) :
    (((twinWindow N).filter (fun n => d ∣ (N - n))).card : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
  have hcard : ((twinWindow N).filter (fun n => d ∣ (N - n))).card
      ≤ ((Finset.Ioc 0 N).filter (fun m => d ∣ m)).card := by
    apply Finset.card_le_card_of_injOn (fun n => N - n)
    · intro n hn
      rw [Finset.mem_coe, Finset.mem_filter] at hn
      rw [Finset.mem_coe, Finset.mem_filter]
      obtain ⟨hnw, hnd⟩ := hn
      rw [twinWindow, Finset.mem_Icc] at hnw
      have h1 : 0 < N - n := by omega
      have h2 : N - n ≤ N := by omega
      exact ⟨Finset.mem_Ioc.mpr ⟨h1, h2⟩, hnd⟩
    · intro n hn m hm h
      rw [Finset.mem_coe, Finset.mem_filter, twinWindow, Finset.mem_Icc] at hn hm
      simp only at h
      omega
  have hdiv : ((Finset.Ioc 0 N).filter (fun m => d ∣ m)).card = N / d :=
    Nat.Ioc_filter_dvd_card_eq_div N d
  calc (((twinWindow N).filter (fun n => d ∣ (N - n))).card : ℝ)
      ≤ (((Finset.Ioc 0 N).filter (fun m => d ∣ m)).card : ℝ) := by exact_mod_cast hcard
    _ = ((N / d : ℕ) : ℝ) := by rw [hdiv]
    _ ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le

/-- **The reflected prime-power strip bound** (`stripSum_le` mirror). -/
theorem gold_stripSum_le {N z y : ℕ} (hN : 2 ≤ N) (hz : 2 ≤ z) :
    ∑ n ∈ twinWindow N, vonMangoldt n * (sqStripZ z y (N - n) : ℝ)
      ≤ Real.log N * (N : ℝ) / ((z : ℝ) - 1) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hcount : ∀ n, (sqStripZ z y (N - n) : ℝ)
      = ∑ p ∈ primeItv z y, (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0) := by
    intro n
    unfold sqStripZ
    rw [Finset.card_filter]
    push_cast
    rfl
  have hexpand : ∑ n ∈ twinWindow N, vonMangoldt n * (sqStripZ z y (N - n) : ℝ)
      = ∑ p ∈ primeItv z y,
          ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0) := by
    have hstep : ∑ n ∈ twinWindow N, vonMangoldt n * (sqStripZ z y (N - n) : ℝ)
        = ∑ n ∈ twinWindow N,
            ∑ p ∈ primeItv z y,
              vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hcount n, Finset.mul_sum]
    rw [hstep, Finset.sum_comm]
  rw [hexpand]
  have hper : ∀ p ∈ primeItv z y,
      ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
        ≤ Real.log N * ((N : ℝ) / ((p : ℝ) ^ 2)) := by
    intro p hp
    have hstep1 : ∑ n ∈ twinWindow N,
        vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
        ≤ ∑ n ∈ twinWindow N, Real.log N * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hd : p ^ 2 ∣ (N - n)
      · simp only [hd, if_true, mul_one]
        rw [twinWindow, Finset.mem_Icc] at hn
        refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
        · exact_mod_cast (by omega : 1 ≤ n)
        · exact_mod_cast (by omega : n ≤ N)
      · simp [hd]
    have hstep2 : ∑ n ∈ twinWindow N, Real.log N * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
        = Real.log N * (((twinWindow N).filter (fun n => p ^ 2 ∣ (N - n))).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.card_filter]
      push_cast
      rfl
    have hstep3 : (((twinWindow N).filter (fun n => p ^ 2 ∣ (N - n))).card : ℝ)
        ≤ (N : ℝ) / ((p : ℝ) ^ 2) := by
      have h := gold_card_window_dvd_le (N := N) (d := p ^ 2) hN
      calc (((twinWindow N).filter (fun n => p ^ 2 ∣ (N - n))).card : ℝ)
          ≤ (N : ℝ) / ((p ^ 2 : ℕ) : ℝ) := h
        _ = (N : ℝ) / ((p : ℝ) ^ 2) := by push_cast; ring
    calc ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
        ≤ Real.log N * (((twinWindow N).filter (fun n => p ^ 2 ∣ (N - n))).card : ℝ) := by
          rw [← hstep2]; exact hstep1
      _ ≤ Real.log N * ((N : ℝ) / ((p : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep3 hlogN
  calc ∑ p ∈ primeItv z y,
          ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
      ≤ ∑ p ∈ primeItv z y, Real.log N * ((N : ℝ) / ((p : ℝ) ^ 2)) :=
        Finset.sum_le_sum hper
    _ = Real.log N * (N : ℝ) * ∑ p ∈ primeItv z y, (1 : ℝ) / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ Real.log N * (N : ℝ) * (1 / ((z : ℝ) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsub : ∑ p ∈ primeItv z y, (1 : ℝ) / ((p : ℝ) ^ 2)
            ≤ ∑ m ∈ Finset.Icc z y, (1 : ℝ) / ((m : ℝ) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; rw [primeItv, Finset.mem_filter] at hp; exact hp.1
          · intro _ _ _; positivity
        exact le_trans hsub (Salt.BrunLower.sum_one_div_sq_le hz)
    _ = Real.log N * (N : ℝ) / ((z : ℝ) - 1) := by ring

/-- **The Goldbach W strip bound.**  The kept strip carrier is dominated termwise by the
`z`-restricted strip sum, via the split bridge at kept points. -/
theorem gold_stripPrimeSumW_le {N z P y Q a w' : ℕ} (hN2 : 2 ≤ N) (hz : 2 ≤ z) (haN : a ≤ N)
    (hzN : 2 * z ≤ N)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P)
    (hQNa : Nat.Coprime Q (N - a)) :
    goldStripPrimeSumW Q a N P y ≤ Real.log N * (N : ℝ) / ((z : ℝ) - 1) := by
  rw [goldStripPrimeSumW]
  refine le_trans ?_ (gold_stripSum_le (y := y) hN2 hz)
  apply Finset.sum_le_sum
  intro n hn
  by_cases hk : Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q
  · have hkeep1 : keepG Q a P N n = 1 := keepG_eq_one_iff.mpr hk
    rw [twinWindow, Finset.mem_Icc] at hn
    have hnN : n ≤ N := by omega
    have hzn : z ≤ n := by omega
    have hcop := factors_ge_z_of_sift_G haN hnN hk.1 hzn hQfull hPfull' hQNa hk.2.1 hk.2.2
    have hn0 : N - n ≠ 0 := by omega
    have heq := sqStrip_eq_sqStripZ (z := z) (y := y) hn0 hcop
    rw [hkeep1, mul_one, heq]
  · have hkeep0 : keepG Q a P N n = 0 := by unfold keepG; rw [if_neg hk]
    rw [hkeep0]
    simp [mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)]

/-! ## Part E — the positivity, the survivor, and the headline consumer -/

/-- **The Goldbach positivity.**  The three main-term bounds + the ledger force the
W-restricted P₂ carrier strictly positive. -/
theorem gold_positivity_W {N z P y Q a w' : ℕ} {mainA1 mainA2 mainA3 : ℝ}
    (hN2 : 2 ≤ N) (hz : 2 ≤ z) (hyx : N < (y + 1) ^ 3) (haN : a ≤ N) (hzN : 2 * z ≤ N)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P)
    (hQNa : Nat.Coprime Q (N - a))
    (hA1 : mainA1 ≤ goldA1PrimeSumW Q a N P)
    (hA2 : goldOmegaPrimeSum Q a N P y ≤ mainA2)
    (hA3 : goldTriplePrimeSumW Q a N P y ≤ mainA3)
    (hledger : 0 < mainA1 - mainA2 / 2 - mainA3 / 2
        - Real.log N * (N : ℝ) / ((z : ℝ) - 1) / 2) :
    0 < goldP2PrimeSumW Q a N z P := by
  have hred := gold_razor_reduction_W (z := z) (w' := w') hN2 hyx haN hzN hQfull hPfull' hQNa
  have hS := gold_stripPrimeSumW_le (y := y) hN2 hz haN hzN hQfull hPfull' hQNa
  linarith [hred, hA1, hA2, hA3, hS, hledger]

/-- **The Goldbach survivor.**  From the positivity: a prime `n` in the window with `N − n`
a genuine P₂ (`IsP2 2`, via `isP2_mono` from the sifted `IsP2 z`). -/
theorem gold_survivor_W {N z P y Q a w' : ℕ} {mainA1 mainA2 mainA3 : ℝ}
    (hN2 : 2 ≤ N) (hz : 2 ≤ z) (hyx : N < (y + 1) ^ 3) (haN : a ≤ N) (hzN : 2 * z ≤ N)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P)
    (hQNa : Nat.Coprime Q (N - a))
    (hA1 : mainA1 ≤ goldA1PrimeSumW Q a N P)
    (hA2 : goldOmegaPrimeSum Q a N P y ≤ mainA2)
    (hA3 : goldTriplePrimeSumW Q a N P y ≤ mainA3)
    (hledger : 0 < mainA1 - mainA2 / 2 - mainA3 / 2
        - Real.log N * (N : ℝ) / ((z : ℝ) - 1) / 2) :
    ∃ n : ℕ, N / 2 ≤ n ∧ n ≤ N - 2 ∧ n.Prime ∧ IsP2 2 (N - n) := by
  have hpos := gold_positivity_W hN2 hz hyx haN hzN hQfull hPfull' hQNa hA1 hA2 hA3 hledger
  have hpos' : 0 < ∑ n ∈ twinWindow N, vonMangoldt n * keepG Q a P N n * p2Ind z (N - n) :=
    hpos
  obtain ⟨n, hn, hterm⟩ :
      ∃ n ∈ twinWindow N, 0 < vonMangoldt n * keepG Q a P N n * p2Ind z (N - n) := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    exact absurd (Finset.sum_nonpos hcon) (not_le.mpr hpos')
  have hkeepne : keepG Q a P N n ≠ 0 := by
    intro h0; rw [h0] at hterm; simp at hterm
  have hkeep1 : keepG Q a P N n = 1 := by
    unfold keepG at hkeepne ⊢
    by_cases hh : Nat.Prime n ∧ Nat.Coprime P (N - n) ∧ n % Q = a % Q
    · rw [if_pos hh]
    · rw [if_neg hh] at hkeepne; exact absurd rfl hkeepne
  obtain ⟨hprime, -⟩ := keepG_eq_one_iff.mp hkeep1
  have hp2ne : p2Ind z (N - n) ≠ 0 := by
    intro h0; rw [h0] at hterm; simp at hterm
  have hIsP2z : IsP2 z (N - n) := by
    unfold p2Ind at hp2ne
    by_contra hnp2
    rw [if_neg hnp2] at hp2ne
    exact hp2ne rfl
  rw [twinWindow, Finset.mem_Icc] at hn
  exact ⟨n, hn.1, hn.2, hprime, isP2_mono hz hIsP2z⟩

/-- **`goldbach_of_hypotheses_W` — the Goldbach headline consumer** (the
`chen_of_hypotheses_W` mirror, in the frozen D0 `∃ N₀, ∀ N ≥ N₀, Even N → …` form).
Given, past a threshold and at every even `N`, an operating tuple `(z, P, y, Q, a, w')`
with the split sifting rows, the reflected-residue coprimality, the three main-term
bounds at the `keepG` carriers, and the ledger positivity — every such `N` is
`prime + P₂`. -/
theorem goldbach_of_hypotheses_W
    (H : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
        ∃ (z P y Q a w' : ℕ) (mainA1 mainA2 mainA3 : ℝ),
        2 ≤ N ∧ 2 ≤ z ∧ N < (y + 1) ^ 3 ∧ a ≤ N ∧ 2 * z ≤ N ∧
        (∀ q, q.Prime → q < w' → q ∣ Q) ∧
        (∀ q, q.Prime → w' ≤ q → q < z → ¬ q ∣ N → q ∣ P) ∧
        Nat.Coprime Q (N - a) ∧
        mainA1 ≤ goldA1PrimeSumW Q a N P ∧
        goldOmegaPrimeSum Q a N P y ≤ mainA2 ∧
        goldTriplePrimeSumW Q a N P y ≤ mainA3 ∧
        0 < mainA1 - mainA2 / 2 - mainA3 / 2
          - Real.log N * (N : ℝ) / ((z : ℝ) - 1) / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, N = p + q ∧ p.Prime ∧ IsP2 2 q := by
  obtain ⟨N₀, hH⟩ := H
  refine ⟨N₀, fun N hN hEven => ?_⟩
  obtain ⟨z, P, y, Q, a, w', m1, m2, m3, hN2, hz, hyx, haN, hzN, hQfull, hPfull', hQNa,
    hA1, hA2, hA3, hledger⟩ := hH N hN hEven
  obtain ⟨n, hlo, hhi, hprime, hp2⟩ :=
    gold_survivor_W hN2 hz hyx haN hzN hQfull hPfull' hQNa hA1 hA2 hA3 hledger
  exact ⟨n, N - n, by omega, hprime, hp2⟩

end Salt.Goldbach
