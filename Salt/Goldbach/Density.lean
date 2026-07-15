/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.WRatioSharp

/-!
# G-DENS — re-derive node (i): the punctured sifting density for `chen_goldbach`

Design: `docs/exploration/q1-design.md`, node **G-DENS** (D2.1) with THE GATE CORRECTION
(2026-07-15) baked into the keystone.  This file mirrors the twin density spine
(`Salt/Chen/TwinA1.lean`, `TwinA1W.lean`, `WRatioSharp.lean`) at the **Goldbach** sieve, where
the sifting modulus is *punctured* — the primes `q ∣ N` are removed — so that the
`{q ∣ N}` unit seam vanishes (`coprime_of_dvd_goldPs`).

## Deliverables

* **Part A — the punctured modulus `goldPs N z w' = ∏_{w'≤q<z, q∤N} q`.**  Squarefree,
  `Coprime (goldPs N z w') N`, and the load-bearing divisor fact
  `d ∣ goldPs → Coprime d N` (`coprime_of_dvd_goldPs`) that the whole Goldbach remainder
  analysis consumes.
* **Part B — the reduced-residue re-threading.**  The Goldbach replacements for
  `coprime_sub_two` (TwinA1:221): from `Coprime d N` the residue class `N mod d` is a unit
  (`coprime_mod_of_coprime`), and the CRT-class-coprimality mirror
  (`crtClass_coprime_gold`, mirroring `crt_class_coprime` TwinA1W:208).
* **Part C — THE GATE-CORRECTED KEYSTONE `window_prod_upper_punctured`.**  For the punctured
  window `primesInWindow z y \ {q ∣ N}` the density product `∏(1 − ν(q))` obeys the full-window
  upper bound (`Salt.Chen.window_prod_upper`) times a correction `≤ exp(8/(z−2))`.  Route (per
  the gate): `Finset.prod_sdiff` factors `∏_{S∖T} = ∏_S / ∏_T`, and the correction
  `∏_T (q−1)/(q−2) ≤ exp(8/(z−2))` via `#{q ∣ N : q ≥ z} ≤ 8` (`card_primesInWindow_dvd_le`).
  A clean folded corollary (`window_prod_upper_punctured_folded`) and the operating-point
  numeric correction (`exp_correction_le_op`) absorb the residual into the existing
  `O(1/log z)` slack shape.
* **Part D — the density instance facts.**  `nuChen` is reused verbatim (N-independent) and the
  `ν(q) ≤ 1/(q−1)` bracket at the punctured modulus (`goldPs_hnu`, delegating to the landed
  `twinA1_hnu`) — the `vratio_prod_le` (Hyp4:124) consumption shape.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset Salt.Chen Salt.BrunLower

namespace Salt.Goldbach

/-! ## Part A — the punctured sifting modulus `goldPs` -/

/-- **The punctured Goldbach sifting modulus** `P_N = ∏_{w'≤q<z, q prime, q∤N} q`.  Mirrors the
twin's primorial-style window product (`opP`, `HeadlineW2:27`) with the extra `q ∤ N` puncture:
the primes dividing `N` are excluded, which is exactly what makes `Coprime d N` free for every
`d ∣ goldPs` (the switch-seam-vanishing fact of the gate). -/
noncomputable def goldPs (N z w' : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Ico w' z).filter (fun q => q.Prime ∧ ¬ q ∣ N), p

/-- A finite product of distinct primes is squarefree (local copy of the twin
`opf_prod_primes_squarefree` pattern; that one lives downstream in `HeadlineW2`). -/
private theorem prod_primes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hap (hsp p hp)).mpr (by rintro rfl; exact ha hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, hap.squarefree, ih hsp⟩

/-- **`goldPs` is squarefree** (a product of distinct primes). -/
theorem goldPs_squarefree (N z w' : ℕ) : Squarefree (goldPs N z w') := by
  rw [goldPs]
  exact prod_primes_squarefree fun p hp => (Finset.mem_filter.mp hp).2.1

/-- **The prime support of `goldPs`** is exactly the punctured prime window
`{q : w' ≤ q < z, q ∤ N}`. -/
theorem goldPs_primeFactors (N z w' : ℕ) :
    (goldPs N z w').primeFactors
      = (Finset.Ico w' z).filter (fun q => q.Prime ∧ ¬ q ∣ N) := by
  rw [goldPs]
  exact Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2.1

/-- **`Coprime (goldPs N z w') N`** — every prime factor of `goldPs` is a prime `q ∤ N`, hence
coprime to `N`; the product is coprime to `N`. -/
theorem goldPs_coprime_N (N z w' : ℕ) : Nat.Coprime (goldPs N z w') N := by
  rw [goldPs]
  apply Nat.Coprime.prod_left
  intro q hq
  obtain ⟨_, hqp, hqN⟩ := Finset.mem_filter.mp hq
  exact hqp.coprime_iff_not_dvd.mpr hqN

/-- **THE load-bearing divisor fact.**  Every divisor `d ∣ goldPs N z w'` is coprime to `N`.
This is what makes the Goldbach `{q ∣ N}` switch seam vanish (gate finding, W2/G-SW): the
residue class `N mod d` is a unit for every `d` the remainder analysis sees. -/
theorem coprime_of_dvd_goldPs {N z w' d : ℕ} (hd : d ∣ goldPs N z w') :
    Nat.Coprime d N :=
  Nat.Coprime.coprime_dvd_left hd (goldPs_coprime_N N z w')

/-- Every prime factor of `goldPs` is `≥ 3` (it is `≥ w' ≥ 3`) — the oddness the sieve-class
side conditions (`divisor_cases`, `hguard`) consume. -/
theorem goldPs_odd {N z w' : ℕ} (hw' : 3 ≤ w') :
    ∀ p ∈ (goldPs N z w').primeFactors, 3 ≤ p := by
  intro p hp
  rw [goldPs_primeFactors] at hp
  have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
  omega

/-- The bundled prime-support facts of `goldPs` (prime, in the window `[w', z)`, `q ∤ N`) — the
raw inputs a consumer assembles into the `vratio_prod_le`/`hguard` hypotheses. -/
theorem goldPs_primeFactors_facts {N z w' : ℕ} :
    ∀ q ∈ (goldPs N z w').primeFactors,
      q.Prime ∧ w' ≤ q ∧ q < z ∧ ¬ q ∣ N := by
  intro q hq
  rw [goldPs_primeFactors, Finset.mem_filter, Finset.mem_Ico] at hq
  exact ⟨hq.2.1, hq.1.1, hq.1.2, hq.2.2⟩

/-! ## Part B — the reduced-residue re-threading (`coprime_sub_two` analogues) -/

/-- **The Goldbach `coprime_sub_two` analogue.**  From `Coprime d N`, the residue class
`N mod d` (the class the Goldbach sieve sifts: `q ∣ N − n ↔ n ≡ N (mod q)`) is a unit mod `d`.
Replaces `coprime_sub_two` (TwinA1:221, `Coprime d (d−2)`) in the Goldbach `apDisc`/CRT
mirrors. -/
theorem coprime_mod_of_coprime {d N : ℕ} (h : Nat.Coprime d N) : Nat.Coprime d (N % d) := by
  have hg : Nat.gcd (N % d) d = Nat.gcd N d := Nat.ModEq.gcd_eq (Nat.mod_modEq N d)
  rw [Nat.Coprime, Nat.gcd_comm, hg, Nat.gcd_comm]
  exact h

/-- **The Goldbach CRT-class-coprimality** (mirroring `crt_class_coprime` TwinA1W:208).  The
fused residue `c` — `c ≡ a (mod Q)` (the `Q`-side class of G-RES) and `c ≡ N (mod d)` (the
`d`-side class) — is reduced mod `Q·d`.  `gcd(c, Q) = gcd(a, Q) = 1` from `hQa`; `gcd(c, d) =
gcd(N mod d, d) = 1` from `Coprime d N` via `coprime_mod_of_coprime`. -/
theorem crtClass_coprime_gold {Q a d c N : ℕ}
    (hQa : Nat.Coprime Q a) (hdN : Nat.Coprime d N)
    (hcQ : c % Q = a % Q) (hcd : c % d = (N % d) % d) :
    Nat.Coprime (Q * d) c := by
  have hQc : Nat.Coprime Q c := by
    have h : Nat.gcd c Q = Nat.gcd a Q := Nat.ModEq.gcd_eq (show c ≡ a [MOD Q] from hcQ)
    rw [Nat.Coprime, Nat.gcd_comm, h, Nat.gcd_comm]
    exact hQa
  have hdc : Nat.Coprime d c := by
    have hmod : Nat.Coprime d (N % d) := coprime_mod_of_coprime hdN
    have h : Nat.gcd c d = Nat.gcd (N % d) d :=
      Nat.ModEq.gcd_eq (show c ≡ (N % d) [MOD d] from hcd)
    rw [Nat.Coprime, Nat.gcd_comm, h, Nat.gcd_comm]
    exact hmod
  exact Nat.Coprime.mul_left hQc hdc

/-! ## Part C — THE GATE-CORRECTED KEYSTONE `window_prod_upper_punctured` -/

/-- **The divisor-count fact `#{q ∣ N : q ≥ z} ≤ 8`.**  The window primes dividing `N` are
distinct primes each `≥ zr`, so their product divides `N` and is `≥ zr^k`; with `N < zr^9`
this forces `zr^k ≤ N < zr^9`, hence `k ≤ 8` (each such prime exceeds `zr = N^{1/8}`, so at
most `8` fit in `N`). -/
theorem card_primesInWindow_dvd_le {zr yr : ℝ} (hz : 3 ≤ zr) {N : ℕ} (hN0 : N ≠ 0)
    (hN9 : (N : ℝ) < zr ^ 9) :
    ((primesInWindow zr yr).filter (fun q => q ∣ N)).card ≤ 8 := by
  set T := (primesInWindow zr yr).filter (fun q => q ∣ N) with hT
  have hsub : T ⊆ N.primeFactors := by
    intro q hq
    rw [hT, Finset.mem_filter] at hq
    obtain ⟨hqw, hqN⟩ := hq
    obtain ⟨hqp, _⟩ := window_mem_facts hz hqw
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqN, hN0⟩
  have hdvd : (∏ q ∈ T, q) ∣ N :=
    dvd_trans (Finset.prod_dvd_prod_of_subset T N.primeFactors (fun q => q) hsub)
      (Nat.prod_primeFactors_dvd N)
  have hprodN : ((∏ q ∈ T, q : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
  have hzpos : (0 : ℝ) ≤ zr := by linarith
  have hlow : zr ^ T.card ≤ ((∏ q ∈ T, q : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    calc zr ^ T.card = ∏ _q ∈ T, zr := (Finset.prod_const zr).symm
      _ ≤ ∏ q ∈ T, (q : ℝ) := by
          apply Finset.prod_le_prod (fun _ _ => hzpos)
          intro q hq
          rw [hT, Finset.mem_filter, primesInWindow, Finset.mem_filter] at hq
          exact hq.1.2.2
  have hzr1 : (1 : ℝ) < zr := by linarith
  by_contra hcon
  have hcon' : 9 ≤ T.card := Nat.not_le.mp hcon
  have hge : zr ^ 9 ≤ zr ^ T.card := pow_le_pow_right₀ hzr1.le hcon'
  have : zr ^ T.card < zr ^ 9 := lt_of_le_of_lt (le_trans hlow hprodN) hN9
  linarith

/-- **The correction factor `∏_{q∣N} (q−1)/(q−2) ≤ exp(8/(z−2))`.**  Each factor
`1 + 1/(q−2) ≤ exp(1/(q−2))`, `1/(q−2) ≤ 1/(zr−2)` (as `q ≥ zr`), and there are `≤ 8` factors
(`hcard`), so the exponent sum is `≤ 8/(zr−2)`. -/
theorem punctured_correction_le {zr yr : ℝ} (hz : 3 ≤ zr) {N : ℕ}
    (hcard : ((primesInWindow zr yr).filter (fun q => q ∣ N)).card ≤ 8) :
    ∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N),
        ((q : ℝ) - 1) / ((q : ℝ) - 2) ≤ Real.exp (8 / (zr - 2)) := by
  set T := (primesInWindow zr yr).filter (fun q => q ∣ N) with hT
  have hz2 : (0 : ℝ) < zr - 2 := by linarith
  have hfacts : ∀ q ∈ T, (3 : ℝ) ≤ (q : ℝ) ∧ zr ≤ (q : ℝ) := by
    intro q hq
    have hqm : q ∈ primesInWindow zr yr := by rw [hT, Finset.mem_filter] at hq; exact hq.1
    obtain ⟨_, hq3⟩ := window_mem_facts hz hqm
    rw [primesInWindow, Finset.mem_filter] at hqm
    exact ⟨by exact_mod_cast hq3, hqm.2.2⟩
  calc ∏ q ∈ T, ((q : ℝ) - 1) / ((q : ℝ) - 2)
      ≤ ∏ q ∈ T, Real.exp (1 / ((q : ℝ) - 2)) := by
        apply Finset.prod_le_prod
        · intro q hq
          obtain ⟨hqR, _⟩ := hfacts q hq
          exact div_nonneg (by linarith) (by linarith)
        · intro q hq
          obtain ⟨hqR, _⟩ := hfacts q hq
          have hq2 : (q : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
          have heq : ((q : ℝ) - 1) / ((q : ℝ) - 2) = 1 + 1 / ((q : ℝ) - 2) := by
            field_simp; ring
          rw [heq]
          have := Real.add_one_le_exp (1 / ((q : ℝ) - 2))
          linarith
    _ = Real.exp (∑ q ∈ T, 1 / ((q : ℝ) - 2)) := (Real.exp_sum T _).symm
    _ ≤ Real.exp (8 / (zr - 2)) := by
        apply Real.exp_le_exp.mpr
        calc ∑ q ∈ T, 1 / ((q : ℝ) - 2)
            ≤ ∑ _q ∈ T, 1 / (zr - 2) := by
              apply Finset.sum_le_sum
              intro q hq
              obtain ⟨_, hzq⟩ := hfacts q hq
              exact one_div_le_one_div_of_le hz2 (by linarith)
          _ = (T.card : ℝ) * (1 / (zr - 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 8 * (1 / (zr - 2)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast hcard
          _ = 8 / (zr - 2) := by ring

/-- **THE GATE-CORRECTED KEYSTONE.**  For the punctured window `primesInWindow z y \ {q ∣ N}`
the density product `∏(1 − ν(q))` obeys the full-window upper bound
`(log z/log y)(1 + 38/log z)` (`Salt.Chen.window_prod_upper`) times the correction
`exp(8/(z−2))`.  Route (gate, D2.1): `Finset.prod_sdiff` factors
`∏_{S∖T}(1−ν) = (∏_S(1−ν))·∏_T (q−1)/(q−2)`, then `window_prod_upper` + `punctured_correction_le`.
The `hcard` slot is discharged by `card_primesInWindow_dvd_le`. -/
theorem window_prod_upper_punctured {zr yr : ℝ} (hz : 3 ≤ zr) (hzy : zr ≤ yr)
    (hz38 : 38 ≤ Real.log zr) {N : ℕ}
    (hcard : ((primesInWindow zr yr).filter (fun q => q ∣ N)).card ≤ 8) :
    ∏ q ∈ (primesInWindow zr yr).filter (fun q => ¬ q ∣ N), (1 - nuChen q)
      ≤ Real.log zr / Real.log yr * (1 + 38 / Real.log zr) * Real.exp (8 / (zr - 2)) := by
  have hTsub : (primesInWindow zr yr).filter (fun q => q ∣ N) ⊆ primesInWindow zr yr :=
    Finset.filter_subset _ _
  have hUeq : (primesInWindow zr yr).filter (fun q => ¬ q ∣ N)
      = primesInWindow zr yr \ (primesInWindow zr yr).filter (fun q => q ∣ N) :=
    Finset.filter_not _ _
  rw [hUeq]
  have hsd := Finset.prod_sdiff (f := fun q => 1 - nuChen q) hTsub
  have hBCorr : (∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N), (1 - nuChen q))
      * (∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N),
          ((q : ℝ) - 1) / ((q : ℝ) - 2)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro q hq
    obtain ⟨hqp, hq3⟩ := window_mem_facts hz (hTsub hq)
    have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
    have hq2 : (q : ℝ) - 2 ≠ 0 := by linarith
    rw [nuChen_prime hqp]; field_simp; ring
  have hkey : ∏ q ∈ primesInWindow zr yr \ (primesInWindow zr yr).filter (fun q => q ∣ N),
        (1 - nuChen q)
      = (∏ q ∈ primesInWindow zr yr, (1 - nuChen q))
        * ∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N),
            ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
    calc ∏ q ∈ primesInWindow zr yr \ (primesInWindow zr yr).filter (fun q => q ∣ N),
            (1 - nuChen q)
        = (∏ q ∈ primesInWindow zr yr \ (primesInWindow zr yr).filter (fun q => q ∣ N),
              (1 - nuChen q))
            * ((∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N), (1 - nuChen q))
              * ∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N),
                  ((q : ℝ) - 1) / ((q : ℝ) - 2)) := by rw [hBCorr]; ring
      _ = ((∏ q ∈ primesInWindow zr yr \ (primesInWindow zr yr).filter (fun q => q ∣ N),
              (1 - nuChen q))
            * ∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N), (1 - nuChen q))
            * ∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N),
                ((q : ℝ) - 1) / ((q : ℝ) - 2) := by ring
      _ = (∏ q ∈ primesInWindow zr yr, (1 - nuChen q))
            * ∏ q ∈ (primesInWindow zr yr).filter (fun q => q ∣ N),
                ((q : ℝ) - 1) / ((q : ℝ) - 2) := by rw [hsd]
  rw [hkey]
  have hlogz : 0 < Real.log zr := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log yr := Real.log_pos (by linarith)
  have hupper0 : 0 ≤ Real.log zr / Real.log yr * (1 + 38 / Real.log zr) :=
    mul_nonneg (div_nonneg hlogz.le hlogy.le) (by positivity)
  apply mul_le_mul (window_prod_upper hz hzy hz38) (punctured_correction_le hz hcard) _ hupper0
  apply Finset.prod_nonneg
  intro q hq
  obtain ⟨_, hq3⟩ := window_mem_facts hz (hTsub hq)
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  exact div_nonneg (by linarith) (by linarith)

/-- **The correction linearised** (mirroring the `window_prod_upper` `1 + C/log z` technique).
For `zr ≥ 18`, `exp(8/(zr−2)) ≤ 1 + 16/(zr−2)` — via `1 − t ≤ exp(−t)` ⟹ `exp t ≤ 1/(1−t)
≤ 1 + 2t` for `t = 8/(zr−2) ≤ 1/2`. -/
theorem exp_correction_le {zr : ℝ} (hz : 18 ≤ zr) :
    Real.exp (8 / (zr - 2)) ≤ 1 + 16 / (zr - 2) := by
  have hz2 : (0 : ℝ) < zr - 2 := by linarith
  set t := 8 / (zr - 2) with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htle : t ≤ 1 / 2 := by rw [ht, div_le_iff₀ hz2]; linarith
  have h1mt : (0 : ℝ) < 1 - t := by linarith
  have hen : 1 - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t); linarith
  have hle1 : (1 - t) * Real.exp t ≤ 1 := by
    have h2 : 1 - t ≤ (Real.exp t)⁻¹ := by rwa [Real.exp_neg] at hen
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos t).le
    rwa [inv_mul_cancel₀ (Real.exp_pos t).ne'] at h3
  have hexpb : Real.exp t ≤ 1 / (1 - t) := by
    rw [le_div_iff₀ h1mt, mul_comm]; exact hle1
  have hfrac : 1 / (1 - t) ≤ 1 + 2 * t := by
    rw [div_le_iff₀ h1mt]
    nlinarith [mul_nonneg ht0 (show (0 : ℝ) ≤ 1 - 2 * t by linarith)]
  have h2t : 2 * t = 16 / (zr - 2) := by rw [ht]; ring
  linarith [hexpb, hfrac, h2t]

/-- **The operating-point numeric correction** (explicit tiny constant, per the gate note).
For `zr ≥ 10^7` (comfortably true at `zr = x^{1/8}`, `log x ≥ 3.4·10⁷`),
`exp(8/(zr−2)) ≤ 1 + 2/10⁶`. -/
theorem exp_correction_le_op {zr : ℝ} (hz : (10 : ℝ) ^ 7 ≤ zr) :
    Real.exp (8 / (zr - 2)) ≤ 1 + 2 / 10 ^ 6 := by
  have h18 : (18 : ℝ) ≤ zr := le_trans (by norm_num) hz
  have hmain := exp_correction_le h18
  have hz2 : (0 : ℝ) < zr - 2 := by linarith
  have hstep : 16 / (zr - 2) ≤ 2 / 10 ^ 6 := by
    rw [div_le_div_iff₀ hz2 (by norm_num)]
    nlinarith [hz]
  linarith [hmain, hstep]

/-- **The consumable folded keystone.**  Combining `window_prod_upper_punctured` with the
linearised correction (`exp_correction_le`), for `zr ≥ 18` the punctured product is bounded by
the same `(log z/log y)(1 + C/log z)`-shape times `(1 + 16/(z−2))` — the residual absorbed
into the `O(1/log z)` slack the `rho − 3/8` W-ratio arithmetic already carries. -/
theorem window_prod_upper_punctured_folded {zr yr : ℝ} (hz18 : 18 ≤ zr) (hzy : zr ≤ yr)
    (hz38 : 38 ≤ Real.log zr) {N : ℕ}
    (hcard : ((primesInWindow zr yr).filter (fun q => q ∣ N)).card ≤ 8) :
    ∏ q ∈ (primesInWindow zr yr).filter (fun q => ¬ q ∣ N), (1 - nuChen q)
      ≤ Real.log zr / Real.log yr * (1 + 38 / Real.log zr) * (1 + 16 / (zr - 2)) := by
  have hz : (3 : ℝ) ≤ zr := by linarith
  refine le_trans (window_prod_upper_punctured hz hzy hz38 hcard) ?_
  have hlogz : 0 < Real.log zr := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log yr := Real.log_pos (by linarith)
  have hupper0 : 0 ≤ Real.log zr / Real.log yr * (1 + 38 / Real.log zr) :=
    mul_nonneg (div_nonneg hlogz.le hlogy.le) (by positivity)
  exact mul_le_mul_of_nonneg_left (exp_correction_le hz18) hupper0

/-! ## Part D — the density instance facts at the punctured modulus -/

/-- `nuChen` is reused verbatim: `ν(d) = 1/φ(d)`, N-independent (nothing about `N` enters the
sifting density — the singular-series invariance of the reuse contract, D1). -/
theorem goldPs_nu_eq (d : ℕ) : nuChen d = 1 / (d.totient : ℝ) := rfl

/-- **The `hnu` bracket at the punctured modulus** (`vratio_prod_le` Hyp4:124 consumption).
`ν(q) ≤ 1/(q−1)` at every sifting prime — an equality (`ν(q) = 1/(q−1)`), so tight.  Delegates
to the landed `twinA1_hnu`, whose statement is over `P.primeFactors` for an arbitrary modulus
`P`; instantiate at `P := goldPs N z w'`. -/
theorem goldPs_hnu (N z w' : ℕ) :
    ∀ q ∈ (goldPs N z w').primeFactors, nuChen q ≤ 1 / ((q : ℝ) - 1) :=
  twinA1_hnu (goldPs N z w')

end Salt.Goldbach
