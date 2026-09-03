/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦THE LOG-REBASE OF B0–B4⟧ — λ-BV wave 2-P, the Route-II door one weight over, 2026-09-03

Wave 1 (`TwinParitySieve.lean`) built the Liouville-twisted twin `BoundingSieve` under
COUNTING weights `1 − λ(m)` and closed the B0–B4 chain to the terminal
`twin_parity_survivor_or_chowla_of_liouvilleTwinDisp` (`:357`), conditional on the named
arithmetic input `LiouvilleTwinDisp`.  This module is the commission's literal order (Route II,
ruled primary 2026-08-21): the same chain under LOG weights `(1 − λ(m))/n`, `m = n(n+2)`.

* `twinParitySieveLog` — B0 at the log weight; `prodPrimes`, `nu` are wave 1's by `rfl`.
* `Llog`/`Clog`/`remLogCount`, `rem_split_log` — B1: the remainder splits into the HARMONIC
  remainder `Clog N d − ν(d)·H_N` and the Liouville discrepancy `Llog N d − ν(d)·Llog N 1`.
* `LiouvilleTwinDispLog` — the named arithmetic input at the log weight (binder C).
* `twinParitySieveLog_brun_lower_ell1` — B2: the ten Props of `brun_lower_ell1` at the log
  sieve; `Wratio`/`hMert` port by a bare `change` to `Salt.TwinSieve.sieve N P hP`.
* `remLogCount_abs_le` (`≤ 4ρ(d)`), `BtwinLog = 4·Btwin`, `twinRemLog_sum_le`,
  `twinParitySieveLog_rosserRemainder_le` — B3 at the log weight.
* `twinParitySieveLog_siftedSum_lower` — B4 in the quantitative (verdict-4) form; and
  `twinParitySieveLog_siftedSum_eq` + `twinParitySieveLog_support_infinite`, the log-world door
  wired to the landed tail-mass infinitude (`twinLogWeight`, `sum_twinLogWeight_range`).

⛔ **Honest label** (freeze §1(c), refuter pass §C): this lands a LOG-WORLD DOOR conditional on
`LiouvilleTwinDispLog` (held by nobody), exactly wave 1's shape one weight over.  It is NOT the
vehicle for the fixed-`z` prize (block W, `Salt/Entropy/Chowla/AffineFork.lean`, is); it does
NOT collapse the Wave-1 terminal (that terminal's left disjunct is an ℓ¹ natural-density mass
and nothing here consumes it); its input at growing `z` is the open λ-BV object.  Class-B port
work.  Nothing here bears on twin primes.
-/
import Salt.TwinBar.TwinParitySieve
import Mathlib

open ArithmeticFunction Finset

namespace Salt.TwinBar

/-! ## Block P — the log-rebase of B0–B4 (the commission's §1.2 literal order).
⛔ Honest label, per §7 verdicts 1–2: this lands a LOG-WORLD DOOR conditional on
`LiouvilleTwinDispLog` (binder C, held by nobody), exactly wave 1's shape one weight over; it is
NOT the vehicle for the fixed-`z` prize (block W is), and its input at growing `z` is the open
λ-BV object.  It is the Captain's ruled primary (Route II) and is class-B port work. -/

/-- **P0a.**  The twin index: `n` from `m = n(n+2)`, i.e. `n = √(m+1) − 1`. -/
def twinIdx (m : ℕ) : ℕ := Nat.sqrt (m + 1) - 1

/-- **P0b (class A).**  `twinIdx` inverts the twin product. -/
theorem twinIdx_twinProd (n : ℕ) : twinIdx (n * (n + 2)) = n := by
  have h : n * (n + 2) + 1 = (n + 1) ^ 2 := by ring
  rw [twinIdx, h, Nat.sqrt_eq']
  omega

/-- **P0 (B0-log).**  The Liouville-twisted twin `BoundingSieve` under `1/n` weights: support,
modulus, density are `twinParitySieve`'s; the weights carry `(1 − λ(m))/n(m)`. -/
noncomputable def twinParitySieveLog (N P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.Icc 1 N).image (fun n => n * (n + 2))
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun m => (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ)) / (twinIdx m : ℝ)
  weights_nonneg := fun m => by
    have := liouville_real_le m
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  totalMass := ∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
    (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ)) / (twinIdx m : ℝ)
  nu := Salt.TwinSieve.nu
  nu_mult := Salt.TwinSieve.nu_mult
  nu_pos_of_prime := fun p hp _ => Salt.TwinSieve.nu_pos_of_prime p hp
  nu_lt_one_of_prime := fun p hp _ => Salt.TwinSieve.nu_lt_one_of_prime p hp

variable {N P : ℕ} {hP : Squarefree P}

@[simp] theorem twinParitySieveLog_prodPrimes :
    (twinParitySieveLog N P hP).prodPrimes = P := rfl

@[simp] theorem twinParitySieveLog_nu :
    (twinParitySieveLog N P hP).nu = Salt.TwinSieve.nu := rfl

/-- **P0 export (class A/B).**  `totalMass = Σ_{n≤N} (1 − λ(n(n+2)))/n`: `change` to the
`image` sum, `Finset.sum_image` over `Salt.TwinSieve.twinProd_injective` (the
`twinParitySieve_totalMass` idiom, `:91-99`), then `twinIdx_twinProd` under the binder. -/
theorem twinParitySieveLog_totalMass :
    (twinParitySieveLog N P hP).totalMass
      = ∑ n ∈ Finset.Icc 1 N,
          (1 - ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ)) / (n : ℝ) := by
  change (∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
      (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ)) / (twinIdx m : ℝ)) = _
  rw [Finset.sum_image (fun a _ b _ h => Salt.TwinSieve.twinProd_injective h)]
  exact Finset.sum_congr rfl fun n _ => by rw [twinIdx_twinProd]

/-- **P1a.**  The log-weighted Liouville sum over the twin values `d ∣ n(n+2)`. -/
noncomputable def Llog (N d : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)),
    ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ)

/-- **P1b.**  The log-weighted count over the same set. -/
noncomputable def Clog (N d : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), (1 : ℝ) / (n : ℝ)

/-- **P1c.**  The harmonic remainder: the log-count minus its main term `ν(d)·H_N`. -/
noncomputable def remLogCount (d N : ℕ) : ℝ := Clog N d - Salt.TwinSieve.nu d * Clog N 1

theorem Llog_one : Llog N 1
    = ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.liouville (n * (n + 2)) : ℤ) : ℝ) / (n : ℝ) := by
  rw [Llog, Finset.filter_true_of_mem (fun n _ => one_dvd _)]

theorem Clog_one : Clog N 1 = ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := by
  rw [Clog, Finset.filter_true_of_mem (fun n _ => one_dvd _)]

/-- **P1d (class B).**  The weighted count of multiples of `d` splits as count minus Liouville. -/
theorem twinParitySieveLog_multSum (d : ℕ) :
    (twinParitySieveLog N P hP).multSum d = Clog N d - Llog N d := by
  rw [Clog, Llog]
  change (∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
      if d ∣ m then (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ)) / (twinIdx m : ℝ)
        else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => Salt.TwinSieve.twinProd_injective h),
    ← Finset.sum_filter, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by rw [twinIdx_twinProd]; ring

/-- **P1 (B1-log, class B).**  The remainder split, every `d`, no side condition. -/
theorem rem_split_log (d : ℕ) :
    (twinParitySieveLog N P hP).rem d
      = remLogCount d N - (Llog N d - Salt.TwinSieve.nu d * Llog N 1) := by
  have h : (twinParitySieveLog N P hP).totalMass = Clog N 1 - Llog N 1 := by
    rw [twinParitySieveLog_totalMass, Clog_one, Llog_one, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [BoundingSieve.rem, twinParitySieveLog_multSum, twinParitySieveLog_nu, h, remLogCount]
  ring

/-- **P1e (B1-log).**  The named arithmetic input, `rosserRemainder`'s shape verbatim, at the
log weight.  Wave 2 asserts nothing about `B`. -/
def LiouvilleTwinDispLog (N P : ℕ) (lvl B : ℝ) : Prop :=
  ∑ d ∈ P.divisors,
    (if (d : ℝ) < lvl then |Llog N d - Salt.TwinSieve.nu d * Llog N 1| else 0) ≤ B

/-- **P2a (class A).** -/
theorem twinParitySieveLog_totalMass_nonneg :
    0 ≤ (twinParitySieveLog N P hP).totalMass := by
  change 0 ≤ ∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
    (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ)) / (twinIdx m : ℝ)
  refine Finset.sum_nonneg fun m _ => ?_
  have := liouville_real_le m
  exact div_nonneg (by linarith) (Nat.cast_nonneg _)

/-- **P2b (class A, by `change`).**  `Wratio`/`windowPrimes` read only `prodPrimes` and `nu`
(`WRatio.lean:77-86`), and for `twinParitySieveLog` both are DEFINITIONALLY the landed twin
sieve's — so this IS `Salt.BrunLower.hMert_twinSieve` (`MertensDischarge.lean:660`) after a
bare `change` whose target is `Salt.TwinSieve.sieve N P hP` (NOT `twinParitySieve` — the
wave-1 twisted sieve gains nothing); the idiom is `twinParitySieve_hMert`
(`TwinParitySieve.lean:177-186`) line for line. -/
theorem twinParitySieveLog_hMert {lam z : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hz : Salt.BrunLower.zThresh lam ≤ z)
    (hpz : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    ∀ n ∈ Finset.Icc 1 (Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin lam z) z),
      Real.log (Salt.BrunLower.Wratio (twinParitySieveLog N P hP)
          (Salt.BrunLower.LamTwin lam z) z n) ≤ (n : ℝ) * (2 * lam) := by
  change ∀ n ∈ Finset.Icc 1 (Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin lam z) z),
      Real.log (Salt.BrunLower.Wratio (Salt.TwinSieve.sieve N P hP)
          (Salt.BrunLower.LamTwin lam z) z n) ≤ (n : ℝ) * (2 * lam)
  exact Salt.BrunLower.hMert_twinSieve hP hlam hlam' hz hpz

/-- **P2 (B2-log, class B).**  `brun_lower_ell1` at the log sieve, `b = 1`, `λ = 1/4`. -/
theorem twinParitySieveLog_brun_lower_ell1 {z : ℝ} (Q : ℝ) (hQ : 1 ≤ Q)
    (hz : Salt.BrunLower.zThresh (1 / 4) ≤ z)
    (hzprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < z) :
    (twinParitySieveLog N P hP).totalMass * Salt.BrunLower.W (twinParitySieveLog N P hP)
        * (1 - 2 * (1 / 4 : ℝ) ^ (2 * 1 : ℕ) * Real.exp (2 * (1 / 4))
            / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4))))
      - Salt.Chen.rosserRemainder (twinParitySieveLog N P hP)
          (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
                * Real.log z)
              * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
                  - 1 : ℕ)))
      ≤ (twinParitySieveLog N P hP).siftedSum := by
  have h := Salt.Chen.brun_lower_ell1 (twinParitySieveLog N P hP)
    (lam := 1 / 4) (Lam := Salt.BrunLower.LamTwin (1 / 4) z) (z := z)
    (kappa := 2 * (1 / 4)) (b := 1) Q hQ le_rfl (by norm_num)
    (Salt.HB.lam_exp_lt_one (by norm_num) le_rfl)
    (Salt.BrunLower.LamTwin_pos (by norm_num) le_rfl hz)
    (one_lt_of_zThresh (by norm_num) le_rfl hz)
    twinParitySieveLog_totalMass_nonneg (fun p hp => hzprimes p hp) le_rfl
    (twinParitySieveLog_hMert (by norm_num) le_rfl hz hzprimes)
  have e1 : (2 * 1 - 2 + 1 : ℕ) = 1 := by omega
  have e2 : (2 * 1 - 2 + 2 * Salt.BrunLower.minLevel
        (Salt.BrunLower.LamTwin (1 / 4) z) z - 1 : ℕ)
      = 2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z - 1 := by omega
  rw [e1, e2, Nat.cast_one] at h
  exact h

/-- Helper (P3a): one residue class `n ≡ r (mod d)`, `r < d`, has harmonic sum within `4` of
its main term `(1/d)·H_N`. -/
private lemma abs_class_sub_harmonic_le {d r : ℕ} (hd : 0 < d) (hr : r < d) (N : ℕ) :
    |(∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ))
        - (1 / (d : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)| ≤ 4 := by
  classical
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have he0 : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  have he1 : 1 / (d : ℝ) ≤ 1 := by
    rw [div_le_one hd0]
    exact_mod_cast hd
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.Icc_eq_empty (by omega : ¬(1 : ℕ) ≤ 0)]
    norm_num
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hHNlow : Real.log (N : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := by
    simpa only [one_div] using log_le_sum_inv_Icc N
  have hHN : (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    simpa only [one_div] using Salt.TwinBar.sum_inv_Icc_le N
  rw [abs_le]
  constructor
  · -- LOWER: reindex the class by `n = d·m + r`, `m ∈ Icc 1 M`, `M = ⌊(N − r)/d⌋`
    obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = (N - r) / d := ⟨_, rfl⟩
    have hdm : d * M + (N - r) % d = N - r := by
      rw [hMdef]; exact Nat.div_add_mod _ _
    have hmlt : (N - r) % d < d := Nat.mod_lt _ hd
    have hstep : N < d * M + 2 * d := by omega
    have hexpand : 2 * d * (M + 1) = d * M + (d * M + 2 * d) := by ring
    have hNbd : N ≤ 2 * d * (M + 1) := by omega
    have hNbdR : (N : ℝ) ≤ 2 * (d : ℝ) * ((M : ℝ) + 1) := by exact_mod_cast hNbd
    have hlogN : Real.log (N : ℝ) ≤ Real.log (2 * (d : ℝ)) + Real.log ((M : ℝ) + 1) := by
      have h := Real.log_le_log hNR hNbdR
      rwa [Real.log_mul (by positivity : (2 * (d : ℝ)) ≠ 0)
        (by positivity : ((M : ℝ) + 1) ≠ 0)] at h
    have hHM : Real.log ((M : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) := by
      simpa only [one_div] using log_succ_le_sum_inv_Icc M
    have hbig : (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ))
        ≤ 1 + Real.log (2 * (d : ℝ)) + ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) := by
      linarith
    have hinj : ∀ a ∈ Finset.Icc 1 M, ∀ b ∈ Finset.Icc 1 M,
        d * a + r = d * b + r → a = b :=
      fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd (Nat.add_right_cancel h)
    have hsubset : (Finset.Icc 1 M).image (fun m => d * m + r)
        ⊆ (Finset.Icc 1 N).filter (fun n => n % d = r) := by
      intro n hn
      simp only [Finset.mem_image, Finset.mem_Icc] at hn
      obtain ⟨m, ⟨hm1, hm2⟩, rfl⟩ := hn
      have h1M : 1 ≤ M := le_trans hm1 hm2
      have hdM1 : d * 1 ≤ d * M := Nat.mul_le_mul (le_refl d) h1M
      have hdmle : d * m ≤ d * M := Nat.mul_le_mul (le_refl d) hm2
      have hgem : d * 1 ≤ d * m := Nat.mul_le_mul (le_refl d) hm1
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [Nat.add_comm (d * m) r, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have haff : (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ)))
        ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ) := by
      have himg : (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * (m : ℝ) + (r : ℝ)))
          = ∑ n ∈ (Finset.Icc 1 M).image (fun m => d * m + r), (1 : ℝ) / (n : ℝ) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun m _ => by push_cast; ring
      rw [himg]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => by positivity)
    have hsandwich := (sum_inv_affine_sub_harmonic hd hr.le M).2
    have htwo : (2 : ℝ) / (d : ℝ) = 2 * (1 / (d : ℝ)) := by ring
    rw [htwo] at hsandwich
    have hlog2d : Real.log (2 * (d : ℝ)) ≤ 2 * (d : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hmulbig : (1 / (d : ℝ)) * (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ))
        ≤ (1 / (d : ℝ)) * (1 + Real.log (2 * (d : ℝ))
            + ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hbig he0.le
    have hlogmul : (1 / (d : ℝ)) * Real.log (2 * (d : ℝ))
        ≤ (1 / (d : ℝ)) * (2 * (d : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hlog2d he0.le
    have hlogmul2 : (1 / (d : ℝ)) * (2 * (d : ℝ) - 1) = 2 - 1 / (d : ℝ) := by
      field_simp
    linarith
  · -- UPPER: the per-class upper count against `log N ≤ H_N`
    have h1 := sum_inv_class_le hd hr N
    have h2 : (1 / (d : ℝ)) * Real.log (N : ℝ)
        ≤ (1 / (d : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) :=
      mul_le_mul_of_nonneg_left hHNlow he0.le
    linarith

/-- **P3a (class B — the hardest B in this file; not a one-line row).**  The harmonic remainder
per divisor: `{n ≤ N : d ∣ n(n+2)}` is the union of `ρ(d)` residue classes `r ∈ Rnat d`
(`dvd_iff_mem_Rnat`, `Salt/Brun/M2.lean:85`, which wants `[NeZero d]` — produce it from `hd`;
`Rnat_card :76`, `Rnat_lt :100`; `nu_apply`: `ν(d) = ρ(d)/d`), and each class is within `4` of
its main term `(1/d)·H_N`, so `|remLogCount d N| ≤ 4·ρ(d)`.
UPPER: `sum_inv_class_le` (`:1087`) gives `class_r ≤ 1 + (1/d)(1 + log N)` and
`log_le_sum_inv_Icc` (`:934`) gives `log N ≤ H_N`, so `class_r − (1/d)H_N ≤ 1 + 1/d ≤ 2`.
LOWER, `r ≥ 1`: reindex `n = d·m + r`, `m ∈ Icc 1 M` with `M = ⌊(N − r)/d⌋` (NOT `⌊N/d⌋`);
`sum_inv_affine_sub_harmonic` (`:1194`, `hr : r ≤ d`) gives `class_r ≥ (1/d)H_M − 2/d`;
`Salt.TwinBar.sum_inv_Icc_le` (`Wall.lean:219`, QUALIFIED — two other `sum_inv_Icc_le`s exist)
gives `H_N ≤ 1 + log N` and `log_succ_le_sum_inv_Icc` (`:~900`) gives `H_M ≥ log(M+1)`; with
`N < d(M+2) ≤ 3dM` at `M ≥ 1` this is `H_N − H_M ≤ 1 + log(3d)`, so the deviation is
`≤ (3 + log 3d)/d ≤ 2.4`.  The `M = 0` case (`N < d + r`, the class has at most one element)
needs its own line.  `r = 0`: `class_0 = (1/d)·H_{⌊N/d⌋}`, deviation `≤ (1 + log 2d)/d`.
`d = 1`: `remLogCount 1 N = 0` outright (`rho 1 = 1`).  The honest per-class sup is `≈ 2.4`;
`4` is a MAJORANT with slack, not a forced value.  STOP: if `4` does not close, land the
constant the arithmetic gives and REPORT — never widen silently. -/
theorem remLogCount_abs_le {d : ℕ} (hd : 0 < d) :
    |remLogCount d N| ≤ 4 * (rho d : ℝ) := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  have hmaps : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n * (n + 2)), n % d ∈ Rnat d := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact (dvd_iff_mem_Rnat d n).mp hn.2
  have hfib : Clog N d = ∑ r ∈ Rnat d,
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ) := by
    rw [Clog, ← Finset.sum_fiberwise_of_maps_to hmaps (fun n => (1 : ℝ) / (n : ℝ))]
    refine Finset.sum_congr rfl fun r hr => ?_
    congr 1
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, (dvd_iff_mem_Rnat d n).mpr ?_⟩, h2⟩
      rw [h2]
      exact hr
  have hmain : Salt.TwinSieve.nu d * Clog N 1
      = ∑ _r ∈ Rnat d, (1 / (d : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := by
    rw [Finset.sum_const, Rnat_card, Clog_one, Salt.TwinSieve.nu_apply, nsmul_eq_mul]
    ring
  have hdiff : remLogCount d N = ∑ r ∈ Rnat d,
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % d = r), (1 : ℝ) / (n : ℝ))
        - (1 / (d : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) := by
    rw [remLogCount, hfib, hmain, ← Finset.sum_sub_distrib]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (fun r hr => abs_class_sub_harmonic_le hd (Rnat_lt hr) N)) ?_
  rw [Finset.sum_const, Rnat_card, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- **P3b.**  The explicit majorant at the log weight: four times the flat one. -/
noncomputable def BtwinLog (lvl : ℝ) : ℝ := 4 * Btwin lvl

/-- **P3c (class B).**  The harmonic remainders summed below the level (`rho_squarefree_le`,
`sum_two_pow_omega_le`, the `twinRem_sum_le` idiom). -/
theorem twinRemLog_sum_le (hPsq : Squarefree P) {lvl : ℝ} (hlvl : 1 ≤ lvl) :
    (∑ d ∈ P.divisors, if (d : ℝ) < lvl then |remLogCount d N| else 0) ≤ BtwinLog lvl := by
  have hfl : 1 ≤ ⌊lvl⌋₊ := Nat.le_floor (by exact_mod_cast hlvl)
  have hsub : P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl) ⊆ Finset.Icc 1 ⌊lvl⌋₊ := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2.le⟩
  have hstep1 : (∑ d ∈ P.divisors, if (d : ℝ) < lvl then |remLogCount d N| else 0)
      = ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl), |remLogCount d N| := by
    rw [Finset.sum_filter]
  have hstep2 : (∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl), |remLogCount d N|)
      ≤ ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl),
          4 * (2 : ℝ) ^ _root_.omega d := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_filter] at hd
    have h1 : |remLogCount d N| ≤ 4 * (rho d : ℝ) :=
      remLogCount_abs_le (Nat.pos_of_mem_divisors hd.1)
    have h2 : (rho d : ℝ) ≤ (2 : ℝ) ^ _root_.omega d := by
      exact_mod_cast rho_squarefree_le d
        (Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd.1) hPsq)
    linarith
  have hstep3 : (∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < lvl),
        4 * (2 : ℝ) ^ _root_.omega d)
      ≤ ∑ q ∈ Finset.Icc 1 ⌊lvl⌋₊, 4 * (2 : ℝ) ^ _root_.omega q := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro d _ _
    positivity
  have hstep4 : (∑ q ∈ Finset.Icc 1 ⌊lvl⌋₊, 4 * (2 : ℝ) ^ _root_.omega q) ≤ BtwinLog lvl := by
    rw [BtwinLog, Btwin, ← Finset.mul_sum]
    have h : (∑ q ∈ Finset.Icc 1 ⌊lvl⌋₊, (2 : ℝ) ^ _root_.omega q)
        ≤ (⌊lvl⌋₊ : ℝ) * (1 + Real.log (⌊lvl⌋₊ : ℝ)) :=
      _root_.sum_two_pow_omega_le ⌊lvl⌋₊ hfl
    linarith
  rw [hstep1]
  linarith

/-- **P3 (B3-log, class B).**  The assembly: `rosserRemainder ≤ BtwinLog lvl + B`. -/
theorem twinParitySieveLog_rosserRemainder_le {lvl B : ℝ} (hlvl : 1 ≤ lvl)
    (hdisp : LiouvilleTwinDispLog N P lvl B) :
    Salt.Chen.rosserRemainder (twinParitySieveLog N P hP) lvl ≤ BtwinLog lvl + B := by
  have hsplit : Salt.Chen.rosserRemainder (twinParitySieveLog N P hP) lvl
      ≤ (∑ d ∈ P.divisors, if (d : ℝ) < lvl then |remLogCount d N| else 0)
        + ∑ d ∈ P.divisors,
            (if (d : ℝ) < lvl then |Llog N d - Salt.TwinSieve.nu d * Llog N 1| else 0) := by
    rw [Salt.Chen.rosserRemainder, twinParitySieveLog_prodPrimes, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases h : (d : ℝ) < lvl
    · rw [if_pos h, if_pos h, if_pos h, rem_split_log d]
      exact abs_sub _ _
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have h1 : (∑ d ∈ P.divisors, if (d : ℝ) < lvl then |remLogCount d N| else 0)
      ≤ BtwinLog lvl := twinRemLog_sum_le hP hlvl
  have h2 : (∑ d ∈ P.divisors,
      (if (d : ℝ) < lvl then |Llog N d - Salt.TwinSieve.nu d * Llog N 1| else 0)) ≤ B := hdisp
  linarith

/-- **P4 (B4-log, class A).**  The quantitative pre-terminal at the log weight (the §7
verdict-4 form, adopted directly — no disjunctive terminal is minted). -/
theorem twinParitySieveLog_siftedSum_lower {z B : ℝ} (Q : ℝ) (hQ : 1 ≤ Q)
    (hz : Salt.BrunLower.zThresh (1 / 4) ≤ z)
    (hzprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < z)
    (hdisp : LiouvilleTwinDispLog N P
      (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
            * Real.log z)
          * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
              - 1 : ℕ))) B) :
    (twinParitySieveLog N P hP).totalMass * Salt.BrunLower.W (twinParitySieveLog N P hP)
          * (1 - 2 * (1 / 4 : ℝ) ^ (2 * 1 : ℕ) * Real.exp (2 * (1 / 4))
              / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4))))
        - (BtwinLog (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
              * Real.log z)
            * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
                - 1 : ℕ))) + B)
      ≤ (twinParitySieveLog N P hP).siftedSum := by
  have hdoor := twinParitySieveLog_brun_lower_ell1 (N := N) (P := P) (hP := hP) (z := z) Q hQ hz
    hzprimes
  have hrem := twinParitySieveLog_rosserRemainder_le (N := N) (P := P) (hP := hP)
    (one_le_ell1_level (z := z) Q hQ hz) hdisp
  linarith

/-- **P5 (class B).**  The log sieve's sifted sum IS the landed `twinLogWeight` partial sum
(`sum_twinLogWeight_range`), so the landed tail-mass infinitude consumes it. -/
theorem twinParitySieveLog_siftedSum_eq :
    (twinParitySieveLog N P hP).siftedSum
      = ∑ n ∈ Finset.range (N + 1), twinLogWeight P n := by
  classical
  rw [sum_twinLogWeight_range]
  change (∑ m ∈ (Finset.Icc 1 N).image (fun n => n * (n + 2)),
      if Nat.Coprime P m then
        (1 - ((ArithmeticFunction.liouville m : ℤ) : ℝ)) / (twinIdx m : ℝ) else 0) = _
  rw [Finset.sum_image (fun a _ b _ h => Salt.TwinSieve.twinProd_injective h),
    ← Finset.sum_filter]
  have hfe : (Finset.Icc 1 N).filter (fun n => Nat.Coprime P (n * (n + 2)))
      = (Finset.Icc 1 N).filter (fun n => Nat.Coprime (n * (n + 2)) P) :=
    Finset.filter_congr (fun n _ => by rw [Nat.coprime_comm])
  rw [hfe]
  exact Finset.sum_congr rfl fun n _ => by rw [twinIdx_twinProd]

/-- **P6 (class B) — the log-world door wired to INFINITUDE.**  If, along `N`, the arithmetic
input holds at a `B N` and the margin `mainTerm N − BtwinLog − B N` is unbounded, the sifted
support is infinite.  Consumer: `support_infinite_of_partialSums_unbounded` (`:607`, obligation
`∀ M, ∃ N, M < ∑ n ∈ range N, w n`) with wave 1's witness idiom `refine ⟨N + 1, ?_⟩` then
`rw [← twinParitySieveLog_siftedSum_eq]` (`twinLogWeight_support_infinite_of_win`,
`:1341-1345`) — NOT `support_infinite_of_lower_unbounded`, whose `hlow` is over `range N`
while P5 delivers `range (N + 1)`: the `+1` is absorbed in the existential, where it is free.
⛔ Both inputs are HYPOTHESES: `Llog N 1 = o(H_N)` (Tao at shift 2, full range — NOT the
corpus's windowed atom) and `B N = o(H_N)` (binder C). -/
theorem twinParitySieveLog_support_infinite {z : ℝ} (Q : ℝ) (hQ : 1 ≤ Q)
    (hz : Salt.BrunLower.zThresh (1 / 4) ≤ z)
    (hzprimes : ∀ p ∈ P.primeFactors, (p : ℝ) < z) {B : ℕ → ℝ}
    (hdisp : ∀ N, LiouvilleTwinDispLog N P
      (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
            * Real.log z)
          * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
              - 1 : ℕ))) (B N))
    (hdiv : ∀ M : ℝ, ∃ N : ℕ, M <
      (twinParitySieveLog N P hP).totalMass * Salt.BrunLower.W (twinParitySieveLog N P hP)
          * (1 - 2 * (1 / 4 : ℝ) ^ (2 * 1 : ℕ) * Real.exp (2 * (1 / 4))
              / (1 - (1 / 4 : ℝ) ^ 2 * Real.exp (2 + 2 * (1 / 4))))
        - (BtwinLog (Q * (Real.exp ((1 + 2 * (Real.exp (Salt.BrunLower.LamTwin (1 / 4) z) - 1)⁻¹)
              * Real.log z)
            * 2 ^ (2 * Salt.BrunLower.minLevel (Salt.BrunLower.LamTwin (1 / 4) z) z
                - 1 : ℕ))) + B N)) :
    {n : ℕ | twinLogWeight P n ≠ 0}.Infinite := by
  refine support_infinite_of_partialSums_unbounded (twinLogWeight_nonneg P) fun M => ?_
  obtain ⟨N, hN⟩ := hdiv M
  refine ⟨N + 1, ?_⟩
  rw [← twinParitySieveLog_siftedSum_eq (N := N) (P := P) (hP := hP)]
  exact lt_of_lt_of_le hN
    (twinParitySieveLog_siftedSum_lower (N := N) (P := P) (hP := hP) (z := z) Q hQ hz
      hzprimes (hdisp N))


end Salt.TwinBar
