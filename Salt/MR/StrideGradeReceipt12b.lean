/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# (B1) β W4 H1 — THE GRADED CROWN AT `2^12`, CAP 9, FED INTO THE GRADED HEAD

Build freeze v2 v1.1 (2026-09-13), §3.1 rule 6: the receipt / terminals of β live in THIS new
module (importing `StrideGradeReceipt` and `StridePairReceiptG12b`), the one place both sides of
the `2^12` graded lane are in scope.

`log_chowla_aff_of_door_crowned_unslotted_g12b` is `log_chowla_aff_of_door_crowned_unslotted_g`
(`StrideGradeReceipt.lean:46`) with ONLY the freeze's §3.1 rule-2 raises: the product cap
`log (a·h) ≤ 7 ↦ ≤ 9`, the head `log_chowla_aff_of_door_unslotted_g ↦ …_g12b` and the crown
`mrtUniformityXiL2AffW_holds_flat_stride_g ↦ …_g12b` (ceiling `837782 * 2 ^ 12`); its conclusion
is `GradedAffHeadAt_g12b a b h A₀` (`StridePrize.lean`), the binder
`log_chowla_aff_composed_of_headG_g12b` composes at.  No hypothesis is added: the crown derives
its own stride bound `a ≤ 8103` from the product cap (freeze §3.0).  No landed declaration moves.

HONEST LABEL.  One one-line application at the new names; nothing here proves a new estimate, and
nothing bears on twin primes.
-/
import Salt.MR.StrideGradeReceipt
import Salt.MR.StridePairReceiptG12b
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **⟦β W34 H1⟧ F5-β-S6 at `2^12` and cap 9 — the graded crown fed into the graded unslotted head,
concluding `GradedAffHeadAt_g12b`.**  `log_chowla_aff_of_door_crowned_unslotted_g`
(StrideGradeReceipt.lean:46) at the `_g12b` names (census band 4 row 14: SUPPLIER-SWAP):
`unfold GradedAffHeadAt_g12b; exact log_chowla_aff_of_door_unslotted_g12b a b h ha hh hba hgcd hah9
(fun A₀' => mrtUniformityXiL2AffW_holds_flat_stride_g12b a b h ha hh hba hah9 A₀') A₀`.  The
`unfold` is the K-check: `GradedAffHeadAt_g12b`'s body must be the graded head's conclusion byte for
byte. -/
theorem log_chowla_aff_of_door_crowned_unslotted_g12b (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hba : b < a) (hgcd : Nat.gcd (b + h) a ∣ h)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (A₀ : ℝ) :
    GradedAffHeadAt_g12b a b h A₀ := by
  unfold GradedAffHeadAt_g12b
  exact log_chowla_aff_of_door_unslotted_g12b a b h ha hh hba hgcd hah9
    (fun A₀' => mrtUniformityXiL2AffW_holds_flat_stride_g12b a b h ha hh hba hah9 A₀') A₀

/-! ## ⟦β W34 H3⟧ — THE W4 TERMINALS: THE PER-CLASS STATEMENTS (D) AND (Q) AT `primorial z ≤ 2310`

Per-class freeze v1.1 §2 (2026-09-13): the statements `zRough_oddOmega_logMass_class` (D) and
`zRough_oddOmega_infinite_class` (Q) are spelled exactly as frozen there.  (D)'s proof is the
refuter probe's route (`r3_D_epsFloor_548`) at the `2^12`, cap-9 names: the crowned head
`log_chowla_aff_of_door_crowned_unslotted_g12b` at `(a, b, h) := (primorial z, r, 2)`, composed by
`log_chowla_aff_composed_of_headG_g12b` (its granted `a ≤ 2310` is `hz`), then
`affWindow_survivorMass_ge`, the parity split `one_sub_liouville_shift_two`, the floor
`64000·P + 1 ≤ log ω` from the regime's `hωbig`, and the rough-filter congruence.  (Q) follows from
(D) with no cap.

CLAIM LABEL (freeze §6).  (D) at a fixed modulus `P = primorial z` is an instance of Tao,
arXiv:1509.05422 (Thm 1.3; Thm 2.3 is the stride form), at `a₁ = a₂ = P`, `b₂ = b₁ + 2`, with weight
`1/k` in the CLASS INDEX `k` (in `1/m`, `m = P·k + r`, the sentence is false by a factor `P`).  What
is here is a kernel-checked derivation of that instance at `primorial z ≤ 2310`, one
`ε = 1/(1000·P)`, in the ∃-window form at floor `log ω ≥ 64000·P + 1`; the content is the
derivation, not the statement.  (Q) also has an elementary proof at each `z` where a seed table is
computed (`zRough_oddOmega_infinite_class_of_seed`).  Nothing here is about primes or twin primes:
`z`-rough with `Ω` odd is not almost-primality.
-/

/-- **⟦β W34 H3⟧ the cap numeral.**  `primorial z ≤ 2310 ⇒ log (primorial z · 2) ≤ 9`:
`primorial z · 2 ≤ 4620 ≤ 2.7182818283 ^ 9 ≤ (exp 1) ^ 9 = exp 9` (`Real.exp_one_gt_d9`). -/
theorem hah9_of_primorial_le_2310 {z : ℕ} (hz : primorial z ≤ 2310) :
    Real.log ((primorial z * 2 : ℕ) : ℝ) ≤ 9 := by
  have hpz : 0 < primorial z := primorial_pos z
  have hle : primorial z * 2 ≤ 4620 := by omega
  have hR : ((primorial z * 2 : ℕ) : ℝ) ≤ 4620 := by exact_mod_cast hle
  have hR0 : (0 : ℝ) < ((primorial z * 2 : ℕ) : ℝ) := by
    have hpos : 0 < primorial z * 2 := by omega
    exact_mod_cast hpos
  have he9 : (4620 : ℝ) ≤ Real.exp 9 := by
    have h3 : Real.exp 9 = (Real.exp 1) ^ (9 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h5 : (2.7182818283 : ℝ) ^ (9 : ℕ) ≤ (Real.exp 1) ^ (9 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) h4.le 9
    have h6 : (4620 : ℝ) ≤ (2.7182818283 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [h3]; linarith
  calc Real.log ((primorial z * 2 : ℕ) : ℝ) ≤ Real.log (Real.exp 9) :=
      Real.log_le_log hR0 (by linarith)
    _ = 9 := Real.log_exp 9

/-- **⟦β W34 H3⟧ the parity split.**  For `0 < m`, `1 − λ(m)·λ(m+2)` is `2` when `Ω(m(m+2))` is odd
and `0` otherwise (`liouville_mul`, then `(-1)^Ω` by parity). -/
theorem one_sub_liouville_shift_two {m : ℕ} (hm : 0 < m) :
    (1 - (ArithmeticFunction.liouville m : ℝ) * (ArithmeticFunction.liouville (m + 2) : ℝ))
      = if Odd (ArithmeticFunction.cardFactors (m * (m + 2))) then 2 else 0 := by
  have hne : m * (m + 2) ≠ 0 := Nat.mul_ne_zero hm.ne' (by omega)
  have hkey : (ArithmeticFunction.liouville m : ℝ) * (ArithmeticFunction.liouville (m + 2) : ℝ)
      = (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (m * (m + 2))) := by
    have hz := liouville_mul m (m + 2)
    rw [ArithmeticFunction.liouville_apply hne] at hz
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at hr
    exact hr.symm
  rw [hkey]
  split_ifs with hod
  · rw [hod.neg_one_pow]; norm_num
  · rw [(Nat.not_odd_iff_even.mp hod).neg_one_pow]; norm_num

/-- **⟦β W34 H3⟧ the rough-filter congruence.**  Under `Nat.Coprime (r(r+2)) (primorial z)` every
`(P·k + r)(P·k + r + 2)` is `z`-rough (`coprime_twinProd_of_affine`, `rough_of_coprime_primorial`),
so the rough∧odd filter over `Ioc (x/ω) x` equals the odd filter (`Finset.filter_congr`). -/
theorem roughOdd_filter_eq_odd_filter {z r : ℕ} (hcop : Nat.Coprime (r * (r + 2)) (primorial z))
    (x ω : ℕ) :
    ∑ k ∈ (Finset.Ioc (x / ω) x).filter
        (fun k => (∀ p ∈ ((primorial z * k + r) * (primorial z * k + r + 2)).primeFactors, z < p)
          ∧ Odd (ArithmeticFunction.cardFactors
            ((primorial z * k + r) * (primorial z * k + r + 2)))), (1 : ℝ) / (k : ℝ)
      = ∑ k ∈ (Finset.Ioc (x / ω) x).filter
        (fun k => Odd (ArithmeticFunction.cardFactors
          ((primorial z * k + r) * (primorial z * k + r + 2)))), (1 : ℝ) / (k : ℝ) := by
  rw [Finset.filter_congr (fun k _ => ⟨fun h => h.2,
    fun h => ⟨rough_of_coprime_primorial (coprime_twinProd_of_affine hcop k), h⟩⟩)]

/-- **⟦β W34 H3⟧ (D) — the class's weighted log-mass, per-class freeze v1.1 §2.**  For
`P = primorial z ≤ 2310` and an admissible class `r` (`Nat.Coprime (r(r+2)) P`): beyond every `M`
there is a window `(x/ω, x]` with `log ω ≥ 64000·P + 1` in which `Σ 1/k`, over class indices `k`
whose `m = P·k + r` has `m(m+2)` `z`-rough with `Ω` odd, is at least `(1 − ε)/2 · log ω − 1/2` at
`ε = 1/(1000·P)`.  The weight is `1/k` in the class index.  An instance of Tao, arXiv:1509.05422
(Thm 1.3 / Thm 2.3) at fixed modulus; the content here is the kernel derivation.  Nothing about
twin primes. -/
theorem zRough_oddOmega_logMass_class {z r : ℕ} (hz : primorial z ≤ 2310) (hr : r < primorial z)
    (hcop : Nat.Coprime (r * (r + 2)) (primorial z)) :
    ∀ M : ℕ, ∃ x ω : ℕ, M < x / ω ∧ 64000 * (primorial z : ℝ) + 1 ≤ Real.log (ω : ℝ) ∧
      (1 - 1 / (1000 * (primorial z : ℝ))) / 2 * Real.log (ω : ℝ) - 1 / 2 ≤
        ∑ k ∈ (Finset.Ioc (x / ω) x).filter
            (fun k => (∀ p ∈ ((primorial z * k + r) * (primorial z * k + r + 2)).primeFactors,
                z < p)
              ∧ Odd (ArithmeticFunction.cardFactors
                ((primorial z * k + r) * (primorial z * k + r + 2)))), (1 : ℝ) / (k : ℝ) := by
  intro M
  have hpz : 0 < primorial z := primorial_pos z
  have hah9 := hah9_of_primorial_le_2310 hz
  obtain ⟨A₀, hA₀⟩ := flatDesignBase_unbounded (M : ℝ)
  have hhead := log_chowla_aff_of_door_crowned_unslotted_g12b (primorial z) r 2 hpz two_pos hr
    (gcd_dvd_two_of_coprime hcop) hah9 A₀
  obtain ⟨ε, A, -, hεeq, -, hA₀A, Ra, -, -, hRaeps, hHlo, -, hnf⟩ :=
    log_chowla_aff_composed_of_headG_g12b (primorial z) r 2 hpz two_pos hah9 hz A₀ hhead
  have heps : ((Ra.eps : ℚ) : ℝ) = 1 / (1000 * (primorial z : ℝ)) := by
    rw [hRaeps, hεeq]; push_cast; ring
  have hPR : (0 : ℝ) < (primorial z : ℝ) := by exact_mod_cast hpz
  refine ⟨Ra.x, Ra.ω, ?_, ?_, ?_⟩
  · have hbaseR : (M : ℝ) < ((flatDesignBase A : ℕ) : ℝ) := hA₀ A hA₀A
    have hbase : M < flatDesignBase A := by exact_mod_cast hbaseR
    exact lt_of_lt_of_le hbase (le_trans hHlo (le_trans Ra.hHlohi Ra.hheadroom))
  · -- ⟦the floor, from `hωbig` exactly as `regime_logOmega_ge` runs it, keeping `64/ε`⟧
    have hεpos : (0 : ℝ) < ((Ra.eps : ℚ) : ℝ) := by exact_mod_cast Ra.heps
    have hHloR : (4000000 : ℝ) ≤ (Ra.Hlo : ℝ) := by exact_mod_cast Ra.hHlo_floor
    have hsqrt : (2000 : ℝ) ≤ Real.sqrt (Ra.Hlo : ℝ) := by
      have h : Real.sqrt (4000000 : ℝ) ≤ Real.sqrt (Ra.Hlo : ℝ) := Real.sqrt_le_sqrt hHloR
      rwa [show (4000000 : ℝ) = 2000 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2000)] at h
    have hw := Ra.hPNTwindow
    have h4000 : (4000 : ℝ) ≤ ((Ra.eps : ℚ) : ℝ) ^ 2 * (Ra.Hlo : ℝ) := by linarith
    have hHle : (Ra.Hlo : ℝ) ≤ (Ra.Hhi : ℝ) := by exact_mod_cast Ra.hHlohi
    have hmono : ((Ra.eps : ℚ) : ℝ) ^ 2 * (Ra.Hlo : ℝ) ≤ ((Ra.eps : ℚ) : ℝ) ^ 2 * (Ra.Hhi : ℝ) :=
      mul_le_mul_of_nonneg_left hHle (sq_nonneg _)
    have hlogpos : (0 : ℝ) ≤ Real.log (((Ra.eps : ℚ) : ℝ) ^ 2 * (Ra.Hhi : ℝ)) :=
      Real.log_nonneg (by linarith)
    have h16 : (0 : ℝ) ≤
        16 / ((Ra.eps : ℚ) : ℝ) * Real.log (((Ra.eps : ℚ) : ℝ) ^ 2 * (Ra.Hhi : ℝ)) :=
      mul_nonneg (by positivity) hlogpos
    have h64 : 64 / ((Ra.eps : ℚ) : ℝ) = 64000 * (primorial z : ℝ) := by
      rw [heps]; field_simp; ring
    have hwb := Ra.hωbig
    linarith [hwb]
  · rw [roughOdd_filter_eq_odd_filter hcop]
    have hmass := affWindow_survivorMass_ge Ra.hx Ra.hω Ra.hωx hnf
    have hdpos : 0 < Ra.x / Ra.ω := Nat.div_pos Ra.hωx (by have := Ra.hω; omega)
    have hsplit : ∑ k ∈ Finset.Ioc (Ra.x / Ra.ω) Ra.x,
        (1 - (ArithmeticFunction.liouville (primorial z * k + r) : ℝ)
          * (ArithmeticFunction.liouville (primorial z * k + r + 2) : ℝ)) / (k : ℝ)
        = 2 * ∑ k ∈ (Finset.Ioc (Ra.x / Ra.ω) Ra.x).filter
            (fun k => Odd (ArithmeticFunction.cardFactors
              ((primorial z * k + r) * (primorial z * k + r + 2)))), (1 : ℝ) / (k : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Ioc] at hk
      have hkpos : 0 < k := lt_trans hdpos hk.1
      have hmpos : 0 < primorial z * k + r :=
        lt_of_lt_of_le (Nat.mul_pos hpz hkpos) (Nat.le_add_right _ _)
      rw [one_sub_liouville_shift_two hmpos]
      split_ifs <;> ring
    rw [hsplit, heps] at hmass
    linarith

/-- **⟦β W34 H3⟧ (Q) — infinitely many in the class, per-class freeze v1.1 §2.**  For
`primorial z ≤ 2310` and an admissible class `r`, infinitely many `n ≡ r (mod primorial z)` have
`n(n+2)` `z`-rough with `Ω` odd.  Derived from (D) (`zRough_oddOmega_logMass_class`): a bounded set
would leave (D)'s filter empty in a window beyond the bound, against the floor `64000·P + 1`.  (Q)
also has an elementary proof at each `z` where a seed table is computed
(`zRough_oddOmega_infinite_class_of_seed`).  Nothing about twin primes. -/
theorem zRough_oddOmega_infinite_class {z r : ℕ} (hz : primorial z ≤ 2310) (hr : r < primorial z)
    (hcop : Nat.Coprime (r * (r + 2)) (primorial z)) :
    {n : ℕ | n % primorial z = r ∧ (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  have hD := zRough_oddOmega_logMass_class hz hr hcop
  have hpz : 0 < primorial z := primorial_pos z
  have hPR : (1 : ℝ) ≤ (primorial z : ℝ) := by exact_mod_cast hpz
  apply Set.infinite_of_not_bddAbove
  intro hbdd
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨x, ω, hMx, hlog, hmass⟩ := hD M
  have hε : 1 / (1000 * (primorial z : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hq : (1 / 4 : ℝ) * Real.log (ω : ℝ)
      ≤ (1 - 1 / (1000 * (primorial z : ℝ))) / 2 * Real.log (ω : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  obtain ⟨k, hk⟩ : ((Finset.Ioc (x / ω) x).filter
      (fun k => (∀ p ∈ ((primorial z * k + r) * (primorial z * k + r + 2)).primeFactors, z < p)
        ∧ Odd (ArithmeticFunction.cardFactors
          ((primorial z * k + r) * (primorial z * k + r + 2))))).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hmass
    linarith
  rw [Finset.mem_filter, Finset.mem_Ioc] at hk
  obtain ⟨⟨hk1, -⟩, hrough, hodd⟩ := hk
  have hmem : primorial z * k + r ∈ {n : ℕ | n % primorial z = r
      ∧ (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))} := by
    refine ⟨?_, hrough, hodd⟩
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hub := hM hmem
  have hkle : k ≤ primorial z * k + r :=
    le_trans (Nat.le_mul_of_pos_left k hpz) (Nat.le_add_right _ _)
  omega

/-- **⟦β W34 H3⟧ CONTROL — the class-`(r + 1)` mutant of (D) is FALSE** at `z = 10`, `r = 11`
(class `12`, admissible `r = 11`: `11 · 13` is coprime to `210`).  Witness: `2 ∣ 210·k + 12`, so
the rough filter is EMPTY in every window, the sum is `0`, and `0 < (1 − ε)/2 · log ω − 1/2` once
`log ω ≥ 64000 · 210 + 1`. -/
theorem zRough_oddOmega_logMass_class_mutant_false :
    ¬ (∀ M : ℕ, ∃ x ω : ℕ, M < x / ω ∧ 64000 * (primorial 10 : ℝ) + 1 ≤ Real.log (ω : ℝ) ∧
      (1 - 1 / (1000 * (primorial 10 : ℝ))) / 2 * Real.log (ω : ℝ) - 1 / 2 ≤
        ∑ k ∈ (Finset.Ioc (x / ω) x).filter
            (fun k => (∀ p ∈ ((primorial 10 * k + (11 + 1))
                * (primorial 10 * k + (11 + 1) + 2)).primeFactors, 10 < p)
              ∧ Odd (ArithmeticFunction.cardFactors
                ((primorial 10 * k + (11 + 1)) * (primorial 10 * k + (11 + 1) + 2)))),
            (1 : ℝ) / (k : ℝ)) := by
  intro h
  obtain ⟨x, ω, -, hlog, hmass⟩ := h 0
  have hP : primorial 10 = 210 := by decide
  have hempty : (Finset.Ioc (x / ω) x).filter
      (fun k => (∀ p ∈ ((primorial 10 * k + (11 + 1))
          * (primorial 10 * k + (11 + 1) + 2)).primeFactors, 10 < p)
        ∧ Odd (ArithmeticFunction.cardFactors
          ((primorial 10 * k + (11 + 1)) * (primorial 10 * k + (11 + 1) + 2)))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k _ hk
    have h2 : 2 ∈ ((primorial 10 * k + (11 + 1))
        * (primorial 10 * k + (11 + 1) + 2)).primeFactors := by
      rw [Nat.mem_primeFactors, hP]
      refine ⟨Nat.prime_two, Dvd.dvd.mul_right (by omega) _, Nat.mul_ne_zero (by omega) (by omega)⟩
    have := hk.1 2 h2
    omega
  rw [hempty, Finset.sum_empty, hP] at hmass
  rw [hP] at hlog
  norm_num at hmass hlog
  linarith

/-- **⟦β W34 H3⟧ NON-VACUITY — (D) instantiated at `z = 10`, `r = 209 = primorial 10 − 1`.** -/
example : ∀ M : ℕ, ∃ x ω : ℕ, M < x / ω ∧ 64000 * (primorial 10 : ℝ) + 1 ≤ Real.log (ω : ℝ) ∧
      (1 - 1 / (1000 * (primorial 10 : ℝ))) / 2 * Real.log (ω : ℝ) - 1 / 2 ≤
        ∑ k ∈ (Finset.Ioc (x / ω) x).filter
            (fun k => (∀ p ∈ ((primorial 10 * k + 209) * (primorial 10 * k + 209 + 2)).primeFactors,
                10 < p)
              ∧ Odd (ArithmeticFunction.cardFactors
                ((primorial 10 * k + 209) * (primorial 10 * k + 209 + 2)))), (1 : ℝ) / (k : ℝ) := by
  have hP : primorial 10 = 210 := by decide
  have hcop : Nat.Coprime (209 * (209 + 2)) (primorial 10) := by rw [hP]; norm_num
  exact zRough_oddOmega_logMass_class (z := 10) (r := 209) (by rw [hP]; norm_num)
    (by rw [hP]; norm_num) hcop

end Salt.MR
