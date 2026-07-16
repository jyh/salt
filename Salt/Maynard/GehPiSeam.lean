/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehDoor
import Salt.Maynard.Level
import Salt.Maynard.EHConsume
import Salt.BV.AbelCore

/-!
# The GEH π-seam consumer (design node D-N2c)

This file consumes the landed π-seam `maxDiscrepancy_le_seqDiscrepancy_prime`
(`Salt/Maynard/GehDoor.lean`) to convert a level-of-distribution bound stated on
the **coprime-mean sequence discrepancy** back to the landed **π-based**
`maxDiscrepancy` target that `HasLevel` (`Salt/Maynard/Level.lean`) sums.

## The three steps

1. **Λ → 1_prime (Abel transfer, `PiLevel` from `LambdaLevel`).** Partial
   summation (`primesCount_abel`-style, `Salt/BV/AbelCore.lean`) turns the
   Λ-weighted sequence discrepancy into the prime-indicator one, at the cost of
   the `1/log` weight and the prime-power correction `ppTerm`.  This step is
   **NOT closed from the point-wise `LambdaLevel` hypothesis** and is carried as
   a named bridge; see the honesty note below.
2. **The seam summed (`sum_seam_le`, complete).**  The per-`q` seam cost
   `ω(q)/φ(q)` summed over the haircut range is polylog, via the landed
   `Salt.BV.sum_omega_mul_le` at `L = 1`.
3. **Assembly (`hasLevel_of_piLevel`, complete).**  The seam
   `maxDiscrepancy x q ≤ seqDiscrepancy 1_prime x q + ω(q)/φ(q)` summed, plus the
   polylog absorption of step 2 via `Salt.BV.absorb_nat`, lands `HasLevel θ` from
   `PiLevel θ`.

## Honesty note — the y-uniformity gap in step 1

The Abel transfer bounds `seqDiscrepancy 1_prime x q` by an Abel transform of
`seqDiscrepancy Λ i q` over **all prefixes `i ≤ x`** at the **fixed** x-scaled
cutoff `Q = ⌊x^θ/(log x)^B⌋`.  Summing over `q ≤ Q` needs
`∑_{q≤Q} seqDiscrepancy Λ i q` for every `i ≤ x` — a **y-uniform** bound over the
x-cutoff.  The `LambdaLevel` interface (as spelled in D-N2a) is point-wise: at
scale `i` it only bounds `∑_{q ≤ ⌊i^θ/(log i)^B⌋} seqDiscrepancy Λ i q` over the
smaller *i-scaled* cutoff, leaving `q ∈ (⌊i^θ/…⌋, Q]` uncontrolled.  So step 1
genuinely needs the y-uniform strengthening of `LambdaLevel` (which the GEH
machinery of D-N2a in fact provides, mirroring the ψ-keystone shape of
`Salt/BV/PsiToPi.lean`'s `PsiToPiTransfer` hypothesis `∀ x y, y ≤ x → …`).  This
file therefore closes steps 2+3 unconditionally and takes the step-1 Abel bridge
as a hypothesis, to be discharged at house assembly.  See
`docs/blueprints/flags.md`, the D-N2c entry.
-/

open Finset

/-- **The prime-indicator level of distribution** (`PiLevel θ`).  Same shape as
`LambdaLevel θ` but on the coprime-mean sequence discrepancy of the prime
indicator `1_prime` rather than the von Mangoldt weight.  This is the π-side of
the Abel transfer (step 1 of the module); `hasLevel_of_piLevel` consumes it. -/
def PiLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
        seqDiscrepancy (fun n => if n.Prime then (1 : ℝ) else 0) x q)
      ≤ C * x / Real.log x ^ A

/-! ## Step 2 — the seam sum is polylog -/

/-- **The π-seam sum.**  The per-`q` seam cost `ω(q)/φ(q)` summed over the haircut
range is `≤ (logb 2 Q)·4(1+log Q)`.  Instantiates `Salt.BV.sum_omega_mul_le` at
`L = 1`. -/
lemma sum_seam_le {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ) / (q.totient : ℝ)
      ≤ Real.logb 2 Q * (4 * (1 + Real.log Q)) := by
  have h := Salt.BV.sum_omega_mul_le hQ (L := (1 : ℝ)) (by norm_num)
  simp only [mul_one] at h
  exact h

/-- **The seam sum is polylog-absorbable.**  Over the haircut range at cutoff
`⌊x^θ/(log x)^B⌋`, the seam sum is `≤ 6·(1 + log x)²`.  For `x ≥ 3` the cutoff is
`≤ x` (as `θ ≤ 1` and `(log x)^B ≥ 1`), so `logb 2 Q ≤ log x / log 2` and
`log Q ≤ log x`; the constant `6` absorbs `4/log 2 < 6`. -/
lemma seam_le_polylog {θ : ℝ} (hθ1 : θ ≤ 1) {x : ℕ} (hx3 : 3 ≤ x) (B : ℝ) (hB : 0 ≤ B) :
    ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
        (q.primeFactors.card : ℝ) / (q.totient : ℝ)
      ≤ 6 * (1 + Real.log x) ^ 2 := by
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLx1 : (1 : ℝ) ≤ Real.log x := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hLx0 : (0 : ℝ) ≤ Real.log x := by linarith
  set Q := ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊ with hQdef
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
  · rw [hQ0, show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl, Finset.sum_empty]
    positivity
  · have hQ1 : 1 ≤ Q := hQpos
    -- the cutoff is `≤ x`
    have hLBge1 : (1 : ℝ) ≤ Real.log x ^ B := by
      calc (1 : ℝ) = Real.log x ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ Real.log x ^ B := Real.rpow_le_rpow_of_exponent_le hLx1 hB
    have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ θ := Real.rpow_nonneg hxpos.le θ
    have hxθle : (x : ℝ) ^ θ ≤ (x : ℝ) := by
      calc (x : ℝ) ^ θ ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hθ1
        _ = (x : ℝ) := Real.rpow_one _
    have hdivle : (x : ℝ) ^ θ / Real.log x ^ B ≤ (x : ℝ) := by
      calc (x : ℝ) ^ θ / Real.log x ^ B ≤ (x : ℝ) ^ θ / 1 := by
            apply div_le_div_of_nonneg_left hxθnn (by norm_num) hLBge1
        _ = (x : ℝ) ^ θ := by rw [div_one]
        _ ≤ (x : ℝ) := hxθle
    have hQx : (Q : ℝ) ≤ (x : ℝ) :=
      le_trans (Nat.floor_le (by positivity)) hdivle
    have hlogQnn : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ1)
    have hlogQx : Real.log Q ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast hQpos) hQx
    -- combine the seam sum with the numeric absorb
    refine le_trans (sum_seam_le hQ1) ?_
    have hA : Real.log Q * (4 * (1 + Real.log Q)) ≤ Real.log x * (4 * (1 + Real.log x)) :=
      mul_le_mul hlogQx (by linarith) (by linarith) hLx0
    have hB' : Real.log x * (4 * (1 + Real.log x)) ≤ 6 * (1 + Real.log x) ^ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9, hLx0, sq_nonneg (1 + Real.log x), mul_nonneg hLx0 hLx0]
    rw [Real.logb, div_mul_eq_mul_div, div_le_iff₀ hlog2]
    exact le_trans hA hB'

/-! ## The crude small-`x` absorber -/

/-- **Crude π-discrepancy sum bound** (cutoff-generic).  Over `Icc 1 Q`, the summed
`maxDiscrepancy` is `≤ Q·(x+1)`: each `maxDiscrepancy x q ≤ x/φq + 1 ≤ x + 1`
(`Salt.Maynard.maxDiscrepancy_le_trivial`, `φq ≥ 1`), over `Q` moduli.  Mirrors
`Salt.BV.sum_maxDiscrepancy_crude`, feeds the finite small-`x` constant. -/
lemma sum_maxDiscrepancy_crude_gen (x Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, maxDiscrepancy x q ≤ (Q : ℝ) * ((x : ℝ) + 1) := by
  calc ∑ q ∈ Finset.Icc 1 Q, maxDiscrepancy x q
      ≤ ∑ _q ∈ Finset.Icc 1 Q, ((x : ℝ) + 1) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [Finset.mem_Icc] at hq
        have hqpos : 0 < q := by omega
        have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
          have : 1 ≤ q.totient := Nat.totient_pos.mpr hqpos
          exact_mod_cast this
        calc maxDiscrepancy x q ≤ (x : ℝ) / (q.totient : ℝ) + 1 :=
              Salt.Maynard.maxDiscrepancy_le_trivial x q
          _ ≤ (x : ℝ) + 1 := by
              have : (x : ℝ) / (q.totient : ℝ) ≤ (x : ℝ) := div_le_self (by positivity) hφ1
              linarith
    _ = (Q : ℝ) * ((x : ℝ) + 1) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast [Nat.add_sub_cancel]; ring

/-! ## Step 3 — assembly: `HasLevel θ` from `PiLevel θ` -/

/-- **`HasLevel θ` from the prime-indicator level `PiLevel θ`** (steps 2+3,
complete).  Sum the landed π-seam `maxDiscrepancy x q ≤ seqDiscrepancy 1_prime x q
+ ω(q)/φ(q)` over the haircut range: the first sum is `PiLevel`-controlled, the
seam sum is polylog (`seam_le_polylog`) and is absorbed into `x/(log x)^A` for
large `x` (`Salt.BV.absorb_nat`), with the finite small-`x` range folded into a
constant `Csm` (as in `Salt/BV/PsiToPi.lean`). -/
theorem hasLevel_of_piLevel {θ : ℝ} (hθ1 : θ ≤ 1) (hP : PiLevel θ) : HasLevel θ := by
  intro A hA
  obtain ⟨B, C, hB, hbnd⟩ := hP A hA
  have habs := Salt.BV.absorb_nat (θ := (0 : ℝ)) (k := (2 : ℝ)) (A := A) (M := (6 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨x₀, hx₀⟩ :=
    Filter.eventually_atTop.mp (habs.and (Filter.eventually_ge_atTop 3))
  set Csm : ℝ := ∑ x' ∈ Finset.Icc 2 x₀,
      (⌊(x' : ℝ) ^ θ / Real.log x' ^ B⌋₊ : ℝ) * ((x' : ℝ) + 1) * Real.log x' ^ A / x'
    with hCsmdef
  have hterm_nn : ∀ x' ∈ Finset.Icc 2 x₀,
      0 ≤ (⌊(x' : ℝ) ^ θ / Real.log x' ^ B⌋₊ : ℝ) * ((x' : ℝ) + 1) * Real.log x' ^ A / x' := by
    intro x' _
    have hlog : (0 : ℝ) ≤ Real.log x' := Real.log_natCast_nonneg x'
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Real.rpow_nonneg hlog A))
      (by positivity)
  have hCsm0 : 0 ≤ Csm := Finset.sum_nonneg hterm_nn
  refine ⟨B, max (C + 1) Csm, hB, fun x hx => ?_⟩
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLApos : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hLpos A
  set t : ℝ := (x : ℝ) / Real.log x ^ A with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  rw [show max (C + 1) Csm * (x : ℝ) / Real.log x ^ A = max (C + 1) Csm * t by rw [htdef]; ring]
  by_cases hxx : x₀ ≤ x
  · obtain ⟨habsx, hx3⟩ := hx₀ x hxx
    rw [Real.rpow_zero, mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at habsx
    have hpi := hbnd x hx
    have hseam := seam_le_polylog hθ1 hx3 B hB
    have hsum : ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊, maxDiscrepancy x q
        ≤ (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (fun n => if n.Prime then (1 : ℝ) else 0) x q)
          + (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
              (q.primeFactors.card : ℝ) / (q.totient : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun q hq => ?_)
      rw [Finset.mem_Icc] at hq
      exact maxDiscrepancy_le_seqDiscrepancy_prime x q (by omega)
    have hcombine : ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊, maxDiscrepancy x q
        ≤ (C + 1) * t := by
      refine le_trans hsum ?_
      rw [htdef]
      have e : (C + 1) * ((x : ℝ) / Real.log x ^ A)
          = C * (x : ℝ) / Real.log x ^ A + (x : ℝ) / Real.log x ^ A := by ring
      rw [e]
      exact add_le_add hpi (le_trans hseam habsx)
    exact le_trans hcombine (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0)
  · have hxmem : x ∈ Finset.Icc 2 x₀ := Finset.mem_Icc.mpr ⟨hx, by omega⟩
    have hsingle :
        (⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊ : ℝ) * ((x : ℝ) + 1) * Real.log x ^ A / x ≤ Csm := by
      rw [hCsmdef]
      exact Finset.single_le_sum hterm_nn hxmem
    calc ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊, maxDiscrepancy x q
        ≤ (⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊ : ℝ) * ((x : ℝ) + 1) := sum_maxDiscrepancy_crude_gen x _
      _ = ((⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊ : ℝ) * ((x : ℝ) + 1) * Real.log x ^ A / x) * t := by
          rw [htdef]; field_simp
      _ ≤ Csm * t := mul_le_mul_of_nonneg_right hsingle ht0
      _ ≤ max (C + 1) Csm * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht0

/-! ## The headline — the Λ-discrepancy consumer (D-N2c) -/

/-- **`HasLevel θ` from the Λ-weighted discrepancy level** (D-N2c, PB-floor).  The
hypothesis `h` is spelled **character-for-character** as the body of D-N2a's
`LambdaLevel θ` (the assembly seam): the point-wise Λ-weighted sequence
discrepancy level.  The step-1 Abel bridge `hbridge` converts it to the
prime-indicator level `PiLevel θ`; `hasLevel_of_piLevel` (steps 2+3, complete)
then lands `HasLevel θ`.  The bridge is the single deferred piece — it needs the
y-uniform strengthening of `LambdaLevel` (see the module docstring's honesty note
and `docs/blueprints/flags.md`, the D-N2c entry). -/
theorem hasLevel_of_lambdaDiscrepancy {θ : ℝ} (_hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (h : ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) x q)
        ≤ C * x / Real.log x ^ A)
    (hbridge : (∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) x q)
        ≤ C * x / Real.log x ^ A) → PiLevel θ) :
    HasLevel θ :=
  hasLevel_of_piLevel hθ1 (hbridge h)
