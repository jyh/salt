/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma7EF
import Salt.SW.DensityStrip

/-!
# Arm B part B3-i — THE ROW-(iv) TAIL RE-GRADE: B2 spent shell by shell (design γ)

LANDED 2026-09-06 (B3-i(a)): the freeze draft v1 §0(A)'s eleven statements, every proof
kernel-checked and sorry-free. The crude count `137·(2T₀+5)·log(q(T₀+4))` is baked into
`efEnvelope`'s definition; this file cuts a sibling envelope whose two zero rows go through
B2's log-free density (`zeroCountM_density_logfree`) shell by shell at the ceiling, and
prices the exponential row's tail integral. Nothing here bears on twin primes.

## The shell spend, in one line

`zeroSum_shells_le` puts each zero of the erased box in the shell
`i(ρ) = ⌊log((1 − Re ρ)/w)/log(6/5)⌋₊` (total on `Z`, since `hbar` gives `1 − Re ρ ≥ w > 0`),
splits the sum fibrewise over `Finset.range (I+1)` with `I = ⌈1/w⌉₊` (Bernoulli
`(6/5)^i ≥ 1 + i/5` against `1 − Re ρ ≤ 1/10` bounds the index), prices fibre `i` by B2 at
`σ = 1 − w(6/5)^{i+1}` (which is `≥ 4/5` because `w(6/5)^{i+1} ≤ 3/25` on a NON-EMPTY fibre),
turns the two `rpow`s into one `exp` whose exponent `hy` drives below `−t_i·log u/4`, and sums
the geometric tail `∑ e^{−i} ≤ 1/(1 − e^{−1}) ≤ 2`.

## The `σb`-free continuity re-cut

`Lemma7EF`'s continuity chain is `private`, so §"Continuity helpers" re-cuts the pieces the B3
envelope needs. The one deliberate difference is recorded there: that chain's
`0 < σb + 1` hypothesis is used only to discharge `ContinuousOn.rpow_const`'s side goal by
`Or.inr`, and on `[3,∞)` the base is `≥ 3 ≠ 0`, so `Or.inl` discharges it with NO hypothesis on
`σb` — which is what `continuousOn_efEnvelopeB3_ceilFun`'s frozen binder list allows.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set MeasureTheory
open Salt.SW
open scoped Topology

namespace Salt.HB

/-- B2's constant, chosen ONCE. -/
noncomputable def n9CB2 : ℝ := Classical.choose zeroCountM_density_logfree

/-- B2's exponent, chosen ONCE (`≤ 150`). -/
noncomputable def n9DB2 : ℝ := Classical.choose (Classical.choose_spec zeroCountM_density_logfree)

/-- Class A: `Classical.choose_spec` twice. -/
theorem n9B2_spec : 0 < n9CB2 ∧ 0 < n9DB2 ∧ n9DB2 ≤ 150 ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 2 ≤ q →
      ∀ (σ T : ℝ), 4 / 5 ≤ σ → σ ≤ 1 → 2 ≤ T →
        zeroCountM χ σ T ≤ n9CB2 * ((q : ℝ) * T) ^ (n9DB2 * (1 - σ)) := by
  exact Classical.choose_spec (Classical.choose_spec zeroCountM_density_logfree)

/-- The termwise form of `efZeroSumM_norm_le_harmonic`. Class A. -/
theorem efZeroSumM_norm_le_termwise {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Z : Finset ℂ} {y : ℝ} (hy : 1 ≤ y) :
    ‖efZeroSumM χ Z y‖ ≤ ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * y ^ ρ.re / ‖ρ‖ := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  rw [efZeroSumM]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ρ _ => ?_)
  rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_natCast]
  exact le_of_eq (mul_div_assoc _ _ _).symm

/-! ### The shell machinery (private helpers for `zeroSum_shells_le`) -/

/-- **The shell index** of a zero at the base scale `w`: `⌊log((1 − Re ρ)/w)/log(6/5)⌋₊`. -/
private noncomputable def shellIdx (w : ℝ) (ρ : ℂ) : ℕ :=
  ⌊Real.log ((1 - ρ.re) / w) / Real.log (6 / 5)⌋₊

/-- **The bracket**: at `w ≤ z` the index `i = ⌊log(z/w)/log(6/5)⌋₊` puts `z` in the shell
`[w·(6/5)^i, w·(6/5)^{i+1})`. -/
private lemma shell_bracket {w z : ℝ} (hw : 0 < w) (hwz : w ≤ z) :
    w * (6 / 5 : ℝ) ^ (⌊Real.log (z / w) / Real.log (6 / 5)⌋₊) ≤ z ∧
      z < w * (6 / 5 : ℝ) ^ (⌊Real.log (z / w) / Real.log (6 / 5)⌋₊ + 1) := by
  have hl65 : (0 : ℝ) < Real.log (6 / 5) := Real.log_pos (by norm_num)
  have hx1 : (1 : ℝ) ≤ z / w := (one_le_div hw).mpr hwz
  have hx0 : (0 : ℝ) < z / w := by linarith
  have hlx : (0 : ℝ) ≤ Real.log (z / w) := Real.log_nonneg hx1
  have hr0 : (0 : ℝ) ≤ Real.log (z / w) / Real.log (6 / 5) := div_nonneg hlx hl65.le
  have hrl : Real.log (z / w) / Real.log (6 / 5) * Real.log (6 / 5) = Real.log (z / w) := by
    field_simp
  have hfl := Nat.floor_le hr0
  have hfu := Nat.lt_floor_add_one (Real.log (z / w) / Real.log (6 / 5))
  constructor
  · have h1 : Real.log ((6 / 5 : ℝ) ^ (⌊Real.log (z / w) / Real.log (6 / 5)⌋₊))
        ≤ Real.log (z / w) := by
      rw [Real.log_pow]
      linarith [mul_le_mul_of_nonneg_right hfl hl65.le, hrl]
    have hp : (0 : ℝ) < ((6 : ℝ) / 5) ^ (⌊Real.log (z / w) / Real.log (6 / 5)⌋₊) := by positivity
    have h2 := Real.exp_le_exp.mpr h1
    rw [Real.exp_log hp, Real.exp_log hx0, le_div_iff₀ hw] at h2
    linarith [h2, mul_comm w (((6 : ℝ) / 5) ^ (⌊Real.log (z / w) / Real.log (6 / 5)⌋₊))]
  · have h1 : Real.log (z / w)
        < Real.log ((6 / 5 : ℝ) ^ (⌊Real.log (z / w) / Real.log (6 / 5)⌋₊ + 1)) := by
      rw [Real.log_pow]
      push_cast
      linarith [mul_lt_mul_of_pos_right hfu hl65, hrl]
    have hp : (0 : ℝ) < ((6 : ℝ) / 5) ^ (⌊Real.log (z / w) / Real.log (6 / 5)⌋₊ + 1) := by
      positivity
    have h2 := Real.exp_lt_exp.mpr h1
    rw [Real.exp_log hx0, Real.exp_log hp, div_lt_iff₀ hw] at h2
    linarith [h2, mul_comm w (((6 : ℝ) / 5) ^ (⌊Real.log (z / w) / Real.log (6 / 5)⌋₊ + 1))]

/-- Bernoulli at `a = 1/5`: `1 + i/5 ≤ (6/5)^i`. -/
private lemma one_add_div_five_le_pow (i : ℕ) : 1 + (i : ℝ) / 5 ≤ (6 / 5 : ℝ) ^ i := by
  have h := one_add_mul_le_pow (a := (1 / 5 : ℝ)) (by norm_num) i
  have he : (1 : ℝ) + 1 / 5 = 6 / 5 := by norm_num
  rw [he] at h
  linarith

/-- `(e^{−1})^i = e^{−i}`. -/
private lemma exp_neg_one_pow (i : ℕ) : (Real.exp (-1)) ^ i = Real.exp (-(i : ℝ)) := by
  induction i with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

/-- The geometric tail of `e^{−i}` is at most `2` (`1/(1 − e^{−1}) ≤ 2`). -/
private lemma geom_exp_neg_sum_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (Real.exp (-1)) ^ i ≤ 2 := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hr0 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have hrhalf : Real.exp (-1) ≤ 1 / 2 := by nlinarith
  have hS0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range n, (Real.exp (-1)) ^ i :=
    Finset.sum_nonneg fun i _ => pow_nonneg hr0.le i
  have hgm := geom_sum_mul (Real.exp (-1)) n
  have hrn : (0 : ℝ) ≤ (Real.exp (-1)) ^ n := pow_nonneg hr0.le n
  nlinarith [hgm, hrn, mul_le_mul_of_nonneg_left hrhalf hS0]

/-- **THE SHELL SPEND** — B2 spent shell by shell at a ceiling `1 − w`. Class C. -/
theorem zeroSum_shells_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σa T u w : ℝ} (hσa : 9 / 10 ≤ σa) (hT : 2 ≤ T)
    (hu : 1 ≤ u) {Z : Finset ℂ} (hZ : Z ⊆ boxZeros χ σa 1 T)
    (hw : 0 < w) (hw1 : w ≤ 1 / 10) (hbar : ∀ ρ ∈ Z, ρ.re ≤ 1 - w)
    (hy : 6 / 5 * n9DB2 * Real.log ((q : ℝ) * T) ≤ 3 / 4 * Real.log u)
    (hbig : 20 ≤ w * Real.log u) :
    ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * u ^ ρ.re
      ≤ 2 * n9CB2 * u * Real.exp (-(w * Real.log u) / 4) := by
  classical
  obtain ⟨hC0, hD0, _hD150, hB2⟩ := n9B2_spec
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hL0 : (0 : ℝ) < Real.log u := by
    rcases lt_or_ge 0 (Real.log u) with hcon | hcon
    · exact hcon
    · nlinarith [mul_nonneg hw.le (neg_nonneg.mpr hcon)]
  have hu0 : (0 : ℝ) < u := by linarith
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqT0 : (0 : ℝ) < (q : ℝ) * T := by nlinarith
  -- the bracket at every zero of `Z`
  have hbr : ∀ ρ ∈ Z, w * (6 / 5 : ℝ) ^ (shellIdx w ρ) ≤ 1 - ρ.re ∧
      1 - ρ.re < w * (6 / 5 : ℝ) ^ (shellIdx w ρ + 1) := by
    intro ρ hρ
    exact shell_bracket hw (by linarith [hbar ρ hρ])
  -- the index range
  set I : ℕ := ⌈1 / w⌉₊ with hIdef
  have hmapsto : ∀ ρ ∈ Z, shellIdx w ρ ∈ Finset.range (I + 1) := by
    intro ρ hρ
    have hb := (hbr ρ hρ).1
    have hmem := (mem_boxZeros hχ1).mp (hZ hρ)
    have h1 : w * (6 / 5 : ℝ) ^ (shellIdx w ρ) ≤ 1 / 10 := by linarith [hmem.2.1]
    have h2 := one_add_div_five_le_pow (shellIdx w ρ)
    have h3 : w * (1 + (shellIdx w ρ : ℝ) / 5) ≤ 1 / 10 := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hw.le]
    have h4 : (shellIdx w ρ : ℝ) ≤ 1 / w := by
      rw [le_div_iff₀ hw]; nlinarith
    have h5 : (shellIdx w ρ : ℝ) ≤ (I : ℝ) := le_trans h4 (by rw [hIdef]; exact Nat.le_ceil _)
    have h6 : shellIdx w ρ ≤ I := by exact_mod_cast h5
    exact Finset.mem_range.mpr (by omega)
  -- the shell budget
  set A : ℝ := w * Real.log u / 4 with hAdef
  have hA5 : (5 : ℝ) ≤ A := by rw [hAdef]; linarith
  -- THE FIBRE BOUND
  have hfib : ∀ (i : ℕ) (F : Finset ℂ), F ⊆ Z → (∀ ρ ∈ F, shellIdx w ρ = i) →
      (∑ ρ ∈ F, (zeroMult χ ρ : ℝ) * u ^ ρ.re)
        ≤ n9CB2 * u * Real.exp (-(A * (6 / 5 : ℝ) ^ i)) := by
    intro i F hFZ hFi
    have hRnn : (0 : ℝ) ≤ n9CB2 * u * Real.exp (-(A * (6 / 5 : ℝ) ^ i)) :=
      mul_nonneg (mul_nonneg hC0.le hu0.le) (Real.exp_pos _).le
    rcases F.eq_empty_or_nonempty with hemp | ⟨ρ₀, hρ₀⟩
    · rw [hemp, Finset.sum_empty]; exact hRnn
    · have hs0 : (0 : ℝ) < w * (6 / 5 : ℝ) ^ i := by positivity
      have hb₀ := (hbr ρ₀ (hFZ hρ₀)).1
      rw [hFi ρ₀ hρ₀] at hb₀
      have hmem₀ := (mem_boxZeros hχ1).mp (hZ (hFZ hρ₀))
      have hsle : w * (6 / 5 : ℝ) ^ i ≤ 1 / 10 := by linarith [hmem₀.2.1]
      have hs' : ∀ ρ ∈ F, 1 - ρ.re < 6 / 5 * (w * (6 / 5 : ℝ) ^ i) := by
        intro ρ hρ
        have h := (hbr ρ (hFZ hρ)).2
        rw [hFi ρ hρ] at h
        rw [pow_succ] at h
        linarith
      have hlow : ∀ ρ ∈ F, ρ.re ≤ 1 - w * (6 / 5 : ℝ) ^ i := by
        intro ρ hρ
        have h := (hbr ρ (hFZ hρ)).1
        rw [hFi ρ hρ] at h
        linarith
      have hsub : F ⊆ boxZeros χ (1 - 6 / 5 * (w * (6 / 5 : ℝ) ^ i)) 1 T := by
        intro ρ hρ
        have hmem := (mem_boxZeros hχ1).mp (hZ (hFZ hρ))
        exact (mem_boxZeros hχ1).mpr
          ⟨hmem.1, by linarith [hs' ρ hρ], hmem.2.2.1, hmem.2.2.2⟩
      calc (∑ ρ ∈ F, (zeroMult χ ρ : ℝ) * u ^ ρ.re)
          ≤ ∑ ρ ∈ F, (zeroMult χ ρ : ℝ) * u ^ (1 - w * (6 / 5 : ℝ) ^ i) := by
            refine Finset.sum_le_sum (fun ρ hρ => ?_)
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hu (hlow ρ hρ)) (by positivity)
        _ = (∑ ρ ∈ F, (zeroMult χ ρ : ℝ)) * u ^ (1 - w * (6 / 5 : ℝ) ^ i) := by
            rw [Finset.sum_mul]
        _ ≤ zeroCountM χ (1 - 6 / 5 * (w * (6 / 5 : ℝ) ^ i)) T
              * u ^ (1 - w * (6 / 5 : ℝ) ^ i) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu0.le _)
            rw [zeroCountM, efMultTotal]
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ ≤ n9CB2 * ((q : ℝ) * T) ^ (n9DB2 * (1 - (1 - 6 / 5 * (w * (6 / 5 : ℝ) ^ i))))
              * u ^ (1 - w * (6 / 5 : ℝ) ^ i) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hu0.le _)
            exact hB2 q χ hχ hq (1 - 6 / 5 * (w * (6 / 5 : ℝ) ^ i)) T (by linarith)
              (by linarith) hT
        _ ≤ n9CB2 * u * Real.exp (-(A * (6 / 5 : ℝ) ^ i)) := by
            have h1 : ((q : ℝ) * T) ^ (n9DB2 * (1 - (1 - 6 / 5 * (w * (6 / 5 : ℝ) ^ i))))
                = Real.exp (n9DB2 * (6 / 5 * (w * (6 / 5 : ℝ) ^ i))
                    * Real.log ((q : ℝ) * T)) := by
              rw [Real.rpow_def_of_pos hqT0]; congr 1; ring
            have h2 : u ^ (1 - w * (6 / 5 : ℝ) ^ i)
                = Real.exp ((1 - w * (6 / 5 : ℝ) ^ i) * Real.log u) := by
              rw [Real.rpow_def_of_pos hu0]; congr 1; ring
            have hkey : w * (6 / 5 : ℝ) ^ i * (6 / 5 * n9DB2 * Real.log ((q : ℝ) * T))
                ≤ w * (6 / 5 : ℝ) ^ i * (3 / 4 * Real.log u) :=
              mul_le_mul_of_nonneg_left hy hs0.le
            have hexp : Real.exp (n9DB2 * (6 / 5 * (w * (6 / 5 : ℝ) ^ i))
                  * Real.log ((q : ℝ) * T))
                * Real.exp ((1 - w * (6 / 5 : ℝ) ^ i) * Real.log u)
                ≤ u * Real.exp (-(A * (6 / 5 : ℝ) ^ i)) := by
              rw [← Real.exp_add]
              have hru : u * Real.exp (-(A * (6 / 5 : ℝ) ^ i))
                  = Real.exp (Real.log u + -(A * (6 / 5 : ℝ) ^ i)) := by
                rw [Real.exp_add, Real.exp_log hu0]
              rw [hru]
              refine Real.exp_le_exp.mpr ?_
              rw [hAdef]
              nlinarith [hkey]
            rw [h1, h2]
            calc n9CB2 * Real.exp (n9DB2 * (6 / 5 * (w * (6 / 5 : ℝ) ^ i))
                    * Real.log ((q : ℝ) * T))
                  * Real.exp ((1 - w * (6 / 5 : ℝ) ^ i) * Real.log u)
                = n9CB2 * (Real.exp (n9DB2 * (6 / 5 * (w * (6 / 5 : ℝ) ^ i))
                    * Real.log ((q : ℝ) * T))
                  * Real.exp ((1 - w * (6 / 5 : ℝ) ^ i) * Real.log u)) := by ring
              _ ≤ n9CB2 * (u * Real.exp (-(A * (6 / 5 : ℝ) ^ i))) :=
                  mul_le_mul_of_nonneg_left hexp hC0.le
              _ = n9CB2 * u * Real.exp (-(A * (6 / 5 : ℝ) ^ i)) := by ring
  -- assemble the shells
  rw [← Finset.sum_fiberwise_of_maps_to hmapsto (fun ρ => (zeroMult χ ρ : ℝ) * u ^ ρ.re)]
  refine le_trans (Finset.sum_le_sum (fun i _ => hfib i _ (Finset.filter_subset _ _)
    (fun ρ hρ => (Finset.mem_filter.mp hρ).2))) ?_
  have hstep : ∀ i ∈ Finset.range (I + 1),
      n9CB2 * u * Real.exp (-(A * (6 / 5 : ℝ) ^ i))
        ≤ n9CB2 * u * Real.exp (-A) * (Real.exp (-1)) ^ i := by
    intro i _
    have hber := one_add_div_five_le_pow i
    have hrw : n9CB2 * u * Real.exp (-A) * (Real.exp (-1)) ^ i
        = n9CB2 * u * Real.exp (-A + -(i : ℝ)) := by
      rw [exp_neg_one_pow i, Real.exp_add]; ring
    rw [hrw]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hC0.le hu0.le)
    nlinarith [mul_le_mul_of_nonneg_left hber (by linarith : (0 : ℝ) ≤ A),
      mul_nonneg (by linarith : (0 : ℝ) ≤ A - 5) (Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  calc n9CB2 * u * Real.exp (-A) * (∑ i ∈ Finset.range (I + 1), (Real.exp (-1)) ^ i)
      ≤ n9CB2 * u * Real.exp (-A) * 2 :=
        mul_le_mul_of_nonneg_left (geom_exp_neg_sum_le _)
          (mul_nonneg (mul_nonneg hC0.le hu0.le) (Real.exp_pos _).le)
    _ = 2 * n9CB2 * u * Real.exp (-(w * Real.log u) / 4) := by
        rw [show -A = -(w * Real.log u) / 4 by rw [hAdef]; ring]
        ring

/-- The shell row of the B3 envelope. -/
noncomputable def efShellRow (q : ℕ) (bceil u : ℝ) : ℝ :=
  (efH q u / u + 5 / 4) * (2 * n9CB2) * Real.exp (-((1 - bceil) * Real.log u) / 4)

/-- **THE B3 ENVELOPE** — `efEnvelope`'s first two summands verbatim, `β₀`'s own term kept
apart, the shell row in place of the two crude-count rows. -/
noncomputable def efEnvelopeB3 (q : ℕ) (β₀ bceil : ℝ) (m : ℕ) (σa σb u : ℝ) : ℝ :=
  ((efH q u + 1) * Real.log (u + efH q u)
    + (efShiftBound q (efT0 q u) σa σb u + efShiftBound q (efT0 q u) σa σb (u + efH q u))
        / efH q u
    + (m : ℝ) * (efH q u * u ^ (β₀ - 1))) / u
  + efShellRow q bceil u

/-- The raw form: `psiDefect_norm_le_of_ef` cut at `hkey`. No ceiling binder; the box's lower
edge `9/10 ≤ σ₀ − w` EXPORTED (R2's K3 repair — it is `hσ₀w` at `Lemma7EF.lean:404`, from
`DensityCrude.lean:870`; the shell lemma's `hσa` and `hbar` need it). Class B. -/
theorem psiDefect_norm_le_raw {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {β₀ u h σa σb T₀ : ℝ}
    (hu : 3 ≤ u) (hh : 0 < h) (hσa : 9 / 10 ≤ σa) (hσab : σa < σb) (hσb : σb < 1)
    (hT₀ : 2 ≤ T₀) (hβ₀1 : β₀ ≤ 1) (hσbβ₀ : σb ≤ β₀)
    (hβ₀zero : LFunction χ (β₀ : ℂ) = 0) :
    ∃ σ₀ T w : ℝ,
      (σa ≤ σ₀ ∧ σ₀ ≤ σb) ∧ (T₀ ≤ T ∧ T ≤ T₀ + 1) ∧ 0 < w ∧
      (σb - σa) / (4 * (137 * (2 * T₀ + 7) * Real.log ((q : ℝ) * (T₀ + 5)) + 1)) ≤ w ∧
      9 / 10 ≤ σ₀ - w ∧
      ‖psiDefect χ β₀ (zeroMult χ (β₀ : ℂ)) u‖
        ≤ (h + 1) * Real.log (u + h)
          + (efShiftError q T σ₀ w u + efShiftError q T σ₀ w (u + h)) / h
          + (zeroMult χ (β₀ : ℂ) : ℝ) * (h * u ^ (β₀ - 1))
          + (h / u + 5 / 4) * ∑ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ),
              (zeroMult χ ρ : ℝ) * u ^ ρ.re := by
  classical
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  obtain ⟨σ₀, T, w, hσ, hT, hw, hwlb, hσ₀w, hσ₀1, hsock⟩ :=
    psi_explicit_sharpM_perZero_unsep χ hχ hq hu hh hσa hσab hσb hT₀
  refine ⟨σ₀, T, w, hσ, hT, hw, hwlb, hσ₀w, ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith [hT.1]
  -- `β₀` lies in the contour box
  have hβZ : (β₀ : ℂ) ∈ boxZeros χ (σ₀ - w) 1 T := by
    rw [mem_boxZeros hχ1]
    refine ⟨hβ₀zero, ?_, ?_, ?_⟩
    · simp only [Complex.ofReal_re]; linarith [hσ.2]
    · simpa using hβ₀1
    · simp only [Complex.ofReal_im, abs_zero]; linarith [hT.1]
  have hres : (((zeroMult χ (β₀ : ℂ) : ℝ) * u ^ β₀ / β₀ : ℝ) : ℂ)
      = (zeroMult χ (β₀ : ℂ) : ℂ) * (((u : ℝ) : ℂ) ^ (β₀ : ℂ) / (β₀ : ℂ)) := by
    push_cast [Complex.ofReal_cpow (le_of_lt hu0)]
    ring
  have hkey : psiDefect χ β₀ (zeroMult χ (β₀ : ℂ)) u
      = (psiChiR u χ + efZeroSumM χ (boxZeros χ (σ₀ - w) 1 T) u)
        - efZeroSumM χ ((boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ)) u := by
    rw [efZeroSumM_erase_split χ hβZ u, psiDefect, hres]
    ring
  -- THE ERASED SPEND, termwise: `‖ρ‖ ≥ Re ρ ≥ σ₀ − w ≥ 9/10`
  have hspend : ‖efZeroSumM χ ((boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ)) u‖
      ≤ 5 / 4 * ∑ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ),
          (zeroMult χ ρ : ℝ) * u ^ ρ.re := by
    refine le_trans (efZeroSumM_norm_le_termwise χ hu1) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun ρ hρ => ?_)
    have hmem := (mem_boxZeros hχ1).mp (Finset.mem_of_mem_erase hρ)
    have hρ9 : (9 : ℝ) / 10 ≤ ‖ρ‖ :=
      le_trans (by linarith [hmem.2.1])
        (le_trans (le_abs_self ρ.re) (Complex.abs_re_le_norm ρ))
    have hnn : (0 : ℝ) ≤ (zeroMult χ ρ : ℝ) * u ^ ρ.re := by positivity
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖ρ‖)]
    nlinarith
  -- THE DE-SMOOTHING SUM, `β₀` kept apart
  have hdesm : ∑ ρ ∈ boxZeros χ (σ₀ - w) 1 T, (zeroMult χ ρ : ℝ) * (h * u ^ (ρ.re - 1))
      = (zeroMult χ (β₀ : ℂ) : ℝ) * (h * u ^ (β₀ - 1))
        + h / u * ∑ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ),
            (zeroMult χ ρ : ℝ) * u ^ ρ.re := by
    rw [← Finset.add_sum_erase _ (fun ρ => (zeroMult χ ρ : ℝ) * (h * u ^ (ρ.re - 1))) hβZ]
    simp only [Complex.ofReal_re]
    refine congrArg _ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [Real.rpow_sub hu0, Real.rpow_one]
    field_simp
  -- assembly
  rw [hkey]
  refine le_trans (norm_sub_le _ _) ?_
  have hexp : (h / u + 5 / 4) * ∑ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ),
        (zeroMult χ ρ : ℝ) * u ^ ρ.re
      = h / u * (∑ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ),
            (zeroMult χ ρ : ℝ) * u ^ ρ.re)
        + 5 / 4 * ∑ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ),
            (zeroMult χ ρ : ℝ) * u ^ ρ.re := by ring
  rw [hexp]
  rw [hdesm] at hsock
  linarith [hsock, hspend]

/-- **`hEF` FOR THE B3 ENVELOPE.** Class C (an assembly). -/
theorem psiDefect_norm_le_envelopeB3 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {β₀ bceil u σa σb : ℝ} {m : ℕ}
    (hu : 3 ≤ u) (hm : m = zeroMult χ (β₀ : ℂ)) (hσa : 9 / 10 ≤ σa) (hσab : σa < σb)
    (hσb : σb < 1) (hβ₀1 : β₀ ≤ 1) (hσbβ₀ : σb ≤ β₀) (hβ₀zero : LFunction χ (β₀ : ℂ) = 0)
    (hceil : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) → 9 / 10 ≤ ρ.re → ρ.re ≤ 1 →
      |ρ.im| ≤ efT0 q u + 1 → ρ.re ≤ bceil)
    (hb16 : 16 / 17 ≤ bceil)
    (hy : 6 / 5 * n9DB2 * Real.log ((q : ℝ) * (efT0 q u + 1)) ≤ 3 / 4 * Real.log u)
    (hbig : 20 ≤ (1 - bceil) * Real.log u) :
    ‖psiDefect χ β₀ m u‖ ≤ u * efEnvelopeB3 q β₀ bceil m σa σb u := by
  subst hm
  have hu0 : (0 : ℝ) < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hT0 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq hu
  have hHpos : 0 < efH q u := efH_pos hq hu
  have huh : (3 : ℝ) ≤ u + efH q u := by linarith
  have hlogu : (0 : ℝ) < Real.log u := Real.log_pos (by linarith)
  have hbc1 : bceil < 1 := by nlinarith
  obtain ⟨σ₀, T, w, hσ, hT, hw, hwlb, hσ₀w, hbnd⟩ :=
    psiDefect_norm_le_raw χ hχ hq hu hHpos hσa hσab hσb hT0 hβ₀1 hσbβ₀ hβ₀zero
  refine le_trans hbnd ?_
  -- THE SHELL SPEND at the exported edge `σa := σ₀ − w`
  have hTle : T ≤ efT0 q u + 1 := hT.2
  have hT2 : (2 : ℝ) ≤ T := le_trans hT0 hT.1
  have hshell : ∑ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ),
      (zeroMult χ ρ : ℝ) * u ^ ρ.re
      ≤ 2 * n9CB2 * u * Real.exp (-((1 - bceil) * Real.log u) / 4) := by
    have hbar : ∀ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ), ρ.re ≤ 1 - (1 - bceil) := by
      intro ρ hρ
      have hmem := (mem_boxZeros hχ1).mp (Finset.mem_of_mem_erase hρ)
      have := hceil ρ hmem.1 (Finset.ne_of_mem_erase hρ) (by linarith [hmem.2.1])
        hmem.2.2.1 (le_trans hmem.2.2.2 hTle)
      linarith
    have hyT : 6 / 5 * n9DB2 * Real.log ((q : ℝ) * T) ≤ 3 / 4 * Real.log u := by
      have hD0 : (0 : ℝ) < n9DB2 := n9B2_spec.2.1
      refine le_trans
        (mul_le_mul_of_nonneg_left ?_ (by linarith : (0 : ℝ) ≤ 6 / 5 * n9DB2)) hy
      exact Real.log_le_log (by nlinarith) (by nlinarith)
    exact zeroSum_shells_le χ hχ hq hσ₀w hT2 hu1 (Finset.erase_subset _ _)
      (by linarith) (by linarith) hbar hyT hbig
  -- the uniformised contour budget
  have hE1 : efShiftError q T σ₀ w u ≤ efShiftBound q (efT0 q u) σa σb u :=
    efShiftError_le_efShiftBound hq hT0 hT.1 hT.2 hσa hσab hσb hσ.1 hσ.2 hw hwlb hu
  have hE2 : efShiftError q T σ₀ w (u + efH q u)
      ≤ efShiftBound q (efT0 q u) σa σb (u + efH q u) :=
    efShiftError_le_efShiftBound hq hT0 hT.1 hT.2 hσa hσab hσb hσ.1 hσ.2 hw hwlb huh
  -- the target, unfolded
  have hnorm : u * efEnvelopeB3 q β₀ bceil (zeroMult χ (β₀ : ℂ)) σa σb u
      = (efH q u + 1) * Real.log (u + efH q u)
        + (efShiftBound q (efT0 q u) σa σb u
            + efShiftBound q (efT0 q u) σa σb (u + efH q u)) / efH q u
        + (zeroMult χ (β₀ : ℂ) : ℝ) * (efH q u * u ^ (β₀ - 1))
        + (efH q u / u + 5 / 4) * (2 * n9CB2 * u
            * Real.exp (-((1 - bceil) * Real.log u) / 4)) := by
    rw [efEnvelopeB3, efShellRow]
    field_simp
  rw [hnorm]
  have hbud : (efShiftError q T σ₀ w u + efShiftError q T σ₀ w (u + efH q u)) / efH q u
      ≤ (efShiftBound q (efT0 q u) σa σb u
          + efShiftBound q (efT0 q u) σa σb (u + efH q u)) / efH q u :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hHpos)
  have hfac : (0 : ℝ) ≤ efH q u / u + 5 / 4 := by positivity
  have hmulle := mul_le_mul_of_nonneg_left hshell hfac
  linarith [hbud, hmulle]

/-- Class B: mirror `efEnvelope_nonneg`. -/
theorem efEnvelopeB3_nonneg {q : ℕ} {β₀ bceil σa σb u : ℝ} {m : ℕ} (hq : 2 ≤ q) (hu : 3 ≤ u)
    (hσa : 9 / 10 ≤ σa) (hσab : σa < σb) (hσb : σb < 1) :
    0 ≤ efEnvelopeB3 q β₀ bceil m σa σb u := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hu0 : (0 : ℝ) < u := by linarith
  have hT0 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq hu
  have hHpos : 0 < efH q u := efH_pos hq hu
  have huh : (3 : ℝ) ≤ u + efH q u := by linarith
  have hC0 : (0 : ℝ) < n9CB2 := n9B2_spec.1
  rw [efEnvelopeB3, efShellRow]
  refine add_nonneg (div_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) (by linarith)) ?_
  · exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  · exact div_nonneg (add_nonneg
      (efShiftBound_nonneg hq hT0 (by linarith) (by linarith) hσab hu)
      (efShiftBound_nonneg hq hT0 (by linarith) (by linarith) hσab huh)) (le_of_lt hHpos)
  · exact mul_nonneg (Nat.cast_nonneg m)
      (mul_nonneg hHpos.le (Real.rpow_nonneg hu0.le _))
  · refine mul_nonneg (mul_nonneg ?_ (by linarith)) (Real.exp_pos _).le
    have h : (0 : ℝ) ≤ efH q u / u := div_nonneg hHpos.le hu0.le
    linarith

/-! ### Continuity helpers

`Lemma7EF`'s own continuity chain is `private`, so the pieces the B3 envelope needs are
re-cut here.  The one deliberate difference: `cont_efShiftBound` there carries a
`0 < σb + 1` hypothesis used only to discharge `ContinuousOn.rpow_const`'s side goal by
`Or.inr`; on `[3,∞)` the base is `≥ 3 ≠ 0`, so `Or.inl` discharges it with no hypothesis
on `σb` at all — which is what the B3 statement's binder list allows. -/

private lemma contB3_log_comp {s : Set ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g s)
    (h0 : ∀ x ∈ s, g x ≠ 0) : ContinuousOn (fun x => Real.log (g x)) s :=
  Real.continuousOn_log.comp hg (fun x hx => by simpa using h0 x hx)

private lemma contB3_logqu {q : ℕ} (hq : 2 ≤ q) :
    ContinuousOn (fun u : ℝ => Real.log ((q : ℝ) * u)) (Set.Ici (3 : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  refine contB3_log_comp (continuousOn_const.mul continuousOn_id) (fun u hu => ?_)
  have h3 : (3 : ℝ) ≤ u := hu
  exact ne_of_gt (by positivity)

private lemma logquB3_ge {q : ℕ} (hq : 2 ≤ q) {u : ℝ} (hu : 3 ≤ u) :
    (3 : ℝ) ≤ Real.log ((q : ℝ) * u) + 2 := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqu : (6 : ℝ) ≤ (q : ℝ) * u := by nlinarith
  have he : Real.exp 1 ≤ (q : ℝ) * u :=
    le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hqu
  have h1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * u) := (Real.le_log_iff_exp_le (by linarith)).mpr he
  linarith

private lemma contB3_efT0 {q : ℕ} (hq : 2 ≤ q) :
    ContinuousOn (fun u : ℝ => efT0 q u) (Set.Ici (3 : ℝ)) := by
  simp only [efT0]
  exact ((contB3_logqu hq).add continuousOn_const).pow 6

private lemma contB3_efH {q : ℕ} (hq : 2 ≤ q) :
    ContinuousOn (fun u : ℝ => efH q u) (Set.Ici (3 : ℝ)) := by
  simp only [efH]
  refine continuousOn_id.div (((contB3_logqu hq).add continuousOn_const).pow 3) (fun u hu => ?_)
  have h := logquB3_ge hq (show (3 : ℝ) ≤ u from hu)
  positivity

private lemma contB3_logQT {q : ℕ} (hq : 2 ≤ q) (a : ℝ) (ha : 0 ≤ a) :
    ContinuousOn (fun u : ℝ => Real.log ((q : ℝ) * (efT0 q u + a))) (Set.Ici (3 : ℝ)) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  refine contB3_log_comp (continuousOn_const.mul ((contB3_efT0 hq).add continuousOn_const))
    (fun u hu => ne_of_gt ?_)
  have h1 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq hu
  nlinarith

private lemma contB3_efShiftB {q : ℕ} (hq : 2 ≤ q) {σa σb : ℝ} :
    ContinuousOn (fun u : ℝ => efShiftB q (efT0 q u) σa σb) (Set.Ici (3 : ℝ)) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsq : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by linarith)
  have hfac1 : ContinuousOn (fun u : ℝ => 120 + 4 * (137 * (2 * efT0 q u + 7)
      * Real.log ((q : ℝ) * (efT0 q u + 5)) + 1) / (Real.log (7 / 6) * (σb - σa)))
      (Set.Ici (3 : ℝ)) := by
    refine continuousOn_const.add (ContinuousOn.div_const (continuousOn_const.mul ?_) _)
    exact ((continuousOn_const.mul ((continuousOn_const.mul (contB3_efT0 hq)).add
      continuousOn_const)).mul (contB3_logQT hq 5 (by norm_num))).add continuousOn_const
  have hfac2 : ContinuousOn (fun u : ℝ =>
      Real.log (4 * (5 * (5 + efT0 q u) * Real.sqrt q * (1 + Real.log q))))
      (Set.Ici (3 : ℝ)) := by
    refine contB3_log_comp (continuousOn_const.mul (((continuousOn_const.mul
      (continuousOn_const.add (contB3_efT0 hq))).mul continuousOn_const).mul
      continuousOn_const)) (fun u hu => ne_of_gt ?_)
    have h1 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq hu
    have h5 : (0 : ℝ) < 5 * (5 + efT0 q u) := by linarith
    have hs : (0 : ℝ) < Real.sqrt q := by linarith
    have hl : (0 : ℝ) < 1 + Real.log q := by linarith
    have := mul_pos (mul_pos h5 hs) hl
    linarith
  simp only [efShiftB]
  exact hfac1.mul hfac2

private lemma contB3_efShiftBound {q : ℕ} (hq : 2 ≤ q) {σa σb : ℝ}
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ici (3 : ℝ)))
    (hφ3 : ∀ u ∈ Set.Ici (3 : ℝ), 3 ≤ φ u) :
    ContinuousOn (fun u : ℝ => efShiftBound q (efT0 q u) σa σb (φ u)) (Set.Ici (3 : ℝ)) := by
  have hlogφ : ContinuousOn (fun u : ℝ => Real.log (φ u)) (Set.Ici (3 : ℝ)) :=
    contB3_log_comp hφ (fun u hu => ne_of_gt (by linarith [hφ3 u hu]))
  have hlogφ0 : ∀ u ∈ Set.Ici (3 : ℝ), Real.log (φ u) ≠ 0 := by
    intro u hu
    have h3 := hφ3 u hu
    have he : Real.exp 1 ≤ φ u :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) h3
    have h1 : (1 : ℝ) ≤ Real.log (φ u) := (Real.le_log_iff_exp_le (by linarith)).mpr he
    linarith
  have hrow1 : ContinuousOn (fun u : ℝ => 2 * ((1 + 1 / Real.log (φ u)) - σa)
      * efShiftB q (efT0 q u) σa σb * (Real.exp 1 * φ u ^ (2 : ℕ)) / efT0 q u ^ 2)
      (Set.Ici (3 : ℝ)) := by
    refine ContinuousOn.div (((continuousOn_const.mul ((continuousOn_const.add
      (continuousOn_const.div hlogφ hlogφ0)).sub continuousOn_const)).mul
      (contB3_efShiftB hq)).mul (continuousOn_const.mul (hφ.pow 2)))
      ((contB3_efT0 hq).pow 2) (fun u hu => ?_)
    have h1 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq hu
    positivity
  have hrow2 : ContinuousOn (fun u : ℝ => efShiftB q (efT0 q u) σa σb * φ u ^ (σb + 1)
      * (Real.pi / σa)) (Set.Ici (3 : ℝ)) :=
    ((contB3_efShiftB hq).mul
      (hφ.rpow_const (fun u hu => Or.inl (ne_of_gt (by linarith [hφ3 u hu]))))).mul
      continuousOn_const
  have hrow3 : ContinuousOn (fun u : ℝ => (Real.log (φ u) + 1) * (Real.exp 1 * φ u ^ (2 : ℕ))
      * (2 / efT0 q u)) (Set.Ici (3 : ℝ)) := by
    refine ((hlogφ.add continuousOn_const).mul (continuousOn_const.mul (hφ.pow 2))).mul
      (continuousOn_const.div (contB3_efT0 hq) (fun u hu => ?_))
    have h1 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq hu
    linarith
  simp only [efShiftBound]
  exact continuousOn_const.mul ((hrow1.add hrow2).add hrow3)

/-- Class B: mirror `continuousOn_efEnvelope_ceilFun`. -/
theorem continuousOn_efEnvelopeB3_ceilFun {q : ℕ} (hq : 2 ≤ q) {β₀ : ℝ} {B : ℝ → ℝ} (m : ℕ)
    (hB : ContinuousOn B (Set.Ici (3 : ℝ))) {σa σb : ℝ} (hσa : 9 / 10 ≤ σa) :
    ContinuousOn (fun u : ℝ => efEnvelopeB3 q β₀ (B u) m σa σb u) (Set.Ici (3 : ℝ)) := by
  have _hσa : (9 : ℝ) / 10 ≤ σa := hσa
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hφ2 : ContinuousOn (fun u : ℝ => u + efH q u) (Set.Ici (3 : ℝ)) :=
    continuousOn_id.add (contB3_efH hq)
  have hφ23 : ∀ u ∈ Set.Ici (3 : ℝ), (3 : ℝ) ≤ u + efH q u := by
    intro u hu
    have h3 : (3 : ℝ) ≤ u := hu
    linarith [efH_pos hq h3]
  have hid : ContinuousOn (fun u : ℝ => u) (Set.Ici (3 : ℝ)) := continuousOn_id
  have hne0 : ∀ u ∈ Set.Ici (3 : ℝ), u ≠ 0 :=
    fun u hu => ne_of_gt (by linarith [show (3 : ℝ) ≤ u from hu])
  have hA : ContinuousOn (fun u : ℝ => (efH q u + 1) * Real.log (u + efH q u))
      (Set.Ici (3 : ℝ)) :=
    ((contB3_efH hq).add continuousOn_const).mul
      (contB3_log_comp hφ2 (fun u hu => ne_of_gt (by linarith [hφ23 u hu])))
  have hBd : ContinuousOn (fun u : ℝ => (efShiftBound q (efT0 q u) σa σb u
      + efShiftBound q (efT0 q u) σa σb (u + efH q u)) / efH q u) (Set.Ici (3 : ℝ)) :=
    ContinuousOn.div ((contB3_efShiftBound hq (continuousOn_id (α := ℝ)) (fun u hu => hu)).add
      (contB3_efShiftBound hq hφ2 hφ23)) (contB3_efH hq)
      (fun u hu => ne_of_gt (efH_pos hq (show (3 : ℝ) ≤ u from hu)))
  have hC : ContinuousOn (fun u : ℝ => (m : ℝ) * (efH q u * u ^ (β₀ - 1))) (Set.Ici (3 : ℝ)) :=
    continuousOn_const.mul ((contB3_efH hq).mul
      (hid.rpow_const (fun u hu => Or.inl (hne0 u hu))))
  have hlogid : ContinuousOn (fun u : ℝ => Real.log u) (Set.Ici (3 : ℝ)) :=
    contB3_log_comp hid hne0
  have hexpo : ContinuousOn (fun u : ℝ => -((1 - B u) * Real.log u) / 4) (Set.Ici (3 : ℝ)) :=
    ContinuousOn.div_const (((continuousOn_const.sub hB).mul hlogid).neg) 4
  have hshell : ContinuousOn (fun u : ℝ => efShellRow q (B u) u) (Set.Ici (3 : ℝ)) := by
    simp only [efShellRow]
    exact ((((contB3_efH hq).div hid hne0).add continuousOn_const).mul continuousOn_const).mul
      hexpo.rexp
  simp only [efEnvelopeB3]
  exact (ContinuousOn.div ((hA.add hBd).add hC) hid hne0).add hshell

/-- **THE B3 LEDGER** — rows (i)–(iii) of the sharp ledger verbatim, the shell row as is.
Class B. -/
theorem efEnvelopeB3_le_ledger {q : ℕ} {β₀ bceil σa σb u M N : ℝ} {m : ℕ}
    (hq : 2 ≤ q) (hu : 3 ≤ u) (hM : M = Real.log ((q : ℝ) * u) + 2)
    (hN : N = Real.log q + 11 * Real.log M)
    (hσa : 9 / 10 ≤ σa) (hσab : σa < σb) (hσb : σb < 1) (hgap : 1 / 20 ≤ σb - σa)
    (hβ₀1 : β₀ ≤ 1) :
    efEnvelopeB3 q β₀ bceil m σa σb u
      ≤ ((m : ℝ) + 2 + 2 * 10 ^ 6 * N ^ 2 / M ^ 2) / M + M / u
        + 10 ^ 6 * M ^ 9 * N ^ 2 * u ^ (σb - 1)
        + (1 / M ^ 3 + 5 / 4) * (2 * n9CB2) * Real.exp (-((1 - bceil) * Real.log u) / 4) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hu0 : (0 : ℝ) < u := by linarith
  have hM3 : (3 : ℝ) ≤ M := by rw [hM]; exact logquB3_ge hq hu
  have hM0 : (0 : ℝ) < M := by linarith
  have hT0 : (2 : ℝ) ≤ efT0 q u := two_le_efT0 hq hu
  have hHpos : 0 < efH q u := efH_pos hq hu
  have hlq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by linarith)
  have hlM : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by linarith)
  have hN0 : (0 : ℝ) ≤ N := by rw [hN]; linarith
  have hMcube : (0 : ℝ) < M ^ 3 := by positivity
  have hCnn : (0 : ℝ) ≤ 10 ^ 3 * M ^ 3 * N := by nlinarith
  -- the shell row, at the ledger's own symbols: `efH q u / u = 1/M³`
  have hHu : efH q u / u = 1 / M ^ 3 := by
    rw [show efH q u = u / M ^ 3 from by rw [efH, hM]]
    field_simp
  have hshellrow : efShellRow q bceil u
      = (1 / M ^ 3 + 5 / 4) * (2 * n9CB2) * Real.exp (-((1 - bceil) * Real.log u) / 4) := by
    rw [efShellRow, hHu]
  -- the B3 envelope is `efEnvelope` at ANY ceiling, minus two non-negative rows
  have hdrop : ∀ b' : ℝ, efEnvelopeB3 q β₀ bceil m σa σb u
      ≤ efEnvelope q β₀ b' m σa σb u + efShellRow q bceil u := by
    intro b'
    have hlogQ4 : (0 : ℝ) ≤ Real.log ((q : ℝ) * (efT0 q u + 4)) :=
      Real.log_nonneg (by nlinarith)
    have hlogT2 : (0 : ℝ) ≤ Real.log (efT0 q u + 2) := Real.log_nonneg (by linarith)
    have hW1 : (0 : ℝ) ≤ efH q u * u ^ (b' - 1)
        * (137 * (2 * efT0 q u + 5) * Real.log ((q : ℝ) * (efT0 q u + 4))) :=
      mul_nonneg (mul_nonneg hHpos.le (Real.rpow_nonneg hu0.le _))
        (mul_nonneg (by linarith) hlogQ4)
    have hW2 : (0 : ℝ) ≤ u ^ b' * (137 * Real.log ((q : ℝ) * (efT0 q u + 4))
        * (8 + 4 * Real.log (efT0 q u + 2))) :=
      mul_nonneg (Real.rpow_nonneg hu0.le _)
        (mul_nonneg (by linarith) (by linarith))
    rw [efEnvelopeB3, efEnvelope]
    have hle : (efH q u + 1) * Real.log (u + efH q u)
        + (efShiftBound q (efT0 q u) σa σb u
            + efShiftBound q (efT0 q u) σa σb (u + efH q u)) / efH q u
        + (m : ℝ) * (efH q u * u ^ (β₀ - 1))
      ≤ (efH q u + 1) * Real.log (u + efH q u)
        + (efShiftBound q (efT0 q u) σa σb u
            + efShiftBound q (efT0 q u) σa σb (u + efH q u)) / efH q u
        + ((m : ℝ) * (efH q u * u ^ (β₀ - 1))
            + efH q u * u ^ (b' - 1)
              * (137 * (2 * efT0 q u + 5) * Real.log ((q : ℝ) * (efT0 q u + 4))))
        + u ^ b' * (137 * Real.log ((q : ℝ) * (efT0 q u + 4))
            * (8 + 4 * Real.log (efT0 q u + 2))) := by linarith
    linarith [div_le_div_of_nonneg_right hle hu0.le]
  have hled : ∀ b' : ℝ, efEnvelope q β₀ b' m σa σb u
      ≤ ((m : ℝ) + 2 + 2 * 10 ^ 6 * N ^ 2 / M ^ 2) / M + M / u
        + 10 ^ 6 * M ^ 9 * N ^ 2 * u ^ (σb - 1) + 10 ^ 3 * M ^ 3 * N * u ^ (b' - 1) :=
    fun b' => efEnvelope_le_ledger_sharp hq hu hM hN hσa hσab hσb hgap hβ₀1
  -- the ceiling row is free: `u^{b'−1} → 0` as `b' → −∞`
  rw [← hshellrow]
  refine le_of_forall_sub_le (fun ε hε => ?_)
  have hlogu : (0 : ℝ) < Real.log u := Real.log_pos (by linarith)
  have hden : (0 : ℝ) < 10 ^ 3 * M ^ 3 * N + 1 := by linarith
  obtain ⟨b', hpow⟩ : ∃ b' : ℝ, u ^ (b' - 1) = ε / (10 ^ 3 * M ^ 3 * N + 1) := by
    refine ⟨1 + Real.log (ε / (10 ^ 3 * M ^ 3 * N + 1)) / Real.log u, ?_⟩
    rw [Real.rpow_def_of_pos hu0]
    rw [show 1 + Real.log (ε / (10 ^ 3 * M ^ 3 * N + 1)) / Real.log u - 1
        = Real.log (ε / (10 ^ 3 * M ^ 3 * N + 1)) / Real.log u from by ring]
    rw [show Real.log u * (Real.log (ε / (10 ^ 3 * M ^ 3 * N + 1)) / Real.log u)
        = Real.log (ε / (10 ^ 3 * M ^ 3 * N + 1)) from by field_simp]
    exact Real.exp_log (div_pos hε hden)
  have hb : efEnvelopeB3 q β₀ bceil m σa σb u
      ≤ ((m : ℝ) + 2 + 2 * 10 ^ 6 * N ^ 2 / M ^ 2) / M + M / u
        + 10 ^ 6 * M ^ 9 * N ^ 2 * u ^ (σb - 1)
        + 10 ^ 3 * M ^ 3 * N * u ^ (b' - 1) + efShellRow q bceil u := by
    linarith [hdrop b', hled b']
  rw [hpow] at hb
  have hCe : 10 ^ 3 * M ^ 3 * N * (ε / (10 ^ 3 * M ^ 3 * N + 1)) ≤ ε := by
    rw [show 10 ^ 3 * M ^ 3 * N * (ε / (10 ^ 3 * M ^ 3 * N + 1))
        = 10 ^ 3 * M ^ 3 * N * ε / (10 ^ 3 * M ^ 3 * N + 1) from by ring,
      div_le_iff₀ hden]
    nlinarith
  linarith

/-- **THE `E₁` BOUND** — the exponential row's tail integral. Class B. -/
theorem integral_rpow_div_log_tail_le {X ε : ℝ} (hX : 3 ≤ X) (hε : 0 < ε) :
    IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) - ε) / Real.log v) (Set.Ioi X) ∧
    ∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε) / Real.log v ≤ X ^ (-ε) / (ε * Real.log X) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have he : Real.exp 1 ≤ X :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hX
    exact (Real.le_log_iff_exp_le hX0).mpr he
  have hlt : -(1 : ℝ) - ε < -1 := by linarith
  have hg : IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) - ε)) (Set.Ioi X) :=
    integrableOn_Ioi_rpow_of_lt hlt hX0
  have hmeas : AEStronglyMeasurable (fun v : ℝ => v ^ (-(1 : ℝ) - ε) / Real.log v)
      (volume.restrict (Set.Ioi X)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hid : ContinuousOn (fun t : ℝ => t) (Set.Ioi X) := continuousOn_id
    exact ContinuousOn.div
      (hid.rpow_const (fun t ht => Or.inl (ne_of_gt (by linarith [Set.mem_Ioi.mp ht]))))
      (Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [Set.mem_Ioi.mp ht])))
      (fun t ht => ne_of_gt (Real.log_pos (by linarith [Set.mem_Ioi.mp ht])))
  have hint : IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) - ε) / Real.log v) (Set.Ioi X) := by
    refine hg.mono' hmeas ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun v hv => ?_)))
    have hvX : X < v := hv
    have hv0 : (0 : ℝ) < v := by linarith
    have hlogv : (1 : ℝ) ≤ Real.log v :=
      le_trans hlogX (Real.log_le_log hX0 (le_of_lt hvX))
    have hrp : (0 : ℝ) < v ^ (-(1 : ℝ) - ε) := Real.rpow_pos_of_pos hv0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨hint, ?_⟩
  have hmaj : IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) - ε) / Real.log X) (Set.Ioi X) :=
    hg.div_const _
  have hmono : (∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε) / Real.log v)
      ≤ ∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε) / Real.log X := by
    refine setIntegral_mono_on hint hmaj measurableSet_Ioi (fun v hv => ?_)
    have hvX : X < v := hv
    have hv0 : (0 : ℝ) < v := by linarith
    have hlogv : Real.log X ≤ Real.log v := Real.log_le_log hX0 (le_of_lt hvX)
    have hrp : (0 : ℝ) < v ^ (-(1 : ℝ) - ε) := Real.rpow_pos_of_pos hv0 _
    exact div_le_div_of_nonneg_left hrp.le (by linarith) hlogv
  have hdiv : (∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε) / Real.log X)
      = (∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε)) / Real.log X := integral_div _ _
  rw [hdiv, integral_Ioi_rpow_of_lt hlt hX0] at hmono
  refine le_trans hmono (le_of_eq ?_)
  rw [show -(1 : ℝ) - ε + 1 = -ε by ring]
  field_simp

end Salt.HB
