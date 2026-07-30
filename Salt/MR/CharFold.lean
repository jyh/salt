/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MVHilbertFinset
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# KMT port, wave P-2, stage S3: the all-χ Plancherel fold

Freeze: `docs/exploration/port-freeze-0729.md` (wave P-2).  Refuter verdict R-P3: the fold
is over **all** characters mod `q` — principal and imprimitive included; no primitivity
filter enters (that filter belongs to `Salt.LS.char_LS`, which is a different, Gauss-sum
based argument).

## What this file extracts

`Salt/LS/CharLS.lean`'s `char_LS_perQ` carries, *inside* its proof, a complete
Plancherel identity for the finite Fourier transform on `(ZMod q)ˣ` (the `horth` /
`expand` / `hcollapse` / `hplancherel` / `descend` / `hplancherelR` chain, lines 88–178).
It is stated there only for the additive-character twist `S a = ∑ c n ψ(na)`.  Here it is
restated as a **standalone lemma over an arbitrary `S : ZMod q → ℂ`**:

`char_plancherel : ∑_{χ mod q} ‖∑_{b} χ(b)·S(b)‖² = φ(q)·∑_{b} [IsUnit b] ‖S b‖²`.

The landed `CharLS` is untouched; the proof below is the same argument with the roles of
the two `ZMod q` variables exchanged (the collapse is driven by the `χ⁻¹`-side variable,
which is the one that must be a unit).

## The bridge

`dpolyChi q s a χ t = ∑_{n∈s} aₙ·χ(n)·n^{it}` splits over residue classes:

`dpolyChi q s a χ t = ∑_{b : ZMod q} χ(b) · dpolyS (classSet q s b) a t`,

where `classSet q s b = {n ∈ s : n ≡ b (mod q)}`.  Non-coprime `n` need no special care:
`χ(n) = 0` there, and the fold's right-hand side already discards the non-unit classes.

Composing the two gives the fold pointwise in `t` (`sum_chi_meanSq_pointwise`) and then,
after the (finite-sum ↔ interval-integral) exchange, in integrated form
(`sum_chi_meanSq_fold`).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral

/-! ## The standalone Plancherel identity over all characters mod `q` -/

/-- `conj (χ b) = χ⁻¹ b`. -/
lemma conj_dirichletChar_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ZMod q) :
    (starRingEnd ℂ) (χ b) = χ⁻¹ b := by
  rw [starRingEnd_apply, MulChar.star_apply']

/-- **Second orthogonality** for Dirichlet characters mod `q`, in the shape the fold needs:
for `b` a unit, `∑_χ χ⁻¹(b)·χ(a) = φ(q)·δ_{b,a}`.  (Restated from `CharLS`'s `horth`;
mathlib's engine is `DirichletCharacter.sum_characters_eq`.) -/
lemma sum_char_inv_mul_char {q : ℕ} [NeZero q] {b : ZMod q} (hb : IsUnit b) (a : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ a) = if b = a then (q.totient : ℂ) else 0 := by
  have hterm : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ a = χ (Ring.inverse b * a) := by
    intro χ; rw [MulChar.inv_apply, ← map_mul]
  simp_rw [hterm]
  rw [DirichletCharacter.sum_characters_eq]
  have hiff : (Ring.inverse b * a = 1) ↔ (b = a) := by
    constructor
    · intro h
      have h2 : b * (Ring.inverse b * a) = b * 1 := by rw [h]
      rwa [← mul_assoc, Ring.mul_inverse_cancel b hb, one_mul, mul_one, eq_comm] at h2
    · rintro rfl
      exact Ring.inverse_mul_cancel b hb
  exact if_congr hiff rfl rfl

/-- **S3 (complex form).**  Plancherel for the character transform over *all* `χ` mod `q`. -/
lemma char_plancherel_complex (q : ℕ) [NeZero q] (S : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
        (∑ b : ZMod q, χ b * S b) * (starRingEnd ℂ) (∑ b : ZMod q, χ b * S b))
      = (q.totient : ℂ)
          * ∑ b : ZMod q, (if IsUnit b then S b * (starRingEnd ℂ) (S b) else 0) := by
  set Tc : DirichletCharacter ℂ q → ℂ := fun χ => ∑ b : ZMod q, χ b * S b with hTdef
  have hTval : ∀ χ, Tc χ = ∑ b : ZMod q, χ b * S b := fun χ => by rw [hTdef]
  -- expand `T·conj T` into a double sum, with the `χ⁻¹` variable outermost
  have expand : ∀ χ : DirichletCharacter ℂ q,
      Tc χ * (starRingEnd ℂ) (Tc χ)
        = ∑ b : ZMod q, ∑ a : ZMod q,
            (χ⁻¹ b * χ a) * (S a * (starRingEnd ℂ) (S b)) := by
    intro χ
    have hTc : (starRingEnd ℂ) (Tc χ) = ∑ b : ZMod q, χ⁻¹ b * (starRingEnd ℂ) (S b) := by
      rw [hTval χ, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, conj_dirichletChar_apply χ b]
    rw [mul_comm, hTc, hTval χ, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  -- collapse the character sum, one `b` at a time
  have hcollapse : ∀ b : ZMod q,
      (∑ χ : DirichletCharacter ℂ q, ∑ a : ZMod q,
          (χ⁻¹ b * χ a) * (S a * (starRingEnd ℂ) (S b)))
        = (if IsUnit b then (q.totient : ℂ) * (S b * (starRingEnd ℂ) (S b)) else 0) := by
    intro b
    rw [Finset.sum_comm]
    by_cases hb : IsUnit b
    · rw [if_pos hb]
      have step : ∀ a : ZMod q,
          (∑ χ : DirichletCharacter ℂ q, (χ⁻¹ b * χ a) * (S a * (starRingEnd ℂ) (S b)))
            = (if b = a then (q.totient : ℂ) else 0) * (S a * (starRingEnd ℂ) (S b)) := by
        intro a
        rw [← Finset.sum_mul, sum_char_inv_mul_char hb a]
      rw [Finset.sum_congr rfl fun a _ => step a]
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ b
        fun a => (q.totient : ℂ) * (S a * (starRingEnd ℂ) (S b))]
      rw [if_pos (Finset.mem_univ b)]
    · rw [if_neg hb]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun χ _ => ?_
      rw [MulChar.map_nonunit χ⁻¹ hb, zero_mul, zero_mul]
  calc (∑ χ : DirichletCharacter ℂ q, Tc χ * (starRingEnd ℂ) (Tc χ))
      = ∑ χ : DirichletCharacter ℂ q, ∑ b : ZMod q, ∑ a : ZMod q,
          (χ⁻¹ b * χ a) * (S a * (starRingEnd ℂ) (S b)) :=
        Finset.sum_congr rfl fun χ _ => expand χ
    _ = ∑ b : ZMod q, ∑ χ : DirichletCharacter ℂ q, ∑ a : ZMod q,
          (χ⁻¹ b * χ a) * (S a * (starRingEnd ℂ) (S b)) := Finset.sum_comm
    _ = ∑ b : ZMod q,
          (if IsUnit b then (q.totient : ℂ) * (S b * (starRingEnd ℂ) (S b)) else 0) :=
        Finset.sum_congr rfl fun b _ => hcollapse b
    _ = (q.totient : ℂ)
          * ∑ b : ZMod q, (if IsUnit b then S b * (starRingEnd ℂ) (S b) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> ring

/-- **S3 — THE ALL-χ FOLD (Plancherel, real form).**  For any `S : ZMod q → ℂ`,
`∑_{χ mod q} ‖∑_{b : ZMod q} χ(b)·S(b)‖² = φ(q)·∑_{b : ZMod q} [IsUnit b]·‖S b‖²`.

All `φ(q)` characters participate — principal and imprimitive included.  The non-unit
classes drop out because `χ` vanishes there. -/
theorem char_plancherel (q : ℕ) [NeZero q] (S : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ b * S b‖ ^ 2)
      = (q.totient : ℝ) * ∑ b : ZMod q, (if IsUnit b then ‖S b‖ ^ 2 else 0) := by
  have h := char_plancherel_complex q S
  have descend_lhs : (∑ χ : DirichletCharacter ℂ q,
        (∑ b : ZMod q, χ b * S b) * (starRingEnd ℂ) (∑ b : ZMod q, χ b * S b))
      = ((∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ b * S b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.mul_conj']; norm_cast
  have descend_rhs : (∑ b : ZMod q, (if IsUnit b then S b * (starRingEnd ℂ) (S b) else 0))
      = ((∑ b : ZMod q, (if IsUnit b then ‖S b‖ ^ 2 else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hb
    · rw [Complex.mul_conj']; norm_cast
    · norm_num
  rw [descend_lhs, descend_rhs] at h
  have hcast : ((∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ b * S b‖ ^ 2 : ℝ) : ℂ)
      = (((q.totient : ℝ) * ∑ b : ZMod q, (if IsUnit b then ‖S b‖ ^ 2 else 0) : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast hcast

/-! ## The residue-class decomposition of the twisted Dirichlet polynomial -/

/-- The slice of `s` lying in the residue class `b` mod `q`. -/
def classSet (q : ℕ) (s : Finset ℕ) (b : ZMod q) : Finset ℕ :=
  s.filter (fun n : ℕ => (n : ZMod q) = b)

lemma mem_classSet {q : ℕ} {s : Finset ℕ} {b : ZMod q} {n : ℕ} :
    n ∈ classSet q s b ↔ n ∈ s ∧ (n : ZMod q) = b := by
  simp [classSet]

lemma classSet_subset {q : ℕ} {s : Finset ℕ} {b : ZMod q} : classSet q s b ⊆ s :=
  Finset.filter_subset _ _

/-- The `χ`-twisted Dirichlet polynomial `∑_{n∈s} aₙ·χ(n)·n^{it}` (KMT Lemma 6.2's inner
sum; the `t`-sign is `n^{+it}`, matching the paper — see `dpolyS_meanSq_reflect` for the
`n^{−it}` convention used by the corpus's large-value callers). -/
noncomputable def dpolyChi (q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * χ (n : ZMod q) * Complex.exp (Complex.I * (t : ℂ) * Real.log n)

/-- `dpolyChi q s a χ` is continuous. -/
lemma continuous_dpolyChi (q : ℕ) (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : Continuous (dpolyChi q s a χ) := by
  unfold dpolyChi
  apply continuous_finsetSum
  intro n _
  fun_prop

/-- **The reindex bridge.**  The `χ`-twisted polynomial is the `χ`-weighted combination of
the residue-class polynomials:
`∑_{n∈s} aₙ χ(n) n^{it} = ∑_{b : ZMod q} χ(b)·(∑_{n∈s, n≡b} aₙ n^{it})`. -/
lemma dpolyChi_eq_class_sum (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    dpolyChi q s a χ t = ∑ b : ZMod q, χ b * dpolyS (classSet q s b) a t := by
  have hfib := Finset.sum_fiberwise s (fun n : ℕ => (n : ZMod q))
    (fun n : ℕ => a n * χ (n : ZMod q) * Complex.exp (Complex.I * (t : ℂ) * Real.log n))
  rw [dpolyChi, ← hfib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dpolyS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hb : (n : ZMod q) = b := (Finset.mem_filter.1 hn).2
  rw [hb]
  ring

/-! ## The fold, pointwise and integrated -/

/-- **S3 composed, pointwise in `t`.**  `∑_χ ‖∑_{n∈s} aₙ χ(n) n^{it}‖²`
`= φ(q)·∑_{b unit} ‖∑_{n∈s, n≡b} aₙ n^{it}‖²`. -/
theorem sum_chi_meanSq_pointwise (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, ‖dpolyChi q s a χ t‖ ^ 2)
      = (q.totient : ℝ) * ∑ b : ZMod q,
          (if IsUnit b then ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0) := by
  have hrw : ∀ χ : DirichletCharacter ℂ q,
      ‖dpolyChi q s a χ t‖ ^ 2 = ‖∑ b : ZMod q, χ b * dpolyS (classSet q s b) a t‖ ^ 2 := by
    intro χ; rw [dpolyChi_eq_class_sum q s a χ t]
  rw [Finset.sum_congr rfl fun χ _ => hrw χ]
  exact char_plancherel q (fun b => dpolyS (classSet q s b) a t)

/-- **S3 — THE FOLD, integrated over the symmetric window.**  The `t`-integral passes
through the (finite) character sum and the (finite) class sum:

`∑_{χ mod q} ∫_{-T}^{T} ‖∑_{n∈s} aₙ χ(n) n^{it}‖² dt`
`= φ(q)·∑_{b unit} ∫_{-T}^{T} ‖∑_{n∈s, n≡b} aₙ n^{it}‖² dt`. -/
theorem sum_chi_meanSq_fold (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖dpolyChi q s a χ t‖ ^ 2)
      = (q.totient : ℝ) * ∑ b : ZMod q,
          (if IsUnit b then ∫ t in (-T)..T, ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0) := by
  -- integrability of each χ-piece and each class-piece
  have hIntChi : ∀ χ : DirichletCharacter ℂ q,
      IntervalIntegrable (fun t => ‖dpolyChi q s a χ t‖ ^ 2) volume (-T) T := fun χ =>
    Continuous.intervalIntegrable (((continuous_dpolyChi q s a χ).norm).pow 2) _ _
  have hIntCls : ∀ b : ZMod q,
      IntervalIntegrable (fun t => ‖dpolyS (classSet q s b) a t‖ ^ 2) volume (-T) T := fun b =>
    Continuous.intervalIntegrable (((continuous_dpolyS (classSet q s b) a).norm).pow 2) _ _
  have hIntIf : ∀ b : ZMod q,
      IntervalIntegrable
        (fun t => if IsUnit b then ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0) volume (-T) T := by
    intro b
    by_cases hb : IsUnit b
    · simpa only [if_pos hb] using hIntCls b
    · simpa only [if_neg hb] using
          (_root_.intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-T) T)
  -- pull the χ-sum inside the integral, apply the pointwise fold, push the class-sum out
  calc (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖dpolyChi q s a χ t‖ ^ 2)
      = ∫ t in (-T)..T, ∑ χ : DirichletCharacter ℂ q, ‖dpolyChi q s a χ t‖ ^ 2 :=
        (intervalIntegral.integral_finsetSum (fun χ _ => hIntChi χ)).symm
    _ = ∫ t in (-T)..T, (q.totient : ℝ) * ∑ b : ZMod q,
          (if IsUnit b then ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        exact sum_chi_meanSq_pointwise q s a t
    _ = (q.totient : ℝ) * ∫ t in (-T)..T, ∑ b : ZMod q,
          (if IsUnit b then ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0) :=
        intervalIntegral.integral_const_mul _ _
    _ = (q.totient : ℝ) * ∑ b : ZMod q, ∫ t in (-T)..T,
          (if IsUnit b then ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0) := by
        rw [intervalIntegral.integral_finsetSum (fun b _ => hIntIf b)]
    _ = (q.totient : ℝ) * ∑ b : ZMod q,
          (if IsUnit b then ∫ t in (-T)..T, ‖dpolyS (classSet q s b) a t‖ ^ 2 else 0) := by
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : IsUnit b
        · simp only [if_pos hb]
        · simp only [if_neg hb, intervalIntegral.integral_zero]

end Salt.MR
