/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Exponential sums: the additive character `eR` and the Weyl–van der Corput A-process

This file opens the exponential-sum track of the LITTLEWOOD campaign.

## The additive character

We work with the normalized additive character `e(x) = exp(2πix)`, written `eR`
here. We define it locally rather than reuse mathlib's `Real.fourierChar`: the
latter lands in the group `Circle` and drags a `↑(·) : Circle → ℂ` coercion plus
`AddChar` plumbing through every manipulation. For sums of complex numbers with
norms and conjugation — all we need — a bare `eR : ℝ → ℂ` with a five-lemma API
is strictly cleaner. The API: `eR_add`, `norm_eR`, `eR_neg`, `conj_eR`, and the
differencing identity `eR_mul_conj`.

## The A-process (Weyl differencing / van der Corput)

For a phase `f : ℤ → ℝ` we bound the exponential sum `S = ∑ eR (f n)` over a
window `Ioc a (a+N)` by an average of *differenced* sums. This is the
foundational inequality of the van der Corput method
(Iwaniec–Kowalski Lemma 8.17, Graham–Kolesnik Lemma 2.5), absent from mathlib.

We take `f : ℤ → ℝ` (not `ℕ → ℝ`): the differenced phase `f (n + h) - f n` with
`h : ℤ` an integer shift is then well-typed with no `toNat`/coercion friction,
and the window `Finset.Ioc (a : ℤ) (a + N)` translates cleanly. This is strictly
more general than `ℕ → ℝ` and composes fine with the k-th derivative test
(the intended consumer), which samples a real phase at integer points.
-/

namespace Salt.ExpSum

open Finset
open scoped ComplexConjugate

/-- The normalized additive character `e(x) = exp(2πix)`. -/
noncomputable def eR (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

@[simp] lemma norm_eR (x : ℝ) : ‖eR x‖ = 1 := by
  have h : eR x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    rw [eR]; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma eR_add (x y : ℝ) : eR (x + y) = eR x * eR y := by
  rw [eR, eR, eR, ← Complex.exp_add]; congr 1; push_cast; ring

lemma eR_neg (x : ℝ) : eR (-x) = (eR x)⁻¹ := by
  rw [eR, eR, ← Complex.exp_neg]; congr 1; push_cast; ring

lemma conj_eR (x : ℝ) : conj (eR x) = eR (-x) := by
  rw [eR_neg]; exact (Complex.inv_eq_conj (norm_eR x)).symm

/-- The differencing identity: `eR x · conj (eR y) = eR (x - y)`. -/
lemma eR_mul_conj (x y : ℝ) : eR x * conj (eR y) = eR (x - y) := by
  rw [conj_eR, ← eR_add, ← sub_eq_add_neg]

/-! ## Reindexing helpers for the A-process -/

/-- Translating the window: for `z` vanishing off `Ioc a (a+N)` and a shift
`0 ≤ r ≤ H`, summing `z (· + r)` over the enlarged window `Ioc (a-H) (a+N)`
recovers the full sum of `z`. -/
lemma sum_shift_single (z : ℤ → ℂ) (a : ℤ) (N H : ℕ)
    (hz : ∀ n ∉ Ioc a (a + N), z n = 0) {r : ℤ} (hr0 : 0 ≤ r) (hrH : r ≤ H) :
    ∑ n ∈ Ioc (a - H) (a + N), z (n + r) = ∑ n ∈ Ioc a (a + N), z n := by
  have hmap : (Ioc (a - (H : ℤ)) (a + N)).map (addRightEmbedding r)
      = Ioc (a - H + r) (a + N + r) := map_add_right_Ioc _ _ _
  calc ∑ n ∈ Ioc (a - (H : ℤ)) (a + N), z (n + r)
      = ∑ m ∈ (Ioc (a - (H : ℤ)) (a + N)).map (addRightEmbedding r), z m := by
        rw [Finset.sum_map]; simp only [addRightEmbedding_apply]
    _ = ∑ m ∈ Ioc (a - H + r) (a + N + r), z m := by rw [hmap]
    _ = ∑ n ∈ Ioc a (a + N), z n := by
        symm
        apply Finset.sum_subset
        · intro x hx
          simp only [Finset.mem_Ioc] at hx ⊢
          omega
        · intro x _ hx
          exact hz x hx

/-- Translating the *product* window: shifting both factors by `-r'` collects the
differenced product over the overlap window with `h = r - r'`. -/
lemma sum_shift_prod (z : ℤ → ℂ) (a : ℤ) (N H : ℕ)
    (hz : ∀ n ∉ Ioc a (a + N), z n = 0) {r r' : ℤ}
    (hr'0 : 0 ≤ r') (hr'H : r' ≤ H) :
    ∑ n ∈ Ioc (a - (H : ℤ)) (a + N), z (n + r) * conj (z (n + r')) =
      ∑ m ∈ (Ioc a (a + N)).filter (fun m => m + (r - r') ∈ Ioc a (a + N)),
        z (m + (r - r')) * conj (z m) := by
  have hmap : (Ioc (a - (H : ℤ)) (a + N)).map (addRightEmbedding r')
      = Ioc (a - H + r') (a + N + r') := map_add_right_Ioc _ _ _
  calc ∑ n ∈ Ioc (a - (H : ℤ)) (a + N), z (n + r) * conj (z (n + r'))
      = ∑ n ∈ Ioc (a - (H : ℤ)) (a + N),
          z ((n + r') + (r - r')) * conj (z (n + r')) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [show (n + r') + (r - r') = n + r by ring]
    _ = ∑ m ∈ (Ioc (a - (H : ℤ)) (a + N)).map (addRightEmbedding r'),
          z (m + (r - r')) * conj (z m) := by
        rw [Finset.sum_map]; simp only [addRightEmbedding_apply]
    _ = ∑ m ∈ Ioc (a - H + r') (a + N + r'), z (m + (r - r')) * conj (z m) := by
        rw [hmap]
    _ = ∑ m ∈ (Ioc a (a + N)).filter (fun m => m + (r - r') ∈ Ioc a (a + N)),
          z (m + (r - r')) * conj (z m) := by
        symm
        apply Finset.sum_subset
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
          omega
        · intro x _ hxni
          rw [Finset.mem_filter, not_and] at hxni
          by_cases hxI : x ∈ Ioc a (a + N)
          · rw [hz _ (hxni hxI), zero_mul]
          · rw [hz x hxI, map_zero, mul_zero]

/-! ## The A-process inequality -/

/-- **The Weyl–van der Corput A-process inequality** (Iwaniec–Kowalski Lemma 8.17,
Graham–Kolesnik Lemma 2.5), abstract complex-sequence form. For `z : ℤ → ℂ`
supported on the window `Ioc a (a+N)`, the squared norm of `∑ z` is bounded by an
average — with explicit constant `(N+H)/(H+1)` — of the differenced
auto-correlation sums over the `2H+1` shifts `|h| ≤ H`.

Proof: write `(H+1)·S` as a shifted double count over the enlarged window
`Ioc (a-H) (a+N)`, apply Cauchy–Schwarz, expand the square and collect the
diagonal pairs `(r, r')` by their difference `h = r - r'`. -/
theorem weyl_vdC_sq (z : ℤ → ℂ) (a : ℤ) (N H : ℕ) (_hH : 1 ≤ H) (_hHN : H ≤ N)
    (hz : ∀ n ∉ Ioc a (a + N), z n = 0) :
    ‖∑ n ∈ Ioc a (a + N), z n‖ ^ 2 ≤
      ((N + H : ℝ) / (H + 1)) *
        ∑ h ∈ Icc (-(H : ℤ)) H,
          ‖∑ n ∈ (Ioc a (a + N)).filter (fun n => n + h ∈ Ioc a (a + N)),
              z (n + h) * conj (z n)‖ := by
  classical
  set S : ℂ := ∑ n ∈ Ioc a (a + N), z n with hSdef
  set R : Finset ℤ := Icc (0 : ℤ) H with hRdef
  set J : Finset ℤ := Ioc (a - (H : ℤ)) (a + N) with hJdef
  set w : ℤ → ℂ := fun n => ∑ r ∈ R, z (n + r) with hwdef
  set G : ℤ → ℂ :=
    fun h => ∑ n ∈ (Ioc a (a + N)).filter (fun n => n + h ∈ Ioc a (a + N)),
      z (n + h) * conj (z n) with hGdef
  -- Fold the goal's inner sums into `G`.
  rw [show (∑ h ∈ Icc (-(H : ℤ)) H,
        ‖∑ n ∈ (Ioc a (a + N)).filter (fun n => n + h ∈ Ioc a (a + N)),
            z (n + h) * conj (z n)‖) = ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖ from by
      simp only [hGdef]]
  -- Cardinalities.
  have hRcard : R.card = H + 1 := by rw [hRdef, Int.card_Icc]; omega
  have hJcard : (J.card : ℝ) = N + H := by
    have hc : J.card = N + H := by rw [hJdef, Int.card_Ioc]; omega
    rw [hc]; push_cast; ring
  -- Claim 1: `(H+1)·S` as a shifted double count.
  have hClaim1 : ∑ n ∈ J, w n = ((H : ℂ) + 1) * S := by
    have hinner : ∀ r ∈ R, ∑ n ∈ J, z (n + r) = S := by
      intro r hr
      rw [hRdef, Finset.mem_Icc] at hr
      rw [hJdef, hSdef]
      exact sum_shift_single z a N H hz hr.1 hr.2
    calc ∑ n ∈ J, w n = ∑ n ∈ J, ∑ r ∈ R, z (n + r) := by simp only [hwdef]
      _ = ∑ r ∈ R, ∑ n ∈ J, z (n + r) := Finset.sum_comm
      _ = ∑ r ∈ R, S := Finset.sum_congr rfl hinner
      _ = R.card • S := Finset.sum_const S
      _ = ((H : ℂ) + 1) * S := by rw [hRcard, nsmul_eq_mul]; push_cast; ring
  -- Claim 2: Cauchy–Schwarz for the double count.
  have hClaim2 : ‖∑ n ∈ J, w n‖ ^ 2 ≤ (N + H : ℝ) * ∑ n ∈ J, ‖w n‖ ^ 2 := by
    have h1 : ‖∑ n ∈ J, w n‖ ≤ ∑ n ∈ J, ‖w n‖ := norm_sum_le _ _
    have h2 : (∑ n ∈ J, ‖w n‖) ^ 2 ≤ (J.card : ℝ) * ∑ n ∈ J, ‖w n‖ ^ 2 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) (fun n => ‖w n‖)
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using hcs
    calc ‖∑ n ∈ J, w n‖ ^ 2 ≤ (∑ n ∈ J, ‖w n‖) ^ 2 := by
          nlinarith [h1, norm_nonneg (∑ n ∈ J, w n),
            Finset.sum_nonneg (fun n (_ : n ∈ J) => norm_nonneg (w n))]
      _ ≤ (J.card : ℝ) * ∑ n ∈ J, ‖w n‖ ^ 2 := h2
      _ = (N + H : ℝ) * ∑ n ∈ J, ‖w n‖ ^ 2 := by rw [hJcard]
  -- Claim 3: expand the square, collect by the difference `h = r - r'`.
  have hstep1 : ((∑ n ∈ J, ‖w n‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ J, w n * conj (w n) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hstep2 : ∑ n ∈ J, w n * conj (w n)
      = ∑ n ∈ J, ∑ r ∈ R, ∑ r' ∈ R, z (n + r) * conj (z (n + r')) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hwdef]
    rw [map_sum, Finset.sum_mul_sum]
  have hstep3 : ∑ n ∈ J, ∑ r ∈ R, ∑ r' ∈ R, z (n + r) * conj (z (n + r'))
      = ∑ r ∈ R, ∑ r' ∈ R, G (r - r') := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r' hr' => ?_)
    rw [hRdef, Finset.mem_Icc] at hr'
    rw [hGdef, hJdef]
    exact sum_shift_prod z a N H hz hr'.1 hr'.2
  have h3a : (∑ n ∈ J, ‖w n‖ ^ 2 : ℝ) = (∑ r ∈ R, ∑ r' ∈ R, G (r - r')).re := by
    have hC : ((∑ n ∈ J, ‖w n‖ ^ 2 : ℝ) : ℂ)
        = ∑ r ∈ R, ∑ r' ∈ R, G (r - r') := by
      rw [hstep1, hstep2, hstep3]
    calc (∑ n ∈ J, ‖w n‖ ^ 2 : ℝ)
        = (((∑ n ∈ J, ‖w n‖ ^ 2 : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]
      _ = (∑ r ∈ R, ∑ r' ∈ R, G (r - r')).re := by rw [hC]
  have h3b : (∑ r ∈ R, ∑ r' ∈ R, G (r - r')).re
      ≤ (H + 1 : ℝ) * ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖ := by
    rw [Complex.re_sum]
    have hre : ∀ r ∈ R, (∑ r' ∈ R, G (r - r')).re
        ≤ ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖ := by
      intro r hr
      rw [hRdef, Finset.mem_Icc] at hr
      obtain ⟨hr0, hrH⟩ := hr
      rw [Complex.re_sum]
      calc ∑ r' ∈ R, (G (r - r')).re
          ≤ ∑ r' ∈ R, ‖G (r - r')‖ := Finset.sum_le_sum (fun r' _ => Complex.re_le_norm _)
        _ = ∑ h ∈ R.image (fun r' => r - r'), ‖G h‖ := by
            have hinj : Set.InjOn (fun r' : ℤ => r - r') (R : Set ℤ) := by
              intro x _ y _ hxy
              simp only [sub_right_inj] at hxy
              exact hxy
            rw [Finset.sum_image hinj]
        _ ≤ ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro h hh
              simp only [Finset.mem_image] at hh
              obtain ⟨r', hr', rfl⟩ := hh
              rw [hRdef, Finset.mem_Icc] at hr'
              obtain ⟨hr'0, hr'H⟩ := hr'
              simp only [Finset.mem_Icc]
              omega
            · intro h _ _; exact norm_nonneg _
    calc ∑ r ∈ R, (∑ r' ∈ R, G (r - r')).re
        ≤ ∑ r ∈ R, ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖ := Finset.sum_le_sum hre
      _ = R.card • ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖ := Finset.sum_const _
      _ = (H + 1 : ℝ) * ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖ := by
          rw [hRcard, nsmul_eq_mul]; push_cast; ring
  -- Combine the three claims.
  have hnormEq : ‖∑ n ∈ J, w n‖ = ((H : ℝ) + 1) * ‖S‖ := by
    rw [hClaim1, norm_mul]
    congr 1
    rw [show ((H : ℂ) + 1) = (((H : ℝ) + 1 : ℝ) : ℂ) from by push_cast; ring]
    exact Complex.norm_of_nonneg (by positivity)
  have hbig : ((H : ℝ) + 1) ^ 2 * ‖S‖ ^ 2
      ≤ (N + H : ℝ) * ((H + 1 : ℝ) * ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖) := by
    calc ((H : ℝ) + 1) ^ 2 * ‖S‖ ^ 2 = ‖∑ n ∈ J, w n‖ ^ 2 := by rw [hnormEq]; ring
      _ ≤ (N + H : ℝ) * ∑ n ∈ J, ‖w n‖ ^ 2 := hClaim2
      _ ≤ (N + H : ℝ) * ((H + 1 : ℝ) * ∑ h ∈ Icc (-(H : ℤ)) H, ‖G h‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [h3a]; exact h3b
  have hHpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hHpos]
  nlinarith [hbig, hHpos, mul_pos hHpos hHpos]

/-- **The A-process for exponential sums.** Specializing `weyl_vdC_sq` to the
sequence `z n = e(f n)` (extended by zero off the window). The differenced
auto-correlations become the classical `∑ e(f (n+h) - f n)`. This is the form the
van der Corput derivative tests consume. -/
theorem weyl_vdC_expSum (f : ℤ → ℝ) (a : ℤ) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    ‖∑ n ∈ Ioc a (a + N), eR (f n)‖ ^ 2 ≤
      ((N + H : ℝ) / (H + 1)) *
        ∑ h ∈ Icc (-(H : ℤ)) H,
          ‖∑ n ∈ (Ioc a (a + N)).filter (fun n => n + h ∈ Ioc a (a + N)),
              eR (f (n + h) - f n)‖ := by
  classical
  set z : ℤ → ℂ := fun n => if n ∈ Ioc a (a + N) then eR (f n) else 0 with hzdef
  have hz : ∀ n ∉ Ioc a (a + N), z n = 0 := by
    intro n hn; simp only [hzdef, if_neg hn]
  have hLHS : ∑ n ∈ Ioc a (a + N), z n = ∑ n ∈ Ioc a (a + N), eR (f n) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [hzdef, if_pos hn]
  have hInner : ∀ h : ℤ,
      ∑ n ∈ (Ioc a (a + N)).filter (fun n => n + h ∈ Ioc a (a + N)),
          z (n + h) * conj (z n)
        = ∑ n ∈ (Ioc a (a + N)).filter (fun n => n + h ∈ Ioc a (a + N)),
            eR (f (n + h) - f n) := by
    intro h
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_filter] at hn
    obtain ⟨hnI, hnhI⟩ := hn
    simp only [hzdef]
    rw [if_pos hnhI, if_pos hnI, eR_mul_conj]
  calc ‖∑ n ∈ Ioc a (a + N), eR (f n)‖ ^ 2
      = ‖∑ n ∈ Ioc a (a + N), z n‖ ^ 2 := by rw [hLHS]
    _ ≤ ((N + H : ℝ) / (H + 1)) *
          ∑ h ∈ Icc (-(H : ℤ)) H,
            ‖∑ n ∈ (Ioc a (a + N)).filter (fun n => n + h ∈ Ioc a (a + N)),
                z (n + h) * conj (z n)‖ := weyl_vdC_sq z a N H hH hHN hz
    _ = ((N + H : ℝ) / (H + 1)) *
          ∑ h ∈ Icc (-(H : ℤ)) H,
            ‖∑ n ∈ (Ioc a (a + N)).filter (fun n => n + h ∈ Ioc a (a + N)),
                eR (f (n + h) - f n)‖ := by
        congr 1
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [hInner h]

end Salt.ExpSum
