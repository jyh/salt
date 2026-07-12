/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.PolyaVinogradov
import Salt.LS.TypeSums

/-!
# V2a — the Type I estimate via Pólya–Vinogradov

Design: `docs/blueprints/bv.md`, node `V2a`. Two frozen bounds on the Type I pieces
of Vaughan's identity, twisted by a primitive Dirichlet character and cut off at an
arbitrary prefix `y ≤ x` (the maximal / `sup'` form the dispersion step consumes).

The two pieces come from `Salt/LS/TypeSums.lean` (`typeI_one_eq` / `typeI_two_eq`),
specialised to the character weight `f := fun n => χ n`; multiplicativity
`χ(d·m) = χ(d)·χ(m)` (`chi_cast_mul`) frees the `m`-sum, which — for fixed outer
index `d` — runs over the contiguous interval `Ioc (V/d) (y/d)` (`filter_eq_Ioc`).
Pólya–Vinogradov (`polya_vinogradov`, `Salt/BV/PolyaVinogradov.lean`) bounds the plain
prefix sums `‖∑_{m<t} χ(m)‖ ≤ √f·(1+log f)`, uniformly in `t`.

* **TypeI₁** (weight `log m`, mass `U`): Abel summation (`Finset.sum_Ioc_by_parts`)
  against the PV prefix bound turns the log-weighted interval sum into `≤ 3·log y·√f·
  (1+log f)` (`abel_log_char_le`); summing over the `≤ U` values of `d` gives mass `U`.
* **TypeI₂** (weight `1`, mass `U·V`): the plain interval sum is a difference of two PV
  prefixes, `≤ 2·√f·(1+log f)` (`interval_char_le`); the outer coefficient
  `typeICoeff U V t` has `|a(t)| ≤ log t` and support `t ≤ U·V`
  (`abs_typeICoeff_le`, `typeICoeff_eq_zero`), giving `∑_t |a(t)| ≤ U·V·log x`.

The `f`-summed assembly (`typeI_one_maxdisc_le`, `typeI_two_maxdisc_le`) collapses the
`(1/φf)·∑_{χ prim}` weight via `#{χ prim} ≤ φ(f)` (`card_primitive_le`), leaving the
frozen `C·mass·(∑_f √f)·(1+log x)²` shape. See the report for the `Q ≤ x` handling.

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.BV

open Finset Salt.LS ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

/-! ## The two Type I pieces, twisted and cut off at `y` -/

/-- The first Type I piece (`Σ₁` of Vaughan), character-twisted, cut off at `y`.
Matches the `TypeI₁` summand of `psiChi_sub_head_eq` with `x := y`. -/
noncomputable def typeI₁ (U V y : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 y).filter (· ≤ U), (μ d : ℂ) *
    ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y),
      (Real.log (m : ℝ) : ℂ) * χ ((d * m : ℕ) : ZMod q)

/-- The second Type I piece (`Σ₂` of Vaughan), character-twisted, cut off at `y`.
Matches the `TypeI₂` summand of `psiChi_sub_head_eq` with `x := y`. -/
noncomputable def typeI₂ (U V y : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ t ∈ Finset.Icc 1 y, (typeICoeff U V t : ℂ) *
    ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < t * m ∧ t * m ≤ y),
      χ ((t * m : ℕ) : ZMod q)

/-! ## The inner `m`-range is a contiguous interval -/

/-- For `d ≥ 1`, the coupled guard `1 ≤ m ≤ y ∧ V < d·m ≤ y` is exactly `V/d < m ≤ y/d`. -/
private lemma filter_eq_Ioc (V y d : ℕ) (hd : 1 ≤ d) :
    (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y) = Finset.Ioc (V / d) (y / d) := by
  have hd0 : 0 < d := hd
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_h1, _hmy⟩, hVdm, hdmy⟩
    refine ⟨(Nat.div_lt_iff_lt_mul hd0).mpr ?_, (Nat.le_div_iff_mul_le hd0).mpr ?_⟩
    · rwa [Nat.mul_comm]
    · rwa [Nat.mul_comm]
  · rintro ⟨hVd, hyd⟩
    have hVdm : V < d * m := by rw [Nat.mul_comm]; exact (Nat.div_lt_iff_lt_mul hd0).mp hVd
    have hdmy : d * m ≤ y := by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hd0).mp hyd
    have hm1 : 1 ≤ m := Nat.lt_of_le_of_lt (Nat.zero_le _) hVd
    have hmy : m ≤ y := le_trans hyd (Nat.div_le_self y d)
    exact ⟨⟨hm1, hmy⟩, hVdm, hdmy⟩

/-! ## Pólya–Vinogradov: the plain and the Abel-weighted interval bounds -/

/-- **Plain interval bound.** `‖∑_{m ∈ Ioc a b} χ(m)‖ ≤ 2·√f·(1+log f)`, the moving
window written as a difference of two PV prefixes. -/
private lemma interval_char_le {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (a b : ℕ) :
    ‖∑ m ∈ Finset.Ioc a b, χ (m : ZMod f)‖ ≤ 2 * (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))) := by
  have hlogf0 : 0 ≤ Real.log (f : ℝ) := Real.log_natCast_nonneg f
  have hB0 : 0 ≤ Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hPV : ∀ k, ‖∑ i ∈ Finset.range k, χ (i : ZMod f)‖
      ≤ Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)) := fun k => polya_vinogradov χ hχ hf k
  by_cases hab : a < b
  · have hcons := Finset.sum_Ico_consecutive (fun m => χ (m : ZMod f))
      (Nat.zero_le (a + 1)) (show a + 1 ≤ b + 1 by omega)
    have hdiff : ∑ m ∈ Finset.Ioc a b, χ (m : ZMod f)
        = (∑ m ∈ Finset.range (b + 1), χ (m : ZMod f))
          - ∑ m ∈ Finset.range (a + 1), χ (m : ZMod f) := by
      rw [← Finset.Ico_add_one_add_one_eq_Ioc, ← Nat.Ico_zero_eq_range (b + 1),
        ← Nat.Ico_zero_eq_range (a + 1), ← hcons]
      ring
    rw [hdiff]
    calc ‖(∑ m ∈ Finset.range (b + 1), χ (m : ZMod f))
            - ∑ m ∈ Finset.range (a + 1), χ (m : ZMod f)‖
        ≤ ‖∑ m ∈ Finset.range (b + 1), χ (m : ZMod f)‖
          + ‖∑ m ∈ Finset.range (a + 1), χ (m : ZMod f)‖ := norm_sub_le _ _
      _ ≤ (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)))
          + (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))) := add_le_add (hPV _) (hPV _)
      _ = 2 * (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))) := by ring
  · rw [Finset.Ioc_eq_empty hab, Finset.sum_empty, norm_zero]
    positivity

/-- **Abel-weighted interval bound.** `‖∑_{m ∈ Ioc a b} log(m)·χ(m)‖ ≤ 3·log b·√f·
(1+log f)`.  Summation by parts (`Finset.sum_Ioc_by_parts`) against the PV prefix bound;
the two boundary terms and the (telescoping, monotone) inner sum each contribute
`≤ log b·√f·(1+log f)`. -/
private lemma abel_log_char_le {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (a b : ℕ) :
    ‖∑ m ∈ Finset.Ioc a b, (Real.log (m : ℝ) : ℂ) * χ (m : ZMod f)‖
      ≤ 3 * Real.log (b : ℝ) * (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))) := by
  set B := Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)) with hBdef
  have hlogf0 : 0 ≤ Real.log (f : ℝ) := Real.log_natCast_nonneg f
  have hB0 : 0 ≤ B := by rw [hBdef]; exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hlogb0 : 0 ≤ Real.log (b : ℝ) := Real.log_natCast_nonneg b
  have hPV : ∀ k, ‖∑ i ∈ Finset.range k, χ (i : ZMod f)‖ ≤ B := fun k => polya_vinogradov χ hχ hf k
  by_cases hab : a < b
  · have hbp := Finset.sum_Ioc_by_parts (fun i => (Real.log (i : ℝ) : ℂ))
      (fun i => χ (i : ZMod f)) hab
    simp only [smul_eq_mul] at hbp
    rw [hbp]
    -- name the three pieces
    set S1 := ∑ i ∈ Finset.range (b + 1), χ (i : ZMod f) with hS1
    set S2 := ∑ i ∈ Finset.range (a + 1), χ (i : ZMod f) with hS2
    set S3 := ∑ i ∈ Finset.Ioc a (b - 1),
        ((Real.log ((i + 1 : ℕ) : ℝ) : ℂ) - (Real.log (i : ℝ) : ℂ)) *
          ∑ j ∈ Finset.range (i + 1), χ (j : ZMod f) with hS3
    -- boundary term 1
    have hT1 : ‖(Real.log (b : ℝ) : ℂ) * S1‖ ≤ Real.log (b : ℝ) * B := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogb0]
      exact mul_le_mul_of_nonneg_left (by rw [hS1]; exact hPV (b + 1)) hlogb0
    -- boundary term 2
    have hloga10 : 0 ≤ Real.log ((a + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg (a + 1)
    have hloga1b : Real.log ((a + 1 : ℕ) : ℝ) ≤ Real.log (b : ℝ) :=
      Real.log_le_log (by exact_mod_cast Nat.succ_pos a) (by exact_mod_cast (by omega : a + 1 ≤ b))
    have hT2 : ‖(Real.log ((a + 1 : ℕ) : ℝ) : ℂ) * S2‖ ≤ Real.log (b : ℝ) * B := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hloga10]
      calc Real.log ((a + 1 : ℕ) : ℝ) * ‖S2‖
          ≤ Real.log ((a + 1 : ℕ) : ℝ) * B :=
            mul_le_mul_of_nonneg_left (by rw [hS2]; exact hPV (a + 1)) hloga10
        _ ≤ Real.log (b : ℝ) * B := mul_le_mul_of_nonneg_right hloga1b hB0
    -- the inner (telescoping) sum
    have hT3 : ‖S3‖ ≤ Real.log (b : ℝ) * B := by
      rw [hS3]
      calc ‖∑ i ∈ Finset.Ioc a (b - 1),
              ((Real.log ((i + 1 : ℕ) : ℝ) : ℂ) - (Real.log (i : ℝ) : ℂ)) *
                ∑ j ∈ Finset.range (i + 1), χ (j : ZMod f)‖
          ≤ ∑ i ∈ Finset.Ioc a (b - 1),
              ‖((Real.log ((i + 1 : ℕ) : ℝ) : ℂ) - (Real.log (i : ℝ) : ℂ)) *
                ∑ j ∈ Finset.range (i + 1), χ (j : ZMod f)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.Ioc a (b - 1),
              (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) * B := by
            refine Finset.sum_le_sum fun i hi => ?_
            simp only [Finset.mem_Ioc] at hi
            have hi1 : 1 ≤ i := by omega
            have hmono : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
              Real.log_le_log (by exact_mod_cast hi1)
                (by exact_mod_cast (by omega : i ≤ i + 1))
            rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith)]
            exact mul_le_mul_of_nonneg_left (hPV (i + 1)) (by linarith)
        _ = (∑ i ∈ Finset.Ioc a (b - 1),
              (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ))) * B := by rw [Finset.sum_mul]
        _ ≤ (∑ i ∈ Finset.range b,
              (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ))) * B := by
            refine mul_le_mul_of_nonneg_right ?_ hB0
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro i hi; simp only [Finset.mem_Ioc] at hi; simp only [Finset.mem_range]; omega
            · intro i _ _
              rcases Nat.eq_zero_or_pos i with h | h
              · subst h
                simp only [Nat.cast_zero, Real.log_zero, Nat.zero_add, sub_zero]
                exact Real.log_natCast_nonneg 1
              · have : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
                  Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast (by omega : i ≤ i + 1))
                linarith
        _ = Real.log (b : ℝ) * B := by
            have hts : (∑ i ∈ Finset.range b,
                (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ))) = Real.log (b : ℝ) := by
              have h := Finset.sum_range_sub (fun i => Real.log (i : ℝ)) b
              simpa only [Nat.cast_zero, Real.log_zero, sub_zero] using h
            rw [hts]
    -- combine the three
    refine le_trans (norm_sub_le _ _) ?_
    calc ‖(Real.log (b : ℝ) : ℂ) * S1 - (Real.log ((a + 1 : ℕ) : ℝ) : ℂ) * S2‖ + ‖S3‖
        ≤ (‖(Real.log (b : ℝ) : ℂ) * S1‖ + ‖(Real.log ((a + 1 : ℕ) : ℝ) : ℂ) * S2‖) + ‖S3‖ :=
          add_le_add (norm_sub_le _ _) (le_refl _)
      _ ≤ Real.log (b : ℝ) * B + Real.log (b : ℝ) * B + Real.log (b : ℝ) * B :=
          add_le_add (add_le_add hT1 hT2) hT3
      _ = 3 * Real.log (b : ℝ) * B := by ring
  · rw [Finset.Ioc_eq_empty hab, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hlogb0) hB0

/-! ## The primitive-character count -/

open Classical in
/-- `#{χ prim mod f} ≤ φ(f)`: there are exactly `φ(f)` Dirichlet characters mod `f`
(`card_eq_totient_of_hasEnoughRootsOfUnity`), and the primitive ones are a subset. -/
theorem card_primitive_le (f : ℕ) [NeZero f] :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive)).card ≤ f.totient := by
  calc (Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive)).card
      ≤ (Finset.univ : Finset (DirichletCharacter ℂ f)).card := Finset.card_filter_le _ _
    _ = Fintype.card (DirichletCharacter ℂ f) := Finset.card_univ
    _ = Nat.card (DirichletCharacter ℂ f) := (Nat.card_eq_fintype_card).symm
    _ = f.totient := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ f

/-- `∑_{f ∈ Icc 1 Q} √f ≤ Q·√Q` (each summand `≤ √Q`, and `#(Icc 1 Q) = Q`). -/
theorem sqrt_sum_le (Q : ℕ) :
    ∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ) ≤ (Q : ℝ) * Real.sqrt (Q : ℝ) := by
  calc ∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)
      ≤ ∑ _f ∈ Finset.Icc 1 Q, Real.sqrt (Q : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        simp only [Finset.mem_Icc] at hi
        exact Real.sqrt_le_sqrt (by exact_mod_cast hi.2)
    _ = ((Finset.Icc 1 Q).card : ℝ) * Real.sqrt (Q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Q : ℝ) * Real.sqrt (Q : ℝ) := by rw [Nat.card_Icc]; simp

/-! ## The per-character bounds -/

/-- **TypeI₁, per primitive `χ`.** `max_{y ≤ x} ‖TypeI₁(y, χ)‖ ≤ 3·U·(1+log x)·√f·
(1+log f)`.  The `max` is free because the PV/Abel bound is `y`-uniform. -/
theorem typeI_one_char_le {x U V : ℕ} {f : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hχ : χ.IsPrimitive) (hf : 2 ≤ f) :
    (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
        (fun y => ‖typeI₁ U V y χ‖)
      ≤ 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) * (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))) := by
  set B := Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)) with hBdef
  have hlogf0 : 0 ≤ Real.log (f : ℝ) := Real.log_natCast_nonneg f
  have hB0 : 0 ≤ B := by rw [hBdef]; exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hlogx0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hUnn : 0 ≤ (U : ℝ) := Nat.cast_nonneg U
  rw [Finset.sup'_le_iff]
  intro y hy
  have hyx : y ≤ x := (Finset.mem_Icc.mp hy).2
  simp only [typeI₁]
  calc ‖∑ d ∈ (Finset.Icc 1 y).filter (· ≤ U), (μ d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y),
            (Real.log (m : ℝ) : ℂ) * χ ((d * m : ℕ) : ZMod f)‖
      ≤ ∑ d ∈ (Finset.Icc 1 y).filter (· ≤ U),
          ‖(μ d : ℂ) * ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y),
            (Real.log (m : ℝ) : ℂ) * χ ((d * m : ℕ) : ZMod f)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ (Finset.Icc 1 y).filter (· ≤ U), 3 * Real.log (x : ℝ) * B := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
        have hsplit : ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < d * m ∧ d * m ≤ y),
              (Real.log (m : ℝ) : ℂ) * χ ((d * m : ℕ) : ZMod f)
            = χ (d : ZMod f) *
                ∑ m ∈ Finset.Ioc (V / d) (y / d), (Real.log (m : ℝ) : ℂ) * χ (m : ZMod f) := by
          rw [filter_eq_Ioc V y d hd1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [chi_cast_mul χ d m]; ring
        rw [hsplit, norm_mul, norm_mul]
        have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
        have habel := abel_log_char_le χ hχ hf (V / d) (y / d)
        have hlogyd : Real.log ((y / d : ℕ) : ℝ) ≤ Real.log (x : ℝ) := by
          rcases Nat.eq_zero_or_pos (y / d) with h0 | hp
          · rw [h0]; simpa using hlogx0
          · exact Real.log_le_log (by exact_mod_cast hp)
              (by exact_mod_cast (le_trans (Nat.div_le_self y d) hyx))
        calc ‖(μ d : ℂ)‖ *
              (‖χ (d : ZMod f)‖ *
                ‖∑ m ∈ Finset.Ioc (V / d) (y / d), (Real.log (m : ℝ) : ℂ) * χ (m : ZMod f)‖)
            ≤ 1 * (1 * (3 * Real.log ((y / d : ℕ) : ℝ) * B)) := by
              refine mul_le_mul hμ ?_ (by positivity) (by norm_num)
              exact mul_le_mul (χ.norm_le_one _) habel (norm_nonneg _) (by norm_num)
          _ = 3 * Real.log ((y / d : ℕ) : ℝ) * B := by ring
          _ ≤ 3 * Real.log (x : ℝ) * B :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogyd (by norm_num)) hB0
    _ = (((Finset.Icc 1 y).filter (· ≤ U)).card : ℝ) * (3 * Real.log (x : ℝ) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (U : ℝ) * (3 * Real.log (x : ℝ) * B) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg (by norm_num) hlogx0) hB0)
        have hcard : ((Finset.Icc 1 y).filter (· ≤ U)).card ≤ U := by
          calc ((Finset.Icc 1 y).filter (· ≤ U)).card ≤ (Finset.Icc 1 U).card := by
                refine Finset.card_le_card fun d hd => ?_
                simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢; omega
            _ = U := by rw [Nat.card_Icc]; omega
        exact_mod_cast hcard
    _ ≤ 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) * B := by
        have h3UB : (0 : ℝ) ≤ 3 * (U : ℝ) * B := mul_nonneg (mul_nonneg (by norm_num) hUnn) hB0
        calc (U : ℝ) * (3 * Real.log (x : ℝ) * B) = (3 * (U : ℝ) * B) * Real.log (x : ℝ) := by ring
          _ ≤ (3 * (U : ℝ) * B) * (1 + Real.log (x : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith) h3UB
          _ = 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) * B := by ring

/-- **TypeI₂, per primitive `χ`.** `max_{y ≤ x} ‖TypeI₂(y, χ)‖ ≤ 2·(U·V)·(1+log x)·√f·
(1+log f)`.  Plain PV (weight `1`); the outer coefficient mass is `∑_t |a(t)| ≤ U·V·log x`. -/
theorem typeI_two_char_le {x U V : ℕ} {f : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hχ : χ.IsPrimitive) (hf : 2 ≤ f) :
    (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
        (fun y => ‖typeI₂ U V y χ‖)
      ≤ 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) *
          (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ))) := by
  set B := Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)) with hBdef
  have hlogf0 : 0 ≤ Real.log (f : ℝ) := Real.log_natCast_nonneg f
  have hB0 : 0 ≤ B := by rw [hBdef]; exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hB20 : (0 : ℝ) ≤ 2 * B := by linarith
  have hlogx0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hUVnn : (0 : ℝ) ≤ (U : ℝ) * (V : ℝ) := by positivity
  rw [Finset.sup'_le_iff]
  intro y hy
  have hyx : y ≤ x := (Finset.mem_Icc.mp hy).2
  simp only [typeI₂]
  -- outer coefficient mass
  have hcoeffsum : ∑ t ∈ Finset.Icc 1 y, |typeICoeff U V t|
      ≤ (U : ℝ) * (V : ℝ) * Real.log (x : ℝ) := by
    have hdrop : ∑ t ∈ Finset.Icc 1 y, |typeICoeff U V t|
        = ∑ t ∈ (Finset.Icc 1 y).filter (· ≤ U * V), |typeICoeff U V t| := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro t ht htn
      have : ¬ (t ≤ U * V) := fun hle => htn (Finset.mem_filter.mpr ⟨ht, hle⟩)
      rw [typeICoeff_eq_zero (by omega : U * V < t), abs_zero]
    rw [hdrop]
    calc ∑ t ∈ (Finset.Icc 1 y).filter (· ≤ U * V), |typeICoeff U V t|
        ≤ ∑ _t ∈ (Finset.Icc 1 y).filter (· ≤ U * V), Real.log (x : ℝ) := by
          refine Finset.sum_le_sum fun t ht => ?_
          simp only [Finset.mem_filter, Finset.mem_Icc] at ht
          calc |typeICoeff U V t| ≤ Real.log (t : ℝ) := abs_typeICoeff_le U V t
            _ ≤ Real.log (x : ℝ) := Real.log_le_log (by exact_mod_cast ht.1.1)
                (by exact_mod_cast (le_trans ht.1.2 hyx))
      _ = (((Finset.Icc 1 y).filter (· ≤ U * V)).card : ℝ) * Real.log (x : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (U : ℝ) * (V : ℝ) * Real.log (x : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogx0
          have hcard : ((Finset.Icc 1 y).filter (· ≤ U * V)).card ≤ U * V := by
            calc ((Finset.Icc 1 y).filter (· ≤ U * V)).card ≤ (Finset.Icc 1 (U * V)).card := by
                  refine Finset.card_le_card fun t ht => ?_
                  simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢; omega
              _ = U * V := by rw [Nat.card_Icc]; omega
          calc (((Finset.Icc 1 y).filter (· ≤ U * V)).card : ℝ) ≤ ((U * V : ℕ) : ℝ) := by
                exact_mod_cast hcard
            _ = (U : ℝ) * (V : ℝ) := by push_cast; ring
  calc ‖∑ t ∈ Finset.Icc 1 y, (typeICoeff U V t : ℂ) *
          ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < t * m ∧ t * m ≤ y), χ ((t * m : ℕ) : ZMod f)‖
      ≤ ∑ t ∈ Finset.Icc 1 y,
          ‖(typeICoeff U V t : ℂ) *
            ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < t * m ∧ t * m ≤ y),
              χ ((t * m : ℕ) : ZMod f)‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.Icc 1 y, |typeICoeff U V t| * (2 * B) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        have hsplit : ∑ m ∈ (Finset.Icc 1 y).filter (fun m => V < t * m ∧ t * m ≤ y),
              χ ((t * m : ℕ) : ZMod f)
            = χ (t : ZMod f) * ∑ m ∈ Finset.Ioc (V / t) (y / t), χ (m : ZMod f) := by
          rw [filter_eq_Ioc V y t ht1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [chi_cast_mul χ t m]
        rw [hsplit, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc ‖χ (t : ZMod f)‖ * ‖∑ m ∈ Finset.Ioc (V / t) (y / t), χ (m : ZMod f)‖
            ≤ 1 * (2 * B) :=
              mul_le_mul (χ.norm_le_one _) (interval_char_le χ hχ hf (V / t) (y / t))
                (norm_nonneg _) (by norm_num)
          _ = 2 * B := one_mul _
    _ = (∑ t ∈ Finset.Icc 1 y, |typeICoeff U V t|) * (2 * B) := by rw [Finset.sum_mul]
    _ ≤ ((U : ℝ) * (V : ℝ) * Real.log (x : ℝ)) * (2 * B) :=
        mul_le_mul_of_nonneg_right hcoeffsum hB20
    _ ≤ 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) * B := by
        have h2UVB : (0 : ℝ) ≤ 2 * ((U : ℝ) * (V : ℝ)) * B :=
          mul_nonneg (mul_nonneg (by norm_num) hUVnn) hB0
        calc ((U : ℝ) * (V : ℝ) * Real.log (x : ℝ)) * (2 * B)
            = (2 * ((U : ℝ) * (V : ℝ)) * B) * Real.log (x : ℝ) := by ring
          _ ≤ (2 * ((U : ℝ) * (V : ℝ)) * B) * (1 + Real.log (x : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith) h2UVB
          _ = 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) * B := by ring

/-! ## The frozen `f`-summed masses -/

open Classical in
/-- **V2a, TypeI₁ (mass `U`).** For `2 ≤ x` and `Q ≤ x`,
`∑_{2 ≤ f ≤ Q} (1/φf) ∑_{χ prim} max_{y ≤ x} ‖TypeI₁(y,χ)‖ ≤ 3·U·(∑_f √f)·(1+log x)²`.
The `(1/φf)·∑_χ` collapses via `#{χ prim} ≤ φf`; `Q ≤ x` folds `(1+log f) ≤ (1+log x)`. -/
theorem typeI_one_maxdisc_le {x U V Q : ℕ} (_hx : 2 ≤ x) (_hU : 1 ≤ U) (_hV : 1 ≤ V)
    (hQx : Q ≤ x) :
    ∑ f ∈ (Finset.Icc 1 Q).filter (2 ≤ ·), (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
            (fun y => ‖typeI₁ U V y χ‖)
      ≤ 3 * (U : ℝ) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 := by
  have hlogx0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hUnn : 0 ≤ (U : ℝ) := Nat.cast_nonneg U
  have h1x0 : (0 : ℝ) ≤ 1 + Real.log (x : ℝ) := by linarith
  -- per-`f` bound
  have perf : ∀ f ∈ (Finset.Icc 1 Q).filter (2 ≤ ·),
      (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
            (fun y => ‖typeI₁ U V y χ‖)
        ≤ 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by
    intro f hf'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hf'
    obtain ⟨⟨hf1, hfQ⟩, hf2⟩ := hf'
    haveI : NeZero f := ⟨by omega⟩
    have hfx : (f : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans hfQ hQx)
    have hlogfx : Real.log (f : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < f)) hfx
    have hsqrt0 : 0 ≤ Real.sqrt (f : ℝ) := Real.sqrt_nonneg _
    have hc : (0 : ℝ)
        ≤ 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by positivity
    have hφpos : 0 < (f.totient : ℝ) := by
      have := Nat.totient_pos.mpr (by omega : 0 < f); exact_mod_cast this
    -- per-`χ`, folded to `(1+log x)²`
    have hchar : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
        (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
            (fun y => ‖typeI₁ U V y χ‖)
          ≤ 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by
      intro χ hχmem
      have hχp : χ.IsPrimitive := (Finset.mem_filter.mp hχmem).2
      refine le_trans (typeI_one_char_le χ hχp hf2) ?_
      have h1f : 1 + Real.log (f : ℝ) ≤ 1 + Real.log (x : ℝ) := by linarith
      have hcoef : (0 : ℝ) ≤ 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) * Real.sqrt (f : ℝ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hUnn) h1x0) hsqrt0
      calc 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) *
              (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)))
          = (3 * (U : ℝ) * (1 + Real.log (x : ℝ)) * Real.sqrt (f : ℝ)) *
              (1 + Real.log (f : ℝ)) := by ring
        _ ≤ (3 * (U : ℝ) * (1 + Real.log (x : ℝ)) * Real.sqrt (f : ℝ)) * (1 + Real.log (x : ℝ)) :=
            mul_le_mul_of_nonneg_left h1f hcoef
        _ = 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by ring
    calc (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
              (fun y => ‖typeI₁ U V y χ‖)
        ≤ (1 / (f.totient : ℝ)) *
            (((Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive)).card : ℝ) *
              (3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := Finset.sum_le_card_nsmul
            (Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive))
            (fun χ => (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
              (fun y => ‖typeI₁ U V y χ‖))
            (3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ)) hchar
          rwa [nsmul_eq_mul] at this
      _ ≤ (1 / (f.totient : ℝ)) *
            ((f.totient : ℝ) * (3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_primitive_le f) hc
      _ = 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by
          rw [one_div, inv_mul_cancel_left₀ hφpos.ne']
  -- sum the per-`f` bound
  refine le_trans (Finset.sum_le_sum perf) ?_
  rw [← Finset.mul_sum]
  calc 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 *
          ∑ f ∈ (Finset.Icc 1 Q).filter (2 ≤ ·), Real.sqrt (f : ℝ)
      ≤ 3 * (U : ℝ) * (1 + Real.log (x : ℝ)) ^ 2 * ∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => Real.sqrt_nonneg _)
    _ = 3 * (U : ℝ) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 := by
        ring

open Classical in
/-- **V2a, TypeI₂ (mass `U·V`).** For `2 ≤ x` and `Q ≤ x`,
`∑_{2 ≤ f ≤ Q} (1/φf) ∑_{χ prim} max_{y ≤ x} ‖TypeI₂(y,χ)‖ ≤ 2·(U·V)·(∑_f √f)·(1+log x)²`. -/
theorem typeI_two_maxdisc_le {x U V Q : ℕ} (_hx : 2 ≤ x) (_hU : 1 ≤ U) (_hV : 1 ≤ V)
    (hQx : Q ≤ x) :
    ∑ f ∈ (Finset.Icc 1 Q).filter (2 ≤ ·), (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
            (fun y => ‖typeI₂ U V y χ‖)
      ≤ 2 * ((U : ℝ) * (V : ℝ)) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) *
          (1 + Real.log (x : ℝ)) ^ 2 := by
  have hlogx0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hUVnn : (0 : ℝ) ≤ (U : ℝ) * (V : ℝ) := by positivity
  have h1x0 : (0 : ℝ) ≤ 1 + Real.log (x : ℝ) := by linarith
  have perf : ∀ f ∈ (Finset.Icc 1 Q).filter (2 ≤ ·),
      (1 / (f.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
          (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
            (fun y => ‖typeI₂ U V y χ‖)
        ≤ 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by
    intro f hf'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hf'
    obtain ⟨⟨hf1, hfQ⟩, hf2⟩ := hf'
    haveI : NeZero f := ⟨by omega⟩
    have hfx : (f : ℝ) ≤ (x : ℝ) := by exact_mod_cast (le_trans hfQ hQx)
    have hlogfx : Real.log (f : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < f)) hfx
    have hsqrt0 : 0 ≤ Real.sqrt (f : ℝ) := Real.sqrt_nonneg _
    have hc : (0 : ℝ)
        ≤ 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by
      positivity
    have hφpos : 0 < (f.totient : ℝ) := by
      have := Nat.totient_pos.mpr (by omega : 0 < f); exact_mod_cast this
    have hchar : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
        (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
            (fun y => ‖typeI₂ U V y χ‖)
          ≤ 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by
      intro χ hχmem
      have hχp : χ.IsPrimitive := (Finset.mem_filter.mp hχmem).2
      refine le_trans (typeI_two_char_le χ hχp hf2) ?_
      have h1f : 1 + Real.log (f : ℝ) ≤ 1 + Real.log (x : ℝ) := by linarith
      have hcoef : (0 : ℝ) ≤ 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) * Real.sqrt (f : ℝ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hUVnn) h1x0) hsqrt0
      calc 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) *
              (Real.sqrt (f : ℝ) * (1 + Real.log (f : ℝ)))
          = (2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) * Real.sqrt (f : ℝ)) *
              (1 + Real.log (f : ℝ)) := by ring
        _ ≤ (2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) * Real.sqrt (f : ℝ)) *
              (1 + Real.log (x : ℝ)) := mul_le_mul_of_nonneg_left h1f hcoef
        _ = 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by ring
    calc (1 / (f.totient : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive),
            (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
              (fun y => ‖typeI₂ U V y χ‖)
        ≤ (1 / (f.totient : ℝ)) *
            (((Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive)).card : ℝ) *
              (2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := Finset.sum_le_card_nsmul
            (Finset.univ.filter (fun χ : DirichletCharacter ℂ f => χ.IsPrimitive))
            (fun χ => (Finset.Icc 0 x).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le x))
              (fun y => ‖typeI₂ U V y χ‖))
            (2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ)) hchar
          rwa [nsmul_eq_mul] at this
      _ ≤ (1 / (f.totient : ℝ)) *
            ((f.totient : ℝ) *
              (2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_primitive_le f) hc
      _ = 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 * Real.sqrt (f : ℝ) := by
          rw [one_div, inv_mul_cancel_left₀ hφpos.ne']
  refine le_trans (Finset.sum_le_sum perf) ?_
  rw [← Finset.mul_sum]
  calc 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 *
          ∑ f ∈ (Finset.Icc 1 Q).filter (2 ≤ ·), Real.sqrt (f : ℝ)
      ≤ 2 * ((U : ℝ) * (V : ℝ)) * (1 + Real.log (x : ℝ)) ^ 2 *
          ∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => Real.sqrt_nonneg _)
    _ = 2 * ((U : ℝ) * (V : ℝ)) * (∑ f ∈ Finset.Icc 1 Q, Real.sqrt (f : ℝ)) *
          (1 + Real.log (x : ℝ)) ^ 2 := by ring

end Salt.BV
