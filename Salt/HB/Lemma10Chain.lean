/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma10
import Salt.Weil.EstermannGlobal
import Salt.Weil.MajorantExpansion
import Salt.Weil.GcdDivisorSum
import Salt.LS.GaussSum

/-!
# HB 1983 §7 — (7.6)–(7.8) and Lemma 10, Wave A of N7 (the assembly gate 08/11)

The trivial bound (7.5) was landed in `Lemma10.lean`; this file lands the Abel transfer,
the completion by additive characters, Estermann's bound spent once, the dyadic sum, and
Lemma 10 at `K = 2 + k^{1/4}`.  Lemma 10 is one input of Lemma 5 (§5, Wave B, unbuilt);
nothing here bears on twin primes.

## What landed in this file, and what did NOT

**LANDED, sorry-free:** the (7.6) trio — `lem10_abel_transfer`, `var_const`, `var_inv` — the
frequency fold `lem10ExpSum_kl_mul`, the (7.7) identity `klPhaseSum_eq_kloosterman`, the (7.7)
bound `klPhaseSum_bound` (at the stated numeral `8`), the (7.8) dyadic sum `lem10_dyadic_bound`
(at the stated numeral `16`), and the R-A6 `±m` conjugation bridge `norm_lem10ExpSum_neg`.

⛔ **NOT LANDED: `hb_lemma10` and `hb_lemma10'`.**  The p.223 assembly — (7.2)'s truncation at
`K = 2 + k^{1/4}`, the dyadic cover of `0 < |m| ≤ K` by blocks `(2^j, 2^{j+1}]`, the exchange of
the finite `n`-sum with the absolutely convergent `m`-sum of (7.3), and the four `m`-ranges — is
a sub-project of its own size, not a step; it is deliberately left to the next wave rather than
half-built here.  Everything below it in the chain is proved and consumable as it stands.
-/

open Finset Salt.Weil Salt.LS

namespace Salt.N7

variable {k : ℕ}

/-! ## The definitions (R-A2 · R-A3 · R-A4) -/

/-- `n̄`: the inverse of `n` modulo `k`, as the integer in `[0, k)`. Junk off the coprime fibre. -/
def invMod (n : ℤ) (k : ℕ) : ℤ := (((n : ZMod k)⁻¹).val : ℤ)

/-- HB's phase `f(n) = (T/n − c·n̄)/k` (the `T/n` variant; `T : ℝ` free, `c : ℤ` free). -/
noncomputable def hbPhase (T : ℝ) (c : ℤ) (k : ℕ) (n : ℤ) : ℝ :=
  (T / (n : ℝ) - (c : ℝ) * (invMod n k : ℝ)) / k

/-- HB's phase `f(n) = (T − c·n̄)/k` (the constant-`T` variant). -/
noncomputable def hbPhase' (T : ℝ) (c : ℤ) (k : ℕ) (n : ℤ) : ℝ :=
  (T - (c : ℝ) * (invMod n k : ℝ)) / k

/-- The Kloosterman-phase sum `Σ′_{n ∈ (A,B]} e(c·n̄/k)` — the inner sum of (7.6). -/
noncomputable def klPhaseSum (k q : ℕ) (b A B c : ℤ) : ℂ :=
  lem10ExpSum k q b (Finset.Ioc A B) 1 (fun n => (c : ℝ) * (invMod n k : ℝ) / k)

/-! ## Service rows: the character's algebra

Two facts about `e` that the corpus carries only inside `private` lemmas or in modules this
file does not import (`Salt.Vk.Shift`'s `eR_lipschitz` lives behind `Salt.Vk.Taylor`).  They
are re-proved here rather than pulled in, so the chain's import surface stays at the five
supply modules the gate names. -/

/-- `e` is invariant under an integer shift: `e (x + j) = e x`. -/
lemma e_add_intCast (x : ℝ) (j : ℤ) : e (x + (j : ℝ)) = e x := by
  rw [e_add]
  have hj : e ((j : ℝ)) = 1 := by
    have h : e ((j : ℝ)) = Complex.exp ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      unfold e; congr 1; push_cast; ring
    rw [h]; exact Complex.exp_int_mul_two_pi_mul_I j
  rw [hj, mul_one]

/-- The derivative of the carrier: `d/dx e(x) = 2πi·e(x)`. -/
private lemma hasDerivAt_e (t : ℝ) :
    HasDerivAt e (e t * (2 * (Real.pi : ℂ) * Complex.I)) t := by
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hf : HasDerivAt (fun s : ℝ => 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ))
      (2 * (Real.pi : ℂ) * Complex.I) t := by
    simpa using h0.const_mul (2 * (Real.pi : ℂ) * Complex.I)
  exact hf.cexp

/-- **The carrier is `2π`-Lipschitz**: `‖e x − e y‖ ≤ 2π|x − y|`.  The `2π` lives inside `e`,
so the constant is `2π` and not `1`. -/
lemma norm_e_sub_le (x y : ℝ) : ‖e x - e y‖ ≤ 2 * Real.pi * |x - y| := by
  have hcont : Continuous e := by
    unfold e; fun_prop
  have hint : IntervalIntegrable (fun t => e t * (2 * (Real.pi : ℂ) * Complex.I))
      MeasureTheory.volume y x :=
    (hcont.mul continuous_const).intervalIntegrable y x
  have hFTC : ∫ t in y..x, e t * (2 * (Real.pi : ℂ) * Complex.I) = e x - e y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_e t) hint
  rw [← hFTC]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * Real.pi) ?_).trans_eq rfl
  intro t _
  rw [norm_mul, norm_e, one_mul]
  have hrw : (2 : ℂ) * (Real.pi : ℂ) * Complex.I = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hrw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-! ## Service rows: `Ioc` over `ℤ`

mathlib's `Finset.prod_Ioc_succ_top` is stated for `ℕ` only; the Abel transfer below runs on
`ℤ`-indexed intervals (R-A2), so the peel-the-top row is re-proved here. -/

/-- Peeling the top of an integer `Ioc`. -/
lemma sum_Ioc_succ_top_int {M : Type*} [AddCommMonoid M] {A B : ℤ} (hAB : A ≤ B) (f : ℤ → M) :
    ∑ n ∈ Finset.Ioc A (B + 1), f n = (∑ n ∈ Finset.Ioc A B, f n) + f (B + 1) := by
  have h1 : Finset.Ioc A (B + 1) = insert (B + 1) (Finset.Ioc A B) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have h2 : (B + 1) ∉ Finset.Ioc A B := by simp
  rw [h1, Finset.sum_insert h2, add_comm]

/-- Peeling the top of an integer `Ico`. -/
lemma sum_Ico_succ_top_int {M : Type*} [AddCommMonoid M] {A B : ℤ} (hAB : A ≤ B) (f : ℤ → M) :
    ∑ n ∈ Finset.Ico A (B + 1), f n = (∑ n ∈ Finset.Ico A B, f n) + f B := by
  have h1 : Finset.Ico A (B + 1) = insert B (Finset.Ico A B) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have h2 : B ∉ Finset.Ico A B := by simp
  rw [h1, Finset.sum_insert h2, add_comm]

/-- **Abel summation on an integer `Ioc`, `Ico` form.**  With `S n = ∑_{A < j ≤ n} a j`,
`∑_{A < n ≤ B} w n · a n = w B · S B − ∑_{A ≤ n < B} (w (n+1) − w n) · S n`. -/
lemma sum_Ioc_abel_int_ico (A : ℤ) (w a : ℤ → ℂ) {B : ℤ} (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ioc A B, w n * a n
      = w B * (∑ n ∈ Finset.Ioc A B, a n)
        - ∑ n ∈ Finset.Ico A B, (w (n + 1) - w n) * (∑ j ∈ Finset.Ioc A n, a j) := by
  induction B, hAB using Int.leInduction with
  | base =>
      have h1 : Finset.Ioc A A = (∅ : Finset ℤ) := by simp
      have h2 : Finset.Ico A A = (∅ : Finset ℤ) := by simp
      rw [h1, h2]; simp
  | succ B hB ih =>
      rw [sum_Ioc_succ_top_int hB (fun n => w n * a n),
        sum_Ioc_succ_top_int hB a, ih,
        sum_Ico_succ_top_int hB (fun n => (w (n + 1) - w n) * (∑ j ∈ Finset.Ioc A n, a j))]
      ring

/-- The `Ico`-indexed correction sum equals the `Ioc`-indexed one whenever the `n = A` term
vanishes — which it does here, the partial sum `S A` being empty. -/
lemma sum_Ico_eq_sum_Ioc_pred {M : Type*} [AddCommMonoid M] (A B : ℤ) (F : ℤ → M)
    (hFA : F A = 0) : ∑ n ∈ Finset.Ico A B, F n = ∑ n ∈ Finset.Ioc A (B - 1), F n := by
  rcases lt_or_ge A B with hlt | hge
  · have h1 : Finset.Ico A B = insert A (Finset.Ioc A (B - 1)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc, Finset.mem_insert]
      omega
    have h2 : A ∉ Finset.Ioc A (B - 1) := by simp
    rw [h1, Finset.sum_insert h2, hFA, zero_add]
  · have h1 : Finset.Ico A B = (∅ : Finset ℤ) := Finset.Ico_eq_empty (by omega)
    have h2 : Finset.Ioc A (B - 1) = (∅ : Finset ℤ) := Finset.Ioc_eq_empty (by omega)
    rw [h1, h2]

/-- **Abel summation on an integer `Ioc`.**  With `S n = ∑_{A < j ≤ n} a j`,
`∑_{A < n ≤ B} w n · a n = w B · S B − ∑_{A < n ≤ B−1} (w (n+1) − w n) · S n`.  The `n = A`
term of the `Ico` form is dropped because `S A` is an empty sum. -/
lemma sum_Ioc_abel_int (A : ℤ) (w a : ℤ → ℂ) {B : ℤ} (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ioc A B, w n * a n
      = w B * (∑ n ∈ Finset.Ioc A B, a n)
        - ∑ n ∈ Finset.Ioc A (B - 1), (w (n + 1) - w n) * (∑ j ∈ Finset.Ioc A n, a j) := by
  rw [sum_Ioc_abel_int_ico A w a hAB,
    sum_Ico_eq_sum_Ioc_pred A B (fun n => (w (n + 1) - w n) * (∑ j ∈ Finset.Ioc A n, a j))
      (by simp)]

/-! ## The primed sum as an `ite`-weighted sum

`lem10ExpSum` carries HB's prime as a filter INSIDE the definition (R-A2).  For the Abel
transfer the filter has to become a coefficient, so the two forms are bridged once here. -/

/-- HB's prime, as a coefficient: `a n = [(n,k)=1 ∧ q ∣ n−b] · e(m·f n)`. -/
noncomputable def lem10Coeff (k q : ℕ) (b : ℤ) (m : ℕ) (f : ℤ → ℝ) (n : ℤ) : ℂ :=
  if Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b then e ((m : ℝ) * f n) else 0

/-- `lem10ExpSum` is the `lem10Coeff`-sum over the *unfiltered* index set. -/
lemma lem10ExpSum_eq_sum_coeff (k q : ℕ) (b : ℤ) (I : Finset ℤ) (m : ℕ) (f : ℤ → ℝ) :
    lem10ExpSum k q b I m f = ∑ n ∈ I, lem10Coeff k q b m f n := by
  unfold lem10ExpSum lem10Coeff
  rw [Finset.sum_filter]

/-! ## (7.6) — the Abel transfer -/

/-- ⭐ **HB (7.6) — THE ABEL TRANSFER** (p.221, `hb1983-notes.md:820`).  Splitting the phase
as `f = g + h`, the `g`-part is removed by partial summation at the cost of the factor
`1 + 2πm·V`, where `V` bounds the total variation of `g` across the window.

Per gate ruling **R-A3 the phase variation is a HYPOTHESIS**, not a computation: HB's two
`f`-shapes (`(T − Cn̄)/k` and `(T/n − Cn̄)/k`) discharge `hvar` in `var_const` and `var_inv`
below, and no calculus of `T/n` enters the main chain.

`hAB : A ≤ B` is load-bearing in a way that is easy to miss: it is what lets `hW` at `n := A`
(where the sum is empty) certify `0 ≤ W`, and every product bound below needs that sign. -/
theorem lem10_abel_transfer (k q : ℕ) (b A B : ℤ) (hAB : A ≤ B) (m : ℕ) (g h : ℤ → ℝ)
    {W V : ℝ}
    (hW : ∀ n : ℤ, n ≤ B → ‖lem10ExpSum k q b (Finset.Ioc A n) m h‖ ≤ W)
    (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V) :
    ‖lem10ExpSum k q b (Finset.Ioc A B) m (fun n => g n + h n)‖
      ≤ (1 + 2 * Real.pi * m * V) * W := by
  set w : ℤ → ℂ := fun n => e ((m : ℝ) * g n) with hw
  set a : ℤ → ℂ := fun n => lem10Coeff k q b m h n with ha
  -- `0 ≤ W`, from the empty initial segment
  have hW0 : (0 : ℝ) ≤ W := by
    have := hW A hAB
    have hemp : Finset.Ioc A A = (∅ : Finset ℤ) := by simp
    rw [hemp] at this
    simpa [lem10ExpSum] using this
  -- the partial sums
  have hS : ∀ n : ℤ, ∑ j ∈ Finset.Ioc A n, a j = lem10ExpSum k q b (Finset.Ioc A n) m h := by
    intro n; rw [lem10ExpSum_eq_sum_coeff]
  -- the target sum in Abel form
  have hmain : lem10ExpSum k q b (Finset.Ioc A B) m (fun n => g n + h n)
      = ∑ n ∈ Finset.Ioc A B, w n * a n := by
    rw [lem10ExpSum_eq_sum_coeff]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hw, ha, lem10Coeff]
    by_cases hp : Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b
    · rw [if_pos hp, if_pos hp,
        show (m : ℝ) * (g n + h n) = (m : ℝ) * g n + (m : ℝ) * h n by ring, e_add]
    · rw [if_neg hp, if_neg hp, mul_zero]
  rw [hmain, sum_Ioc_abel_int A w a hAB]
  have hbound : ‖w B * (∑ n ∈ Finset.Ioc A B, a n)
      - ∑ n ∈ Finset.Ioc A (B - 1), (w (n + 1) - w n) * (∑ j ∈ Finset.Ioc A n, a j)‖
      ≤ ‖w B‖ * ‖∑ n ∈ Finset.Ioc A B, a n‖
        + ∑ n ∈ Finset.Ioc A (B - 1),
            ‖w (n + 1) - w n‖ * ‖∑ j ∈ Finset.Ioc A n, a j‖ := by
    refine le_trans (norm_sub_le _ _) (add_le_add (le_of_eq (norm_mul _ _)) ?_)
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun n _ => norm_mul _ _)
  refine le_trans hbound ?_
  have h1 : ‖w B‖ * ‖∑ n ∈ Finset.Ioc A B, a n‖ ≤ W := by
    simp only [hw, norm_e, one_mul]
    rw [hS B]
    exact hW B le_rfl
  have h2 : ∑ n ∈ Finset.Ioc A (B - 1), ‖w (n + 1) - w n‖ * ‖∑ j ∈ Finset.Ioc A n, a j‖
      ≤ 2 * Real.pi * m * V * W := by
    have hterm : ∀ n ∈ Finset.Ioc A (B - 1),
        ‖w (n + 1) - w n‖ * ‖∑ j ∈ Finset.Ioc A n, a j‖
          ≤ (2 * Real.pi * m * |g (n + 1) - g n|) * W := by
      intro n hn
      simp only [Finset.mem_Ioc] at hn
      have hdrift : ‖w (n + 1) - w n‖ ≤ 2 * Real.pi * m * |g (n + 1) - g n| := by
        simp only [hw]
        refine le_trans (norm_e_sub_le _ _) ?_
        have : |(m : ℝ) * g (n + 1) - (m : ℝ) * g n| = (m : ℝ) * |g (n + 1) - g n| := by
          rw [show (m : ℝ) * g (n + 1) - (m : ℝ) * g n = (m : ℝ) * (g (n + 1) - g n) by ring,
            abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))]
        rw [this]; ring_nf; exact le_rfl
      have hpart : ‖∑ j ∈ Finset.Ioc A n, a j‖ ≤ W := by
        rw [hS n]; exact hW n (by omega)
      exact mul_le_mul hdrift hpart (norm_nonneg _)
        (by positivity)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hV : 2 * Real.pi * (m : ℝ) * (∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n|)
        ≤ 2 * Real.pi * (m : ℝ) * V :=
      mul_le_mul_of_nonneg_left hvar (by positivity)
    calc (2 * Real.pi * (m : ℝ) * ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n|) * W
        ≤ (2 * Real.pi * (m : ℝ) * V) * W := mul_le_mul_of_nonneg_right hV hW0
      _ = 2 * Real.pi * m * V * W := by ring
  nlinarith [h1, h2]

/-! ## (7.6)'s two phase-variation discharges (R-A3)

The hypothesis `hvar` of `lem10_abel_transfer` is discharged once per HB `f`-shape.  Neither
lemma is about the character: both are statements about a real sequence's total variation. -/

set_option linter.unusedVariables false in
/-- **The constant-`T` variant's variation** (HB's `f(n) = (T − Cn̄)/k`): the `T`-part is
constant in `n`, so its total variation is exactly `0`. -/
theorem var_const (A B : ℤ) (T : ℝ) (k : ℕ) :
    ∑ n ∈ Finset.Ioc A (B - 1), |T / k - T / k| = 0 := by
  simp

/-- Telescoping on an integer `Ioc`: `∑_{A < n ≤ M} (F n − F (n+1)) = F (A+1) − F (M+1)`. -/
private lemma sum_Ioc_telescope (F : ℤ → ℝ) (A : ℤ) {M : ℤ} (hAM : A ≤ M) :
    ∑ n ∈ Finset.Ioc A M, (F n - F (n + 1)) = F (A + 1) - F (M + 1) := by
  induction M, hAM using Int.leInduction with
  | base => rw [show Finset.Ioc A A = (∅ : Finset ℤ) by simp]; simp
  | succ M hM ih =>
      rw [sum_Ioc_succ_top_int hM (fun n => F n - F (n + 1)), ih]
      ring

/-- **The `T/n` variant's variation** (HB's `f(n) = (T/n − Cn̄)/k`): across a window whose left
endpoint is at least `E ≥ 1`, the total variation of `n ↦ T/(kn)` is at most `|T|/(kE)`.

The sum telescopes; `1 ≤ E` and `E ≤ A` are what keep every `n` in the window positive, so the
increments have a constant sign and the absolute values collapse.  `k = 0` is admitted and is
not vacuous — both sides are then `0`, Lean's `x/0 = 0`. -/
theorem var_inv (T : ℝ) (k : ℕ) {E : ℝ} (hE : 1 ≤ E) {A B : ℤ} (hA : E ≤ A) :
    ∑ n ∈ Finset.Ioc A (B - 1),
        |T / ((k : ℝ) * ((n + 1 : ℤ) : ℝ)) - T / ((k : ℝ) * (n : ℝ))|
      ≤ |T| / ((k : ℝ) * E) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; simp
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hAR : (1 : ℝ) ≤ (A : ℝ) := le_trans hE hA
  rcases lt_or_ge (B - 1) A with hlt | hge
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  have hterm : ∀ n ∈ Finset.Ioc A (B - 1),
      |T / ((k : ℝ) * ((n + 1 : ℤ) : ℝ)) - T / ((k : ℝ) * (n : ℝ))|
        = (|T| / (k : ℝ)) * ((fun j : ℤ => (1 : ℝ) / (j : ℝ)) n
            - (fun j : ℤ => (1 : ℝ) / (j : ℝ)) (n + 1)) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hAn : (A : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hnp : (0 : ℝ) < (n : ℝ) := by linarith
    have hcast : (((n + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hn1p : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    simp only [hcast]
    have hval : T / ((k : ℝ) * ((n : ℝ) + 1)) - T / ((k : ℝ) * (n : ℝ))
        = -((T / (k : ℝ)) * ((1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
      field_simp
      ring
    have hpos : (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le hnp (by linarith))
    rw [hval, abs_neg, abs_mul, abs_of_nonneg hpos, abs_div, abs_of_pos hkR]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_Ioc_telescope (fun j : ℤ => (1 : ℝ) / (j : ℝ)) A hge]
  have hBpos : (0 : ℝ) < ((B - 1 + 1 : ℤ) : ℝ) := by
    have : (A : ℝ) ≤ ((B - 1 : ℤ) : ℝ) := by exact_mod_cast hge
    push_cast at this ⊢
    linarith
  have h1 : (0 : ℝ) ≤ (1 : ℝ) / ((B - 1 + 1 : ℤ) : ℝ) := le_of_lt (by positivity)
  have h2 : (1 : ℝ) / ((A + 1 : ℤ) : ℝ) ≤ 1 / E := by
    refine one_div_le_one_div_of_le hE0 ?_
    have : (E : ℝ) ≤ (A : ℝ) := hA
    push_cast
    linarith
  have hTk : (0 : ℝ) ≤ |T| / (k : ℝ) := by positivity
  calc (|T| / (k : ℝ))
        * ((1 : ℝ) / ((A + 1 : ℤ) : ℝ) - (1 : ℝ) / ((B - 1 + 1 : ℤ) : ℝ))
      ≤ (|T| / (k : ℝ)) * (1 / E) := by
        refine mul_le_mul_of_nonneg_left ?_ hTk
        linarith
    _ = |T| / ((k : ℝ) * E) := by field_simp

/-- **Folding the dyadic `m` into the Kloosterman phase.**  `e(m·c·n̄/k)` at frequency `1` is
`e(c·n̄/k)` at frequency `m`; this is the rewrite that lets `(7.8)` quote the `(7.7)` bound once
per `m` with `c ↦ m·c`. -/
theorem lem10ExpSum_kl_mul (k q : ℕ) (b : ℤ) (I : Finset ℤ) (m : ℕ) (c : ℤ) :
    lem10ExpSum k q b I m (fun n => (c : ℝ) * (invMod n k : ℝ) / k)
      = lem10ExpSum k q b I 1 (fun n => ((m * c : ℤ) : ℝ) * (invMod n k : ℝ) / k) := by
  unfold lem10ExpSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  congr 1
  push_cast
  ring

/-! ## (7.7) — completion by additive characters mod `k`

HB p.222.  The inner sum of (7.6) carries a coprimality prime; the completion drops it,
because the character detection `∑_t [t = n]` is *already* zero at a non-unit `n`.  That is why
the supply row `congrExpSum` carries no coprimality condition: none is needed on the right. -/

/-- The bridge from mathlib's standard additive character to the track carrier, at an integer
argument: `ψ(x mod k) = e(x/k)`.  No periodicity argument is needed — `ZMod.stdAddChar_coe`
already states the character at an integer representative. -/
lemma stdAddChar_intCast_eq_e (k : ℕ) [NeZero k] (x : ℤ) :
    (ZMod.stdAddChar ((x : ZMod k)) : ℂ) = e ((x : ℝ) / (k : ℝ)) := by
  rw [ZMod.stdAddChar_coe]
  unfold Salt.LS.e
  congr 1
  push_cast
  ring

/-- **`n` is invertible mod `k` exactly when `(n,k) = 1`** — the integer-indexed form.  mathlib
carries `ZMod.isUnit_iff_coprime` for a NATURAL numerator only; the chain's index type is `ℤ`
(R-A2), and casting through `natAbs` would put a sign case where none belongs. -/
lemma isUnit_intCast_iff (k : ℕ) [NeZero k] (n : ℤ) :
    IsUnit ((n : ZMod k)) ↔ Int.gcd n (k : ℤ) = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    have hinv : ((u⁻¹ : (ZMod k)ˣ) : ZMod k) * ((n : ZMod k)) = 1 := by
      rw [← hu]; simp
    have hdvd : (k : ℤ) ∣ ((((u⁻¹ : (ZMod k)ˣ) : ZMod k).val : ℤ)) * n - 1 := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, hinv, sub_self]
    obtain ⟨m, hm⟩ := hdvd
    have h1 : (Int.gcd n (k : ℤ) : ℤ) ∣ n := Int.gcd_dvd_left n (k : ℤ)
    have h2 : (Int.gcd n (k : ℤ) : ℤ) ∣ (k : ℤ) := Int.gcd_dvd_right n (k : ℤ)
    have hone : (Int.gcd n (k : ℤ) : ℤ) ∣ 1 := by
      have hrw : (1 : ℤ)
          = ((((u⁻¹ : (ZMod k)ˣ) : ZMod k).val : ℤ)) * n - (k : ℤ) * m := by linarith [hm]
      rw [hrw]
      exact dvd_sub (h1.mul_left _) (h2.mul_right _)
    have : Int.gcd n (k : ℤ) ∣ 1 := by exact_mod_cast hone
    exact Nat.dvd_one.mp this
  · intro hg
    obtain ⟨u, v, huv⟩ : IsCoprime n (k : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hg
    have h : ((n : ZMod k)) * ((u : ℤ) : ZMod k) = 1 := by
      have hc := congrArg (fun z : ℤ => (z : ZMod k)) huv
      push_cast at hc
      rw [ZMod.natCast_self] at hc
      linear_combination hc
    exact isUnit_iff_exists.mpr ⟨((u : ℤ) : ZMod k), h, by rw [mul_comm]; exact h⟩

/-- ⭐ **HB (7.7), the identity half — COMPLETION BY ADDITIVE CHARACTERS** (p.222,
`hb1983-notes.md:824`).  Detecting `n ≡ t (mod k)` by the additive characters mod `k` turns the
primed phase sum into `k^{-1}` times a Kloosterman sum against the congruence-restricted
completion `congrExpSum`.

⚠️ **The coprimality prime on the left is not dropped, it is DISCHARGED.** On the right no
coprimality appears anywhere — and that is correct, not a slip: the inner detection
`∑_{t ∈ (ZMod k)ˣ} [t = n]` is identically zero at a non-unit `n`, so the right-hand side kills
the non-coprime `n` on its own.  This is exactly why the supply row `congrExpSum` was landed
without a coprimality filter. -/
theorem klPhaseSum_eq_kloosterman [NeZero k] (q : ℕ) (b A B c : ℤ) :
    klPhaseSum k q b A B c
      = (1 / (k : ℂ)) * ∑ s : ZMod k,
          kloosterman s (c : ZMod k) * congrExpSum k (s.val : ℤ) b q A B := by
  classical
  have hk0 : (k : ℂ) ≠ 0 := by
    have hkn : k ≠ 0 := NeZero.ne k
    exact_mod_cast hkn
  -- (i) the congruence-restricted completion, in character form
  have hcongr : ∀ s : ZMod k, congrExpSum k (s.val : ℤ) b q A B
      = ∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b),
          (ZMod.stdAddChar (-(s * ((n : ℤ) : ZMod k))) : ℂ) := by
    intro s
    unfold congrExpSum
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hz : (-(s * ((n : ℤ) : ZMod k))) = (((-((s.val : ℤ) * n)) : ℤ) : ZMod k) := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [hz, stdAddChar_intCast_eq_e]
    congr 1
    push_cast
    ring
  -- (ii) the completed double sum, `k` times the primed sum
  have hRHS : ∑ s : ZMod k, kloosterman s (c : ZMod k) * congrExpSum k (s.val : ℤ) b q A B
      = (k : ℂ) * klPhaseSum k q b A B c := by
    calc ∑ s : ZMod k, kloosterman s (c : ZMod k) * congrExpSum k (s.val : ℤ) b q A B
        = ∑ s : ZMod k, ∑ t : (ZMod k)ˣ,
            ∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b),
              (ZMod.stdAddChar (s * (t : ZMod k)
                  + (c : ZMod k) * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ)
                * (ZMod.stdAddChar (-(s * ((n : ℤ) : ZMod k))) : ℂ) := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [hcongr s, kloosterman, Finset.sum_mul_sum]
      _ = ∑ s : ZMod k, ∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b),
            ∑ t : (ZMod k)ˣ,
              (ZMod.stdAddChar (s * (t : ZMod k)
                  + (c : ZMod k) * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ)
                * (ZMod.stdAddChar (-(s * ((n : ℤ) : ZMod k))) : ℂ) :=
          Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
      _ = ∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b), ∑ s : ZMod k,
            ∑ t : (ZMod k)ˣ,
              (ZMod.stdAddChar (s * (t : ZMod k)
                  + (c : ZMod k) * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ)
                * (ZMod.stdAddChar (-(s * ((n : ℤ) : ZMod k))) : ℂ) := Finset.sum_comm
      _ = ∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b), ∑ t : (ZMod k)ˣ,
            ∑ s : ZMod k,
              (ZMod.stdAddChar (s * (t : ZMod k)
                  + (c : ZMod k) * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ)
                * (ZMod.stdAddChar (-(s * ((n : ℤ) : ZMod k))) : ℂ) :=
          Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
      _ = ∑ n ∈ (Finset.Ioc A B).filter (fun n => (q : ℤ) ∣ n - b), ∑ t : (ZMod k)ˣ,
            (ZMod.stdAddChar ((c : ZMod k) * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ)
              * (if (t : ZMod k) = ((n : ℤ) : ZMod k) then (k : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun t _ => ?_))
          have hprod : ∀ s : ZMod k,
              (ZMod.stdAddChar (s * (t : ZMod k)
                  + (c : ZMod k) * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ)
                * (ZMod.stdAddChar (-(s * ((n : ℤ) : ZMod k))) : ℂ)
              = (ZMod.stdAddChar ((c : ZMod k) * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ)
                * (ZMod.stdAddChar (s * ((t : ZMod k) - ((n : ℤ) : ZMod k))) : ℂ) := by
            intro s
            rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
            congr 1
            ring
          rw [Finset.sum_congr rfl (fun s _ => hprod s), ← Finset.mul_sum,
            AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar k), ZMod.card]
          congr 1
          by_cases hts : (t : ZMod k) - ((n : ℤ) : ZMod k) = 0
          · rw [if_pos hts, if_pos (sub_eq_zero.mp hts)]
          · rw [if_neg hts, if_neg (fun hc => hts (sub_eq_zero.mpr hc))]
            exact Nat.cast_zero
      _ = (k : ℂ) * klPhaseSum k q b A B c := by
          rw [klPhaseSum, lem10ExpSum, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          by_cases h2 : (q : ℤ) ∣ n - b
          · by_cases h1 : Int.gcd n k = 1
            · rw [if_pos h2, if_pos ⟨h1, h2⟩]
              obtain ⟨u, hu⟩ : IsUnit ((n : ZMod k)) :=
                (isUnit_intCast_iff k n).mpr h1
              have hiff : ∀ t : (ZMod k)ˣ,
                  ((t : ZMod k) = ((n : ℤ) : ZMod k)) ↔ t = u := by
                intro t
                rw [← hu]
                exact ⟨fun h => Units.ext h, fun h => by rw [h]⟩
              simp only [hiff]
              rw [Finset.sum_congr rfl (fun t (_ : t ∈ (Finset.univ : Finset (ZMod k)ˣ)) =>
                show (ZMod.stdAddChar ((c : ZMod k) * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ)
                    * (if t = u then (k : ℂ) else 0)
                  = (if t = u then
                      (k : ℂ) * (ZMod.stdAddChar ((c : ZMod k)
                        * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ) else 0) by
                  by_cases h : t = u
                  · rw [if_pos h, if_pos h]; ring
                  · rw [if_neg h, if_neg h]; ring)]
              rw [Finset.sum_ite_eq' Finset.univ u
                (fun t => (k : ℂ) * (ZMod.stdAddChar ((c : ZMod k)
                  * ((t⁻¹ : (ZMod k)ˣ) : ZMod k)) : ℂ))]
              rw [if_pos (Finset.mem_univ u)]
              congr 1
              have hinvcast : ((c : ZMod k) * ((u⁻¹ : (ZMod k)ˣ) : ZMod k))
                  = (((c * invMod n k : ℤ)) : ZMod k) := by
                rw [invMod]
                push_cast
                rw [ZMod.natCast_val, ZMod.cast_id, ← ZMod.inv_coe_unit, hu]
              rw [hinvcast, stdAddChar_intCast_eq_e]
              congr 1
              push_cast
              ring
            · rw [if_pos h2, if_neg (fun hc => h1 hc.1)]
              refine Finset.sum_eq_zero (fun t _ => ?_)
              have hne : (t : ZMod k) ≠ ((n : ℤ) : ZMod k) := by
                intro hc
                exact h1 ((isUnit_intCast_iff k n).mp (hc ▸ t.isUnit))
              rw [if_neg hne, mul_zero]
          · rw [if_neg h2, if_neg (fun hc => h2 hc.2)]
  rw [hRHS, ← mul_assoc, one_div, inv_mul_cancel₀ hk0, one_mul]


/-! ## Service rows for (7.7)'s BOUND

The bound splits the `s`-sum of the completion along `s mod k₀` (`k = q·k₀`); these are the
five elementary rows that split it. -/

/-- Reindexing `ZMod k` by `val` onto `range k`. -/
lemma sum_zmod_val_eq_sum_range (k : ℕ) [NeZero k] (F : ℕ → ℝ) :
    ∑ s : ZMod k, F s.val = ∑ v ∈ Finset.range k, F v := by
  classical
  have himg : (Finset.univ : Finset (ZMod k)).image ZMod.val = Finset.range k := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨s, rfl⟩; exact ZMod.val_lt s
    · intro hv; exact ⟨(v : ZMod k), ZMod.val_cast_of_lt hv⟩
  have hinj : Set.InjOn ZMod.val ((Finset.univ : Finset (ZMod k)) : Set (ZMod k)) := by
    intro x _ y _ hxy
    have hc : ((x.val : ℕ) : ZMod k) = ((y.val : ℕ) : ZMod k) := by
      simp only [hxy]
    rwa [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id] at hc
  rw [← himg, Finset.sum_image hinj]

/-- Every residue mod `k₀` is hit exactly `q` times in `range (k₀·q)`. -/
lemma sum_range_mul_mod (k₀ q : ℕ) (g : ℕ → ℝ) :
    ∑ v ∈ Finset.range (k₀ * q), g (v % k₀) = q * ∑ r ∈ Finset.range k₀, g r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have hcongr : ∀ x ∈ Finset.range k₀, g ((k₀ * q + x) % k₀) = g x := by
        intro x hx
        simp only [Finset.mem_range] at hx
        congr 1
        rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      rw [Finset.sum_congr rfl hcongr]
      push_cast
      ring

/-- The reflection `r ↦ n − r` of `Ico 1 n`. -/
lemma sum_Ico_reflect (n : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Ico 1 n, f (n - r) = ∑ r ∈ Finset.Ico 1 n, f r := by
  refine Finset.sum_bij' (fun r _ => n - r) (fun r _ => n - r)
    (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) (fun a _ => rfl)
  · simp only [Finset.mem_Ico] at *; omega
  · simp only [Finset.mem_Ico] at *; omega
  · simp only [Finset.mem_Ico] at *; omega
  · simp only [Finset.mem_Ico] at *; omega

/-- `gcd` only sees the residue: congruent integers have the same `gcd` with the modulus. -/
lemma gcd_natAbs_eq_of_dvd_sub {d : ℕ} {a b : ℤ} (h : (d : ℤ) ∣ a - b) :
    Nat.gcd d a.natAbs = Nat.gcd d b.natAbs := by
  have key : ∀ x y : ℤ, (d : ℤ) ∣ x - y → Nat.gcd d x.natAbs ∣ Nat.gcd d y.natAbs := by
    intro x y hxy
    refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
    have hgx : ((Nat.gcd d x.natAbs : ℕ) : ℤ) ∣ x := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast Nat.gcd_dvd_right d x.natAbs
    have hgd : ((Nat.gcd d x.natAbs : ℕ) : ℤ) ∣ (d : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left d x.natAbs
    have hgy : ((Nat.gcd d x.natAbs : ℕ) : ℤ) ∣ y := by
      have : ((Nat.gcd d x.natAbs : ℕ) : ℤ) ∣ x - y := hgd.trans hxy
      simpa using dvd_sub hgx this
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    exact hgy
  exact Nat.dvd_antisymm (key a b h) (key b a (by simpa using (dvd_neg.mpr h)))

/-- `gcd(q·k₀, X) ≤ q·gcd(k₀, X)`, in the square-rooted shape (7.7) consumes. -/
lemma sqrt_gcd_mul_le {q k₀ : ℕ} (hq : 0 < q) (hk₀ : 0 < k₀) (X : ℕ) :
    Real.sqrt ((Nat.gcd (q * k₀) X : ℕ) : ℝ)
      ≤ Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ X : ℕ) : ℝ) := by
  have hdvd : Nat.gcd (q * k₀) X ∣ Nat.gcd q X * Nat.gcd k₀ X := by
    have h := gcd_mul_dvd_mul_gcd X q k₀
    rw [gcd_eq_nat_gcd, gcd_eq_nat_gcd, gcd_eq_nat_gcd] at h
    rw [Nat.gcd_comm (q * k₀) X, Nat.gcd_comm q X, Nat.gcd_comm k₀ X]
    exact h
  have hg1 : 0 < Nat.gcd q X :=
    Nat.pos_of_ne_zero (fun hz => by
      have := (Nat.gcd_eq_zero_iff.mp hz).1; omega)
  have hg2 : 0 < Nat.gcd k₀ X :=
    Nat.pos_of_ne_zero (fun hz => by
      have := (Nat.gcd_eq_zero_iff.mp hz).1; omega)
  have hle : Nat.gcd (q * k₀) X ≤ q * Nat.gcd k₀ X := by
    refine le_trans (Nat.le_of_dvd (Nat.mul_pos hg1 hg2) hdvd) ?_
    exact Nat.mul_le_mul_right _ (Nat.gcd_le_left _ hq)
  have hleR : ((Nat.gcd (q * k₀) X : ℕ) : ℝ) ≤ (q : ℝ) * ((Nat.gcd k₀ X : ℕ) : ℝ) := by
    exact_mod_cast hle
  calc Real.sqrt ((Nat.gcd (q * k₀) X : ℕ) : ℝ)
      ≤ Real.sqrt ((q : ℝ) * ((Nat.gcd k₀ X : ℕ) : ℝ)) := Real.sqrt_le_sqrt hleR
    _ = Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ X : ℕ) : ℝ) :=
        Real.sqrt_mul (by positivity) _

/-- The circle distance of `m + r/k₀` is at least `min(r, k₀−r)/k₀`. -/
lemma dist₁_shift_lower {k₀ : ℕ} (hk₀ : 0 < k₀) (m : ℤ) {r : ℕ} (hr0 : 0 < r) (hrk : r < k₀) :
    ((min r (k₀ - r) : ℕ) : ℝ) / (k₀ : ℝ) ≤ dist₁ ((m : ℝ) + (r : ℝ) / (k₀ : ℝ)) 0 := by
  have hk0R : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk₀
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hrkR : ((r : ℝ)) < (k₀ : ℝ) := by exact_mod_cast hrk
  have hsub : (((k₀ - r : ℕ)) : ℝ) = (k₀ : ℝ) - (r : ℝ) := by
    have := Nat.cast_sub (R := ℝ) (le_of_lt hrk)
    simpa using this
  have hmin : ((min r (k₀ - r) : ℕ) : ℝ) = min ((r : ℝ)) ((k₀ : ℝ) - (r : ℝ)) := by
    rw [Nat.cast_min, hsub]
  rw [hmin]
  have hd : dist₁ ((m : ℝ) + (r : ℝ) / (k₀ : ℝ)) 0
      = |((m : ℝ) + (r : ℝ) / (k₀ : ℝ)) - ((round ((m : ℝ) + (r : ℝ) / (k₀ : ℝ)) : ℤ) : ℝ)| := by
    unfold dist₁; rw [sub_zero]
  rw [hd]
  set x : ℝ := (m : ℝ) + (r : ℝ) / (k₀ : ℝ) with hx
  set j : ℤ := round x with hj
  rcases le_or_gt j m with hjm | hjm
  · have hjR : ((j : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
    have h1 : (r : ℝ) / (k₀ : ℝ) ≤ x - (j : ℝ) := by rw [hx]; linarith
    have h2 : min ((r : ℝ)) ((k₀ : ℝ) - (r : ℝ)) / (k₀ : ℝ) ≤ (r : ℝ) / (k₀ : ℝ) := by
      gcongr
      exact min_le_left _ _
    exact le_trans h2 (le_trans h1 (le_abs_self _))
  · have hjR : (m : ℝ) + 1 ≤ ((j : ℤ) : ℝ) := by exact_mod_cast hjm
    have hdiv : (r : ℝ) / (k₀ : ℝ) < 1 := by
      rw [div_lt_one hk0R]; exact hrkR
    have h1 : ((k₀ : ℝ) - (r : ℝ)) / (k₀ : ℝ) ≤ (j : ℝ) - x := by
      rw [hx]
      have : ((k₀ : ℝ) - (r : ℝ)) / (k₀ : ℝ) = 1 - (r : ℝ) / (k₀ : ℝ) := by
        field_simp
      rw [this]
      linarith
    have h2 : min ((r : ℝ)) ((k₀ : ℝ) - (r : ℝ)) / (k₀ : ℝ)
        ≤ ((k₀ : ℝ) - (r : ℝ)) / (k₀ : ℝ) := by
      gcongr
      exact min_le_right _ _
    have h3 : (j : ℝ) - x ≤ |x - (j : ℝ)| := by
      rw [abs_sub_comm]; exact le_abs_self _
    exact le_trans h2 (le_trans h1 h3)

/-- ⭐ **The (7.7) gcd average, in the `min(r, k₀−r)` shape the completion produces.**  Folding
by the reflection `r ↦ k₀ − r` costs a factor `2` and returns the landed supply row
`sum_sqrt_gcd_div_le_log_two_mul`. -/
lemma sum_sqrt_gcd_min_le {k₀ : ℕ} (hk₀ : 0 < k₀) :
    ∑ r ∈ Finset.Ico 1 k₀,
        Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / ((min r (k₀ - r) : ℕ) : ℝ)
      ≤ 2 * ((Real.log 2)⁻¹ * (k₀.divisors.card : ℝ) * Real.log (2 * (k₀ : ℝ))) := by
  have hstep : ∀ r ∈ Finset.Ico 1 k₀,
      Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / ((min r (k₀ - r) : ℕ) : ℝ)
        ≤ Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / (r : ℝ)
          + Real.sqrt ((Nat.gcd k₀ (k₀ - r) : ℕ) : ℝ) / (((k₀ - r : ℕ)) : ℝ) := by
    intro r hr
    simp only [Finset.mem_Ico] at hr
    have hr1 : 0 < r := hr.1
    have hrk : r < k₀ := hr.2
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hsR : (0 : ℝ) < (((k₀ - r : ℕ)) : ℝ) := by
      have : 0 < k₀ - r := by omega
      exact_mod_cast this
    have hgeq : Nat.gcd k₀ (k₀ - r) = Nat.gcd k₀ r := Nat.gcd_self_sub_right (le_of_lt hrk)
    rw [hgeq]
    have hsq : (0 : ℝ) ≤ Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) := Real.sqrt_nonneg _
    have hmincast : ((min r (k₀ - r) : ℕ) : ℝ) = min ((r : ℝ)) ((((k₀ - r : ℕ))) : ℝ) := by
      rw [Nat.cast_min]
    rw [hmincast]
    rcases le_total ((r : ℝ)) ((((k₀ - r : ℕ))) : ℝ) with hle | hle
    · rw [min_eq_left hle]
      have : (0 : ℝ) ≤ Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / ((((k₀ - r : ℕ))) : ℝ) := by
        positivity
      linarith
    · rw [min_eq_right hle]
      have : (0 : ℝ) ≤ Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / (r : ℝ) := by positivity
      linarith
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_add_distrib]
  have hrefl : ∑ r ∈ Finset.Ico 1 k₀,
      Real.sqrt ((Nat.gcd k₀ (k₀ - r) : ℕ) : ℝ) / (((k₀ - r : ℕ)) : ℝ)
      = ∑ r ∈ Finset.Ico 1 k₀, Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / (r : ℝ) :=
    sum_Ico_reflect k₀ (fun j => Real.sqrt ((Nat.gcd k₀ j : ℕ) : ℝ) / (j : ℝ))
  rw [hrefl]
  have hsubset : ∑ r ∈ Finset.Ico 1 k₀, Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / (r : ℝ)
      ≤ ∑ r ∈ Finset.Icc 1 k₀, Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / (r : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self ?_
    intro i _ _
    positivity
  have hsupply := Salt.Weil.sum_sqrt_gcd_div_le_log_two_mul k₀ (Nat.pos_iff_ne_zero.mp hk₀)
  linarith [hsubset, hsupply]


/-- ⭐ **HB (7.7), the bound half — ESTERMANN SPENT ONCE** (p.222, `hb1983-notes.md:826`).

The `s`-sum of the completion splits along `s mod k₀` (`k = q·k₀`): the `q` residues with
`k₀ ∣ s` see the DEGENERATE arm of `norm_congrExpSum_le` (the length bound `2E`), and the rest
see the geometric arm `‖sq/k‖⁻¹`, whose reciprocal is `k₀/min(r, k₀−r)` at `r = s mod k₀`.
Estermann (7.1) is quoted exactly once, at `norm_kloosterman_estermann`.

The numeral `8` covers both arms with room: the ledger's two constants are `2` (the length arm)
and `1/log 2 = 1.4427…` (the gcd-average arm). -/
theorem klPhaseSum_bound [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B c : ℤ) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E) :
    ‖klPhaseSum k q b A B c‖
      ≤ 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
          * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt k
          * (E * Real.sqrt (Nat.gcd (k / q) c.natAbs : ℝ)
              + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ))) := by
  classical
  obtain ⟨k₀, hkeq⟩ := id hqk
  have hkpos : 0 < k := by omega
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · exfalso; rw [h, Nat.mul_zero] at hkeq; omega
    · exact h
  have hkq : k / q = k₀ := by rw [hkeq]; exact Nat.mul_div_cancel_left k₀ hq
  rw [hkq]
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hk₀R : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk₀pos
  have hskpos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  have hsk2 : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := Real.mul_self_sqrt (le_of_lt hkR)
  -- the residue-indexed majorant
  set hfun : ℕ → ℝ := fun r =>
      if r = 0 then 2 * E * (Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ))
      else Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ)
            * ((k₀ : ℝ) / (2 * ((min r (k₀ - r) : ℕ) : ℝ))) with hfun_def
  -- (a) the per-`s` bound
  have hper : ∀ s : ZMod k,
      ‖kloosterman s (c : ZMod k)‖ * ‖congrExpSum k ((s.val : ℤ)) b q A B‖
        ≤ (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) * Real.sqrt (k : ℝ))
            * hfun (s.val % k₀) := by
    intro s
    have hkl := norm_kloosterman_estermann (k := k) s (c : ZMod k)
    have hcg := norm_congrExpSum_le (q := q) (k := k) hq hqk ((s.val : ℤ)) b A B
    refine le_trans (mul_le_mul hkl hcg (norm_nonneg _) (by positivity)) ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    -- notation
    have hcastv : (((s.val : ℤ)) : ℝ) = ((s.val : ℕ) : ℝ) := by push_cast; ring
    have hkRq : (k : ℝ) = (q : ℝ) * (k₀ : ℝ) := by rw [hkeq]; push_cast; ring
    by_cases hr : s.val % k₀ = 0
    · -- the degenerate arm: `k₀ ∣ s`, the length bound
      have hqcast : ((q : ℕ) : ℝ) = (((q : ℕ) : ℤ) : ℝ) := by push_cast; ring
      have hzero : dist₁ ((((s.val : ℤ)) : ℝ) * (q : ℝ) / (k : ℝ)) 0 = 0 := by
        rw [hqcast, dist₁_mul_div_eq_zero_iff hkpos]
        obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hr
        refine ⟨(t : ℤ), ?_⟩
        have hvt : ((s.val : ℕ) : ℤ) = (k₀ : ℤ) * (t : ℤ) := by exact_mod_cast ht
        rw [hvt, hkeq]
        push_cast
        ring
      rw [if_pos hzero]
      simp only [hfun_def, if_pos hr]
      have hg1 : Nat.gcd k (Nat.gcd s.val ((c : ZMod k)).val) ∣ Nat.gcd k ((c : ZMod k)).val :=
        Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
          ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
      have hgpos : 0 < Nat.gcd k ((c : ZMod k)).val :=
        Nat.pos_of_ne_zero (fun hz => by
          have := (Nat.gcd_eq_zero_iff.mp hz).1; omega)
      have hgle : ((Nat.gcd k (Nat.gcd s.val ((c : ZMod k)).val) : ℕ) : ℝ)
          ≤ ((Nat.gcd k ((c : ZMod k)).val : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hgpos hg1
      have hcc : Nat.gcd k₀ ((c : ZMod k)).val = Nat.gcd k₀ c.natAbs := by
        have hk₀dvd : k₀ ∣ k := ⟨q, by rw [hkeq]; ring⟩
        have hdd : (k₀ : ℤ) ∣ c - ((((c : ZMod k)).val : ℕ) : ℤ) := by
          have hkdvd : (k : ℤ) ∣ c - ((((c : ZMod k)).val : ℕ) : ℤ) := by
            refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
            push_cast
            rw [ZMod.natCast_val, ZMod.cast_id, sub_self]
          exact dvd_trans (Int.natCast_dvd_natCast.mpr hk₀dvd) hkdvd
        have hthis := gcd_natAbs_eq_of_dvd_sub (d := k₀) hdd
        rw [Int.natAbs_natCast] at hthis
        exact hthis.symm
      have hstep : Real.sqrt ((Nat.gcd k (Nat.gcd s.val ((c : ZMod k)).val) : ℕ) : ℝ)
          ≤ Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ) := by
        refine le_trans (Real.sqrt_le_sqrt hgle) ?_
        have h1 : Nat.gcd k ((c : ZMod k)).val = Nat.gcd (q * k₀) ((c : ZMod k)).val := by
          rw [← hkeq]
        rw [h1, ← hcc]
        exact sqrt_gcd_mul_le hq hk₀pos _
      calc Real.sqrt ((Nat.gcd k (Nat.gcd s.val ((c : ZMod k)).val) : ℕ) : ℝ)
            * (((B - A).toNat : ℕ) : ℝ)
          ≤ (Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)) * (2 * E) :=
            mul_le_mul hstep hlen (by positivity) (by positivity)
        _ = 2 * E * (Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)) := by ring
    · -- the geometric arm
      have hrpos : 0 < s.val % k₀ := Nat.pos_of_ne_zero hr
      have hrlt : s.val % k₀ < k₀ := Nat.mod_lt _ hk₀pos
      have hvsplit : ((s.val : ℕ) : ℝ)
          = (k₀ : ℝ) * (((s.val / k₀ : ℕ)) : ℝ) + (((s.val % k₀ : ℕ)) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod (s.val) k₀).symm
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
      have hk0ne : (k₀ : ℝ) ≠ 0 := ne_of_gt hk₀R
      have hcast2 : ((((s.val / k₀ : ℕ) : ℤ)) : ℝ) = (((s.val / k₀ : ℕ)) : ℝ) := by norm_cast
      have hx : (((s.val : ℤ)) : ℝ) * (q : ℝ) / (k : ℝ)
          = ((((s.val / k₀ : ℕ) : ℤ)) : ℝ) + (((s.val % k₀ : ℕ)) : ℝ) / (k₀ : ℝ) := by
        rw [hcastv, hkRq, hcast2, hvsplit]
        field_simp
      have hdlow : (((min (s.val % k₀) (k₀ - s.val % k₀) : ℕ)) : ℝ) / (k₀ : ℝ)
          ≤ dist₁ ((((s.val : ℤ)) : ℝ) * (q : ℝ) / (k : ℝ)) 0 := by
        rw [hx]
        exact dist₁_shift_lower hk₀pos ((s.val / k₀ : ℕ) : ℤ) hrpos hrlt
      have hminpos : (0 : ℝ) < (((min (s.val % k₀) (k₀ - s.val % k₀) : ℕ)) : ℝ) := by
        have hmp : 0 < min (s.val % k₀) (k₀ - s.val % k₀) := by omega
        exact_mod_cast hmp
      have hdpos : 0 < dist₁ ((((s.val : ℤ)) : ℝ) * (q : ℝ) / (k : ℝ)) 0 :=
        lt_of_lt_of_le (by positivity) hdlow
      rw [if_neg (ne_of_gt hdpos)]
      simp only [hfun_def, if_neg hr]
      have hCb : min ((((B - A).toNat : ℕ)) : ℝ)
            (1 / (2 * dist₁ ((((s.val : ℤ)) : ℝ) * (q : ℝ) / (k : ℝ)) 0))
          ≤ (k₀ : ℝ) / (2 * (((min (s.val % k₀) (k₀ - s.val % k₀) : ℕ)) : ℝ)) := by
        refine le_trans (min_le_right _ _) ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hmul : (((min (s.val % k₀) (k₀ - s.val % k₀) : ℕ)) : ℝ)
            ≤ (k₀ : ℝ) * dist₁ ((((s.val : ℤ)) : ℝ) * (q : ℝ) / (k : ℝ)) 0 := by
          have hh := hdlow
          rw [div_le_iff₀ hk₀R] at hh
          linarith [hh]
        linarith [hmul]
      have hgv : Nat.gcd k₀ (s.val) = Nat.gcd k₀ (s.val % k₀) := by
        rw [Nat.gcd_rec k₀ (s.val), Nat.gcd_comm]
      have hstep : Real.sqrt ((Nat.gcd k (Nat.gcd s.val ((c : ZMod k)).val) : ℕ) : ℝ)
          ≤ Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ (s.val % k₀) : ℕ) : ℝ) := by
        have hg1 : Nat.gcd k (Nat.gcd s.val ((c : ZMod k)).val) ∣ Nat.gcd k s.val :=
          Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
            ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
        have hgpos : 0 < Nat.gcd k s.val :=
          Nat.pos_of_ne_zero (fun hz => by
            have := (Nat.gcd_eq_zero_iff.mp hz).1; omega)
        have hgle : ((Nat.gcd k (Nat.gcd s.val ((c : ZMod k)).val) : ℕ) : ℝ)
            ≤ ((Nat.gcd k (s.val) : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_of_dvd hgpos hg1
        refine le_trans (Real.sqrt_le_sqrt hgle) ?_
        have h1 : Nat.gcd k (s.val) = Nat.gcd (q * k₀) (s.val) := by rw [← hkeq]
        rw [h1, ← hgv]
        exact sqrt_gcd_mul_le hq hk₀pos _
      calc Real.sqrt ((Nat.gcd k (Nat.gcd s.val ((c : ZMod k)).val) : ℕ) : ℝ)
            * min ((((B - A).toNat : ℕ)) : ℝ)
              (1 / (2 * dist₁ ((((s.val : ℤ)) : ℝ) * (q : ℝ) / (k : ℝ)) 0))
          ≤ (Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ (s.val % k₀) : ℕ) : ℝ))
              * ((k₀ : ℝ) / (2 * (((min (s.val % k₀) (k₀ - s.val % k₀) : ℕ)) : ℝ))) := by
            refine mul_le_mul hstep hCb ?_ (by positivity)
            exact le_trans (by positivity) (min_le_right _ _)
        _ = Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ (s.val % k₀) : ℕ) : ℝ)
              * ((k₀ : ℝ) / (2 * (((min (s.val % k₀) (k₀ - s.val % k₀) : ℕ)) : ℝ))) := by ring
  -- (b) the residue sum
  have hsum : ∑ s : ZMod k, hfun (s.val % k₀) = (q : ℝ) * ∑ r ∈ Finset.range k₀, hfun r := by
    rw [sum_zmod_val_eq_sum_range k (fun v => hfun (v % k₀))]
    have hkk : k = k₀ * q := by rw [hkeq]; ring
    rw [hkk, sum_range_mul_mod k₀ q hfun]
  have hrange : ∑ r ∈ Finset.range k₀, hfun r
      ≤ Real.sqrt (q : ℝ)
        * (2 * E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
            + (Real.log 2)⁻¹ * (k₀ : ℝ) * (k₀.divisors.card : ℝ)
              * Real.log (2 * (k₀ : ℝ))) := by
    have hins : Finset.range k₀ = insert 0 (Finset.Ico 1 k₀) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hins, Finset.sum_insert (by simp)]
    have h0 : hfun 0
        = 2 * E * (Real.sqrt (q : ℝ) * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)) := by
      simp only [hfun_def, if_pos rfl]
    rw [h0]
    have hIco : ∑ r ∈ Finset.Ico 1 k₀, hfun r
        = (Real.sqrt (q : ℝ) * ((k₀ : ℝ) / 2))
          * ∑ r ∈ Finset.Ico 1 k₀,
              Real.sqrt ((Nat.gcd k₀ r : ℕ) : ℝ) / ((min r (k₀ - r) : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      simp only [Finset.mem_Ico] at hr
      simp only [hfun_def, if_neg (by omega : ¬ r = 0)]
      ring
    rw [hIco]
    have hSle := sum_sqrt_gcd_min_le hk₀pos
    have hcoef : (0 : ℝ) ≤ Real.sqrt (q : ℝ) * ((k₀ : ℝ) / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hSle hcoef]
  -- (c) assembly
  have hchain : ‖klPhaseSum k q b A B c‖
      ≤ (1 / (k : ℝ))
        * ((Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
              * Real.sqrt (k : ℝ))
          * ((q : ℝ) * (Real.sqrt (q : ℝ)
              * (2 * E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
                  + (Real.log 2)⁻¹ * (k₀ : ℝ) * (k₀.divisors.card : ℝ)
                    * Real.log (2 * (k₀ : ℝ)))))) := by
    rw [klPhaseSum_eq_kloosterman (k := k) q b A B c]
    have hnorm : ‖(1 / (k : ℂ)) * ∑ s : ZMod k,
          kloosterman s (c : ZMod k) * congrExpSum k ((s.val : ℤ)) b q A B‖
        ≤ (1 / (k : ℝ)) * ∑ s : ZMod k,
            ‖kloosterman s (c : ZMod k)‖ * ‖congrExpSum k ((s.val : ℤ)) b q A B‖ := by
      rw [norm_mul]
      have h1 : ‖(1 / (k : ℂ))‖ = 1 / (k : ℝ) := by
        rw [norm_div, norm_one, Complex.norm_natCast]
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      exact Finset.sum_congr rfl (fun s _ => norm_mul _ _)
    refine le_trans hnorm ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hper s)) ?_
    rw [← Finset.mul_sum, hsum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left hrange (le_of_lt hqR)
  refine le_trans hchain ?_
  -- the numeric close
  have hsq_inv : (Real.sqrt (k : ℝ))⁻¹ = (k : ℝ)⁻¹ * Real.sqrt (k : ℝ) := by
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
    have hsne : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt hskpos
    field_simp
    linarith [hsk2]
  have hq32 : (q : ℝ) ^ ((3 : ℝ) / 2) = (q : ℝ) * Real.sqrt (q : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hqR, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinv8 : (Real.log 2)⁻¹ ≤ 8 := by
    have h1 : (1 : ℝ) ≤ 8 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
    calc (Real.log 2)⁻¹ = 1 / Real.log 2 := by rw [one_div]
      _ ≤ 8 := by rw [div_le_iff₀ hlog2]; linarith
  have hlgnn : (0 : ℝ) ≤ Real.log (2 * (k₀ : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀pos
    linarith
  have hEnn : (0 : ℝ) ≤ E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ E := by linarith
    positivity
  have hKnn : (0 : ℝ) ≤ (k₀ : ℝ) * (k₀.divisors.card : ℝ) * Real.log (2 * (k₀ : ℝ)) := by
    positivity
  have hW : 2 * E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
        + (Real.log 2)⁻¹ * (k₀ : ℝ) * (k₀.divisors.card : ℝ) * Real.log (2 * (k₀ : ℝ))
      ≤ 8 * (E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
          + (k₀ : ℝ) * (k₀.divisors.card : ℝ) * Real.log (2 * (k₀ : ℝ))) := by
    nlinarith [mul_le_mul_of_nonneg_right hinv8 hKnn, hEnn]
  have hLHS : (1 / (k : ℝ))
      * ((Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * Real.sqrt (k : ℝ))
        * ((q : ℝ) * (Real.sqrt (q : ℝ)
            * (2 * E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
                + (Real.log 2)⁻¹ * (k₀ : ℝ) * (k₀.divisors.card : ℝ)
                  * Real.log (2 * (k₀ : ℝ))))))
      = (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ))
        * (2 * E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
            + (Real.log 2)⁻¹ * (k₀ : ℝ) * (k₀.divisors.card : ℝ)
              * Real.log (2 * (k₀ : ℝ))) := by
    rw [hq32]
    simp only [div_eq_mul_inv, one_mul]
    rw [hsq_inv]
    ring
  rw [hLHS]
  have hpre : (0 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
      * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ) := by positivity
  calc (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ))
        * (2 * E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
            + (Real.log 2)⁻¹ * (k₀ : ℝ) * (k₀.divisors.card : ℝ)
              * Real.log (2 * (k₀ : ℝ)))
      ≤ (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ))
        * (8 * (E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
            + (k₀ : ℝ) * (k₀.divisors.card : ℝ) * Real.log (2 * (k₀ : ℝ)))) :=
        mul_le_mul_of_nonneg_left hW hpre
    _ = 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
          * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
          * (E * Real.sqrt ((Nat.gcd k₀ c.natAbs : ℕ) : ℝ)
              + (k₀ : ℝ) * (k₀.divisors.card : ℝ) * Real.log (2 * (k₀ : ℝ))) := by ring


/-! ## (7.8) — the dyadic `m`-sum -/

/-- ⭐ **HB (7.8) — THE DYADIC SUM** (p.222, `hb1983-notes.md:832`).  Summing the (7.6)+(7.7)
composite over a dyadic block `M < m ≤ 2M`.

Three things are spent here and nowhere else: `lem10ExpSum_kl_mul` folds the frequency `m` into
the Kloosterman phase (`c ↦ m·c`); **`hc : (C, k₀) = 1` is spent** to turn `gcd(k₀, m·c)` into
`gcd(k₀, m)` — HB's own "since `(C,k₀) = 1`", the step the source's display omits; and the gcd
average `sum_sqrt_gcd_dyadic_le_of_dvd` converts `∑_{M<m≤2M} √(k₀,m)` into `2M·d(k)`.

The `d(k)³` is LITERAL (the freeze rule), earned by `d(k)·d(k)·d(k₀) ≤ d(k)³`; the single
`log(2k)` is the sharp intermediate of ADDENDUM A.2, not the cube. -/
theorem lem10_dyadic_bound [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q)) (M : ℕ) :
    ∑ m ∈ Finset.Ioc M (2 * M),
        ‖lem10ExpSum k q b (Finset.Ioc A B) m
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (1 + 4 * Real.pi * M * V) * 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
          * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
          * M * (E + k) / Real.sqrt k := by
  classical
  have hkpos : 0 < k := by omega
  have hkne : k ≠ 0 := by omega
  have hk₀dvd : (k / q) ∣ k := Nat.div_dvd_of_dvd hqk
  have hk₀pos : 0 < k / q := Nat.div_pos (Nat.le_of_dvd hkpos hqk) hq
  have hV0 : (0 : ℝ) ≤ V :=
    le_trans (Finset.sum_nonneg (fun n _ => abs_nonneg _)) hvar
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hPfac : (0 : ℝ) ≤ 1 + 4 * Real.pi * (M : ℝ) * V := by
    have hpi4 : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    have h2 : (0 : ℝ) ≤ 4 * Real.pi * (M : ℝ) := mul_nonneg hpi4 hMR
    have h3 : (0 : ℝ) ≤ 4 * Real.pi * (M : ℝ) * V := mul_nonneg h2 hV0
    linarith
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  have hnatabs : ∀ m : ℕ, ((m : ℤ) * c).natAbs = m * c.natAbs := by
    intro m; rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hgcdmul : ∀ m : ℕ, Nat.gcd (k / q) (m * c.natAbs) = Nat.gcd (k / q) m := by
    intro m
    refine Nat.dvd_antisymm ?_ ?_
    · refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
      have hd : Nat.gcd (k / q) (m * c.natAbs) ∣ m * c.natAbs := Nat.gcd_dvd_right _ _
      have hcop : Nat.Coprime (Nat.gcd (k / q) (m * c.natAbs)) c.natAbs :=
        Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hc.symm
      exact hcop.dvd_of_dvd_mul_right hd
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        ((Nat.gcd_dvd_right (k / q) m).mul_right c.natAbs)
  -- (a) the per-`m` composite
  have hper : ∀ m ∈ Finset.Ioc M (2 * M),
      ‖lem10ExpSum k q b (Finset.Ioc A B) m
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
        ≤ (1 + 4 * Real.pi * (M : ℝ) * V)
          * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
              * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
            * (E * Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ)
                + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ)))) := by
    intro m hmem
    simp only [Finset.mem_Ioc] at hmem
    have habel := lem10_abel_transfer k q b A B hAB m g
      (fun n => (c : ℝ) * (invMod n k : ℝ) / k)
      (W := 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
              * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
            * (E * Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ)
                + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ))))
      (V := V) ?_ hvar
    · refine le_trans habel ?_
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · have hmle : (m : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hmem.2
        have hpv : (0 : ℝ) ≤ 2 * Real.pi * V := mul_nonneg (by positivity) hV0
        linarith [mul_le_mul_of_nonneg_left hmle hpv]
      · have hlognn : (0 : ℝ) ≤ Real.log (2 * ((k / q : ℕ) : ℝ)) := by
          refine Real.log_nonneg ?_
          have h1 : (1 : ℝ) ≤ ((k / q : ℕ) : ℝ) := by exact_mod_cast hk₀pos
          linarith
        have h1 : (0 : ℝ) ≤ E * Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ) := by positivity
        have h2 : (0 : ℝ) ≤ ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
            * Real.log (2 * ((k / q : ℕ) : ℝ)) :=
          mul_nonneg (by positivity) hlognn
        have h3 : (0 : ℝ) ≤ 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
            * (k.divisors.card : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ) := by
          positivity
        exact mul_nonneg h3 (by linarith)
    · intro n hnB
      rw [lem10ExpSum_kl_mul]
      have hkp : lem10ExpSum k q b (Finset.Ioc A n) 1
          (fun x => (((m : ℤ) * c : ℤ) : ℝ) * (invMod x k : ℝ) / k)
          = klPhaseSum k q b A n ((m : ℤ) * c) := rfl
      rw [hkp]
      have hlen' : (((n - A).toNat : ℕ) : ℝ) ≤ 2 * E := by
        have h1 : (n - A).toNat ≤ (B - A).toNat := by omega
        have h2 : (((n - A).toNat : ℕ) : ℝ) ≤ (((B - A).toNat : ℕ) : ℝ) := by exact_mod_cast h1
        linarith [hlen]
      have hbd := klPhaseSum_bound (k := k) hk hq hqk b A n ((m : ℤ) * c) hE hlen'
      rw [hnatabs m, hgcdmul m] at hbd
      exact hbd
  -- (b) the dyadic sum
  have hcard : (Finset.Ioc M (2 * M)).card = M := by rw [Nat.card_Ioc]; omega
  have hsplit : ∑ m ∈ Finset.Ioc M (2 * M),
        ((1 + 4 * Real.pi * (M : ℝ) * V)
          * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
              * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
            * (E * Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ)
                + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ)))))
      = (1 + 4 * Real.pi * (M : ℝ) * V)
          * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
              * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ))
          * (E * (∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ))
              + (M : ℝ) * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ)))) := by
    rw [Finset.sum_congr rfl (fun m _ =>
      show (1 + 4 * Real.pi * (M : ℝ) * V)
          * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
              * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
            * (E * Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ)
                + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ))))
        = ((1 + 4 * Real.pi * (M : ℝ) * V)
            * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
                * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)) * E)
            * Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ)
          + (1 + 4 * Real.pi * (M : ℝ) * V)
            * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
                * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ))
            * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                * Real.log (2 * ((k / q : ℕ) : ℝ))) by ring)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  have hgcdsum : ∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ)
      ≤ 2 * (M : ℝ) * (k.divisors.card : ℝ) :=
    sum_sqrt_gcd_dyadic_le_of_dvd hkne hk₀dvd
  -- (c) the numeric close
  have hd1 : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
    have : 1 ≤ k.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hkne⟩
    exact_mod_cast this
  have hlog1 : (1 : ℝ) ≤ Real.log (2 * (k : ℝ)) := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h4 : (4 : ℝ) ≤ 2 * (k : ℝ) := by linarith
    have : Real.log 4 ≤ Real.log (2 * (k : ℝ)) := Real.log_le_log (by norm_num) h4
    have h4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4eq] at this
    nlinarith [Real.log_two_gt_d9]
  have hKle : ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
        * Real.log (2 * ((k / q : ℕ) : ℝ))
      ≤ (k : ℝ) * (k.divisors.card : ℝ) * Real.log (2 * (k : ℝ)) := by
    have h1 : ((k / q : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hkpos hk₀dvd
    have h2 : (((k / q).divisors.card : ℕ) : ℝ) ≤ (k.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_le_of_dvd hkne hk₀dvd
    have h3 : Real.log (2 * ((k / q : ℕ) : ℝ)) ≤ Real.log (2 * (k : ℝ)) := by
      refine Real.log_le_log (by positivity) ?_
      linarith
    have h4 : (0 : ℝ) ≤ Real.log (2 * ((k / q : ℕ) : ℝ)) := by
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ ((k / q : ℕ) : ℝ) := by exact_mod_cast hk₀pos
      linarith
    have h5 : (0 : ℝ) ≤ ((k / q : ℕ) : ℝ) := by positivity
    have h6 : (0 : ℝ) ≤ (((k / q).divisors.card : ℕ) : ℝ) := by positivity
    have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    calc ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
            * Real.log (2 * ((k / q : ℕ) : ℝ))
        ≤ (k : ℝ) * ((k / q).divisors.card : ℝ) * Real.log (2 * ((k / q : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h6) h4
      _ ≤ (k : ℝ) * (k.divisors.card : ℝ) * Real.log (2 * ((k / q : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hkR0) h4
      _ ≤ (k : ℝ) * (k.divisors.card : ℝ) * Real.log (2 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hnum : 16 * E * (k.divisors.card : ℝ) ^ 2
        + 8 * (k.divisors.card : ℝ)
          * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
              * Real.log (2 * ((k / q : ℕ) : ℝ)))
      ≤ 16 * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (E + (k : ℝ)) := by
    have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hd0 : (0 : ℝ) ≤ (k.divisors.card : ℝ) := by positivity
    have hL0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := by linarith
    have hdL : (1 : ℝ) ≤ (k.divisors.card : ℝ) * Real.log (2 * (k : ℝ)) := by
      nlinarith [hd1, hlog1]
    have hA := mul_le_mul_of_nonneg_left hKle
      (by linarith : (0 : ℝ) ≤ 8 * (k.divisors.card : ℝ))
    have hB : 16 * E * (k.divisors.card : ℝ) ^ 2
        ≤ 16 * E * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) := by
      have h1 : (k.divisors.card : ℝ) ^ 2 * 1
          ≤ (k.divisors.card : ℝ) ^ 2 * ((k.divisors.card : ℝ) * Real.log (2 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_left hdL (by positivity)
      have h2 : (0 : ℝ) ≤ 16 * E := by linarith
      linarith [mul_le_mul_of_nonneg_left h1 h2]
    have hd23 : 8 * (k.divisors.card : ℝ) ^ 2 ≤ 16 * (k.divisors.card : ℝ) ^ 3 := by
      nlinarith [hd1, hd0]
    have hC : 8 * (k : ℝ) * (k.divisors.card : ℝ) ^ 2 * Real.log (2 * (k : ℝ))
        ≤ 16 * (k : ℝ) * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) := by
      have hkl : (0 : ℝ) ≤ (k : ℝ) * Real.log (2 * (k : ℝ)) := mul_nonneg hkR hL0
      linarith [mul_le_mul_of_nonneg_left hd23 hkl]
    linarith [hA, hB, hC]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [hsplit]
  have hpre : (0 : ℝ) ≤ (1 + 4 * Real.pi * (M : ℝ) * V)
      * (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (q : ℝ) ^ ((3 : ℝ) / 2)
          / Real.sqrt (k : ℝ)) := by positivity
  have hinner : E * (∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ))
      + (M : ℝ) * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
          * Real.log (2 * ((k / q : ℕ) : ℝ)))
      ≤ E * (2 * (M : ℝ) * (k.divisors.card : ℝ))
        + (M : ℝ) * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
            * Real.log (2 * ((k / q : ℕ) : ℝ))) := by
    have := mul_le_mul_of_nonneg_left hgcdsum hE0.le
    linarith [this]
  have hstep1 : (1 + 4 * Real.pi * (M : ℝ) * V)
        * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ))
        * (E * (∑ m ∈ Finset.Ioc M (2 * M), Real.sqrt ((Nat.gcd (k / q) m : ℕ) : ℝ))
            + (M : ℝ) * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                * Real.log (2 * ((k / q : ℕ) : ℝ))))
      ≤ (1 + 4 * Real.pi * (M : ℝ) * V)
        * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ))
        * (E * (2 * (M : ℝ) * (k.divisors.card : ℝ))
            + (M : ℝ) * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                * Real.log (2 * ((k / q : ℕ) : ℝ)))) := by
    refine mul_le_mul_of_nonneg_left hinner ?_
    positivity
  refine le_trans hstep1 ?_
  calc (1 + 4 * Real.pi * (M : ℝ) * V)
        * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ))
        * (E * (2 * (M : ℝ) * (k.divisors.card : ℝ))
            + (M : ℝ) * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                * Real.log (2 * ((k / q : ℕ) : ℝ))))
      = ((1 + 4 * Real.pi * (M : ℝ) * V)
          * (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (q : ℝ) ^ ((3 : ℝ) / 2)
              / Real.sqrt (k : ℝ)))
        * ((M : ℝ) * (16 * E * (k.divisors.card : ℝ) ^ 2
            + 8 * (k.divisors.card : ℝ)
              * (((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ))))) := by ring
    _ ≤ ((1 + 4 * Real.pi * (M : ℝ) * V)
          * (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (q : ℝ) ^ ((3 : ℝ) / 2)
              / Real.sqrt (k : ℝ)))
        * ((M : ℝ) * (16 * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ))
            * (E + (k : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnum hMR) hpre
    _ = (1 + 4 * Real.pi * (M : ℝ) * V) * 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
          * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
          * (M : ℝ) * (E + (k : ℝ)) / Real.sqrt (k : ℝ) := by ring


/-! ## R-A6 — the `±m` conjugation bridge

The final assembly of Lemma 10 sums over `m ∈ ℤ` (to match `majorantCoeff`'s index) while every
workhorse above is indexed by `m : ℕ`.  Per gate ruling **R-A6 the two index types never mix
inside one statement**; this single row is the bridge, and it is an equality of NORMS, which is
all the assembly needs. -/

/-- The carrier at a negated argument is the conjugate: `e(−x) = conj (e x)`. -/
lemma e_neg_eq_conj (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  have hx : e x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold Salt.LS.e; congr 1; push_cast; ring
  have hnx : e (-x) = Complex.exp (((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I) := by
    unfold Salt.LS.e; congr 1; push_cast; ring
  rw [hx, hnx, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- ⭐ **THE `±m` BRIDGE (R-A6).**  `‖S_{−m}‖ = ‖S_m‖`: the primed sum at the negated frequency
is the complex conjugate of the sum at `+m`, so the two have the same modulus.

*Stated as an equality of norms rather than of sums on purpose.*  The assembly of Lemma 10 pairs
`m` with `−m` under `∑_{0<|m|≤K}`, where only the modulus is ever used; carrying the conjugation
itself into the chain would force every downstream bound to travel with a `starRingEnd`. -/
lemma norm_lem10ExpSum_neg (k q : ℕ) (b : ℤ) (I : Finset ℤ) (m : ℕ) (f : ℤ → ℝ) :
    ‖∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b),
        e (-((m : ℝ) * f n))‖
      = ‖lem10ExpSum k q b I m f‖ := by
  unfold lem10ExpSum
  rw [Finset.sum_congr rfl (fun n _ => e_neg_eq_conj ((m : ℝ) * f n)),
    ← map_sum (starRingEnd ℂ) (fun n => e ((m : ℝ) * f n))
      (I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b))]
  exact RCLike.norm_conj _


end Salt.N7
