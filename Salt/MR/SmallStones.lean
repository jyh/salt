/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.BallSup
import Salt.MR.RamareMR

/-!
# SmallStones — two residual B-stones of the MR block

Two independent residuals, each recorded in the header of the file it serves.

## Stone 1 — `BallSup`'s residual #2: the `hMball` conversion

`BallSup.ball_sup_of_center` carries the named hypothesis

  `hMball : ∀ x ∈ [X, 2X], 𝔻(f·n^{−it₁}, 1; x)² ≤ P(x)/8`

(the A.4 ball dichotomy in *Mertens-mass* form), while `PropA3Core.dist_split_A4_frozen`
states the branch-b centre cap in *loglog* form, `≤ (1/16)·loglog X`.  `BallSup`'s header
records the exact obstruction: converting `(1/16)·loglog X ≤ P(x)/8` needs

  `12/log X − M ≤ (1/2)·loglog X`,

i.e. a large-`X` threshold **plus a numeric lower bound on the Meissel–Mertens constant**
`M` — "neither is in the corpus, so the conversion is NOT performed here".

Both are supplied here:

* `mertensM_ge_neg_seventeen` — `−17 ≤ M`.  The bound is crude (the true value is
  `M ≈ 0.2615`) but it is the only kind available *from the corpus itself*: the sharp
  Mertens-2 estimate `mertens_second_sharp_real` at `t = 2` reads
  `|1/2 − (log log 2 + M)| ≤ 12/log 2`, and `12/log 2 ≤ 17.4`, `log log 2 ≤ 0` finish it.
  A sharper constant would need `γ`- and `B`-numerics through `mertensM_eq_sub`, which the
  corpus does not carry.
* `ballMertensThreshold := exp (exp 40)` and `loglog_mertens_slack` — the explicit
  threshold at which the crude constant still closes the slack inequality (`loglog X ≥ 40`
  against `12/log X ≤ 1` and `−M ≤ 17`, margin `2`).
* `sixteenth_loglog_le_SPartial_div_eight` — the numeric core: for `X` past the threshold
  and any `x ≥ X`, `(1/16)·loglog X ≤ P(x)/8`.
* `A4_to_mertens_form` — the conversion in the abstract (any quantity capped by the A.4
  ball convention on `[X,2X]` obeys the Mertens-mass convention there), and
  `hMball_of_A4_cap` — the same in `ball_sup_of_center`'s literal binder shape.

What is **not** closed: the A.4 branch-b cap is stated for `pretDistSq f (costwist t₁) X`
(untwisted `f`, twist in the second slot, at the single scale `X`), whereas `hMball` wants
`pretDistSq (f·eIu(−t₁)) 1 x` on the whole of `[X,2X]`.  The *shape* move (twist transfer
between the slots) and the *scale* move (`X ⟶ x ∈ [X,2X]`) are a separate residual; the
stone here is the Mertens-mass conversion, which is what `BallSup`'s header names.

## Stone 2 — `RamareMR`'s residual: the `p²` row's `1/P` collapse

`lemma12_meansq_mr_consume` leaves the `p²` row's symbolic mass
`∑_{n≤N} ‖ramP2coeffMR n‖²/n²` in-statement, noting "its collapse to MR's `1/P` is the
`∑_{p≥P} p^{−2}` zeta-tail — a separate stone".  That stone is `ramP2mass_le`:

  `∑_{n≤N} ‖ramP2coeffMR n‖²/n² ≤ 64/P²`   (1-bounded `a`, `b`, `c`; `1 ≤ P`, `1 ≤ X`).

The page.  Every summand of `ramP2coeffMR n` has norm `≤ 2` (`ramareWeight ≤ 1`,
`(ω+1)⁻¹ ≤ 1`), so with `A n := ∑_{σ ↦ n} 2/(σ.1·σ.2)` one has `‖coeff n‖/n ≤ A n`;
`∑ a² ≤ (∑ a)²` for non-negative `a` (`sum_sq_le_sq_sum`) and the fiberwise identity
(`Finset.sum_fiberwise_of_maps_to`, the same `hmaps` as `ramP2corrMR_eq_spoly`) turn the
mass into `(∑_{σ ∈ ramP2domMR} 2/(σ.1σ.2))²`.  On the domain `p ∣ m` and `X ≤ pm ≤ 2X`,
so `1/(pm) ≤ 1/X` while the cofactors inject into `[1, 2X/p²]` (`m ↦ m/p`): the inner sum
is `≤ (2X/p²)·(2/X) = 4/p²`.  The prime sum is then dominated by the integer tail
`∑_{P ≤ n ≤ Q} n^{−2} ≤ 2/P` (`sum_inv_sq_tail_le`, telescoping `n^{−2} ≤ (n−1)^{−1} − n^{−1}`),
giving `(4·2/P)² = 64/P²`.  This is *stronger* than MR's `1/P` row (`64/P² ≤ 64/P` for
`P ≥ 1`, `ramP2mass_le_inv_P`), and `lemma12_meansq_mr_final` plugs it into
`lemma12_meansq_mr_consume`.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## Stone 1 — the Mertens-mass conversion of the A.4 ball convention -/

/-- `S(2) = 1/2`: the only prime `≤ 2` is `2`. -/
lemma SPartial_two : Salt.Mertens.SPartial 2 = 1 / 2 := by
  have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
  rw [Salt.Mertens.SPartial, hfl]
  have hset : (Finset.range (2 + 1)).filter Nat.Prime = {2} := by decide
  rw [hset]
  norm_num

/-- **A numeric lower bound on the Meissel–Mertens constant**: `−17 ≤ M`.

Crude (the true value is `M = γ − B ≈ 0.2615`) but corpus-internal: the sharp
real-variable Mertens-2 estimate at `t = 2` gives `1/2 − log log 2 − M ≤ 12/log 2`, and
`log log 2 ≤ 0` (since `log 2 ≤ 1`) together with `12/log 2 ≤ 17.4` close it. -/
theorem mertensM_ge_neg_seventeen : (-17 : ℝ) ≤ Salt.Mertens.mertensM := by
  have hkey := Salt.Mertens.mertens_second_sharp_real (t := 2) le_rfl
  rw [SPartial_two] at hkey
  have hlo := (abs_le.mp hkey).2
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hll : Real.log (Real.log 2) ≤ 0 :=
    Real.log_nonpos (le_of_lt hlog2pos) (by linarith)
  have h12 : 12 / Real.log 2 ≤ 17.4 := by
    rw [div_le_iff₀ hlog2pos]; nlinarith
  linarith

/-- The threshold past which the crude constant `−17 ≤ M` still closes the A.4 conversion:
`exp (exp 40)` (so `loglog X ≥ 40`). -/
noncomputable def ballMertensThreshold : ℝ := Real.exp (Real.exp 40)

lemma exp_forty_ge : (41 : ℝ) ≤ Real.exp 40 := by
  have := Real.add_one_le_exp (40 : ℝ); linarith

/-- The threshold clears every positivity floor the consumers use (`3 ≤ X`). -/
theorem three_le_ballMertensThreshold : (3 : ℝ) ≤ ballMertensThreshold := by
  have h1 : (42 : ℝ) ≤ Real.exp 41 := by have := Real.add_one_le_exp (41 : ℝ); linarith
  have h2 : Real.exp 41 ≤ Real.exp (Real.exp 40) :=
    Real.exp_le_exp.mpr exp_forty_ge
  rw [ballMertensThreshold]; linarith

/-- Past the threshold, `log X ≥ exp 40` and `log log X ≥ 40`. -/
lemma loglog_ge_forty {X : ℝ} (hX : ballMertensThreshold ≤ X) :
    Real.exp 40 ≤ Real.log X ∧ (40 : ℝ) ≤ Real.log (Real.log X) := by
  have h1 : Real.log ballMertensThreshold ≤ Real.log X :=
    Real.log_le_log (by rw [ballMertensThreshold]; exact Real.exp_pos _) hX
  rw [ballMertensThreshold, Real.log_exp] at h1
  refine ⟨h1, ?_⟩
  have h2 : Real.log (Real.exp 40) ≤ Real.log (Real.log X) :=
    Real.log_le_log (Real.exp_pos 40) h1
  rwa [Real.log_exp] at h2

/-- **The slack inequality** `12/log X − M ≤ (1/2)·loglog X` at the threshold.  This is the
exact numeric obligation `BallSup`'s header names. -/
theorem loglog_mertens_slack {X : ℝ} (hX : ballMertensThreshold ≤ X) :
    12 / Real.log X - Salt.Mertens.mertensM ≤ (1 / 2) * Real.log (Real.log X) := by
  obtain ⟨h1, h2⟩ := loglog_ge_forty hX
  have hpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le (by linarith [exp_forty_ge]) h1
  have hsmall : 12 / Real.log X ≤ 1 := by
    rw [div_le_one hpos]; linarith [exp_forty_ge]
  linarith [mertensM_ge_neg_seventeen]

/-- Past the threshold `X` is comfortably `≥ 2`, hence so is every `x ≥ X`. -/
lemma two_le_of_threshold {X x : ℝ} (hX : ballMertensThreshold ≤ X) (hx : X ≤ x) :
    (2 : ℝ) ≤ x := le_trans (by linarith [three_le_ballMertensThreshold]) (le_trans hX hx)

/-- **The numeric core of the conversion.**  For `X` past `ballMertensThreshold` and any
`x ≥ X`, the A.4 ball convention `(1/16)·loglog X` sits below the Mertens-mass convention
`P(x)/8`.

Route: `mertens_second_sharp_real` gives `P(x) ≥ loglog x + M − 12/log x`; `loglog` is
monotone and `12/log ·` decreasing, so `P(x) ≥ loglog X + M − 12/log X`, and
`loglog X + M − 12/log X ≥ (1/2)·loglog X` is `loglog_mertens_slack`. -/
theorem sixteenth_loglog_le_SPartial_div_eight {X x : ℝ}
    (hX : ballMertensThreshold ≤ X) (hx : X ≤ x) :
    (1 / 16) * Real.log (Real.log X) ≤ Salt.Mertens.SPartial x / 8 := by
  obtain ⟨h1, _h2⟩ := loglog_ge_forty hX
  have hlogXpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le (by linarith [exp_forty_ge]) h1
  have hX2 : (2 : ℝ) ≤ X := le_trans (by linarith [three_le_ballMertensThreshold]) hX
  have hx2 : (2 : ℝ) ≤ x := two_le_of_threshold hX hx
  have hsharp := (abs_le.mp (Salt.Mertens.mertens_second_sharp_real hx2)).1
  -- `log x ≥ log X > 0`
  have hlogmono : Real.log X ≤ Real.log x := Real.log_le_log (by linarith) hx
  have hlogxpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le hlogXpos hlogmono
  have hllmono : Real.log (Real.log X) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogXpos hlogmono
  have hdiv : 12 / Real.log x ≤ 12 / Real.log X := by
    apply div_le_div_of_nonneg_left (by norm_num) hlogXpos hlogmono
  have hslack := loglog_mertens_slack hX
  linarith

/-- **STONE 1 — the A.4 ⟶ Mertens-mass conversion, abstract.**  Any quantity capped by the
A.4 ball convention `(1/16)·loglog X` on the dyadic range `[X, 2X]` obeys the Mertens-mass
convention `P(x)/8` there, provided `X ≥ ballMertensThreshold`. -/
theorem A4_to_mertens_form {X : ℝ} (hX : ballMertensThreshold ≤ X) {D : ℝ → ℝ}
    (hD : ∀ x : ℝ, X ≤ x → x ≤ 2 * X → D x ≤ (1 / 16) * Real.log (Real.log X)) :
    ∀ x : ℝ, X ≤ x → x ≤ 2 * X → D x ≤ Salt.Mertens.SPartial x / 8 :=
  fun x h1 h2 => (hD x h1 h2).trans (sixteenth_loglog_le_SPartial_div_eight hX h1)

/-- **STONE 1, exit — `ball_sup_of_center`'s `hMball` from the A.4 ball cap.**  In the
literal binder shape of `BallSup.ball_sup_of_center`. -/
theorem hMball_of_A4_cap {f : ℕ → ℂ} {X t₁ : ℝ} (hX : ballMertensThreshold ≤ X)
    (hcap : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1) x
        ≤ (1 / 16) * Real.log (Real.log X)) :
    ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8 :=
  A4_to_mertens_form (D := fun x => pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1) x)
    hX hcap

/-! ## Stone 2 — the `p²` row's zeta-tail collapse -/

/-- **The integer `n^{-2}` tail**: `∑_{P ≤ n ≤ Q} n^{−2} ≤ 2/P` for `1 ≤ P`.  Telescoping
`n^{−2} ≤ (n−1)^{−1} − n^{−1}` above `P ≥ 2`; the `P = 1` case is `sum_inv_sq_le`. -/
private lemma sum_inv_sq_Icc_telescope {P : ℕ} (hP : 2 ≤ P) :
    ∀ Q : ℕ, P ≤ Q → ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2
      ≤ 1 / ((P : ℝ) - 1) - 1 / (Q : ℝ) := by
  intro Q hQ
  have hP2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  induction Q, hQ using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hPne : (P : ℝ) ≠ 0 := by linarith
    have hP1ne : (P : ℝ) - 1 ≠ 0 := by linarith
    have hstep : 1 / ((P : ℝ) - 1) - 1 / (P : ℝ) = 1 / ((P : ℝ) * ((P : ℝ) - 1)) := by
      field_simp; ring
    rw [hstep]
    refine one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  | succ Q hQ ih =>
    have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := le_trans hP2 (by exact_mod_cast hQ)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hcast : ((Q + 1 : ℕ) : ℝ) = (Q : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hQne : (Q : ℝ) ≠ 0 := by linarith
    have hQ1ne : (Q : ℝ) + 1 ≠ 0 := by linarith
    have hstep : 1 / (Q : ℝ) - 1 / ((Q : ℝ) + 1) = 1 / ((Q : ℝ) * ((Q : ℝ) + 1)) := by
      field_simp; ring
    have hnew : 1 / ((Q : ℝ) + 1) ^ 2 ≤ 1 / (Q : ℝ) - 1 / ((Q : ℝ) + 1) := by
      rw [hstep]
      refine one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
    linarith

/-- `∑_{P ≤ n ≤ Q} n^{−2} ≤ 2/P` for `1 ≤ P`. -/
lemma sum_inv_sq_tail_le {P : ℕ} (hP : 1 ≤ P) (Q : ℕ) :
    ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 ≤ 2 / (P : ℝ) := by
  rcases eq_or_lt_of_le hP with h1 | h2
  · rw [← h1]
    simpa using sum_inv_sq_le Q
  · have hP2 : 2 ≤ P := h2
    have hP2R : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP2
    rcases le_or_gt P Q with hQ | hQ
    · have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := le_trans hP2R (by exact_mod_cast hQ)
      have h := sum_inv_sq_Icc_telescope hP2 Q hQ
      have hb : 1 / ((P : ℝ) - 1) ≤ 2 / (P : ℝ) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
      have hQpos : (0 : ℝ) < 1 / (Q : ℝ) := by positivity
      linarith
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity

/-- Squares sum below the square of the sum, for non-negative terms. -/
private lemma sum_sq_le_sq_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) : ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have hS : ∀ i ∈ s, f i ^ 2 ≤ f i * ∑ j ∈ s, f j := by
    intro i hi
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hf hi) (hf i hi)
  calc ∑ i ∈ s, f i ^ 2 ≤ ∑ i ∈ s, f i * ∑ j ∈ s, f j := Finset.sum_le_sum hS
    _ = (∑ i ∈ s, f i) * ∑ j ∈ s, f j := by rw [← Finset.sum_mul]
    _ = (∑ i ∈ s, f i) ^ 2 := (sq _).symm

/-- The Ramaré weight is bounded by `1` in absolute value: its denominator is either `0`
(Lean's `1/0 = 0`) or at least `1`. -/
lemma abs_ramareWeight_le_one (P Q p m : ℕ) : |ramareWeight P Q p m| ≤ 1 := by
  rw [ramareWeight]
  have hite : (0 : ℝ) ≤ (if Nat.Coprime p m then 1 else 0) := by split_ifs <;> norm_num
  have hcard : (0 : ℝ) ≤ ((BlockPrimeDivs P Q m).card : ℝ) := Nat.cast_nonneg _
  have hcase : ((BlockPrimeDivs P Q m).card : ℝ) + (if Nat.Coprime p m then 1 else 0) = 0 ∨
      (1 : ℝ) ≤ ((BlockPrimeDivs P Q m).card : ℝ) + (if Nat.Coprime p m then 1 else 0) := by
    rcases Nat.eq_zero_or_pos (BlockPrimeDivs P Q m).card with h0 | h0
    · by_cases hc : Nat.Coprime p m
      · right; rw [h0, if_pos hc]; norm_num
      · left; rw [h0, if_neg hc]; norm_num
    · right
      have h1 : (1 : ℝ) ≤ ((BlockPrimeDivs P Q m).card : ℝ) := by exact_mod_cast h0
      linarith
  rcases hcase with h | h
  · rw [h]; norm_num
  · rw [abs_of_nonneg (by positivity), div_le_one (by linarith)]
    linarith

/-- `‖(ω(m;P,Q) + 1)⁻¹‖ ≤ 1`. -/
lemma norm_blockOmega_inv_le_one (P Q m : ℕ) :
    ‖((blockOmega P Q m : ℂ) + 1)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hc : ((blockOmega P Q m : ℕ) : ℂ) + 1 = ((blockOmega P Q m + 1 : ℕ) : ℂ) := by
    push_cast; ring
  rw [hc, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ ((blockOmega P Q m + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ blockOmega P Q m + 1 := Nat.le_add_left 1 _
    exact_mod_cast this
  rw [inv_eq_one_div, div_le_one (by linarith)]
  linarith

/-- Each summand of `ramP2coeffMR` has norm `≤ 2`. -/
lemma ramP2_term_norm_le {P Q : ℕ} {a b c : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) (p m : ℕ) :
    ‖(ramareWeight P Q p m : ℂ) * a (p * m)
        - b m * c p * ((blockOmega P Q m : ℂ) + 1)⁻¹‖ ≤ 2 := by
  have h1 : ‖(ramareWeight P Q p m : ℂ) * a (p * m)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := abs_ramareWeight_le_one P Q p m
    have h2 := ha (p * m)
    nlinarith [abs_nonneg (ramareWeight P Q p m), norm_nonneg (a (p * m))]
  have h2 : ‖b m * c p * ((blockOmega P Q m : ℂ) + 1)⁻¹‖ ≤ 1 := by
    rw [norm_mul, norm_mul]
    have hbm := hb m
    have hcp := hc p
    have hw := norm_blockOmega_inv_le_one P Q m
    calc ‖b m‖ * ‖c p‖ * ‖((blockOmega P Q m : ℂ) + 1)⁻¹‖
        ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul hbm hcp (norm_nonneg _) (by norm_num)) hw
            (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc ‖(ramareWeight P Q p m : ℂ) * a (p * m)
        - b m * c p * ((blockOmega P Q m : ℂ) + 1)⁻¹‖
      ≤ ‖(ramareWeight P Q p m : ℂ) * a (p * m)‖
        + ‖b m * c p * ((blockOmega P Q m : ℂ) + 1)⁻¹‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

/-- **The `p²` cofactor count.**  The cofactors `m` with `p ∣ m` and `X ≤ pm ≤ 2X` inject
into `[1, 2X/p²]` via `m ↦ m/p`, so there are at most `2X/p²` of them. -/
private lemma card_ramP2_cofactors_le (N X p : ℕ) (hp : 0 < p) :
    ((((ramHonMR N X p).filter (fun m => p ∣ m)).card : ℕ) : ℝ) ≤ 2 * (X : ℝ) / (p : ℝ) ^ 2 := by
  classical
  have hcard : ((ramHonMR N X p).filter (fun m => p ∣ m)).card
      ≤ (Finset.Icc 1 (2 * X / (p * p))).card := by
    refine Finset.card_le_card_of_injOn (fun m => m / p) ?_ ?_
    · intro m hm
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hm
      obtain ⟨hmem, hdvd⟩ := hm
      rw [ramHonMR, Finset.mem_filter, Finset.mem_Icc] at hmem
      obtain ⟨⟨hm1, _hmN⟩, _hlo, hhi⟩ := hmem
      have hpm : p * m ≤ 2 * X := by
        have : ((p * m : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, Nat.mul_zero] at hk; omega
        · exact h0
      have hkdiv : m / p = k := by rw [hk]; exact Nat.mul_div_cancel_left k hp
      have hkle : k ≤ 2 * X / (p * p) := by
        rw [Nat.le_div_iff_mul_le (by positivity)]
        calc k * (p * p) = p * (p * k) := by ring
          _ = p * m := by rw [hk]
          _ ≤ 2 * X := hpm
      simp only [Finset.coe_Icc, Set.mem_Icc, hkdiv]
      exact ⟨hk0, hkle⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hm₁ hm₂
      have h1 : m₁ / p * p = m₁ := Nat.div_mul_cancel hm₁.2
      have h2 : m₂ / p * p = m₂ := Nat.div_mul_cancel hm₂.2
      have h3 : m₁ / p = m₂ / p := heq
      rw [← h1, ← h2, h3]
  have hIcc : (Finset.Icc 1 (2 * X / (p * p))).card = 2 * X / (p * p) := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  rw [hIcc] at hcard
  have hstep : (((2 * X / (p * p) : ℕ)) : ℝ) ≤ ((2 * X : ℕ) : ℝ) / ((p * p : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hcast : ((2 * X : ℕ) : ℝ) / ((p * p : ℕ) : ℝ) = 2 * (X : ℝ) / (p : ℝ) ^ 2 := by
    push_cast; ring
  have hleft : (((ramHonMR N X p).filter (fun m => p ∣ m)).card : ℝ)
      ≤ (((2 * X / (p * p) : ℕ)) : ℝ) := by exact_mod_cast hcard
  rw [hcast] at hstep
  linarith

/-- The inner (`p`-fixed) row of the `p²` domain sum: `∑_m 2/(pm) ≤ 4/p²`. -/
private lemma ramP2_inner_row_le (N X p : ℕ) (hX : 1 ≤ X) (hp : 0 < p) :
    ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m), 2 / ((p * m : ℕ) : ℝ)
      ≤ 4 / (p : ℝ) ^ 2 := by
  classical
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hterm : ∀ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m),
      2 / ((p * m : ℕ) : ℝ) ≤ 2 / (X : ℝ) := by
    intro m hm
    rw [Finset.mem_filter, ramHonMR, Finset.mem_filter] at hm
    obtain ⟨⟨-, hlo, -⟩, -⟩ := hm
    have hcast : ((p * m : ℕ) : ℝ) = (p : ℝ) * (m : ℝ) := by push_cast; ring
    rw [hcast]
    exact div_le_div_of_nonneg_left (by norm_num) hX0 hlo
  have hbound := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hbound
  refine hbound.trans ?_
  have hc := card_ramP2_cofactors_le N X p hp
  have hmul : (((ramHonMR N X p).filter (fun m => p ∣ m)).card : ℝ) * (2 / (X : ℝ))
      ≤ (2 * (X : ℝ) / (p : ℝ) ^ 2) * (2 / (X : ℝ)) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  refine hmul.trans ?_
  rw [div_mul_div_comm]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  ring_nf
  nlinarith [sq_nonneg ((p : ℝ)), hX0.le, hp0.le]

/-- **The whole `p²` domain sum** `∑_{σ ∈ ramP2domMR} 2/(σ.1σ.2) ≤ 8/P`: the `p`-rows
are `≤ 4/p²`, and the block primes sit inside `[P,Q]`, where `sum_inv_sq_tail_le` gives
`2/P`. -/
private lemma ramP2_dom_sum_le (N X P Q : ℕ) (hX : 1 ≤ X) (hP : 1 ≤ P) :
    ∑ σ ∈ ramP2domMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ) ≤ 8 / (P : ℝ) := by
  classical
  rw [ramP2domMR, Finset.sum_sigma]
  have hrow : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      ∑ m ∈ (ramHonMR N X p).filter (fun m => p ∣ m), 2 / ((p * m : ℕ) : ℝ)
        ≤ 4 / (p : ℝ) ^ 2 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ramP2_inner_row_le N X p hX hp.2.pos
  refine (Finset.sum_le_sum hrow).trans ?_
  have hsub : ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime, 4 / (p : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc P Q, 4 / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)
  refine hsub.trans ?_
  have heq : ∑ n ∈ Finset.Icc P Q, 4 / (n : ℝ) ^ 2
      = 4 * ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [heq]
  have htail := sum_inv_sq_tail_le hP Q
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  calc 4 * ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 ≤ 4 * (2 / (P : ℝ)) := by linarith
    _ = 8 / (P : ℝ) := by ring

/-- **STONE 2 — the `p²` row's mass collapses to `64/P²`.**

`lemma12_meansq_mr_consume` leaves `∑_{n≤N} ‖ramP2coeffMR n‖²/n²` in-statement; this is
its collapse.  Each summand of the coefficient has norm `≤ 2` (`ramP2_term_norm_le`), so
`‖coeff n‖/n ≤ ∑_{σ ↦ n} 2/(σ.1σ.2)`; `∑ a² ≤ (∑ a)²` and the fiberwise identity turn the
mass into `(∑_{σ ∈ ramP2domMR} 2/(σ.1σ.2))²`, which `ramP2_dom_sum_le` caps at `(8/P)²`. -/
theorem ramP2mass_le (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 64 / (P : ℝ) ^ 2 := by
  classical
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hNR : 2 * (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- the fiber map (the same `hmaps` as `ramP2corrMR_eq_spoly`)
  have hmaps : ∀ σ ∈ ramP2domMR N X P Q, σ.1 * σ.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    rw [ramP2domMR, Finset.mem_sigma] at hσ
    obtain ⟨-, h2⟩ := hσ
    rw [Finset.mem_filter, ramHonMR, Finset.mem_filter] at h2
    obtain ⟨⟨-, hlo, hhi⟩, -⟩ := h2
    rw [Finset.mem_Icc]
    constructor
    · have h : (1 : ℝ) ≤ ((σ.1 * σ.2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    · have h : ((σ.1 * σ.2 : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; linarith
      exact_mod_cast h
  -- pointwise: `‖coeff n‖/n` below the fiber sum
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)
        ≤ ∑ σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
            2 / ((σ.1 * σ.2 : ℕ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have heq : (∑ σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n),
          2 / ((σ.1 * σ.2 : ℕ) : ℝ))
        = (∑ _σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n), (2 : ℝ)) / (n : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [Finset.mem_filter] at hσ
      rw [hσ.2]
    rw [heq, div_le_div_iff_of_pos_right hn0, ramP2coeffMR]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ _ => ?_))
    exact ramP2_term_norm_le ha hb hc σ.1 σ.2
  -- the mass ≤ (domain sum)²
  have hfiber : (∑ n ∈ Finset.Icc 1 N,
        ∑ σ ∈ (ramP2domMR N X P Q).filter (fun σ => σ.1 * σ.2 = n), 2 / ((σ.1 * σ.2 : ℕ) : ℝ))
      = ∑ σ ∈ ramP2domMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hsum : (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ))
      ≤ ∑ σ ∈ ramP2domMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ) := by
    rw [← hfiber]; exact Finset.sum_le_sum hpt
  have hdomnn : (0 : ℝ) ≤ ∑ σ ∈ ramP2domMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun σ _ => by positivity)
  calc ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      = ∑ n ∈ Finset.Icc 1 N, (‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)) ^ 2 :=
        Finset.sum_congr rfl (fun n _ => (div_pow _ _ _).symm)
    _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ / (n : ℝ)) ^ 2 :=
        sum_sq_le_sq_sum (fun n _ => by positivity)
    _ ≤ (∑ σ ∈ ramP2domMR N X P Q, 2 / ((σ.1 * σ.2 : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => by positivity)) hsum 2
    _ ≤ (8 / (P : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hdomnn (ramP2_dom_sum_le N X P Q hX hP) 2
    _ = 64 / (P : ℝ) ^ 2 := by rw [div_pow]; norm_num

/-- The `1/P` form MR's row is stated in (`64/P² ≤ 64/P` for `P ≥ 1`). -/
theorem ramP2mass_le_inv_P (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 64 / (P : ℝ) := by
  refine (ramP2mass_le N X P Q hX hN hP a b c ha hb hc).trans ?_
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

/-- **STONE 2, exit — Lemma 12 at the MR range with the `p²` row COLLAPSED.**  The fully
numeric consumption form: the three rows are the main term, MR's `(T/X+1)/H` seam grade,
and the `p²` row at `512·(2T+20N)/P²`. -/
theorem lemma12_meansq_mr_final (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ) (hX : 1 ≤ X)
    (hN : 2 * X ≤ N) (hN2 : (N : ℝ) ≤ 2 * (X : ℝ)) (hHX : H ≤ (X : ℝ)) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m → a (p * m) = b m * c p)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (hsupp : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P Q n)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q, ∫ t in (-T)..T, ‖ramMain H N X P Q b c j t‖ ^ 2)
        + 4160 * (T / (X : ℝ) + 1) / H
        + 512 * (2 * T + 20 * (N : ℝ)) / (P : ℝ) ^ 2 := by
  refine (lemma12_meansq_mr_consume H hH N X P Q hX hN hN2 hHX hP a b c hcoef hb hc
    hasupp hsupp T hT).trans ?_
  have hmass := ramP2mass_le N X P Q hX hN hP a b c ha hb hc
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hfac : (0 : ℝ) ≤ 8 * (2 * T + 20 * (N : ℝ)) := by linarith
  have hstep := mul_le_mul_of_nonneg_left hmass hfac
  have hring : 8 * (2 * T + 20 * (N : ℝ)) * (64 / (P : ℝ) ^ 2)
      = 512 * (2 * T + 20 * (N : ℝ)) / (P : ℝ) ^ 2 := by ring
  rw [hring] at hstep
  linarith

end Salt.MR
