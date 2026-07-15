import Mathlib
import Salt.Chen.RosserChain

/-!
# C1b — The `fₙ` tail certification (BJS Lemma 8 lineage)

The truncated Rosser chains `Fchain N` / `fchain N` (C1a, `RosserChain.lean`)
differ from their untruncated limits by the tail `Σ_{n > N} fseq n s`.  This file
bounds that tail at the linear-sieve operating points, discharging the C0 ledger's
S1 cert budget (`≤ 4.3·10⁻⁴` at `s ≈ 4`).

## The mechanism (BJS Lemma 8, arXiv:2207.09452v6 eqn (18))

BJS prove a per-level geometric bound `fₙ(s) ≤ 2e²·cₙ^{n-1}·h(s)` with a uniform
ratio `cₙ = 0.9607 = H(2)/(2h(2))` (their `α = 0.96068`), where `h` is a
piecewise `e^{-s}`-shaped majorant.  We formalise the **same mechanism** with a
Lean-friendly **exponential majorant**

  `hbar s := exp(-2 - (6/5)·(max s 2 - 2))`

(flat `e⁻²` on `s ≤ 2`, geometric decay at rate `λ = 6/5` for `s ≥ 2`), and the
looser but fully certified ratio `ρ = 99/100`.  The crux is the functional
inequality `∫_{s-1}^∞ hbar ≤ ρ·s·hbar s` (`hbar_funcbound`), proved region by
region; the transition band `[2,3]` uses a 4-panel convexity-secant argument
(`analytic_lo_core`).  The per-level bound is then

  `fseq_le : fseq (n+1) s ≤ 2·e²·ρ^n·hbar s`      (`ρ = 99/100`)

for **all** `s`, by one induction.  Summing the geometric tail and instantiating
at the operating point gives the consumable tail bounds.

The looser `ρ = 99/100` (vs BJS's `0.9607`) costs only a larger truncation depth
`N`, which is free: the numeric endgame closes `ρ^N ≤ target` by 11 repeated
squarings (`pow99_2048`), never a giant `norm_num` power.

**FLOOR (honest flag).** The C0 ledger's S1 row cites `N = 23` (BJS's sharp
Table-2 `cₙ`).  This file reaches the same `4.3·10⁻⁴` budget at `N = 2048`
(`fseq_tail_le`), a floor forced by the looser certified ratio `ρ = 99/100` and
the crude `hbar s ≤ e⁻²` used at the operating point.  The `N = 23` sharpness
was **not** reached; recovering it needs BJS's per-level Table-2 `cₙ` (each a
one-integration bound in the `fseq_two_window` style), a compute-heavier
refinement left for a follow-up.  Downstream (C1c/C2) consumes only the tail
*value* being `≤ 4.3·10⁻⁴`, which holds at `N = 2048`, so the floor is
load-bearing as-is.
-/

namespace Salt.Chen

open MeasureTheory intervalIntegral Set

/-! ### The exponential majorant `hbar` -/

/-- The Lean-friendly majorant: flat `e⁻²` on `s ≤ 2`, geometric decay at rate
`λ = 6/5` for `s ≥ 2`.  Dominates `fₙ/(2e²ρⁿ)` (see `fseq_le`). -/
noncomputable def hbar (s : ℝ) : ℝ := Real.exp (-2 - (6/5) * (max s 2 - 2))

theorem hbar_pos (s : ℝ) : 0 < hbar s := Real.exp_pos _

theorem hbar_hi {s : ℝ} (hs : 2 ≤ s) : hbar s = Real.exp (-2 - (6/5) * (s - 2)) := by
  unfold hbar; rw [max_eq_left hs]

theorem hbar_lo {s : ℝ} (hs : s ≤ 2) : hbar s = Real.exp (-2) := by
  unfold hbar; rw [max_eq_right hs]; norm_num

theorem hbar_continuous : Continuous hbar := by
  unfold hbar
  exact Real.continuous_exp.comp <|
    (continuous_const.sub (continuous_const.mul
      ((continuous_id.max continuous_const).sub continuous_const)))

theorem hbar_antitone : Antitone hbar := by
  intro a b hab
  unfold hbar
  exact Real.exp_le_exp.mpr (by nlinarith [max_le_max hab (le_refl (2:ℝ))])

/-! ### Numeric `exp` upper bounds at the `[2,3]` grid points

Rational upper bounds on `exp` of `3/10, 3/5, 9/10, 6/5`, obtained from the
Taylor remainder (`Real.exp_bound`); `exp (6/5)` is `exp (3/5)²`. -/

theorem exp_310_le : Real.exp (3/10) ≤ 1.35 := by
  have h := Real.exp_bound (x := 3/10) (by norm_num) (n := 5) (by norm_num)
  rw [abs_le] at h; have := h.2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num at this ⊢; nlinarith [this]

theorem exp_35_le : Real.exp (3/5) ≤ 1.8225 := by
  have h := Real.exp_bound (x := 3/5) (by norm_num) (n := 6) (by norm_num)
  rw [abs_le] at h; have := h.2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num at this ⊢; nlinarith [this]

theorem exp_910_le : Real.exp (9/10) ≤ 2.46 := by
  have h := Real.exp_bound (x := 9/10) (by norm_num) (n := 7) (by norm_num)
  rw [abs_le] at h; have := h.2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num at this ⊢; nlinarith [this]

theorem exp_65_le : Real.exp (6/5) ≤ 3.3216 := by
  have he : Real.exp (6/5) = Real.exp (3/5) * Real.exp (3/5) := by
    rw [← Real.exp_add]; norm_num
  rw [he]; nlinarith [exp_35_le, Real.exp_pos (3/5)]

/-! ### The convexity-secant panel lemma and the transition-band inequality -/

/-- Convexity of `exp` gives a secant (linear) upper bound on `exp((6/5)(s-2))`
over a panel `[a,b]`, from rational upper bounds `Ua, Ub` at the endpoints.
Stated in cleared (division-free) form for downstream `nlinarith`. -/
theorem secant_piece {a b Ua Ub s : ℝ} (hab : a < b) (ha : a ≤ s) (hb : s ≤ b)
    (hUa : Real.exp ((6 / 5) * (a - 2)) ≤ Ua) (hUb : Real.exp ((6 / 5) * (b - 2)) ≤ Ub) :
    (b - a) * Real.exp ((6 / 5) * (s - 2)) ≤ Ua * (b - s) + Ub * (s - a) := by
  have hba : 0 < b - a := by linarith
  have hbane : b - a ≠ 0 := ne_of_gt hba
  set p := (b - s)/(b - a) with hp
  set q := (s - a)/(b - a) with hq
  have hp0 : 0 ≤ p := div_nonneg (by linarith) hba.le
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hba.le
  have hpq : p + q = 1 := by rw [hp, hq]; field_simp; ring
  have hcombo : (6/5)*(s-2) = p * ((6/5)*(a-2)) + q * ((6/5)*(b-2)) := by
    rw [hp, hq]; field_simp; ring
  have hsec := convexOn_exp.2 (mem_univ ((6/5)*(a-2))) (mem_univ ((6/5)*(b-2))) hp0 hq0 hpq
  simp only [smul_eq_mul] at hsec
  rw [← hcombo] at hsec
  have h2 : Real.exp ((6/5)*(s-2)) ≤ p * Ua + q * Ub := by
    refine hsec.trans ?_
    apply add_le_add <;>
      [exact mul_le_mul_of_nonneg_left hUa hp0; exact mul_le_mul_of_nonneg_left hUb hq0]
  have hmul := mul_le_mul_of_nonneg_left h2 hba.le
  rw [hp, hq] at hmul
  calc (b-a) * Real.exp ((6/5)*(s-2))
      ≤ (b-a) * ((b-s)/(b-a) * Ua + (s-a)/(b-a) * Ub) := hmul
    _ = Ua*(b-s) + Ub*(s-a) := by field_simp

/-- The transition-band functional inequality (BJS Lemma 8, `s ∈ [2,3]`):
`(23/6 - s)·exp((6/5)(s-2)) ≤ (99/100)·s`.  Four convexity panels
`[2,9/4],[9/4,5/2],[5/2,11/4],[11/4,3]`; the third (tightest) panel carries a
`sq_nonneg` certificate. -/
theorem analytic_lo_core : ∀ s, 2 ≤ s → s ≤ 3 →
    (23/6 - s) * Real.exp ((6/5)*(s-2)) ≤ (99/100) * s := by
  intro s h2 h3
  have hfac : 0 ≤ 23/6 - s := by linarith
  have hexp : 0 < Real.exp ((6/5)*(s-2)) := Real.exp_pos _
  rcases le_total s (9/4) with h | h
  · have hUa : Real.exp ((6/5)*((2:ℝ)-2)) ≤ 1 := by
      rw [show (6/5)*((2:ℝ)-2) = 0 by norm_num, Real.exp_zero]
    have hUb : Real.exp ((6/5)*((9/4:ℝ)-2)) ≤ 1.35 := by
      rw [show (6/5)*((9/4:ℝ)-2) = 3/10 by norm_num]; exact exp_310_le
    have hs := secant_piece (a:=2) (b:=9/4) (by norm_num) h2 h hUa hUb
    nlinarith [hs, hfac, hexp, h2, h]
  rcases le_total s (5/2) with h' | h'
  · have hUa : Real.exp ((6/5)*((9/4:ℝ)-2)) ≤ 1.35 := by
      rw [show (6/5)*((9/4:ℝ)-2) = 3/10 by norm_num]; exact exp_310_le
    have hUb : Real.exp ((6/5)*((5/2:ℝ)-2)) ≤ 1.8225 := by
      rw [show (6/5)*((5/2:ℝ)-2) = 3/5 by norm_num]; exact exp_35_le
    have hs := secant_piece (a:=9/4) (b:=5/2) (by norm_num) h h' hUa hUb
    nlinarith [hs, hfac, hexp, h, h']
  rcases le_total s (11/4) with h'' | h''
  · have hUa : Real.exp ((6/5)*((5/2:ℝ)-2)) ≤ 1.8225 := by
      rw [show (6/5)*((5/2:ℝ)-2) = 3/5 by norm_num]; exact exp_35_le
    have hUb : Real.exp ((6/5)*((11/4:ℝ)-2)) ≤ 2.46 := by
      rw [show (6/5)*((11/4:ℝ)-2) = 9/10 by norm_num]; exact exp_910_le
    have hs := secant_piece (a:=5/2) (b:=11/4) (by norm_num) h' h'' hUa hUb
    nlinarith [mul_le_mul_of_nonneg_left hs hfac, hexp, sq_nonneg (408*s - 1067)]
  · have hUa : Real.exp ((6/5)*((11/4:ℝ)-2)) ≤ 2.46 := by
      rw [show (6/5)*((11/4:ℝ)-2) = 9/10 by norm_num]; exact exp_910_le
    have hUb : Real.exp ((6/5)*((3:ℝ)-2)) ≤ 3.3216 := by
      rw [show (6/5)*((3:ℝ)-2) = 6/5 by norm_num]; exact exp_65_le
    have hs := secant_piece (a:=11/4) (b:=3) (by norm_num) h'' h3 hUa hUb
    nlinarith [hs, hfac, hexp, h'', h3]

/-- The tail-region functional inequality (`s ≥ 3`): `(5/6)·hbar(s-1) ≤
(99/100)·s·hbar s`.  Uses `hbar(s-1) = exp(6/5)·hbar s` and `exp(6/5) ≤ 3.3216`. -/
theorem analytic_hi : ∀ s, 3 ≤ s → (5 / 6) * hbar (s - 1) ≤ (99 / 100) * s * hbar s := by
  intro s hs
  have hs1 : (2 : ℝ) ≤ s - 1 := by linarith
  have hs2 : (2 : ℝ) ≤ s := by linarith
  have hrel : hbar (s - 1) = Real.exp (6 / 5) * hbar s := by
    rw [hbar_hi hs1, hbar_hi hs2, ← Real.exp_add]; congr 1; ring
  rw [hrel]
  have hpos : 0 < hbar s := hbar_pos s
  have hcoef : (5 / 6) * Real.exp (6 / 5) ≤ (99 / 100) * s := by nlinarith [exp_65_le, hs]
  nlinarith [mul_le_mul_of_nonneg_right hcoef hpos.le, hpos]

/-! ### Bounding the finite majorant integral by the closed-form tail

`Ahbar a = ∫_a^∞ hbar` in closed form; the recursion needs
`∫_a^c hbar ≤ Ahbar a` for arbitrary upper limit `c` (`hbar ≥ 0`).  Realised
through the smooth antiderivative of the decay branch (`hasDerivAt_Gexp`), split
at the junction `s = 2` for the crossing case (`intbound_cross`). -/

/-- `x ↦ -(5/6)·exp(-2 - (6/5)(x-2))` is a primitive of the decay-branch of
`hbar` (which equals `hbar` for `x ≥ 2`). -/
theorem hasDerivAt_Gexp (u : ℝ) :
    HasDerivAt (fun x => -(5 / 6) * Real.exp (-2 - (6 / 5) * (x - 2)))
      (Real.exp (-2 - (6 / 5) * (u - 2))) u := by
  have h1 : HasDerivAt (fun x : ℝ => -2 - (6 / 5) * (x - 2)) (-(6 / 5)) u := by
    simpa using ((((hasDerivAt_id u).sub_const 2).const_mul (6 / 5)).const_sub (-2 : ℝ))
  have h2 : HasDerivAt (fun x => -(5 / 6) * Real.exp (-2 - (6 / 5) * (x - 2)))
      (-(5 / 6) * (Real.exp (-2 - (6 / 5) * (u - 2)) * -(6 / 5))) u := (h1.exp).const_mul (-(5 / 6))
  have heq : (-(5 / 6) * (Real.exp (-2 - (6 / 5) * (u - 2)) * -(6 / 5)))
      = Real.exp (-2 - (6 / 5) * (u - 2)) := by ring
  rwa [heq] at h2

/-- For `a ≥ 2` (fully inside the decay branch), `∫_a^c hbar ≤ (5/6)·hbar a`. -/
theorem intbound_hi (a c : ℝ) (ha : 2 ≤ a) : (∫ u in a..c, hbar u) ≤ (5 / 6) * hbar a := by
  rcases le_total a c with hac | hac
  · have hcongr : (∫ u in a..c, hbar u) = ∫ u in a..c, Real.exp (-2 - (6 / 5) * (u - 2)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hac] at hu
      exact hbar_hi (le_trans ha hu.1)
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_Gexp u)
        ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _), hbar_hi ha]
    nlinarith [Real.exp_pos (-2 - (6 / 5) * (c - 2))]
  · rw [intervalIntegral.integral_symm]
    have h1 : 0 ≤ ∫ u in c..a, hbar u :=
      intervalIntegral.integral_nonneg hac (fun u _ => (hbar_pos u).le)
    have h2 : 0 < hbar a := hbar_pos a
    linarith

/-- For `a ≤ 2` (crossing the junction), `∫_a^c hbar ≤ exp(-2)·(17/6 - a)`. -/
theorem intbound_cross (a c : ℝ) (ha2 : a ≤ 2) :
    (∫ u in a..c, hbar u) ≤ Real.exp (-2) * (17 / 6 - a) := by
  have hsplit : (∫ u in a..c, hbar u)
      = (∫ u in a..(2 : ℝ), hbar u) + ∫ u in (2 : ℝ)..c, hbar u := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hbar_continuous.intervalIntegrable _ _)
      (hbar_continuous.intervalIntegrable _ _)]
  rw [hsplit]
  have hflat : (∫ u in a..(2 : ℝ), hbar u) = Real.exp (-2) * (2 - a) := by
    have hcongr : (∫ u in a..(2 : ℝ), hbar u) = ∫ _u in a..(2 : ℝ), Real.exp (-2) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ha2] at hu
      exact hbar_lo hu.2
    rw [hcongr, intervalIntegral.integral_const]; simp; ring
  rw [hflat]
  have hupper : (∫ u in (2 : ℝ)..c, hbar u) ≤ (5 / 6) * hbar 2 := intbound_hi 2 c le_rfl
  rw [hbar_lo le_rfl] at hupper
  nlinarith [hupper, Real.exp_pos (-2 : ℝ)]

/-- **The functional inequality** (BJS Lemma 8 crux): the majorant integral from
`s-1` is bounded by `(99/100)·s·hbar s`, for `s ≥ 2` and any upper limit `c`.
This is exactly what one induction step of `fseq_le` consumes. -/
theorem hbar_funcbound (s c : ℝ) (hs : 2 ≤ s) :
    (∫ u in (s - 1)..c, hbar u) ≤ (99 / 100) * s * hbar s := by
  rcases le_total s 3 with h3 | h3
  · -- transition band s ∈ [2,3]: s-1 ∈ [1,2], crossing bound + analytic_lo_core
    have hcross := intbound_cross (s - 1) c (by linarith)
    have hcore := analytic_lo_core s hs h3
    have hident : Real.exp ((6 / 5) * (s - 2)) * hbar s = Real.exp (-2) := by
      rw [hbar_hi hs, ← Real.exp_add]; congr 1; ring
    have hmul := mul_le_mul_of_nonneg_right hcore (hbar_pos s).le
    rw [mul_assoc, hident] at hmul
    calc (∫ u in (s - 1)..c, hbar u) ≤ Real.exp (-2) * (17 / 6 - (s - 1)) := hcross
      _ = (23 / 6 - s) * Real.exp (-2) := by ring
      _ ≤ (99 / 100) * s * hbar s := hmul
  · -- tail region s ≥ 3: s-1 ≥ 2, decay bound + analytic_hi
    have hs1 : (2 : ℝ) ≤ s - 1 := by linarith
    calc (∫ u in (s - 1)..c, hbar u) ≤ (5 / 6) * hbar (s - 1) := intbound_hi (s - 1) c hs1
      _ ≤ (99 / 100) * s * hbar s := analytic_hi s h3

/-! ### The per-level geometric bound `fseq (n+1) s ≤ 2·e²·(99/100)ⁿ·hbar s` -/

/-- Base case: `f₁(s) ≤ 2·e²·hbar s` for all `s`.  Tight at `s = 1`
(`f₁(1) = 2 = 2e²·e⁻²`). -/
theorem fseq_one_le (s : ℝ) : fseq 1 s ≤ 2 * Real.exp 2 * hbar s := by
  rw [fseq_one_eq]
  split_ifs with h
  · obtain ⟨h1, h3⟩ := h
    have hs0 : (0 : ℝ) < s := by linarith
    rcases le_total s 2 with h2 | h2
    · rw [hbar_lo h2, show (2 : ℝ) * Real.exp 2 * Real.exp (-2) = 2 by
        rw [mul_assoc, ← Real.exp_add]; norm_num, div_le_iff₀ hs0]
      linarith
    · rw [hbar_hi h2]
      have hmono : Real.exp (-16 / 5) ≤ Real.exp (-2 - (6 / 5) * (s - 2)) :=
        Real.exp_le_exp.mpr (by nlinarith [h3])
      have hval : (2 : ℝ) * Real.exp 2 * Real.exp (-16 / 5) = 2 * Real.exp (-6 / 5) := by
        rw [mul_assoc, ← Real.exp_add]; norm_num
      have hquarter : (1 : ℝ) / 4 ≤ Real.exp (-6 / 5) := by
        have hprod : Real.exp (6 / 5) * Real.exp (-6 / 5) = 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [hprod, exp_65_le, Real.exp_pos (-6 / 5 : ℝ)]
      have hlow : (1 : ℝ) / 2 ≤ 2 * Real.exp 2 * Real.exp (-2 - (6 / 5) * (s - 2)) := by
        have h2pos : (0 : ℝ) ≤ 2 * Real.exp 2 := by positivity
        calc (1 : ℝ) / 2 = 2 * (1 / 4) := by norm_num
          _ ≤ 2 * Real.exp (-6 / 5) := by linarith [hquarter]
          _ = 2 * Real.exp 2 * Real.exp (-16 / 5) := hval.symm
          _ ≤ 2 * Real.exp 2 * Real.exp (-2 - (6 / 5) * (s - 2)) :=
              mul_le_mul_of_nonneg_left hmono h2pos
      rw [div_le_iff₀ hs0]; nlinarith [hlow, h3]
  · exact mul_nonneg (by positivity) (hbar_pos s).le

/-- Odd-flattening functional bound: `(5/6)·e⁻² = ∫₂^∞ hbar ≤ (99/100)·s·hbar s`
for `s ∈ [1,3]`.  The flat branch (17) integrates from `3`, i.e. `∫₂^∞` of the
majorant; on `[2,3]` it reduces to `analytic_lo_core` via `5/6 ≤ 23/6 - s`. -/
theorem oddflat_bound (s : ℝ) (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    (5 / 6) * Real.exp (-2) ≤ (99 / 100) * s * hbar s := by
  rcases le_total s 2 with h2 | h2
  · rw [hbar_lo h2]; nlinarith [Real.exp_pos (-2 : ℝ), h1]
  · have hcore := analytic_lo_core s h2 h3
    have hident : Real.exp ((6 / 5) * (s - 2)) * hbar s = Real.exp (-2) := by
      rw [hbar_hi h2, ← Real.exp_add]; congr 1; ring
    have hmul := mul_le_mul_of_nonneg_right hcore (hbar_pos s).le
    rw [mul_assoc, hident] at hmul
    have hle : (5 / 6) * Real.exp (-2) ≤ (23 / 6 - s) * Real.exp (-2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    linarith [hmul, hle]

/-- **The per-level geometric bound** (BJS Lemma 8 / eqn (18) at `α = 99/100`):
`fₙ₊₁(s) ≤ 2·e²·(99/100)ⁿ·hbar s` for **all** `s`, by one induction on `n`.
The induction step reduces to the functional inequality `hbar_funcbound` (window
cases, even and odd-tail) and `oddflat_bound` (the (17) flattening); the support
and below-window branches are the junk-zero of `fseq`. -/
theorem fseq_le : ∀ (n : ℕ) (s : ℝ),
    fseq (n + 1) s ≤ 2 * Real.exp 2 * (99 / 100) ^ n * hbar s := by
  intro n
  induction n with
  | zero => intro s; simpa using fseq_one_le s
  | succ m ih =>
    intro s
    have hKnn : (0 : ℝ) ≤ 2 * Real.exp 2 * (99 / 100) ^ m := by positivity
    have hRHSnn : (0 : ℝ) ≤ 2 * Real.exp 2 * (99 / 100) ^ (m + 1) * hbar s :=
      mul_nonneg (by positivity) (hbar_pos s).le
    have windowbd : ∀ (lo : ℝ), 2 ≤ lo → lo ≤ (m : ℝ) + 4 →
        (∫ t in lo..((m : ℝ) + 1 + 3), fseq (m + 1) (t - 1))
          ≤ (2 * Real.exp 2 * (99 / 100) ^ m) * ((99 / 100) * lo * hbar lo) := by
      intro lo hlo hlo2
      have hshift : (∫ t in lo..((m : ℝ) + 1 + 3), fseq (m + 1) (t - 1))
          = ∫ u in (lo - 1)..((m : ℝ) + 3), fseq (m + 1) u := by
        rw [integral_comp_sub_right (fun u => fseq (m + 1) u) 1]; congr 1; ring
      rw [hshift]
      have hab : lo - 1 ≤ (m : ℝ) + 3 := by linarith
      have hmono : (∫ u in (lo - 1)..((m : ℝ) + 3), fseq (m + 1) u)
          ≤ (2 * Real.exp 2 * (99 / 100) ^ m) * ∫ u in (lo - 1)..((m : ℝ) + 3), hbar u := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hab (fseq_intervalIntegrable (m + 1) _ _)
          ((continuous_const.mul hbar_continuous).intervalIntegrable _ _) (fun u _ => ih u)
      exact hmono.trans (mul_le_mul_of_nonneg_left (hbar_funcbound lo ((m : ℝ) + 3) hlo) hKnn)
    have flatbd :
        (∫ t in (3 : ℝ)..((m : ℝ) + 1 + 3), fseq (m + 1) (t - 1))
          ≤ (2 * Real.exp 2 * (99 / 100) ^ m) * ((5 / 6) * Real.exp (-2)) := by
      have hshift : (∫ t in (3 : ℝ)..((m : ℝ) + 1 + 3), fseq (m + 1) (t - 1))
          = ∫ u in (2 : ℝ)..((m : ℝ) + 3), fseq (m + 1) u := by
        rw [integral_comp_sub_right (fun u => fseq (m + 1) u) 1]; congr 1 <;> ring
      rw [hshift]
      have hab : (2 : ℝ) ≤ (m : ℝ) + 3 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
      have hmono : (∫ u in (2 : ℝ)..((m : ℝ) + 3), fseq (m + 1) u)
          ≤ (2 * Real.exp 2 * (99 / 100) ^ m) * ∫ u in (2 : ℝ)..((m : ℝ) + 3), hbar u := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hab (fseq_intervalIntegrable (m + 1) _ _)
          ((continuous_const.mul hbar_continuous).intervalIntegrable _ _) (fun u _ => ih u)
      have hib := intbound_hi 2 ((m : ℝ) + 3) le_rfl
      rw [hbar_lo (le_refl (2 : ℝ))] at hib
      exact hmono.trans (mul_le_mul_of_nonneg_left hib hKnn)
    by_cases hsupp : (m : ℝ) + 4 ≤ s
    · rw [fseq_eq_zero_of_ge (m + 1 + 1) s (by push_cast; linarith)]; exact hRHSnn
    · replace hsupp := not_le.mp hsupp
      by_cases hev : Even (m + 1 + 1)
      · rcases le_or_gt 2 s with hs2 | hs2
        · rw [fseq_even_window hev hs2]
          have hwb := windowbd s hs2 (le_of_lt hsupp)
          push_cast at hwb ⊢
          have hs0 : (0 : ℝ) < s := by linarith
          have hsne : s ≠ 0 := hs0.ne'
          refine (mul_le_mul_of_nonneg_left hwb (by positivity : (0 : ℝ) ≤ 1 / s)).trans
            (le_of_eq ?_)
          field_simp
          ring
        · rw [fseq_even_below hev hs2]; exact hRHSnn
      · rcases le_or_gt 3 s with hs3 | hs3
        · rw [fseq_odd_tail_window (by omega) hev hs3]
          have hwb := windowbd s (by linarith) (le_of_lt hsupp)
          push_cast at hwb ⊢
          have hs0 : (0 : ℝ) < s := by linarith
          have hsne : s ≠ 0 := hs0.ne'
          refine (mul_le_mul_of_nonneg_left hwb (by positivity : (0 : ℝ) ≤ 1 / s)).trans
            (le_of_eq ?_)
          field_simp
          ring
        · rcases le_or_gt 1 s with hs1 | hs1
          · rw [fseq_odd_flat_window (by omega) hev hs1 hs3]
            have hob := oddflat_bound s hs1 (le_of_lt hs3)
            have hchain := flatbd.trans (mul_le_mul_of_nonneg_left hob hKnn)
            push_cast at hchain ⊢
            have hs0 : (0 : ℝ) < s := by linarith
            have hsne : s ≠ 0 := hs0.ne'
            refine (mul_le_mul_of_nonneg_left hchain (by positivity : (0 : ℝ) ≤ 1 / s)).trans
              (le_of_eq ?_)
            field_simp
            ring
          · rw [fseq_odd_below (by omega) hev hs1]; exact hRHSnn

/-! ### The geometric tail sum and the numeric endgame -/

/-- Finite geometric tail: `Σ_{k ∈ [N,M)} (99/100)^k ≤ 100·(99/100)^N`. -/
theorem geom_tail (N M : ℕ) :
    (∑ k ∈ Finset.Ico N M, (99 / 100 : ℝ) ^ k) ≤ 100 * (99 / 100) ^ N := by
  rcases le_or_gt N M with hNM | hNM
  · rw [geom_sum_Ico (x := (99 / 100 : ℝ)) (by norm_num) hNM]
    have e1 : ((99 / 100 : ℝ) ^ M - (99 / 100) ^ N) / ((99 / 100) - 1)
        = 100 * ((99 / 100) ^ N - (99 / 100) ^ M) := by
      rw [show ((99 / 100 : ℝ) - 1) = -(1 / 100) by norm_num]; field_simp; ring
    rw [e1]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 99 / 100 by norm_num) M]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; positivity

/-- **The finite-truncation tail sum bound** (the C1b consumable): for any window
`(N, M]`, `Σ_{n ∈ (N,M]} fₙ(s) ≤ 2e²·hbar s·100·(99/100)^N`.  Obtained from the
per-level bound `fseq_le`, reindexed onto a geometric tail. -/
theorem fseq_tail_sum_le (N M : ℕ) (s : ℝ) :
    (∑ n ∈ Finset.Ioc N M, fseq n s) ≤ 2 * Real.exp 2 * hbar s * (100 * (99 / 100) ^ N) := by
  have hpre : (0 : ℝ) ≤ 2 * Real.exp 2 * hbar s := by have := hbar_pos s; positivity
  have hterm : ∀ n ∈ Finset.Ioc N M,
      fseq n s ≤ (2 * Real.exp 2 * hbar s) * (99 / 100) ^ (n - 1) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp only [Finset.mem_Ioc] at hn; omega⟩
    simp only [Nat.add_sub_cancel]
    exact (fseq_le k s).trans (le_of_eq (by ring))
  have hreindex : (∑ n ∈ Finset.Ioc N M, (99 / 100 : ℝ) ^ (n - 1))
      = ∑ k ∈ Finset.Ico N M, (99 / 100 : ℝ) ^ k := by
    apply Finset.sum_nbij' (fun n => n - 1) (fun k => k + 1)
    · intro n hn; simp only [Finset.mem_Ioc] at hn; simp only [Finset.mem_Ico]; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk; simp only [Finset.mem_Ioc]; omega
    · intro n hn; simp only [Finset.mem_Ioc] at hn; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk; omega
    · intro n _; rfl
  calc (∑ n ∈ Finset.Ioc N M, fseq n s)
      ≤ ∑ n ∈ Finset.Ioc N M, (2 * Real.exp 2 * hbar s) * (99 / 100) ^ (n - 1) :=
        Finset.sum_le_sum hterm
    _ = (2 * Real.exp 2 * hbar s) * ∑ n ∈ Finset.Ioc N M, (99 / 100) ^ (n - 1) := by
        rw [← Finset.mul_sum]
    _ = (2 * Real.exp 2 * hbar s) * ∑ k ∈ Finset.Ico N M, (99 / 100) ^ k := by rw [hreindex]
    _ ≤ (2 * Real.exp 2 * hbar s) * (100 * (99 / 100) ^ N) :=
        mul_le_mul_of_nonneg_left (geom_tail N M) hpre

/-- `(99/100)^2048 ≤ 10⁻⁸`, by 11 repeated squarings (each a `norm_num` on
4-digit rationals — never a giant power). -/
theorem pow99_2048 : (99 / 100 : ℝ) ^ 2048 ≤ 1 / 100000000 := by
  have step : ∀ (k : ℕ) (c : ℝ), (99 / 100 : ℝ) ^ k ≤ c → (99 / 100 : ℝ) ^ (k * 2) ≤ c ^ 2 := by
    intro k c h; rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) h 2
  have b2    : (99 / 100 : ℝ) ^ 2 ≤ 0.9801 := by norm_num
  have b4    : (99 / 100 : ℝ) ^ 4 ≤ 0.9606 := le_trans (step 2 _ b2) (by norm_num)
  have b8    : (99 / 100 : ℝ) ^ 8 ≤ 0.9228 := le_trans (step 4 _ b4) (by norm_num)
  have b16   : (99 / 100 : ℝ) ^ 16 ≤ 0.8516 := le_trans (step 8 _ b8) (by norm_num)
  have b32   : (99 / 100 : ℝ) ^ 32 ≤ 0.7253 := le_trans (step 16 _ b16) (by norm_num)
  have b64   : (99 / 100 : ℝ) ^ 64 ≤ 0.5261 := le_trans (step 32 _ b32) (by norm_num)
  have b128  : (99 / 100 : ℝ) ^ 128 ≤ 0.2768 := le_trans (step 64 _ b64) (by norm_num)
  have b256  : (99 / 100 : ℝ) ^ 256 ≤ 0.0767 := le_trans (step 128 _ b128) (by norm_num)
  have b512  : (99 / 100 : ℝ) ^ 512 ≤ 0.0059 := le_trans (step 256 _ b256) (by norm_num)
  have b1024 : (99 / 100 : ℝ) ^ 1024 ≤ 0.0000349 := le_trans (step 512 _ b512) (by norm_num)
  exact le_trans (step 1024 _ b1024) (by norm_num)

/-- **The S1 cert budget** (BJS/C0 ledger): at any operating point `s ≥ 4/3`
(covering the lower side `s ≈ 4` and the uppers `s ∈ [4/3,3]`), truncating at
depth `N ≥ 2048` bounds the tail below `4.3·10⁻⁴`.  The uniform `hbar s ≤ e⁻²`
for `s ≥ 4/3` collapses `2e²·hbar s ≤ 2`, so the tail is `≤ 200·(99/100)^N`. -/
theorem fseq_tail_le (N M : ℕ) (hN : 2048 ≤ N) (s : ℝ) (hs : 4 / 3 ≤ s) :
    (∑ n ∈ Finset.Ioc N M, fseq n s) ≤ 43 / 100000 := by
  refine (fseq_tail_sum_le N M s).trans ?_
  have hhbar : hbar s ≤ Real.exp (-2) := by
    have h1 : hbar s ≤ hbar (4 / 3) := hbar_antitone hs
    rwa [hbar_lo (by norm_num : (4 : ℝ) / 3 ≤ 2)] at h1
  have h2exp : 2 * Real.exp 2 * hbar s ≤ 2 := by
    have hid : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
    have hfac : 2 * Real.exp 2 * Real.exp (-2) = 2 := by rw [mul_assoc, hid, mul_one]
    have hmul2 := mul_le_mul_of_nonneg_left hhbar (by positivity : (0 : ℝ) ≤ 2 * Real.exp 2)
    linarith [hmul2, hfac]
  have hρN : (99 / 100 : ℝ) ^ N ≤ (99 / 100) ^ 2048 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  calc 2 * Real.exp 2 * hbar s * (100 * (99 / 100) ^ N)
      ≤ 2 * (100 * (99 / 100) ^ 2048) := by
        apply mul_le_mul h2exp (mul_le_mul_of_nonneg_left hρN (by norm_num))
          (by positivity) (by norm_num)
    _ ≤ 2 * (100 * (1 / 100000000)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left pow99_2048 (by norm_num)) (by norm_num)
    _ ≤ 43 / 100000 := by norm_num

/-! ### The composed consumables for C1c: chain closeness

The truncated chains are Cauchy in `N` with a rate that C1c's Theorem-6
application cites directly: at `s ≥ 4/3`, all truncations past depth `2048`
agree to within the S1 budget. -/

/-- `|f_N(s) − f_M(s)| ≤ 2e²·hbar s·100·(99/100)^N` for `N ≤ M`: the `fchain`
truncation tail (the even-`n` partial sum, catch #24 parity). -/
theorem fchain_close (N M : ℕ) (hNM : N ≤ M) (s : ℝ) :
    |fchain N s - fchain M s| ≤ 2 * Real.exp 2 * hbar s * (100 * (99 / 100) ^ N) := by
  set t := (Finset.range (M + 1)).filter (fun n => Even n) with ht
  set u := (Finset.range (N + 1)).filter (fun n => Even n) with hu
  have hsub : u ⊆ t := Finset.filter_subset_filter _ (Finset.range_mono (by omega))
  have hdiff : fchain N s - fchain M s = ∑ n ∈ t \ u, fseq n s := by
    rw [Finset.sum_sdiff_eq_sub hsub]; simp only [fchain, ht, hu]; ring
  rw [hdiff, abs_of_nonneg (Finset.sum_nonneg (fun n _ => fseq_nonneg n s))]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => fseq_nonneg n s))
    (fseq_tail_sum_le N M s)
  intro n hn
  rw [Finset.mem_sdiff] at hn
  obtain ⟨hnt, hnu⟩ := hn
  rw [ht, Finset.mem_filter, Finset.mem_range] at hnt
  rw [hu, Finset.mem_filter, Finset.mem_range] at hnu
  obtain ⟨hnM, hEven⟩ := hnt
  rw [Finset.mem_Ioc]
  refine ⟨?_, by omega⟩
  rcases Nat.lt_or_ge n (N + 1) with h | h
  · exact absurd ⟨h, hEven⟩ hnu
  · omega

/-- `|F_N(s) − F_M(s)| ≤ 2e²·hbar s·100·(99/100)^N` for `N ≤ M`: the `Fchain`
truncation tail (the odd-`n` partial sum). -/
theorem Fchain_close (N M : ℕ) (hNM : N ≤ M) (s : ℝ) :
    |Fchain N s - Fchain M s| ≤ 2 * Real.exp 2 * hbar s * (100 * (99 / 100) ^ N) := by
  set t := (Finset.range (M + 1)).filter (fun n => Odd n) with ht
  set u := (Finset.range (N + 1)).filter (fun n => Odd n) with hu
  have hsub : u ⊆ t := Finset.filter_subset_filter _ (Finset.range_mono (by omega))
  have hdiff : Fchain N s - Fchain M s = -(∑ n ∈ t \ u, fseq n s) := by
    rw [Finset.sum_sdiff_eq_sub hsub]; simp only [Fchain, ht, hu]; ring
  rw [hdiff, abs_neg, abs_of_nonneg (Finset.sum_nonneg (fun n _ => fseq_nonneg n s))]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => fseq_nonneg n s))
    (fseq_tail_sum_le N M s)
  intro n hn
  rw [Finset.mem_sdiff] at hn
  obtain ⟨hnt, hnu⟩ := hn
  rw [ht, Finset.mem_filter, Finset.mem_range] at hnt
  rw [hu, Finset.mem_filter, Finset.mem_range] at hnu
  obtain ⟨hnM, hOdd⟩ := hnt
  rw [Finset.mem_Ioc]
  refine ⟨?_, by omega⟩
  rcases Nat.lt_or_ge n (N + 1) with h | h
  · exact absurd ⟨h, hOdd⟩ hnu
  · omega

end Salt.Chen
