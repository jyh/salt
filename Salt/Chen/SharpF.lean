/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.SharpH2
import Salt.Chen.FseqAntitone
import Salt.Chen.TnInduction

/-!
# E₁c-hf — the sharp `f`-side windowed comparison (the last analytic comparison of the Chen arc)

This file lands `hf_sharp_of_window` — the conditioned per-step `f`-slot of
`WindowedStepC.StepHypWPC` at the boundary-padded forcing `cfSharpB` — plus the wiring lemma
`vlow_le_of_guard` (VD1).  Where the `h`-side (`SharpH2`) ran the pushforward through the
kernel `Kh = -hBJS'` and integration-by-parts, `fseq` has **no clean derivative kernel**
(it is only piecewise-smooth, with a jump at its window edge), so that route is unavailable.

## The derivative-free engine

`abel_pushforward` (Part 0) is the `fseq`-side replacement for `SharpH2.layer_cake_pushforward`:
for an **antitone** nonnegative integrable weight `g`, nonnegative Stieltjes masses `m p` at
points `x p`, with the affine up-set mass control `Σ_{x p ≤ v} m p ≤ c·(v−a)+d`, it proves

  `Σ_p m p·g (x p) ≤ d·g a + c·∫_a^U g`

by peeling the `x`-minimizer (moving the lower reference) — pure Abel summation + Riemann lower
sums, no FTC / IBP / kernel.  `fseq n` is antitone on its parity window (AF1
`fseq_antitoneOn_odd/even`), which is exactly why the layer-cake route applies here (the parity
coupling `side' % 2 ≠ n % 2` keeps `fseq n` on that window).

## The cells (all sharing the one engine)

* `hf_cell_ge2` — side' = 2 (⇒ `S ≥ 2`, `n` odd, `n+1` even window) and side' = 1, `S ≥ 3`
  (`n` even, `n+1` odd-tail window): the main term is **EXACT** via the window equation
  `(1/S)∫_{S-1}^{n+2} fseq n = fseq (n+1) S`; the `(1+ε)`-excess and the `z`-edge boundary
  `ε·fseq n (S−1)` ride in `cfSharpB`.
* `hf_sharp_flat` — side' = 1, `S ∈ [1,3)` (`n` even, `n+1` odd-flat window, FIXED lower
  limit 3 ⇒ integral `∫_2^{n+2}`): window-relative mass at `D'^{1/3}` (`upset_mass_window_le`),
  closed with the `h4`-shape `Vlow ≤ (3(1+ε)/S)·W`.

## Defect budget (numeric self-check, `fseq` DDE, hi-precision)

`cfSharpB n ε = 20εe²(99/100)ⁿ` for `n ≥ 1`.  Achieved per-cell defect totals (in units of
`εe²(99/100)ⁿ hBJS S`, all `≤ 20`):

* `S ≥ 2` cells: main `(1+ε)`-excess `ε·fseq(n+1)(S) ≤ 2` + boundary
  `ε·fseq n (S−1) ≤ 8·(100/99) = 8.08` via `fseq_le` + `hbar_le_hBJS` + `hBJS_shift_le` (×4);
  total **10.08** (`8 ≤ 18·99/100 = 17.82` closes it; true sup 2.675 at (n,S)=(1,2)).
* flat cell: main excess `(2ε+ε²)·fseq(n+1)(S) ≤ 4.002` + boundary
  `ε·Vlow·fseq n(2) ≤ 6.066` (using `hbar 2 = e⁻²` ⇒ `fseq n(2) ≤ 2(99/100)ⁿ⁻¹`);
  total **10.07** (true sup 6.66 at (n,S)=(2,1)).

So `cfSharpB = 20` carries ≈ 2× cushion on the lemma path (≈ 2.5× vs the gate).
-/

open Finset MeasureTheory

namespace Salt.Chen

/-- **The derivative-free discrete Abel pushforward.**  For an antitone nonnegative integrable
weight `g` on `[a, U]`, nonnegative Stieltjes masses `m p` at points `x p ∈ [a, U]`, with the
affine up-set mass control `Σ_{x p ≤ v} m p ≤ c·(v − a) + d` (`c, d ≥ 0`), the weighted sum is
bounded by the boundary term plus the integral form:

  `Σ_p m p · g (x p) ≤ d · g a + c · ∫_a^U g`.

Proof by peeling the `x`-minimizer `p₀` (moving the lower reference to `x₀`), so no derivative
kernel / integration-by-parts is needed — only `g` antitone, `g ≥ 0`, and Riemann lower sums.
This is the `fseq`-side analogue of `SharpH2.layer_cake_pushforward` (which is hard-wired to the
kernel `Kh = -hBJS'`); `fseq` has no clean derivative, so this Abel route replaces the IBP one. -/
theorem abel_pushforward (g : ℝ → ℝ) (U c : ℝ) (hc : 0 ≤ c) (x m : ℕ → ℝ)
    (hgint : ∀ p q : ℝ, IntervalIntegrable g volume p q) :
    ∀ (T : Finset ℕ) (a d : ℝ), 0 ≤ d → a ≤ U →
      AntitoneOn g (Set.Icc a U) → (∀ v ∈ Set.Icc a U, 0 ≤ g v) →
      (∀ p ∈ T, 0 ≤ m p) →
      (∀ p ∈ T, x p ∈ Set.Icc a U) →
      (∀ v : ℝ, a ≤ v → (∑ p ∈ T.filter (fun p => x p ≤ v), m p) ≤ c * (v - a) + d) →
      (∑ p ∈ T, m p * g (x p)) ≤ d * g a + c * ∫ v in a..U, g v := by
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    intro a d hd haU hanti hgnn hmnn hxmem hmass
    rcases T.eq_empty_or_nonempty with hemp | hne
    · subst hemp
      simp only [Finset.sum_empty]
      have hga : 0 ≤ g a := hgnn a ⟨le_refl a, haU⟩
      have hint_nn : 0 ≤ ∫ v in a..U, g v :=
        intervalIntegral.integral_nonneg haU (fun v hv => hgnn v ⟨hv.1, hv.2⟩)
      positivity
    · obtain ⟨p₀, hp₀T, hp₀min⟩ := T.exists_min_image x hne
      set x₀ := x p₀ with hx₀
      set T' := T.erase p₀ with hT'
      have hT'sub : T' ⊂ T := Finset.erase_ssubset hp₀T
      have hx₀mem : x₀ ∈ Set.Icc a U := hxmem p₀ hp₀T
      have hax₀ : a ≤ x₀ := hx₀mem.1
      have hx₀U : x₀ ≤ U := hx₀mem.2
      have hm₀ : 0 ≤ m p₀ := hmnn p₀ hp₀T
      -- the mass at (or below) `x₀` is bounded by `c(x₀-a)+d`, so `m p₀ ≤` that
      have hmassx₀ : m p₀ ≤ c * (x₀ - a) + d := by
        have hle := hmass x₀ hax₀
        have hp₀f : p₀ ∈ T.filter (fun p => x p ≤ x₀) := Finset.mem_filter.mpr ⟨hp₀T, le_refl _⟩
        have hterm : m p₀ ≤ ∑ p ∈ T.filter (fun p => x p ≤ x₀), m p :=
          Finset.single_le_sum (f := m) (fun p hp => hmnn p (Finset.mem_filter.mp hp).1) hp₀f
        linarith
      set d' := c * (x₀ - a) + d - m p₀ with hd'
      have hd'nn : 0 ≤ d' := by rw [hd']; linarith [hmassx₀]
      -- mass control for `T'` referenced at `x₀`
      have hmass' : ∀ v : ℝ, x₀ ≤ v →
          (∑ p ∈ T'.filter (fun p => x p ≤ v), m p) ≤ c * (v - x₀) + d' := by
        intro v hv
        have hp₀fv : p₀ ∈ T.filter (fun p => x p ≤ v) :=
          Finset.mem_filter.mpr ⟨hp₀T, le_trans (le_refl x₀) hv⟩
        have herase : T'.filter (fun p => x p ≤ v) = (T.filter (fun p => x p ≤ v)).erase p₀ := by
          rw [hT', Finset.filter_erase]
        rw [herase, Finset.sum_erase_eq_sub hp₀fv]
        have hle := hmass v (le_trans hax₀ hv)
        rw [hd']; linarith [hle]
      -- IH on `T'`
      have hih := ih T' hT'sub x₀ d' hd'nn hx₀U
        (hanti.mono (Set.Icc_subset_Icc hax₀ (le_refl U)))
        (fun v hv => hgnn v ⟨le_trans hax₀ hv.1, hv.2⟩)
        (fun p hp => hmnn p (Finset.mem_of_mem_erase hp))
        (fun p hp => ⟨hp₀min p (Finset.mem_of_mem_erase hp),
          (hxmem p (Finset.mem_of_mem_erase hp)).2⟩)
        hmass'
      -- combine: Σ_T = m p₀ · g x₀ + Σ_T'
      have hsum : (∑ p ∈ T, m p * g (x p)) = m p₀ * g x₀ + ∑ p ∈ T', m p * g (x p) := by
        rw [hT', ← Finset.add_sum_erase T (fun p => m p * g (x p)) hp₀T]
      -- g x₀ ≤ g a
      have hgx₀a : g x₀ ≤ g a := hanti ⟨le_refl a, haU⟩ hx₀mem hax₀
      -- (x₀ - a) g x₀ ≤ ∫_a^{x₀} g
      have hRiemann : (x₀ - a) * g x₀ ≤ ∫ v in a..x₀, g v := by
        have hconst : (∫ v in a..x₀, (g x₀ : ℝ)) = (x₀ - a) * g x₀ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [← hconst]
        apply intervalIntegral.integral_mono_on hax₀ (intervalIntegrable_const) (hgint a x₀)
        intro v hv
        exact hanti ⟨hv.1, le_trans hv.2 hx₀U⟩ ⟨hax₀, hx₀U⟩ hv.2
      -- ∫_a^{x₀} + ∫_{x₀}^U = ∫_a^U
      have hsplit : (∫ v in a..x₀, g v) + ∫ v in x₀..U, g v = ∫ v in a..U, g v :=
        intervalIntegral.integral_add_adjacent_intervals (hgint a x₀) (hgint x₀ U)
      rw [hsum]
      have hstep : m p₀ * g x₀ + (∑ p ∈ T', m p * g (x p))
          ≤ (c * (x₀ - a) + d) * g x₀ + c * ∫ v in x₀..U, g v := by
        have : m p₀ * g x₀ + (d' * g x₀ + c * ∫ v in x₀..U, g v)
            = (m p₀ + d') * g x₀ + c * ∫ v in x₀..U, g v := by ring
        have hcoef : m p₀ + d' = c * (x₀ - a) + d := by rw [hd']; ring
        calc m p₀ * g x₀ + (∑ p ∈ T', m p * g (x p))
            ≤ m p₀ * g x₀ + (d' * g x₀ + c * ∫ v in x₀..U, g v) := by linarith [hih]
          _ = (m p₀ + d') * g x₀ + c * ∫ v in x₀..U, g v := by ring
          _ = (c * (x₀ - a) + d) * g x₀ + c * ∫ v in x₀..U, g v := by rw [hcoef]
      refine le_trans hstep ?_
      have hga_nn : 0 ≤ g a := hgnn a ⟨le_refl a, haU⟩
      have e1 : d * g x₀ ≤ d * g a := mul_le_mul_of_nonneg_left hgx₀a hd
      have e2 : c * ((x₀ - a) * g x₀) ≤ c * ∫ v in a..x₀, g v :=
        mul_le_mul_of_nonneg_left hRiemann hc
      have hfold : (c * (x₀ - a) + d) * g x₀ + c * ∫ v in x₀..U, g v
          = d * g x₀ + (c * ((x₀ - a) * g x₀) + c * ∫ v in x₀..U, g v) := by ring
      rw [hfold]
      have : c * ((x₀ - a) * g x₀) + c * ∫ v in x₀..U, g v ≤ c * ∫ v in a..U, g v := by
        have := hsplit
        nlinarith [e2, mul_le_mul_of_nonneg_left (le_of_eq hsplit) hc]
      linarith [e1, this]

/-! ## Part 1 — the `S ≥ 2` cell (side' = 2 even-window; side' = 1, `S ≥ 3` odd-tail) -/

/-- **The `S ≥ 2` `f`-cell.**  Given the window equation `hwin_eq` (`(1/S)∫_{S-1}^U fseq n =
fseq (n+1) S`, per parity: even-window for side' = 2, odd-tail for side' = 1 `S ≥ 3`), the
antitone majorant `fseq n` on `Ici L` (`L = loBnd (3-side') ∈ {1,2}`, `L ≤ S−1`), and the child
floor `hσL` (`σ_p ≥ L`), the engine + `upset_mass_le` + `fseq_le` close the cell at `cfSharpB`. -/
theorem hf_cell_ge2 (s' : BoundingSieve) (ε : ℝ) (z D' n : ℕ)
    (hε : 0 ≤ ε) (hn1 : 1 ≤ n) (hD : 1 ≤ D')
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS2 : 2 ≤ logRatio z D')
    (win : Finset ℕ) (hsub : win ⊆ s'.prodPrimes.primeFactors)
    (U : ℝ) (hUS : logRatio z D' - 1 ≤ U)
    (hUpts : ∀ p ∈ win, logRatio p D' - 1 ≤ U)
    (L : ℝ) (hLS : L ≤ logRatio z D' - 1)
    (hanti : AntitoneOn (fseq n) (Set.Ici L))
    (hσL : ∀ p ∈ win, L ≤ logRatio p (cdiv D' p))
    (hwin_eq : (∫ v in (logRatio z D' - 1)..U, fseq n v)
        = logRatio z D' * fseq (n + 1) (logRatio z D')) :
    (∑ p ∈ win, s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)))
      ≤ Salt.BrunLower.W s'
        * (fseq (n + 1) (logRatio z D') + cfSharpB n ε * hBJS (logRatio z D')) := by
  classical
  set S := logRatio z D' with hSdef
  set W := Salt.BrunLower.W s' with hWdef
  have hW := Salt.BrunLower.W_pos s'
  have hS1 : (1 : ℝ) ≤ S := by linarith
  have hS0 : (0 : ℝ) < S := by linarith
  -- log preamble
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [hSdef, logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [hSdef, logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  -- masses / points
  set m : ℕ → ℝ := fun p => s'.nu p * Vbelow s' p with hm
  set x : ℕ → ℝ := fun p => logRatio p D' - 1 with hx
  have hmnn : ∀ p ∈ win, 0 ≤ m p := by
    intro p hp
    have hppf := hsub hp
    exact mul_nonneg (s'.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hppf)
      (Nat.dvd_of_mem_primeFactors hppf)).le (Vbelow_pos s' p).le
  -- points lower bound `S - 1 ≤ x p` (from `p < z`)
  have hxge : ∀ p ∈ win, S - 1 ≤ x p := by
    intro p hp
    have hppf := hsub hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hpz : (p : ℝ) < (z : ℝ) := by exact_mod_cast hz p hppf
    have hlpz : Real.log p ≤ Real.log z := Real.log_le_log (by linarith) hpz.le
    have : S ≤ logRatio p D' := by
      rw [hSdef, logRatio, logRatio]; exact div_le_div_of_nonneg_left hlogD.le hlogp hlpz
    simp only [hx]; linarith
  have hxmem : ∀ p ∈ win, x p ∈ Set.Icc (S - 1) U :=
    fun p hp => ⟨hxge p hp, hUpts p hp⟩
  -- antitone `fseq n` on `[S-1, U] ⊆ Ici L`
  have hganti : AntitoneOn (fseq n) (Set.Icc (S - 1) U) :=
    hanti.mono (fun v hv => le_trans hLS hv.1)
  -- the affine mass control (from `upset_mass_le`)
  have hmass : ∀ v : ℝ, S - 1 ≤ v →
      (∑ p ∈ win.filter (fun p => x p ≤ v), m p) ≤ (1 + ε) * W / S * (v - (S - 1)) + ε * W := by
    intro v hv
    have hmass0 := upset_mass_le s' ε z D' (v + 1) hε hz hguard hnu hS1 (by linarith)
    have hsubfilt : win.filter (fun p => x p ≤ v)
        ⊆ s'.prodPrimes.primeFactors.filter (fun p => (logRatio p D' : ℝ) ≤ v + 1) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨hsub hp.1, ?_⟩
      have := hp.2; simp only [hx] at this; linarith
    have hle : (∑ p ∈ win.filter (fun p => x p ≤ v), m p)
        ≤ ∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => (logRatio p D' : ℝ) ≤ v + 1),
            s'.nu p * Vbelow s' p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubfilt
      intro p hp _
      have hppf := (Finset.mem_filter.mp hp).1
      exact mul_nonneg (s'.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hppf)
        (Nat.dvd_of_mem_primeFactors hppf)).le (Vbelow_pos s' p).le
    refine le_trans hle (le_trans hmass0 (le_of_eq ?_))
    rw [hSdef] at *; field_simp; ring
  -- run the engine
  have heng := abel_pushforward (fseq n) U ((1 + ε) * W / S)
    (by positivity) x m (fun p q => fseq_intervalIntegrable n p q)
    win (S - 1) (ε * W) (by positivity) (by linarith)
    hganti (fun v _ => fseq_nonneg n v) hmnn hxmem hmass
  -- majorization: `fseq n (σ_p) ≤ fseq n (x_p)`
  have hmaj : (∑ p ∈ win, m p * fseq n (logRatio p (cdiv D' p)))
      ≤ ∑ p ∈ win, m p * fseq n (x p) := by
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (hmnn p hp)
    have hppf := hsub hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hchild : x p ≤ logRatio p (cdiv D' p) := by
      have h := logRatio_child_ge hD hpp
      simp only [hx, logRatio]; exact h
    have hxL : L ≤ x p := le_trans hLS (hxge p hp)
    have hσLp : L ≤ logRatio p (cdiv D' p) := hσL p hp
    exact hanti (Set.mem_Ici.mpr hxL) (Set.mem_Ici.mpr hσLp) hchild
  -- rewrite LHS via majorization + engine + window equation
  have hstep : (∑ p ∈ win, s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)))
      ≤ ε * W * fseq n (S - 1) + (1 + ε) * W * fseq (n + 1) S := by
    have hcalc : ε * W * fseq n (S - 1)
        + (1 + ε) * W / S * (∫ v in (S - 1)..U, fseq n v)
        = ε * W * fseq n (S - 1) + (1 + ε) * W * fseq (n + 1) S := by
      rw [hwin_eq]; field_simp
    calc (∑ p ∈ win, s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)))
        = ∑ p ∈ win, m p * fseq n (logRatio p (cdiv D' p)) := by simp only [hm]
      _ ≤ ∑ p ∈ win, m p * fseq n (x p) := hmaj
      _ ≤ ε * W * fseq n (S - 1) + (1 + ε) * W / S * (∫ v in (S - 1)..U, fseq n v) := heng
      _ = ε * W * fseq n (S - 1) + (1 + ε) * W * fseq (n + 1) S := hcalc
  -- the defect bound
  refine le_trans hstep ?_
  obtain ⟨mm, rfl⟩ : ∃ mm, n = mm + 1 := ⟨n - 1, by omega⟩
  set Q := ε * Real.exp 2 * (99 / 100 : ℝ) ^ mm * hBJS S with hQ
  have hQnn : 0 ≤ Q := by
    rw [hQ]
    exact mul_nonneg (mul_nonneg (mul_nonneg hε (Real.exp_pos 2).le)
      (pow_nonneg (by norm_num) mm)) (hBJS_pos S).le
  -- the `(1+ε)`-excess (main term) rides in `2 · Q · (99/100)`
  have e1 : ε * fseq (mm + 1 + 1) S ≤ 2 * (99 / 100) * Q := by
    have hcoef : (0 : ℝ) ≤ 2 * Real.exp 2 * (99 / 100) ^ (mm + 1) := by positivity
    have hb : fseq (mm + 1 + 1) S ≤ 2 * Real.exp 2 * (99 / 100) ^ (mm + 1) * hBJS S :=
      le_trans (fseq_le (mm + 1) S) (mul_le_mul_of_nonneg_left (hbar_le_hBJS S) hcoef)
    refine le_trans (mul_le_mul_of_nonneg_left hb hε) (le_of_eq ?_)
    rw [hQ, pow_succ]; ring
  -- the `z`-edge boundary rides in `8 · Q` (via `hbar ≤ hBJS` + `hBJS_shift_le` ×4)
  have e2 : ε * fseq (mm + 1) (S - 1) ≤ 8 * Q := by
    have hcoef : (0 : ℝ) ≤ 2 * Real.exp 2 * (99 / 100) ^ mm := by positivity
    have hb : fseq (mm + 1) (S - 1) ≤ 2 * Real.exp 2 * (99 / 100) ^ mm * (4 * hBJS S) :=
      le_trans (fseq_le mm (S - 1))
        (mul_le_mul_of_nonneg_left (le_trans (hbar_le_hBJS (S - 1)) (hBJS_shift_le hS1)) hcoef)
    refine le_trans (mul_le_mul_of_nonneg_left hb hε) (le_of_eq ?_)
    rw [hQ]; ring
  have hRHS : cfSharpB (mm + 1) ε * hBJS S = 20 * (99 / 100) * Q := by
    rw [cfSharpB_of_pos (by omega) ε, hQ, pow_succ]; ring
  -- 8 + 2·(99/100) = 9.98 ≤ 20·(99/100) = 19.8
  have key : ε * fseq (mm + 1) (S - 1) + ε * fseq (mm + 1 + 1) S
      ≤ cfSharpB (mm + 1) ε * hBJS S := by
    rw [hRHS]; nlinarith [e1, e2, hQnn]
  have hWkey := mul_le_mul_of_nonneg_left key hW.le
  nlinarith [hWkey]

/-- **The flat-cell density floor** `e² · S · hBJS S ≥ 1` for `1 ≤ S ≤ 3` (equivalently
`S · hBJS S ≥ e⁻²`, sharp at `S = 1`).  This keeps the `1/S` and `hBJS S` factors of the flat
boundary together, so the boundary defect closes at coefficient `6(1+ε)/(99/100) ≈ 6.07`
(not the ~16.5 the double-crude `1/S ≤ 1`, `hBJS S ≥ e⁻³` would give).  The `2 < S ≤ 3` branch
uses the convexity secant `e^{S-2} ≤ (3−S) + (S−2)e ≤ S`. -/
theorem hBJS_flat_lb {S : ℝ} (hS1 : 1 ≤ S) (hS3 : S ≤ 3) : 1 ≤ Real.exp 2 * (S * hBJS S) := by
  have he21 : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
  rcases le_total S 2 with h2 | h2
  · rw [hBJS_le2 h2]
    have hid : Real.exp 2 * (S * Real.exp (-2)) = S := by
      rw [show Real.exp 2 * (S * Real.exp (-2)) = S * (Real.exp 2 * Real.exp (-2)) by ring,
        he21, mul_one]
    rw [hid]; exact hS1
  · rw [hBJS_mid h2 hS3]
    have hsec := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
      (show (0:ℝ) ≤ 3 - S by linarith) (show (0:ℝ) ≤ S - 2 by linarith) (by ring)
    simp only [smul_eq_mul] at hsec
    rw [show (3 - S) * (0:ℝ) + (S - 2) * 1 = S - 2 by ring, Real.exp_zero, mul_one] at hsec
    have he := Real.exp_one_lt_d9
    have hle : Real.exp (S - 2) ≤ S := by
      nlinarith [hsec, mul_nonneg (show (0:ℝ) ≤ S - 2 by linarith)
        (show (0:ℝ) ≤ 2.7182818286 - Real.exp 1 by linarith [he])]
    have hpos : (0:ℝ) < Real.exp (2 - S) := Real.exp_pos _
    have hid : Real.exp (S - 2) * Real.exp (2 - S) = 1 := by rw [← Real.exp_add]; norm_num
    have hkey : (1:ℝ) ≤ S * Real.exp (2 - S) := by
      nlinarith [mul_le_mul_of_nonneg_right hle hpos.le, hid, hpos]
    calc (1:ℝ) ≤ S * Real.exp (2 - S) := hkey
      _ = Real.exp 2 * (S * Real.exp (-S)) := by
          rw [show (2:ℝ) - S = 2 + -S by ring, Real.exp_add]; ring

/-! ## Part 2 — VD1: the window density bound `Vlow ≤ (3(1+ε)/S)·W` -/

/-- **VD1 — the window density bound** (the `h4`-shape, `h4`-free).  `Vlow = V(D'^{1/3}) ≤
(3(1+ε)/S)·W` for `1 ≤ S := logRatio z D' ≤ 3`, derived internally from the per-prime guards via
`vratio_prod_le` anchored at the up-window's minimal prime `p₀ ≥ D'^{1/3}` (so
`log p₀ ≥ (log D')/3`, giving `log z/log p₀ ≤ 3/S`).  The `≈ 100-line` sibling of
`upset_mass_window_le`; unblocks E₁c-close's `h4`-free discharge of `StepHypWPC`. -/
theorem vlow_le_of_guard (s' : BoundingSieve) (ε : ℝ) (z D' : ℕ)
    (hε : 0 ≤ ε)
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D') (hS3 : logRatio z D' ≤ 3) :
    Vlow s' D' ≤ (3 * (1 + ε) / logRatio z D') * Salt.BrunLower.W s' := by
  classical
  have hW := Salt.BrunLower.W_pos s'
  have hVlow := Vlow_pos s' D'
  set S := logRatio z D' with hSdef
  have hS0 : 0 < S := by linarith
  -- log preamble
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [hSdef, logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [hSdef, logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  -- `F = {p ∈ pf : ¬ p³ < D'} = {p ≥ D'^{1/3}}`
  set F := s'.prodPrimes.primeFactors.filter (fun p => ¬ p ^ 3 < D') with hFdef
  have hFprod_pos : 0 < ∏ p ∈ F, (1 - s'.nu p) := by
    apply Finset.prod_pos
    intro p hp
    have hppf := (Finset.mem_filter.mp hp).1
    have := s'.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hppf)
      (Nat.dvd_of_mem_primeFactors hppf)
    linarith
  -- `W = Vlow · ∏_F`
  have hWsplit : Salt.BrunLower.W s' = Vlow s' D' * ∏ p ∈ F, (1 - s'.nu p) := by
    rw [hFdef, Vlow, Salt.BrunLower.W]
    exact (Finset.prod_filter_mul_prod_filter_not s'.prodPrimes.primeFactors
      (fun p => p ^ 3 < D') (fun p => 1 - s'.nu p)).symm
  -- `(∏_F)⁻¹ ≤ 3(1+ε)/S`
  have hVratio : (∏ p ∈ F, (1 - s'.nu p))⁻¹ ≤ 3 * (1 + ε) / S := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · rw [hFe, Finset.prod_empty, inv_one]
      rw [le_div_iff₀ hS0]; nlinarith [hS3, hε, hS0]
    · set p₀ := F.min' hFne with hp₀
      have hp₀F : p₀ ∈ F := F.min'_mem hFne
      have hp₀pf : p₀ ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp₀F).1
      have hp₀cube : ¬ p₀ ^ 3 < D' := (Finset.mem_filter.mp hp₀F).2
      obtain ⟨hp₀3, hp₀thr⟩ := hguard p₀ hp₀pf
      have hp₀pp : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀pf
      have hp₀2 : (2 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀pp.two_le
      have hlogp₀ : 0 < Real.log p₀ := Real.log_pos (by linarith)
      have hp₀z : (p₀ : ℝ) ≤ (z : ℝ) := le_of_lt (by exact_mod_cast hz p₀ hp₀pf)
      have hmain := vratio_prod_le s' F hε hp₀3 hp₀z hp₀thr (fun p hp => by
        have hppf : p ∈ s'.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
        exact ⟨Nat.prime_of_mem_primeFactors hppf, by exact_mod_cast F.min'_le p hp,
          by exact_mod_cast hz p hppf, hnu p hppf⟩)
      -- `log p₀ ≥ (log D')/3`  (from `p₀³ ≥ D'`)
      have hcube : (D' : ℝ) ≤ (p₀ : ℝ) ^ 3 := by
        have : D' ≤ p₀ ^ 3 := Nat.not_lt.mp hp₀cube
        exact_mod_cast this
      have hlogcube : Real.log D' ≤ 3 * Real.log p₀ := by
        have hDpos : (0 : ℝ) < (D' : ℝ) := by
          rcases Nat.eq_zero_or_pos D' with h | h
          · rw [h] at hlogD; simp at hlogD
          · exact_mod_cast h
        have h := Real.log_le_log hDpos hcube
        rw [Real.log_pow] at h; push_cast at h; linarith [h]
      -- `log z/log p₀ ≤ 3/S`
      have hSval : Real.log z * S = Real.log D' := by
        rw [hSdef, logRatio, mul_comm, div_mul_cancel₀ _ (ne_of_gt hlogz)]
      have hlogzp : Real.log z / Real.log p₀ ≤ 3 / S := by
        rw [div_le_div_iff₀ hlogp₀ hS0]
        nlinarith [hlogcube, hSval, hlogz, hlogp₀]
      calc (∏ p ∈ F, (1 - s'.nu p))⁻¹ ≤ (1 + ε) * Real.log z / Real.log p₀ := hmain
        _ = (1 + ε) * (Real.log z / Real.log p₀) := by ring
        _ ≤ (1 + ε) * (3 / S) := mul_le_mul_of_nonneg_left hlogzp (by linarith)
        _ = 3 * (1 + ε) / S := by ring
  -- assemble
  have hVeq : Vlow s' D' = Salt.BrunLower.W s' * (∏ p ∈ F, (1 - s'.nu p))⁻¹ := by
    rw [hWsplit, mul_assoc, mul_inv_cancel₀ (ne_of_gt hFprod_pos), mul_one]
  rw [hVeq]
  calc Salt.BrunLower.W s' * (∏ p ∈ F, (1 - s'.nu p))⁻¹
      ≤ Salt.BrunLower.W s' * (3 * (1 + ε) / S) := mul_le_mul_of_nonneg_left hVratio hW.le
    _ = 3 * (1 + ε) / S * Salt.BrunLower.W s' := by ring

/-! ## Part 3 — the flat cell (side' = 1, `S ∈ [1,3)`, `n` even, odd-flat window) -/

set_option maxHeartbeats 400000 in
-- The flat cell composes the engine, majorization, window equation, VD1, and the two-term
-- defect ledger in one proof (many `set`/`calc` layers); the default budget is insufficient.
/-- **The flat `f`-cell** (side' = 1, `S ∈ [1,3)`).  Window-relative mass at `D'^{1/3}`
(`upset_mass_window_le`, fixed `S = 3` ⇒ fixed lower limit `2`), odd-flat window equation
`(1/S)∫_2^{n+2} fseq n = fseq (n+1) S`, `h4` from VD1 (`vlow_le_of_guard`).  Main
`(1+ε)²`-excess `≤ 4.002`, boundary `ε·Vlow·fseq n(2) ≤ 6.066` (via `fseq n(2) ≤ 2(99/100)ⁿ⁻¹`
and `hBJS_flat_lb`); total `≤ 20 = cfSharpB`. -/
theorem hf_sharp_flat (s' : BoundingSieve) (ε : ℝ) (z D' n : ℕ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) (hn1 : 1 ≤ n) (hnev : Even n) (hD : 1 ≤ D')
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D') (hS3 : logRatio z D' < 3) :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D'),
        s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)))
      ≤ Salt.BrunLower.W s'
        * (fseq (n + 1) (logRatio z D') + cfSharpB n ε * hBJS (logRatio z D')) := by
  classical
  set S := logRatio z D' with hSdef
  set W := Salt.BrunLower.W s' with hWdef
  have hW := Salt.BrunLower.W_pos s'
  have hVlowpos := Vlow_pos s' D'
  have hS0 : (0 : ℝ) < S := by linarith
  -- log preamble
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [hSdef, logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [hSdef, logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn0 : m + 1 ≠ 0 := by omega
  have hnev' : Even (m + 1) := hnev
  set win := s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D') with hwindef
  have hsub : win ⊆ s'.prodPrimes.primeFactors := Finset.filter_subset _ _
  set m' : ℕ → ℝ := fun p => s'.nu p * Vbelow s' p with hm'
  set x : ℕ → ℝ := fun p => logRatio p D' - 1 with hx
  set U := (m : ℝ) + 3 + logRatio 2 D' with hU
  have hlR2 : 0 ≤ logRatio 2 D' := by
    rw [logRatio]; exact div_nonneg hlogD.le hlog2.le
  have hUge : (m : ℝ) + 3 ≤ U := by rw [hU]; linarith
  -- window primes: `logRatio p D' > 3`, so `x p > 2`
  have hxlo : ∀ p ∈ win, (2 : ℝ) ≤ x p := by
    intro p hp
    have hp3 : p ^ 3 < D' := (Finset.mem_filter.mp hp).2
    have hppf := hsub hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have h3lp : 3 * Real.log p < Real.log D' := by
      have hpr : ((p : ℝ)) ^ 3 < (D' : ℝ) := by exact_mod_cast hp3
      have h1 := Real.log_lt_log (show (0:ℝ) < (p:ℝ)^3 by positivity) hpr
      rw [Real.log_pow] at h1; push_cast at h1; linarith
    have : (3 : ℝ) ≤ logRatio p D' := by rw [logRatio, le_div_iff₀ hlogp]; linarith
    simp only [hx]; linarith
  have hxU : ∀ p ∈ win, x p ≤ U := by
    intro p hp
    have hppf := hsub hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlog2p : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have hle : logRatio p D' ≤ logRatio 2 D' := by
      rw [logRatio, logRatio]; exact div_le_div_of_nonneg_left hlogD.le hlog2 hlog2p
    simp only [hx, hU]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hxmem : ∀ p ∈ win, x p ∈ Set.Icc (2 : ℝ) U := fun p hp => ⟨hxlo p hp, hxU p hp⟩
  have hmnn : ∀ p ∈ win, 0 ≤ m' p := by
    intro p hp
    have hppf := hsub hp
    exact mul_nonneg (s'.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hppf)
      (Nat.dvd_of_mem_primeFactors hppf)).le (Vbelow_pos s' p).le
  -- antitone `fseq (m+1)` on `[2,U]` (even level)
  have hganti : AntitoneOn (fseq (m + 1)) (Set.Icc (2 : ℝ) U) :=
    (fseq_antitoneOn_even hn0 hnev').mono (fun v hv => hv.1)
  -- the window-relative affine mass control
  have hmass : ∀ v : ℝ, (2 : ℝ) ≤ v →
      (∑ p ∈ win.filter (fun p => x p ≤ v), m' p)
        ≤ (1 + ε) * Vlow s' D' / 3 * (v - 2) + ε * Vlow s' D' := by
    intro v hv
    have hmass0 := upset_mass_window_le s' ε D' (v + 1) hε hlogD hguard hnu (by linarith)
    have hfiltereq : win.filter (fun p => x p ≤ v)
        = (s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D')).filter
            (fun p => (logRatio p D' : ℝ) ≤ v + 1) := by
      rw [hwindef]
      apply Finset.filter_congr
      intro p _; simp only [hx]
      constructor <;> intro h <;> linarith
    rw [hfiltereq]
    refine le_trans hmass0 (le_of_eq ?_)
    ring
  -- run the engine (a = 2, W → Vlow)
  have heng := abel_pushforward (fseq (m + 1)) U ((1 + ε) * Vlow s' D' / 3)
    (by positivity) x m' (fun p q => fseq_intervalIntegrable (m + 1) p q)
    win (2 : ℝ) (ε * Vlow s' D') (by positivity) (by linarith [hUge, Nat.cast_nonneg (α := ℝ) m])
    hganti (fun v _ => fseq_nonneg (m + 1) v) hmnn hxmem hmass
  -- majorization: `fseq (m+1) σ_p ≤ fseq (m+1) x_p`
  have hmaj : (∑ p ∈ win, m' p * fseq (m + 1) (logRatio p (cdiv D' p)))
      ≤ ∑ p ∈ win, m' p * fseq (m + 1) (x p) := by
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (hmnn p hp)
    have hppf := hsub hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppf
    have hchild : x p ≤ logRatio p (cdiv D' p) := by
      have h := logRatio_child_ge hD hpp; simp only [hx, logRatio]; exact h
    have hxL : (2 : ℝ) ≤ x p := hxlo p hp
    have hσL : (2 : ℝ) ≤ logRatio p (cdiv D' p) := by
      have h := logRatio_child_lower hD (Or.inl rfl) hppf
        (by intro _; exact (Finset.mem_filter.mp hp).2) hz (by rw [loBnd_one]; linarith)
      rwa [show (3 : ℕ) - 1 = 2 from rfl, loBnd_two] at h
    exact (fseq_antitoneOn_even hn0 hnev') (Set.mem_Ici.mpr hxL) (Set.mem_Ici.mpr hσL) hchild
  -- window equation: `∫_2^U fseq (m+1) = S · fseq (m+2) S`
  have hwin_eq : (∫ v in (2:ℝ)..U, fseq (m + 1) v) = S * fseq (m + 1 + 1) S := by
    have hodd : ¬ Even (m + 1 + 1) := by
      rw [Nat.even_add_one]; simpa using hnev'
    have htail : (∫ v in (2:ℝ)..U, fseq (m + 1) v)
        = ∫ v in (2:ℝ)..((m : ℝ) + 3), fseq (m + 1) v := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (fseq_intervalIntegrable (m + 1) 2 ((m : ℝ) + 3))
        (fseq_intervalIntegrable (m + 1) ((m : ℝ) + 3) U)]
      have hz2 : (∫ v in ((m : ℝ) + 3)..U, fseq (m + 1) v) = 0 := by
        rw [show (0:ℝ) = ∫ _v in ((m : ℝ) + 3)..U, (0:ℝ) from by simp]
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le hUge] at hv
        exact fseq_eq_zero_of_ge (m + 1) v (by push_cast; linarith [hv.1])
      rw [hz2, add_zero]
    have hshift : (∫ v in (2:ℝ)..((m : ℝ) + 3), fseq (m + 1) v)
        = ∫ t in (3:ℝ)..(((m + 1 : ℕ) : ℝ) + 3), fseq (m + 1) (t - 1) := by
      have he2 : (3 : ℝ) - 1 = 2 := by norm_num
      have he3 : ((m + 1 : ℕ) : ℝ) + 3 - 1 = (m : ℝ) + 3 := by push_cast; ring
      rw [intervalIntegral.integral_comp_sub_right (fun u => fseq (m + 1) u) 1, he2, he3]
    have hflat := fseq_odd_flat_window (n := m + 1) hn0 hodd (s := S) hS1 hS3
    have hSfeq : S * fseq (m + 1 + 1) S
        = ∫ t in (3:ℝ)..(((m + 1 : ℕ) : ℝ) + 3), fseq (m + 1) (t - 1) := by
      rw [hflat, ← mul_assoc, mul_one_div, div_self hS0.ne', one_mul]
    rw [htail, hshift]; exact hSfeq.symm
  -- h4 from VD1
  have h4 : Vlow s' D' ≤ (3 * (1 + ε) / S) * W :=
    vlow_le_of_guard s' ε z D' hε hz hguard hnu hS1 (le_of_lt hS3)
  -- assemble the pre-defect bound
  have hstep : (∑ p ∈ win, s'.nu p * Vbelow s' p * fseq (m + 1) (logRatio p (cdiv D' p)))
      ≤ ε * Vlow s' D' * fseq (m + 1) 2 + (1 + ε) * Vlow s' D' / 3 * (S * fseq (m + 1 + 1) S) := by
    calc (∑ p ∈ win, s'.nu p * Vbelow s' p * fseq (m + 1) (logRatio p (cdiv D' p)))
        = ∑ p ∈ win, m' p * fseq (m + 1) (logRatio p (cdiv D' p)) := by simp only [hm']
      _ ≤ ∑ p ∈ win, m' p * fseq (m + 1) (x p) := hmaj
      _ ≤ ε * Vlow s' D' * fseq (m + 1) 2
            + (1 + ε) * Vlow s' D' / 3 * (∫ v in (2:ℝ)..U, fseq (m + 1) v) := heng
      _ = ε * Vlow s' D' * fseq (m + 1) 2
            + (1 + ε) * Vlow s' D' / 3 * (S * fseq (m + 1 + 1) S) := by rw [hwin_eq]
  refine le_trans hstep ?_
  -- the monomial the defects ride on
  set M := Real.exp 2 * (99 / 100 : ℝ) ^ m * hBJS S with hM
  have hMnn : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (mul_nonneg (Real.exp_pos 2).le (pow_nonneg (by norm_num) m))
      (hBJS_pos S).le
  have hhBJSnn : (0 : ℝ) ≤ hBJS S := (hBJS_pos S).le
  have hfnn : (0 : ℝ) ≤ fseq (m + 1 + 1) S := fseq_nonneg _ _
  -- MAIN term: `(1+ε)·Vlow/3·(S·f) ≤ (1+ε)²·W·f`
  have hmain : (1 + ε) * Vlow s' D' / 3 * (S * fseq (m + 1 + 1) S)
      ≤ (1 + ε) ^ 2 * W * fseq (m + 1 + 1) S := by
    have hcoef : (0 : ℝ) ≤ (1 + ε) * S / 3 * fseq (m + 1 + 1) S :=
      mul_nonneg (by positivity) hfnn
    have h := mul_le_mul_of_nonneg_left h4 hcoef
    calc (1 + ε) * Vlow s' D' / 3 * (S * fseq (m + 1 + 1) S)
        = (1 + ε) * S / 3 * fseq (m + 1 + 1) S * Vlow s' D' := by ring
      _ ≤ (1 + ε) * S / 3 * fseq (m + 1 + 1) S * (3 * (1 + ε) / S * W) := h
      _ = (1 + ε) ^ 2 * W * fseq (m + 1 + 1) S := by field_simp
  -- BOUNDARY term: `ε·Vlow·fseq(m+1)(2) ≤ 6ε(1+ε)/S·(99/100)^m·W`
  have hf2 : fseq (m + 1) 2 ≤ 2 * (99 / 100 : ℝ) ^ m := by
    have h := fseq_le m 2
    rw [hbar_lo (le_refl (2:ℝ))] at h
    have he21 : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
    calc fseq (m + 1) 2 ≤ 2 * Real.exp 2 * (99 / 100 : ℝ) ^ m * Real.exp (-2) := h
      _ = 2 * (99 / 100 : ℝ) ^ m := by
          rw [show 2 * Real.exp 2 * (99 / 100 : ℝ) ^ m * Real.exp (-2)
              = 2 * (99 / 100 : ℝ) ^ m * (Real.exp 2 * Real.exp (-2)) by ring, he21, mul_one]
  have hbdry : ε * Vlow s' D' * fseq (m + 1) 2 ≤ 6 * ε * (1 + ε) / S * (99 / 100 : ℝ) ^ m * W := by
    have hVh : Vlow s' D' * fseq (m + 1) 2 ≤ (3 * (1 + ε) / S * W) * (2 * (99 / 100 : ℝ) ^ m) :=
      mul_le_mul h4 hf2 (fseq_nonneg _ _) (le_trans hVlowpos.le h4)
    calc ε * Vlow s' D' * fseq (m + 1) 2 = ε * (Vlow s' D' * fseq (m + 1) 2) := by ring
      _ ≤ ε * ((3 * (1 + ε) / S * W) * (2 * (99 / 100 : ℝ) ^ m)) :=
          mul_le_mul_of_nonneg_left hVh hε
      _ = 6 * ε * (1 + ε) / S * (99 / 100 : ℝ) ^ m * W := by ring
  -- the defect close: main-excess + boundary ≤ cfSharpB·hBJS·W
  refine le_trans (add_le_add hbdry hmain) ?_
  rw [cfSharpB_of_pos hn0 ε]
  -- fseq (m+2) S ≤ 2·(99/100)·M  (= 2 e² (99/100)^{m+1} hBJS S)
  have hfbnd : fseq (m + 1 + 1) S ≤ 2 * (99 / 100) * M := by
    have h := le_trans (fseq_le (m + 1) S)
      (mul_le_mul_of_nonneg_left (hbar_le_hBJS S)
        (show (0:ℝ) ≤ 2 * Real.exp 2 * (99 / 100 : ℝ) ^ (m + 1) by positivity))
    refine le_trans h (le_of_eq ?_)
    rw [hM, pow_succ]; ring
  -- 1/S ≤ e² · hBJS S   (from hBJS_flat_lb)
  have hinvS : (1 : ℝ) / S ≤ Real.exp 2 * hBJS S := by
    have hlb := hBJS_flat_lb hS1 (le_of_lt hS3)
    rw [div_le_iff₀ hS0]
    calc (1 : ℝ) ≤ Real.exp 2 * (S * hBJS S) := hlb
      _ = Real.exp 2 * hBJS S * S := by ring
  set P := ε * M * W with hP
  have hPnn : 0 ≤ P := by rw [hP]; exact mul_nonneg (mul_nonneg hε hMnn) hW.le
  -- boundary ≤ 6(1+ε)·P
  have hbdryM : 6 * ε * (1 + ε) / S * (99 / 100 : ℝ) ^ m * W ≤ 6 * (1 + ε) * P := by
    have hcoefnn : (0 : ℝ) ≤ 6 * ε * (1 + ε) * (99 / 100 : ℝ) ^ m * W :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)) hW.le
    have hkey := mul_le_mul_of_nonneg_left hinvS hcoefnn
    calc 6 * ε * (1 + ε) / S * (99 / 100 : ℝ) ^ m * W
        = 6 * ε * (1 + ε) * (99 / 100 : ℝ) ^ m * W * (1 / S) := by ring
      _ ≤ 6 * ε * (1 + ε) * (99 / 100 : ℝ) ^ m * W * (Real.exp 2 * hBJS S) := hkey
      _ = 6 * (1 + ε) * P := by rw [hP, hM]; ring
  -- main-excess ≤ 2·(99/100)·(2+ε)·P
  have hmainM : (1 + ε) ^ 2 * W * fseq (m + 1 + 1) S
      ≤ W * fseq (m + 1 + 1) S + 2 * (99 / 100) * (2 + ε) * P := by
    have hc : (0 : ℝ) ≤ (2 + ε) * ε := by nlinarith [hε]
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfbnd hc) hW.le
    rw [show (2 + ε) * ε * (2 * (99 / 100) * M) * W = 2 * (99 / 100) * (2 + ε) * P by rw [hP]; ring]
      at hmul
    have hL : (1 + ε) ^ 2 * W * fseq (m + 1 + 1) S
        = W * fseq (m + 1 + 1) S + (2 + ε) * ε * fseq (m + 1 + 1) S * W := by ring
    rw [hL]; linarith [hmul]
  -- combine and close the scalar coefficient `≤ 20·(99/100)`
  refine le_trans (add_le_add hbdryM hmainM) ?_
  have hRHSeq : W * (fseq (m + 1 + 1) S + 20 * ε * Real.exp 2 * (99 / 100) ^ (m + 1) * hBJS S)
      = W * fseq (m + 1 + 1) S + 20 * (99 / 100) * P := by rw [hP, hM, pow_succ]; ring
  rw [hRHSeq]
  have hcoefclose : 6 * (1 + ε) + 2 * (99 / 100) * (2 + ε) ≤ 20 * (99 / 100) := by
    nlinarith [hε, hεsmall]
  have hprod := mul_le_mul_of_nonneg_right hcoefclose hPnn
  have hexpand : 6 * (1 + ε) * P + 2 * (99 / 100) * (2 + ε) * P
      = (6 * (1 + ε) + 2 * (99 / 100) * (2 + ε)) * P := by ring
  linarith [hprod, hexpand]

/-! ## Part 4 — the assembled sharp `f`-comparison `hf_sharp_of_window` -/

/-- The `S ≥ 2` window-equation glue: from the recursion `S·fseq(n+1)(S) = ∫_S^{n+3} fseq n(t−1)`
(even-window or odd-tail), the engine's integral `∫_{S-1}^U fseq n` equals `S·fseq(n+1)(S)` for
any `U ≥ n+2` (the tail past `n+2` vanishes; shift `v = t−1`). -/
theorem windoweq_of_Sfeq (n : ℕ) (S U : ℝ) (hUn : (n : ℝ) + 2 ≤ U)
    (hSfeq : S * fseq (n + 1) S = ∫ t in S..((n : ℝ) + 3), fseq n (t - 1)) :
    (∫ v in (S - 1)..U, fseq n v) = S * fseq (n + 1) S := by
  have htail : (∫ v in (S - 1)..U, fseq n v) = ∫ v in (S - 1)..((n : ℝ) + 2), fseq n v := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (fseq_intervalIntegrable n (S - 1) ((n : ℝ) + 2))
      (fseq_intervalIntegrable n ((n : ℝ) + 2) U)]
    have hz2 : (∫ v in ((n : ℝ) + 2)..U, fseq n v) = 0 := by
      rw [show (0:ℝ) = ∫ _v in ((n : ℝ) + 2)..U, (0:ℝ) from by simp]
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le hUn] at hv
      exact fseq_eq_zero_of_ge n v hv.1
    rw [hz2, add_zero]
  have hshift : (∫ v in (S - 1)..((n : ℝ) + 2), fseq n v)
      = ∫ t in S..((n : ℝ) + 3), fseq n (t - 1) := by
    have he : ((n : ℝ) + 3) - 1 = (n : ℝ) + 2 := by ring
    rw [intervalIntegral.integral_comp_sub_right (fun u => fseq n u) 1, he]
  rw [htail, hshift, hSfeq]

/-- **The sharp `f`-part windowed comparison** — the `cfSharpB` `f`-slot of `StepHypWPC`, composed
by cases on `side'` and `S := logRatio z D'`.  `side' = 2` (⇒ `S ≥ 2`, `n` odd, even window) and
`side' = 1, S ≥ 3` (`n` even, odd-tail window) close via `hf_cell_ge2`; `side' = 1, S ∈ [1,3)`
(odd-flat window) via `hf_sharp_flat` (which derives its `h4` from VD1 `vlow_le_of_guard`, so no
`h4` hypothesis is threaded).  The `f`-side sibling of `hh_sharp_of_window`.

Carries `hεsmall : ε ≤ 1/1000` (as does `hh_sharp_of_window`): the flat cell's `(1+ε)²` main
excess is quadratic in `ε` while `cfSharpB` is linear, so an `ε`-bound is unavoidable there;
`ε_sieve = 2·10⁻⁸ ≤ 1/1000` supplies it downstream. -/
theorem hf_sharp_of_window (s' : BoundingSieve) (ε : ℝ) (z side' D' n : ℕ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000) (hn : 1 ≤ n) (hD : 1 ≤ D')
    (hside : side' = 1 ∨ side' = 2)
    (hz : ∀ q ∈ s'.prodPrimes.primeFactors, q < z)
    (hguard : ∀ q ∈ s'.prodPrimes.primeFactors,
        3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε))
    (hnu : ∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1))
    (hS1 : 1 ≤ logRatio z D') (hSn : logRatio z D' ≤ (n : ℝ) + 3)
    (hlo : loBnd side' ≤ logRatio z D') (hpar : side' % 2 ≠ n % 2) :
    (∑ p ∈ s'.prodPrimes.primeFactors.filter (fun p => side' % 2 = 1 → p ^ 3 < D'),
        s'.nu p * Vbelow s' p * fseq n (logRatio p (cdiv D' p)))
      ≤ Salt.BrunLower.W s'
        * (fseq (n + 1) (logRatio z D') + cfSharpB n ε * hBJS (logRatio z D')) := by
  classical
  set S := logRatio z D' with hSdef
  have hSpos : (0 : ℝ) < S := by linarith
  -- log preamble (for the point/window bounds)
  have hlz_nn : (0 : ℝ) ≤ Real.log z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlogz : 0 < Real.log z := by
    rcases lt_or_eq_of_le hlz_nn with h | h
    · exact h
    · exfalso; rw [hSdef, logRatio, ← h, div_zero] at hS1; linarith
  have hzD : Real.log z ≤ Real.log D' := by
    have h := hS1; rw [hSdef, logRatio, le_div_iff₀ hlogz, one_mul] at h; exact h
  have hlogD : 0 < Real.log D' := lt_of_lt_of_le hlogz hzD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set U := (n : ℝ) + 2 + logRatio 2 D' with hU
  have hlR2 : 0 ≤ logRatio 2 D' := by rw [logRatio]; exact div_nonneg hlogD.le hlog2.le
  have hUn : (n : ℝ) + 2 ≤ U := by rw [hU]; linarith
  have hUS : S - 1 ≤ U := by rw [hU]; linarith [hSn]
  have hUpts_gen : ∀ p ∈ s'.prodPrimes.primeFactors, logRatio p D' - 1 ≤ U := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlog2p : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have hle : logRatio p D' ≤ logRatio 2 D' := by
      rw [logRatio, logRatio]; exact div_le_div_of_nonneg_left hlogD.le hlog2 hlog2p
    rw [hU]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  rcases hside with rfl | rfl
  · -- side' = 1 ⟹ `n` even
    have hnev : Even n := Nat.even_iff.mpr (by omega)
    by_cases hlt3 : S < 3
    · -- flat cell
      have hfilter :
          s'.prodPrimes.primeFactors.filter (fun p => 1 % 2 = 1 → p ^ 3 < D')
            = s'.prodPrimes.primeFactors.filter (fun p => p ^ 3 < D') :=
        Finset.filter_congr (fun p _ => ⟨fun h => h (by norm_num), fun h _ => h⟩)
      rw [hfilter]
      exact hf_sharp_flat s' ε z D' n hε hεsmall hn hnev hD hz hguard hnu hS1 hlt3
    · -- `S ≥ 3` odd-tail cell
      have hS3 : (3 : ℝ) ≤ S := not_lt.mp hlt3
      have hS2 : (2 : ℝ) ≤ S := by linarith
      set win := s'.prodPrimes.primeFactors.filter (fun p => 1 % 2 = 1 → p ^ 3 < D') with hwin
      have hsub : win ⊆ s'.prodPrimes.primeFactors := Finset.filter_subset _ _
      have hSfeq : S * fseq (n + 1) S = ∫ t in S..((n : ℝ) + 3), fseq n (t - 1) := by
        have hodd : ¬ Even (n + 1) := by rw [Nat.even_add_one]; simpa using hnev
        have h := fseq_odd_tail_window (n := n) (by omega) hodd (s := S) hS3
        rw [h, ← mul_assoc, mul_one_div, div_self hSpos.ne', one_mul]
      have hwin_eq := windoweq_of_Sfeq n S U hUn hSfeq
      have hanti : AntitoneOn (fseq n) (Set.Ici (2 : ℝ)) := fseq_antitoneOn_even (by omega) hnev
      have hσL : ∀ p ∈ win, (2 : ℝ) ≤ logRatio p (cdiv D' p) := by
        intro p hp
        have hp_pf := hsub hp
        have hp_win : 1 % 2 = 1 → p ^ 3 < D' := (Finset.mem_filter.mp hp).2
        have h := logRatio_child_lower hD (Or.inl rfl) hp_pf hp_win hz (by rw [loBnd_one]; linarith)
        rwa [show (3 : ℕ) - 1 = 2 from rfl, loBnd_two] at h
      exact hf_cell_ge2 s' ε z D' n hε hn hD hz hguard hnu hS2 win hsub U hUS
        (fun p hp => hUpts_gen p (hsub hp)) 2 (by linarith) hanti hσL hwin_eq
  · -- side' = 2 ⟹ `n` odd, `S ≥ 2` (loBnd 2 = 2)
    have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
    have hS2 : (2 : ℝ) ≤ S := by rw [loBnd_two] at hlo; exact hlo
    set win := s'.prodPrimes.primeFactors.filter (fun p => 2 % 2 = 1 → p ^ 3 < D') with hwin
    have hsub : win ⊆ s'.prodPrimes.primeFactors := Finset.filter_subset _ _
    have hSfeq : S * fseq (n + 1) S = ∫ t in S..((n : ℝ) + 3), fseq n (t - 1) := by
      have hev : Even (n + 1) := by rw [Nat.even_add_one]; simpa using hnodd
      have h := fseq_even_window (n := n) hev (s := S) hS2
      rw [h, ← mul_assoc, mul_one_div, div_self hSpos.ne', one_mul]
    have hwin_eq := windoweq_of_Sfeq n S U hUn hSfeq
    have hanti : AntitoneOn (fseq n) (Set.Ici (1 : ℝ)) := fseq_antitoneOn_odd hnodd
    have hσL : ∀ p ∈ win, (1 : ℝ) ≤ logRatio p (cdiv D' p) := by
      intro p hp
      have hp_pf := hsub hp
      have hp_win : 2 % 2 = 1 → p ^ 3 < D' := fun h => absurd h (by decide)
      have h := logRatio_child_lower hD (Or.inr rfl) hp_pf hp_win hz (by rw [loBnd_two]; linarith)
      rwa [show (3 : ℕ) - 2 = 1 from rfl, loBnd_one] at h
    exact hf_cell_ge2 s' ε z D' n hε hn hD hz hguard hnu hS2 win hsub U hUS
      (fun p hp => hUpts_gen p (hsub hp)) 1 (by linarith) hanti hσL hwin_eq

end Salt.Chen
