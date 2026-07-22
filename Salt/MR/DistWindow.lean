/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PropA3Core

/-!
# PART 3 — T-1 — the W-VANISHING window-restriction route (HLOSS RESOLVED)

The terminal-assembly freeze (`docs/exploration/terminal-assembly-freeze.md`,
PART 3, T-1 — DESIGNED, the TERM-REF amendment).

TERM-REF's counterexample (`f = costwist t₀`: center distance 0 yet in-window
defect `~ loglog X`) kills the halve-minus-`W` route at resonant `t₀`, AND exposes
an iron-rule-1 drift: the landed `dist_split_A4_frozen` carries a `−W` term while
the s8-freeze N2 FROZEN conclusion has NO `W`.  THE AMENDED ROUTE (additive
supersession — the `−W` lemmas in `DistSplit`/`PropA3Core` stay landed, untouched):

* **(i) `dist_window_restrict`** — the window-restriction identity.  From
  `pretDistSq`'s definition and the `fgJ = f·windowIndicator·twist` coefficient
  structure: out-of-window primes contribute `≥ −(their 1/p mass)`, in-window
  primes contribute the f-defect at the SHIFTED frequency `t+t₀` (the twist
  recentering).  Dropping the (nonneg) in-window part on the `≥` side gives
  `𝔻(fgJ, costwist t)² ≥ 𝔻(f, costwist(t+t₀))² − (out-of-window mass)`.
  **W DISAPPEARS** — there is no `𝔻(f, fgJ)²` loss; the price is the concrete,
  boundable out-of-window prime mass.
* **(ii) `out_of_window_mass_le`** — the out-of-window mass is
  `Σ_{p≤y} 1/p + Σ_{X/y≤p≤X} 1/p = O(logloglog X)` at polylog `y = (log X)^A`
  (`mertens_second_sharp` twice; the `A` enters the constant).  The dominant
  `Σ_{p≤y} 1/p ≍ loglog y = logloglog X + log A` — coefficient **1** on
  `logloglog X`, absorbed by the frozen `−5·logloglog` slack with room (1 ≤ 5).
* **(iii) `dist_split_A4_N2`** — the R3.1 floor AT THE FROZEN N2 SHAPE,
  `(1/32)loglog X − 5·logloglog(2X+16) − C`, **NO W** — via (i)+(ii) and the
  branch f-floor (restated at the shifted frequency `t+t₀`).  The `−5·logloglog`
  slack absorbs (ii)'s mass; the constant fit is honest (coefficient 1 ≤ 5).

The frequency bookkeeping: the `t` in `𝔻(fgJ, costwist t)` is already
`t₀`-recentered (the seam twist `n^{−it₀}`), so the f-floor lands at `t+t₀`.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators
open Complex

/-! ## The out-of-window mass -/

/-- **The out-of-window prime mass.**  `Σ_{p≤X prime, p ∉ (y,Y)} 1/p`, written as an
`if`-sum over the full prime set (matching `dist_window_restrict`'s per-prime
bookkeeping).  In the seam `Y = X/y`, so the out-of-window primes are `p ≤ y` and
`X/y ≤ p ≤ X`. -/
def outWindowMass (y Y X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
    (if y < (p : ℝ) ∧ (p : ℝ) < Y then 0 else (1 : ℝ) / p)

lemma outWindowMass_nonneg (y Y X : ℝ) : 0 ≤ outWindowMass y Y X := by
  unfold outWindowMass
  refine Finset.sum_nonneg (fun p hp => ?_)
  split_ifs with h
  · exact le_refl (0 : ℝ)
  · positivity

/-! ## The twist algebra bridge -/

/-- The seam twist `n ↦ n^{−it₀}` equals the character `costwist (−t₀)`.  Bridges
the `cpow` twist in `seamCoeff`/`fgJ` to the `costwist` character algebra. -/
private lemma natCpow_neg_costwist (t₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-(t₀ : ℂ) * I) = costwist (-t₀) n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  unfold costwist
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-! ## (i) The window-restriction identity -/

/-- **T-1 (i) — the window-restriction identity (`dist_window_restrict`).**  For
1-bounded `f`, the windowed–twisted seam datum `fgJ f t₀ y Y` obeys

  `𝔻(fgJ f t₀ y Y, costwist t; X)² ≥ 𝔻(f, costwist(t+t₀); X)² − outWindowMass y Y X`.

Per-prime: IN-window primes give the exact f-defect at the SHIFTED frequency `t+t₀`
(the `n^{−it₀}` twist folds into the character, `natCpow_neg_costwist` +
`costwist_add`/`costwist_conj`); OUT-of-window primes have `fgJ = 0`, so their
`fgJ`-summand is `1/p` while the f-summand is `≤ 2/p` (as `Re(f·conj costwist) ≥ −1`),
a deficit of `≥ −1/p`.  Summing the deficit gives `−outWindowMass`.  **No `𝔻(f,fgJ)²`
window loss `W` appears** — this is the additive supersession of the `−W` route. -/
theorem dist_window_restrict {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y t X : ℝ) :
    pretDistSq f (costwist (t + t₀)) X - outWindowMass y Y X
      ≤ pretDistSq (fgJ f t₀ y Y) (costwist t) X := by
  unfold pretDistSq outWindowMass
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun p hp => ?_)
  obtain ⟨_, hpp⟩ := Finset.mem_filter.mp hp
  have hp1 : 1 ≤ p := hpp.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hpne : (p : ℕ) ≠ 0 := Nat.one_le_iff_ne_zero.mp hp1
  by_cases hw : y < (p : ℝ) ∧ (p : ℝ) < Y
  · -- IN window: the fgJ-summand equals the f-summand at the shifted frequency
    have hfgJ : fgJ f t₀ y Y p = f p * costwist (-t₀) p := by
      unfold fgJ seamCoeff
      rw [if_neg hpne,
        show windowIndicator y Y p = 1 from by unfold windowIndicator; rw [if_pos hw],
        natCpow_neg_costwist t₀ hp1, mul_one]
    have heq : fgJ f t₀ y Y p * (starRingEnd ℂ) (costwist t p)
        = f p * (starRingEnd ℂ) (costwist (t + t₀) p) := by
      rw [hfgJ, costwist_conj t p, costwist_conj (t + t₀) p, mul_assoc,
        costwist_add (-t₀) (-t) p, show -t₀ + -t = -(t + t₀) from by ring]
    have heqre : (fgJ f t₀ y Y p * (starRingEnd ℂ) (costwist t p)).re
        = (f p * (starRingEnd ℂ) (costwist (t + t₀) p)).re := by rw [heq]
    rw [if_pos hw, sub_zero]
    exact le_of_eq (by rw [heqre])
  · -- OUT of window: fgJ p = 0, so the fgJ-summand is 1/p and the deficit is ≥ −1/p
    have hfgJ0 : fgJ f t₀ y Y p = 0 := by
      unfold fgJ seamCoeff
      rw [if_neg hpne,
        show windowIndicator y Y p = 0 from by unfold windowIndicator; rw [if_neg hw]]
      ring
    have hre_ge : (-1 : ℝ) ≤ (f p * (starRingEnd ℂ) (costwist (t + t₀) p)).re := by
      have hnorm : ‖f p * (starRingEnd ℂ) (costwist (t + t₀) p)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_conj]
        calc ‖f p‖ * ‖costwist (t + t₀) p‖ ≤ 1 * 1 :=
              mul_le_mul (hf p) (norm_costwist_le (t + t₀) p) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have h1 : (-(f p * (starRingEnd ℂ) (costwist (t + t₀) p))).re
          ≤ ‖-(f p * (starRingEnd ℂ) (costwist (t + t₀) p))‖ := Complex.re_le_norm _
      rw [Complex.neg_re, norm_neg] at h1
      linarith [h1, hnorm]
    rw [if_neg hw]
    simp only [hfgJ0, zero_mul, Complex.zero_re, sub_zero]
    rw [div_sub_div_same]
    gcongr
    linarith [hre_ge]

/-! ## (ii) The out-of-window mass bound

The structural reduction to the two Mertens-ready prime tails is landed cleanly.
The dominant LOWER tail `Σ_{p≤y} 1/p ≍ loglog y = logloglog X + log A` (coefficient
`1` on `logloglog X`, `mertens_second_sharp`); the UPPER tail
`Σ_{X/y≤p≤X} 1/p = loglog X − loglog(X/y) → 0` (two-sided `mertens_second_sharp`).
Both fit the frozen `−5·logloglog` slack (`1 ≤ 5`). -/

/-- **T-1 (ii) — the tail reduction (`outWindowMass_le_tails`).**  The out-of-window
mass is at most the sum of the LOWER prime tail `Σ_{p≤y} 1/p` and the UPPER prime tail
`Σ_{Y≤p≤X} 1/p` (the two Mertens-ready pieces).  Pure Finset bookkeeping: each
out-of-window prime (`¬(y<p<Y)`, i.e. `p≤y ∨ Y≤p`) is counted by at least one tail
indicator.  This is the structural half of the mass bound; the numeric discharge of
each tail into `logloglog X + C` via `mertens_second_sharp` is the remaining
arithmetic (the dominant lower tail carries coefficient `1` on `logloglog X`). -/
theorem outWindowMass_le_tails (y Y X : ℝ) :
    outWindowMass y Y X
      ≤ (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
            if (p : ℝ) ≤ y then 1 / (p : ℝ) else 0)
        + (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
            if Y ≤ (p : ℝ) then 1 / (p : ℝ) else 0) := by
  unfold outWindowMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p hp => ?_)
  obtain ⟨_, hpp⟩ := Finset.mem_filter.mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlo : (0 : ℝ) ≤ (if (p : ℝ) ≤ y then 1 / (p : ℝ) else 0) := by
    split_ifs <;> positivity
  have hhi : (0 : ℝ) ≤ (if Y ≤ (p : ℝ) then 1 / (p : ℝ) else 0) := by
    split_ifs <;> positivity
  by_cases hw : y < (p : ℝ) ∧ (p : ℝ) < Y
  · rw [if_pos hw]; linarith [hlo, hhi]
  · rw [if_neg hw]
    have hcase : (p : ℝ) ≤ y ∨ Y ≤ (p : ℝ) := by
      rcases not_and_or.mp hw with h | h
      · exact Or.inl (not_lt.mp h)
      · exact Or.inr (not_lt.mp h)
    rcases hcase with hle | hge
    · rw [if_pos hle]; linarith [hhi]
    · rw [if_pos hge]; linarith [hlo]

/-- **T-1 (ii) — the LOWER tail bound (`lowerTail_le`), the honesty crux.**  The
dominant out-of-window tail `Σ_{p≤y} 1/p` at `y ≤ (log X)^A` is bounded by
`logloglog X + C` with **coefficient 1** on `logloglog X` (`mertens_second_sharp` +
`loglog y ≤ loglog((log X)^A) = logloglog X + log A`).  This is the piece that answers
"does the frozen `−5·logloglog` slack absorb (ii)'s mass?" — YES: the coefficient is
`1 ≤ 5`, with room.  (`hyA : y ≤ (log X)^A`, `hy2 : 2 ≤ y` force `log X > 1`, so
`loglog X > 0`; `hyX : ⌊y⌋₊ ≤ ⌊X⌋₊` places the tail inside the prime range.) -/
theorem lowerTail_le {X y A : ℝ} (hX : Real.exp 1 ≤ X) (hA : 0 < A) (hy2 : 2 ≤ y)
    (hyA : y ≤ (Real.log X) ^ A) (hyX : ⌊y⌋₊ ≤ ⌊X⌋₊) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          if (p : ℝ) ≤ y then 1 / (p : ℝ) else 0)
        ≤ Real.log (Real.log (Real.log X)) + C := by
  -- Mertens data
  obtain ⟨M, C₀, hC₀, hMert⟩ := Salt.Mertens.mertens_second_sharp
  set n := ⌊y⌋₊ with hndef
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hy2)
  have hn1r : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- the tail is the Mertens prime sum up to `n = ⌊y⌋₊`
  have hfeq : ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => (p : ℝ) ≤ y)
      = (Finset.range (n + 1)).filter Nat.Prime := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hqp⟩, hqy⟩
      exact ⟨by have := (Nat.le_floor_iff hy0).mpr hqy; omega, hqp⟩
    · rintro ⟨hqn, hqp⟩
      have hqle : q ≤ n := by omega
      exact ⟨⟨by omega, hqp⟩, (Nat.le_floor_iff hy0).mp hqle⟩
  have hsum : (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
        if (p : ℝ) ≤ y then 1 / (p : ℝ) else 0)
      = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p := by
    rw [← Finset.sum_filter, hfeq]
  -- log positivity chain (the y-regime forces `log X > 1`, hence `loglog X > 0`)
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hlogXgt1 : (1 : ℝ) < Real.log X := by
    by_contra hcon
    have hcon' : Real.log X ≤ 1 := not_lt.mp hcon
    have h1 : (Real.log X) ^ A ≤ 1 := Real.rpow_le_one hlogXpos.le hcon' hA.le
    linarith [le_trans hy2 hyA]
  have hloglogXpos : (0 : ℝ) < Real.log (Real.log X) := Real.log_pos hlogXgt1
  -- `loglog n ≤ logloglog X + log A`
  have hLnpos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos hn1r
  have hchain : Real.log (n : ℝ) ≤ A * Real.log (Real.log X) := by
    have h1 : Real.log (n : ℝ) ≤ Real.log y :=
      Real.log_le_log hnpos (Nat.floor_le hy0)
    have h2 : Real.log y ≤ Real.log ((Real.log X) ^ A) :=
      Real.log_le_log (by linarith) hyA
    rw [Real.log_rpow hlogXpos] at h2
    linarith
  have hloglog : Real.log (Real.log (n : ℝ))
      ≤ Real.log A + Real.log (Real.log (Real.log X)) := by
    have hstep : Real.log (Real.log (n : ℝ)) ≤ Real.log (A * Real.log (Real.log X)) :=
      Real.log_le_log hLnpos hchain
    rwa [Real.log_mul hA.ne' hloglogXpos.ne'] at hstep
  -- Mertens at `n`, then fold the error `C₀/log n ≤ C₀/log 2`
  have hMn := hMert n hn2
  have habs : (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
      ≤ Real.log (Real.log (n : ℝ)) + M + C₀ / Real.log (n : ℝ) := by
    have := (abs_le.mp hMn).2
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have herr : C₀ / Real.log (n : ℝ) ≤ C₀ / Real.log 2 := by
    apply div_le_div_of_nonneg_left hC₀ hlog2pos
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  refine ⟨max (Real.log A + M + C₀ / Real.log 2) 0, le_max_right _ _, ?_⟩
  rw [hsum]
  have hle := le_max_left (Real.log A + M + C₀ / Real.log 2) 0
  linarith [habs, hloglog, herr, hle]

/-- **T-1 (ii) — the out-of-window mass bound (`out_of_window_mass_le`).**  Combining
the tail reduction (`outWindowMass_le_tails`), the proven LOWER tail (`lowerTail_le`,
coefficient `1` on `logloglog X`), and the UPPER tail carried as `hupper` (the o(1)
two-sided-Mertens piece `Σ_{X/y≤p≤X} 1/p → 0`), the mass fits the frozen
`5·logloglog(2X+16)` slack:

  `∃ C ≥ 0, outWindowMass y (X/y) X ≤ 5·logloglog(2X+16) + C`.

**Honesty (freeze's question — answered).**  The dominant tail carries coefficient
`1`; `logloglog X ≤ logloglog(2X+16) ≤ 5·logloglog(2X+16)` (`X ≥ e`), so the slack
absorbs it with a factor `5×` to spare.  The upper tail is the genuine o(1) residual
(a second `mertens_second_sharp` difference), isolated in `hupper`. -/
theorem out_of_window_mass_le {X y A : ℝ} (hX : Real.exp 1 ≤ X) (hA : 0 < A)
    (hy2 : 2 ≤ y) (hyA : y ≤ (Real.log X) ^ A) (hyX : ⌊y⌋₊ ≤ ⌊X⌋₊)
    {Cupper : ℝ} (huppernn : 0 ≤ Cupper)
    (hupper : (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
        if X / y ≤ (p : ℝ) then 1 / (p : ℝ) else 0) ≤ Cupper) :
    ∃ C : ℝ, 0 ≤ C ∧
      outWindowMass y (X / y) X
        ≤ 5 * Real.log (Real.log (Real.log (2 * X + 16))) + C := by
  obtain ⟨Clow, hClow, hlow⟩ := lowerTail_le hX hA hy2 hyA hyX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hred := outWindowMass_le_tails y (X / y) X
  -- the y-regime forces `log X > 1`, hence `loglog X > 0`
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hlogXgt1 : (1 : ℝ) < Real.log X := by
    by_contra hcon
    have hcon' : Real.log X ≤ 1 := not_lt.mp hcon
    have h1 : (Real.log X) ^ A ≤ 1 := Real.rpow_le_one hlogXpos.le hcon' hA.le
    linarith [le_trans hy2 hyA]
  have hloglogXpos : (0 : ℝ) < Real.log (Real.log X) := Real.log_pos hlogXgt1
  -- `logloglog X ≤ logloglog(2X+16)` and the latter `≥ 0`
  have hlogmono : Real.log X ≤ Real.log (2 * X + 16) :=
    Real.log_le_log hXpos (by linarith)
  have hllmono : Real.log (Real.log X) ≤ Real.log (Real.log (2 * X + 16)) :=
    Real.log_le_log hlogXpos hlogmono
  have hmono : Real.log (Real.log (Real.log X))
      ≤ Real.log (Real.log (Real.log (2 * X + 16))) :=
    Real.log_le_log hloglogXpos hllmono
  -- `e^e ≤ 2X+16`, so `logloglog(2X+16) ≥ 0`
  have hL3nn : (0 : ℝ) ≤ Real.log (Real.log (Real.log (2 * X + 16))) := by
    have he1u : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have he1l : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hX' : (2.7182818283 : ℝ) < X := lt_of_lt_of_le he1l hX
    have hexp3eq : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; ring
    have hexp3lt : Real.exp 3 < 2.7182818286 ^ 3 := by rw [hexp3eq]; gcongr
    have hee : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by linarith)
    have hpow : (2.7182818286 : ℝ) ^ 3 < 21 := by norm_num
    have hexpexp : Real.exp (Real.exp 1) ≤ 2 * X + 16 := by
      linarith [hee, hexp3lt, hpow, hX']
    have hlog2X : Real.exp 1 ≤ Real.log (2 * X + 16) :=
      (Real.le_log_iff_exp_le (by linarith)).mpr hexpexp
    have hll1 : (1 : ℝ) ≤ Real.log (Real.log (2 * X + 16)) :=
      (Real.le_log_iff_exp_le (Real.log_pos (by linarith))).mpr hlog2X
    exact Real.log_nonneg hll1
  refine ⟨Clow + Cupper, by linarith, ?_⟩
  linarith [hred, hlow, hupper, hmono, hL3nn]

/-! ## (iii) The frozen N2 floor — NO W -/

/-- **T-1 (iii) — the frozen N2 floor, NO W (`dist_split_A4_N2`).**  The R3.1 floor at
the FROZEN N2 SHAPE (`s8-freeze.md`, R3.1 frozen conclusion), with the window loss `W`
REPLACED by the concrete out-of-window mass via (i)+(ii):

  `𝔻(fgJ f t₀ y Y, costwist t; X)² ≥ (1/32)loglog X − 5·logloglog(2X+16) − C`.

Inputs: `hfloor` the f-floor `(1/16)loglog X ≤ 𝔻(f, costwist(t+t₀); X)²` at the SHIFTED
frequency (established by the caller via the branch-a direct floor or the branch-b
recentering `dist_recenter_sq` — restated at `t+t₀`), and `hmass` the out-of-window
mass bound (discharged by `out_of_window_mass_le`).  The `(1/16) → (1/32)` weakening
uses `loglog X ≥ 0`; the `−5·logloglog(2X+16)` slack absorbs the mass (coefficient
1 ≤ 5, honest — see (ii)).  **No `W`** — the additive supersession is complete. -/
theorem dist_split_A4_N2 {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y t X C : ℝ)
    (hX : Real.exp 1 ≤ X)
    (hfloor : (1 / 16) * Real.log (Real.log X) ≤ pretDistSq f (costwist (t + t₀)) X)
    (hmass : outWindowMass y Y X
        ≤ 5 * Real.log (Real.log (Real.log (2 * X + 16))) + C) :
    (1 / 32) * Real.log (Real.log X)
          - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - C
      ≤ pretDistSq (fgJ f t₀ y Y) (costwist t) X := by
  have hwin := dist_window_restrict hf t₀ y Y t X
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hℓnn : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogX1
  set ℓ := Real.log (Real.log X) with hℓdef
  set L3 := Real.log (Real.log (Real.log (2 * X + 16))) with hL3def
  linarith [hwin, hfloor, hmass, hℓnn]

/-- **T-1 — the assembled W-vanishing floor (`dist_split_A4_N2_windowed`).**  The
full chain (i)+(ii)+(iii) at the seam window `Y = X/y`: `out_of_window_mass_le`
discharges the mass into the frozen `5·logloglog(2X+16)` slack, and `dist_split_A4_N2`
delivers the frozen N2 floor **without any `W`**:

  `∃ C ≥ 0, 𝔻(fgJ f t₀ y (X/y), costwist t; X)²
              ≥ (1/32)loglog X − 5·logloglog(2X+16) − C`.

Everything is discharged except the branch f-floor `hfloor` (from H3's branch-a/b,
restated at the shifted frequency `t+t₀`) and the o(1) upper-tail `hupper` (the
genuine `Σ_{X/y≤p≤X} 1/p → 0` two-sided-Mertens residual).  **The `−W` route is
superseded; `W` is gone from the chain.** -/
theorem dist_split_A4_N2_windowed {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y t : ℝ)
    {X A : ℝ} (hX : Real.exp 1 ≤ X) (hA : 0 < A) (hy2 : 2 ≤ y)
    (hyA : y ≤ (Real.log X) ^ A) (hyX : ⌊y⌋₊ ≤ ⌊X⌋₊)
    {Cupper : ℝ} (huppernn : 0 ≤ Cupper)
    (hupper : (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
        if X / y ≤ (p : ℝ) then 1 / (p : ℝ) else 0) ≤ Cupper)
    (hfloor : (1 / 16) * Real.log (Real.log X) ≤ pretDistSq f (costwist (t + t₀)) X) :
    ∃ C : ℝ, 0 ≤ C ∧
      (1 / 32) * Real.log (Real.log X)
            - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - C
        ≤ pretDistSq (fgJ f t₀ y (X / y)) (costwist t) X := by
  obtain ⟨C, hC, hmass⟩ := out_of_window_mass_le hX hA hy2 hyA hyX huppernn hupper
  exact ⟨C, hC, dist_split_A4_N2 hf t₀ y (X / y) t X C hX hfloor hmass⟩

/-! ## (ii)′ — the UPPER prime tail discharged (HUPPER)

The last residual hypothesis of the landed W-vanishing chain: the `hupper` binder of
`out_of_window_mass_le`/`dist_split_A4_N2_windowed` — the genuine `o(1)` tail
`Σ_{X/y ≤ p ≤ X} 1/p → 0`.  It is discharged here (`upper_tail_le`), making the whole
T-1 chain UNCONDITIONAL above an explicit `A`-dependent threshold
(`dist_split_A4_N2_final`). -/

/-- **HUPPER (analytic core) — threshold + structural log bounds (`upper_tail_analytic`).**
The pure real-analysis half of `upper_tail_le`, split off for the heartbeat budget:
above `X₀ = exp(s₀²)` (the explicit √-device threshold), for `2 ≤ y ≤ (log X)^A`, it
produces `(log X)^A ≤ X`, `20·C₀ + 20 ≤ log X`, `X/y ≥ 4`, and the two structural log
bounds `log ⌊X⌋₊ , log(⌊X/y⌋₊ − 1) ≥ (1/2)·log X` (the `log y = o(log X)` gain). -/
private lemma upper_tail_analytic {A C₀ : ℝ} (hA : 0 < A) (hC₀ : 0 ≤ C₀) :
    ∃ X₀ : ℝ, Real.exp 1 ≤ X₀ ∧ ∀ (X y : ℝ), X₀ ≤ X → 2 ≤ y → y ≤ (Real.log X) ^ A →
      (Real.log X) ^ A ≤ X ∧
      20 * C₀ + 20 ≤ Real.log X ∧
      4 ≤ X / y ∧
      (1 / 2) * Real.log X ≤ Real.log (⌊X⌋₊ : ℝ) ∧
      (1 / 2) * Real.log X ≤ Real.log ((⌊X / y⌋₊ - 1 : ℕ) : ℝ) := by
  have hlog4nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2_07 : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  set c₁ : ℝ := Real.log 4 + Real.log 2 with hc₁def
  have hc₁nn : 0 ≤ c₁ := by rw [hc₁def]; linarith
  set s₀ : ℝ := 8 * A + 2 * c₁ + 5 * C₀ + 10 with hs₀def
  have hs₀ge10 : 10 ≤ s₀ := by rw [hs₀def]; nlinarith [hA.le, hc₁nn, hC₀]
  refine ⟨Real.exp (s₀ ^ 2), Real.exp_le_exp.mpr (by nlinarith [hs₀ge10]), ?_⟩
  intro X y hX hy2 hyA
  have hX0pos : (0 : ℝ) < Real.exp (s₀ ^ 2) := Real.exp_pos _
  have hXpos : 0 < X := lt_of_lt_of_le hX0pos hX
  have hy0 : (0 : ℝ) < y := by linarith
  have hXy_pos : (0 : ℝ) < X / y := div_pos hXpos hy0
  have hLbig : s₀ ^ 2 ≤ Real.log X := by
    have h := Real.log_le_log hX0pos hX; rwa [Real.log_exp] at h
  have hlogXpos : 0 < Real.log X := by nlinarith [hs₀ge10, hLbig]
  have hlogXne : Real.log X ≠ 0 := ne_of_gt hlogXpos
  have hX_big : Real.log X + 1 ≤ X := by
    have h := Real.add_one_le_exp (Real.log X); rwa [Real.exp_log hXpos] at h
  have hs₀geC : 5 * C₀ + 10 ≤ s₀ := by rw [hs₀def]; nlinarith [hA.le, hc₁nn]
  have hlogX_C : 20 * C₀ + 20 ≤ Real.log X := by
    nlinarith [hs₀geC, hC₀, hLbig, sq_nonneg (s₀ - (5 * C₀ + 10))]
  have hlogXge4 : (4 : ℝ) ≤ Real.log X := by linarith [hC₀, hlogX_C]
  -- (⋆′): `A·loglog X + c₁ ≤ (1/2)·log X` via the √-device `log t ≤ 2√t`
  have hstar : A * Real.log (Real.log X) + c₁ ≤ (1 / 2) * Real.log X := by
    set s : ℝ := Real.sqrt (Real.log X) with hsdef
    have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
    have hs_sq : s ^ 2 = Real.log X := Real.sq_sqrt hlogXpos.le
    have hs0_le : s₀ ≤ s := by
      have h1 : Real.sqrt (s₀ ^ 2) ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hLbig
      rwa [Real.sqrt_sq (by linarith [hs₀ge10])] at h1
    have hs1 : 1 ≤ s := by linarith [hs₀ge10]
    have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hlogL_eq : Real.log (Real.log X) = 2 * Real.log s := by
      rw [← hs_sq, Real.log_pow]; push_cast; ring
    have hlogL_le : Real.log (Real.log X) ≤ 2 * s := by rw [hlogL_eq]; linarith
    have hAlogL : A * Real.log (Real.log X) ≤ 2 * A * s := by
      nlinarith [mul_le_mul_of_nonneg_left hlogL_le hA.le]
    have hs_lb : 8 * A + 2 * c₁ + 1 ≤ s := by linarith [hs0_le, hs₀def, hC₀]
    have hquad : 8 * A * s + 2 * c₁ ≤ s ^ 2 := by
      nlinarith [hs_lb, hs1, hc₁nn, hA.le,
        mul_nonneg hc₁nn (by linarith [hs1] : (0 : ℝ) ≤ s - 1),
        mul_nonneg hA.le hs_nn, mul_le_mul_of_nonneg_left hs_lb hs_nn]
    nlinarith [hAlogL, hquad, hs_sq, mul_nonneg hA.le hs_nn]
  have hlogy : Real.log y ≤ A * Real.log (Real.log X) := by
    have h1 : Real.log y ≤ Real.log ((Real.log X) ^ A) := Real.log_le_log hy0 hyA
    rwa [Real.log_rpow hlogXpos] at h1
  have hrpownn : 0 ≤ (Real.log X) ^ A := Real.rpow_nonneg hlogXpos.le A
  have hrpowpos : 0 < (Real.log X) ^ A := Real.rpow_pos_of_pos hlogXpos A
  have hII4 : 4 * (Real.log X) ^ A ≤ X := by
    have hlhs_pos : 0 < 4 * (Real.log X) ^ A := by linarith
    have hlog_le : Real.log (4 * (Real.log X) ^ A) ≤ Real.log X := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hrpowpos), Real.log_rpow hlogXpos]
      linarith [hstar, hc₁def, hlog2nn, hlogXpos]
    calc 4 * (Real.log X) ^ A
        = Real.exp (Real.log (4 * (Real.log X) ^ A)) := (Real.exp_log hlhs_pos).symm
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hlog_le
      _ = X := Real.exp_log hXpos
  have hII : (Real.log X) ^ A ≤ X := by linarith
  have hr4 : (4 : ℝ) ≤ X / y := by
    rw [le_div_iff₀ hy0]
    calc (4 : ℝ) * y ≤ 4 * (Real.log X) ^ A := by nlinarith [hyA, hrpownn]
      _ ≤ X := hII4
  set N : ℕ := ⌊X⌋₊ with hNdef
  set m : ℕ := ⌊X / y⌋₊ with hmdef
  have hm_ge4 : 4 ≤ m := by rw [hmdef]; apply Nat.le_floor; push_cast; exact hr4
  have hyX : X / y ≤ X := div_le_self hXpos.le (by linarith)
  have hmN : m ≤ N := by rw [hmdef, hNdef]; exact Nat.floor_le_floor hyX
  have hN_ge4 : 4 ≤ N := le_trans hm_ge4 hmN
  have hmmr_eq : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
  have hN_ge : X / 2 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one X; rw [← hNdef] at h; linarith [hX_big, hlogXge4]
  have hlogN_half : (1 / 2) * Real.log X ≤ Real.log (N : ℝ) := by
    have h1 : Real.log (X / 2) ≤ Real.log (N : ℝ) := Real.log_le_log (by linarith) hN_ge
    rw [Real.log_div (ne_of_gt hXpos) (by norm_num)] at h1
    linarith [hlog2_07, hlogXge4]
  have hmmr_ge : (X / y) / 2 ≤ ((m - 1 : ℕ) : ℝ) := by
    rw [hmmr_eq]
    have h := Nat.lt_floor_add_one (X / y); rw [← hmdef] at h; linarith [hr4]
  have hlogmm_half : (1 / 2) * Real.log X ≤ Real.log ((m - 1 : ℕ) : ℝ) := by
    have h1 : Real.log ((X / y) / 2) ≤ Real.log ((m - 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hmmr_ge
    rw [Real.log_div (ne_of_gt hXy_pos) (by norm_num),
      Real.log_div (ne_of_gt hXpos) (ne_of_gt hy0)] at h1
    linarith [hlogy, hstar, hc₁def, hlog4nn]
  exact ⟨hII, hlogX_C, hr4, hlogN_half, hlogmm_half⟩

/-- **HUPPER — the upper prime tail `o(1)` bound (`upper_tail_le`).**  For `y ≤ (log X)^A`,
the upper prime tail `Σ_{X/y ≤ p ≤ X} 1/p` is at most `1` once `X` exceeds an explicit
`A`-dependent threshold `X₀`.  (It also carries `(log X)^A ≤ X`, the `⌊y⌋₊ ≤ ⌊X⌋₊`
feeder for the assembled chain.)  This is the genuine two-sided-`mertens_second_sharp`
residual that `out_of_window_mass_le` isolated in `hupper`.

Route: the tail is `≤ S(N) − S(m−1)` with `N = ⌊X⌋₊`, `m = ⌊X/y⌋₊` (a subset bound +
the exact prime-filter identity), and `mertens_second_sharp` at both ends gives
`≤ (loglog N − loglog(m−1)) + C/log N + C/log(m−1)`.  The structural key
(`upper_tail_analytic`) is `log(m−1) ≥ (1/2)·log X` — from `X/y ≥ 4` and
`log y ≤ A·loglog X = o(log X)` — whence `loglog(m−1) ≥ loglog X − log 2`, so the leading
loglog difference is `≤ log 2 < 1`, and each `C/log`-term is `≤ 1/10`; total
`≤ log 2 + 1/5 < 1`. -/
theorem upper_tail_le {A : ℝ} (hA : 0 < A) :
    ∃ X₀ : ℝ, Real.exp 1 ≤ X₀ ∧ ∀ (X y : ℝ), X₀ ≤ X → 2 ≤ y → y ≤ (Real.log X) ^ A →
      (Real.log X) ^ A ≤ X ∧
      (∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
          if X / y ≤ (p : ℝ) then 1 / (p : ℝ) else 0) ≤ 1 := by
  obtain ⟨M, C₀, hC₀, hMert⟩ := Salt.Mertens.mertens_second_sharp
  obtain ⟨X₀, hX₀e, hana⟩ := upper_tail_analytic hA hC₀
  have hlog2_07 : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  refine ⟨X₀, hX₀e, fun X y hX hy2 hyA => ?_⟩
  obtain ⟨hII, hlogX_C, hr4, hlogN_half, hlogmm_half⟩ := hana X y hX hy2 hyA
  refine ⟨hII, ?_⟩
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) (le_trans hX₀e hX)
  have hy0 : (0 : ℝ) < y := by linarith
  have hXy_pos : (0 : ℝ) < X / y := div_pos hXpos hy0
  have hlogXpos : 0 < Real.log X := by linarith [hlogX_C, hC₀]
  have hlogXne : Real.log X ≠ 0 := ne_of_gt hlogXpos
  set N : ℕ := ⌊X⌋₊ with hNdef
  set m : ℕ := ⌊X / y⌋₊ with hmdef
  have hm_ge4 : 4 ≤ m := by rw [hmdef]; apply Nat.le_floor; push_cast; exact hr4
  have hyX : X / y ≤ X := div_le_self hXpos.le (by linarith)
  have hmN : m ≤ N := by rw [hmdef, hNdef]; exact Nat.floor_le_floor hyX
  have hN_ge4 : 4 ≤ N := le_trans hm_ge4 hmN
  have hMertN := hMert N (by omega)
  have hMertm := hMert (m - 1) (by omega)
  set S_N : ℝ := ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / p with hSNdef
  set S_m : ℝ := ∑ p ∈ (Finset.range ((m - 1) + 1)).filter Nat.Prime, (1 : ℝ) / p with hSmdef
  set T_u : ℝ := ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      (if X / y ≤ (p : ℝ) then 1 / (p : ℝ) else 0) with hTudef
  set T_m : ℝ := ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      (if m ≤ p then (1 : ℝ) / p else 0) with hTmdef
  set Low : ℝ := ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      (if p < m then (1 : ℝ) / p else 0) with hLowdef
  -- step A: `T_u ≤ T_m` (`X/y ≤ p ⟹ m ≤ p`, else `0 ≤ ·`)
  have hstepA : T_u ≤ T_m := by
    rw [hTudef, hTmdef]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hppos : (0 : ℝ) < (p : ℝ) := by
      have := (Finset.mem_filter.mp hp).2; exact_mod_cast this.pos
    by_cases hcond : X / y ≤ (p : ℝ)
    · have hmp : m ≤ p := by
        have h1 : (m : ℝ) ≤ X / y := by rw [hmdef]; exact Nat.floor_le hXy_pos.le
        exact_mod_cast le_trans h1 hcond
      exact le_of_eq (by rw [if_pos hcond, if_pos hmp])
    · rw [if_neg hcond]; split_ifs <;> positivity
  -- step B: `T_m + Low = S_N` (complementary indicators)
  have hB : T_m + Low = S_N := by
    rw [hTmdef, hLowdef, ← Finset.sum_add_distrib, hSNdef]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rcases Nat.lt_or_ge p m with h | h
    · rw [if_neg (by omega), if_pos h]; ring
    · rw [if_pos h, if_neg (by omega)]; ring
  -- `Low = S(m−1)` (the exact prime-filter identity)
  have hLoweq : Low = S_m := by
    rw [hLowdef, hSmdef, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hq⟩, hqm⟩; exact ⟨by omega, hq⟩
    · rintro ⟨hqm, hq⟩; exact ⟨⟨by omega, hq⟩, by omega⟩
  have hTm_eq : T_m = S_N - S_m := by rw [hLoweq] at hB; linarith
  -- Mertens two-sided at `N` and `m−1`
  have hSN_ub : S_N ≤ Real.log (Real.log (N : ℝ)) + M + C₀ / Real.log (N : ℝ) := by
    have h := (abs_le.mp hMertN).2; linarith
  have hSm_lb : Real.log (Real.log ((m - 1 : ℕ) : ℝ)) + M - C₀ / Real.log ((m - 1 : ℕ) : ℝ)
      ≤ S_m := by
    have h := (abs_le.mp hMertm).1; linarith
  have hNr_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogmm_pos : 0 < Real.log ((m - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m - 1 by omega))
  -- `loglog N ≤ loglog X` and `loglog(m−1) ≥ loglog X − log 2`
  have hℓN_le : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log X) := by
    refine Real.log_le_log hlogN_pos (Real.log_le_log hNr_pos ?_)
    rw [hNdef]; exact Nat.floor_le hXpos.le
  have hℓm_ge : Real.log (Real.log X) - Real.log 2
      ≤ Real.log (Real.log ((m - 1 : ℕ) : ℝ)) := by
    have h1 : Real.log ((1 / 2) * Real.log X) ≤ Real.log (Real.log ((m - 1 : ℕ) : ℝ)) :=
      Real.log_le_log (by linarith) hlogmm_half
    rw [Real.log_mul (by norm_num) hlogXne,
      show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h1
    linarith
  have hℓdiff : Real.log (Real.log (N : ℝ)) - Real.log (Real.log ((m - 1 : ℕ) : ℝ))
      ≤ Real.log 2 := by linarith [hℓN_le, hℓm_ge]
  -- each Mertens error is `≤ 1/10` (from `log ≥ (1/2)log X ≥ 10·C₀ + 10`)
  have herrN : C₀ / Real.log (N : ℝ) ≤ 1 / 10 := by
    rw [div_le_iff₀ hlogN_pos]; linarith [hlogN_half, hlogX_C]
  have herrm : C₀ / Real.log ((m - 1 : ℕ) : ℝ) ≤ 1 / 10 := by
    rw [div_le_iff₀ hlogmm_pos]; linarith [hlogmm_half, hlogX_C]
  -- assemble: `T_u ≤ (ℓN − ℓm) + errN + errm ≤ log 2 + 1/5 < 1`
  have hTu_SN : T_u ≤ S_N - S_m := le_trans hstepA (le_of_eq hTm_eq)
  linarith [hTu_SN, hSN_ub, hSm_lb, hℓdiff, herrN, herrm, hlog2_07]

/-- **HUPPER discharged — the UNCONDITIONAL W-vanishing floor (`dist_split_A4_N2_final`).**
The assembled T-1 chain with the last residual hypothesis `hupper` DISCHARGED (via
`upper_tail_le`): above an explicit `A`-dependent threshold `X₀ ≥ e`, for `2 ≤ y ≤ (log X)^A`
and the branch `f`-floor at the shifted frequency `t+t₀` (hypothesis `hfloor`, from H3's
branch-a/b), the frozen N2 floor holds with NO `W` and NO named tail hypothesis:

  `∃ C ≥ 0, 𝔻(fgJ f t₀ y (X/y), costwist t; X)²
              ≥ (1/32)loglog X − 5·logloglog(2X+16) − C`.

The only remaining hypothesis is the branch `f`-floor `hfloor`; the out-of-window prime
mass (both tails) is fully discharged.  **T-1 is unconditional.** -/
theorem dist_split_A4_N2_final {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y t : ℝ) {A : ℝ}
    (hA : 0 < A) :
    ∃ X₀ : ℝ, Real.exp 1 ≤ X₀ ∧ ∀ (X : ℝ), X₀ ≤ X → 2 ≤ y → y ≤ (Real.log X) ^ A →
      (1 / 16) * Real.log (Real.log X) ≤ pretDistSq f (costwist (t + t₀)) X →
      ∃ C : ℝ, 0 ≤ C ∧
        (1 / 32) * Real.log (Real.log X)
              - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - C
          ≤ pretDistSq (fgJ f t₀ y (X / y)) (costwist t) X := by
  obtain ⟨X₀, hX₀e, hut⟩ := upper_tail_le hA
  refine ⟨X₀, hX₀e, fun X hX hy2 hyA hfloor => ?_⟩
  have hXe : Real.exp 1 ≤ X := le_trans hX₀e hX
  obtain ⟨hyleX, hupper⟩ := hut X y hX hy2 hyA
  have hyX : ⌊y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor (le_trans hyA hyleX)
  exact dist_split_A4_N2_windowed hf t₀ y t hXe hA hy2 hyA hyX
    (by norm_num : (0 : ℝ) ≤ 1) hupper hfloor

end Salt.MR
