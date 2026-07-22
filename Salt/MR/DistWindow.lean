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

end Salt.MR
