/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The barely-divergent decrement clears `log 2` (the entropy-decrement floor)

The last input of the regime instantiation (`RegimeInst.lean`, field `hJcon`):
`∃ J, log 2 < towerDropSum 2 1 4·10⁶ J`.  The telescoped decrement
`Σ_{j<J} 1/(2 log H_j · logloglog H_j)` diverges (barely), so it crosses any
constant, in particular `log 2`.  Route:

* `tower_log_upper` — by induction, `log H_j ≤ 32·(j+2)·log(j+2)` (the increment
  `log⌊2 L_j M_j⌋ ≤ log 2 + 2 log L_j` closes against `32 log(j+3)`).
* the abstract divergence `Σ 1/(n log n loglog n) = ∞` via Cauchy condensation.
* the per-summand comparison `1/(2 L_j M_j) ≥ (1/128)/((j+2)log(j+2)loglog(j+2))`
  for `j ≥ 30`, transferring the divergence to `towerDropSum`.
* extraction: nonneg + non-summable ⇒ partial sums `→ ∞` ⇒ some `J` clears `log 2`.

Feeds `regime_exists_of_dropSum_exists`, discharging the anti-vacuity of
`ChowlaRegime` unconditionally (`chowlaRegime_exists`).
-/
import Salt.Entropy.Chowla.RegimeInst

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### Piece 1 — the upper tower bound `log H_j ≤ 32(j+2)log(j+2)` -/

/-- The tower's logarithm grows at most like `32·(j+2)·log(j+2)`.  Proved by
    induction: `log H_{j+1} = log H_j + log⌊2 L_j M_j⌋ ≤ log H_j + log 2 +
    2 log L_j`, and `log L_j ≤ log 32 + 2 log(j+2)`, so the increment is
    `≤ log 2 + 2 log 32 + 4 log(j+2) ≤ 32 log(j+3)`, which is `≤` the gap
    `32[(j+3)log(j+3) - (j+2)log(j+2)]`. -/
theorem tower_log_upper (j : ℕ) :
    Real.log (chowlaTower 2 1 4000000 j : ℝ)
      ≤ 32 * ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) := by
  induction j with
  | zero =>
    have h1 : (chowlaTower 2 1 4000000 0 : ℝ) = 4000000 := by
      norm_num [chowlaTower]
    rw [h1]
    have hlog2pos : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hb : (4000000 : ℝ) ≤ (2 : ℝ) ^ 22 := by norm_num
    calc Real.log 4000000
        ≤ Real.log ((2 : ℝ) ^ 22) := by
          apply Real.log_le_log (by norm_num) hb
      _ = 22 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 32 * (((0 : ℕ) : ℝ) + 2) * Real.log (((0 : ℕ) : ℝ) + 2) := by
          have : (32 : ℝ) * (((0 : ℕ) : ℝ) + 2) * Real.log (((0 : ℕ) : ℝ) + 2)
              = 64 * Real.log 2 := by norm_num
          rw [this]; linarith [hlog2pos]
  | succ j ih =>
    set Hj := chowlaTower 2 1 4000000 j with hHjdef
    have hge : 4000000 ≤ Hj := chowlaTower_two_one_base_le j
    have hHjpos : (0 : ℝ) < (Hj : ℝ) := by
      have : (4000000 : ℝ) ≤ (Hj : ℝ) := by exact_mod_cast hge
      linarith
    obtain ⟨hL15, hM12⟩ := tower_log_bounds hge
    set L := Real.log (Hj : ℝ) with hLdef
    set M := Real.log (Real.log L) with hMdef
    -- positivity facts
    have hLpos : (0 : ℝ) < L := by linarith [hL15]
    have hlogL_pos : (0 : ℝ) < Real.log L := by
      have : Real.log 15 ≤ Real.log L := Real.log_le_log (by norm_num) hL15
      have h15 : (0 : ℝ) < Real.log 15 := Real.log_pos (by norm_num)
      linarith
    have hMpos : (0 : ℝ) < M := by linarith [hM12]
    -- the multiplier `m = ⌊2 L M⌋₊`
    have hm2 : 2 ≤ ⌊(2 : ℝ) * L * M⌋₊ := by
      have := tower_mult_ge_two (show (2 : ℕ) ≤ 2 from le_refl 2) hge
      -- normalise the `((2:ℕ):ℝ)` coefficient
      simpa [hLdef, hMdef] using this
    set m := ⌊(2 : ℝ) * L * M⌋₊ with hmdef
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      linarith
    have h2LM_pos : (0 : ℝ) < 2 * L * M := by positivity
    have hm_le : (m : ℝ) ≤ 2 * L * M := by
      have := Nat.floor_le (le_of_lt h2LM_pos)
      simpa [hmdef] using this
    -- succ-step: log H_{j+1} = L + log m
    have hsucc : Real.log (chowlaTower 2 1 4000000 (j + 1) : ℝ) = L + Real.log (m : ℝ) := by
      rw [chowlaTower_succ, ← hHjdef, Nat.cast_ofNat, ← hLdef, ← hMdef, ← hmdef,
        Nat.cast_mul, Real.log_mul (ne_of_gt hHjpos) (ne_of_gt hmpos), ← hLdef]
    rw [hsucc]
    -- bound log m ≤ log 2 + 2 log L
    have hlogm : Real.log (m : ℝ) ≤ Real.log 2 + 2 * Real.log L := by
      have step1 : Real.log (m : ℝ) ≤ Real.log (2 * L * M) :=
        Real.log_le_log hmpos hm_le
      -- 2 L M ≤ 2 L^2
      have hM_le_logL : M ≤ Real.log L := by
        rw [hMdef]; exact Real.log_le_self (le_of_lt hlogL_pos)
      have hlogL_le_L : Real.log L ≤ L := Real.log_le_self (le_of_lt hLpos)
      have hML : M ≤ L := le_trans hM_le_logL hlogL_le_L
      have hchain : 2 * L * M ≤ 2 * L ^ 2 := by nlinarith [hLpos, hML]
      have step2 : Real.log (2 * L * M) ≤ Real.log (2 * L ^ 2) :=
        Real.log_le_log h2LM_pos hchain
      have step3 : Real.log (2 * L ^ 2) = Real.log 2 + 2 * Real.log L := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (ne_of_gt hLpos)), Real.log_pow]
        push_cast; ring
      linarith [step1, step2, step3]
    -- bound log L ≤ log 32 + 2 log(j+2)
    have hlogL_bnd : Real.log L ≤ Real.log 32 + 2 * Real.log ((j : ℝ) + 2) := by
      have hlogj_le : Real.log ((j : ℝ) + 2) ≤ (j : ℝ) + 2 := Real.log_le_self (by positivity)
      have hP0 : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
      have hstep : 32 * ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2)
          ≤ 32 * ((j : ℝ) + 2) ^ 2 := by
        nlinarith [hlogj_le, hP0]
      have ha : L ≤ 32 * ((j : ℝ) + 2) ^ 2 := le_trans ih hstep
      have hb : Real.log L ≤ Real.log (32 * ((j : ℝ) + 2) ^ 2) :=
        Real.log_le_log hLpos ha
      have hc : Real.log (32 * ((j : ℝ) + 2) ^ 2)
          = Real.log 32 + 2 * Real.log ((j : ℝ) + 2) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (ne_of_gt (show (0:ℝ) < (j:ℝ)+2 by
          positivity))), Real.log_pow]
        push_cast; ring
      linarith
    -- assemble the increment inequality
    have hlog32 : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num, Real.log_pow]; push_cast; ring
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    -- gap: 32(j+3)log(j+3) ≥ 32(j+2)log(j+2) + 32 log(j+3)
    have hpq : Real.log ((j : ℝ) + 2) ≤ Real.log ((j : ℝ) + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hq1 : (1 : ℝ) ≤ Real.log ((j : ℝ) + 3) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9; linarith
    have hPnn : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
    have hgap : 32 * ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) + 32 * Real.log ((j : ℝ) + 3)
        ≤ 32 * (((j + 1 : ℕ) : ℝ) + 2) * Real.log (((j + 1 : ℕ) : ℝ) + 2) := by
      have hcast : ((j + 1 : ℕ) : ℝ) + 2 = (j : ℝ) + 3 := by push_cast; ring
      rw [hcast]
      nlinarith [hpq, hPnn, hq1]
    -- final chain
    have hincr : Real.log 2 + 2 * Real.log L ≤ 32 * Real.log ((j : ℝ) + 3) := by
      have h11 : Real.log 2 + 2 * Real.log 32 ≤ 11 := by
        rw [hlog32]; linarith [hlog2_le1]
      linarith [hlogL_bnd, hpq, hq1, h11]
    -- combine: L + log m ≤ (32(j+2)log(j+2)) + (log2 + 2 log L)
    calc L + Real.log (m : ℝ)
        ≤ 32 * ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) + (Real.log 2 + 2 * Real.log L) := by
          linarith [ih, hlogm]
      _ ≤ 32 * ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) + 32 * Real.log ((j : ℝ) + 3) := by
          linarith [hincr]
      _ ≤ 32 * (((j + 1 : ℕ) : ℝ) + 2) * Real.log (((j + 1 : ℕ) : ℝ) + 2) := hgap

/-! ### Piece 3 — plumbing for non-summability via condensation -/

/-- Non-summability transfers across a tail-equality `g = h` on `[N, ∞)`. -/
private lemma not_summable_of_eventually_eq {g h : ℕ → ℝ} (N : ℕ)
    (hgh : ∀ n, N ≤ n → g n = h n) (hg : ¬ Summable g) : ¬ Summable h := by
  intro hsum
  apply hg
  rw [← summable_nat_add_iff N] at hsum ⊢
  exact (summable_congr (fun n => hgh (n + N) (Nat.le_add_left N n))).mpr hsum

/-- Non-summability transfers up an eventual pointwise bound `a ≤ b` on `[N, ∞)`. -/
private lemma not_summable_of_eventually_le {a b : ℕ → ℝ} (N : ℕ)
    (ha : ∀ n, N ≤ n → 0 ≤ a n) (hab : ∀ n, N ≤ n → a n ≤ b n)
    (hna : ¬ Summable a) : ¬ Summable b := by
  intro hb
  apply hna
  rw [← summable_nat_add_iff N] at hb ⊢
  exact hb.of_nonneg_of_le (fun n => ha (n + N) (Nat.le_add_left N n))
    (fun n => hab (n + N) (Nat.le_add_left N n))

/-- Contrapositive of Cauchy condensation (`summable_condensed_iff_of_nonneg`). -/
private lemma not_summable_of_condensed {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m)
    (hcond : ¬ Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) : ¬ Summable f :=
  fun hf => hcond ((summable_condensed_iff_of_nonneg h_nonneg h_mono).mpr hf)

/-! ### Piece 3a — `Σ 1/(n log n)` diverges (one condensation to the harmonic series) -/

/-- The series `Σ 1/(n log n)` is not summable.  Cauchy condensation sends it to
    `Σ 2ᵏ/(2ᵏ·k log 2) = Σ 1/(k log 2) ≥ Σ 1/k`, the harmonic series. -/
lemma not_summable_one_div_nat_log :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) := by
  set f : ℕ → ℝ :=
    fun n => 1 / (((max n 2 : ℕ) : ℝ) * Real.log ((max n 2 : ℕ) : ℝ)) with hf
  have hden : ∀ m : ℕ, 2 ≤ m → 0 < ((m : ℝ) * Real.log m) := by
    intro m hm
    have h1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    exact mul_pos (by linarith) (Real.log_pos h1)
  have hmax : ∀ n : ℕ, 2 ≤ max n 2 := fun n => le_max_right n 2
  have hfnonneg : ∀ n, 0 ≤ f n := by
    intro n
    simp only [hf]
    exact one_div_nonneg.mpr (le_of_lt (hden _ (hmax n)))
  have hfmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n _ hmn
    simp only [hf]
    have hab : (max m 2 : ℕ) ≤ max n 2 := max_le_max hmn le_rfl
    have h2m : (2 : ℝ) ≤ ((max m 2 : ℕ) : ℝ) := by exact_mod_cast hmax m
    have hcast : ((max m 2 : ℕ) : ℝ) ≤ ((max n 2 : ℕ) : ℝ) := by exact_mod_cast hab
    have hlogle : Real.log ((max m 2 : ℕ) : ℝ) ≤ Real.log ((max n 2 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hcast
    have hlognn : 0 ≤ Real.log ((max m 2 : ℕ) : ℝ) := Real.log_nonneg (by linarith)
    exact one_div_le_one_div_of_le (hden _ (hmax m))
      (mul_le_mul hcast hlogle hlognn (by linarith))
  refine not_summable_of_eventually_eq (g := f) 2 (fun n hn => ?_) ?_
  · simp only [hf, max_eq_left hn]
  · apply not_summable_of_condensed hfnonneg hfmono
    refine not_summable_of_eventually_le 1 (a := fun k => 1 / (k : ℝ))
      (fun k _ => by positivity) (fun k hk => ?_) Real.not_summable_one_div_natCast
    have h2 : (2 : ℕ) ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hval : (2 : ℝ) ^ k * f (2 ^ k) = 1 / ((k : ℝ) * Real.log 2) := by
      simp only [hf, max_eq_left h2, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
      have hl2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
      have h2kne : (2 : ℝ) ^ k ≠ 0 := ne_of_gt h2kpos
      field_simp
    rw [hval]
    exact one_div_le_one_div_of_le (mul_pos hkpos hlog2) (by nlinarith [hlog2le, hkpos])

/-! ### Piece 3b — `Σ 1/(n log n loglog n)` diverges (condensation onto Piece 3a) -/

/-- The barely-divergent iterated-log series `Σ 1/(n log n loglog n)` is not
    summable.  Condensation sends it to `Σ 1/(k log 2 · log(k log 2))`, which
    dominates `Σ 1/(k log k)` (`not_summable_one_div_nat_log`). -/
lemma not_summable_one_div_nat_loglog :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log n * Real.log (Real.log n))) := by
  set f : ℕ → ℝ := fun n => 1 / (((max n 16 : ℕ) : ℝ) * Real.log ((max n 16 : ℕ) : ℝ)
      * Real.log (Real.log ((max n 16 : ℕ) : ℝ))) with hf
  have hmax : ∀ n : ℕ, 16 ≤ max n 16 := fun n => le_max_right n 16
  have hlogpos : ∀ m : ℕ, 16 ≤ m → 1 < Real.log m := by
    intro m hm
    have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hllpos : ∀ m : ℕ, 16 ≤ m → 0 < Real.log (Real.log m) :=
    fun m hm => Real.log_pos (hlogpos m hm)
  have hden : ∀ m : ℕ, 16 ≤ m → 0 < ((m : ℝ) * Real.log m * Real.log (Real.log m)) := by
    intro m hm
    have h0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact mul_pos (mul_pos h0 (by linarith [hlogpos m hm])) (hllpos m hm)
  have hklog1 : ∀ k : ℕ, 4 ≤ k → 1 < (k : ℝ) * Real.log 2 := by
    intro k hk
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hl2 : (1 : ℝ) / 4 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
    calc (1 : ℝ) = 4 * (1 / 4) := by norm_num
      _ < 4 * Real.log 2 := by linarith [hl2]
      _ ≤ (k : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hkR (le_of_lt hlog2pos)
  have hfnonneg : ∀ n, 0 ≤ f n := fun n => by
    simp only [hf]; exact one_div_nonneg.mpr (le_of_lt (hden _ (hmax n)))
  have hfmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n _ hmn
    simp only [hf]
    have hab : (max m 16 : ℕ) ≤ max n 16 := max_le_max hmn le_rfl
    have h16m : (16 : ℝ) ≤ ((max m 16 : ℕ) : ℝ) := by exact_mod_cast hmax m
    have hcast : ((max m 16 : ℕ) : ℝ) ≤ ((max n 16 : ℕ) : ℝ) := by exact_mod_cast hab
    have hlogm_pos : 0 < Real.log ((max m 16 : ℕ) : ℝ) := by linarith [hlogpos _ (hmax m)]
    have hlogab : Real.log ((max m 16 : ℕ) : ℝ) ≤ Real.log ((max n 16 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hcast
    have hllab : Real.log (Real.log ((max m 16 : ℕ) : ℝ))
        ≤ Real.log (Real.log ((max n 16 : ℕ) : ℝ)) := Real.log_le_log hlogm_pos hlogab
    have hllnn : 0 ≤ Real.log (Real.log ((max m 16 : ℕ) : ℝ)) := le_of_lt (hllpos _ (hmax m))
    have hstep1 : ((max m 16 : ℕ) : ℝ) * Real.log ((max m 16 : ℕ) : ℝ)
        ≤ ((max n 16 : ℕ) : ℝ) * Real.log ((max n 16 : ℕ) : ℝ) :=
      mul_le_mul hcast hlogab (le_of_lt hlogm_pos) (by linarith)
    have hstep1nn : 0 ≤ ((max m 16 : ℕ) : ℝ) * Real.log ((max m 16 : ℕ) : ℝ) :=
      mul_nonneg (by linarith) (le_of_lt hlogm_pos)
    have hdenle : ((max m 16 : ℕ) : ℝ) * Real.log ((max m 16 : ℕ) : ℝ)
          * Real.log (Real.log ((max m 16 : ℕ) : ℝ))
        ≤ ((max n 16 : ℕ) : ℝ) * Real.log ((max n 16 : ℕ) : ℝ)
          * Real.log (Real.log ((max n 16 : ℕ) : ℝ)) :=
      mul_le_mul hstep1 hllab hllnn (by linarith)
    exact one_div_le_one_div_of_le (hden _ (hmax m)) hdenle
  refine not_summable_of_eventually_eq (g := f) 16 (fun n hn => ?_) ?_
  · simp only [hf, max_eq_left hn]
  · apply not_summable_of_condensed hfnonneg hfmono
    refine not_summable_of_eventually_le 4 (a := fun k => 1 / ((k : ℝ) * Real.log k))
      (fun k hk => ?_) (fun k hk => ?_) not_summable_one_div_nat_log
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg hk1))
    · have h16 : (16 : ℕ) ≤ 2 ^ k := by
        calc (16 : ℕ) = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hX_pos : 0 < Real.log ((k : ℝ) * Real.log 2) := Real.log_pos (hklog1 k hk)
      have hval : (2 : ℝ) ^ k * f (2 ^ k)
          = 1 / ((k : ℝ) * Real.log 2 * Real.log ((k : ℝ) * Real.log 2)) := by
        simp only [hf, max_eq_left h16, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        have h2kne : (2 : ℝ) ^ k ≠ 0 := by positivity
        have hAne : (k : ℝ) * Real.log 2 ≠ 0 := ne_of_gt (mul_pos hkpos hlog2)
        have hXne : Real.log ((k : ℝ) * Real.log 2) ≠ 0 := ne_of_gt hX_pos
        field_simp
      have hcmp : (k : ℝ) * Real.log 2 * Real.log ((k : ℝ) * Real.log 2)
          ≤ (k : ℝ) * Real.log k := by
        have hlog2le1 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
        have hkl2_le_k : (k : ℝ) * Real.log 2 ≤ (k : ℝ) := by
          nlinarith [hlog2le1, hkpos,
            mul_nonneg (le_of_lt hkpos) (by linarith [hlog2le1] : (0 : ℝ) ≤ 1 - Real.log 2)]
        have hXle : Real.log ((k : ℝ) * Real.log 2) ≤ Real.log k :=
          Real.log_le_log (mul_pos hkpos hlog2) hkl2_le_k
        have h1 : Real.log 2 * Real.log ((k : ℝ) * Real.log 2) ≤ Real.log k := by
          nlinarith [hlog2le1, hX_pos.le, hXle,
            mul_nonneg (by linarith [hlog2le1] : (0 : ℝ) ≤ 1 - Real.log 2) hX_pos.le]
        nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt hkpos)]
      rw [hval]
      exact one_div_le_one_div_of_le (mul_pos (mul_pos hkpos hlog2) hX_pos) hcmp

/-! ### Piece 2 — the per-summand comparison to the abstract series -/

/-- Each tower decrement summand `1/(2 log H_j · logloglog H_j)` dominates
    `(1/128)/((j+2)log(j+2)loglog(j+2))` for `j ≥ 30`.  Uses the Piece-1 upper
    bound `log H_j ≤ 32(j+2)log(j+2)` and `logloglog H_j ≤ 2·loglog(j+2)`. -/
lemma summand_lower (j : ℕ) (hj : 30 ≤ j) :
    (1 / 128 : ℝ) * (1 / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)
        * Real.log (Real.log ((j + 2 : ℕ) : ℝ))))
      ≤ 1 / (2 * Real.log (chowlaTower 2 1 4000000 j : ℝ)
          * Real.log (Real.log (Real.log (chowlaTower 2 1 4000000 j : ℝ)))) := by
  have hPeq : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
  rw [hPeq]
  set P : ℝ := (j : ℝ) + 2 with hPdef
  have hjR : (30 : ℝ) ≤ j := by exact_mod_cast hj
  have hP32 : (32 : ℝ) ≤ P := by rw [hPdef]; linarith
  have hPpos : (0 : ℝ) < P := by linarith
  have hp_pos : 0 < Real.log P := Real.log_pos (by linarith)
  set p : ℝ := Real.log P with hpdef
  have hp3 : (3 : ℝ) ≤ p := by
    rw [hpdef]
    have h32 : Real.log 32 ≤ Real.log P := Real.log_le_log (by norm_num) hP32
    have hlog32_ge3 : (3 : ℝ) ≤ Real.log 32 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_gt_d9]
    linarith
  have hq_pos : 0 < Real.log p := Real.log_pos (by linarith)
  set q : ℝ := Real.log p with hqdef
  have hge : 4000000 ≤ chowlaTower 2 1 4000000 j := chowlaTower_two_one_base_le j
  obtain ⟨hL15, hM12⟩ := tower_log_bounds hge
  set L : ℝ := Real.log (chowlaTower 2 1 4000000 j : ℝ) with hLdef
  set M : ℝ := Real.log (Real.log (Real.log (chowlaTower 2 1 4000000 j : ℝ))) with hMdef
  have hLpos : 0 < L := by linarith [hL15]
  have hMpos : 0 < M := by linarith [hM12]
  have hlogL_pos : 0 < Real.log L := by
    have : Real.log 15 ≤ Real.log L := Real.log_le_log (by norm_num) hL15
    linarith [Real.log_pos (show (1 : ℝ) < 15 by norm_num)]
  have hUp : L ≤ 32 * P * p := by
    have h := tower_log_upper j
    rw [← hLdef, ← hPdef, ← hpdef] at h
    exact h
  -- the key: M ≤ 2 q
  have h32Pp_pos : (0 : ℝ) < 32 * P * p := mul_pos (mul_pos (by norm_num) hPpos) hp_pos
  have hlog32Pp : Real.log (32 * P * p) ≤ 3 * p := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hPpos)) (ne_of_gt hp_pos),
      Real.log_mul (by norm_num) (ne_of_gt hPpos), ← hpdef, ← hqdef]
    have hlog32_le_p : Real.log 32 ≤ p := by
      rw [hpdef]; exact Real.log_le_log (by norm_num) hP32
    have hq_le_p : q ≤ p := by rw [hqdef]; exact Real.log_le_self (le_of_lt hp_pos)
    linarith
  have hM_le : M ≤ 2 * q := by
    have hMeq : M = Real.log (Real.log L) := by rw [hMdef, hLdef]
    rw [hMeq]
    have h1 : Real.log (Real.log L) ≤ Real.log (Real.log (32 * P * p)) :=
      Real.log_le_log hlogL_pos (Real.log_le_log hLpos hUp)
    have hgt1 : (1 : ℝ) < 32 * P * p := by nlinarith [hP32, hp3, hPpos, hp_pos]
    have h2 : Real.log (Real.log (32 * P * p)) ≤ Real.log (3 * p) :=
      Real.log_le_log (Real.log_pos hgt1) hlog32Pp
    have h3 : Real.log (3 * p) = Real.log 3 + q := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hp_pos), ← hqdef]
    have hlog3_le_q : Real.log 3 ≤ q := by
      rw [hqdef]; exact Real.log_le_log (by norm_num) hp3
    calc Real.log (Real.log L) ≤ Real.log (Real.log (32 * P * p)) := h1
      _ ≤ Real.log (3 * p) := h2
      _ = Real.log 3 + q := h3
      _ ≤ 2 * q := by linarith
  -- assemble L M ≤ 64 P p q
  have hkey : L * M ≤ 64 * (P * p * q) := by
    calc L * M ≤ (32 * P * p) * (2 * q) :=
          mul_le_mul hUp hM_le (le_of_lt hMpos) (le_of_lt h32Pp_pos)
      _ = 64 * (P * p * q) := by ring
  have hRHSpos : (0 : ℝ) < 2 * L * M := mul_pos (mul_pos (by norm_num) hLpos) hMpos
  have hdenle : 2 * L * M ≤ 128 * (P * p * q) := by nlinarith [hkey]
  have hLHS_eq : (1 / 128 : ℝ) * (1 / (P * p * q)) = 1 / (128 * (P * p * q)) := by
    rw [mul_one_div, div_div]
  rw [hLHS_eq]
  exact one_div_le_one_div_of_le hRHSpos hdenle

/-! ### Piece 4 — extraction: the decrement crosses `log 2` -/

/-- **The barely-divergent decrement clears `log 2`.**  The summand is nonneg and
    the series diverges (Piece 2 comparison to `not_summable_one_div_nat_loglog`),
    so the partial sums `towerDropSum` tend to `+∞` and eventually exceed `log 2`. -/
theorem dropSum_exceeds_log_two : ∃ J : ℕ, Real.log 2 < towerDropSum 2 1 4000000 J := by
  set W : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log n * Real.log (Real.log n)) with hW
  set s : ℕ → ℝ := fun j => 1 / (2 * Real.log (chowlaTower 2 1 4000000 j : ℝ)
      * Real.log (Real.log (Real.log (chowlaTower 2 1 4000000 j : ℝ)))) with hs
  have hsum_eq : ∀ J, towerDropSum 2 1 4000000 J = ∑ j ∈ Finset.range J, s j := fun J => rfl
  have hs_nonneg : ∀ j, 0 ≤ s j := by
    intro j
    have hge : 4000000 ≤ chowlaTower 2 1 4000000 j := chowlaTower_two_one_base_le j
    obtain ⟨hL15, hM12⟩ := tower_log_bounds hge
    have hpos : (0 : ℝ) < 2 * Real.log (chowlaTower 2 1 4000000 j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower 2 1 4000000 j : ℝ))) :=
      mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    exact one_div_nonneg.mpr (le_of_lt hpos)
  -- the abstract series shifted by 2 is non-summable
  have hnW : ¬ Summable W := not_summable_one_div_nat_loglog
  have hshift : ¬ Summable (fun j => W (j + 2)) :=
    fun h => hnW ((summable_nat_add_iff 2).mp h)
  have hna : ¬ Summable (fun j => (1 / 128 : ℝ) * W (j + 2)) := by
    intro hsum
    apply hshift
    have h := hsum.mul_left 128
    exact (summable_congr (fun j => by ring)).mp h
  -- s is not summable, via the eventual comparison (Piece 2)
  have hs_notsummable : ¬ Summable s := by
    refine not_summable_of_eventually_le 30 (a := fun j => (1 / 128 : ℝ) * W (j + 2))
      (fun j hj => ?_) (fun j hj => ?_) hna
    · have hP : (32 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
        have : (32 : ℕ) ≤ j + 2 := by omega
        exact_mod_cast this
      have hlp : 1 < Real.log ((j + 2 : ℕ) : ℝ) := by
        rw [Real.lt_log_iff_exp_lt (by linarith)]
        linarith [Real.exp_one_lt_d9]
      have hd : (0 : ℝ) < ((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)
          * Real.log (Real.log ((j + 2 : ℕ) : ℝ)) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (Real.log_pos hlp)
      have hWnn : (0 : ℝ) ≤ W (j + 2) := by
        change (0 : ℝ) ≤ 1 / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)
          * Real.log (Real.log ((j + 2 : ℕ) : ℝ)))
        exact one_div_nonneg.mpr (le_of_lt hd)
      exact mul_nonneg (by norm_num) hWnn
    · exact summand_lower j hj
  -- partial sums diverge, hence cross log 2
  have htend : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, s j) Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hs_nonneg).mp hs_notsummable
  have htend' : Filter.Tendsto (towerDropSum 2 1 4000000) Filter.atTop Filter.atTop := by
    have hfe : towerDropSum 2 1 4000000 = fun N => ∑ j ∈ Finset.range N, s j := funext hsum_eq
    rw [hfe]; exact htend
  obtain ⟨J, hJ⟩ := (htend'.eventually_gt_atTop (Real.log 2)).exists
  exact ⟨J, hJ⟩

/-- **The anti-vacuity witness, unconditional.**  Combining `dropSum_exceeds_log_two`
    with `regime_exists_of_dropSum_exists`: a `ChowlaRegime` with `a = 1` exists. -/
theorem chowlaRegime_exists : ∃ R : ChowlaRegime, R.a = 1 :=
  regime_exists_of_dropSum_exists dropSum_exceeds_log_two

end Salt.Entropy.Chowla
