/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.MassLedgerA1
import Salt.Chen.MassCert
import Salt.Chen.FseqAntitone

/-!
# SS1 — the super-solution certification (the numeric keystone's final node)

Design: `docs/blueprints/flags.md`, `2026-07-13 TK3 ROUTE (b)` and `THE TK3b GATE`.

Both mass ledgers (`MassLedger.Fchain_le_A2_of_massSum` needs `Σ_{even k} massE k ≤ 43/75`;
`MassLedgerA1.fchain_ge_A1_of_massSums` needs that PLUS `Σ_{odd j} massO j ≤ 11/125`) close
through a single **super-solution** object.  The route escapes the Perron wall (catches #38/#39):
instead of normalized per-level propagation, one fixed monotone inequality is checked on a
pointwise-dominating majorant, and the ledger demand is INTEGRAL not pointwise.

## The structural layer (this file — profile-independent)

Write the truncated even/odd Rosser-chain partial sums as functions of the sieve variable:

  `Xe K v = Σ_{k even, 2 ≤ k ≤ K} fseq k v`,   `Xo K w = Σ_{j odd, 3 ≤ j ≤ K} fseq j w`.

Summing the window equations (BJS (16)/(17)) TERMWISE and extending every finite integral to a
common top — free, because each `fseq n` vanishes past its support edge `n+2` — gives the
**closed monotone recursion**

  `Xe K v = fseq 2 v + (1/v)·∫_v^{K+2} Xo (K−1) (t−1) dt`         (`Xe_recursion`, `v ≥ 2`),
  `Xo K w = (1/w)·∫_{max w 3}^{K+2} Xe (K−1) (t−1) dt`           (`odd_step`,      `w ≥ 1`).

A **super-solution pair** `(Ebar, Obar)` (nonneg, integrable) satisfying the two fixed
inequalities (`hSE`, `hSO` below — the panel-certified facts) then dominates every truncation
POINTWISE by an elementary coupled induction (`superSol_dominates`), no spectral theory.

## The ledger integrals (the reduction)

`Σ_{even k ≤ K} massE k = ∫_2^{K+2} Xe K` and `Σ_{odd j ≤ K} massO j = ∫_3^{K+2} Xo K`
(`massE_sum_eq`, `massO_sum_eq`; each `massE k = ∫_2^{k+2} fseq k` extended to the common top).
Composing domination with integral monotonicity yields the EXACT consumer shapes
(`massSum_le_A2_of_superSolution`, `massOSum_le_A1_of_superSolution`, and the `∀ N`, `range N`
converters `massSum_le_A2_final` / `massOSum_le_A1_final`) as functions of the super-solution
hypotheses.  Instantiating with the frozen 43-knot PL + wing `Ebar` (`∫Ebar ≤ 43/75`,
`∫Obar ≤ 11/125`) and discharging the 43 panel checks (`hSE`/`hSO`) is the numeric follow-up
(the toolkit `LogToolkit.lean` is the enabler); this file freezes the STRUCTURE those consume.
-/

open intervalIntegral MeasureTheory Set

namespace Salt.Chen

/-! ## The truncated even/odd partial-sum functions -/

/-- The truncated even Rosser-chain partial sum `Σ_{k even, 2 ≤ k ≤ K} fseq k`, as a function of
the sieve variable.  Its integral over `[2, K+2]` is the A₂ mass sum (`massE_sum_eq`). -/
noncomputable def Xe (K : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k), fseq k v

/-- The truncated odd Rosser-chain partial sum `Σ_{j odd, 3 ≤ j ≤ K} fseq j`. -/
noncomputable def Xo (K : ℕ) (w : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (K + 1)).filter (fun j => Odd j ∧ 3 ≤ j), fseq j w

theorem Xe_apply (K : ℕ) (v : ℝ) :
    Xe K v = ∑ k ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k), fseq k v := rfl

theorem Xo_apply (K : ℕ) (w : ℝ) :
    Xo K w = ∑ j ∈ (Finset.range (K + 1)).filter (fun j => Odd j ∧ 3 ≤ j), fseq j w := rfl

/-! ### Nonnegativity, support, integrability -/

theorem Xe_nonneg (K : ℕ) (v : ℝ) : 0 ≤ Xe K v :=
  Finset.sum_nonneg (fun k _ => fseq_nonneg k v)

theorem Xo_nonneg (K : ℕ) (w : ℝ) : 0 ≤ Xo K w :=
  Finset.sum_nonneg (fun j _ => fseq_nonneg j w)

/-- `Xe K v = 0` past the support edge `K+2`. -/
theorem Xe_eq_zero_of_large (K : ℕ) (v : ℝ) (h : (K : ℝ) + 2 ≤ v) : Xe K v = 0 := by
  rw [Xe_apply]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hklt, -⟩ := Finset.mem_filter.mp hk
  have hkK : (k : ℝ) ≤ (K : ℝ) := by
    have : k ≤ K := by have := Finset.mem_range.mp hklt; omega
    exact_mod_cast this
  exact fseq_eq_zero_of_ge k v (by linarith)

/-- `Xo K w = 0` past the support edge `K+2`. -/
theorem Xo_eq_zero_of_large (K : ℕ) (w : ℝ) (h : (K : ℝ) + 2 ≤ w) : Xo K w = 0 := by
  rw [Xo_apply]
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hjlt, -⟩ := Finset.mem_filter.mp hj
  have hjK : (j : ℝ) ≤ (K : ℝ) := by
    have : j ≤ K := by have := Finset.mem_range.mp hjlt; omega
    exact_mod_cast this
  exact fseq_eq_zero_of_ge j w (by linarith)

theorem Xe_intervalIntegrable (K : ℕ) (a b : ℝ) : IntervalIntegrable (Xe K) volume a b := by
  have hfun : Xe K = ∑ k ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k), fseq k := by
    funext v; rw [Xe_apply, Finset.sum_apply]
  rw [hfun]
  exact IntervalIntegrable.sum _ (fun k _ => fseq_intervalIntegrable k a b)

theorem Xo_intervalIntegrable (K : ℕ) (a b : ℝ) : IntervalIntegrable (Xo K) volume a b := by
  have hfun : Xo K = ∑ j ∈ (Finset.range (K + 1)).filter (fun j => Odd j ∧ 3 ≤ j), fseq j := by
    funext w; rw [Xo_apply, Finset.sum_apply]
  rw [hfun]
  exact IntervalIntegrable.sum _ (fun j _ => fseq_intervalIntegrable j a b)

theorem Xe_shift_ii (K : ℕ) (a b : ℝ) : IntervalIntegrable (fun t => Xe K (t - 1)) volume a b := by
  simpa using (Xe_intervalIntegrable K (a - 1) (b - 1)).comp_sub_right 1

theorem Xo_shift_ii (K : ℕ) (a b : ℝ) : IntervalIntegrable (fun t => Xo K (t - 1)) volume a b := by
  simpa using (Xo_intervalIntegrable K (a - 1) (b - 1)).comp_sub_right 1

/-! ## The single-level window identities with a common top

Each even level `k = i+1` (`i` even) integrates its odd predecessor up to `i+3 = k+2`; each odd
level `j = i+1` (`i` even) integrates its even predecessor from `max s 3` up to `i+3 = j+2`.  We
extend each to a common top `K+2` (`fseq i` vanishes past `i+2`, so the extension is free). -/

/-- The odd level `i+1` (`i ≠ 0`, `i+1` odd), collapsed to the single `max`-form valid on all of
`[1,∞)` (flat below `3`, tail above, agreeing at `3`). -/
theorem fseq_odd_max {i : ℕ} (hi0 : i ≠ 0) (hev : ¬ Even (i + 1)) {w : ℝ} (hw : 1 ≤ w) :
    fseq (i + 1) w = (1 / w) * ∫ t in (max w 3)..((i : ℝ) + 3), fseq i (t - 1) := by
  rcases le_or_gt w 3 with h3 | h3
  · rcases lt_or_eq_of_le h3 with hlt | heq
    · rw [max_eq_right h3, fseq_odd_flat_window hi0 hev hw hlt]
    · subst heq
      rw [max_self, fseq_odd_tail_window hi0 hev (le_refl 3)]
  · rw [max_eq_left h3.le, fseq_odd_tail_window hi0 hev h3.le]

/-- Even level `j+1` (`j` odd), window equation extended to the common top `K+2`. -/
theorem fseq_even_ext {j : ℕ} (hj : Odd j) {K : ℕ} (hjK : j + 1 ≤ K) {v : ℝ} (hv : 2 ≤ v) :
    fseq (j + 1) v = (1 / v) * ∫ t in v..((K : ℝ) + 2), fseq j (t - 1) := by
  have hev : Even (j + 1) := hj.add_one
  rw [fseq_even_window hev hv]
  congr 1
  have hjc : (j : ℝ) + 3 ≤ (K : ℝ) + 2 := by
    have : (j : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hjK
    linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (fseq_shift_intervalIntegrable j v ((j : ℝ) + 3))
        (fseq_shift_intervalIntegrable j ((j : ℝ) + 3) ((K : ℝ) + 2))]
  have hz : (∫ t in ((j : ℝ) + 3)..((K : ℝ) + 2), fseq j (t - 1)) = 0 := by
    have hc : (∫ t in ((j : ℝ) + 3)..((K : ℝ) + 2), fseq j (t - 1))
        = ∫ _t in ((j : ℝ) + 3)..((K : ℝ) + 2), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hjc] at ht
      exact fseq_eq_zero_of_ge j (t - 1) (by have := ht.1; linarith)
    rw [hc, intervalIntegral.integral_zero]
  rw [hz, add_zero]

/-- Odd level `i+1` (`i` even, `2 ≤ i`), window equation extended to the common top `K+2`. -/
theorem fseq_odd_ext {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) {K : ℕ} (hiK : i + 1 ≤ K) {w : ℝ}
    (hw : 1 ≤ w) :
    fseq (i + 1) w = (1 / w) * ∫ t in (max w 3)..((K : ℝ) + 2), fseq i (t - 1) := by
  have hi0 : i ≠ 0 := by omega
  have hev : ¬ Even (i + 1) := by rw [Nat.even_add_one]; exact not_not_intro hi
  rw [fseq_odd_max hi0 hev hw]
  congr 1
  have hjc : (i : ℝ) + 3 ≤ (K : ℝ) + 2 := by
    have : (i : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hiK
    linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (fseq_shift_intervalIntegrable i (max w 3) ((i : ℝ) + 3))
        (fseq_shift_intervalIntegrable i ((i : ℝ) + 3) ((K : ℝ) + 2))]
  have hz : (∫ t in ((i : ℝ) + 3)..((K : ℝ) + 2), fseq i (t - 1)) = 0 := by
    have hc : (∫ t in ((i : ℝ) + 3)..((K : ℝ) + 2), fseq i (t - 1))
        = ∫ _t in ((i : ℝ) + 3)..((K : ℝ) + 2), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hjc] at ht
      exact fseq_eq_zero_of_ge i (t - 1) (by have := ht.1; linarith)
    rw [hc, intervalIntegral.integral_zero]
  rw [hz, add_zero]

/-! ## The summed window identities (the closed monotone recursion)

Summing the single-level identities over the parity index set and swapping the finite sum with the
integral (`integral_finsetSum`) turns the termwise windows into a two-function closed system. -/

/-- The even sum above the base (`k ≥ 4`) equals the `T_e`-image of the odd sum one level down. -/
theorem even_step (K : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    (∑ k ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 4 ≤ k), fseq k v)
      = (1 / v) * ∫ t in v..((K : ℝ) + 2), Xo (K - 1) (t - 1) := by
  have hreidx :
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 4 ≤ k), fseq k v)
        = ∑ j ∈ (Finset.range ((K - 1) + 1)).filter (fun j => Odd j ∧ 3 ≤ j), fseq (j + 1) v := by
    apply Finset.sum_nbij' (fun k => k - 1) (fun j => j + 1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff, Nat.odd_iff] at hk ⊢
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff, Nat.odd_iff] at hj ⊢
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff] at hk
      congr 1
      omega
  rw [hreidx]
  have hterm : ∀ j ∈ (Finset.range ((K - 1) + 1)).filter (fun j => Odd j ∧ 3 ≤ j),
      fseq (j + 1) v = (1 / v) * ∫ t in v..((K : ℝ) + 2), fseq j (t - 1) := by
    intro j hj
    obtain ⟨hjlt, hjodd, hj3⟩ := by
      simpa only [Finset.mem_filter, Finset.mem_range] using hj
    exact fseq_even_ext hjodd (by omega : j + 1 ≤ K) hv
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [← intervalIntegral.integral_finsetSum
        (fun j _ => fseq_shift_intervalIntegrable j v ((K : ℝ) + 2))]
  apply intervalIntegral.integral_congr
  intro t _
  rfl

/-- **The even two-level recursion.**  `Xe K = fseq 2 + (1/v)·∫_v^{K+2} Xo (K−1) (·−1)`
for `v ≥ 2` and `K ≥ 2`. -/
theorem Xe_recursion (K : ℕ) (hK : 2 ≤ K) {v : ℝ} (hv : 2 ≤ v) :
    Xe K v = fseq 2 v + (1 / v) * ∫ t in v..((K : ℝ) + 2), Xo (K - 1) (t - 1) := by
  have h2mem : 2 ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), even_two, le_refl 2⟩
  have hpeel : Xe K v
      = fseq 2 v
        + ∑ k ∈ ((Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k)).erase 2, fseq k v := by
    rw [Xe_apply]
    exact (Finset.add_sum_erase _ (fun k => fseq k v) h2mem).symm
  have herase : ((Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k)).erase 2
      = (Finset.range (K + 1)).filter (fun k => Even k ∧ 4 ≤ k) := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, Nat.even_iff]
    omega
  rw [hpeel, herase, even_step K hv]

/-- **The odd one-level recursion.**  `Xo K = (1/w)·∫_{max w 3}^{K+2} Xe (K−1) (·−1)` for
`w ≥ 1` (all `K`; both sides vanish when the index set is empty). -/
theorem odd_step (K : ℕ) {w : ℝ} (hw : 1 ≤ w) :
    Xo K w = (1 / w) * ∫ t in (max w 3)..((K : ℝ) + 2), Xe (K - 1) (t - 1) := by
  rw [Xo_apply]
  have hreidx :
      (∑ j ∈ (Finset.range (K + 1)).filter (fun j => Odd j ∧ 3 ≤ j), fseq j w)
        = ∑ i ∈ (Finset.range ((K - 1) + 1)).filter (fun i => Even i ∧ 2 ≤ i), fseq (i + 1) w := by
    apply Finset.sum_nbij' (fun j => j - 1) (fun i => i + 1)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff, Nat.odd_iff] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff, Nat.odd_iff] at hi ⊢
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at hj
      omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at hj
      congr 1
      omega
  rw [hreidx]
  have hterm : ∀ i ∈ (Finset.range ((K - 1) + 1)).filter (fun i => Even i ∧ 2 ≤ i),
      fseq (i + 1) w = (1 / w) * ∫ t in (max w 3)..((K : ℝ) + 2), fseq i (t - 1) := by
    intro i hi
    obtain ⟨hilt, hie, hi2⟩ := by
      simpa only [Finset.mem_filter, Finset.mem_range] using hi
    exact fseq_odd_ext hie hi2 (by omega : i + 1 ≤ K) hw
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [← intervalIntegral.integral_finsetSum
        (fun i _ => fseq_shift_intervalIntegrable i (max w 3) ((K : ℝ) + 2))]
  apply intervalIntegral.integral_congr
  intro t _
  rfl

/-! ## The domination induction (the Lean-friendly Neumann)

A super-solution pair `(Ebar, Obar)` — nonneg, integrable, satisfying the two fixed inequalities
`hSE`/`hSO` (in the `∀ b`-family form so everything stays a finite `intervalIntegral`) —
dominates every truncation pointwise, by a single coupled induction on the truncation depth. -/

/-- **The domination theorem (super-solution ⟹ pointwise majorant).**  If `Ebar, Obar ≥ 0` are
interval-integrable and satisfy the super-solution inequalities

* `hSE`: `fseq 2 v + (1/v)·∫_v^b Obar (·−1) ≤ Ebar v`   (for `2 ≤ v ≤ b`),
* `hSO`: `(1/w)·∫_{max w 3}^b Ebar (·−1) ≤ Obar w`       (for `1 ≤ w`, `max w 3 ≤ b`),

then `Xe K ≤ Ebar` on `[2,∞)` and `Xo K ≤ Obar` on `[1,∞)` for every truncation depth `K`. -/
theorem superSol_dominates (Ebar Obar : ℝ → ℝ)
    (hE0 : ∀ v, 0 ≤ Ebar v) (hO0 : ∀ w, 0 ≤ Obar w)
    (hEii : ∀ a b, IntervalIntegrable Ebar volume a b)
    (hOii : ∀ a b, IntervalIntegrable Obar volume a b)
    (hSE : ∀ v, 2 ≤ v → ∀ b, v ≤ b →
      fseq 2 v + (1 / v) * ∫ t in v..b, Obar (t - 1) ≤ Ebar v)
    (hSO : ∀ w, 1 ≤ w → ∀ b, max w 3 ≤ b →
      (1 / w) * ∫ t in (max w 3)..b, Ebar (t - 1) ≤ Obar w) :
    ∀ K, (∀ v, 2 ≤ v → Xe K v ≤ Ebar v) ∧ (∀ w, 1 ≤ w → Xo K w ≤ Obar w) := by
  intro K
  induction K with
  | zero =>
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · rw [Xe_eq_zero_of_large 0 v (by push_cast; linarith)]; exact hE0 v
    · -- Xo 0 w = 0 (the odd index set {3 ≤ j ≤ 0} is empty)
      have hz : Xo 0 w = 0 := by
        rw [Xo_apply]
        apply Finset.sum_eq_zero
        intro j hj
        obtain ⟨hlt, -, h3⟩ := by simpa only [Finset.mem_filter, Finset.mem_range] using hj
        exact absurd h3 (by omega)
      rw [hz]; exact hO0 w
  | succ n ih =>
    obtain ⟨ihE, ihO⟩ := ih
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · -- even part: Xe (n+1) v ≤ Ebar v
      rcases Nat.lt_or_ge (n + 1) 2 with hn1 | hn2
      · -- n+1 < 2 (n = 0): Xe 1 = 0 (the even index set {2 ≤ k ≤ 1} is empty)
        have hz : Xe (n + 1) v = 0 := by
          rw [Xe_apply]
          apply Finset.sum_eq_zero
          intro k hk
          obtain ⟨hlt, -, h2⟩ := by simpa only [Finset.mem_filter, Finset.mem_range] using hk
          exact absurd h2 (by omega)
        rw [hz]; exact hE0 v
      · by_cases hvK : v ≤ ((n + 1 : ℕ) : ℝ) + 2
        · have hrec := Xe_recursion (n + 1) hn2 hv
          simp only [Nat.add_sub_cancel] at hrec
          rw [hrec]
          have hmono : (∫ t in v..(((n + 1 : ℕ) : ℝ) + 2), Xo n (t - 1))
              ≤ ∫ t in v..(((n + 1 : ℕ) : ℝ) + 2), Obar (t - 1) := by
            apply intervalIntegral.integral_mono_on hvK (Xo_shift_ii n v _)
              (by simpa using (hOii (v - 1) (((n + 1 : ℕ) : ℝ) + 2 - 1)).comp_sub_right 1)
            intro t ht
            exact ihO (t - 1) (by have := ht.1; linarith)
          have hscale := mul_le_mul_of_nonneg_left hmono (show (0 : ℝ) ≤ 1 / v by positivity)
          have hfin := hSE v hv (((n + 1 : ℕ) : ℝ) + 2) hvK
          linarith
        · rw [Xe_eq_zero_of_large (n + 1) v (le_of_lt (not_le.mp hvK))]
          exact hE0 v
    · -- odd part: Xo (n+1) w ≤ Obar w  (odd_step holds for every K)
      by_cases hwK : w ≤ ((n + 1 : ℕ) : ℝ) + 2
      · have hrec := odd_step (n + 1) hw
        simp only [Nat.add_sub_cancel] at hrec
        rw [hrec]
        have hmax : max w 3 ≤ ((n + 1 : ℕ) : ℝ) + 2 := by
          refine max_le hwK ?_
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          push_cast; linarith
        have hmono : (∫ t in (max w 3)..(((n + 1 : ℕ) : ℝ) + 2), Xe n (t - 1))
            ≤ ∫ t in (max w 3)..(((n + 1 : ℕ) : ℝ) + 2), Ebar (t - 1) := by
          apply intervalIntegral.integral_mono_on hmax (Xe_shift_ii n _ _)
            (by simpa using (hEii (max w 3 - 1) (((n + 1 : ℕ) : ℝ) + 2 - 1)).comp_sub_right 1)
          intro t ht
          have h3t : (3 : ℝ) ≤ t := le_trans (le_max_right w 3) ht.1
          exact ihE (t - 1) (by linarith)
        have hscale := mul_le_mul_of_nonneg_left hmono (show (0 : ℝ) ≤ 1 / w by positivity)
        have hfin := hSO w hw (((n + 1 : ℕ) : ℝ) + 2) hmax
        linarith
      · rw [Xo_eq_zero_of_large (n + 1) w (le_of_lt (not_le.mp hwK))]
        exact hO0 w

/-! ## The ledger integrals: mass sums as integrals of the partial-sum functions -/

/-- `Σ_{even k, 2 ≤ k ≤ K} massE k = ∫_2^{K+2} Xe K` (each `massE k = ∫_2^{k+2} fseq k` extended to
the common top). -/
theorem massE_sum_eq (K : ℕ) :
    (∑ k ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k), massE k)
      = ∫ v in (2 : ℝ)..((K : ℝ) + 2), Xe K v := by
  have hswap : (∫ v in (2 : ℝ)..((K : ℝ) + 2), Xe K v)
      = ∑ k ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k),
          ∫ v in (2 : ℝ)..((K : ℝ) + 2), fseq k v :=
    intervalIntegral.integral_finsetSum (fun k _ => fseq_intervalIntegrable k 2 ((K : ℝ) + 2))
  rw [hswap]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hklt, hke, hk2⟩ := by simpa only [Finset.mem_filter, Finset.mem_range] using hk
  have hkK : (k : ℝ) + 2 ≤ (K : ℝ) + 2 := by
    have : k ≤ K := by omega
    have : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
    linarith
  symm
  unfold massE
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (fseq_intervalIntegrable k 2 ((k : ℝ) + 2))
        (fseq_intervalIntegrable k ((k : ℝ) + 2) ((K : ℝ) + 2))]
  have hz : (∫ v in ((k : ℝ) + 2)..((K : ℝ) + 2), fseq k v) = 0 := by
    have hc : (∫ v in ((k : ℝ) + 2)..((K : ℝ) + 2), fseq k v)
        = ∫ _v in ((k : ℝ) + 2)..((K : ℝ) + 2), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le hkK] at hv
      exact fseq_eq_zero_of_ge k v (by have := hv.1; linarith)
    rw [hc, intervalIntegral.integral_zero]
  rw [hz, add_zero]

/-- `Σ_{odd j, 3 ≤ j ≤ K} massO j = ∫_3^{K+2} Xo K` (sibling of `massE_sum_eq`, lower limit `3`). -/
theorem massO_sum_eq (K : ℕ) :
    (∑ j ∈ (Finset.range (K + 1)).filter (fun j => Odd j ∧ 3 ≤ j), massO j)
      = ∫ w in (3 : ℝ)..((K : ℝ) + 2), Xo K w := by
  have hswap : (∫ w in (3 : ℝ)..((K : ℝ) + 2), Xo K w)
      = ∑ j ∈ (Finset.range (K + 1)).filter (fun j => Odd j ∧ 3 ≤ j),
          ∫ w in (3 : ℝ)..((K : ℝ) + 2), fseq j w :=
    intervalIntegral.integral_finsetSum (fun j _ => fseq_intervalIntegrable j 3 ((K : ℝ) + 2))
  rw [hswap]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hjlt, hjo, hj3⟩ := by simpa only [Finset.mem_filter, Finset.mem_range] using hj
  have hjK : (j : ℝ) + 2 ≤ (K : ℝ) + 2 := by
    have : j ≤ K := by omega
    have : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
    linarith
  symm
  unfold massO
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (fseq_intervalIntegrable j 3 ((j : ℝ) + 2))
        (fseq_intervalIntegrable j ((j : ℝ) + 2) ((K : ℝ) + 2))]
  have hz : (∫ w in ((j : ℝ) + 2)..((K : ℝ) + 2), fseq j w) = 0 := by
    have hc : (∫ w in ((j : ℝ) + 2)..((K : ℝ) + 2), fseq j w)
        = ∫ _w in ((j : ℝ) + 2)..((K : ℝ) + 2), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le hjK] at hw
      exact fseq_eq_zero_of_ge j w (by have := hw.1; linarith)
    rw [hc, intervalIntegral.integral_zero]
  rw [hz, add_zero]

/-! ## The composed ledger reductions (the exact consumer shapes)

Domination + integral monotonicity + the two integral budgets close both ledgers, as functions of
the super-solution hypotheses.  The `∀ N`, `Finset.range N` forms match `MassLedger`/`MassLedgerA1`
verbatim; a downstream call applies them at its truncation depth. -/

/-- **The A₂ ledger, from a super-solution.**  With the domination hypotheses and the even integral
budget `∫_2^b Ebar ≤ 43/75`, the A₂ even-mass sum is `≤ 43/75` for every `N` — exactly the
hypothesis `MassLedger.Fchain_le_A2_of_massSum` consumes. -/
theorem massSum_le_A2_of_superSolution (Ebar Obar : ℝ → ℝ)
    (hE0 : ∀ v, 0 ≤ Ebar v) (hO0 : ∀ w, 0 ≤ Obar w)
    (hEii : ∀ a b, IntervalIntegrable Ebar volume a b)
    (hOii : ∀ a b, IntervalIntegrable Obar volume a b)
    (hSE : ∀ v, 2 ≤ v → ∀ b, v ≤ b →
      fseq 2 v + (1 / v) * ∫ t in v..b, Obar (t - 1) ≤ Ebar v)
    (hSO : ∀ w, 1 ≤ w → ∀ b, max w 3 ≤ b →
      (1 / w) * ∫ t in (max w 3)..b, Ebar (t - 1) ≤ Obar w)
    (hEbound : ∀ b, 2 ≤ b → (∫ v in (2 : ℝ)..b, Ebar v) ≤ 43 / 75) :
    ∀ N, (∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k) ≤ 43 / 75 := by
  have hdom := superSol_dominates Ebar Obar hE0 hO0 hEii hOii hSE hSO
  have hkey : ∀ K,
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => Even k ∧ 2 ≤ k), massE k) ≤ 43 / 75 := by
    intro K
    have hle2 : (2 : ℝ) ≤ (K : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) K; linarith
    rw [massE_sum_eq K]
    calc (∫ v in (2 : ℝ)..((K : ℝ) + 2), Xe K v)
        ≤ ∫ v in (2 : ℝ)..((K : ℝ) + 2), Ebar v := by
          apply intervalIntegral.integral_mono_on hle2 (Xe_intervalIntegrable K 2 _) (hEii 2 _)
          intro v hv; exact (hdom K).1 v hv.1
      _ ≤ 43 / 75 := hEbound ((K : ℝ) + 2) hle2
  intro N
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp only [Finset.range_zero, Finset.filter_empty, Finset.sum_empty]; norm_num
  · have hN : N = (N - 1) + 1 := by omega
    rw [hN]; exact hkey (N - 1)

/-- **The A₁ odd-tail ledger, from a super-solution.**  With the domination hypotheses and the odd
integral budget `∫_3^b Obar ≤ 11/125`, the A₁ odd-mass sum is `≤ 11/125` for every `N` — the second
hypothesis `MassLedgerA1.fchain_ge_A1_of_massSums` consumes (the first is the A₂ bound above). -/
theorem massOSum_le_A1_of_superSolution (Ebar Obar : ℝ → ℝ)
    (hE0 : ∀ v, 0 ≤ Ebar v) (hO0 : ∀ w, 0 ≤ Obar w)
    (hEii : ∀ a b, IntervalIntegrable Ebar volume a b)
    (hOii : ∀ a b, IntervalIntegrable Obar volume a b)
    (hSE : ∀ v, 2 ≤ v → ∀ b, v ≤ b →
      fseq 2 v + (1 / v) * ∫ t in v..b, Obar (t - 1) ≤ Ebar v)
    (hSO : ∀ w, 1 ≤ w → ∀ b, max w 3 ≤ b →
      (1 / w) * ∫ t in (max w 3)..b, Ebar (t - 1) ≤ Obar w)
    (hObound : ∀ b, 3 ≤ b → (∫ w in (3 : ℝ)..b, Obar w) ≤ 11 / 125) :
    ∀ N, (∑ j ∈ (Finset.range N).filter (fun j => Odd j ∧ 3 ≤ j), massO j) ≤ 11 / 125 := by
  have hdom := superSol_dominates Ebar Obar hE0 hO0 hEii hOii hSE hSO
  have hkey : ∀ K,
      (∑ j ∈ (Finset.range (K + 1)).filter (fun j => Odd j ∧ 3 ≤ j), massO j) ≤ 11 / 125 := by
    intro K
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · -- K = 0: the odd index set {3 ≤ j ≤ 0} is empty
      subst hK0
      have hz : (∑ j ∈ (Finset.range 1).filter (fun j => Odd j ∧ 3 ≤ j), massO j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        obtain ⟨hlt, -, h3⟩ := by simpa only [Finset.mem_filter, Finset.mem_range] using hj
        exact absurd h3 (by omega)
      rw [hz]; norm_num
    have hK1 : 1 ≤ K := hKpos
    have hle3 : (3 : ℝ) ≤ (K : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
      linarith
    rw [massO_sum_eq K]
    calc (∫ w in (3 : ℝ)..((K : ℝ) + 2), Xo K w)
        ≤ ∫ w in (3 : ℝ)..((K : ℝ) + 2), Obar w := by
          apply intervalIntegral.integral_mono_on hle3 (Xo_intervalIntegrable K 3 _) (hOii 3 _)
          intro w hw; exact (hdom K).2 w (by linarith [hw.1])
      _ ≤ 11 / 125 := hObound ((K : ℝ) + 2) hle3
  intro N
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp only [Finset.range_zero, Finset.filter_empty, Finset.sum_empty]; norm_num
  · have hN : N = (N - 1) + 1 := by omega
    rw [hN]; exact hkey (N - 1)

end Salt.Chen
