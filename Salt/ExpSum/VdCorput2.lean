/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.Kusmin

/-!
# van der Corput's second-derivative test (Milestone 2)

This file discharges the `VK-N2-M2` residual: the discrete second-derivative
test built on top of `kusmin_landau` (Milestone 1, `Salt/ExpSum/Kusmin.lean`).

With `g n := f (n+1) - f n` the consecutive differences, if the second
differences satisfy `lam ≤ g (n+1) - g n ≤ c · lam` on the range (`0 < lam`,
`1 ≤ c`), then for `L := (b : ℝ) - a`,
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 8 · (c · L · √lam + 1 / √lam)`.

See the file `Kusmin.lean`'s Milestone-2 docstring for the full paper
arithmetic.  The engine here:

* `step_accum` — accumulate a per-step difference bound `g (n+1) - g n ≤ β`
  into `g q - g p ≤ (q - p) · β`.  Used twice (with `β = c·lam` and, via `-g`,
  with the lower bound `lam`).
* `fibre_is_interval` — **the sub-obstacle**: a `g`-monotone-predicate filter of
  an interval `Ioc a b` is itself a `Finset.Ioc`.  Built by hand from strict
  monotonicity via `min'`/`max'` (no mathlib shortcut exists for a general
  monotone predicate).  This is what lets each good window feed `kusmin_landau`.
* `count_window` — a window of `g`-length `w` holds `≤ w/lam + 1` indices, since
  `g` steps up by `≥ lam`.  Bounds the two bad windows per fibre.

**Constant.**  The recorded arithmetic advertised `C' = 5` using the (in general
false) step `⌊x⌋ - ⌊y⌋ ≤ x - y`; the honest fibre count is `K ≤ c·lam·L + 2`,
which lands the constant at `C' = 8` (explicitly permitted by the task).
-/

namespace Salt.ExpSum

open Real Finset

/-- **Step accumulation.**  If `g (n+1) - g n ≤ β` for every `n` strictly inside
`(a, b)`, then `g q - g p ≤ (q - p) · β` for `a < p ≤ q ≤ b`. -/
lemma step_accum {g : ℕ → ℝ} {a b : ℕ} {β : ℝ}
    (hstep : ∀ n, a < n → n < b → g (n + 1) - g n ≤ β)
    (p : ℕ) (hp : a < p) :
    ∀ q, p ≤ q → q ≤ b → g q - g p ≤ ((q : ℝ) - p) * β := by
  intro q hpq
  induction q, hpq using Nat.le_induction with
  | base => intro _; simp
  | succ q hpq ih =>
      intro hqb
      have h1 := ih (by omega)
      have h2 := hstep q (by omega) (by omega)
      have hexp : ((q + 1 : ℕ) : ℝ) - p = ((q : ℝ) - p) + 1 := by push_cast; ring
      rw [hexp, add_mul, one_mul]
      linarith

/-- **The fibre-is-an-interval lemma (the sub-obstacle).**  For a `g` strictly
monotone on `(a, b]` and reals `u ≤ v` (or any `u v`), the filter of `Ioc a b`
by the monotone predicate `u ≤ g n ∧ g n ≤ v` is a `Finset.Ioc a' b'` with
`a ≤ a'` and `b' ≤ b` (empty when `b' ≤ a'`). -/
lemma fibre_is_interval {g : ℕ → ℝ} {a b : ℕ}
    (hmono : ∀ p q, a < p → p < q → q ≤ b → g p < g q) (u v : ℝ) :
    ∃ a' b' : ℕ, a ≤ a' ∧ b' ≤ b ∧
      (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n ≤ v) = Finset.Ioc a' b' := by
  set T := (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n ≤ v) with hTdef
  rcases T.eq_empty_or_nonempty with he | hne
  · exact ⟨a, 0, le_refl a, Nat.zero_le b, by rw [he, Finset.Ioc_eq_empty (by omega)]⟩
  · have hn0mem : T.min' hne ∈ T := T.min'_mem hne
    have hn1mem : T.max' hne ∈ T := T.max'_mem hne
    set n0 := T.min' hne with hn0def
    set n1 := T.max' hne with hn1def
    obtain ⟨hn0Ioc, hn0lb, hn0ub⟩ := Finset.mem_filter.mp hn0mem
    obtain ⟨hn1Ioc, hn1lb, hn1ub⟩ := Finset.mem_filter.mp hn1mem
    obtain ⟨ha0, hb0⟩ := Finset.mem_Ioc.mp hn0Ioc
    obtain ⟨ha1, hb1⟩ := Finset.mem_Ioc.mp hn1Ioc
    refine ⟨n0 - 1, n1, by omega, hb1, ?_⟩
    ext x
    simp only [Finset.mem_Ioc]
    constructor
    · intro hx
      have hx0 : n0 ≤ x := Finset.min'_le T x hx
      have hx1 : x ≤ n1 := Finset.le_max' T x hx
      omega
    · rintro ⟨hlt, hle⟩
      have hx0 : n0 ≤ x := by omega
      have hxa : a < x := by omega
      have hxb : x ≤ b := le_trans hle hb1
      have hgx_lb : u ≤ g x := by
        rcases eq_or_lt_of_le hx0 with h | h
        · rw [← h]; exact hn0lb
        · exact le_trans hn0lb (le_of_lt (hmono n0 x ha0 h hxb))
      have hgx_ub : g x ≤ v := by
        rcases eq_or_lt_of_le hle with h | h
        · rw [h]; exact hn1ub
        · exact le_trans (le_of_lt (hmono x n1 hxa h hb1)) hn1ub
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hxa, hxb⟩, hgx_lb, hgx_ub⟩

/-- **Window count.**  If `g` steps up by `≥ lam > 0` (encoded via the lower
accumulation `hacc`), a window `[u, u+w)` of `g`-values holds at most
`w / lam + 1` indices in `Ioc a b`. -/
lemma count_window {g : ℕ → ℝ} {a b : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hacc : ∀ p q, a < p → p ≤ q → q ≤ b → ((q : ℝ) - p) * lam ≤ g q - g p)
    (u w : ℝ) (hw : 0 ≤ w) :
    (((Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n < u + w)).card : ℝ)
      ≤ w / lam + 1 := by
  set T := (Finset.Ioc a b).filter (fun n => u ≤ g n ∧ g n < u + w) with hTdef
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : 0 ≤ w / lam := div_nonneg hw (le_of_lt hlam)
    linarith
  · have hn0mem : T.min' hne ∈ T := T.min'_mem hne
    have hn1mem : T.max' hne ∈ T := T.max'_mem hne
    set n0 := T.min' hne with hn0def
    set n1 := T.max' hne with hn1def
    obtain ⟨hn0Ioc, hn0lb, hn0ub⟩ := Finset.mem_filter.mp hn0mem
    obtain ⟨hn1Ioc, hn1lb, hn1ub⟩ := Finset.mem_filter.mp hn1mem
    obtain ⟨ha0, hb0⟩ := Finset.mem_Ioc.mp hn0Ioc
    obtain ⟨ha1, hb1⟩ := Finset.mem_Ioc.mp hn1Ioc
    have hn01 : n0 ≤ n1 := T.min'_le_max' hne
    have hsub : T ⊆ Finset.Icc n0 n1 := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le T x hx, Finset.le_max' T x hx⟩
    have hcard : T.card ≤ (Finset.Icc n0 n1).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcardR : (T.card : ℝ) ≤ (n1 : ℝ) - n0 + 1 := by
      calc (T.card : ℝ) ≤ ((n1 + 1 - n0 : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (n1 : ℝ) - n0 + 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hspread : ((n1 : ℝ) - n0) * lam ≤ g n1 - g n0 := hacc n0 n1 ha0 hn01 hb1
    have hgdiff : g n1 - g n0 < w := by linarith
    have hn1n0 : (n1 : ℝ) - n0 ≤ w / lam := by
      rw [le_div_iff₀ hlam]; linarith
    linarith

/-- **van der Corput's second-derivative test (Milestone 2).**

With `g n := f (n+1) - f n`, if the second differences satisfy
`lam ≤ g (n+1) - g n ≤ c · lam` for all `a < n < b` (`0 < lam`, `1 ≤ c`), then
`‖∑ n ∈ Ioc a b, eK (f n)‖ ≤ 8 · (c · (b - a) · √lam + 1 / √lam)`.

The absolute constant is `C' = 8` (the recorded arithmetic advertised `5` using
a step that is false in general; see the header). -/
theorem vdC_second_derivative {f : ℕ → ℝ} {a b : ℕ} {lam c : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam) (hc : 1 ≤ c)
    (h2nd_lb : ∀ n, a < n → n < b →
        lam ≤ (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n))
    (h2nd_ub : ∀ n, a < n → n < b →
        (f (n + 1 + 1) - f (n + 1)) - (f (n + 1) - f n) ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
      ≤ 8 * (c * ((b : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  set g : ℕ → ℝ := fun n => f (n + 1) - f n with hgdef
  set δ := Real.sqrt lam with hδdef
  have hδpos : 0 < δ := Real.sqrt_pos.mpr hlam
  have hne : δ ≠ 0 := ne_of_gt hδpos
  -- step bounds in terms of g
  have hstep_lb : ∀ n, a < n → n < b → lam ≤ g (n + 1) - g n := by
    intro n h1 h2; have := h2nd_lb n h1 h2; simpa only [hgdef] using this
  have hstep_ub : ∀ n, a < n → n < b → g (n + 1) - g n ≤ c * lam := by
    intro n h1 h2; have := h2nd_ub n h1 h2; simpa only [hgdef] using this
  -- accumulations
  have hacc_hi : ∀ p q, a < p → p ≤ q → q ≤ b → g q - g p ≤ ((q : ℝ) - p) * (c * lam) := by
    intro p q hp hpq hqb; exact step_accum hstep_ub p hp q hpq hqb
  have hacc_lo : ∀ p q, a < p → p ≤ q → q ≤ b → ((q : ℝ) - p) * lam ≤ g q - g p := by
    intro p q hp hpq hqb
    have hstep' : ∀ n, a < n → n < b → (fun m => -g m) (n + 1) - (fun m => -g m) n ≤ -lam := by
      intro n hn1 hn2; dsimp only; linarith [hstep_lb n hn1 hn2]
    have key : -g q - -g p ≤ ((q : ℝ) - p) * (-lam) :=
      step_accum (g := fun m => -g m) hstep' p hp q hpq hqb
    rw [mul_neg] at key; linarith
  have hstrictmono : ∀ p q, a < p → p < q → q ≤ b → g p < g q := by
    intro p q hp hpq hqb
    have h := hacc_lo p q hp (le_of_lt hpq) hqb
    have hpos : (0 : ℝ) < ((q : ℝ) - p) * lam := by
      apply mul_pos _ hlam
      have : (p : ℝ) < q := by exact_mod_cast hpq
      linarith
    linarith
  by_cases hsmall : lam ≤ 1 / 4
  · -- ═══ main case: lam ≤ 1/4 (δ ≤ 1/2) ═══
    have hδhalf : δ ≤ 1 / 2 := by
      rw [hδdef, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hsmall
    have hδsq : lam = δ ^ 2 := by rw [hδdef]; exact (Real.sq_sqrt (le_of_lt hlam)).symm
    have hδlam : δ / lam = 1 / δ := by rw [hδsq, sq]; field_simp
    rcases eq_or_lt_of_le hab with hEq | haltb
    · -- empty: a = b
      have hEq2 : b = a := hEq.symm
      subst hEq2
      rw [Finset.Ioc_self, Finset.sum_empty, norm_zero]
      simp only [sub_self, mul_zero, zero_mul, zero_add]
      positivity
    · -- a < b
      have hLpos : (0 : ℝ) < (b : ℝ) - a := by
        have : (a : ℝ) < b := by exact_mod_cast haltb
        linarith
      have hLnn : (0 : ℝ) ≤ (b : ℝ) - a := le_of_lt hLpos
      set φ : ℕ → ℤ := fun n => ⌊g n⌋ with hφdef
      set K := (Finset.Ioc a b).image φ with hKdef
      have hmaps : ∀ n ∈ Finset.Ioc a b, φ n ∈ K := fun n hn => Finset.mem_image_of_mem φ hn
      -- STEP 1: triangle over fibres
      have hStep1 : ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => eK (f n))]
        exact norm_sum_le _ _
      -- PER-FIBRE bound
      have hfibre : ∀ k ∈ K,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ ≤ 3 / δ + 2 := by
        intro k _
        set Fk := (Finset.Ioc a b).filter (fun n => φ n = k) with hFkdef
        set Gk := (Finset.Ioc a b).filter
          (fun n => (k : ℝ) + δ ≤ g n ∧ g n ≤ (k : ℝ) + 1 - δ) with hGkdef
        have hGsub : Gk ⊆ Fk := by
          intro n hn
          rw [hGkdef, Finset.mem_filter] at hn
          obtain ⟨hnIoc, hlb, hub⟩ := hn
          rw [hFkdef, Finset.mem_filter]
          refine ⟨hnIoc, ?_⟩
          rw [hφdef]
          exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
        have hsplit : ∑ n ∈ Fk, eK (f n)
            = (∑ n ∈ Fk \ Gk, eK (f n)) + (∑ n ∈ Gk, eK (f n)) :=
          (Finset.sum_sdiff hGsub).symm
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        -- good part via kusmin
        have hgood : ‖∑ n ∈ Gk, eK (f n)‖ ≤ 1 / δ := by
          obtain ⟨a', b', ha', hb', hGeq⟩ :=
            fibre_is_interval hstrictmono ((k : ℝ) + δ) ((k : ℝ) + 1 - δ)
          have hGkeq : Gk = Finset.Ioc a' b' := by rw [hGkdef]; exact hGeq
          rw [hGkeq]
          apply kusmin_landau hδpos hδhalf
          · intro n hn1 hn2
            have hnmem : n ∈ Gk := by rw [hGkeq]; exact Finset.mem_Ioc.mpr ⟨hn1, hn2⟩
            rw [hGkdef, Finset.mem_filter] at hnmem
            exact hnmem.2.1
          · intro n hn1 hn2
            have hnmem : n ∈ Gk := by rw [hGkeq]; exact Finset.mem_Ioc.mpr ⟨hn1, hn2⟩
            rw [hGkdef, Finset.mem_filter] at hnmem
            exact hnmem.2.2
          · intro n hn1 hn2
            exact le_of_lt (hstrictmono n (n + 1) (by omega) (by omega) (by omega))
        -- bad part via count_window
        have hbad : ‖∑ n ∈ Fk \ Gk, eK (f n)‖ ≤ 2 / δ + 2 := by
          have hcardbound : ((Fk \ Gk).card : ℝ) ≤ 2 / δ + 2 := by
            set Left := (Finset.Ioc a b).filter
              (fun n => (k : ℝ) ≤ g n ∧ g n < (k : ℝ) + δ) with hLeftdef
            set Right := (Finset.Ioc a b).filter
              (fun n => (k : ℝ) + 1 - δ ≤ g n ∧ g n < (k : ℝ) + 1 - δ + δ) with hRightdef
            have hsubLR : Fk \ Gk ⊆ Left ∪ Right := by
              intro n hn
              rw [Finset.mem_sdiff] at hn
              obtain ⟨hnFk, hnGk⟩ := hn
              rw [hFkdef, Finset.mem_filter] at hnFk
              obtain ⟨hnIoc, hφk⟩ := hnFk
              rw [hφdef] at hφk
              obtain ⟨hgk1, hgk2⟩ := Int.floor_eq_iff.mp hφk
              rw [hGkdef, Finset.mem_filter, not_and] at hnGk
              have hnotpred := hnGk hnIoc
              rw [not_and_or] at hnotpred
              rw [Finset.mem_union]
              rcases hnotpred with h | h
              · left
                rw [hLeftdef, Finset.mem_filter]
                rw [not_le] at h
                exact ⟨hnIoc, hgk1, h⟩
              · right
                rw [hRightdef, Finset.mem_filter]
                rw [not_le] at h
                refine ⟨hnIoc, le_of_lt h, ?_⟩
                have he : (k : ℝ) + 1 - δ + δ = (k : ℝ) + 1 := by ring
                rw [he]; exact hgk2
            have hcLR : (Fk \ Gk).card ≤ Left.card + Right.card :=
              le_trans (Finset.card_le_card hsubLR) (Finset.card_union_le Left Right)
            have hLeftC : (Left.card : ℝ) ≤ δ / lam + 1 :=
              count_window hlam hacc_lo (k : ℝ) δ (le_of_lt hδpos)
            have hRightC : (Right.card : ℝ) ≤ δ / lam + 1 :=
              count_window hlam hacc_lo ((k : ℝ) + 1 - δ) δ (le_of_lt hδpos)
            rw [hδlam] at hLeftC hRightC
            have hcast : ((Fk \ Gk).card : ℝ) ≤ (Left.card : ℝ) + (Right.card : ℝ) := by
              exact_mod_cast hcLR
            have hbridge : (2 : ℝ) / δ = 1 / δ + 1 / δ := by ring
            linarith [hcast, hLeftC, hRightC, hbridge]
          calc ‖∑ n ∈ Fk \ Gk, eK (f n)‖
              ≤ ∑ n ∈ Fk \ Gk, ‖eK (f n)‖ := norm_sum_le _ _
            _ = ∑ n ∈ Fk \ Gk, (1 : ℝ) := by simp [eK_norm]
            _ = ((Fk \ Gk).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ ≤ 2 / δ + 2 := hcardbound
        have hbridge : (3 : ℝ) / δ = 2 / δ + 1 / δ := by ring
        linarith [hgood, hbad, hbridge]
      -- STEP 2: sum the fibre bounds
      have hStep2 : ∑ k ∈ K,
          ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖
          ≤ (K.card : ℝ) * (3 / δ + 2) := by
        calc ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖
            ≤ ∑ _k ∈ K, (3 / δ + 2) := Finset.sum_le_sum hfibre
          _ = (K.card : ℝ) * (3 / δ + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      -- fibre count K ≤ c·lam·L + 2
      have hKcard : (K.card : ℝ) ≤ c * lam * ((b : ℝ) - a) + 2 := by
        have hφmono : ∀ n ∈ Finset.Ioc a b, φ (a + 1) ≤ φ n ∧ φ n ≤ φ b := by
          intro n hn
          obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
          simp only [hφdef]
          refine ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩
          · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hna) with h | h
            · exact le_of_eq (congrArg g h)
            · exact le_of_lt (hstrictmono (a + 1) n (by omega) h hnb)
          · rcases eq_or_lt_of_le hnb with h | h
            · exact le_of_eq (congrArg g h)
            · exact le_of_lt (hstrictmono n b hna h (le_refl b))
        have hKsub : K ⊆ Finset.Icc (φ (a + 1)) (φ b) := by
          intro z hz
          rw [hKdef, Finset.mem_image] at hz
          obtain ⟨n, hn, rfl⟩ := hz
          rw [Finset.mem_Icc]
          exact hφmono n hn
        have hmemA : a + 1 ∈ Finset.Ioc a b :=
          Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        have hφab : φ (a + 1) ≤ φ b := (hφmono (a + 1) hmemA).2
        have hcardZ : (K.card : ℤ) ≤ φ b + 1 - φ (a + 1) := by
          have h1 : K.card ≤ (Finset.Icc (φ (a + 1)) (φ b)).card := Finset.card_le_card hKsub
          have h2 : ((Finset.Icc (φ (a + 1)) (φ b)).card : ℤ) = φ b + 1 - φ (a + 1) := by
            rw [Int.card_Icc, Int.toNat_of_nonneg (show (0 : ℤ) ≤ φ b + 1 - φ (a + 1) by omega)]
          calc (K.card : ℤ) ≤ ((Finset.Icc (φ (a + 1)) (φ b)).card : ℤ) := by exact_mod_cast h1
            _ = φ b + 1 - φ (a + 1) := h2
        have hKR : (K.card : ℝ) ≤ (φ b : ℝ) + 1 - (φ (a + 1) : ℝ) := by
          calc (K.card : ℝ) = ((K.card : ℤ) : ℝ) := by push_cast; ring
            _ ≤ ((φ b + 1 - φ (a + 1) : ℤ) : ℝ) := by exact_mod_cast hcardZ
            _ = (φ b : ℝ) + 1 - (φ (a + 1) : ℝ) := by push_cast; ring
        have hfb : (φ b : ℝ) ≤ g b := by rw [hφdef]; exact Int.floor_le (g b)
        have hfa : g (a + 1) - 1 < (φ (a + 1) : ℝ) := by
          rw [hφdef]; exact Int.sub_one_lt_floor (g (a + 1))
        have hgub := hacc_hi (a + 1) b (by omega) (by omega) (le_refl b)
        have hclam : (0 : ℝ) ≤ c * lam := mul_nonneg (by linarith) (le_of_lt hlam)
        have hgub2 : g b - g (a + 1) ≤ c * lam * ((b : ℝ) - a) := by
          have hstep : ((b : ℝ) - (a + 1)) * (c * lam) ≤ c * lam * ((b : ℝ) - a) := by
            nlinarith [hclam]
          push_cast at hgub
          linarith [hgub, hstep]
        linarith [hKR, hfb, hfa, hgub2]
      -- FINAL arithmetic
      have hfinal : (K.card : ℝ) * (3 / δ + 2) ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := by
        have hcleared : (c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)
            ≤ 8 * (c * ((b : ℝ) - a) * δ) * δ + 8 := by
          rw [hδsq]
          nlinarith [hδpos, hδhalf, hLnn, hc,
            mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hLnn) (sq_nonneg δ),
            mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c) hLnn)
              (sq_nonneg δ)) (by linarith : (0 : ℝ) ≤ 5 - 2 * δ)]
        have e1 : (c * lam * ((b : ℝ) - a) + 2) * (3 / δ + 2)
            = ((c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)) / δ := by field_simp
        have e2 : 8 * (c * ((b : ℝ) - a) * δ + 1 / δ)
            = (8 * (c * ((b : ℝ) - a) * δ) * δ + 8) / δ := by field_simp
        calc (K.card : ℝ) * (3 / δ + 2)
            ≤ (c * lam * ((b : ℝ) - a) + 2) * (3 / δ + 2) :=
              mul_le_mul_of_nonneg_right hKcard (by positivity)
          _ = ((c * lam * ((b : ℝ) - a) + 2) * (3 + 2 * δ)) / δ := e1
          _ ≤ (8 * (c * ((b : ℝ) - a) * δ) * δ + 8) / δ :=
              (div_le_div_iff_of_pos_right hδpos).mpr hcleared
          _ = 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := e2.symm
      calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ k ∈ K, ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => φ n = k), eK (f n)‖ := hStep1
        _ ≤ (K.card : ℝ) * (3 / δ + 2) := hStep2
        _ ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := hfinal
  · -- ═══ trivial case: lam > 1/4 (δ > 1/2) ═══
    have hbig : (1 : ℝ) / 4 < lam := not_le.mp hsmall
    have hδhalf : (1 : ℝ) / 2 < δ := by
      rw [hδdef, show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hbig
    have hL : (0 : ℝ) ≤ (b : ℝ) - a := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have hnorm : ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ (b : ℝ) - a := by
      calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖
          ≤ ∑ n ∈ Finset.Ioc a b, ‖eK (f n)‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.Ioc a b, (1 : ℝ) := by simp [eK_norm]
        _ = ((Finset.Ioc a b).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = (b : ℝ) - a := by rw [Nat.card_Ioc, Nat.cast_sub hab]
    have hcδ : (1 : ℝ) / 2 ≤ c * δ := by
      nlinarith [hc, hδhalf, hδpos, mul_nonneg (sub_nonneg.mpr hc) (le_of_lt hδpos)]
    have hbound : (b : ℝ) - a ≤ 8 * (c * ((b : ℝ) - a) * δ) := by
      nlinarith [hL, hcδ, mul_nonneg hL (by linarith [hcδ] : (0 : ℝ) ≤ c * δ - 1 / 2)]
    have h1δ : (0 : ℝ) ≤ 1 / δ := by positivity
    calc ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤ (b : ℝ) - a := hnorm
      _ ≤ 8 * (c * ((b : ℝ) - a) * δ) := hbound
      _ ≤ 8 * (c * ((b : ℝ) - a) * δ + 1 / δ) := by linarith

end Salt.ExpSum
