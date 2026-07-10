/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.BudgetMoment
import Salt.Twelve.BudgetPoly
import Salt.Twelve.W3Prep

/-!
# W3-1 (workhorse) — the multi-dimensional budget moment (`mv_monomial`)

Card W3-1 of the `explicit12` wave-3 dispatch
(`docs/blueprints/explicit12-design.md`).  The keystone the two sieve
evaluations (`mv_I`, `mv_J`) both consume: a general-`n` induction that peels one
coordinate of the decoupled box `decBox` at a time, reducing each peel to the
landed one-dimensional `budget_moment`, with the Dirichlet constants `DInt'`
telescoping exactly through the `Nat.factorial` β-identity `DInt'_succ`.

Structure:
* `decBox` — the decoupled sieve box (frozen definition).
* `decBox_succ_sum` — the head/tail split of a sum over `decBox (n+1)` into an
  outer sum over the head coordinate and an inner sum over `decBox n` at the
  ℕ-capped `z' = (z-1)/r₀ + 1`.
* `abs_pow_sub_pow_le` — the `[0,1]`-Lipschitz bound `|xᵈ − yᵈ| ≤ d·|x−y|`.
* `DInt'_succ` — the exact β-telescope of the Dirichlet constant.
* `mv_monomial` — the keystone (main-term shape frozen).
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-- The DECOUPLED box: like `kSieveIndex` but WITHOUT pairwise coprimality, and
with cap `z` decoupled from the weight normalization `R`.  Frozen (appears in
`mv_monomial`'s statement). -/
def decBox (n z W' : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range z).filter
    (fun r => (∀ i, Squarefree (r i)) ∧ (∀ i, (r i).Coprime W') ∧ ∏ i, r i < z)

/-! ## The head/tail split of a sum over `decBox (n+1)` -/

/-- Split a sum over `decBox (n+1) z W'` as an outer sum over the head coordinate
`r₀` (squarefree, coprime, `< z`) and an inner sum over the tail box
`decBox n ((z-1)/r₀ + 1) W'`, reindexed by `Fin.cons`. -/
lemma decBox_succ_sum {M : Type*} [AddCommMonoid M] (n z W' : ℕ)
    (f : (Fin (n + 1) → ℕ) → M) :
    ∑ r ∈ decBox (n+1) z W', f r
      = ∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
          ∑ r' ∈ decBox n ((z-1)/r₀ + 1) W', f (Fin.cons r₀ r') := by
  classical
  set HS := (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W') with hHS
  set T : ℕ → Finset (Fin n → ℕ) := fun r₀ => decBox n ((z-1)/r₀ + 1) W' with hT
  rw [← Finset.sum_sigma HS T (fun x => f (Fin.cons x.1 x.2))]
  refine Finset.sum_bij' (fun r _ => (⟨r 0, Fin.tail r⟩ : Σ _ : ℕ, Fin n → ℕ))
    (fun x _ => Fin.cons x.1 x.2) ?hi ?hj ?li ?ri ?val
  case hi =>
    intro r hr
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
    obtain ⟨hpi, hsqf, hcop, hprod⟩ := hr
    have hr0z : r 0 < z := hpi 0
    have hr0pos : 1 ≤ r 0 := Nat.pos_of_ne_zero (hsqf 0).ne_zero
    have hzpos : 1 ≤ z := by omega
    set P := ∏ i, (Fin.tail r) i with hP
    have hsplit : ∏ i, r i = r 0 * P := by rw [Fin.prod_univ_succ]; rfl
    have hmul : r 0 * P < z := by rw [← hsplit]; exact hprod
    have hPr0 : P * r 0 ≤ z - 1 := by rw [Nat.mul_comm]; omega
    have hPle : P ≤ (z - 1) / (r 0) := (Nat.le_div_iff_mul_le hr0pos).mpr hPr0
    have hPlt : P < (z - 1) / (r 0) + 1 := by omega
    rw [Finset.mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [hHS, Finset.mem_filter, Finset.mem_range]; exact ⟨hr0z, hsqf 0, hcop 0⟩
    · rw [hT]
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨?_, ?_, ?_, hPlt⟩
      · intro i
        have hle : (Fin.tail r) i ≤ P :=
          Finset.single_le_prod' (fun j _ => Nat.pos_of_ne_zero (hsqf j.succ).ne_zero)
            (Finset.mem_univ i)
        omega
      · intro i; exact hsqf i.succ
      · intro i; exact hcop i.succ
  case hj =>
    intro x hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hx0, hxt⟩ := hx
    rw [hHS, Finset.mem_filter, Finset.mem_range] at hx0
    obtain ⟨hr0z, hsqf0, hcop0⟩ := hx0
    rw [hT] at hxt
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hxt
    obtain ⟨hpi, hsqf, hcop, hprod⟩ := hxt
    have hr0pos : 1 ≤ x.1 := Nat.pos_of_ne_zero hsqf0.ne_zero
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    have hsplit : ∏ i, (Fin.cons x.1 x.2) i = x.1 * ∏ i, x.2 i := by
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
    have hProdlt : x.1 * ∏ i, x.2 i < z := by
      have hle : (∏ i, x.2 i) ≤ (z - 1) / (x.1) := Nat.lt_succ_iff.mp hprod
      have h2 : (∏ i, x.2 i) * x.1 ≤ z - 1 := (Nat.le_div_iff_mul_le hr0pos).mp hle
      rw [Nat.mul_comm] at h2; omega
    have hz'lez : (z - 1) / (x.1) + 1 ≤ z := by
      have := Nat.div_le_self (z - 1) x.1; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · rw [Fin.cons_zero]; exact hr0z
      · intro j; rw [Fin.cons_succ]; have := hpi j; omega
    · intro i; refine Fin.cases ?_ ?_ i
      · rw [Fin.cons_zero]; exact hsqf0
      · intro j; rw [Fin.cons_succ]; exact hsqf j
    · intro i; refine Fin.cases ?_ ?_ i
      · rw [Fin.cons_zero]; exact hcop0
      · intro j; rw [Fin.cons_succ]; exact hcop j
    · rw [hsplit]; exact hProdlt
  case li =>
    intro r hr; exact Fin.cons_self_tail r
  case ri =>
    intro x hx; simp only [Fin.cons_zero, Fin.tail_cons]
  case val =>
    intro r hr; exact congrArg f (Fin.cons_self_tail r).symm

/-- The single-coordinate reindex: a sum over `decBox 1 z W'` is a sum over the
squarefree-coprime range, evaluated at the constant tuple. -/
lemma decBox_one_sum {M : Type*} [AddCommMonoid M] (z W' : ℕ) (g : (Fin 1 → ℕ) → M) :
    ∑ r ∈ decBox 1 z W', g r
      = ∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
          g (fun _ => r₀) := by
  classical
  refine Finset.sum_bij' (fun r _ => r 0) (fun r₀ _ => (fun _ => r₀)) ?hi ?hj ?li ?ri ?val
  case hi =>
    intro r hr
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr ⊢
    exact ⟨hr.1 0, hr.2.1 0, hr.2.2.1 0⟩
  case hj =>
    intro r₀ hr₀
    simp only [Finset.mem_filter, Finset.mem_range] at hr₀
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
      Fin.prod_univ_one]
    exact ⟨fun _ => hr₀.1, fun _ => hr₀.2.1, fun _ => hr₀.2.2, hr₀.1⟩
  case li => intro r hr; funext i; rw [Fin.fin_one_eq_zero i]
  case ri => intro r₀ hr₀; rfl
  case val => intro r hr; congr 1; funext i; rw [Fin.fin_one_eq_zero i]

/-! ## The `[0,1]`-Lipschitz bound and the Dirichlet telescope -/

/-- For `x, y ∈ [0,1]`, `|xᵈ − yᵈ| ≤ d·|x − y|` (from the geometric factorization
`xᵈ − yᵈ = (∑ᵢ xⁱ yᵈ⁻¹⁻ⁱ)(x − y)`, each summand `≤ 1`). -/
lemma abs_pow_sub_pow_le (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) (d : ℕ) : |x ^ d - y ^ d| ≤ (d : ℝ) * |x - y| := by
  rw [← geom_sum₂_mul x y d, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc |∑ i ∈ Finset.range d, x ^ i * y ^ (d - 1 - i)|
      ≤ ∑ i ∈ Finset.range d, |x ^ i * y ^ (d - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range d, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg hx0, abs_of_nonneg hy0]
        calc x ^ i * y ^ (d - 1 - i) ≤ 1 * 1 :=
              mul_le_mul (pow_le_one₀ hx0 hx1) (pow_le_one₀ hy0 hy1) (pow_nonneg hy0 _)
                (by norm_num)
          _ = 1 := by ring
    _ = (d : ℝ) := by rw [Finset.sum_const, Finset.card_range]; simp

/-- The exact β-telescope of the Dirichlet constant: peeling coordinate `0`
factors `DInt'` into the level-`n` tail constant times the Beta factor
`e₀!·K!/(e₀+K+1)!` with `K = n + d + Σ' e`. -/
lemma DInt'_succ {n : ℕ} (e : Fin (n + 1) → ℕ) (d : ℕ) :
    DInt' e d = DInt' (Fin.tail e) d *
      ((((e 0).factorial * (n + d + ∑ i, (Fin.tail e) i).factorial : ℕ) : ℚ) /
        (((e 0) + (n + d + ∑ i, (Fin.tail e) i) + 1).factorial : ℕ)) := by
  unfold DInt'
  set K := n + d + ∑ i, (Fin.tail e) i with hK
  have hprod : (∏ i, (e i).factorial) = (e 0).factorial * ∏ i, ((Fin.tail e) i).factorial := by
    rw [Fin.prod_univ_succ]; rfl
  have hsum : (∑ i, e i) = e 0 + ∑ i, (Fin.tail e) i := Fin.sum_univ_succ e
  have harg : n + 1 + d + (∑ i, e i) = (e 0) + K + 1 := by rw [hsum, hK]; ring
  rw [hprod, harg]
  have hKfac : ((K.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos K).ne'
  have hAfac : (((e 0 + K + 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  field_simp

/-- `DInt'` is nonnegative (a ratio of `Nat.factorial` products). -/
lemma DInt'_nonneg {n : ℕ} (e : Fin n → ℕ) (d : ℕ) : 0 ≤ ((DInt' e d : ℚ) : ℝ) := by
  rw [DInt']; push_cast; positivity

/-! ## The keystone -/

set_option maxHeartbeats 1600000 in
-- The single-block induction (base cases + the peel step with its three-piece error
-- decomposition and all sub-bounds inline) exceeds the default heartbeat budget.
theorem mv_monomial (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (n : ℕ) (e : Fin n → ℕ) (d : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ r ∈ decBox n z W',
            (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
              / ∏ i, (Nat.totient (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ n
            * ((DInt' e d : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ (n + d + ∑ i, e i)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n - 1) := by
  suffices H : ∀ (N : ℕ) (e : Fin N → ℕ) (d : ℕ), ∃ c : ℝ, 0 ≤ c ∧
      ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
        |(∑ r ∈ decBox N z W', (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
              / ∏ i, (Nat.totient (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ N * ((DInt' e d : ℚ) : ℝ)
              * (Real.log z / Real.log R) ^ (N + d + ∑ i, e i)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (N - 1) by exact H n e d
  clear e d n
  intro N
  induction N with
  | zero =>
    intro e d
    refine ⟨0, le_refl 0, ?_⟩
    intro z R hz hzR hR
    have hset : decBox 0 z W' = {fun i => i.elim0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨?_, ?_⟩
      · simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp; omega⟩
      · intro x _; funext i; exact i.elim0
    rw [hset, Finset.sum_singleton]
    have hDq : DInt' (e : Fin 0 → ℕ) d = 1 := by
      simp only [DInt', Fin.prod_univ_zero, Fin.sum_univ_zero, one_mul, Nat.zero_add, Nat.add_zero]
      exact div_self (by exact_mod_cast (Nat.factorial_pos d).ne')
    have hD : ((DInt' (e : Fin 0 → ℕ) d : ℚ) : ℝ) = 1 := by rw [hDq]; norm_num
    simp only [Fin.prod_univ_zero, Fin.sum_univ_zero, sub_zero, div_one, pow_zero, one_mul,
      Nat.zero_add, Nat.add_zero, hD, mul_one, sub_self, abs_zero]
    positivity
  | succ m IH =>
    intro e d
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · -- n = 1 : reduce to `budget_moment`
      obtain ⟨Catom, hCatom0, hCatom⟩ := budget_moment W' hW' hpos hUpper (e 0) d
      refine ⟨Catom * 4 ^ (d + e 0), by positivity, ?_⟩
      intro z R hz hzR hR
      rw [decBox_one_sum]
      have hsimp : ∀ r₀ : ℕ,
          (∏ i, (Real.log ((fun _ : Fin 1 => r₀) i) / Real.log R) ^ e i)
            * ((Real.log z - ∑ i, Real.log ((fun _ : Fin 1 => r₀) i)) / Real.log R) ^ d
            / ∏ i, (Nat.totient ((fun _ : Fin 1 => r₀) i) : ℝ)
          = (Real.log r₀ / Real.log R) ^ e 0
              * ((Real.log z - Real.log r₀) / Real.log R) ^ d / (Nat.totient r₀ : ℝ) := by
        intro r₀; simp only [Fin.prod_univ_one, Fin.sum_univ_one]
      simp_rw [hsimp]
      have hDcast : ((DInt' e d : ℚ) : ℝ)
          = (((e 0).factorial * d.factorial : ℝ)) / ((e 0) + d + 1).factorial := by
        have hq : DInt' e d
            = (((e 0).factorial * d.factorial : ℕ) : ℚ) / (((e 0) + d + 1).factorial : ℕ) := by
          unfold DInt'
          rw [Fin.prod_univ_one, Fin.sum_univ_one, show (0 : ℕ) + 1 + d + e 0 = e 0 + d + 1 by ring]
        rw [hq]; push_cast; ring
      have hexp : (0 + 1) + d + ∑ i, e i = (e 0) + d + 1 := by rw [Fin.sum_univ_one]; ring
      have hmain : ((W'.totient : ℝ) / W' * Real.log R) ^ (0 + 1) * ((DInt' e d : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ ((0 + 1) + d + ∑ i, e i)
          = (Nat.totient W' / W' : ℝ) * Real.log R
              * ((((e 0).factorial * d.factorial : ℝ)) / ((e 0) + d + 1).factorial)
              * (Real.log z / Real.log R) ^ ((e 0) + d + 1) := by
        rw [hDcast, hexp]; ring
      rw [hmain]
      have hkey := hCatom z R hz hzR hR
      simpa using hkey
    · -- n = m + 1, m ≥ 1 : the general peel
      obtain ⟨ct, hct0, hct⟩ := IH (Fin.tail e) d
      obtain ⟨c0, hc00, hc0⟩ := IH (fun _ => 0) 0
      obtain ⟨cb1, hcb10, hcb1⟩ := budget_moment W' hW' hpos hUpper (e 0) 0
      obtain ⟨cb2, hcb20, hcb2⟩ :=
        budget_moment W' hW' hpos hUpper (e 0) (m + d + ∑ i, (Fin.tail e) i)
      set K := m + d + ∑ i, (Fin.tail e) i with hKdef
      set Dt : ℝ := ((DInt' (Fin.tail e) d : ℚ) : ℝ) with hDtdef
      have hDt0 : 0 ≤ Dt := DInt'_nonneg _ _
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      set D0 : ℝ := ((DInt' (fun _ : Fin m => 0) 0 : ℚ) : ℝ) with hD0def
      have hD00 : 0 ≤ D0 := DInt'_nonneg _ _
      set Q0 : ℝ := D0 + c0 with hQ0def
      have hQ00 : 0 ≤ Q0 := add_nonneg hD00 hc00
      set G : ℝ := (d : ℝ) * Real.log 2 * Q0 + Dt * (K : ℝ) * Real.log 2 with hGdef
      have hG0 : 0 ≤ G := add_nonneg
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hlog2) hQ00)
        (mul_nonneg (mul_nonneg hDt0 (Nat.cast_nonneg K)) hlog2)
      set C' : ℝ := cb1 * 4 ^ (e 0) with hC'def
      have hC'0 : 0 ≤ C' := mul_nonneg hcb10 (by positivity)
      refine ⟨(ct + G) * (1 + C') + Dt * cb2 * 4 ^ (K + e 0),
        add_nonneg (mul_nonneg (add_nonneg hct0 hG0) (by linarith))
          (mul_nonneg (mul_nonneg hDt0 hcb20) (by positivity)), ?_⟩
      intro z R hz hzR hR
      have hLpos : 0 < Real.log R := lt_of_lt_of_le zero_lt_one hR
      set X : ℝ := (W'.totient : ℝ) / W' * Real.log R with hXdef
      have hX0 : 0 ≤ X := by rw [hXdef]; exact mul_nonneg (by positivity) hLpos.le
      have h1X0 : (0 : ℝ) ≤ 1 + X := by linarith
      have hXleL : X ≤ Real.log R := by
        rw [hXdef]
        calc (W'.totient : ℝ) / W' * Real.log R ≤ 1 * Real.log R :=
              mul_le_mul_of_nonneg_right
                (by rw [div_le_one (by exact_mod_cast hpos)]; exact_mod_cast Nat.totient_le W')
                hLpos.le
          _ = Real.log R := one_mul _
      rw [Nat.add_sub_cancel]
      -- abbreviations for the peel
      set head : ℕ → ℝ := fun r₀ =>
        (Real.log r₀ / Real.log R) ^ e 0 / (Nat.totient r₀ : ℝ) with hheaddef
      set Sinner : ℕ → ℝ := fun r₀ =>
        ∑ r' ∈ decBox m ((z - 1) / r₀ + 1) W',
          (∏ i, (Real.log (r' i) / Real.log R) ^ (Fin.tail e) i)
            * ((Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)) / Real.log R) ^ d
            / ∏ i, (Nat.totient (r' i) : ℝ) with hSinnerdef
      set MI : ℕ → ℝ := fun r₀ =>
        X ^ m * Dt * ((Real.log z - Real.log r₀) / Real.log R) ^ K with hMIdef
      -- (a) the head/tail split
      have ha : (∑ r ∈ decBox (m + 1) z W',
            (∏ i, (Real.log (r i) / Real.log R) ^ e i)
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ d
              / ∏ i, (Nat.totient (r i) : ℝ))
          = ∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
              head r₀ * Sinner r₀ := by
        rw [decBox_succ_sum m z W']
        refine Finset.sum_congr rfl (fun r₀ hr₀ => ?_)
        simp only [hheaddef, hSinnerdef]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r' hr' => ?_)
        rw [Fin.prod_univ_succ
              (fun i => (Real.log ((Fin.cons r₀ r' : Fin (m + 1) → ℕ) i) / Real.log R) ^ e i),
            Fin.sum_univ_succ (fun i => Real.log ((Fin.cons r₀ r' : Fin (m + 1) → ℕ) i)),
            Fin.prod_univ_succ
              (fun i => (Nat.totient ((Fin.cons r₀ r' : Fin (m + 1) → ℕ) i) : ℝ))]
        simp only [Fin.cons_zero, Fin.cons_succ,
          show ∀ i : Fin m, e i.succ = (Fin.tail e) i from fun _ => rfl]
        rw [show Real.log z - (Real.log r₀ + ∑ i, Real.log (r' i))
              = Real.log z - Real.log r₀ - ∑ i, Real.log (r' i) from by ring]
        ring
      rw [ha]
      -- membership facts for the outer coordinate
      have hmemHS : ∀ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
          1 ≤ r₀ ∧ r₀ < z := by
        intro r₀ hr₀
        rw [Finset.mem_filter, Finset.mem_range] at hr₀
        exact ⟨Nat.pos_of_ne_zero hr₀.2.1.ne_zero, hr₀.1⟩
      -- (d) head ≥ 0
      have hHeadNonneg : ∀ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
          0 ≤ head r₀ := by
        intro r₀ hr₀
        obtain ⟨hr₀1, _⟩ := hmemHS r₀ hr₀
        have : (0 : ℝ) ≤ Real.log r₀ := Real.log_nonneg (by exact_mod_cast hr₀1)
        simp only [hheaddef]
        exact div_nonneg (pow_nonneg (div_nonneg this hLpos.le) _) (Nat.cast_nonneg _)
      -- (c) the per-r₀ inner estimate
      have hInner : ∀ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
          |Sinner r₀ - MI r₀|
            ≤ ct * (1 + X) ^ (m - 1) + (1 / Real.log R) * G * (1 + X) ^ m := by
        intro r₀ hr₀
        obtain ⟨hr₀1, hr₀z⟩ := hmemHS r₀ hr₀
        set zc := (z - 1) / r₀ + 1 with hzcdef
        have hzc1 : 1 ≤ (z - 1) / r₀ := (Nat.le_div_iff_mul_le hr₀1).mpr (by omega)
        have hzc2 : 2 ≤ zc := by omega
        have hzcz : zc ≤ z := by have := Nat.div_le_self (z - 1) r₀; omega
        have hzcR : zc ≤ R := le_trans hzcz hzR
        have hlogr₀0 : (0 : ℝ) ≤ Real.log r₀ := Real.log_nonneg (by exact_mod_cast hr₀1)
        have hlogzc0 : (0 : ℝ) ≤ Real.log zc :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ zc))
        have hlogzcR : Real.log zc ≤ Real.log R :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < zc)) (by exact_mod_cast hzcR)
        have hlogr₀z : Real.log r₀ ≤ Real.log z :=
          Real.log_le_log (by exact_mod_cast hr₀1) (by exact_mod_cast (by omega : r₀ ≤ z))
        have hlogzR : Real.log z ≤ Real.log R :=
          Real.log_le_log (by exact_mod_cast (by omega : (0:ℕ) < z)) (by exact_mod_cast hzR)
        set S_target : ℝ := ∑ r ∈ decBox m zc W',
          (∏ i, (Real.log (r i) / Real.log R) ^ (Fin.tail e) i)
            * ((Real.log zc - ∑ i, Real.log (r i)) / Real.log R) ^ d
            / ∏ i, (Nat.totient (r i) : ℝ) with hStdef
        set MT : ℝ := X ^ m * Dt * (Real.log zc / Real.log R) ^ K with hMTdef
        -- (A) IH at zc
        have hpA : |S_target - MT| ≤ ct * (1 + X) ^ (m - 1) := by
          have hc := hct zc R hzc2 hzcR hR
          rw [← hXdef] at hc
          rw [hStdef, hMTdef]; exact hc
        -- (C) deterministic slip
        have hnc : |Real.log zc - (Real.log z - Real.log r₀)| ≤ Real.log 2 := by
          have := log_natCap_slip r₀ z hr₀1 hr₀z
          rwa [← hzcdef] at this
        have hb2nn : (0 : ℝ) ≤ (Real.log z - Real.log r₀) / Real.log R :=
          div_nonneg (by linarith) hLpos.le
        have hb2le : (Real.log z - Real.log r₀) / Real.log R ≤ 1 :=
          (div_le_one hLpos).mpr (by linarith)
        have hb1nn : (0 : ℝ) ≤ Real.log zc / Real.log R := div_nonneg hlogzc0 hLpos.le
        have hb1le : Real.log zc / Real.log R ≤ 1 := (div_le_one hLpos).mpr hlogzcR
        have hpC : |MT - MI r₀| ≤ (1 / Real.log R) * (Dt * (K : ℝ) * Real.log 2) * (1 + X) ^ m := by
          rw [hMTdef, hMIdef, ← mul_sub, abs_mul,
            abs_of_nonneg (mul_nonneg (pow_nonneg hX0 m) hDt0)]
          have hslip : |Real.log zc / Real.log R - (Real.log z - Real.log r₀) / Real.log R|
              ≤ Real.log 2 / Real.log R := by
            rw [div_sub_div_same, abs_div, abs_of_pos hLpos]
            gcongr
          have hlip := abs_pow_sub_pow_le (Real.log zc / Real.log R)
            ((Real.log z - Real.log r₀) / Real.log R) hb1nn hb1le hb2nn hb2le K
          calc X ^ m * Dt
                * |(Real.log zc / Real.log R) ^ K
                  - ((Real.log z - Real.log r₀) / Real.log R) ^ K|
              ≤ X ^ m * Dt * ((K : ℝ) * (Real.log 2 / Real.log R)) := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hX0 m) hDt0)
                calc |(Real.log zc / Real.log R) ^ K
                      - ((Real.log z - Real.log r₀) / Real.log R) ^ K|
                    ≤ (K : ℝ) * |Real.log zc / Real.log R
                        - (Real.log z - Real.log r₀) / Real.log R| := hlip
                  _ ≤ (K : ℝ) * (Real.log 2 / Real.log R) :=
                      mul_le_mul_of_nonneg_left hslip (Nat.cast_nonneg K)
            _ ≤ (1 + X) ^ m * Dt * ((K : ℝ) * (Real.log 2 / Real.log R)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX0 (by linarith) m) hDt0
            _ = (1 / Real.log R) * (Dt * (K : ℝ) * Real.log 2) * (1 + X) ^ m := by ring
        -- (B) the slip-sum bound
        have hSum1 : (∑ r' ∈ decBox m zc W', (1 : ℝ) / ∏ i, (Nat.totient (r' i) : ℝ))
            ≤ Q0 * (1 + X) ^ m := by
          have hc0' := hc0 zc R hzc2 hzcR hR
          rw [← hXdef] at hc0'
          have hsum0 : (∑ r ∈ decBox m zc W',
                (∏ i, (Real.log (r i) / Real.log R) ^ (fun _ : Fin m => 0) i)
                  * ((Real.log zc - ∑ i, Real.log (r i)) / Real.log R) ^ 0
                  / ∏ i, (Nat.totient (r i) : ℝ))
              = ∑ r' ∈ decBox m zc W', (1 : ℝ) / ∏ i, (Nat.totient (r' i) : ℝ) := by
            refine Finset.sum_congr rfl (fun r _ => ?_); simp
          have hexp0 : m + 0 + ∑ i, ((fun _ : Fin m => 0) i) = m := by simp
          rw [hsum0, hexp0] at hc0'
          have hb := (abs_le.mp hc0').2
          have hmterm : X ^ m * D0 * (Real.log zc / Real.log R) ^ m ≤ (1 + X) ^ m * D0 := by
            have h1 : X ^ m * (Real.log zc / Real.log R) ^ m ≤ (1 + X) ^ m := by
              calc X ^ m * (Real.log zc / Real.log R) ^ m ≤ X ^ m * 1 :=
                    mul_le_mul_of_nonneg_left (pow_le_one₀ hb1nn hb1le) (pow_nonneg hX0 m)
                _ = X ^ m := mul_one _
                _ ≤ (1 + X) ^ m := pow_le_pow_left₀ hX0 (by linarith) m
            calc X ^ m * D0 * (Real.log zc / Real.log R) ^ m
                = D0 * (X ^ m * (Real.log zc / Real.log R) ^ m) := by ring
              _ ≤ D0 * (1 + X) ^ m := mul_le_mul_of_nonneg_left h1 hD00
              _ = (1 + X) ^ m * D0 := by ring
          have herr : c0 * (1 + X) ^ (m - 1) ≤ c0 * (1 + X) ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (Nat.sub_le m 1)) hc00
          have hQexp : Q0 * (1 + X) ^ m = (1 + X) ^ m * D0 + c0 * (1 + X) ^ m := by
            rw [hQ0def]; ring
          rw [hQexp]
          linarith [hb, hmterm, herr]
        have hpB : |Sinner r₀ - S_target|
            ≤ (1 / Real.log R) * ((d : ℝ) * Real.log 2 * Q0) * (1 + X) ^ m := by
          have hdiff : Sinner r₀ - S_target
              = ∑ r' ∈ decBox m zc W',
                  (∏ i, (Real.log (r' i) / Real.log R) ^ (Fin.tail e) i)
                    / (∏ i, (Nat.totient (r' i) : ℝ))
                    * (((Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)) / Real.log R) ^ d
                      - ((Real.log zc - ∑ i, Real.log (r' i)) / Real.log R) ^ d) := by
            simp only [hSinnerdef, hStdef, ← hzcdef]
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl (fun r' _ => by ring)
          have hpertm : ∀ r' ∈ decBox m zc W',
              |(∏ i, (Real.log (r' i) / Real.log R) ^ (Fin.tail e) i)
                    / (∏ i, (Nat.totient (r' i) : ℝ))
                    * (((Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)) / Real.log R) ^ d
                      - ((Real.log zc - ∑ i, Real.log (r' i)) / Real.log R) ^ d)|
                ≤ (1 / ∏ i, (Nat.totient (r' i) : ℝ)) * ((d : ℝ) * (Real.log 2 / Real.log R)) := by
            intro r' hr'
            simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr'
            obtain ⟨hlt, hsqf, hcop, hprod⟩ := hr'
            have hr'1 : ∀ i, 1 ≤ r' i := fun i => Nat.pos_of_ne_zero (hsqf i).ne_zero
            have hlogr'0 : ∀ i, (0 : ℝ) ≤ Real.log (r' i) :=
              fun i => Real.log_nonneg (by exact_mod_cast hr'1 i)
            have hlogr'R : ∀ i, Real.log (r' i) ≤ Real.log R := fun i =>
              Real.log_le_log (by exact_mod_cast hr'1 i)
                (by exact_mod_cast (by have := hlt i; omega : r' i ≤ R))
            have hPpos : (0 : ℝ) < ∏ i, (Nat.totient (r' i) : ℝ) :=
              Finset.prod_pos (fun i _ => by
                have := hr'1 i; exact_mod_cast Nat.totient_pos.mpr (by omega))
            have hA0 : (0 : ℝ) ≤ ∏ i, (Real.log (r' i) / Real.log R) ^ (Fin.tail e) i :=
              Finset.prod_nonneg (fun i _ => pow_nonneg (div_nonneg (hlogr'0 i) hLpos.le) _)
            have hA1 : (∏ i, (Real.log (r' i) / Real.log R) ^ (Fin.tail e) i) ≤ 1 :=
              Finset.prod_le_one (fun i _ => pow_nonneg (div_nonneg (hlogr'0 i) hLpos.le) _)
                (fun i _ => pow_le_one₀ (div_nonneg (hlogr'0 i) hLpos.le)
                  ((div_le_one hLpos).mpr (hlogr'R i)))
            have hprodpos : 0 < ∏ i, r' i := Finset.prod_pos (fun i _ => by have := hr'1 i; omega)
            have hSLnn : (0 : ℝ) ≤ ∑ i, Real.log (r' i) := Finset.sum_nonneg (fun i _ => hlogr'0 i)
            have hne : ∀ i ∈ (Finset.univ : Finset (Fin m)), ((r' i : ℝ)) ≠ 0 :=
              fun i _ => by exact_mod_cast Nat.one_le_iff_ne_zero.mp (hr'1 i)
            have hSLeq : ∑ i, Real.log (r' i) = Real.log ((∏ i, r' i : ℕ) : ℝ) := by
              rw [Nat.cast_prod, ← Real.log_prod hne]
            have hSLub_zc : ∑ i, Real.log (r' i) ≤ Real.log zc := by
              rw [hSLeq]
              exact Real.log_le_log (by exact_mod_cast hprodpos)
                (by exact_mod_cast (by omega : (∏ i, r' i) ≤ zc))
            have hr₀PP : r₀ * ∏ i, r' i ≤ z - 1 := by
              have hp := hprod
              rw [hzcdef] at hp
              have h1 : (∏ i, r' i) ≤ (z - 1) / r₀ := Nat.lt_succ_iff.mp hp
              have h2 : (∏ i, r' i) * r₀ ≤ z - 1 := (Nat.le_div_iff_mul_le hr₀1).mp h1
              rw [Nat.mul_comm] at h2; exact h2
            have hSLub_z : Real.log r₀ + ∑ i, Real.log (r' i) ≤ Real.log z := by
              rw [hSLeq, ← Real.log_mul (by exact_mod_cast (by omega : r₀ ≠ 0))
                (by exact_mod_cast hprodpos.ne'), ← Nat.cast_mul]
              exact Real.log_le_log (by exact_mod_cast (by positivity : 0 < r₀ * ∏ i, r' i))
                (by exact_mod_cast (by omega : r₀ * ∏ i, r' i ≤ z))
            have hbTnn : (0 : ℝ) ≤ (Real.log zc - ∑ i, Real.log (r' i)) / Real.log R :=
              div_nonneg (by linarith) hLpos.le
            have hbTle : (Real.log zc - ∑ i, Real.log (r' i)) / Real.log R ≤ 1 :=
              (div_le_one hLpos).mpr (by linarith [hlogzcR])
            have hbInn : (0 : ℝ) ≤ (Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)) / Real.log R :=
              div_nonneg (by linarith) hLpos.le
            have hbIle : (Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)) / Real.log R ≤ 1 :=
              (div_le_one hLpos).mpr (by linarith [hlogzR])
            have hbdiff : |(Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)) / Real.log R
                - (Real.log zc - ∑ i, Real.log (r' i)) / Real.log R| ≤ Real.log 2 / Real.log R := by
              rw [div_sub_div_same, abs_div, abs_of_pos hLpos,
                show Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)
                    - (Real.log zc - ∑ i, Real.log (r' i))
                  = -(Real.log zc - (Real.log z - Real.log r₀)) from by ring, abs_neg]
              gcongr
            have hpowdiff : |((Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)) / Real.log R) ^ d
                - ((Real.log zc - ∑ i, Real.log (r' i)) / Real.log R) ^ d|
                ≤ (d : ℝ) * (Real.log 2 / Real.log R) :=
              le_trans (abs_pow_sub_pow_le _ _ hbInn hbIle hbTnn hbTle d)
                (mul_le_mul_of_nonneg_left hbdiff (Nat.cast_nonneg d))
            rw [abs_mul, abs_of_nonneg (div_nonneg hA0 hPpos.le)]
            apply mul_le_mul _ hpowdiff (abs_nonneg _) (by positivity)
            gcongr
          rw [hdiff]
          calc |∑ r' ∈ decBox m zc W',
                (∏ i, (Real.log (r' i) / Real.log R) ^ (Fin.tail e) i)
                  / (∏ i, (Nat.totient (r' i) : ℝ))
                  * (((Real.log z - Real.log r₀ - ∑ i, Real.log (r' i)) / Real.log R) ^ d
                    - ((Real.log zc - ∑ i, Real.log (r' i)) / Real.log R) ^ d)|
              ≤ ∑ r' ∈ decBox m zc W',
                  (1 / ∏ i, (Nat.totient (r' i) : ℝ)) * ((d : ℝ) * (Real.log 2 / Real.log R)) :=
                le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hpertm)
            _ = ((d : ℝ) * (Real.log 2 / Real.log R))
                * ∑ r' ∈ decBox m zc W', (1 : ℝ) / ∏ i, (Nat.totient (r' i) : ℝ) := by
                rw [← Finset.sum_mul, mul_comm]
            _ ≤ ((d : ℝ) * (Real.log 2 / Real.log R)) * (Q0 * (1 + X) ^ m) :=
                mul_le_mul_of_nonneg_left hSum1 (by positivity)
            _ = (1 / Real.log R) * ((d : ℝ) * Real.log 2 * Q0) * (1 + X) ^ m := by ring
        calc |Sinner r₀ - MI r₀|
            ≤ |Sinner r₀ - S_target| + |S_target - MT| + |MT - MI r₀| := by
              have t1 := abs_sub_le (Sinner r₀) S_target (MI r₀)
              have t2 := abs_sub_le S_target MT (MI r₀)
              linarith
          _ ≤ (1 / Real.log R) * ((d : ℝ) * Real.log 2 * Q0) * (1 + X) ^ m
                + ct * (1 + X) ^ (m - 1)
                + (1 / Real.log R) * (Dt * (K : ℝ) * Real.log 2) * (1 + X) ^ m :=
              add_le_add (add_le_add hpB hpA) hpC
          _ = ct * (1 + X) ^ (m - 1) + (1 / Real.log R) * G * (1 + X) ^ m := by
              rw [hGdef]; ring
      -- (e) the head-sum bound
      have hHeadSum : ∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
          head r₀ ≤ X + C' := by
        have hbm1 := hcb1 z R hz hzR hR
        rw [← hXdef] at hbm1
        have hsumeq : (∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
              head r₀)
            = ∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
                (Real.log r / Real.log R) ^ e 0
                  * ((Real.log z - Real.log r) / Real.log R) ^ 0 / (Nat.totient r : ℝ) := by
          refine Finset.sum_congr rfl (fun r₀ _ => ?_)
          simp only [hheaddef, pow_zero, mul_one]
        rw [hsumeq]
        have hmain_le : X * ((e 0).factorial * (0 : ℕ).factorial / ((e 0) + 0 + 1).factorial)
              * (Real.log z / Real.log R) ^ ((e 0) + 0 + 1) ≤ X := by
          have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
          have hZL : (Real.log z / Real.log R) ^ ((e 0) + 0 + 1) ≤ 1 :=
            pow_le_one₀ (div_nonneg (Real.log_nonneg hz1) hLpos.le)
              ((div_le_one hLpos).mpr (Real.log_le_log (by linarith) (by exact_mod_cast hzR)))
          have hβ : ((e 0).factorial * (0 : ℕ).factorial / ((e 0) + 0 + 1).factorial : ℝ) ≤ 1 := by
            have h1 : (e 0).factorial * (0 : ℕ).factorial ≤ ((e 0) + 0 + 1).factorial := by
              simp only [Nat.factorial_zero, mul_one, Nat.add_zero]
              exact Nat.factorial_le (Nat.le_succ _)
            rw [div_le_one (by positivity)]; exact_mod_cast h1
          calc X * ((e 0).factorial * (0 : ℕ).factorial / ((e 0) + 0 + 1).factorial)
                  * (Real.log z / Real.log R) ^ ((e 0) + 0 + 1)
              ≤ X * 1 * 1 := by
                apply mul_le_mul (mul_le_mul_of_nonneg_left hβ hX0) hZL (by positivity)
                  (by positivity)
            _ = X := by ring
        have hthis := (abs_le.mp hbm1).2
        rw [Nat.zero_add] at hthis
        simp only [hC'def]
        linarith [hthis, hmain_le]
      -- (b') the E2 error: ∑ head·MI vs Main
      have hE2 : |(∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
              head r₀ * MI r₀)
            - X ^ (m + 1) * ((DInt' e d : ℚ) : ℝ)
                * (Real.log z / Real.log R) ^ ((m + 1) + d + ∑ i, e i)|
          ≤ Dt * cb2 * 4 ^ (K + e 0) * (1 + X) ^ m := by
        have hbm2 := hcb2 z R hz hzR hR
        rw [← hXdef] at hbm2
        have hSMI : (∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
              head r₀ * MI r₀)
            = X ^ m * Dt * ∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
                (Real.log r / Real.log R) ^ e 0
                  * ((Real.log z - Real.log r) / Real.log R) ^ K / (Nat.totient r : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun r₀ _ => ?_)
          simp only [hheaddef, hMIdef]; ring
        have htel : ((DInt' e d : ℚ) : ℝ)
            = Dt * (((e 0).factorial * K.factorial : ℝ) / ((e 0) + K + 1).factorial) := by
          rw [hDtdef]
          have hts := DInt'_succ e d
          rw [← hKdef] at hts
          rw [hts]; push_cast; ring
        have hexp : (m + 1) + d + ∑ i, e i = (e 0) + K + 1 := by
          have hs : ∑ i, e i = e 0 + ∑ i, (Fin.tail e) i := Fin.sum_univ_succ e
          rw [hs, hKdef]; ring
        have hMainEq : X ^ (m + 1) * ((DInt' e d : ℚ) : ℝ)
              * (Real.log z / Real.log R) ^ ((m + 1) + d + ∑ i, e i)
            = X ^ m * Dt * (X * ((e 0).factorial * K.factorial / ((e 0) + K + 1).factorial)
                * (Real.log z / Real.log R) ^ ((e 0) + K + 1)) := by
          rw [htel, hexp, pow_succ]; ring
        rw [hSMI, hMainEq, ← mul_sub, abs_mul,
          abs_of_nonneg (mul_nonneg (pow_nonneg hX0 m) hDt0)]
        calc X ^ m * Dt
              * |(∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
                  (Real.log r / Real.log R) ^ e 0
                    * ((Real.log z - Real.log r) / Real.log R) ^ K / (Nat.totient r : ℝ))
                - X * ((e 0).factorial * K.factorial / ((e 0) + K + 1).factorial)
                    * (Real.log z / Real.log R) ^ ((e 0) + K + 1)|
            ≤ X ^ m * Dt * (cb2 * 4 ^ (K + e 0)) :=
              mul_le_mul_of_nonneg_left hbm2 (mul_nonneg (pow_nonneg hX0 m) hDt0)
          _ ≤ (1 + X) ^ m * Dt * (cb2 * 4 ^ (K + e 0)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX0 (by linarith) m) hDt0
          _ = Dt * cb2 * 4 ^ (K + e 0) * (1 + X) ^ m := by ring
      -- combine E1 (inner) and E2
      have hsplit3 : |(∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
              head r₀ * Sinner r₀)
            - X ^ (m + 1) * ((DInt' e d : ℚ) : ℝ)
                * (Real.log z / Real.log R) ^ ((m + 1) + d + ∑ i, e i)|
          ≤ |(∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                head r₀ * Sinner r₀)
              - (∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                  head r₀ * MI r₀)|
            + |(∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                  head r₀ * MI r₀)
              - X ^ (m + 1) * ((DInt' e d : ℚ) : ℝ)
                  * (Real.log z / Real.log R) ^ ((m + 1) + d + ∑ i, e i)| :=
        abs_sub_le _ _ _
      -- E1 bound
      have hE1 : |(∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
              head r₀ * Sinner r₀)
            - (∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                head r₀ * MI r₀)|
          ≤ (ct + G) * (1 + C') * (1 + X) ^ m := by
        have hsub : (∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
              head r₀ * Sinner r₀)
            - (∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                head r₀ * MI r₀)
            = ∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                head r₀ * (Sinner r₀ - MI r₀) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun r₀ _ => by rw [mul_sub])
        rw [hsub]
        set Bnd : ℝ := ct * (1 + X) ^ (m - 1) + (1 / Real.log R) * G * (1 + X) ^ m with hBnddef
        have hBnd0 : 0 ≤ Bnd := by
          rw [hBnddef]
          exact add_nonneg (mul_nonneg hct0 (by positivity))
            (mul_nonneg (mul_nonneg (by positivity) hG0) (by positivity))
        calc |∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                head r₀ * (Sinner r₀ - MI r₀)|
            ≤ ∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                |head r₀ * (Sinner r₀ - MI r₀)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                head r₀ * Bnd := by
              refine Finset.sum_le_sum (fun r₀ hr₀ => ?_)
              rw [abs_mul, abs_of_nonneg (hHeadNonneg r₀ hr₀)]
              exact mul_le_mul_of_nonneg_left (hInner r₀ hr₀) (hHeadNonneg r₀ hr₀)
          _ = (∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
                head r₀) * Bnd := by rw [Finset.sum_mul]
          _ ≤ (X + C') * Bnd :=
              mul_le_mul_of_nonneg_right hHeadSum hBnd0
          _ ≤ (ct + G) * (1 + C') * (1 + X) ^ m := by
              rw [hBnddef]
              have hP : (0 : ℝ) ≤ (1 + X) ^ m := by positivity
              have hP1 : (0 : ℝ) ≤ (1 + X) ^ (m - 1) := by positivity
              have hP1X : (1 + X) ^ (m - 1) * X ≤ (1 + X) ^ m := by
                calc (1 + X) ^ (m - 1) * X ≤ (1 + X) ^ (m - 1) * (1 + X) := by
                      apply mul_le_mul_of_nonneg_left (by linarith) hP1
                  _ = (1 + X) ^ ((m - 1) + 1) := by rw [pow_succ]
                  _ = (1 + X) ^ m := by rw [Nat.sub_add_cancel hmpos]
              have hP1P : (1 + X) ^ (m - 1) ≤ (1 + X) ^ m :=
                pow_le_pow_right₀ (by linarith) (by omega)
              have hLXP : (1 / Real.log R) * (1 + X) ^ m * X ≤ (1 + X) ^ m := by
                rw [show (1 / Real.log R) * (1 + X) ^ m * X = (1 + X) ^ m * X / Real.log R by ring,
                  div_le_iff₀ hLpos]
                exact mul_le_mul_of_nonneg_left hXleL hP
              have hL1 : (1 / Real.log R) ≤ 1 := by
                rw [div_le_one hLpos]; exact hR
              have k1 : ct * ((1 + X) ^ (m - 1) * X) ≤ ct * (1 + X) ^ m :=
                mul_le_mul_of_nonneg_left hP1X hct0
              have k2 : ct * C' * (1 + X) ^ (m - 1) ≤ ct * C' * (1 + X) ^ m :=
                mul_le_mul_of_nonneg_left hP1P (mul_nonneg hct0 hC'0)
              have k3 : G * (1 / Real.log R * (1 + X) ^ m * X) ≤ G * (1 + X) ^ m :=
                mul_le_mul_of_nonneg_left hLXP hG0
              have k4 : G * C' * (1 / Real.log R * (1 + X) ^ m) ≤ G * C' * (1 + X) ^ m := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg hG0 hC'0)
                calc 1 / Real.log R * (1 + X) ^ m ≤ 1 * (1 + X) ^ m :=
                      mul_le_mul_of_nonneg_right hL1 hP
                  _ = (1 + X) ^ m := one_mul _
              have hexpand : (X + C') * (ct * (1 + X) ^ (m - 1) + 1 / Real.log R * G * (1 + X) ^ m)
                  = ct * ((1 + X) ^ (m - 1) * X) + ct * C' * (1 + X) ^ (m - 1)
                    + G * (1 / Real.log R * (1 + X) ^ m * X)
                    + G * C' * (1 / Real.log R * (1 + X) ^ m) := by ring
              have hrhs : (ct + G) * (1 + C') * (1 + X) ^ m
                  = ct * (1 + X) ^ m + ct * C' * (1 + X) ^ m + G * (1 + X) ^ m
                    + G * C' * (1 + X) ^ m := by ring
              rw [hexpand, hrhs]
              linarith [k1, k2, k3, k4]
      -- final assembly
      calc |(∑ r₀ ∈ (Finset.range z).filter (fun r₀ => Squarefree r₀ ∧ r₀.Coprime W'),
              head r₀ * Sinner r₀)
            - X ^ (m + 1) * ((DInt' e d : ℚ) : ℝ)
                * (Real.log z / Real.log R) ^ ((m + 1) + d + ∑ i, e i)|
          ≤ _ + _ := hsplit3
        _ ≤ (ct + G) * (1 + C') * (1 + X) ^ m + Dt * cb2 * 4 ^ (K + e 0) * (1 + X) ^ m :=
            add_le_add hE1 hE2
        _ = ((ct + G) * (1 + C') + Dt * cb2 * 4 ^ (K + e 0)) * (1 + X) ^ m := by ring

end Salt.Twelve
