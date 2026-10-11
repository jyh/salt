/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.MvSplit

/-!
# C1 · B4.2a — `mv_I_split` at general `k` for a budget polynomial (`mv_I_split_gen`)

`Fin 5 → Fin k`, `sq (ofPoly F) → P`, `^ 5 → ^ k`, the `40 = 2·C(5,2)·2` collision constant → `2k²`
(pair count `≤ k²`, never `decide` on a card). `mv_I_split_of_gen` recovers the landed statement.
Ported by an Opus executor from a frozen brief (2026-10-11).
-/

open Finset

namespace Salt.MaynardK

open Salt.Twelve

open Salt.Maynard

/-- `phiAtomSum` is a sum of nonnegative terms. -/
private lemma pas_nonneg (z W' : ℕ) : 0 ≤ Salt.Maynard.phiAtomSum z W' := by
  unfold Salt.Maynard.phiAtomSum
  exact Finset.sum_nonneg fun r _ => by positivity


/-! ## General `List`-sum helpers -/

/-- `List`-triangle inequality: `|Σ| ≤ Σ|·|`. -/
private lemma list_abs_sum_le (l : List ℝ) : |l.sum| ≤ (l.map (fun x => |x|)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le a l.sum).trans (by linarith [ih])

/-- Subtraction of two mapped `List`-sums is the sum of the pointwise differences. -/
private lemma list_sum_map_sub {γ : Type*} (l : List γ) (f g : γ → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map (fun x => f x - g x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

/-- Dividing a mapped `List`-sum distributes over the list. -/
private lemma list_sum_map_div {γ : Type*} (l : List γ) (f : γ → ℝ) (c : ℝ) :
    (l.map f).sum / c = (l.map (fun x => f x / c)).sum := by
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]
  simp only [div_eq_mul_inv]

/-- Swap a `Finset`-sum over a box with the `List`-sum over monomials. -/
private lemma sum_finset_list_swap {k : ℕ} {γ : Type*} (B : Finset (Fin k → ℕ))
    (P : List γ) (f : γ → (Fin k → ℕ) → ℝ) :
    ∑ r ∈ B, (P.map (fun m => f m r)).sum = (P.map (fun m => ∑ r ∈ B, f m r)).sum := by
  induction P with
  | nil => simp
  | cons a P ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

/-- Pointwise-`≤` monotonicity of a mapped `List`-sum. -/
private lemma list_sum_map_le {γ : Type*} (l : List γ) (f g : γ → ℝ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    linarith

/-- Nonnegativity of a mapped `List`-sum. -/
private lemma list_map_sum_nonneg {γ : Type*} (l : List γ) (f : γ → ℝ)
    (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    linarith

/-- Addition of two mapped `List`-sums. -/
private lemma list_sum_map_add {γ : Type*} (l : List γ) (f g : γ → ℝ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

/-! ## The prime tail `Σ_{p>D} 1/(p-1)² ≤ 2/D` -/

/-- Telescoping tail over the integer range `(D, R)`: `Σ 1/(k-1)² ≤ 1/(D-1)`. -/
private lemma int_tail (D R : ℕ) (hD : 3 ≤ D) :
    ∑ k ∈ (Finset.range R).filter (fun k => D < k), 1 / ((k:ℝ) - 1)^2
      ≤ 1 / ((D:ℝ) - 1) := by
  have hset : (Finset.range R).filter (fun k => D < k) = Finset.Ico (D+1) R := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  set N := R - (D+1) with hN
  set φ : ℕ → ℝ := fun t => 1 / ((D:ℝ) - 1 + t) with hφ
  have hterm : ∀ t ∈ Finset.range N,
      1 / (((D+1+t:ℕ):ℝ) - 1)^2 ≤ φ t - φ (t+1) := by
    intro t _
    set a : ℝ := (D:ℝ) - 1 + t with ha_def
    have ha : (0:ℝ) < a := by
      have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
      have ht : (0:ℝ) ≤ (t:ℝ) := by positivity
      simp only [ha_def]; linarith
    have ha1 : (0:ℝ) < a + 1 := by linarith
    have hcast : (((D+1+t:ℕ):ℝ) - 1) = a + 1 := by simp only [ha_def]; push_cast; ring
    have hφt : φ t = 1 / a := by simp only [hφ, ha_def]
    have hφt1 : φ (t+1) = 1 / (a+1) := by
      simp only [hφ, ha_def]
      rw [show (D:ℝ) - 1 + (t+1:ℕ) = (D:ℝ) - 1 + t + 1 by push_cast; ring]
    rw [hcast, hφt, hφt1]
    have hstep1 : 1 / (a*(a+1)) = 1/a - 1/(a+1) := by field_simp; ring
    have hle : a * (a+1) ≤ (a+1)^2 := by linarith only [ha]
    have hstep2 : 1 / (a+1)^2 ≤ 1 / (a*(a+1)) :=
      one_div_le_one_div_of_le (mul_pos ha ha1) hle
    rw [← hstep1]; exact hstep2
  calc ∑ t ∈ Finset.range N, 1 / (((D+1+t:ℕ):ℝ) - 1)^2
      ≤ ∑ t ∈ Finset.range N, (φ t - φ (t+1)) := Finset.sum_le_sum hterm
    _ = φ 0 - φ N := Finset.sum_range_sub' φ N
    _ ≤ φ 0 := by
        have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
        have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
        have hpos : (0:ℝ) < (D:ℝ) - 1 + (N:ℝ) := by linarith
        have : 0 ≤ φ N := by simp only [hφ]; exact div_nonneg zero_le_one hpos.le
        linarith
    _ = 1 / ((D:ℝ) - 1) := by simp [hφ]

/-- The prime tail bound: `Σ_{D<p<R} 1/(p-1)² ≤ 2/D`. -/
private lemma prime_tail (D R : ℕ) (hD : 3 ≤ D) :
    ∑ p ∈ (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p), 1 / ((p:ℝ) - 1)^2
      ≤ 2 / (D:ℝ) := by
  have hsub : (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p)
      ⊆ (Finset.range R).filter (fun k => D < k) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  have h1 : ∑ p ∈ (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p), 1 / ((p:ℝ) - 1)^2
      ≤ ∑ k ∈ (Finset.range R).filter (fun k => D < k), 1 / ((k:ℝ) - 1)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _ _; positivity
  have h2 : (1:ℝ) / ((D:ℝ) - 1) ≤ 2 / (D:ℝ) := by
    have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith only [h3]
  linarith [int_tail D R hD, h1, h2]


/-! ## The relative pairwise-collision bound (Stage 2 kernel, `mv_I` side)

Truncation of the landed `Salt.Twelve.badpair_bound` (`MvI.lean`, `private`):
each of the five coordinate factors `∑_{g_k ∣ s} 1/φ(s)` is bounded by
`marked_sqf_phi_rel` at `s = g k`, `a = 0`, `z = R`, giving `(1/φ(g_k))·PAS`
with NO opaque constant. -/

private lemma badpair_bound_rel_gen (k : ℕ) (hk : 2 ≤ k) (W' : ℕ) (hW' : Squarefree W')
        (hpos : 0 < W')
    (R : ℕ) (hR2 : 2 ≤ R) (i j : Fin k) (hij : i ≠ j) (p : ℕ) (hp : Nat.Prime p) :
    ∑ r ∈ (decBox k R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ (Salt.Maynard.phiAtomSum R W') ^ k / ((p:ℝ) - 1) ^ 2 := by
  classical
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set g : Fin k → ℕ := fun k => if k = i ∨ k = j then p else 1 with hg
  have hp2 : 2 ≤ p := hp.two_le
  have hp1R : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    linarith
  have hgpos : ∀ k, 0 < g k := by
    intro k; simp only [hg]; split
    · exact hp.pos
    · exact one_pos
  set coordSet : Fin k → Finset ℕ := fun k =>
    (Finset.range R).filter (fun s => Squarefree s ∧ s.Coprime W' ∧ g k ∣ s) with hcoord
  have hstepA : ∑ r ∈ (decBox k R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ ∏ k, ∑ s ∈ coordSet k, (1 / (Nat.totient s : ℝ)) := by
    rw [Finset.prod_univ_sum coordSet (fun _ s => 1 / (Nat.totient s : ℝ))]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      rw [Finset.mem_filter] at hr
      obtain ⟨hrdec, hpi, hpj⟩ := hr
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hrdec
      obtain ⟨hlt, hsqf, hcop, _⟩ := hrdec
      rw [Fintype.mem_piFinset]
      intro k
      rw [hcoord, Finset.mem_filter, Finset.mem_range]
      refine ⟨hlt k, hsqf k, hcop k, ?_⟩
      simp only [hg]
      split
      · rename_i hcase
        rcases hcase with hki | hkj
        · rw [hki]; exact hpi
        · rw [hkj]; exact hpj
      · exact one_dvd _
    · intro r _ _
      exact Finset.prod_nonneg (fun k _ => by positivity)
  set h : Fin k → ℝ := fun k => ∑ s ∈ coordSet k, (1 / (Nat.totient s : ℝ)) with hh
  have hhnn : ∀ k, 0 ≤ h k := fun k => Finset.sum_nonneg (fun s _ => by positivity)
  have hhle : ∀ k, h k ≤ (1 / (Nat.totient (g k) : ℝ)) * PAS := by
    intro k
    have hkey := marked_sqf_phi_rel W' hW' hpos 0 (g k) R (hgpos k) hR2
    have hrw : ∑ s ∈ coordSet k, (Real.log s) ^ 0 / (Nat.totient s : ℝ) = h k := by
      simp only [hh, hcoord, pow_zero]
    rw [hrw, pow_zero, mul_one, ← hPASdef] at hkey
    exact hkey
  have hgi : g i = p := by simp [hg]
  have hgj : g j = p := by simp [hg]
  have hφp : (Nat.totient p : ℝ) = (p:ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hi_le : h i ≤ PAS / ((p:ℝ) - 1) := by
    have := hhle i; rw [hgi, hφp] at this
    calc h i ≤ 1 / ((p:ℝ) - 1) * PAS := this
      _ = PAS / ((p:ℝ) - 1) := by ring
  have hj_le : h j ≤ PAS / ((p:ℝ) - 1) := by
    have := hhle j; rw [hgj, hφp] at this
    calc h j ≤ 1 / ((p:ℝ) - 1) * PAS := this
      _ = PAS / ((p:ℝ) - 1) := by ring
  have hother : ∀ k ∈ (Finset.univ.erase i).erase j, h k ≤ PAS := by
    intro k hk
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    obtain ⟨hkj, hki, _⟩ := hk
    have hgk : g k = 1 := by simp only [hg]; rw [if_neg (by tauto)]
    have := hhle k; rw [hgk] at this; simpa using this
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hsplit : ∏ k, h k = h i * (h j * ∏ k ∈ (Finset.univ.erase i).erase j, h k) := by
    rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ i),
        ← Finset.mul_prod_erase (Finset.univ.erase i) h hjmem]
  have hcard : ((Finset.univ.erase i).erase j).card = k - 2 := by
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp; omega
  have hprodrest : ∏ k ∈ (Finset.univ.erase i).erase j, h k ≤ PAS ^ (k - 2) := by
    calc ∏ k ∈ (Finset.univ.erase i).erase j, h k
        ≤ ∏ _k ∈ (Finset.univ.erase i).erase j, PAS :=
          Finset.prod_le_prod (fun k _ => hhnn k) hother
      _ = PAS ^ (k - 2) := by rw [Finset.prod_const, hcard]
  have hbnd : ∏ k, h k
      ≤ (PAS / ((p:ℝ) - 1)) * ((PAS / ((p:ℝ) - 1)) * PAS ^ (k - 2)) := by
    rw [hsplit]
    apply mul_le_mul hi_le _ (mul_nonneg (hhnn j) (Finset.prod_nonneg (fun k _ => hhnn k)))
      (div_nonneg hPAS0 hp1R.le)
    apply mul_le_mul hj_le hprodrest (Finset.prod_nonneg (fun k _ => hhnn k))
      (div_nonneg hPAS0 hp1R.le)
  have hfinal : (PAS / ((p:ℝ) - 1)) * ((PAS / ((p:ℝ) - 1)) * PAS ^ (k - 2))
      = PAS ^ k / ((p:ℝ) - 1) ^ 2 := by
    have hne : (p:ℝ) - 1 ≠ 0 := ne_of_gt hp1R
    have e : PAS ^ k = PAS ^ (k - 2) * PAS ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    field_simp
  calc ∑ r ∈ (decBox k R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ ∏ k, h k := hstepA
    _ ≤ _ := hbnd
    _ = PAS ^ k / ((p:ℝ) - 1) ^ 2 := hfinal

/-! ## `mv_I_split` -/

theorem mv_I_split_gen (k : ℕ) (hk : 2 ≤ k) (P : BPoly k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ kSieveIndex k R W',
              eval P (fun i => Real.log (r i) / Real.log R)
                / ∏ i, (Nat.totient (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ k
              * ((simplexInt P : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ k / Real.log R
          + A * (1 + Salt.Maynard.phiAtomSum R W') ^ k / D := by
  classical
  set Qabs : ℝ := (P.map (fun m => |(m.2.2 : ℝ)|)).sum with hQabsdef
  have hQabs0 : 0 ≤ Qabs := by
    rw [hQabsdef]; exact list_map_sum_nonneg _ _ (fun m _ => abs_nonneg _)
  refine ⟨(2 * (k : ℝ) ^ 2) * Qabs, by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  -- per-monomial `mv_monomial` constants
  set Cfun : ((Fin k → ℕ) × ℕ × ℚ) → ℝ :=
    fun m => Classical.choose (mv_monomial W' hW' hpos hUpper k m.1 m.2.1) with hCfundef
  have hCfunspec : ∀ m, 0 ≤ Cfun m ∧ ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ r ∈ decBox k z W',
            (∏ i, (Real.log (r i) / Real.log R) ^ (m.1 i))
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ (m.2.1)
              / ∏ i, (Nat.totient (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ k * ((DInt' m.1 m.2.1 : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ (k + m.2.1 + ∑ i, m.1 i)|
      ≤ Cfun m * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (k - 1) :=
    fun m => Classical.choose_spec (mv_monomial W' hW' hpos hUpper k m.1 m.2.1)
  have hCfun0 : ∀ m, 0 ≤ Cfun m := fun m => (hCfunspec m).1
  set Cmain : ℝ := (P.map (fun m => |(m.2.2 : ℝ)| * Cfun m)).sum with hCmaindef
  have hCmain0 : 0 ≤ Cmain := by
    rw [hCmaindef]
    exact list_map_sum_nonneg _ _ (fun m _ => mul_nonneg (abs_nonneg _) (hCfun0 m))
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  have hκle1 : κ ≤ 1 := by
    rw [hκdef, div_le_one (by exact_mod_cast hpos)]; exact_mod_cast Nat.totient_le W'
  refine ⟨Cmain / κ, div_nonneg hCmain0 hκpos.le, ?_⟩
  intro R hlogR
  -- basic real facts
  have hRpos : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · rw [h] at hlogR; simp at hlogR; linarith
    · exact h
  have hR2 : 2 ≤ R := by
    have hRr : (0:ℝ) < (R:ℝ) := by exact_mod_cast hRpos
    have h2e : (2:ℝ) ≤ Real.exp (Real.log R) := by
      calc (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
        _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hlogR
    rw [Real.exp_log hRr] at h2e
    exact_mod_cast h2e
  set L : ℝ := Real.log R with hLdef
  set X : ℝ := (W'.totient : ℝ) / W' * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXκL : X = κ * L := by rw [hXdef, hκdef, hLdef]
  have hX0 : 0 ≤ X := by rw [hXκL]; exact mul_nonneg hκpos.le hLpos.le
  have h1X0 : 0 ≤ 1 + X := by linarith
  have hκL1X : κ * L ≤ 1 + X := by rw [← hXκL]; linarith
  -- absorption facts for the 1/L side
  have h4 : (1 + X) ^ (k - 1) ≤ (1 + X) ^ k / (κ * L) := by
    rw [le_div_iff₀ (mul_pos hκpos hLpos)]
    calc (1 + X) ^ (k - 1) * (κ * L) ≤ (1 + X) ^ (k - 1) * (1 + X) := by
          apply mul_le_mul_of_nonneg_left hκL1X (by positivity)
      _ = (1 + X) ^ k := by rw [← pow_succ]; congr 1; omega
  -- the per-monomial box sums
  set MSK : ((Fin k → ℕ) × ℕ × ℚ) → ℝ := fun m =>
    ∑ r ∈ kSieveIndex k R W',
      (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
        / ∏ i, (Nat.totient (r i) : ℝ) with hMSKdef
  set MSD : ((Fin k → ℕ) × ℕ × ℚ) → ℝ := fun m =>
    ∑ r ∈ decBox k R W',
      (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
        / ∏ i, (Nat.totient (r i) : ℝ) with hMSDdef
  set Drop : ℝ := ∑ r ∈ decBox k R W' \ kSieveIndex k R W',
      ∏ i, (1 / (Nat.totient (r i) : ℝ)) with hDropdef
  -- Stage 1: the LHS sum expands into a `List`-sum over the monomials of `P`.
  have hLHS : (∑ r ∈ kSieveIndex k R W',
        eval P (fun i => Real.log (r i) / L) / ∏ i, (Nat.totient (r i) : ℝ))
      = (P.map (fun m => (m.2.2 : ℝ) * MSK m)).sum := by
    have hbudget : ∀ r : Fin k → ℕ,
        (1 : ℝ) - ∑ i, Real.log (r i) / L = (L - ∑ i, Real.log (r i)) / L := by
      intro r; rw [← Finset.sum_div, sub_div, div_self hLne]
    have hper : ∀ r ∈ kSieveIndex k R W',
        eval P (fun i => Real.log (r i) / L) / ∏ i, (Nat.totient (r i) : ℝ)
          = (P.map (fun m => (m.2.2 : ℝ) * ((∏ i, (Real.log (r i) / L) ^ (m.1 i))
              * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
              / ∏ i, (Nat.totient (r i) : ℝ)))).sum := by
      intro r _
      have hev : eval P (fun i => Real.log (r i) / L)
          = (P.map (fun m => (m.2.2 : ℝ) * (∏ i, (Real.log (r i) / L) ^ (m.1 i))
              * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1))).sum := by
        unfold eval
        refine congrArg List.sum (List.map_congr_left (fun m _ => ?_))
        dsimp only
        rw [hbudget r]
      rw [hev, list_sum_map_div]
      refine congrArg List.sum (List.map_congr_left (fun m _ => ?_))
      ring
    rw [Finset.sum_congr rfl hper, sum_finset_list_swap]
    refine congrArg List.sum (List.map_congr_left (fun m _ => ?_))
    rw [hMSKdef, ← Finset.mul_sum]
  -- the main term expands into a `List`-sum.
  have hMainSum : X ^ k * ((simplexInt P : ℚ) : ℝ)
      = (P.map (fun m => X ^ k * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ)))).sum := by
    have hcast : ((simplexInt P : ℚ) : ℝ)
        = (P.map (fun m => (m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))).sum := by
      rw [simplexInt, Rat.cast_list_sum, List.map_map]
      refine congrArg List.sum (List.map_congr_left (fun m _ => ?_))
      simp only [Function.comp_apply]; push_cast; ring
    rw [hcast, ← List.sum_map_mul_left]
  -- Stage 3: `mv_monomial` at `z = R` per monomial.
  have hStage3 : ∀ m : (Fin k → ℕ) × ℕ × ℚ,
      |MSD m - X ^ k * ((DInt' m.1 m.2.1 : ℚ) : ℝ)| ≤ Cfun m * (1 + X) ^ (k - 1) := by
    intro m
    have hspec := (hCfunspec m).2 R R hR2 le_rfl hlogR
    rw [← hXdef, ← hLdef, div_self hLne, one_pow, mul_one] at hspec
    exact hspec
  -- Stage 2: the pairwise-coprimality drop, per monomial and in aggregate.
  have hsubset : kSieveIndex k R W' ⊆ decBox k R W' := by
    intro r hr
    have hmem := (mem_kSieveIndex_iff r).mp hr
    obtain ⟨hsqf, _, hcop, hprod⟩ := hmem
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
  have hDropPer : ∀ m : (Fin k → ℕ) × ℕ × ℚ, |MSK m - MSD m| ≤ Drop := by
    intro m
    have hbdd : ∀ r ∈ decBox k R W',
        0 ≤ (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
              / ∏ i, (Nat.totient (r i) : ℝ)
        ∧ (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
              / ∏ i, (Nat.totient (r i) : ℝ) ≤ ∏ i, (1 / (Nat.totient (r i) : ℝ)) := by
      intro r hr
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
      obtain ⟨hlt, hsqf, hcop, hprod⟩ := hr
      have hr1 : ∀ i, 1 ≤ r i := fun i => Nat.pos_of_ne_zero (hsqf i).ne_zero
      have hlogr0 : ∀ i, 0 ≤ Real.log (r i) := fun i => Real.log_nonneg (by exact_mod_cast hr1 i)
      have hlogrL : ∀ i, Real.log (r i) ≤ L := fun i => by
        rw [hLdef]
        exact Real.log_le_log (by exact_mod_cast hr1 i) (by exact_mod_cast (le_of_lt (hlt i)))
      have hφpos : (0:ℝ) < ∏ i, (Nat.totient (r i) : ℝ) := Finset.prod_pos (fun i _ => by
        have := hr1 i; exact_mod_cast Nat.totient_pos.mpr (by omega))
      have hti0 : ∀ i, 0 ≤ Real.log (r i) / L := fun i => div_nonneg (hlogr0 i) hLpos.le
      have hti1 : ∀ i, Real.log (r i) / L ≤ 1 := fun i => (div_le_one hLpos).mpr (hlogrL i)
      have hprodt0 : 0 ≤ ∏ i, (Real.log (r i) / L) ^ (m.1 i) :=
        Finset.prod_nonneg (fun i _ => pow_nonneg (hti0 i) _)
      have hprodt1 : ∏ i, (Real.log (r i) / L) ^ (m.1 i) ≤ 1 :=
        Finset.prod_le_one (fun i _ => pow_nonneg (hti0 i) _)
          (fun i _ => pow_le_one₀ (hti0 i) (hti1 i))
      have hSL : ∑ i, Real.log (r i) = Real.log ((∏ i, r i : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
        exact (Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (by have := hr1 i; omega))).symm
      have hprodpos : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => by have := hr1 i; omega)
      have hSLL : ∑ i, Real.log (r i) ≤ L := by
        rw [hSL, hLdef]
        exact Real.log_le_log (by exact_mod_cast hprodpos)
          (by exact_mod_cast (le_of_lt hprod))
      have hSL0 : 0 ≤ ∑ i, Real.log (r i) := Finset.sum_nonneg (fun i _ => hlogr0 i)
      have hbud0 : 0 ≤ (L - ∑ i, Real.log (r i)) / L := div_nonneg (by linarith) hLpos.le
      have hbud1 : (L - ∑ i, Real.log (r i)) / L ≤ 1 := (div_le_one hLpos).mpr (by linarith)
      have hnum0 : 0 ≤ (∏ i, (Real.log (r i) / L) ^ (m.1 i))
          * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1) := mul_nonneg hprodt0 (pow_nonneg hbud0 _)
      have hnum1 : (∏ i, (Real.log (r i) / L) ^ (m.1 i))
          * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1) ≤ 1 := by
        calc (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
            ≤ 1 * 1 :=
              mul_le_mul hprodt1 (pow_le_one₀ hbud0 hbud1) (pow_nonneg hbud0 _) (by norm_num)
          _ = 1 := by ring
      have hprodinv : (∏ i, (1 / (Nat.totient (r i) : ℝ))) = 1 / ∏ i, (Nat.totient (r i) : ℝ) := by
        rw [Finset.prod_div_distrib, Finset.prod_const_one]
      refine ⟨div_nonneg hnum0 hφpos.le, ?_⟩
      rw [hprodinv, div_le_div_iff₀ hφpos hφpos]
      linarith only [mul_le_mul_of_nonneg_right hnum1 hφpos.le]
    have hsdiff : MSD m - MSK m = ∑ r ∈ decBox k R W' \ kSieveIndex k R W',
        (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
          / ∏ i, (Nat.totient (r i) : ℝ) := by
      have h := Finset.sum_sdiff (f := fun r => (∏ i, (Real.log (r i) / L) ^ (m.1 i))
        * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1) / ∏ i, (Nat.totient (r i) : ℝ)) hsubset
      simp only [hMSDdef, hMSKdef]
      linarith [h]
    have hnn : 0 ≤ ∑ r ∈ decBox k R W' \ kSieveIndex k R W',
        (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
          / ∏ i, (Nat.totient (r i) : ℝ) :=
      Finset.sum_nonneg (fun r hr => (hbdd r (Finset.mem_sdiff.mp hr).1).1)
    have hle : (∑ r ∈ decBox k R W' \ kSieveIndex k R W',
        (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
          / ∏ i, (Nat.totient (r i) : ℝ)) ≤ Drop := by
      rw [hDropdef]
      exact Finset.sum_le_sum (fun r hr => (hbdd r (Finset.mem_sdiff.mp hr).1).2)
    have hneg : MSK m - MSD m = -(∑ r ∈ decBox k R W' \ kSieveIndex k R W',
        (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
          / ∏ i, (Nat.totient (r i) : ℝ)) := by rw [← hsdiff]; ring
    rw [hneg, abs_neg, abs_of_nonneg hnn]
    exact hle
  have hDropBound : Drop ≤ (2 * (k : ℝ) ^ 2) * PAS ^ k / (D : ℝ) := by
    set Pairs : Finset (Fin k × Fin k) :=
      (Finset.univ : Finset (Fin k × Fin k)).filter (fun q => q.1 ≠ q.2) with hPairsdef
    set Primes : Finset ℕ :=
      (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimesdef
    set T : Finset ((Fin k × Fin k) × ℕ) := Pairs ×ˢ Primes with hTdef
    set Bad : (Fin k × Fin k) × ℕ → Finset (Fin k → ℕ) := fun x =>
      (decBox k R W').filter (fun r => x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2) with hBaddef
    set ind : (Fin k × Fin k) × ℕ → (Fin k → ℕ) → ℝ := fun x r =>
      if x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2 then ∏ i, (1 / (Nat.totient (r i) : ℝ)) else 0 with hinddef
    have hindnn : ∀ x r, 0 ≤ ind x r := by
      intro x r; simp only [hinddef]; split_ifs
      · exact Finset.prod_nonneg (fun i _ => by positivity)
      · exact le_refl 0
    have hcover : Drop ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))) := by
      rw [hDropdef]
      have hpt : ∀ r ∈ decBox k R W' \ kSieveIndex k R W',
          (∏ i, (1 / (Nat.totient (r i) : ℝ))) ≤ ∑ x ∈ T, ind x r := by
        intro r hr
        obtain ⟨hrdec, hrnk⟩ := Finset.mem_sdiff.mp hr
        have hrdec' := hrdec
        simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hrdec'
        obtain ⟨hlt, hsqf, hcop, hprod⟩ := hrdec'
        rw [mem_kSieveIndex_iff] at hrnk
        have hpair_neg : ¬ (∀ i j : Fin k, i ≠ j → Nat.Coprime (r i) (r j)) :=
          fun hpair => hrnk ⟨hsqf, hpair, hcop, hprod⟩
        simp only [not_forall] at hpair_neg
        obtain ⟨i, j, hij, hncop⟩ := hpair_neg
        have hg1 : Nat.gcd (r i) (r j) ≠ 1 := hncop
        obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
        have hpi : p ∣ r i := hpg.trans (Nat.gcd_dvd_left _ _)
        have hpj : p ∣ r j := hpg.trans (Nat.gcd_dvd_right _ _)
        have hpW' : ¬ p ∣ W' := by
          intro hpW
          have h1 : p ∣ (1 : ℕ) := (hcop i) ▸ Nat.dvd_gcd hpi hpW
          exact absurd (Nat.dvd_one.mp h1) hp.one_lt.ne'
        have hDp : D < p := hDW p hp hpW'
        have hri1 : 1 ≤ r i := Nat.pos_of_ne_zero (hsqf i).ne_zero
        have hpR : p < R := lt_of_le_of_lt (Nat.le_of_dvd (by omega) hpi) (hlt i)
        have hpmem : p ∈ Primes := by
          rw [hPrimesdef, Finset.mem_filter, Finset.mem_range]; exact ⟨hpR, hp, hDp⟩
        have hqmem : (i, j) ∈ Pairs := by
          rw [hPairsdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩
        have hx0 : ((i, j), p) ∈ T := by rw [hTdef]; exact Finset.mem_product.mpr ⟨hqmem, hpmem⟩
        have hindeq : ind ((i, j), p) r = ∏ i, (1 / (Nat.totient (r i) : ℝ)) := by
          rw [hinddef]; simp only [if_pos (And.intro hpi hpj)]
        rw [← hindeq]
        exact Finset.single_le_sum (fun x _ => hindnn x r) hx0
      calc ∑ r ∈ decBox k R W' \ kSieveIndex k R W', (∏ i, (1 / (Nat.totient (r i) : ℝ)))
          ≤ ∑ r ∈ decBox k R W' \ kSieveIndex k R W', ∑ x ∈ T, ind x r :=
            Finset.sum_le_sum hpt
        _ = ∑ x ∈ T, ∑ r ∈ decBox k R W' \ kSieveIndex k R W', ind x r := Finset.sum_comm
        _ ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))) := by
            apply Finset.sum_le_sum
            intro x _
            rw [hinddef]
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · rw [hBaddef]
              exact Finset.filter_subset_filter _ Finset.sdiff_subset
            · intro r _ _; exact Finset.prod_nonneg (fun i _ => by positivity)
    have hPairsCard : (Pairs.card : ℝ) ≤ (k : ℝ) ^ 2 := by
      have h : Pairs.card ≤ k ^ 2 := by
        calc Pairs.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
          _ = k ^ 2 := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, _root_.sq]
      exact_mod_cast h
    have hfinal : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))))
        ≤ (2 * (k : ℝ) ^ 2) * PAS ^ k / (D : ℝ) := by
      have h1 : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))))
          ≤ ∑ x ∈ T, PAS ^ k / ((x.2 : ℝ) - 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [hTdef, Finset.mem_product] at hx
        obtain ⟨hq, hpx⟩ := hx
        rw [hPairsdef, Finset.mem_filter] at hq
        rw [hPrimesdef, Finset.mem_filter] at hpx
        have hbp := badpair_bound_rel_gen k hk W' hW' hpos R hR2 x.1.1 x.1.2 hq.2 x.2 hpx.2.1
        rw [← hPASdef] at hbp
        rw [hBaddef]; exact hbp
      refine le_trans h1 ?_
      rw [hTdef, Finset.sum_product]
      have hPAS5 : 0 ≤ PAS ^ k := pow_nonneg hPAS0 k
      have hinner : ∀ q ∈ Pairs,
          (∑ p ∈ Primes, PAS ^ k / (((q, p).2 : ℝ) - 1) ^ 2)
            ≤ PAS ^ k * (2 / (D : ℝ)) := by
        intro q _
        have heq : (∑ p ∈ Primes, PAS ^ k / ((p : ℝ) - 1) ^ 2)
            = PAS ^ k * ∑ p ∈ Primes, 1 / ((p : ℝ) - 1) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
        simp only
        rw [heq]
        exact mul_le_mul_of_nonneg_left (prime_tail D R hD) hPAS5
      calc (∑ q ∈ Pairs, ∑ p ∈ Primes, PAS ^ k / (((q, p).2 : ℝ) - 1) ^ 2)
          ≤ ∑ q ∈ Pairs, PAS ^ k * (2 / (D : ℝ)) := Finset.sum_le_sum hinner
        _ = (Pairs.card : ℝ) * (PAS ^ k * (2 / (D : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (k : ℝ) ^ 2 * (PAS ^ k * (2 / (D : ℝ))) :=
            mul_le_mul_of_nonneg_right hPairsCard
              (mul_nonneg hPAS5 (div_nonneg (by norm_num) (Nat.cast_nonneg D)))
        _ = (2 * (k : ℝ) ^ 2) * PAS ^ k / (D : ℝ) := by ring
    exact le_trans hcover hfinal
  -- per-monomial total bound
  have hPer : ∀ m ∈ P, |(m.2.2 : ℝ) * MSK m - X ^ k * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))|
      ≤ |(m.2.2 : ℝ)| * Drop + |(m.2.2 : ℝ)| * Cfun m * (1 + X) ^ (k - 1) := by
    intro m _
    have hfac : (m.2.2 : ℝ) * MSK m - X ^ k * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))
        = (m.2.2 : ℝ) * (MSK m - X ^ k * ((DInt' m.1 m.2.1 : ℚ) : ℝ)) := by ring
    rw [hfac, abs_mul]
    have htri : |MSK m - X ^ k * ((DInt' m.1 m.2.1 : ℚ) : ℝ)|
        ≤ Drop + Cfun m * (1 + X) ^ (k - 1) := by
      calc |MSK m - X ^ k * ((DInt' m.1 m.2.1 : ℚ) : ℝ)|
          ≤ |MSK m - MSD m| + |MSD m - X ^ k * ((DInt' m.1 m.2.1 : ℚ) : ℝ)| :=
            abs_sub_le _ _ _
        _ ≤ Drop + Cfun m * (1 + X) ^ (k - 1) := add_le_add (hDropPer m) (hStage3 m)
    calc |(m.2.2 : ℝ)| * |MSK m - X ^ k * ((DInt' m.1 m.2.1 : ℚ) : ℝ)|
        ≤ |(m.2.2 : ℝ)| * (Drop + Cfun m * (1 + X) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left htri (abs_nonneg _)
      _ = |(m.2.2 : ℝ)| * Drop + |(m.2.2 : ℝ)| * Cfun m * (1 + X) ^ (k - 1) := by ring
  -- assembly
  rw [hLHS, hMainSum, list_sum_map_sub]
  calc |(P.map (fun m => (m.2.2 : ℝ) * MSK m
          - X ^ k * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ)))).sum|
      ≤ (P.map (fun m => |(m.2.2 : ℝ) * MSK m
          - X ^ k * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))|)).sum := by
        have := list_abs_sum_le (P.map (fun m => (m.2.2 : ℝ) * MSK m
          - X ^ k * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))))
        rwa [List.map_map, Function.comp_def] at this
    _ ≤ (P.map (fun m => |(m.2.2 : ℝ)| * Drop + |(m.2.2 : ℝ)| * Cfun m * (1 + X) ^ (k - 1))).sum :=
        list_sum_map_le _ _ _ hPer
    _ = (P.map (fun m => |(m.2.2 : ℝ)| * Drop)).sum
          + (P.map (fun m => |(m.2.2 : ℝ)| * Cfun m * (1 + X) ^ (k - 1))).sum
                  := list_sum_map_add _ _ _
    _ = Drop * Qabs + (1 + X) ^ (k - 1) * Cmain := by
        rw [hQabsdef, hCmaindef,
          List.sum_map_mul_right P (fun m => |(m.2.2 : ℝ)|) Drop,
          List.sum_map_mul_right P (fun m => |(m.2.2 : ℝ)| * Cfun m) ((1 + X) ^ (k - 1))]
        ring
    _ ≤ Cmain / κ * (1 + X) ^ k / L + (2 * (k : ℝ) ^ 2) * Qabs * (1 + PAS) ^ k / (D : ℝ) := by
        have hDpos : (0:ℝ) < (D : ℝ) := by
          have : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
          linarith
        -- Drop side → 1/D
        have hPAS15 : PAS ^ k ≤ (1 + PAS) ^ k :=
          pow_le_pow_left₀ hPAS0 (by linarith) k
        have hDropSide : Drop * Qabs ≤ (2 * (k : ℝ) ^ 2) * Qabs * (1 + PAS) ^ k / (D : ℝ) := by
          calc Drop * Qabs ≤ ((2 * (k : ℝ) ^ 2) * PAS ^ k / (D : ℝ)) * Qabs :=
                mul_le_mul_of_nonneg_right hDropBound hQabs0
            _ = (2 * (k : ℝ) ^ 2) * Qabs / (D : ℝ) * PAS ^ k := by ring
            _ ≤ (2 * (k : ℝ) ^ 2) * Qabs / (D : ℝ) * (1 + PAS) ^ k :=
                mul_le_mul_of_nonneg_left hPAS15
                  (div_nonneg (by positivity) hDpos.le)
            _ = (2 * (k : ℝ) ^ 2) * Qabs * (1 + PAS) ^ k / (D : ℝ) := by ring
        -- main side → 1/L
        have hMainSide : (1 + X) ^ (k - 1) * Cmain ≤ Cmain / κ * (1 + X) ^ k / L := by
          have e1 : (1 + X) ^ (k - 1) * Cmain = Cmain * (1 + X) ^ (k - 1) := by ring
          have hκne : κ ≠ 0 := ne_of_gt hκpos
          have e2 : Cmain / κ * (1 + X) ^ k / L = Cmain * ((1 + X) ^ k / (κ * L)) := by
            field_simp
          rw [e1, e2]; exact mul_le_mul_of_nonneg_left h4 hCmain0
        linarith [hDropSide, hMainSide]

/-! ## Helpers for `inner_contract_rel` (private copies from `MvJ.lean`) -/

/-- CONTROL: the landed `MvSplit.mv_I_split` statement, VERBATIM, as the k = 5 corollary. -/
theorem mv_I_split_of_gen (F : Poly) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ kSieveIndex 5 R W',
              eval (ofPoly F) (fun i => Real.log (r i) / Real.log R) ^ 2
                / ∏ i, (Nat.totient (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 5
              * ((simplexInt (sq (ofPoly F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 5 / Real.log R
          + A * (1 + Salt.Maynard.phiAtomSum R W') ^ 5 / D := by
  simpa only [eval_sq] using mv_I_split_gen 5 (by norm_num) (sq (ofPoly F))


end Salt.MaynardK
