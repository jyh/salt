/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.MvI
import Salt.Twelve.MvJ
import Salt.Twelve.RelEngines
import Salt.Twelve.MvMoment
import Salt.Twelve.MvMomentG
import Salt.Twelve.BudgetMoment
import Salt.Twelve.BudgetMomentG
import Salt.Twelve.BudgetPoly
import Salt.Twelve.W3Prep
import Salt.Maynard.KSieve
import Salt.Maynard.PhiAtom

/-!
# W4-2 (MvSplit) — the split-error keystone re-statements

Card W4-2 of the `explicit12` wave-4 dispatch
(`docs/blueprints/explicit12-design.md`).  The wave-3 keystones `mv_I`/`mv_J`
quantify their opaque error constant `∃c` AFTER `W'`, so the residual `c(W')/D`
term is consumption-poison at the endgame (where `W' = primorial D` is linked to
`D`).  Here the `1/D`-side errors are re-stated RELATIVE to the concrete
`phiAtomSum R W'` (`PAS`) with an ABSOLUTE (`W'`-free, F-only) coefficient `A`
quantified BEFORE `W'`; the `1/log R`-side keeps landed per-`W'` opaque
constants inside `∃c`.

Deliverables (statements frozen):
* `inner_contract_rel` — the landed `inner_contract` with its `Pr(r)`-weighted
  error re-based on `PAS` (F-only coefficient `A`);
* `mv_I_split`, `mv_J_split` — the split moments.
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-! ## `phiAtomSum` basics -/

/-- `phiAtomSum` is a sum of nonnegative terms. -/
private lemma pas_nonneg (z W' : ℕ) : 0 ≤ Salt.Maynard.phiAtomSum z W' := by
  unfold Salt.Maynard.phiAtomSum
  exact Finset.sum_nonneg fun r _ => by positivity

/-- `phiAtomSum` is monotone in the cap (more terms, all nonnegative). -/
private lemma pas_mono {z z' W' : ℕ} (h : z ≤ z') :
    Salt.Maynard.phiAtomSum z W' ≤ Salt.Maynard.phiAtomSum z' W' := by
  unfold Salt.Maynard.phiAtomSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    simp only [Salt.Maynard.sqfCop, Finset.mem_filter, Finset.mem_range] at hr ⊢
    exact ⟨lt_of_lt_of_le hr.1 h, hr.2⟩
  · intro r _ _; positivity

/-! ## General `List`-sum helpers (private copies) -/

private lemma list_abs_sum_le (l : List ℝ) : |l.sum| ≤ (l.map (fun x => |x|)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le a l.sum).trans (by linarith [ih])

private lemma list_sum_map_sub {γ : Type*} (l : List γ) (f g : γ → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map (fun x => f x - g x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

private lemma list_sum_map_div {γ : Type*} (l : List γ) (f : γ → ℝ) (c : ℝ) :
    (l.map f).sum / c = (l.map (fun x => f x / c)).sum := by
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]
  simp only [div_eq_mul_inv]

private lemma sum_finset_list_swap {γ : Type*} (B : Finset (Fin 5 → ℕ))
    (P : List γ) (f : γ → (Fin 5 → ℕ) → ℝ) :
    ∑ r ∈ B, (P.map (fun m => f m r)).sum = (P.map (fun m => ∑ r ∈ B, f m r)).sum := by
  induction P with
  | nil => simp
  | cons a P ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

private lemma list_sum_map_le {γ : Type*} (l : List γ) (f g : γ → ℝ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    linarith

private lemma list_map_sum_nonneg {γ : Type*} (l : List γ) (f : γ → ℝ)
    (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    linarith

private lemma list_sum_map_add {γ : Type*} (l : List γ) (f g : γ → ℝ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

/-! ## The prime tail `Σ_{p>D} 1/(p-1)² ≤ 2/D` (private copy) -/

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
    have hle : a * (a+1) ≤ (a+1)^2 := by nlinarith
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
    nlinarith
  linarith [int_tail D R hD, h1, h2]

/-! ## The relative pairwise-collision bound (Stage 2 kernel, `mv_I` side)

Truncation of the landed `Salt.Twelve.badpair_bound` (`MvI.lean`, `private`):
each of the five coordinate factors `∑_{g_k ∣ s} 1/φ(s)` is bounded by
`marked_sqf_phi_rel` at `s = g k`, `a = 0`, `z = R`, giving `(1/φ(g_k))·PAS`
with NO opaque constant. -/

private lemma badpair_bound_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (R : ℕ) (hR2 : 2 ≤ R) (i j : Fin 5) (hij : i ≠ j) (p : ℕ) (hp : Nat.Prime p) :
    ∑ r ∈ (decBox 5 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ (Salt.Maynard.phiAtomSum R W') ^ 5 / ((p:ℝ) - 1) ^ 2 := by
  classical
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set g : Fin 5 → ℕ := fun k => if k = i ∨ k = j then p else 1 with hg
  have hp2 : 2 ≤ p := hp.two_le
  have hp1R : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    linarith
  have hgpos : ∀ k, 0 < g k := by
    intro k; simp only [hg]; split
    · exact hp.pos
    · exact one_pos
  set coordSet : Fin 5 → Finset ℕ := fun k =>
    (Finset.range R).filter (fun s => Squarefree s ∧ s.Coprime W' ∧ g k ∣ s) with hcoord
  have hstepA : ∑ r ∈ (decBox 5 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
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
  set h : Fin 5 → ℝ := fun k => ∑ s ∈ coordSet k, (1 / (Nat.totient s : ℝ)) with hh
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
  have hcard : ((Finset.univ.erase i).erase j).card = 3 := by
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hprodrest : ∏ k ∈ (Finset.univ.erase i).erase j, h k ≤ PAS ^ 3 := by
    calc ∏ k ∈ (Finset.univ.erase i).erase j, h k
        ≤ ∏ _k ∈ (Finset.univ.erase i).erase j, PAS :=
          Finset.prod_le_prod (fun k _ => hhnn k) hother
      _ = PAS ^ 3 := by rw [Finset.prod_const, hcard]
  have hbnd : ∏ k, h k
      ≤ (PAS / ((p:ℝ) - 1)) * ((PAS / ((p:ℝ) - 1)) * PAS ^ 3) := by
    rw [hsplit]
    apply mul_le_mul hi_le _ (mul_nonneg (hhnn j) (Finset.prod_nonneg (fun k _ => hhnn k)))
      (div_nonneg hPAS0 hp1R.le)
    apply mul_le_mul hj_le hprodrest (Finset.prod_nonneg (fun k _ => hhnn k))
      (div_nonneg hPAS0 hp1R.le)
  have hfinal : (PAS / ((p:ℝ) - 1)) * ((PAS / ((p:ℝ) - 1)) * PAS ^ 3)
      = PAS ^ 5 / ((p:ℝ) - 1) ^ 2 := by
    have hne : (p:ℝ) - 1 ≠ 0 := ne_of_gt hp1R
    field_simp
  calc ∑ r ∈ (decBox 5 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ ∏ k, h k := hstepA
    _ ≤ _ := hbnd
    _ = PAS ^ 5 / ((p:ℝ) - 1) ^ 2 := hfinal

/-! ## `mv_I_split` -/

theorem mv_I_split (F : Poly) :
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
  classical
  set P : BPoly 5 := sq (ofPoly F) with hPdef
  set Qabs : ℝ := (P.map (fun m => |(m.2.2 : ℝ)|)).sum with hQabsdef
  have hQabs0 : 0 ≤ Qabs := by
    rw [hQabsdef]; exact list_map_sum_nonneg _ _ (fun m _ => abs_nonneg _)
  refine ⟨40 * Qabs, by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  -- per-monomial `mv_monomial` constants
  set Cfun : ((Fin 5 → ℕ) × ℕ × ℚ) → ℝ :=
    fun m => Classical.choose (mv_monomial W' hW' hpos hUpper 5 m.1 m.2.1) with hCfundef
  have hCfunspec : ∀ m, 0 ≤ Cfun m ∧ ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ r ∈ decBox 5 z W',
            (∏ i, (Real.log (r i) / Real.log R) ^ (m.1 i))
              * ((Real.log z - ∑ i, Real.log (r i)) / Real.log R) ^ (m.2.1)
              / ∏ i, (Nat.totient (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 5 * ((DInt' m.1 m.2.1 : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ (5 + m.2.1 + ∑ i, m.1 i)|
      ≤ Cfun m * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (5 - 1) :=
    fun m => Classical.choose_spec (mv_monomial W' hW' hpos hUpper 5 m.1 m.2.1)
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
  have h4 : (1 + X) ^ 4 ≤ (1 + X) ^ 5 / (κ * L) := by
    rw [le_div_iff₀ (mul_pos hκpos hLpos)]
    calc (1 + X) ^ 4 * (κ * L) ≤ (1 + X) ^ 4 * (1 + X) := by
          apply mul_le_mul_of_nonneg_left hκL1X (by positivity)
      _ = (1 + X) ^ 5 := by ring
  -- the per-monomial box sums
  set MSK : ((Fin 5 → ℕ) × ℕ × ℚ) → ℝ := fun m =>
    ∑ r ∈ kSieveIndex 5 R W',
      (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
        / ∏ i, (Nat.totient (r i) : ℝ) with hMSKdef
  set MSD : ((Fin 5 → ℕ) × ℕ × ℚ) → ℝ := fun m =>
    ∑ r ∈ decBox 5 R W',
      (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
        / ∏ i, (Nat.totient (r i) : ℝ) with hMSDdef
  set Drop : ℝ := ∑ r ∈ decBox 5 R W' \ kSieveIndex 5 R W',
      ∏ i, (1 / (Nat.totient (r i) : ℝ)) with hDropdef
  -- Stage 1: the LHS sum expands into a `List`-sum over the monomials of `P`.
  have hLHS : (∑ r ∈ kSieveIndex 5 R W',
        eval (ofPoly F) (fun i => Real.log (r i) / L) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
      = (P.map (fun m => (m.2.2 : ℝ) * MSK m)).sum := by
    have hbudget : ∀ r : Fin 5 → ℕ,
        (1 : ℝ) - ∑ i, Real.log (r i) / L = (L - ∑ i, Real.log (r i)) / L := by
      intro r; rw [← Finset.sum_div, sub_div, div_self hLne]
    have hsq : ∀ r : Fin 5 → ℕ,
        eval (ofPoly F) (fun i => Real.log (r i) / L) ^ 2
          = eval P (fun i => Real.log (r i) / L) := by
      intro r; rw [hPdef]; exact (eval_sq (ofPoly F) _).symm
    have hper : ∀ r ∈ kSieveIndex 5 R W',
        eval (ofPoly F) (fun i => Real.log (r i) / L) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
          = (P.map (fun m => (m.2.2 : ℝ) * ((∏ i, (Real.log (r i) / L) ^ (m.1 i))
              * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
              / ∏ i, (Nat.totient (r i) : ℝ)))).sum := by
      intro r _
      rw [hsq r]
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
  have hMainSum : X ^ 5 * ((simplexInt P : ℚ) : ℝ)
      = (P.map (fun m => X ^ 5 * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ)))).sum := by
    have hcast : ((simplexInt P : ℚ) : ℝ)
        = (P.map (fun m => (m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))).sum := by
      rw [simplexInt, Rat.cast_list_sum, List.map_map]
      refine congrArg List.sum (List.map_congr_left (fun m _ => ?_))
      simp only [Function.comp_apply]; push_cast; ring
    rw [hcast, ← List.sum_map_mul_left]
  -- Stage 3: `mv_monomial` at `z = R` per monomial.
  have hStage3 : ∀ m : (Fin 5 → ℕ) × ℕ × ℚ,
      |MSD m - X ^ 5 * ((DInt' m.1 m.2.1 : ℚ) : ℝ)| ≤ Cfun m * (1 + X) ^ 4 := by
    intro m
    have hspec := (hCfunspec m).2 R R hR2 le_rfl hlogR
    rw [← hXdef, ← hLdef, div_self hLne, one_pow, mul_one] at hspec
    exact hspec
  -- Stage 2: the pairwise-coprimality drop, per monomial and in aggregate.
  have hsubset : kSieveIndex 5 R W' ⊆ decBox 5 R W' := by
    intro r hr
    have hmem := (mem_kSieveIndex_iff r).mp hr
    obtain ⟨hsqf, _, hcop, hprod⟩ := hmem
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
  have hDropPer : ∀ m : (Fin 5 → ℕ) × ℕ × ℚ, |MSK m - MSD m| ≤ Drop := by
    intro m
    have hbdd : ∀ r ∈ decBox 5 R W',
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
      nlinarith [mul_le_mul_of_nonneg_right hnum1 hφpos.le]
    have hsdiff : MSD m - MSK m = ∑ r ∈ decBox 5 R W' \ kSieveIndex 5 R W',
        (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
          / ∏ i, (Nat.totient (r i) : ℝ) := by
      have h := Finset.sum_sdiff (f := fun r => (∏ i, (Real.log (r i) / L) ^ (m.1 i))
        * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1) / ∏ i, (Nat.totient (r i) : ℝ)) hsubset
      simp only [hMSDdef, hMSKdef]
      linarith [h]
    have hnn : 0 ≤ ∑ r ∈ decBox 5 R W' \ kSieveIndex 5 R W',
        (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
          / ∏ i, (Nat.totient (r i) : ℝ) :=
      Finset.sum_nonneg (fun r hr => (hbdd r (Finset.mem_sdiff.mp hr).1).1)
    have hle : (∑ r ∈ decBox 5 R W' \ kSieveIndex 5 R W',
        (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
          / ∏ i, (Nat.totient (r i) : ℝ)) ≤ Drop := by
      rw [hDropdef]
      exact Finset.sum_le_sum (fun r hr => (hbdd r (Finset.mem_sdiff.mp hr).1).2)
    have hneg : MSK m - MSD m = -(∑ r ∈ decBox 5 R W' \ kSieveIndex 5 R W',
        (∏ i, (Real.log (r i) / L) ^ (m.1 i)) * ((L - ∑ i, Real.log (r i)) / L) ^ (m.2.1)
          / ∏ i, (Nat.totient (r i) : ℝ)) := by rw [← hsdiff]; ring
    rw [hneg, abs_neg, abs_of_nonneg hnn]
    exact hle
  have hDropBound : Drop ≤ 40 * PAS ^ 5 / (D : ℝ) := by
    set Pairs : Finset (Fin 5 × Fin 5) :=
      (Finset.univ : Finset (Fin 5 × Fin 5)).filter (fun q => q.1 ≠ q.2) with hPairsdef
    set Primes : Finset ℕ :=
      (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimesdef
    set T : Finset ((Fin 5 × Fin 5) × ℕ) := Pairs ×ˢ Primes with hTdef
    set Bad : (Fin 5 × Fin 5) × ℕ → Finset (Fin 5 → ℕ) := fun x =>
      (decBox 5 R W').filter (fun r => x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2) with hBaddef
    set ind : (Fin 5 × Fin 5) × ℕ → (Fin 5 → ℕ) → ℝ := fun x r =>
      if x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2 then ∏ i, (1 / (Nat.totient (r i) : ℝ)) else 0 with hinddef
    have hindnn : ∀ x r, 0 ≤ ind x r := by
      intro x r; simp only [hinddef]; split_ifs
      · exact Finset.prod_nonneg (fun i _ => by positivity)
      · exact le_refl 0
    have hcover : Drop ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))) := by
      rw [hDropdef]
      have hpt : ∀ r ∈ decBox 5 R W' \ kSieveIndex 5 R W',
          (∏ i, (1 / (Nat.totient (r i) : ℝ))) ≤ ∑ x ∈ T, ind x r := by
        intro r hr
        obtain ⟨hrdec, hrnk⟩ := Finset.mem_sdiff.mp hr
        have hrdec' := hrdec
        simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hrdec'
        obtain ⟨hlt, hsqf, hcop, hprod⟩ := hrdec'
        rw [mem_kSieveIndex_iff] at hrnk
        have hpair_neg : ¬ (∀ i j : Fin 5, i ≠ j → Nat.Coprime (r i) (r j)) :=
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
      calc ∑ r ∈ decBox 5 R W' \ kSieveIndex 5 R W', (∏ i, (1 / (Nat.totient (r i) : ℝ)))
          ≤ ∑ r ∈ decBox 5 R W' \ kSieveIndex 5 R W', ∑ x ∈ T, ind x r :=
            Finset.sum_le_sum hpt
        _ = ∑ x ∈ T, ∑ r ∈ decBox 5 R W' \ kSieveIndex 5 R W', ind x r := Finset.sum_comm
        _ ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))) := by
            apply Finset.sum_le_sum
            intro x _
            rw [hinddef]
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · rw [hBaddef]
              exact Finset.filter_subset_filter _ Finset.sdiff_subset
            · intro r _ _; exact Finset.prod_nonneg (fun i _ => by positivity)
    have hPairsCard : Pairs.card = 20 := by rw [hPairsdef]; decide
    have hfinal : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))))
        ≤ 40 * PAS ^ 5 / (D : ℝ) := by
      have h1 : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))))
          ≤ ∑ x ∈ T, PAS ^ 5 / ((x.2 : ℝ) - 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [hTdef, Finset.mem_product] at hx
        obtain ⟨hq, hpx⟩ := hx
        rw [hPairsdef, Finset.mem_filter] at hq
        rw [hPrimesdef, Finset.mem_filter] at hpx
        have hbp := badpair_bound_rel W' hW' hpos R hR2 x.1.1 x.1.2 hq.2 x.2 hpx.2.1
        rw [← hPASdef] at hbp
        rw [hBaddef]; exact hbp
      refine le_trans h1 ?_
      rw [hTdef, Finset.sum_product]
      have hPAS5 : 0 ≤ PAS ^ 5 := pow_nonneg hPAS0 5
      have hinner : ∀ q ∈ Pairs,
          (∑ p ∈ Primes, PAS ^ 5 / (((q, p).2 : ℝ) - 1) ^ 2)
            ≤ PAS ^ 5 * (2 / (D : ℝ)) := by
        intro q _
        have heq : (∑ p ∈ Primes, PAS ^ 5 / ((p : ℝ) - 1) ^ 2)
            = PAS ^ 5 * ∑ p ∈ Primes, 1 / ((p : ℝ) - 1) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
        simp only
        rw [heq]
        exact mul_le_mul_of_nonneg_left (prime_tail D R hD) hPAS5
      calc (∑ q ∈ Pairs, ∑ p ∈ Primes, PAS ^ 5 / (((q, p).2 : ℝ) - 1) ^ 2)
          ≤ ∑ q ∈ Pairs, PAS ^ 5 * (2 / (D : ℝ)) := Finset.sum_le_sum hinner
        _ = (Pairs.card : ℝ) * (PAS ^ 5 * (2 / (D : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = 40 * PAS ^ 5 / (D : ℝ) := by rw [hPairsCard]; push_cast; ring
    exact le_trans hcover hfinal
  -- per-monomial total bound
  have hPer : ∀ m ∈ P, |(m.2.2 : ℝ) * MSK m - X ^ 5 * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))|
      ≤ |(m.2.2 : ℝ)| * Drop + |(m.2.2 : ℝ)| * Cfun m * (1 + X) ^ 4 := by
    intro m _
    have hfac : (m.2.2 : ℝ) * MSK m - X ^ 5 * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))
        = (m.2.2 : ℝ) * (MSK m - X ^ 5 * ((DInt' m.1 m.2.1 : ℚ) : ℝ)) := by ring
    rw [hfac, abs_mul]
    have htri : |MSK m - X ^ 5 * ((DInt' m.1 m.2.1 : ℚ) : ℝ)|
        ≤ Drop + Cfun m * (1 + X) ^ 4 := by
      calc |MSK m - X ^ 5 * ((DInt' m.1 m.2.1 : ℚ) : ℝ)|
          ≤ |MSK m - MSD m| + |MSD m - X ^ 5 * ((DInt' m.1 m.2.1 : ℚ) : ℝ)| :=
            abs_sub_le _ _ _
        _ ≤ Drop + Cfun m * (1 + X) ^ 4 := add_le_add (hDropPer m) (hStage3 m)
    calc |(m.2.2 : ℝ)| * |MSK m - X ^ 5 * ((DInt' m.1 m.2.1 : ℚ) : ℝ)|
        ≤ |(m.2.2 : ℝ)| * (Drop + Cfun m * (1 + X) ^ 4) :=
          mul_le_mul_of_nonneg_left htri (abs_nonneg _)
      _ = |(m.2.2 : ℝ)| * Drop + |(m.2.2 : ℝ)| * Cfun m * (1 + X) ^ 4 := by ring
  -- assembly
  rw [hLHS, hMainSum, list_sum_map_sub]
  calc |(P.map (fun m => (m.2.2 : ℝ) * MSK m
          - X ^ 5 * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ)))).sum|
      ≤ (P.map (fun m => |(m.2.2 : ℝ) * MSK m
          - X ^ 5 * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))|)).sum := by
        have := list_abs_sum_le (P.map (fun m => (m.2.2 : ℝ) * MSK m
          - X ^ 5 * ((m.2.2 : ℝ) * ((DInt' m.1 m.2.1 : ℚ) : ℝ))))
        rwa [List.map_map, Function.comp_def] at this
    _ ≤ (P.map (fun m => |(m.2.2 : ℝ)| * Drop + |(m.2.2 : ℝ)| * Cfun m * (1 + X) ^ 4)).sum :=
        list_sum_map_le _ _ _ hPer
    _ = (P.map (fun m => |(m.2.2 : ℝ)| * Drop)).sum
          + (P.map (fun m => |(m.2.2 : ℝ)| * Cfun m * (1 + X) ^ 4)).sum := list_sum_map_add _ _ _
    _ = Drop * Qabs + (1 + X) ^ 4 * Cmain := by
        rw [hQabsdef, hCmaindef,
          List.sum_map_mul_right P (fun m => |(m.2.2 : ℝ)|) Drop,
          List.sum_map_mul_right P (fun m => |(m.2.2 : ℝ)| * Cfun m) ((1 + X) ^ 4)]
        ring
    _ ≤ Cmain / κ * (1 + X) ^ 5 / L + 40 * Qabs * (1 + PAS) ^ 5 / (D : ℝ) := by
        have hDpos : (0:ℝ) < (D : ℝ) := by
          have : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
          linarith
        -- Drop side → 1/D
        have hPAS15 : PAS ^ 5 ≤ (1 + PAS) ^ 5 :=
          pow_le_pow_left₀ hPAS0 (by linarith) 5
        have hDropSide : Drop * Qabs ≤ 40 * Qabs * (1 + PAS) ^ 5 / (D : ℝ) := by
          calc Drop * Qabs ≤ (40 * PAS ^ 5 / (D : ℝ)) * Qabs :=
                mul_le_mul_of_nonneg_right hDropBound hQabs0
            _ = 40 * Qabs / (D : ℝ) * PAS ^ 5 := by ring
            _ ≤ 40 * Qabs / (D : ℝ) * (1 + PAS) ^ 5 :=
                mul_le_mul_of_nonneg_left hPAS15
                  (div_nonneg (by positivity) hDpos.le)
            _ = 40 * Qabs * (1 + PAS) ^ 5 / (D : ℝ) := by ring
        -- main side → 1/L
        have hMainSide : (1 + X) ^ 4 * Cmain ≤ Cmain / κ * (1 + X) ^ 5 / L := by
          have e1 : (1 + X) ^ 4 * Cmain = Cmain * (1 + X) ^ 4 := by ring
          have hκne : κ ≠ 0 := ne_of_gt hκpos
          have e2 : Cmain / κ * (1 + X) ^ 5 / L = Cmain * ((1 + X) ^ 5 / (κ * L)) := by
            field_simp
          rw [e1, e2]; exact mul_le_mul_of_nonneg_left h4 hCmain0
        linarith [hDropSide, hMainSide]

/-! ## Helpers for `inner_contract_rel` (private copies from `MvJ.lean`) -/

private lemma ic_sum_finset_list_sum {ι γ : Type*} (S : Finset ι) (L : List γ)
    (f : ι → γ → ℝ) :
    ∑ u ∈ S, (L.map (fun x => f u x)).sum = (L.map (fun x => ∑ u ∈ S, f u x)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

private lemma ic_list_abs_sum_le {γ : Type*} (L : List γ) (f : γ → ℝ) :
    |(L.map f).sum| ≤ (L.map (fun a => |f a|)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      calc |f a + (L.map f).sum| ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
        _ ≤ |f a| + (L.map (fun a => |f a|)).sum := by linarith [ih]

private lemma ic_list_sum_map_add {γ : Type*} (L : List γ) (f g : γ → ℝ) :
    (L.map (fun a => f a + g a)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private lemma ic_list_sum_div {γ : Type*} (L : List γ) (g : γ → ℝ) (c : ℝ) :
    (L.map g).sum / c = (L.map (fun a => g a / c)).sum := by
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]; simp only [div_eq_mul_inv]

private lemma ic_list_sum_map_sub {γ : Type*} (L : List γ) (f g : γ → ℝ) :
    (L.map f).sum - (L.map g).sum = (L.map (fun a => f a - g a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

private lemma ic_list_sum_le {γ : Type*} (L : List γ) (f g : γ → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- For `A, B ∈ [0,1]`, `|Aⁿ − Bⁿ| ≤ n·|A − B|`. -/
private lemma abs_pow_sub_pow_le_unit {A B : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (n : ℕ) : |A ^ n - B ^ n| ≤ n * |A - B| := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hBn : |B ^ n| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg hB0 n)]; exact pow_le_one₀ hB0 hB1
      have hAle : |A| ≤ 1 := by rw [abs_of_nonneg hA0]; exact hA1
      have key : A ^ (n + 1) - B ^ (n + 1) = A * (A ^ n - B ^ n) + (A - B) * B ^ n := by ring
      calc |A ^ (n + 1) - B ^ (n + 1)|
          = |A * (A ^ n - B ^ n) + (A - B) * B ^ n| := by rw [key]
        _ ≤ |A * (A ^ n - B ^ n)| + |(A - B) * B ^ n| := abs_add_le _ _
        _ = |A| * |A ^ n - B ^ n| + |A - B| * |B ^ n| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * ((n : ℝ) * |A - B|) + |A - B| * 1 := by
              apply add_le_add
              · exact mul_le_mul hAle ih (abs_nonneg _) (by norm_num)
              · exact mul_le_mul_of_nonneg_left hBn (abs_nonneg _)
        _ = ((n : ℝ) + 1) * |A - B| := by ring
        _ = ((n + 1 : ℕ) : ℝ) * |A - B| := by push_cast; ring

/-- `∏ᵢ (update r m u) i = u · ∏ᵢ r i` when `r m = 1`. -/
private lemma prod_update_eq {r : Fin 5 → ℕ} {m : Fin 5} (hrm : r m = 1) (u : ℕ) :
    ∏ i, Function.update r m u i = u * ∏ i, r i := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ m)]
  congr 1
  rw [← Finset.erase_eq]
  exact Finset.prod_erase _ hrm

/-- Membership of `Function.update r m u` in the sieve box, unfolded to the
one-dimensional conditions on `u`. -/
private lemma update_mem_kSieveIndex_iff {R W' : ℕ} {r : Fin 5 → ℕ}
    (hr : r ∈ kSieveIndex 5 R W') {m : Fin 5} (hrm : r m = 1) (u : ℕ) :
    Function.update r m u ∈ kSieveIndex 5 R W' ↔
      (Squarefree u ∧ u.Coprime W' ∧ u.Coprime (∏ i, r i) ∧ u * (∏ i, r i) < R) := by
  rw [mem_kSieveIndex_iff] at hr ⊢
  obtain ⟨hrSF, hrPC, hrW, hrlt⟩ := hr
  have hprodU : ∏ i, Function.update r m u i = u * ∏ i, r i := prod_update_eq hrm u
  constructor
  · rintro ⟨hSF, hPC, hW, hlt⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := hSF m; rwa [Function.update_self] at this
    · have := hW m; rwa [Function.update_self] at this
    · rw [Nat.coprime_fintype_prod_right_iff]
      intro i
      rcases eq_or_ne i m with hi | hi
      · subst hi; rw [hrm]; exact Nat.coprime_one_right u
      · have := hPC m i (Ne.symm hi)
        rwa [Function.update_self, Function.update_of_ne hi] at this
    · rwa [hprodU] at hlt
  · rintro ⟨hSFu, hcopu, hcopuP, hlt⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rcases eq_or_ne i m with hi | hi
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]; exact hrSF i
    · intro i j hij
      rcases eq_or_ne i m with hi | hi
      · have hjm : j ≠ m := hi ▸ hij.symm
        rw [hi, Function.update_self, Function.update_of_ne hjm]
        exact Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem r (Finset.mem_univ j)) hcopuP
      · rcases eq_or_ne j m with hj | hj
        · rw [hj, Function.update_self, Function.update_of_ne hi]
          exact (Nat.Coprime.coprime_dvd_right
            (Finset.dvd_prod_of_mem r (Finset.mem_univ i)) hcopuP).symm
        · rw [Function.update_of_ne hi, Function.update_of_ne hj]
          exact hrPC i j hij
    · intro i
      rcases eq_or_ne i m with hi | hi
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]; exact hrW i
    · rwa [hprodU]

/-- `eval (ofPoly F) t` as an explicit monomial `List.sum` (budget power `0`). -/
private lemma eval_ofPoly (F : Poly) (t : Fin 5 → ℝ) :
    eval (ofPoly F) t = (F.map (fun a => (a.2 : ℝ) * ∏ i, t i ^ a.1 i)).sum := by
  simp only [eval, ofPoly, List.map_map, Function.comp_def, pow_zero, mul_one]

/-- `eval (contractAt m F) t` as an explicit monomial `List.sum`. -/
private lemma eval_contractAt (m : Fin 5) (F : Poly) (t : Fin 4 → ℝ) :
    eval (contractAt m F) t
      = (F.map (fun a => ((a.2 / ((a.1 m + 1 : ℕ) : ℚ) : ℚ) : ℝ)
          * (∏ i, t i ^ a.1 (m.succAbove i)) * (1 - ∑ i, t i) ^ (a.1 m + 1))).sum := by
  simp only [eval, contractAt, List.map_map, Function.comp_def, Fin.removeNth_apply]

/-- The product `∏ᵢ (log (update r m u) i / RR)^{α i}` splits off the `m`-th factor. -/
private lemma prod_update_split (r : Fin 5 → ℕ) (m : Fin 5) (u : ℕ) (RR : ℝ)
    (a : Fin 5 → ℕ) :
    ∏ i, (Real.log ((Function.update r m u) i) / RR) ^ a i
      = (Real.log u / RR) ^ a m
        * ∏ i : Fin 4, (Real.log (r (m.succAbove i)) / RR) ^ a (m.succAbove i) := by
  rw [Fin.prod_univ_succAbove _ m]
  congr 1
  · rw [Function.update_self]
  · exact Finset.prod_congr rfl
      (fun i _ => by rw [Function.update_of_ne (Fin.succAbove_ne m i)])

/-! ## The relative one-dimensional inner-sum estimate

Truncation of `Salt.Twelve.inner_sum_estimate` (`MvJ.lean`, `private`): the
budget bound (`hUnc`) and the floor-slip bound (`hslip`) are UNCHANGED and keep
the opaque `budget_moment` constant; only the `u ⊥ ∏r`-drop is re-based on
`marked_sqf_phi_rel`, giving `PAS · Pr(r)` with NO opaque constant. -/

private lemma inner_sum_estimate_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') {R : ℕ} (hR : 1 ≤ Real.log R)
    {r : Fin 5 → ℕ} (hr : r ∈ kSieveIndex 5 R W') {m : Fin 5} (hrm : r m = 1) (c : ℕ) :
    |(∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
      - ((W'.totient : ℝ) / W' * Real.log R)
          * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + 1) / ((c : ℝ) + 1)|
    ≤ ((budget_moment W' hW' hpos hUpper c 0).choose * 4 ^ c + Real.log 2)
      + Salt.Maynard.phiAtomSum R W'
          * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
  classical
  obtain ⟨hCatom0, hbudgetspec⟩ := (budget_moment W' hW' hpos hUpper c 0).choose_spec
  set Catom := (budget_moment W' hW' hpos hUpper c 0).choose with hCatomdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hLpos : 0 < Real.log R := lt_of_lt_of_le zero_lt_one hR
  have hQpos : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => kSieveIndex_coord_pos hr i)
  have hQltR : ∏ i, r i < R := ((mem_kSieveIndex_iff r).mp hr).2.2.2
  have hR1 : 1 ≤ R := by omega
  set z := (R - 1) / (∏ i, r i) + 1 with hzdef
  have hz2 : 2 ≤ z := by
    have h1 : 1 ≤ (R - 1) / (∏ i, r i) := by
      rw [Nat.le_div_iff_mul_le hQpos]; omega
    omega
  have hzR : z ≤ R := by
    have := Nat.div_le_self (R - 1) (∏ i, r i)
    omega
  have hcap : ∀ u, u * (∏ i, r i) < R ↔ u < z := by
    intro u
    rw [hzdef, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hQpos]; omega
  have hSeteq :
      (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W')
        = ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
            (fun u => u.Coprime (∏ i, r i)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [update_mem_kSieveIndex_iff hr hrm]
    constructor
    · rintro ⟨_huR, hSF, hcW, hcP, hmul⟩
      exact ⟨⟨(hcap u).mp hmul, hSF, hcW⟩, hcP⟩
    · rintro ⟨⟨hlt, hSF, hcW⟩, hcP⟩
      exact ⟨lt_of_lt_of_le hlt hzR, hSF, hcW, hcP, (hcap u).mpr hlt⟩
  rw [hSeteq]
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hzR' : Real.log (z : ℝ) ≤ Real.log R := Real.log_le_log hzpos (by exact_mod_cast hzR)
  have hzlog0 : (0 : ℝ) ≤ Real.log (z : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  have hQlog0 : (0 : ℝ) ≤ Real.log (∏ i, r i) :=
    Real.log_nonneg (by exact_mod_cast hQpos)
  have hQlogR : Real.log (∏ i, r i) ≤ Real.log R :=
    Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQltR.le)
  -- === The budget bound (UNCHANGED, opaque constant) ===
  have hbudget := hbudgetspec z R hz2 hzR hR
  simp only [pow_zero, mul_one] at hbudget
  have hfacsimp : ((Nat.factorial c : ℝ) * (Nat.factorial 0 : ℝ)) /
      (Nat.factorial (c + 0 + 1) : ℝ) = 1 / ((c : ℝ) + 1) := by
    have hc0 : c + 0 + 1 = c + 1 := rfl
    rw [hc0, Nat.factorial_succ, Nat.factorial_zero]
    have hcf : (Nat.factorial c : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos c).ne'
    push_cast
    field_simp
  rw [hfacsimp] at hbudget
  rw [Nat.zero_add] at hbudget
  have hUnc :
      |(∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'),
            (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        - ((Nat.totient W' : ℝ) / W' * Real.log R)
            * (Real.log z / Real.log R) ^ (c + 1) / ((c : ℝ) + 1)|
      ≤ Catom * 4 ^ c := by
    have ee : ((Nat.totient W' : ℝ) / W' * Real.log R) * (1 / ((c : ℝ) + 1))
          * (Real.log z / Real.log R) ^ (c + 0 + 1)
        = ((Nat.totient W' : ℝ) / W' * Real.log R) * (Real.log z / Real.log R) ^ (c + 1)
            / ((c : ℝ) + 1) := by ring
    rw [ee] at hbudget
    exact hbudget
  -- === The slip bound (UNCHANGED) ===
  have hslip :
      |((Nat.totient W' : ℝ) / W' * Real.log R)
            * (Real.log z / Real.log R) ^ (c + 1) / ((c : ℝ) + 1)
        - ((Nat.totient W' : ℝ) / W' * Real.log R)
            * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + 1) / ((c : ℝ) + 1)|
      ≤ Real.log 2 := by
    set A := Real.log (z : ℝ) / Real.log R with hA
    set B := (Real.log R - Real.log (∏ i, r i)) / Real.log R with hB
    set XX := (Nat.totient W' : ℝ) / W' * Real.log R with hX
    have hX0 : 0 ≤ XX := by
      rw [hX]; positivity
    have hXle : XX ≤ Real.log R := by
      rw [hX]
      have hφle : (Nat.totient W' : ℝ) / W' ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hpos)]
        exact_mod_cast Nat.totient_le W'
      nlinarith [hLpos, hφle]
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    have hA1 : A ≤ 1 := by rw [hA, div_le_one hLpos]; exact hzR'
    have hB0 : 0 ≤ B := by rw [hB]; apply div_nonneg (by linarith) hLpos.le
    have hB1 : B ≤ 1 := by rw [hB, div_le_one hLpos]; linarith
    have hAB : |A - B| ≤ Real.log 2 / Real.log R := by
      have hslipnat := log_natCap_slip (∏ i, r i) R hQpos hQltR
      rw [Nat.cast_prod] at hslipnat
      have hABeq : A - B = (Real.log (((R - 1) / (∏ i, r i) + 1 : ℕ) : ℝ)
            - (Real.log R - Real.log (∏ i, r i))) / Real.log R := by
        rw [hA, hB, ← hzdef, div_sub_div_same]
      rw [hABeq, abs_div, abs_of_pos hLpos, div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hslipnat (inv_nonneg.mpr hLpos.le)
    calc |XX * A ^ (c + 1) / ((c : ℝ) + 1) - XX * B ^ (c + 1) / ((c : ℝ) + 1)|
        = (XX / ((c : ℝ) + 1)) * |A ^ (c + 1) - B ^ (c + 1)| := by
          rw [show XX * A ^ (c + 1) / ((c:ℝ)+1) - XX * B ^ (c + 1) / ((c:ℝ)+1)
                = (XX / ((c:ℝ)+1)) * (A ^ (c + 1) - B ^ (c + 1)) from by ring, abs_mul,
            abs_of_nonneg (div_nonneg hX0 (by positivity))]
      _ ≤ (XX / ((c : ℝ) + 1)) * (((c + 1 : ℕ) : ℝ) * |A - B|) :=
            mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le_unit hA0 hA1 hB0 hB1 (c + 1))
              (div_nonneg hX0 (by positivity))
      _ ≤ (XX / ((c : ℝ) + 1)) * (((c + 1 : ℕ) : ℝ) * (Real.log 2 / Real.log R)) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg hX0 (by positivity))
            exact mul_le_mul_of_nonneg_left hAB (by positivity)
      _ = XX / Real.log R * Real.log 2 := by
            have hcne : ((c:ℝ) + 1) ≠ 0 := by positivity
            have hLne : Real.log R ≠ 0 := ne_of_gt hLpos
            push_cast
            field_simp
      _ ≤ 1 * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
            rw [div_le_one hLpos]; exact hXle
      _ = Real.log 2 := one_mul _
  -- === The RELATIVE drop bound (marked primes via `marked_sqf_phi_rel`) ===
  have hmarked_p : ∀ p ∈ (∏ i, r i).primeFactors,
      (∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
            (fun u => p ∣ u), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ PAS * (1 / ((p : ℝ) - 1)) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpQ, _⟩ := hp
    have hp0 : 0 < p := hpp.pos
    have hpge2 : 2 ≤ p := hpp.two_le
    have hfilterEq :
        ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter (fun u => p ∣ u)
          = (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W' ∧ p ∣ u) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro u _
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [hfilterEq]
    have hfac : ∀ u : ℕ, (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ)
        = (1 / (Real.log R) ^ c) * ((Real.log u) ^ c / (Nat.totient u : ℝ)) := by
      intro u; rw [div_pow]; ring
    rw [Finset.sum_congr rfl (fun u _ => hfac u), ← Finset.mul_sum]
    have hmark := marked_sqf_phi_rel W' hW' hpos c p z hp0 hz2
    have hLcpos : (0 : ℝ) < (Real.log R) ^ c := pow_pos hLpos c
    have htotp : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.totient_prime hpp]; push_cast [Nat.cast_sub hp0]; ring
    have hp1pos : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2:ℝ) ≤ p := by exact_mod_cast hpge2
      linarith
    -- `PAS z W' ≤ PAS R W'` and `(log z)^c ≤ (log R)^c`.
    have hPASz : Salt.Maynard.phiAtomSum z W' ≤ PAS := pas_mono hzR
    have hPASz0 : 0 ≤ Salt.Maynard.phiAtomSum z W' := pas_nonneg z W'
    have hzc : (Real.log z) ^ c ≤ (Real.log R) ^ c := pow_le_pow_left₀ hzlog0 hzR' c
    calc (1 / (Real.log R) ^ c)
          * ∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W' ∧ p ∣ u),
              (Real.log u) ^ c / (Nat.totient u : ℝ)
        ≤ (1 / (Real.log R) ^ c)
            * ((1 / (Nat.totient p : ℝ)) * (Real.log z) ^ c * Salt.Maynard.phiAtomSum z W') := by
          apply mul_le_mul_of_nonneg_left hmark (by positivity)
      _ = (1 / ((p : ℝ) - 1)) * ((Real.log z) ^ c / (Real.log R) ^ c)
            * Salt.Maynard.phiAtomSum z W' := by
          rw [htotp]; ring
      _ ≤ (1 / ((p : ℝ) - 1)) * 1 * PAS := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_one hLcpos]; simpa using hzc
          · exact hPASz
          · exact hPASz0
          · positivity
      _ = PAS * (1 / ((p : ℝ) - 1)) := by ring
  have hg0 : ∀ u : ℕ, (0 : ℝ) ≤ (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) := by
    intro u; positivity
  have hcover :
      (∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
            (fun u => ¬ u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ ∑ p ∈ (∏ i, r i).primeFactors,
            ∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
              (fun u => p ∣ u), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) := by
    rw [Finset.sum_filter]
    have hswap :
        ∑ p ∈ (∏ i, r i).primeFactors,
            ∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
              (fun u => p ∣ u), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ)
          = ∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'),
              ∑ p ∈ (∏ i, r i).primeFactors,
                (if p ∣ u then (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_filter]
    rw [hswap]
    apply Finset.sum_le_sum
    intro u _huT
    by_cases hcop : u.Coprime (∏ i, r i)
    · rw [if_neg (not_not.mpr hcop)]
      exact Finset.sum_nonneg (fun p _ => by split_ifs with h; exacts [hg0 u, le_rfl])
    · rw [if_pos hcop]
      have hdne1 : Nat.gcd u (∏ i, r i) ≠ 1 := hcop
      have hp0prime : Nat.Prime (Nat.gcd u (∏ i, r i)).minFac := Nat.minFac_prime hdne1
      have hp0du : (Nat.gcd u (∏ i, r i)).minFac ∣ u :=
        (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left u (∏ i, r i))
      have hp0dQ : (Nat.gcd u (∏ i, r i)).minFac ∣ (∏ i, r i) :=
        (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right u (∏ i, r i))
      have hp0mem : (Nat.gcd u (∏ i, r i)).minFac ∈ (∏ i, r i).primeFactors := by
        rw [Nat.mem_primeFactors]; exact ⟨hp0prime, hp0dQ, hQpos.ne'⟩
      calc (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ)
          = (if (Nat.gcd u (∏ i, r i)).minFac ∣ u then
              (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) else 0) := by rw [if_pos hp0du]
        _ ≤ ∑ p ∈ (∏ i, r i).primeFactors,
              (if p ∣ u then (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) else 0) :=
            Finset.single_le_sum
              (f := fun p =>
                if p ∣ u then (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) else 0)
              (fun p _ => by split_ifs with h; exacts [hg0 u, le_rfl]) hp0mem
  have hdrop :
      (∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        - (∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
              (fun u => u.Coprime (∏ i, r i)),
            (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ PAS * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'))
      (fun u => u.Coprime (∏ i, r i))
      (fun u => (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
    have hdropeq :
        (∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'),
            (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
          - (∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
                (fun u => u.Coprime (∏ i, r i)),
              (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
          = ∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
              (fun u => ¬ u.Coprime (∏ i, r i)),
              (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) := by
      linarith [hsplit]
    rw [hdropeq]
    calc _ ≤ ∑ p ∈ (∏ i, r i).primeFactors,
            ∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
              (fun u => p ∣ u), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) := hcover
      _ ≤ ∑ p ∈ (∏ i, r i).primeFactors, PAS * (1 / ((p : ℝ) - 1)) :=
            Finset.sum_le_sum hmarked_p
      _ = PAS * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
            rw [Finset.mul_sum]
  have hSfull_le :
      (∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
            (fun u => u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ ∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'),
            (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro u _ _; exact hg0 u
  have hDropAbs :
      |(∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
            (fun u => u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        - (∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'),
            (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))|
      ≤ PAS * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hSfull_le])]
    exact hdrop
  have t1 := abs_sub_le
    (∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
        (fun u => u.Coprime (∏ i, r i)), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
    (∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'),
        (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
    (((Nat.totient W' : ℝ) / W' * Real.log R)
      * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + 1) / ((c : ℝ) + 1))
  have t2 := abs_sub_le
    (∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W'),
        (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
    (((Nat.totient W' : ℝ) / W' * Real.log R) * (Real.log z / Real.log R) ^ (c + 1) / ((c : ℝ) + 1))
    (((Nat.totient W' : ℝ) / W' * Real.log R)
      * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + 1) / ((c : ℝ) + 1))
  linarith [hUnc, hslip, hDropAbs, t1, t2]

/-! ## `inner_contract_rel` (frozen deliverable 1) -/

theorem inner_contract_rel (F : Poly) (m : Fin 5) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
      ∀ r ∈ kSieveIndex 5 R W', r m = 1 →
      |(∑ u ∈ Finset.range R,
            yF R W' F (Function.update r m u) / (Nat.totient u : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R)
            * eval (contractAt m F)
                (fun i => Real.log (r (m.succAbove i)) / Real.log R)|
      ≤ c + A * Salt.Maynard.phiAtomSum R W'
              * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
  classical
  set cF : ℝ := (F.map (fun a => |(a.2 : ℝ)|)).sum with hcFdef
  have hcF0 : 0 ≤ cF := by
    rw [hcFdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx; exact abs_nonneg _
  refine ⟨cF, hcF0, ?_⟩
  intro W' D hW' hpos hUpper _hD _hDW
  set Cb : ℕ → ℝ := fun k => (budget_moment W' hW' hpos hUpper k 0).choose with hCbdef
  have hCb0 : ∀ k, 0 ≤ Cb k := fun k => (budget_moment W' hW' hpos hUpper k 0).choose_spec.1
  set Cabs : ℝ :=
    (F.map (fun a => |(a.2 : ℝ)| * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2))).sum with hCabsdef
  have hCabs0 : 0 ≤ Cabs := by
    rw [hCabsdef]; apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx
    exact mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (hCb0 _) (by positivity)) (Real.log_nonneg (by norm_num)))
  refine ⟨Cabs, hCabs0, ?_⟩
  intro R hR r hr hrm
  have hLpos : 0 < Real.log R := lt_of_lt_of_le zero_lt_one hR
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  set S : ℝ := ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p:ℝ) - 1)) with hSdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply Finset.sum_nonneg
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  -- The budget factor `B = 1 − Σ t'`.
  have hBval : (1 : ℝ) - ∑ i : Fin 4, Real.log (r (m.succAbove i)) / Real.log R
      = (Real.log R - Real.log (∏ i, r i)) / Real.log R := by
    have hsum : ∑ i : Fin 4, Real.log (r (m.succAbove i)) = Real.log (∏ i, (r i : ℝ)) := by
      have h5 : ∑ j : Fin 5, Real.log (r j)
          = Real.log (r m) + ∑ i : Fin 4, Real.log (r (m.succAbove i)) :=
        Fin.sum_univ_succAbove (fun j => Real.log (r j)) m
      have hlogprod : Real.log (∏ i, (r i : ℝ)) = ∑ j : Fin 5, Real.log (r j) := by
        rw [Real.log_prod]
        intro j _
        exact_mod_cast (kSieveIndex_coord_pos hr j).ne'
      rw [hlogprod, h5, hrm]; simp
    rw [← Finset.sum_div, hsum, sub_div, div_self (ne_of_gt hLpos)]
  -- === Rewrite the target main term ===
  have hTarget : ((W'.totient : ℝ) / W' * Real.log R)
        * eval (contractAt m F) (fun i => Real.log (r (m.succAbove i)) / Real.log R)
      = (F.map (fun a => (a.2 : ℝ)
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * (((W'.totient : ℝ) / W' * Real.log R)
              * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (a.1 m + 1)
              / ((a.1 m : ℝ) + 1)))).sum := by
    rw [eval_contractAt, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    rw [hBval]
    push_cast
    ring
  -- === Rewrite the full sum ===
  have hFull : (∑ u ∈ Finset.range R, yF R W' F (Function.update r m u) / (Nat.totient u : ℝ))
      = (F.map (fun a => (a.2 : ℝ)
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * (∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
                (Real.log u / Real.log R) ^ a.1 m / (Nat.totient u : ℝ)))).sum := by
    have e1 : (∑ u ∈ Finset.range R, yF R W' F (Function.update r m u) / (Nat.totient u : ℝ))
        = ∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
            eval (ofPoly F) (fun i => Real.log ((Function.update r m u) i) / Real.log R)
              / (Nat.totient u : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      unfold yF
      split_ifs with h
      · rfl
      · simp
    rw [e1, Finset.sum_congr rfl (fun u _ => by rw [eval_ofPoly, ic_list_sum_div]),
      ic_sum_finset_list_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    have hre : ∀ u : ℕ,
        (a.2 : ℝ) * (∏ i, (Real.log ((Function.update r m u) i) / Real.log R) ^ a.1 i)
            / (Nat.totient u : ℝ)
          = ((a.2 : ℝ)
              * ∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
            * ((Real.log u / Real.log R) ^ a.1 m / (Nat.totient u : ℝ)) := by
      intro u
      rw [prod_update_split r m u (Real.log R) a.1]; ring
    rw [Finset.sum_congr rfl (fun u _ => hre u), ← Finset.mul_sum]
  -- === The per-monomial bound (RELATIVE) ===
  have hpera : ∀ a ∈ F,
      |((a.2 : ℝ)
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * (∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
                (Real.log u / Real.log R) ^ a.1 m / (Nat.totient u : ℝ)))
        - ((a.2 : ℝ)
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * (((W'.totient : ℝ) / W' * Real.log R)
              * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (a.1 m + 1)
              / ((a.1 m : ℝ) + 1)))|
      ≤ |(a.2 : ℝ)| * ((Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2) + PAS * S) := by
    intro a _
    have hKnn : 0 ≤ ∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i) := by
      apply Finset.prod_nonneg
      intro i _
      exact pow_nonneg (div_nonneg (Real.log_nonneg (by
        exact_mod_cast kSieveIndex_coord_pos hr (m.succAbove i))) hLpos.le) _
    have hK1 : (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i)) ≤ 1 := by
      apply Finset.prod_le_one
      · intro i _
        exact pow_nonneg (div_nonneg (Real.log_nonneg (by
          exact_mod_cast kSieveIndex_coord_pos hr (m.succAbove i))) hLpos.le) _
      · intro i _
        apply pow_le_one₀ (div_nonneg (Real.log_nonneg (by
          exact_mod_cast kSieveIndex_coord_pos hr (m.succAbove i))) hLpos.le)
        rw [div_le_one hLpos]
        exact Real.log_le_log (by exact_mod_cast kSieveIndex_coord_pos hr (m.succAbove i))
          (by exact_mod_cast (kSieveIndex_coord_lt hr (m.succAbove i)).le)
    have hfactor :
        ((a.2 : ℝ) * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
            * (∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
                  (Real.log u / Real.log R) ^ a.1 m / (Nat.totient u : ℝ)))
          - ((a.2 : ℝ) * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
            * (((W'.totient : ℝ) / W' * Real.log R)
                * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (a.1 m + 1)
                / ((a.1 m : ℝ) + 1)))
        = (a.2 : ℝ) * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
            * ((∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
                  (Real.log u / Real.log R) ^ a.1 m / (Nat.totient u : ℝ))
              - ((W'.totient : ℝ) / W' * Real.log R)
                  * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (a.1 m + 1)
                  / ((a.1 m : ℝ) + 1)) := by ring
    rw [hfactor, abs_mul, abs_mul, abs_of_nonneg hKnn]
    have hest := inner_sum_estimate_rel W' hW' hpos hUpper hR hr hrm (a.1 m)
    rw [← hPASdef, ← hSdef] at hest
    calc |(a.2 : ℝ)|
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * |(∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
                (Real.log u / Real.log R) ^ a.1 m / (Nat.totient u : ℝ))
              - ((W'.totient : ℝ) / W' * Real.log R)
                  * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (a.1 m + 1)
                  / ((a.1 m : ℝ) + 1)|
        ≤ |(a.2 : ℝ)| * 1 * ((Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2) + PAS * S) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hK1 (abs_nonneg _)) hest (abs_nonneg _)
          exact mul_nonneg (abs_nonneg _) zero_le_one
      _ = |(a.2 : ℝ)| * ((Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2) + PAS * S) := by rw [mul_one]
  -- === Assemble ===
  have hbndsum :
      (F.map (fun a => |(a.2 : ℝ)| * ((Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2) + PAS * S))).sum
        = Cabs + cF * PAS * S := by
    have hsplit :
        (fun a : Mono => |(a.2 : ℝ)| * ((Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2) + PAS * S))
        = fun a => (|(a.2 : ℝ)| * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2))
          + (|(a.2 : ℝ)|) * (PAS * S) := by
      funext a; ring
    rw [hsplit, ic_list_sum_map_add, List.sum_map_mul_right, ← hCabsdef, ← hcFdef]
    ring
  rw [hFull, hTarget, list_sum_map_sub]
  refine le_trans (ic_list_abs_sum_le F _) ?_
  refine le_trans (ic_list_sum_le F _ _ hpera) ?_
  rw [hbndsum]

end Salt.Twelve
