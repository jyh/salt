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

/-! ## `mv_J_split` — shared helpers (private copies from `MvJ.lean`) -/

private lemma mjs_gMult_prime_cast {p : ℕ} (hp : Nat.Prime p) : (gMult p : ℝ) = (p : ℝ) - 2 := by
  have : gMult p = p - 2 := by rw [gMult, Nat.Prime.primeFactors hp, Finset.prod_singleton]
  rw [this, Nat.cast_sub hp.two_le]; norm_num

private lemma mjs_gMult_one_cast : (gMult 1 : ℝ) = 1 := by
  rw [gMult, Nat.primeFactors_one, Finset.prod_empty]; norm_num

private lemma mjs_gMult_pq_cast {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (gMult (p * q) : ℝ) = ((p:ℝ) - 2) * ((q:ℝ) - 2) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hmul : gMult (p * q) = gMult p * gMult q := by
    rw [gMult, gMult, gMult, Nat.Coprime.primeFactors_mul hcop,
      Finset.prod_union hcop.disjoint_primeFactors]
  rw [hmul, Nat.cast_mul, mjs_gMult_prime_cast hp, mjs_gMult_prime_cast hq]

private lemma mjs_box_PF_subset {W' D R : ℕ} (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    {x : ℕ} (hxR : x < R) (hxcop : x.Coprime W') :
    x.primeFactors ⊆ (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpx := Nat.dvd_of_mem_primeFactors hp
  have hx0 : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
  have hpltR : p < R := lt_of_le_of_lt (Nat.le_of_dvd hx0 hpx) hxR
  have hnpW : ¬ p ∣ W' := by
    intro hpW; have h1 : p ∣ 1 := hxcop ▸ Nat.dvd_gcd hpx hpW
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
  rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hpltR, hpp, hD p hpp hnpW⟩

private lemma mjs_PFsum_nn (m : ℕ) : 0 ≤ ∑ p ∈ m.primeFactors, (1 / ((p:ℝ) - 1)) := by
  apply Finset.sum_nonneg; intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
  have : (0:ℝ) < (p:ℝ) - 1 := by linarith
  positivity

private lemma mjs_sum_biUnion_le {ι : Type*} (s : Finset ι) (t : ι → Finset ℕ)
    (g : ℕ → ℝ) (hg : ∀ i ∈ s, ∀ p ∈ t i, 0 ≤ g p) :
    ∑ p ∈ s.biUnion t, g p ≤ ∑ i ∈ s, ∑ p ∈ t i, g p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hga : ∀ p ∈ t a, 0 ≤ g p := hg a (Finset.mem_insert_self a s)
    have hgs : ∀ i ∈ s, ∀ p ∈ t i, 0 ≤ g p :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hunion : ∑ p ∈ t a ∪ s.biUnion t, g p ≤ ∑ p ∈ t a, g p + ∑ p ∈ s.biUnion t, g p := by
      rw [← Finset.sum_union_inter]
      have : 0 ≤ ∑ p ∈ t a ∩ s.biUnion t, g p :=
        Finset.sum_nonneg (fun p hp => hga p (Finset.mem_of_mem_inter_left hp))
      linarith
    linarith [ih hgs]

private lemma mjs_P_subadd (ρ : Fin 4 → ℕ) (hρ : ∀ i, ρ i ≠ 0) :
    (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
      ≤ ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) := by
  classical
  have hsub : (∏ i, ρ i).primeFactors ⊆ Finset.univ.biUnion (fun i => (ρ i).primeFactors) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨i, _, hpi⟩ := (Prime.exists_mem_finset_dvd hpp.prime hpdvd)
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, Nat.mem_primeFactors.mpr ⟨hpp, hpi, hρ i⟩⟩
  calc (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
      ≤ ∑ p ∈ Finset.univ.biUnion (fun i => (ρ i).primeFactors), (1 / ((p:ℝ) - 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        rw [Finset.mem_biUnion] at hp
        obtain ⟨i, _, hpi⟩ := hp
        have hpp := Nat.prime_of_mem_primeFactors hpi
        have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        have : (0:ℝ) < (p:ℝ) - 1 := by linarith
        positivity
    _ ≤ ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) := by
        apply mjs_sum_biUnion_le
        intro i _ p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        have : (0:ℝ) < (p:ℝ) - 1 := by linarith
        positivity

private lemma mjs_factor_one (F_R : Finset ℕ) (i : Fin 4) (w : ℕ → ℝ) :
    ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R), w (ρ i) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ))) * (∑ x ∈ F_R, (1 / (gMult x : ℝ))) ^ 3 := by
  classical
  have hrw : ∀ ρ : Fin 4 → ℕ, w (ρ i) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∏ k, (if k = i then w (ρ k) * (1 / (gMult (ρ k) : ℝ)) else (1 / (gMult (ρ k) : ℝ))) := by
    intro ρ
    rw [← Finset.mul_prod_erase Finset.univ (fun k => (1 / (gMult (ρ k) : ℝ))) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ
        (fun k => if k = i then w (ρ k) * (1 / (gMult (ρ k) : ℝ)) else (1 / (gMult (ρ k) : ℝ)))
        (Finset.mem_univ i)]
    rw [if_pos rfl]
    have hp : (∏ k ∈ Finset.univ.erase i,
        (if k = i then w (ρ k) * (1 / (gMult (ρ k) : ℝ)) else (1 / (gMult (ρ k) : ℝ))))
        = ∏ k ∈ Finset.univ.erase i, (1 / (gMult (ρ k) : ℝ)) :=
      Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))
    rw [hp]; ring
  rw [Finset.sum_congr rfl (fun ρ _ => hrw ρ),
    ← Finset.prod_univ_sum (fun _ : Fin 4 => F_R)
      (fun k x => if k = i then w x * (1 / (gMult x : ℝ)) else (1 / (gMult x : ℝ)))]
  have heval : ∀ k : Fin 4,
      (∑ x ∈ F_R, (if k = i then w x * (1 / (gMult x : ℝ)) else (1 / (gMult x : ℝ))))
      = if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ)))
          else (∑ x ∈ F_R, (1 / (gMult x : ℝ))) := by
    intro k; by_cases hk : k = i
    · simp only [hk, if_true]
    · simp only [hk, if_false]
  rw [Finset.prod_congr rfl (fun k _ => heval k)]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun k => if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ)))
        else (∑ x ∈ F_R, (1 / (gMult x : ℝ)))) (Finset.mem_univ i)]
  rw [if_pos rfl]
  have hp2 : (∏ k ∈ Finset.univ.erase i,
      (if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ)))
        else (∑ x ∈ F_R, (1 / (gMult x : ℝ)))))
      = ∏ k ∈ Finset.univ.erase i, (∑ x ∈ F_R, (1 / (gMult x : ℝ))) :=
    Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))
  rw [hp2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

private lemma mjs_enlarge_to_PB (W' R : ℕ)
    (num : (Fin 4 → ℕ) → ℝ) (hnum0 : ∀ ρ, 0 ≤ num ρ) :
    (∑ ρ ∈ kSieveIndex 4 R W', num ρ / ∏ i, (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ Fintype.piFinset
          (fun _ : Fin 4 => (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W')),
          num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
  classical
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  have hsub1 : kSieveIndex 4 R W' ⊆ decBox 4 R W' := by
    intro r hr
    have hmem := (mem_kSieveIndex_iff r).mp hr
    obtain ⟨hsqf, _, hcop, hprod⟩ := hmem
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
  have hsub2 : decBox 4 R W' ⊆ Fintype.piFinset (fun _ : Fin 4 => F_R) := by
    intro r hr
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
    rw [Fintype.mem_piFinset]; intro i
    rw [hF_R, Finset.mem_filter, Finset.mem_range]; exact ⟨hr.1 i, hr.2.1 i, hr.2.2.1 i⟩
  have hrw : ∀ ρ, num ρ / ∏ i, (gMult (ρ i) : ℝ) = num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
    intro ρ; rw [Finset.prod_div_distrib, Finset.prod_const_one, div_eq_mul_inv, one_div,
      ← Finset.prod_inv_distrib]
  have hnn : ∀ ρ, 0 ≤ num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) :=
    fun ρ => mul_nonneg (hnum0 ρ) (Finset.prod_nonneg (fun i _ => by positivity))
  calc (∑ ρ ∈ kSieveIndex 4 R W', num ρ / ∏ i, (gMult (ρ i) : ℝ))
      = ∑ ρ ∈ kSieveIndex 4 R W', num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) :=
        Finset.sum_congr rfl (fun ρ _ => hrw ρ)
    _ ≤ ∑ ρ ∈ decBox 4 R W', num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun ρ _ _ => hnn ρ)
    _ ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R), num ρ * ∏ i, (1 / (gMult (ρ i) : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun ρ _ _ => hnn ρ)

private lemma mjs_erase_prod_removeNth {M : Type*} [CommMonoid M] (m : Fin 5) (F : Fin 5 → M) :
    ∏ i ∈ Finset.univ.erase m, F i = ∏ i : Fin 4, F (m.succAbove i) := by
  have he : Finset.univ.erase m = ({m}ᶜ : Finset (Fin 5)) := by
    rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]
  rw [he, ← Fin.image_succAbove_univ m, Finset.prod_image
    (fun i _ j _ h => Fin.succAbove_right_injective h)]

private lemma mjs_eval_bpoly_bound {n : ℕ} (P : BPoly n) (t : Fin n → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (hs : ∑ i, t i ≤ 1) :
    |eval P t| ≤ (P.map (fun mo => |(mo.2.2 : ℝ)|)).sum := by
  unfold eval
  refine le_trans (ic_list_abs_sum_le P _) (ic_list_sum_le _ _ _ (fun mo _ => ?_))
  have hprod0 : 0 ≤ ∏ i, t i ^ mo.1 i := Finset.prod_nonneg (fun i _ => pow_nonneg (ht0 i) _)
  have hprod1 : ∏ i, t i ^ mo.1 i ≤ 1 :=
    Finset.prod_le_one (fun i _ => pow_nonneg (ht0 i) _) (fun i _ => pow_le_one₀ (ht0 i) (ht1 i))
  have hb0 : 0 ≤ 1 - ∑ i, t i := by linarith
  have hb1 : 1 - ∑ i, t i ≤ 1 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => ht0 i); linarith
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hprod0, abs_of_nonneg hb0]
  calc |(mo.2.2:ℝ)| * (∏ i, t i ^ mo.1 i) * (1 - ∑ i, t i) ^ mo.2.1
      ≤ |(mo.2.2:ℝ)| * 1 * 1 := by
        apply mul_le_mul _ (pow_le_one₀ hb0 hb1) (pow_nonneg hb0 _) (by positivity)
        exact mul_le_mul_of_nonneg_left hprod1 (abs_nonneg _)
    _ = |(mo.2.2:ℝ)| := by ring

/-! ### Relative one-coordinate g-moments (`M0`, `MQ`, `MQ2`) over `sqfCop R W'` -/

private lemma mjs_M0_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)))
      ≤ 2 * Salt.Maynard.phiAtomSum R W' := by
  have hg1 := marked_sqf_g_rel W' hW' hpos 0 D 1 R hD hDW one_pos hR2
  have hFeq : ((Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ (1:ℕ) ∣ r))
      = (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') := by
    apply Finset.filter_congr; intro r _
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, one_dvd r⟩
  rw [mjs_gMult_one_cast, hFeq] at hg1
  have hL : ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (Real.log x) ^ 0 / (gMult x : ℝ)
      = ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)) :=
    Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
  rw [hL] at hg1
  simpa using hg1

private lemma mjs_M0_op (W' : ℕ) (_hW' : Squarefree W') (_hpos : 0 < W') (cg : ℝ)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)))
      ≤ cg * Real.log R := by
  have hg1 := hcg D 1 R hD hDW one_pos hR2
  have hFeq : ((Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ (1:ℕ) ∣ r))
      = (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') := by
    apply Finset.filter_congr; intro r _
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, one_dvd r⟩
  rw [mjs_gMult_one_cast, hFeq] at hg1
  have hL : ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (Real.log x) ^ 0 / (gMult x : ℝ)
      = ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)) :=
    Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
  rw [hL] at hg1
  have hRw : (1:ℝ) / 1 * cg * (Real.log R) ^ (0 + 1) = cg * Real.log R := by norm_num
  rw [hRw] at hg1
  exact hg1

private lemma mjs_MQ_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
      ≤ 8 * Salt.Maynard.phiAtomSum R W' / (D : ℝ) := by
  classical
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set Primes := (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimes
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have hswap : (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
      ≤ ∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
          ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)) := by
    have hstep : (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
        ≤ ∑ x ∈ F_R, ∑ p ∈ Primes,
            (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [hF_R, Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hxR, hxsf, hxcop⟩ := hx
      rw [Finset.sum_div]
      have hcongr : ∑ p ∈ x.primeFactors, 1 / ((p:ℝ) - 1) / (gMult x : ℝ)
          = ∑ p ∈ x.primeFactors, 1 / ((p:ℝ) - 1) * (1 / (gMult x : ℝ)) :=
        Finset.sum_congr rfl (fun p _ => by ring)
      rw [hcongr, ← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter]
        exact ⟨mjs_box_PF_subset hDW hxR hxcop hp, Nat.dvd_of_mem_primeFactors hp⟩
      · intro p hp _
        rw [Finset.mem_filter, hPrimes, Finset.mem_filter, Finset.mem_range] at hp
        have hpD : D < p := hp.1.2.2
        have hp1 : (0:ℝ) < (p:ℝ) - 1 := by
          have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
          linarith
        positivity
    calc (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
        ≤ ∑ x ∈ F_R, ∑ p ∈ Primes,
            (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) := hstep
      _ = ∑ p ∈ Primes, ∑ x ∈ F_R,
            (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) := Finset.sum_comm
      _ = ∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
            ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)) := by
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.mul_sum, ← Finset.sum_filter]
  refine le_trans hswap ?_
  have hper : ∀ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
        ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ))
      ≤ 2 * PAS * (2 / ((p:ℝ) - 1) ^ 2) := by
    intro p hp
    rw [hPrimes, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpR, hpp, hpD⟩ := hp
    have hp3 : 3 ≤ p := by omega
    have hp3R : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    have hmk := marked_sqf_g_rel W' hW' hpos 0 D p R hD hDW hpp.pos hR2
    rw [mjs_gMult_prime_cast hpp] at hmk
    have hfilt : F_R.filter (fun x => p ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨h1,h2,h3⟩
      · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1,h2⟩,h3⟩
    rw [hfilt]
    have hsum_le : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
          (1 / (gMult x : ℝ)) ≤ (1 / ((p:ℝ) - 2)) * 2 * PAS := by
      have hcv : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
          (Real.log x) ^ 0 / (gMult x : ℝ)
          = ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
            (1 / (gMult x : ℝ)) := Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
      rw [hcv] at hmk
      rw [hPAS]; simpa using hmk
    have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
    have hp2 : (0:ℝ) < (p:ℝ) - 2 := by linarith
    have hfrac : (1 / ((p:ℝ) - 1)) * (1 / ((p:ℝ) - 2)) ≤ 2 / ((p:ℝ) - 1) ^ 2 := by
      rw [one_div_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc (1 / ((p:ℝ) - 1)) * ∑ x ∈ (Finset.range R).filter
            (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r), (1 / (gMult x : ℝ))
        ≤ (1 / ((p:ℝ) - 1)) * ((1 / ((p:ℝ) - 2)) * 2 * PAS) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = 2 * PAS * ((1 / ((p:ℝ) - 1)) * (1 / ((p:ℝ) - 2))) := by ring
      _ ≤ 2 * PAS * (2 / ((p:ℝ) - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
  calc (∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
          ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)))
      ≤ ∑ p ∈ Primes, 2 * PAS * (2 / ((p:ℝ) - 1) ^ 2) := Finset.sum_le_sum hper
    _ = 2 * PAS * (2 * ∑ p ∈ Primes, 1 / ((p:ℝ) - 1) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ 2 * PAS * (2 * (2 / (D:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left (prime_tail D R hD) (by norm_num)
    _ = 8 * PAS / (D : ℝ) := by ring

private lemma mjs_MQ2_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / (gMult x : ℝ))
      ≤ 40 * Salt.Maynard.phiAtomSum R W' / (D : ℝ) := by
  classical
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set Primes := (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimes
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have hprime_facts : ∀ p ∈ Primes,
      Nat.Prime p ∧ D < p ∧ (0:ℝ) < (p:ℝ) - 1 ∧ (0:ℝ) < (p:ℝ) - 2 := by
    intro p hp
    rw [hPrimes, Finset.mem_filter, Finset.mem_range] at hp
    have hpge : (4:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 4 ≤ p)
    exact ⟨hp.2.1, hp.2.2, by linarith, by linarith⟩
  set c1 : ℕ → ℝ := fun p => 1 / ((p:ℝ) - 1) with hc1def
  set S : ℕ → ℕ → ℝ := fun p q =>
    ∑ x ∈ F_R.filter (fun x => p ∣ x ∧ q ∣ x), (1 / (gMult x : ℝ)) with hSdef
  have hSnn : ∀ p q, 0 ≤ S p q := fun p q => Finset.sum_nonneg (fun x _ => by positivity)
  have hexp : ∀ x, (∑ p ∈ x.primeFactors, c1 p) ^ 2 / (gMult x : ℝ)
      = ∑ p ∈ x.primeFactors, ∑ q ∈ x.primeFactors, c1 p * c1 q * (1 / (gMult x : ℝ)) := by
    intro x
    rw [pow_two, sum_mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro q _; ring
  have hbound_x : ∀ x ∈ F_R,
      (∑ p ∈ x.primeFactors, ∑ q ∈ x.primeFactors, c1 p * c1 q * (1 / (gMult x : ℝ)))
      ≤ ∑ p ∈ Primes, ∑ q ∈ Primes,
          (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
    intro x hx
    rw [hF_R, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hxR, hxsf, hxcop⟩ := hx
    have hsub : x.primeFactors ⊆ Primes := mjs_box_PF_subset hDW hxR hxcop
    have hnnW : ∀ p q, p ∈ Primes → q ∈ Primes → 0 ≤ c1 p * c1 q * (1 / (gMult x : ℝ)) := by
      intro p q hpP hqP
      obtain ⟨_, _, hp1, _⟩ := hprime_facts p hpP
      obtain ⟨_, _, hq1, _⟩ := hprime_facts q hqP
      rw [hc1def]; positivity
    calc (∑ p ∈ x.primeFactors, ∑ q ∈ x.primeFactors, c1 p * c1 q * (1 / (gMult x : ℝ)))
        ≤ ∑ p ∈ x.primeFactors, ∑ q ∈ Primes,
            (if q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
          apply Finset.sum_le_sum; intro p hp
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq; rw [Finset.mem_filter]
            exact ⟨hsub hq, Nat.dvd_of_mem_primeFactors hq⟩
          · intro q hq _; exact hnnW p q (hsub hp) (Finset.mem_of_mem_filter q hq)
      _ ≤ ∑ p ∈ Primes,
            (if p ∣ x then ∑ q ∈ Primes,
              (if q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) else 0) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; rw [Finset.mem_filter]
            exact ⟨hsub hp, Nat.dvd_of_mem_primeFactors hp⟩
          · intro p hp _
            apply Finset.sum_nonneg; intro q hq; split_ifs with hqx
            · exact hnnW p q (Finset.mem_of_mem_filter p hp) hq
            · exact le_refl 0
      _ = ∑ p ∈ Primes, ∑ q ∈ Primes,
            (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
          apply Finset.sum_congr rfl; intro p _
          by_cases hpx : p ∣ x
          · rw [if_pos hpx]; apply Finset.sum_congr rfl; intro q _
            by_cases hqx : q ∣ x
            · rw [if_pos hqx, if_pos ⟨hpx, hqx⟩]
            · rw [if_neg hqx, if_neg (fun h => hqx h.2)]
          · rw [if_neg hpx]; symm; apply Finset.sum_eq_zero; intro q _
            rw [if_neg (fun h => hpx h.1)]
  have hMQ2_le : (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, c1 p) ^ 2 / (gMult x : ℝ))
      ≤ ∑ p ∈ Primes, ∑ q ∈ Primes, c1 p * c1 q * S p q := by
    calc ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, c1 p) ^ 2 / (gMult x : ℝ)
        = ∑ x ∈ F_R, ∑ p ∈ x.primeFactors, ∑ q ∈ x.primeFactors,
            c1 p * c1 q * (1 / (gMult x : ℝ)) := by
          apply Finset.sum_congr rfl; intro x _; exact hexp x
      _ ≤ ∑ x ∈ F_R, ∑ p ∈ Primes, ∑ q ∈ Primes,
            (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) :=
          Finset.sum_le_sum hbound_x
      _ = ∑ p ∈ Primes, ∑ q ∈ Primes, ∑ x ∈ F_R,
            (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_comm]
      _ = ∑ p ∈ Primes, ∑ q ∈ Primes, c1 p * c1 q * S p q := by
          apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _
          rw [← Finset.sum_filter, hSdef, Finset.mul_sum]
  refine le_trans hMQ2_le ?_
  have htail_a : ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) ≤ 4 / (D:ℝ) := by
    have hpt : ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)))
        ≤ ∑ p ∈ Primes, (2 / ((p:ℝ) - 1) ^ 2) := by
      apply Finset.sum_le_sum; intro p hp
      obtain ⟨_, hpD, hp1, hp2⟩ := hprime_facts p hp
      have hp4 : (4:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 4 ≤ p)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hp1, hp2, hp4]
    calc ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)))
        ≤ ∑ p ∈ Primes, (2 / ((p:ℝ) - 1) ^ 2) := hpt
      _ = 2 * ∑ p ∈ Primes, (1 / ((p:ℝ) - 1) ^ 2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ 2 * (2 / (D:ℝ)) := by apply mul_le_mul_of_nonneg_left (prime_tail D R hD) (by norm_num)
      _ = 4 / (D:ℝ) := by ring
  have hmarked : ∀ s : ℕ, 0 < s →
      (∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
          (1 / (gMult x : ℝ)))
        ≤ (1 / (gMult s : ℝ)) * 2 * PAS := by
    intro s hs
    have hmk := marked_sqf_g_rel W' hW' hpos 0 D s R hD hDW hs hR2
    have hcv : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log x)^0/(gMult x:ℝ)
        = ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
          (1/(gMult x:ℝ)) := Finset.sum_congr rfl (fun x _ => by rw [pow_zero])
    rw [hcv] at hmk; rw [hPAS]; simpa using hmk
  have hS_diag : ∀ p ∈ Primes, S p p ≤ (1 / ((p:ℝ) - 2)) * 2 * PAS := by
    intro p hp
    obtain ⟨hpp, _, _, _⟩ := hprime_facts p hp
    have hfe : F_R.filter (fun x => p ∣ x ∧ p ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3,_⟩; exact ⟨h1,h2,h3⟩
      · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1,h2⟩,h3,h3⟩
    simp only [hSdef]; rw [hfe]
    have := hmarked p hpp.pos; rw [mjs_gMult_prime_cast hpp] at this; exact this
  have hS_off : ∀ p ∈ Primes, ∀ q ∈ Primes, p ≠ q →
      S p q ≤ (1 / (((p:ℝ) - 2) * ((q:ℝ) - 2))) * 2 * PAS := by
    intro p hp q hq hpq
    obtain ⟨hpp, _, _, _⟩ := hprime_facts p hp
    obtain ⟨hqp, _, _, _⟩ := hprime_facts q hq
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hpq
    have hfe : F_R.filter (fun x => p ∣ x ∧ q ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p * q ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3,h4⟩; exact ⟨h1,h2, hcop.mul_dvd_of_dvd_of_dvd h3 h4⟩
      · rintro ⟨h1,h2,h3⟩
        exact ⟨⟨h1,h2⟩, (dvd_mul_right p q).trans h3, (dvd_mul_left q p).trans h3⟩
    simp only [hSdef]; rw [hfe]
    have := hmarked (p*q) (Nat.mul_pos hpp.pos hqp.pos)
    rw [mjs_gMult_pq_cast hpp hqp hpq] at this; exact this
  have hsplit : ∑ p ∈ Primes, ∑ q ∈ Primes, c1 p * c1 q * S p q
      = ∑ p ∈ Primes, c1 p * c1 p * S p p
        + ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p hp
    exact (Finset.add_sum_erase Primes (fun q => c1 p * c1 q * S p q) hp).symm
  rw [hsplit]
  have h2PAS0 : 0 ≤ 2 * PAS := by positivity
  have hdiag : ∑ p ∈ Primes, c1 p * c1 p * S p p ≤ 2 * PAS * (4 / (D:ℝ)) := by
    have hstep : ∑ p ∈ Primes, c1 p * c1 p * S p p
        ≤ ∑ p ∈ Primes, (2 * PAS) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by
      apply Finset.sum_le_sum; intro p hp
      obtain ⟨_, _, hp1, hp2⟩ := hprime_facts p hp
      have hc1nn : 0 ≤ c1 p := by rw [hc1def]; positivity
      have hc1le1 : c1 p ≤ 1 := by rw [hc1def, div_le_one hp1]; linarith
      have hcSnn : 0 ≤ c1 p * S p p := mul_nonneg hc1nn (hSnn p p)
      have hap : c1 p * (1 / ((p:ℝ) - 2)) = 1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)) := by
        rw [hc1def, div_mul_div_comm, one_mul]
      calc c1 p * c1 p * S p p
          = c1 p * (c1 p * S p p) := by ring
        _ ≤ 1 * (c1 p * S p p) := mul_le_mul_of_nonneg_right hc1le1 hcSnn
        _ = c1 p * S p p := one_mul _
        _ ≤ c1 p * ((1 / ((p:ℝ) - 2)) * 2 * PAS) :=
            mul_le_mul_of_nonneg_left (hS_diag p hp) hc1nn
        _ = (2 * PAS) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by rw [← hap]; ring
    calc ∑ p ∈ Primes, c1 p * c1 p * S p p
        ≤ ∑ p ∈ Primes, (2 * PAS) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := hstep
      _ = (2 * PAS) * ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by rw [Finset.mul_sum]
      _ ≤ (2 * PAS) * (4 / (D:ℝ)) := mul_le_mul_of_nonneg_left htail_a h2PAS0
  have hoff : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
      ≤ 2 * PAS * ((4 / (D:ℝ)) * (4 / (D:ℝ))) := by
    set a : ℕ → ℝ := fun p => 1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)) with hadef
    have hann : ∀ p ∈ Primes, 0 ≤ a p := by
      intro p hp; obtain ⟨_,_,hp1,hp2⟩ := hprime_facts p hp; rw [hadef]; positivity
    have hstep1 : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (2 * PAS) * (a p * a q) := by
      apply Finset.sum_le_sum; intro p hp
      apply Finset.sum_le_sum; intro q hq
      have hqP : q ∈ Primes := Finset.mem_of_mem_erase hq
      have hne : p ≠ q := (Finset.ne_of_mem_erase hq).symm
      obtain ⟨_,_,hp1,hp2⟩ := hprime_facts p hp
      obtain ⟨_,_,hq1,hq2⟩ := hprime_facts q hqP
      have hc1nn : 0 ≤ c1 p * c1 q := by rw [hc1def]; positivity
      have h1 : (p:ℝ)-1 ≠ 0 := ne_of_gt hp1
      have h2 : (p:ℝ)-2 ≠ 0 := ne_of_gt hp2
      have h3 : (q:ℝ)-1 ≠ 0 := ne_of_gt hq1
      have h4 : (q:ℝ)-2 ≠ 0 := ne_of_gt hq2
      calc c1 p * c1 q * S p q
          ≤ c1 p * c1 q * ((1 / (((p:ℝ) - 2) * ((q:ℝ) - 2))) * 2 * PAS) :=
            mul_le_mul_of_nonneg_left (hS_off p hp q hqP hne) hc1nn
        _ = (2 * PAS) * (a p * a q) := by rw [hc1def, hadef]; field_simp
    have hstep2 : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (2 * PAS) * (a p * a q)
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes, (2 * PAS) * (a p * a q) := by
      apply Finset.sum_le_sum; intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p Primes)
      intro q hq _
      exact mul_nonneg h2PAS0 (mul_nonneg (hann p hp) (hann q hq))
    calc ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (2 * PAS) * (a p * a q) := hstep1
      _ ≤ ∑ p ∈ Primes, ∑ q ∈ Primes, (2 * PAS) * (a p * a q) := hstep2
      _ = (2 * PAS) * ((∑ p ∈ Primes, a p) * (∑ q ∈ Primes, a q)) := by
          rw [sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.mul_sum]
      _ ≤ (2 * PAS) * ((4 / (D:ℝ)) * (4 / (D:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ h2PAS0
          apply mul_le_mul htail_a htail_a (Finset.sum_nonneg (fun q hq => hann q hq))
            (by positivity)
  have hfinal : 2 * PAS * (4 / (D:ℝ)) + 2 * PAS * ((4 / (D:ℝ)) * (4 / (D:ℝ)))
      ≤ 40 * PAS / (D:ℝ) := by
    have hD1 : (1:ℝ) ≤ (D:ℝ) := by linarith
    have hDsq : (4 / (D:ℝ)) * (4 / (D:ℝ)) ≤ 16 / (D:ℝ) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hDpos]; nlinarith
    have h2 : 2 * PAS * ((4 / (D:ℝ)) * (4 / (D:ℝ))) ≤ 2 * PAS * (16 / (D:ℝ)) :=
      mul_le_mul_of_nonneg_left hDsq h2PAS0
    have h3 : 2 * PAS * (4 / (D:ℝ)) + 2 * PAS * (16 / (D:ℝ)) = 40 * PAS / (D:ℝ) := by ring
    linarith
  linarith [hdiag, hoff, hfinal]

/-! ### The 4-dim aggregate g-moments `T0` (opaque), `T1`, `T2` (relative) -/

private lemma mjs_T0_op (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (cg : ℝ) (_hcg0 : 0 ≤ cg)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex 4 R W', (1:ℝ) / ∏ i, (gMult (ρ i) : ℝ)) ≤ (cg * Real.log R) ^ 4 := by
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ cg * Real.log R := mjs_M0_op W' hW' hpos cg hcg D R hD hDW hR2
  have h1 := mjs_enlarge_to_PB W' R (fun _ => (1:ℝ)) (fun _ => zero_le_one)
  refine le_trans h1 ?_
  have hfac := mjs_factor_one F_R 0 (fun _ => (1:ℝ))
  simp only [one_mul] at hfac ⊢
  rw [hfac]
  calc (∑ x ∈ F_R, (1 / (gMult x : ℝ))) * (∑ x ∈ F_R, (1 / (gMult x : ℝ))) ^ 3
      = M0 ^ 4 := by rw [hM0def]; ring
    _ ≤ (cg * Real.log R) ^ 4 := pow_le_pow_left₀ hM0nn hM0le 4

private lemma mjs_T1_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex 4 R W',
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) / ∏ i, (gMult (ρ i) : ℝ))
      ≤ 256 * (Salt.Maynard.phiAtomSum R W') ^ 4 / (D:ℝ) := by
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ) with hMQdef
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ 2 * PAS := mjs_M0_rel W' hW' hpos D R hD hDW hR2
  have hMQnn : 0 ≤ MQ := Finset.sum_nonneg (fun x _ => div_nonneg (mjs_PFsum_nn _) (by positivity))
  have hMQle : MQ ≤ 8 * PAS / (D:ℝ) := mjs_MQ_rel W' hW' hpos D R hD hDW hR2
  have h1 := mjs_enlarge_to_PB W' R
    (fun ρ => ∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) (fun ρ => mjs_PFsum_nn _)
  refine le_trans h1 ?_
  have hstep2 : ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R),
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ i, (1 / (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R),
          (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
    apply Finset.sum_le_sum; intro ρ hr
    rw [Fintype.mem_piFinset] at hr
    have hρne : ∀ i, ρ i ≠ 0 := fun i => by
      have := hr i; rw [hF_R, Finset.mem_filter, Finset.mem_range] at this; exact this.2.1.ne_zero
    exact mul_le_mul_of_nonneg_right (mjs_P_subadd ρ hρne)
      (Finset.prod_nonneg (fun i _ => by positivity))
  refine le_trans hstep2 ?_
  have hdist : ∀ ρ : Fin 4 → ℕ,
      (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
    fun ρ => by rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => hdist ρ), Finset.sum_comm]
  have hi : ∀ i : Fin 4,
      (∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R),
        (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = MQ * M0 ^ 3 := by
    intro i
    rw [mjs_factor_one F_R i (fun x => ∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1)))]
    congr 1
    rw [hMQdef]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hM0cube : M0 ^ 3 ≤ (2 * PAS) ^ 3 := pow_le_pow_left₀ hM0nn hM0le 3
  have hMQM0 : MQ * M0 ^ 3 ≤ (8 * PAS / (D:ℝ)) * (2 * PAS) ^ 3 :=
    mul_le_mul hMQle hM0cube (by positivity) (by positivity)
  calc (4:ℝ) * (MQ * M0 ^ 3) ≤ 4 * ((8 * PAS / (D:ℝ)) * (2 * PAS) ^ 3) :=
        mul_le_mul_of_nonneg_left hMQM0 (by norm_num)
    _ = 256 * PAS ^ 4 / (D:ℝ) := by ring

private lemma mjs_T2_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex 4 R W',
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / ∏ i, (gMult (ρ i) : ℝ))
      ≤ 5120 * (Salt.Maynard.phiAtomSum R W') ^ 4 / (D:ℝ) := by
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set PB := Fintype.piFinset (fun _ : Fin 4 => F_R) with hPBdef
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ2 := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / (gMult x : ℝ) with hMQ2def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ 2 * PAS := mjs_M0_rel W' hW' hpos D R hD hDW hR2
  have hMQ2le : MQ2 ≤ 40 * PAS / (D:ℝ) := mjs_MQ2_rel W' hW' hpos D R hD hDW hR2
  have hQsqmom : ∀ i : Fin 4,
      (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = MQ2 * M0 ^ 3 := by
    intro i
    rw [hPBdef, mjs_factor_one F_R i (fun x => (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2)]
    congr 1
    rw [hMQ2def]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  have h1 := mjs_enlarge_to_PB W' R
    (fun ρ => (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2) (fun ρ => sq_nonneg _)
  refine le_trans h1 ?_
  rw [← hPBdef]
  have hstep2 : ∑ ρ ∈ PB,
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ i, (1 / (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ PB, (∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
              * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) := by
    apply Finset.sum_le_sum; intro ρ hr
    rw [hPBdef, Fintype.mem_piFinset] at hr
    have hρne : ∀ i, ρ i ≠ 0 := fun i => by
      have := hr i; rw [hF_R, Finset.mem_filter, Finset.mem_range] at this; exact this.2.1.ne_zero
    have hsub := mjs_P_subadd ρ hρne
    have hsq : (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
        ≤ (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) ^ 2 :=
      pow_le_pow_left₀ (mjs_PFsum_nn _) hsub 2
    have hexp : (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) ^ 2
        = ∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
              * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) := by rw [pow_two, sum_mul_sum]
    rw [hexp] at hsq
    exact mul_le_mul_of_nonneg_right hsq (Finset.prod_nonneg (fun k _ => by positivity))
  refine le_trans hstep2 ?_
  have hdist : ∀ ρ : Fin 4 → ℕ,
      (∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) := by
    intro ρ; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => hdist ρ), Finset.sum_comm]
  have hswapj : ∀ i : Fin 4,
      (∑ ρ ∈ PB, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = ∑ j, ∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
    fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i _ => hswapj i)]
  have hij : ∀ i j : Fin 4,
      (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      ≤ MQ2 * M0 ^ 3 := by
    intro i j
    have hamgm : ∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
        ≤ ∑ ρ ∈ PB, (1/2) * ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
            * ∏ k, (1 / (gMult (ρ k) : ℝ))
            + (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
              * ∏ k, (1 / (gMult (ρ k) : ℝ))) := by
      apply Finset.sum_le_sum; intro ρ _
      have hprodnn : 0 ≤ ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
        Finset.prod_nonneg (fun k _ => by positivity)
      have hamg : (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
            * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))
          ≤ (1/2) * ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
              + (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2) := by
        nlinarith [sq_nonneg ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          - (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))))]
      nlinarith [mul_le_mul_of_nonneg_right hamg hprodnn]
    refine le_trans hamgm (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hQsqmom i, hQsqmom j]; ring
  calc ∑ i, ∑ j, (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      ≤ ∑ i : Fin 4, ∑ j : Fin 4, MQ2 * M0 ^ 3 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hij i j))
    _ = 16 * (MQ2 * M0 ^ 3) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ 5120 * PAS ^ 4 / (D:ℝ) := by
        have hM0cube : M0 ^ 3 ≤ (2 * PAS) ^ 3 := pow_le_pow_left₀ hM0nn hM0le 3
        have hMM : MQ2 * M0 ^ 3 ≤ (40 * PAS / (D:ℝ)) * (2 * PAS) ^ 3 :=
          mul_le_mul hMQ2le hM0cube (by positivity) (by positivity)
        calc (16:ℝ) * (MQ2 * M0 ^ 3)
            ≤ 16 * ((40 * PAS / (D:ℝ)) * (2 * PAS) ^ 3) :=
              mul_le_mul_of_nonneg_left hMM (by norm_num)
          _ = 5120 * PAS ^ 4 / (D:ℝ) := by ring

/-! ### The 4-dim g→φ gap -/

/-- For `aᵢ ∈ [0,1]`, `1 − ∏aᵢ ≤ ∑(1 − aᵢ)`. -/
private lemma mjs_one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have hax := ha x (Finset.mem_insert_self x s)
    have has : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hih := ih has
    have hsum_nn : 0 ≤ ∑ i ∈ s, (1 - a i) :=
      Finset.sum_nonneg (fun i hi => by have := (has i hi).2; linarith)
    have hprod_nn : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg (fun i hi => (has i hi).1)
    have hprod_le1 : ∏ i ∈ s, a i ≤ 1 :=
      Finset.prod_le_one (fun i hi => (has i hi).1) (fun i hi => (has i hi).2)
    nlinarith [hax.1, hax.2, hih, hsum_nn, hprod_nn, hprod_le1]

private lemma mjs_gap_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex 4 R W',
        (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)))
      ≤ 256 * (Salt.Maynard.phiAtomSum R W') ^ 4 / (D:ℝ) := by
  classical
  -- per-coordinate: `1 − g(ρᵢ)/φ(ρᵢ) ≤ Q(ρᵢ)`
  have hcoord : ∀ x : ℕ, Squarefree x → x.Coprime W' →
      1 - (gMult x : ℝ) / (Nat.totient x : ℝ) ≤ ∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1)) := by
    intro x hxsf hxcop
    have hp3 : ∀ p ∈ x.primeFactors, 3 ≤ p := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpx := Nat.dvd_of_mem_primeFactors hp
      have hnpW : ¬ p ∣ W' := by
        intro hpW; have h1 : p ∣ 1 := hxcop ▸ Nat.dvd_gcd hpx hpW
        exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
      have := hDW p hpp hnpW; omega
    have hgcast : (gMult x : ℝ) = ∏ p ∈ x.primeFactors, ((p:ℝ) - 2) := gMult_cast hp3
    have hφcast : (Nat.totient x : ℝ) = ∏ p ∈ x.primeFactors, ((p:ℝ) - 1) :=
      totient_squarefree_cast hxsf
    have hφpos : ∀ p ∈ x.primeFactors, (0:ℝ) < (p:ℝ) - 1 := by
      intro p hp
      have hp3p : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3 p hp
      linarith
    have hratio : (gMult x : ℝ) / (Nat.totient x : ℝ)
        = ∏ p ∈ x.primeFactors, (((p:ℝ) - 2) / ((p:ℝ) - 1)) := by
      rw [hgcast, hφcast, ← Finset.prod_div_distrib]
    rw [hratio]
    have hbnd := mjs_one_sub_prod_le_sum x.primeFactors (fun p => ((p:ℝ) - 2) / ((p:ℝ) - 1))
      (fun p hp => by
        have h1 := hφpos p hp
        have h3 : (3:ℝ) ≤ (p:ℝ) := by have := hp3 p hp; exact_mod_cast this
        constructor
        · exact div_nonneg (by linarith) (by linarith)
        · rw [div_le_one (by linarith)]; linarith)
    refine le_trans hbnd (le_of_eq ?_)
    apply Finset.sum_congr rfl; intro p hp
    have h1 : ((p:ℝ) - 1) ≠ 0 := (hφpos p hp).ne'
    field_simp
    ring
  -- per-tuple: `1/∏g − 1/∏φ ≤ (∑ᵢ Q(ρᵢ))/∏g`
  have hpertuple : ∀ ρ ∈ kSieveIndex 4 R W',
      1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)
      ≤ (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) / ∏ i, (gMult (ρ i) : ℝ) := by
    intro ρ hρ
    obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff ρ).mp hρ
    have hgpos : ∀ i, (0:ℝ) < (gMult (ρ i) : ℝ) := fun i => by
      have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this
    have hφpos : ∀ i, (0:ℝ) < (Nat.totient (ρ i) : ℝ) := fun i => by
      have : 0 < ρ i := Nat.pos_of_ne_zero (hsqf i).ne_zero
      exact_mod_cast Nat.totient_pos.mpr this
    have hpg : (0:ℝ) < ∏ i, (gMult (ρ i) : ℝ) := Finset.prod_pos (fun i _ => hgpos i)
    have hpφ : (0:ℝ) < ∏ i, (Nat.totient (ρ i) : ℝ) := Finset.prod_pos (fun i _ => hφpos i)
    have hgleφ : ∀ i, (gMult (ρ i) : ℝ) ≤ (Nat.totient (ρ i) : ℝ) := fun i => by
      have := gMult_le_totient (hsqf i)
        (fun p hp => by
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hpx := Nat.dvd_of_mem_primeFactors hp
          have hnpW : ¬ p ∣ W' := by
            intro hpW; have h1 : p ∣ 1 := (hcop i) ▸ Nat.dvd_gcd hpx hpW
            exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
          have := hDW p hpp hnpW; omega)
      exact_mod_cast this
    have hprodratio : (∏ i, (gMult (ρ i) : ℝ)) / (∏ i, (Nat.totient (ρ i) : ℝ))
        = ∏ i, ((gMult (ρ i) : ℝ) / (Nat.totient (ρ i) : ℝ)) := by
      rw [← Finset.prod_div_distrib]
    have h1prod : 1 - (∏ i, (gMult (ρ i) : ℝ)) / (∏ i, (Nat.totient (ρ i) : ℝ))
        ≤ ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) := by
      rw [hprodratio]
      refine le_trans (mjs_one_sub_prod_le_sum Finset.univ
        (fun i => (gMult (ρ i) : ℝ) / (Nat.totient (ρ i) : ℝ)) (fun i _ => ?_)) ?_
      · exact ⟨div_nonneg (le_of_lt (hgpos i)) (le_of_lt (hφpos i)),
          (div_le_one (hφpos i)).mpr (hgleφ i)⟩
      · exact Finset.sum_le_sum (fun i _ =>
          hcoord (ρ i) (hsqf i) (hcop i))
    have heq : 1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)
        = (1 / ∏ i, (gMult (ρ i) : ℝ))
          * (1 - (∏ i, (gMult (ρ i) : ℝ)) / (∏ i, (Nat.totient (ρ i) : ℝ))) := by
      field_simp
    rw [heq]
    have hrhs : (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) / ∏ i, (gMult (ρ i) : ℝ)
        = (1 / ∏ i, (gMult (ρ i) : ℝ))
          * (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) := by
      rw [one_div, mul_comm, ← div_eq_mul_inv]
    rw [hrhs]
    exact mul_le_mul_of_nonneg_left h1prod (by positivity)
  -- sum + bound via `mjs_T1`-style tail (∑ᵢQ, no `P_subadd`)
  refine le_trans (Finset.sum_le_sum hpertuple) ?_
  -- `∑_{kSieveIndex4} (∑ᵢQ(ρᵢ))/∏g ≤ 256 PAS⁴/D`
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ) with hMQdef
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ 2 * PAS := mjs_M0_rel W' hW' hpos D R hD hDW hR2
  have hMQnn : 0 ≤ MQ := Finset.sum_nonneg (fun x _ => div_nonneg (mjs_PFsum_nn _) (by positivity))
  have hMQle : MQ ≤ 8 * PAS / (D:ℝ) := mjs_MQ_rel W' hW' hpos D R hD hDW hR2
  have h1 := mjs_enlarge_to_PB W' R
    (fun ρ => ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))))
    (fun ρ => Finset.sum_nonneg (fun i _ => mjs_PFsum_nn _))
  refine le_trans h1 ?_
  have hdist : ∀ ρ : Fin 4 → ℕ,
      (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
    fun ρ => by rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => hdist ρ), Finset.sum_comm]
  have hi : ∀ i : Fin 4,
      (∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R),
        (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = MQ * M0 ^ 3 := by
    intro i
    rw [mjs_factor_one F_R i (fun x => ∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1)))]
    congr 1
    rw [hMQdef]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hM0cube : M0 ^ 3 ≤ (2 * PAS) ^ 3 := pow_le_pow_left₀ hM0nn hM0le 3
  have hMQM0 : MQ * M0 ^ 3 ≤ (8 * PAS / (D:ℝ)) * (2 * PAS) ^ 3 :=
    mul_le_mul hMQle hM0cube (by positivity) (by positivity)
  calc (4:ℝ) * (MQ * M0 ^ 3) ≤ 4 * ((8 * PAS / (D:ℝ)) * (2 * PAS) ^ 3) :=
        mul_le_mul_of_nonneg_left hMQM0 (by norm_num)
    _ = 256 * PAS ^ 4 / (D:ℝ) := by ring

/-! ### The 4-dim φ pairwise-coprimality drop -/

private lemma mjs_badpair_rel4 (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (R : ℕ) (hR2 : 2 ≤ R) (i j : Fin 4) (hij : i ≠ j) (p : ℕ) (hp : Nat.Prime p) :
    ∑ r ∈ (decBox 4 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ (Salt.Maynard.phiAtomSum R W') ^ 4 / ((p:ℝ) - 1) ^ 2 := by
  classical
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set g : Fin 4 → ℕ := fun k => if k = i ∨ k = j then p else 1 with hg
  have hp2 : 2 ≤ p := hp.two_le
  have hp1R : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    linarith
  have hgpos : ∀ k, 0 < g k := by
    intro k; simp only [hg]; split
    · exact hp.pos
    · exact one_pos
  set coordSet : Fin 4 → Finset ℕ := fun k =>
    (Finset.range R).filter (fun s => Squarefree s ∧ s.Coprime W' ∧ g k ∣ s) with hcoord
  have hstepA : ∑ r ∈ (decBox 4 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
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
  set h : Fin 4 → ℝ := fun k => ∑ s ∈ coordSet k, (1 / (Nat.totient s : ℝ)) with hh
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
  have hcard : ((Finset.univ.erase i).erase j).card = 2 := by
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hprodrest : ∏ k ∈ (Finset.univ.erase i).erase j, h k ≤ PAS ^ 2 := by
    calc ∏ k ∈ (Finset.univ.erase i).erase j, h k
        ≤ ∏ _k ∈ (Finset.univ.erase i).erase j, PAS :=
          Finset.prod_le_prod (fun k _ => hhnn k) hother
      _ = PAS ^ 2 := by rw [Finset.prod_const, hcard]
  have hbnd : ∏ k, h k
      ≤ (PAS / ((p:ℝ) - 1)) * ((PAS / ((p:ℝ) - 1)) * PAS ^ 2) := by
    rw [hsplit]
    apply mul_le_mul hi_le _ (mul_nonneg (hhnn j) (Finset.prod_nonneg (fun k _ => hhnn k)))
      (div_nonneg hPAS0 hp1R.le)
    apply mul_le_mul hj_le hprodrest (Finset.prod_nonneg (fun k _ => hhnn k))
      (div_nonneg hPAS0 hp1R.le)
  have hfinal : (PAS / ((p:ℝ) - 1)) * ((PAS / ((p:ℝ) - 1)) * PAS ^ 2)
      = PAS ^ 4 / ((p:ℝ) - 1) ^ 2 := by
    have hne : (p:ℝ) - 1 ≠ 0 := ne_of_gt hp1R
    field_simp
  calc ∑ r ∈ (decBox 4 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ ∏ k, h k := hstepA
    _ ≤ _ := hbnd
    _ = PAS ^ 4 / ((p:ℝ) - 1) ^ 2 := hfinal

private lemma mjs_drop_phi4 (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ r ∈ decBox 4 R W' \ kSieveIndex 4 R W', ∏ i, (1 / (Nat.totient (r i) : ℝ)))
      ≤ 24 * (Salt.Maynard.phiAtomSum R W') ^ 4 / (D : ℝ) := by
  classical
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set Pairs : Finset (Fin 4 × Fin 4) :=
    (Finset.univ : Finset (Fin 4 × Fin 4)).filter (fun q => q.1 ≠ q.2) with hPairsdef
  set Primes : Finset ℕ :=
    (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimesdef
  set T : Finset ((Fin 4 × Fin 4) × ℕ) := Pairs ×ˢ Primes with hTdef
  set Bad : (Fin 4 × Fin 4) × ℕ → Finset (Fin 4 → ℕ) := fun x =>
    (decBox 4 R W').filter (fun r => x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2) with hBaddef
  set ind : (Fin 4 × Fin 4) × ℕ → (Fin 4 → ℕ) → ℝ := fun x r =>
    if x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2 then ∏ i, (1 / (Nat.totient (r i) : ℝ)) else 0 with hinddef
  have hindnn : ∀ x r, 0 ≤ ind x r := by
    intro x r; simp only [hinddef]; split_ifs
    · exact Finset.prod_nonneg (fun i _ => by positivity)
    · exact le_refl 0
  have hcover : (∑ r ∈ decBox 4 R W' \ kSieveIndex 4 R W', ∏ i, (1 / (Nat.totient (r i) : ℝ)))
      ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))) := by
    have hpt : ∀ r ∈ decBox 4 R W' \ kSieveIndex 4 R W',
        (∏ i, (1 / (Nat.totient (r i) : ℝ))) ≤ ∑ x ∈ T, ind x r := by
      intro r hr
      obtain ⟨hrdec, hrnk⟩ := Finset.mem_sdiff.mp hr
      have hrdec' := hrdec
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hrdec'
      obtain ⟨hlt, hsqf, hcop, hprod⟩ := hrdec'
      rw [mem_kSieveIndex_iff] at hrnk
      have hpair_neg : ¬ (∀ i j : Fin 4, i ≠ j → Nat.Coprime (r i) (r j)) :=
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
    calc ∑ r ∈ decBox 4 R W' \ kSieveIndex 4 R W', (∏ i, (1 / (Nat.totient (r i) : ℝ)))
        ≤ ∑ r ∈ decBox 4 R W' \ kSieveIndex 4 R W', ∑ x ∈ T, ind x r :=
          Finset.sum_le_sum hpt
      _ = ∑ x ∈ T, ∑ r ∈ decBox 4 R W' \ kSieveIndex 4 R W', ind x r := Finset.sum_comm
      _ ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))) := by
          apply Finset.sum_le_sum
          intro x _
          rw [hinddef, ← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · rw [hBaddef]
            exact Finset.filter_subset_filter _ Finset.sdiff_subset
          · intro r _ _; exact Finset.prod_nonneg (fun i _ => by positivity)
  have hPairsCard : Pairs.card = 12 := by rw [hPairsdef]; decide
  have hfinal : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))))
      ≤ 24 * PAS ^ 4 / (D : ℝ) := by
    have h1 : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))))
        ≤ ∑ x ∈ T, PAS ^ 4 / ((x.2 : ℝ) - 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [hTdef, Finset.mem_product] at hx
      obtain ⟨hq, hpx⟩ := hx
      rw [hPairsdef, Finset.mem_filter] at hq
      rw [hPrimesdef, Finset.mem_filter] at hpx
      have hbp := mjs_badpair_rel4 W' hW' hpos R hR2 x.1.1 x.1.2 hq.2 x.2 hpx.2.1
      rw [← hPASdef] at hbp
      rw [hBaddef]; exact hbp
    refine le_trans h1 ?_
    rw [hTdef, Finset.sum_product]
    have hPAS4 : 0 ≤ PAS ^ 4 := pow_nonneg hPAS0 4
    have hinner : ∀ q ∈ Pairs,
        (∑ p ∈ Primes, PAS ^ 4 / (((q, p).2 : ℝ) - 1) ^ 2) ≤ PAS ^ 4 * (2 / (D : ℝ)) := by
      intro q _
      have heq : (∑ p ∈ Primes, PAS ^ 4 / ((p : ℝ) - 1) ^ 2)
          = PAS ^ 4 * ∑ p ∈ Primes, 1 / ((p : ℝ) - 1) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
      simp only
      rw [heq]
      exact mul_le_mul_of_nonneg_left (prime_tail D R hD) hPAS4
    calc (∑ q ∈ Pairs, ∑ p ∈ Primes, PAS ^ 4 / (((q, p).2 : ℝ) - 1) ^ 2)
        ≤ ∑ q ∈ Pairs, PAS ^ 4 * (2 / (D : ℝ)) := Finset.sum_le_sum hinner
      _ = (Pairs.card : ℝ) * (PAS ^ 4 * (2 / (D : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = 24 * PAS ^ 4 / (D : ℝ) := by rw [hPairsCard]; push_cast; ring
  exact le_trans hcover hfinal

/-! ## `mv_J_main_split` — the relativized 4-dim g-weighted main moment -/

private lemma mv_J_main_split (F : Poly) (m : Fin 5) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
              eval (contractAt m F) (fun i => Real.log (r (m.succAbove i)) / Real.log R) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 4
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 4 / Real.log R
          + A * (1 + Salt.Maynard.phiAtomSum R W') ^ 4 / D := by
  classical
  set Q : BPoly 4 := sq (contractAt m F) with hQdef
  set cF : ℝ := ((contractAt m F).map (fun mo => |(mo.2.2 : ℝ)|)).sum with hcFdef
  have hcF0 : 0 ≤ cF := by
    rw [hcFdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨mo, _, rfl⟩ := hx; exact abs_nonneg _
  refine ⟨280 * cF ^ 2, by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  -- per-monomial `mv_monomial` constants (φ workhorse, n = 4)
  set Cfun : ((Fin 4 → ℕ) × ℕ × ℚ) → ℝ :=
    fun mo => Classical.choose (mv_monomial W' hW' hpos hUpper 4 mo.1 mo.2.1) with hCfundef
  have hCfunspec : ∀ mo, 0 ≤ Cfun mo ∧ ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ ρ ∈ decBox 4 z W',
            (∏ i, (Real.log (ρ i) / Real.log R) ^ (mo.1 i))
              * ((Real.log z - ∑ i, Real.log (ρ i)) / Real.log R) ^ (mo.2.1)
              / ∏ i, (Nat.totient (ρ i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 4 * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ (4 + mo.2.1 + ∑ i, mo.1 i)|
      ≤ Cfun mo * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (4 - 1) :=
    fun mo => Classical.choose_spec (mv_monomial W' hW' hpos hUpper 4 mo.1 mo.2.1)
  have hCfun0 : ∀ mo, 0 ≤ Cfun mo := fun mo => (hCfunspec mo).1
  set Cmain : ℝ := (Q.map (fun mo => |(mo.2.2 : ℝ)| * Cfun mo)).sum with hCmaindef
  have hCmain0 : 0 ≤ Cmain := by
    rw [hCmaindef]; apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx; obtain ⟨mo, _, rfl⟩ := hx
    exact mul_nonneg (abs_nonneg _) (hCfun0 mo)
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  refine ⟨Cmain / κ, div_nonneg hCmain0 hκpos.le, ?_⟩
  intro R hlogR
  have hRpos : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · rw [h] at hlogR; simp at hlogR; linarith
    · exact h
  have hR2 : 2 ≤ R := by
    have hRr : (0:ℝ) < (R:ℝ) := by exact_mod_cast hRpos
    have h2e : (2:ℝ) ≤ Real.exp (Real.log R) := by
      calc (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
        _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hlogR
    rw [Real.exp_log hRr] at h2e; exact_mod_cast h2e
  set L : ℝ := Real.log R with hLdef
  set X : ℝ := (W'.totient : ℝ) / W' * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXκL : X = κ * L := by rw [hXdef, hκdef, hLdef]
  have hX0 : 0 ≤ X := by rw [hXκL]; exact mul_nonneg hκpos.le hLpos.le
  have hκL1X : κ * L ≤ 1 + X := by rw [← hXκL]; linarith
  have hDpos : (0:ℝ) < (D : ℝ) := by
    have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    linarith
  -- the reindexed pieces
  set Ev' : (Fin 4 → ℕ) → ℝ := fun ρ => eval (contractAt m F) (fun i => Real.log (ρ i) / L)
    with hEv'def
  have hEvbd : ∀ ρ ∈ decBox 4 R W', |Ev' ρ| ≤ cF := by
    intro ρ hr
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
    obtain ⟨hlt, hsqf, hcop, hprod⟩ := hr
    have hr1 : ∀ i, 1 ≤ ρ i := fun i => Nat.pos_of_ne_zero (hsqf i).ne_zero
    rw [hEv'def, hcFdef]
    apply mjs_eval_bpoly_bound
    · intro i; exact div_nonneg (Real.log_nonneg (by exact_mod_cast hr1 i)) hLpos.le
    · intro i; rw [div_le_one hLpos, hLdef]
      exact Real.log_le_log (by exact_mod_cast hr1 i) (by exact_mod_cast (le_of_lt (hlt i)))
    · rw [← Finset.sum_div, div_le_one hLpos]
      have hSL : ∑ i, Real.log (ρ i) = Real.log ((∏ i, ρ i : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
        exact (Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (by have := hr1 i; omega))).symm
      rw [hSL, hLdef]
      exact Real.log_le_log (by exact_mod_cast Finset.prod_pos (fun i _ => hr1 i))
        (by exact_mod_cast hprod.le)
  -- reindex the LHS to `∑_{kSieveIndex4} Ev'² / ∏g`
  have hreindex : (∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
        eval (contractAt m F) (fun i => Real.log (r (m.succAbove i)) / L) ^ 2
          / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
      = ∑ ρ ∈ kSieveIndex 4 R W', Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) := by
    rw [← sum_filt_removeNth R W' m
      (fun ρ => Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ))]
    apply Finset.sum_congr rfl
    intro r _
    rw [mjs_erase_prod_removeNth m (fun i => (gMult (r i) : ℝ))]
    simp only [Fin.removeNth_apply, hEv'def]
  rw [hreindex]
  -- the three brackets
  set T_kg : ℝ := ∑ ρ ∈ kSieveIndex 4 R W', Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) with hTkg
  set T_kφ : ℝ := ∑ ρ ∈ kSieveIndex 4 R W', Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) with hTkφ
  set T_dφ : ℝ := ∑ ρ ∈ decBox 4 R W', Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) with hTdφ
  -- bracket 1: gap `T_kg − T_kφ ≤ 256 cF² PAS⁴/D`
  have hgap : T_kg - T_kφ ≤ 256 * cF ^ 2 * PAS ^ 4 / (D : ℝ) := by
    have hkSieve_sub : kSieveIndex 4 R W' ⊆ decBox 4 R W' := by
      intro r hr
      obtain ⟨hsqf, _, hcop, hprod⟩ := (mem_kSieveIndex_iff r).mp hr
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
    have hterm : ∀ ρ ∈ kSieveIndex 4 R W',
        Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) - Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ)
        ≤ cF ^ 2 * (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)) := by
      intro ρ hρ
      obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff ρ).mp hρ
      have hgpos : (0:ℝ) < ∏ i, (gMult (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
        have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this)
      have hφpos : (0:ℝ) < ∏ i, (Nat.totient (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
        have : 0 < ρ i := Nat.pos_of_ne_zero (hsqf i).ne_zero
        exact_mod_cast Nat.totient_pos.mpr this)
      have hgleφ2 : ∏ i, (gMult (ρ i) : ℝ) ≤ ∏ i, (Nat.totient (ρ i) : ℝ) := by
        apply Finset.prod_le_prod (fun i _ => by positivity)
        intro i _
        have := gMult_le_totient (hsqf i)
          (fun q hq => by
            have hqp := Nat.prime_of_mem_primeFactors hq
            have hqx := Nat.dvd_of_mem_primeFactors hq
            have hnpW : ¬ q ∣ W' := by
              intro hqW; have h1 : q ∣ 1 := (hcop i) ▸ Nat.dvd_gcd hqx hqW
              exact hqp.one_lt.ne' (Nat.dvd_one.mp h1)
            have := hDW q hqp hnpW; omega)
        exact_mod_cast this
      have hgapnn : 0 ≤ 1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ) := by
        rw [sub_nonneg]; exact one_div_le_one_div_of_le hgpos hgleφ2
      have hEv2 : Ev' ρ ^ 2 ≤ cF ^ 2 := by
        have := hEvbd ρ (hkSieve_sub hρ)
        nlinarith [abs_nonneg (Ev' ρ), sq_abs (Ev' ρ)]
      have hfac : Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) - Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ)
          = Ev' ρ ^ 2 * (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)) := by
        ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_right hEv2 hgapnn
    have hsum : T_kg - T_kφ ≤ cF ^ 2 * (∑ ρ ∈ kSieveIndex 4 R W',
        (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ))) := by
      rw [hTkg, hTkφ, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    refine le_trans hsum ?_
    have hgr := mjs_gap_rel W' hW' hpos D R hD hDW hR2
    rw [← hPASdef] at hgr
    calc cF ^ 2 * (∑ ρ ∈ kSieveIndex 4 R W',
          (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)))
        ≤ cF ^ 2 * (256 * PAS ^ 4 / (D : ℝ)) := mul_le_mul_of_nonneg_left hgr (by positivity)
      _ = 256 * cF ^ 2 * PAS ^ 4 / (D : ℝ) := by ring
  -- bracket 2: drop `T_kφ − T_dφ`, `|·| ≤ 24 cF² PAS⁴/D`
  have hdrop : |T_kφ - T_dφ| ≤ 24 * cF ^ 2 * PAS ^ 4 / (D : ℝ) := by
    have hkSieve_sub : kSieveIndex 4 R W' ⊆ decBox 4 R W' := by
      intro r hr
      obtain ⟨hsqf, _, hcop, hprod⟩ := (mem_kSieveIndex_iff r).mp hr
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
    have hsdiff : T_dφ - T_kφ = ∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
        Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) := by
      have h := Finset.sum_sdiff (f := fun ρ => Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ))
        hkSieve_sub
      rw [hTdφ, hTkφ]; linarith [h]
    have hbdd : ∀ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
        Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) ≤ cF ^ 2 * ∏ i, (1 / (Nat.totient (ρ i) : ℝ)) := by
      intro ρ hρ
      have hρd := (Finset.mem_sdiff.mp hρ).1
      have hmem := hρd
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hmem
      obtain ⟨hlt, hsqf, hcop, hprod⟩ := hmem
      have hφpos : (0:ℝ) < ∏ i, (Nat.totient (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
        have : 0 < ρ i := Nat.pos_of_ne_zero (hsqf i).ne_zero
        exact_mod_cast Nat.totient_pos.mpr this)
      have hEv2 : Ev' ρ ^ 2 ≤ cF ^ 2 := by
        have := hEvbd ρ hρd
        nlinarith [abs_nonneg (Ev' ρ), sq_abs (Ev' ρ)]
      have hprodinv : (∏ i, (1 / (Nat.totient (ρ i) : ℝ))) = 1 / ∏ i, (Nat.totient (ρ i) : ℝ) := by
        rw [Finset.prod_div_distrib, Finset.prod_const_one]
      rw [hprodinv, mul_one_div, div_le_div_iff₀ hφpos hφpos]
      nlinarith [hEv2, hφpos]
    have hnn : 0 ≤ ∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
        Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) :=
      Finset.sum_nonneg (fun ρ _ => by positivity)
    have hle : (∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W', Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ))
        ≤ 24 * cF ^ 2 * PAS ^ 4 / (D : ℝ) := by
      calc (∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W', Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ))
          ≤ ∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
              cF ^ 2 * ∏ i, (1 / (Nat.totient (ρ i) : ℝ)) := Finset.sum_le_sum hbdd
        _ = cF ^ 2 * ∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
              ∏ i, (1 / (Nat.totient (ρ i) : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ cF ^ 2 * (24 * PAS ^ 4 / (D : ℝ)) := by
            have hdp := mjs_drop_phi4 W' hW' hpos D R hD hDW hR2
            rw [← hPASdef] at hdp
            exact mul_le_mul_of_nonneg_left hdp (by positivity)
        _ = 24 * cF ^ 2 * PAS ^ 4 / (D : ℝ) := by ring
    rw [abs_sub_comm, abs_of_nonneg (by rw [hsdiff]; exact hnn)]
    rw [hsdiff]; exact hle
  -- bracket 3: `T_dφ − X⁴J`, `|·| ≤ Cmain (1+X)³`
  have hmain : |T_dφ - X ^ 4 * ((simplexInt Q : ℚ) : ℝ)| ≤ Cmain * (1 + X) ^ 3 := by
    set MSD : ((Fin 4 → ℕ) × ℕ × ℚ) → ℝ := fun mo =>
      ∑ ρ ∈ decBox 4 R W',
        (∏ i, (Real.log (ρ i) / L) ^ (mo.1 i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1)
          / ∏ i, (Nat.totient (ρ i) : ℝ) with hMSDdef
    have hTdφexp : T_dφ = (Q.map (fun mo => (mo.2.2 : ℝ) * MSD mo)).sum := by
      have hbudget : ∀ ρ : Fin 4 → ℕ,
          (1 : ℝ) - ∑ i, Real.log (ρ i) / L = (L - ∑ i, Real.log (ρ i)) / L := by
        intro ρ; rw [← Finset.sum_div, sub_div, div_self hLne]
      have hper : ∀ ρ ∈ decBox 4 R W',
          Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ)
            = (Q.map (fun mo => (mo.2.2 : ℝ) * ((∏ i, (Real.log (ρ i) / L) ^ (mo.1 i))
                * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1)
                / ∏ i, (Nat.totient (ρ i) : ℝ)))).sum := by
        intro ρ _
        rw [hEv'def, ← eval_sq (contractAt m F), ← hQdef]
        have hev : eval Q (fun i => Real.log (ρ i) / L)
            = (Q.map (fun mo => (mo.2.2 : ℝ) * (∏ i, (Real.log (ρ i) / L) ^ (mo.1 i))
                * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1))).sum := by
          unfold eval
          refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
          dsimp only; rw [hbudget ρ]
        rw [hev, ic_list_sum_div]
        refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
        ring
      rw [hTdφ, Finset.sum_congr rfl hper, ic_sum_finset_list_sum]
      refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
      rw [hMSDdef, ← Finset.mul_sum]
    have hMainSum : X ^ 4 * ((simplexInt Q : ℚ) : ℝ)
        = (Q.map (fun mo => X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)))).sum := by
      have hcast : ((simplexInt Q : ℚ) : ℝ)
          = (Q.map (fun mo => (mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))).sum := by
        rw [simplexInt, Rat.cast_list_sum, List.map_map]
        refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
        simp only [Function.comp_apply]; push_cast; ring
      rw [hcast, ← List.sum_map_mul_left]
    have hStage3 : ∀ mo : (Fin 4 → ℕ) × ℕ × ℚ,
        |MSD mo - X ^ 4 * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)| ≤ Cfun mo * (1 + X) ^ 3 := by
      intro mo
      have hspec := (hCfunspec mo).2 R R hR2 le_rfl hlogR
      rw [← hXdef, ← hLdef, div_self hLne, one_pow, mul_one] at hspec
      exact hspec
    have hPer : ∀ mo ∈ Q,
        |(mo.2.2 : ℝ) * MSD mo - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))|
        ≤ |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ 3 := by
      intro mo _
      have hfac : (mo.2.2 : ℝ) * MSD mo - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))
          = (mo.2.2 : ℝ) * (MSD mo - X ^ 4 * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)) := by ring
      rw [hfac, abs_mul]
      calc |(mo.2.2 : ℝ)| * |MSD mo - X ^ 4 * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)|
          ≤ |(mo.2.2 : ℝ)| * (Cfun mo * (1 + X) ^ 3) :=
            mul_le_mul_of_nonneg_left (hStage3 mo) (abs_nonneg _)
        _ = |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ 3 := by ring
    rw [hTdφexp, hMainSum, ic_list_sum_map_sub]
    calc |(Q.map (fun mo => (mo.2.2 : ℝ) * MSD mo
            - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)))).sum|
        ≤ (Q.map (fun mo => |(mo.2.2 : ℝ) * MSD mo
            - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))|)).sum :=
          ic_list_abs_sum_le _ _
      _ ≤ (Q.map (fun mo => |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ 3)).sum :=
          ic_list_sum_le _ _ _ hPer
      _ = Cmain * (1 + X) ^ 3 := by
          rw [hCmaindef,
            List.sum_map_mul_right Q (fun mo => |(mo.2.2 : ℝ)| * Cfun mo) ((1 + X) ^ 3)]
  -- combine the three brackets and absorb
  have htri : |T_kg - X ^ 4 * ((simplexInt Q : ℚ) : ℝ)|
      ≤ (256 * cF ^ 2 * PAS ^ 4 / (D : ℝ)) + (24 * cF ^ 2 * PAS ^ 4 / (D : ℝ))
        + Cmain * (1 + X) ^ 3 := by
    calc |T_kg - X ^ 4 * ((simplexInt Q : ℚ) : ℝ)|
        ≤ |T_kg - T_kφ| + |T_kφ - T_dφ| + |T_dφ - X ^ 4 * ((simplexInt Q : ℚ) : ℝ)| := by
          have h1 := abs_sub_le (T_kg) (T_kφ) (X ^ 4 * ((simplexInt Q : ℚ) : ℝ))
          have h2 := abs_sub_le (T_kφ) (T_dφ) (X ^ 4 * ((simplexInt Q : ℚ) : ℝ))
          linarith [h1, h2]
      _ ≤ (256 * cF ^ 2 * PAS ^ 4 / (D : ℝ)) + (24 * cF ^ 2 * PAS ^ 4 / (D : ℝ))
          + Cmain * (1 + X) ^ 3 := by
          have hg2 : |T_kg - T_kφ| ≤ 256 * cF ^ 2 * PAS ^ 4 / (D : ℝ) := by
            rw [abs_of_nonneg]
            · exact hgap
            · -- `T_kg ≥ T_kφ` since `1/∏g ≥ 1/∏φ`
              rw [hTkg, hTkφ, ← Finset.sum_sub_distrib]
              apply Finset.sum_nonneg
              intro ρ hρ
              obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff ρ).mp hρ
              have hgpos : (0:ℝ) < ∏ i, (gMult (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
                have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this)
              have hφpos : (0:ℝ) < ∏ i, (Nat.totient (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
                have : 0 < ρ i := Nat.pos_of_ne_zero (hsqf i).ne_zero
                exact_mod_cast Nat.totient_pos.mpr this)
              have hgleφ2 : ∏ i, (gMult (ρ i) : ℝ) ≤ ∏ i, (Nat.totient (ρ i) : ℝ) := by
                apply Finset.prod_le_prod (fun i _ => by positivity)
                intro i _
                have := gMult_le_totient (hsqf i)
                  (fun q hq => by
                    have hqp := Nat.prime_of_mem_primeFactors hq
                    have hqx := Nat.dvd_of_mem_primeFactors hq
                    have hnpW : ¬ q ∣ W' := by
                      intro hqW; have h1 : q ∣ 1 := (hcop i) ▸ Nat.dvd_gcd hqx hqW
                      exact hqp.one_lt.ne' (Nat.dvd_one.mp h1)
                    have := hDW q hqp hnpW; omega)
                exact_mod_cast this
              have hEvnn : 0 ≤ Ev' ρ ^ 2 := sq_nonneg _
              have : Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ)
                  ≤ Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) :=
                div_le_div_of_nonneg_left hEvnn hgpos hgleφ2
              linarith
          linarith [hg2, hdrop]
  refine le_trans htri ?_
  -- absorb: `Cmain(1+X)³ → (Cmain/κ)(1+X)⁴/L`; `(256+24)cF²PAS⁴/D → 280cF²(1+PAS)⁴/D`
  have hPAS15 : PAS ^ 4 ≤ (1 + PAS) ^ 4 := pow_le_pow_left₀ hPAS0 (by linarith) 4
  have hDside : (256 * cF ^ 2 * PAS ^ 4 / (D : ℝ)) + (24 * cF ^ 2 * PAS ^ 4 / (D : ℝ))
      ≤ 280 * cF ^ 2 * (1 + PAS) ^ 4 / (D : ℝ) := by
    have he : (256 * cF ^ 2 * PAS ^ 4 / (D : ℝ)) + (24 * cF ^ 2 * PAS ^ 4 / (D : ℝ))
        = 280 * cF ^ 2 / (D : ℝ) * PAS ^ 4 := by ring
    rw [he]
    calc 280 * cF ^ 2 / (D : ℝ) * PAS ^ 4
        ≤ 280 * cF ^ 2 / (D : ℝ) * (1 + PAS) ^ 4 :=
          mul_le_mul_of_nonneg_left hPAS15 (div_nonneg (by positivity) hDpos.le)
      _ = 280 * cF ^ 2 * (1 + PAS) ^ 4 / (D : ℝ) := by ring
  have hLside : Cmain * (1 + X) ^ 3 ≤ Cmain / κ * (1 + X) ^ 4 / L := by
    have h3 : (1 + X) ^ 3 ≤ (1 + X) ^ 4 / (κ * L) := by
      rw [le_div_iff₀ (mul_pos hκpos hLpos)]
      calc (1 + X) ^ 3 * (κ * L) ≤ (1 + X) ^ 3 * (1 + X) := by
            apply mul_le_mul_of_nonneg_left hκL1X (by positivity)
        _ = (1 + X) ^ 4 := by ring
    have e2 : Cmain / κ * (1 + X) ^ 4 / L = Cmain * ((1 + X) ^ 4 / (κ * L)) := by
      have hκne : κ ≠ 0 := ne_of_gt hκpos
      field_simp
    rw [e2]; exact mul_le_mul_of_nonneg_left h3 hCmain0
  linarith [hDside, hLside]

/-! ## `mv_J_split` (frozen deliverable, mixed-power `1/D` bucket) -/

private lemma mjs_absorb (κ L : ℝ) (hκ : 0 < κ) (hL : 1 ≤ L) :
    κ * L * L ^ 4 ≤ 1 / κ ^ 5 * (1 + κ * L) ^ 6 * (1 / L)
    ∧ L ^ 4 ≤ 1 / κ ^ 6 * (1 + κ * L) ^ 6 * (1 / L) := by
  have hLpos : 0 < L := by linarith
  have hbase : (κ * L) ^ 6 ≤ (1 + κ * L) ^ 6 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 6
  constructor
  · rw [show 1 / κ ^ 5 * (1 + κ * L) ^ 6 * (1 / L) = (1 + κ * L) ^ 6 / (κ ^ 5 * L) by field_simp,
      le_div_iff₀ (by positivity)]
    calc κ * L * L ^ 4 * (κ ^ 5 * L) = (κ * L) ^ 6 := by ring
      _ ≤ (1 + κ * L) ^ 6 := hbase
  · rw [show 1 / κ ^ 6 * (1 + κ * L) ^ 6 * (1 / L) = (1 + κ * L) ^ 6 / (κ ^ 6 * L) by field_simp,
      le_div_iff₀ (by positivity)]
    calc L ^ 4 * (κ ^ 6 * L) = κ ^ 6 * L ^ 5 := by ring
      _ ≤ κ ^ 6 * L ^ 6 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc L ^ 5 = L ^ 5 * 1 := by ring
            _ ≤ L ^ 5 * L := by apply mul_le_mul_of_nonneg_left hL (by positivity)
            _ = L ^ 6 := by ring
      _ = (κ * L) ^ 6 := by ring
      _ ≤ (1 + κ * L) ^ 6 := hbase

set_option maxHeartbeats 2000000 in
-- The final square-expand assembly (inner_contract_rel substitution, the three
-- relativized swap sums, the mixed-base absorptions) elaborates in one block and
-- exceeds the default heartbeat budget (a resource limit, not an axiom).
theorem mv_J_split (F : Poly) (m : Fin 5) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
              (∑ u ∈ Finset.range R,
                  yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
          + A * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D := by
  classical
  obtain ⟨Amain, hAmain0, hAmain⟩ := mv_J_main_split F m
  obtain ⟨Aic, hAic0, hAic⟩ := inner_contract_rel F m
  set cF : ℝ := ((contractAt m F).map (fun mo => |(mo.2.2 : ℝ)|)).sum with hcFdef
  have hcF0 : 0 ≤ cF := by
    rw [hcFdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨mo, _, rfl⟩ := hx; exact abs_nonneg _
  refine ⟨Amain + 512 * cF * Aic + 10240 * Aic ^ 2, by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  obtain ⟨cg, hcg0, hcg⟩ := marked_sqf_g W' hW' hpos 0
  obtain ⟨cmain, hcmain0, hcmain⟩ := hAmain W' D hW' hpos hUpper hD hDW
  obtain ⟨cic, hcic0, hcic⟩ := hAic W' D hW' hpos hUpper hD hDW
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  have hκle1 : κ ≤ 1 := by
    rw [hκdef, div_le_one (by exact_mod_cast hpos)]; exact_mod_cast Nat.totient_le W'
  refine ⟨cmain + 2 * cF * cic * cg ^ 4 / κ ^ 5 + 2 * cic ^ 2 * cg ^ 4 / κ ^ 6, by positivity, ?_⟩
  intro R hlogR
  have hRpos : 0 < R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · rw [h] at hlogR; simp at hlogR; linarith
    · exact h
  have hR2 : 2 ≤ R := by
    have hRr : (0:ℝ) < (R:ℝ) := by exact_mod_cast hRpos
    have h2e : (2:ℝ) ≤ Real.exp (Real.log R) := by
      calc (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
        _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hlogR
    rw [Real.exp_log hRr] at h2e; exact_mod_cast h2e
  set L : ℝ := Real.log R with hLdef
  set X : ℝ := κ * L with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hDpos : (0:ℝ) < (D:ℝ) := by
    have : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    linarith
  have hclogR : 0 ≤ cg * L := mul_nonneg hcg0 hLpos.le
  set Y : ℝ := 1 + X + PAS with hYdef
  have hY1 : 1 ≤ Y := by rw [hYdef]; linarith
  have hXY : X ≤ Y := by rw [hYdef]; linarith
  have hPASY : PAS ≤ Y := by rw [hYdef]; linarith
  have h1PASY : 1 + PAS ≤ Y := by rw [hYdef]; linarith
  have hY0 : 0 ≤ Y := by linarith
  -- abbreviations
  set filt := (kSieveIndex 5 R W').filter (fun r => r m = 1) with hfiltdef
  set Denom : (Fin 5 → ℕ) → ℝ := fun r => ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)
    with hDenomdef
  set Inn : (Fin 5 → ℕ) → ℝ := fun r => ∑ u ∈ Finset.range R,
      yF R W' F (Function.update r m u) / (Nat.totient u : ℝ) with hInndef
  set Ev : (Fin 5 → ℕ) → ℝ := fun r =>
      eval (contractAt m F) (fun i => Real.log (r (m.succAbove i)) / L) with hEvdef
  set Pr : (Fin 5 → ℕ) → ℝ := fun r =>
      ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p:ℝ) - 1)) with hPrdef
  have hX_eq : (W'.totient : ℝ) / W' * Real.log R = X := by rw [hXdef, hκdef, hLdef]
  -- Denom positive on filt
  have hDenompos : ∀ r ∈ filt, 0 < Denom r := by
    intro r hr; rw [hfiltdef, Finset.mem_filter, mem_kSieveIndex_iff] at hr
    obtain ⟨⟨hsqf, _, hcop, _⟩, _⟩ := hr
    rw [hDenomdef]; apply Finset.prod_pos; intro i _
    have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this
  have hprodeq : ∀ r ∈ filt, (∏ i, r i) = ∏ i : Fin 4, r (m.succAbove i) := by
    intro r hr; rw [hfiltdef, Finset.mem_filter] at hr
    rw [Fin.prod_univ_succAbove (fun j => r j) m, hr.2, one_mul]
  -- |Ev| ≤ cF on filt
  have hEvbd : ∀ r ∈ filt, |Ev r| ≤ cF := by
    intro r hr
    have hrmem := hr
    rw [hfiltdef, Finset.mem_filter] at hr
    have hrk := hr.1
    rw [hEvdef, hcFdef]
    apply mjs_eval_bpoly_bound
    · intro i; apply div_nonneg (Real.log_nonneg _) hLpos.le
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (kSieveIndex_coord_pos hrk (m.succAbove i)).ne'
    · intro i; rw [div_le_one hLpos, hLdef]
      exact Real.log_le_log (by exact_mod_cast kSieveIndex_coord_pos hrk (m.succAbove i))
        (by exact_mod_cast (kSieveIndex_coord_lt hrk (m.succAbove i)).le)
    · have hpe := hprodeq r hrmem
      have hprodlt : (∏ i, r i) < R := ((mem_kSieveIndex_iff r).mp hrk).2.2.2
      have hlogsum : (∑ i : Fin 4, Real.log (r (m.succAbove i))) = Real.log ((∏ i, r i : ℕ):ℝ) := by
        have h1 : ((∏ i, r i : ℕ):ℝ) = ∏ i : Fin 4, ((r (m.succAbove i) : ℕ):ℝ) := by
          rw [hpe, Nat.cast_prod]
        rw [h1, Real.log_prod
          (fun i _ => by exact_mod_cast (kSieveIndex_coord_pos hrk (m.succAbove i)).ne')]
      rw [← Finset.sum_div, div_le_one hLpos, hlogsum, hLdef]
      exact Real.log_le_log
        (by exact_mod_cast Finset.prod_pos (fun i _ => kSieveIndex_coord_pos hrk i))
        (by exact_mod_cast hprodlt.le)
  -- inner_contract_rel per r
  have hInnbd : ∀ r ∈ filt, |Inn r - X * Ev r| ≤ cic + Aic * PAS * Pr r := by
    intro r hr
    rw [hfiltdef, Finset.mem_filter] at hr
    have := hcic R hlogR r hr.1 hr.2
    rw [hX_eq] at this
    exact this
  -- the reindex helper
  have hreindex_gen : ∀ (gn : ℕ → ℝ),
      (∑ r ∈ filt, gn (∏ i, r i) / Denom r)
        = ∑ ρ ∈ kSieveIndex 4 R W', gn (∏ i, ρ i) / ∏ i, (gMult (ρ i) : ℝ) := by
    intro gn
    rw [← sum_filt_removeNth R W' m (fun ρ => gn (∏ i, ρ i) / ∏ i, (gMult (ρ i) : ℝ))]
    rw [hfiltdef]
    apply Finset.sum_congr rfl
    intro r hr
    have hrf : r ∈ filt := by rw [hfiltdef]; exact hr
    simp only [hDenomdef, Fin.removeNth_apply]
    rw [mjs_erase_prod_removeNth m (fun i => (gMult (r i):ℝ)), hprodeq r hrf]
  -- S0, S1, S2 bounds
  have hS0le : (∑ r ∈ filt, (1:ℝ) / Denom r) ≤ (cg * L) ^ 4 := by
    have key : (∑ r ∈ filt, (1:ℝ) / Denom r)
        = ∑ ρ ∈ kSieveIndex 4 R W', (1:ℝ) / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun _ => 1)
    rw [key]; exact mjs_T0_op W' hW' hpos cg hcg0 hcg D R hD hDW hR2
  have hS1le : (∑ r ∈ filt, Pr r / Denom r) ≤ 256 * PAS ^ 4 / (D:ℝ) := by
    have key : (∑ r ∈ filt, Pr r / Denom r)
        = ∑ ρ ∈ kSieveIndex 4 R W',
            (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun N => ∑ p ∈ N.primeFactors, (1 / ((p:ℝ) - 1)))
    rw [key, hPASdef]; exact mjs_T1_rel W' hW' hpos D R hD hDW hR2
  have hS2le : (∑ r ∈ filt, (Pr r) ^ 2 / Denom r) ≤ 5120 * PAS ^ 4 / (D:ℝ) := by
    have key : (∑ r ∈ filt, (Pr r) ^ 2 / Denom r)
        = ∑ ρ ∈ kSieveIndex 4 R W',
            (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun N => (∑ p ∈ N.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2)
    rw [key, hPASdef]; exact mjs_T2_rel W' hW' hpos D R hD hDW hR2
  -- === main part via mv_J_main_split ===
  have hEvSum : |(∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
        - X ^ 4 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ cmain * (1 + X) ^ 4 / L + Amain * (1 + PAS) ^ 4 / (D:ℝ) := by
    have h := hcmain R hlogR
    rw [hX_eq, ← hLdef, ← hPASdef] at h
    exact h
  have hmainpart : |X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
        - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ cmain * (1 + X) ^ 6 / L + Amain * Y ^ 6 / (D:ℝ) := by
    have hfac : X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
          - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)
        = X ^ 2 * ((∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
          - X ^ 4 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ X ^ 2)]
    -- X² · (1/L-bound + 1/D-bound)
    have hLpart : X ^ 2 * (cmain * (1 + X) ^ 4 / L) ≤ cmain * (1 + X) ^ 6 / L := by
      have hXsq : X ^ 2 ≤ (1 + X) ^ 2 := pow_le_pow_left₀ hX0 (by linarith) 2
      have e : X ^ 2 * (cmain * (1 + X) ^ 4 / L) = cmain * (X ^ 2 * (1 + X) ^ 4) / L := by ring
      have e2 : cmain * (1 + X) ^ 6 / L = cmain * ((1 + X) ^ 2 * (1 + X) ^ 4) / L := by ring
      rw [e, e2]
      refine div_le_div_of_nonneg_right ?_ hLpos.le
      refine mul_le_mul_of_nonneg_left ?_ hcmain0
      exact mul_le_mul_of_nonneg_right hXsq (by positivity)
    have hDpart : X ^ 2 * (Amain * (1 + PAS) ^ 4 / (D:ℝ)) ≤ Amain * Y ^ 6 / (D:ℝ) := by
      have hkey : X ^ 2 * (1 + PAS) ^ 4 ≤ Y ^ 6 := by
        calc X ^ 2 * (1 + PAS) ^ 4 ≤ Y ^ 2 * Y ^ 4 :=
              mul_le_mul (pow_le_pow_left₀ hX0 hXY 2) (pow_le_pow_left₀ (by linarith) h1PASY 4)
                (by positivity) (by positivity)
          _ = Y ^ 6 := by ring
      have e : X ^ 2 * (Amain * (1 + PAS) ^ 4 / (D:ℝ))
          = Amain * (X ^ 2 * (1 + PAS) ^ 4) / (D:ℝ) := by
        ring
      rw [e]
      refine div_le_div_of_nonneg_right ?_ hDpos.le
      exact mul_le_mul_of_nonneg_left hkey hAmain0
    calc X ^ 2 * |(∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
            - X ^ 4 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ X ^ 2 * (cmain * (1 + X) ^ 4 / L + Amain * (1 + PAS) ^ 4 / (D:ℝ)) :=
          mul_le_mul_of_nonneg_left hEvSum (by positivity)
      _ = X ^ 2 * (cmain * (1 + X) ^ 4 / L) + X ^ 2 * (Amain * (1 + PAS) ^ 4 / (D:ℝ)) := by ring
      _ ≤ cmain * (1 + X) ^ 6 / L + Amain * Y ^ 6 / (D:ℝ) := add_le_add hLpart hDpart
  -- === error part (Approach A: Inn² − X²Ev² = 2X·Ev·δ + δ²) ===
  have hPrnn : ∀ r, 0 ≤ Pr r := fun r => by rw [hPrdef]; exact mjs_PFsum_nn _
  have hterm : ∀ r ∈ filt,
      |(Inn r) ^ 2 / Denom r - X ^ 2 * ((Ev r) ^ 2 / Denom r)|
      ≤ ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r := by
    intro r hr
    have hdpos := hDenompos r hr
    have hE := hEvbd r hr
    have hI := hInnbd r hr
    have hPr := hPrnn r
    set δ : ℝ := Inn r - X * Ev r with hδdef
    set Q : ℝ := Aic * PAS * Pr r with hQdef
    have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
    have hδbd : |δ| ≤ cic + Q := by rw [hδdef, hQdef]; exact hI
    have hnum : (Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2 = 2 * X * (Ev r) * δ + δ ^ 2 := by
      rw [hδdef]; ring
    have habs : |(Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2|
        ≤ (2 * X * cF * cic + 2 * cic ^ 2) + 2 * X * cF * Aic * PAS * Pr r
          + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2 := by
      rw [hnum]
      have h1 : |2 * X * (Ev r) * δ| = 2 * X * |Ev r| * |δ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * X)]
      have h2 : |2 * X * (Ev r) * δ| ≤ 2 * X * cF * (cic + Q) := by
        rw [h1]
        have hb : |Ev r| * |δ| ≤ cF * (cic + Q) :=
          mul_le_mul hE hδbd (abs_nonneg _) hcF0
        calc 2 * X * |Ev r| * |δ| = 2 * X * (|Ev r| * |δ|) := by ring
          _ ≤ 2 * X * (cF * (cic + Q)) := mul_le_mul_of_nonneg_left hb (by positivity)
          _ = 2 * X * cF * (cic + Q) := by ring
      have h3 : |δ ^ 2| ≤ 2 * cic ^ 2 + 2 * Q ^ 2 := by
        rw [abs_pow]
        have hsq : |δ| ^ 2 ≤ (cic + Q) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδbd 2
        nlinarith [hsq, sq_nonneg (cic - Q)]
      have hcomb : 2 * X * cF * (cic + Q) + (2 * cic ^ 2 + 2 * Q ^ 2)
          = (2 * X * cF * cic + 2 * cic ^ 2) + 2 * X * cF * Aic * PAS * Pr r
            + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2 := by rw [hQdef]; ring
      calc |2 * X * (Ev r) * δ + δ ^ 2|
          ≤ |2 * X * (Ev r) * δ| + |δ ^ 2| := abs_add_le _ _
        _ ≤ 2 * X * cF * (cic + Q) + (2 * cic ^ 2 + 2 * Q ^ 2) := add_le_add h2 h3
        _ = _ := hcomb
    have heq : (Inn r) ^ 2 / Denom r - X ^ 2 * ((Ev r) ^ 2 / Denom r)
        = ((Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2) / Denom r := by ring
    rw [heq, abs_div, abs_of_pos hdpos]
    exact div_le_div_of_nonneg_right habs hdpos.le
  have herr : |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
        - X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)|
      ≤ ∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hbound_eq : (∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r)
      = (2 * X * cF * cic + 2 * cic ^ 2) * (∑ r ∈ filt, 1 / Denom r)
        + (2 * X * cF * Aic * PAS) * (∑ r ∈ filt, Pr r / Denom r)
        + (2 * Aic ^ 2 * PAS ^ 2) * (∑ r ∈ filt, (Pr r) ^ 2 / Denom r) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  have herr2 : (∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r)
      ≤ (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ 4
        + (2 * X * cF * Aic * PAS) * (256 * PAS ^ 4 / (D:ℝ))
        + (2 * Aic ^ 2 * PAS ^ 2) * (5120 * PAS ^ 4 / (D:ℝ)) := by
    rw [hbound_eq]
    have c0 : 0 ≤ 2 * X * cF * cic + 2 * cic ^ 2 := by positivity
    have c1 : 0 ≤ 2 * X * cF * Aic * PAS := by positivity
    have c2 : 0 ≤ 2 * Aic ^ 2 * PAS ^ 2 := by positivity
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hS0le c0
    · exact mul_le_mul_of_nonneg_left hS1le c1
    · exact mul_le_mul_of_nonneg_left hS2le c2
  -- === absorptions ===
  obtain ⟨habsXL0, habsL0⟩ := mjs_absorb κ L hκpos hL1
  have habsXL : X * L ^ 4 ≤ (1 / κ ^ 5) * (1 + X) ^ 6 * (1 / L) := by
    rw [hXdef]; exact habsXL0
  have habsL : L ^ 4 ≤ (1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L) := by
    rw [hXdef]; exact habsL0
  -- assemble error side
  have hLLnn : (0:ℝ) ≤ 1 / L := by positivity
  have hXPAS5 : X * PAS ^ 5 ≤ Y ^ 6 := by
    calc X * PAS ^ 5 ≤ Y * Y ^ 5 :=
          mul_le_mul hXY (pow_le_pow_left₀ hPAS0 hPASY 5) (by positivity) hY0
      _ = Y ^ 6 := by ring
  have hPAS6 : PAS ^ 6 ≤ Y ^ 6 := pow_le_pow_left₀ hPAS0 hPASY 6
  -- the 1/L opaque pieces
  have hm1 : (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ 4
      ≤ (2 * cF * cic * cg ^ 4 / κ ^ 5 + 2 * cic ^ 2 * cg ^ 4 / κ ^ 6) * (1 + X) ^ 6 / L := by
    have e : (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ 4
        = (2 * cF * cic * cg ^ 4) * (X * L ^ 4) + (2 * cic ^ 2 * cg ^ 4) * (L ^ 4) := by ring
    rw [e]
    have hb1 : (2 * cF * cic * cg ^ 4) * (X * L ^ 4)
        ≤ (2 * cF * cic * cg ^ 4) * ((1 / κ ^ 5) * (1 + X) ^ 6 * (1 / L)) :=
      mul_le_mul_of_nonneg_left habsXL (by positivity)
    have hb2 : (2 * cic ^ 2 * cg ^ 4) * (L ^ 4)
        ≤ (2 * cic ^ 2 * cg ^ 4) * ((1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L)) :=
      mul_le_mul_of_nonneg_left habsL (by positivity)
    calc (2 * cF * cic * cg ^ 4) * (X * L ^ 4) + (2 * cic ^ 2 * cg ^ 4) * (L ^ 4)
        ≤ (2 * cF * cic * cg ^ 4) * ((1 / κ ^ 5) * (1 + X) ^ 6 * (1 / L))
          + (2 * cic ^ 2 * cg ^ 4) * ((1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L)) := add_le_add hb1 hb2
      _ = (2 * cF * cic * cg ^ 4 / κ ^ 5 + 2 * cic ^ 2 * cg ^ 4 / κ ^ 6) * (1 + X) ^ 6 / L := by
        ring
  -- the 1/D relative pieces
  have hm2 : (2 * X * cF * Aic * PAS) * (256 * PAS ^ 4 / (D:ℝ))
      ≤ (512 * cF * Aic) * Y ^ 6 / (D:ℝ) := by
    have e : (2 * X * cF * Aic * PAS) * (256 * PAS ^ 4 / (D:ℝ))
        = (512 * cF * Aic) * (X * PAS ^ 5) / (D:ℝ) := by ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    exact mul_le_mul_of_nonneg_left hXPAS5 (by positivity)
  have hm3 : (2 * Aic ^ 2 * PAS ^ 2) * (5120 * PAS ^ 4 / (D:ℝ))
      ≤ (10240 * Aic ^ 2) * Y ^ 6 / (D:ℝ) := by
    have e : (2 * Aic ^ 2 * PAS ^ 2) * (5120 * PAS ^ 4 / (D:ℝ))
        = (10240 * Aic ^ 2) * (PAS ^ 6) / (D:ℝ) := by ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    exact mul_le_mul_of_nonneg_left hPAS6 (by positivity)
  -- === final assembly ===
  have hgoal : |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
        - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ (cmain + 2 * cF * cic * cg ^ 4 / κ ^ 5 + 2 * cic ^ 2 * cg ^ 4 / κ ^ 6) * (1 + X) ^ 6 / L
        + (Amain + 512 * cF * Aic + 10240 * Aic ^ 2) * Y ^ 6 / (D:ℝ) := by
    calc |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
            - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r) - X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)|
          + |X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
            - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)| := abs_sub_le _ _ _
      _ ≤ ((2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ 4
            + (2 * X * cF * Aic * PAS) * (256 * PAS ^ 4 / (D:ℝ))
            + (2 * Aic ^ 2 * PAS ^ 2) * (5120 * PAS ^ 4 / (D:ℝ)))
          + (cmain * (1 + X) ^ 6 / L + Amain * Y ^ 6 / (D:ℝ)) :=
          add_le_add (le_trans herr herr2) hmainpart
      _ ≤ (cmain + 2 * cF * cic * cg ^ 4 / κ ^ 5 + 2 * cic ^ 2 * cg ^ 4 / κ ^ 6) * (1 + X) ^ 6 / L
          + (Amain + 512 * cF * Aic + 10240 * Aic ^ 2) * Y ^ 6 / (D:ℝ) := by
          have hexpand :
              (cmain + 2 * cF * cic * cg ^ 4 / κ ^ 5 + 2 * cic ^ 2 * cg ^ 4 / κ ^ 6)
                  * (1 + X) ^ 6 / L
              = (2 * cF * cic * cg ^ 4 / κ ^ 5 + 2 * cic ^ 2 * cg ^ 4 / κ ^ 6) * (1 + X) ^ 6 / L
                + cmain * (1 + X) ^ 6 / L := by ring
          have hexpand2 :
              (Amain + 512 * cF * Aic + 10240 * Aic ^ 2) * Y ^ 6 / (D:ℝ)
              = (512 * cF * Aic) * Y ^ 6 / (D:ℝ) + (10240 * Aic ^ 2) * Y ^ 6 / (D:ℝ)
                + Amain * Y ^ 6 / (D:ℝ) := by ring
          rw [hexpand, hexpand2]
          linarith [hm1, hm2, hm3]
  -- the frozen goal is definitionally the `Inn/Denom/X/Y` form
  exact hgoal

end Salt.Twelve
