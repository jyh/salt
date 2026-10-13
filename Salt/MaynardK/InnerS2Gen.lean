/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.InnerS2

/-!
# C1 · B4.3b — the S₂ inner bound for a bounded weight at general `k` (`s2_inner_y_gen`)

InnerS2's k = 5 half (`box_marked_gmoment`, `yF_V_mul_g_le`, `s2_inner_yF`) at general `k`; the
k-generic half is imported. `s2_inner_yF_of_gen` (in `Controls`) recovers the landed `s2_inner_yF`
verbatim. Ported by an Opus executor from a frozen brief (2026-10-11).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Maynard Salt.Twelve

/-- `lemma53_tightW` at `B = 1` for a bounded weight (general-`k` `yM_sub_inn_le`). -/
theorem yM_sub_inn_le_gen_s2 (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hyB : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (hR : 2 ≤ R) (hW' : Squarefree W')
    (hDW : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hDk : 12 * k ^ 2 ≤ D)
    (u : Fin k → ℕ) (hum : u m = 1) (husupp : u ∈ kSieveIndex k R W') :
    |yM k R W' m y u
        - ∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ lemma53Const * (k : ℝ) * Real.log R / (D : ℝ) := by
  have h := lemma53_tightW k R W' D m y 1 (by norm_num) hyB hysupp u hum hR
    husupp hW' hDW m.pos hDk
  simpa using h

/-- `|Inn(u)| ≤ PAS` for a bounded weight (general-`k` `absInn_le_pas`). -/
theorem absInn_le_pas_gen_s2 (k R W' : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hyB : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (hR : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W') (u : Fin k → ℕ) :
    |∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ Salt.Maynard.phiAtomSum R W' := by
  classical
  have hstep : ∀ am ∈ Finset.range R,
      |y (Function.update u m am) / (Nat.totient am : ℝ)|
        ≤ (if (Squarefree am ∧ am.Coprime W' ∧ (1 : ℕ) ∣ am)
            then (Real.log am) ^ 0 / (Nat.totient am : ℝ) else 0) := by
    intro am _
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient am : ℝ))]
    split_ifs with hc
    · rw [pow_zero]
      exact div_le_div_of_nonneg_right (hyB _) (by positivity)
    · have hnot : Function.update u m am ∉ kSieveIndex k R W' := by
        intro hmem
        obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff _).mp hmem
        have h1 : Squarefree am := by
          have := hsqf m; rwa [Function.update_self] at this
        have h2 : am.Coprime W' := by
          have := hcop m; rwa [Function.update_self] at this
        exact hc ⟨h1, h2, one_dvd am⟩
      rw [hysupp _ hnot, abs_zero, zero_div]
  calc |∑ am ∈ Finset.range R, y (Function.update u m am) / (Nat.totient am : ℝ)|
      ≤ ∑ am ∈ Finset.range R, |y (Function.update u m am) / (Nat.totient am : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ am ∈ Finset.range R,
          (if (Squarefree am ∧ am.Coprime W' ∧ (1 : ℕ) ∣ am)
            then (Real.log am) ^ 0 / (Nat.totient am : ℝ) else 0) :=
        Finset.sum_le_sum hstep
    _ = ∑ am ∈ (Finset.range R).filter
          (fun r => Squarefree r ∧ r.Coprime W' ∧ (1 : ℕ) ∣ r),
          (Real.log am) ^ 0 / (Nat.totient am : ℝ) := (Finset.sum_filter _ _).symm
    _ ≤ (1 / (Nat.totient 1 : ℝ)) * (Real.log R) ^ 0 * Salt.Maynard.phiAtomSum R W' :=
        marked_sqf_phi_rel W' hW' hpos 0 1 R one_pos hR
    _ = Salt.Maynard.phiAtomSum R W' := by simp

/-! ## Deliverable 1 — the marked 4-dim `g`-moment `box_marked_gmoment`

The marked generalisation of the landed `gmoment4_le` (which is the `Q = ∅`
case): the `1/∏_{i≠m}g`-moment over the pinned box `uₘ = 1`, further restricted
to tuples with `p ∣ u (slot p)` for every marked prime `p ∈ Q`, is bounded by
`(∏_{p∈Q}(p−2)⁻¹)·(2·PAS)⁴`.  Proof: mirror `gmoment4_le`'s box→per-coordinate
product→`marked_sqf_g_rel` structure, threading the `|Q|` marks through the
per-coordinate `marked_sqf_g_rel` reindexes at the `slot`-selected products
`sfun i = ∏_{p∈Q, slot p = i} p`, and collecting the constants by fiberwise
partition of `Q` under `slot`. -/
theorem box_marked_gmoment_gen (k R W' D : ℕ) (m : Fin k) (Q : Finset ℕ) (slot : ℕ → Fin k)
    (hslot : ∀ p ∈ Q, slot p ≠ m) (hQp : ∀ p ∈ Q, p.Prime) (hDlt : ∀ p ∈ Q, D < p)
    (hW' : Squarefree W') (hpos : 0 < W') (hD : 3 ≤ D)
    (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ u ∈ (kSieveIndex k R W').filter
        (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slot p)),
        1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ))
      ≤ (∏ p ∈ Q, ((p : ℝ) - 2)⁻¹) * (2 * Salt.Maynard.phiAtomSum R W') ^ (k - 1) := by
  classical
  -- the slot-selected forced product on each coordinate
  set sfun : Fin k → ℕ := fun i => ∏ p ∈ Q.filter (fun p => slot p = i), p with hsfun
  set f : Fin k → ℕ → ℝ := fun i x => if i = m then 1 else (gMult x : ℝ)⁻¹ with hf
  set coordSet : Fin k → Finset ℕ := fun i =>
    if i = m then {1}
    else (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W' ∧ sfun i ∣ x)
    with hcoordSet
  -- primes of `Q` are all `≥ 3`
  have hQ3 : ∀ p ∈ Q, 3 ≤ p := fun p hp => by have := hDlt p hp; omega
  have hsfunpos : ∀ i, 0 < sfun i := fun i => by
    change 0 < ∏ p ∈ Q.filter (fun p => slot p = i), p
    exact Finset.prod_pos (fun p hp => (hQp p (Finset.mem_of_mem_filter p hp)).pos)
  -- helper equations for `f` and `coordSet`
  have hf_m : ∀ x, f m x = 1 := fun x => by simp [hf]
  have hf_ne : ∀ i x, i ≠ m → f i x = (gMult x : ℝ)⁻¹ := fun i x hi => by simp [hf, hi]
  have hcs_m : coordSet m = {1} := by simp [hcoordSet]
  have hcs_ne : ∀ i, i ≠ m → coordSet i
      = (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W' ∧ sfun i ∣ x) :=
    fun i hi => by simp [hcoordSet, hi]
  have hfnn : ∀ i x, 0 ≤ f i x := fun i x => by simp only [hf]; split_ifs <;> positivity
  have hcard : (Finset.univ.erase m).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
  -- the `g`-constant collapses to `∏_{p∈Q}(p−2)⁻¹` by fiberwise partition
  have hgcast : ∀ i ∈ Finset.univ.erase m,
      (gMult (sfun i) : ℝ) = ∏ p ∈ Q.filter (fun p => slot p = i), ((p : ℝ) - 2) := by
    intro i _
    have hpf : (sfun i).primeFactors = Q.filter (fun p => slot p = i) := by
      change (∏ p ∈ Q.filter (fun p => slot p = i), p).primeFactors
          = Q.filter (fun p => slot p = i)
      exact Nat.primeFactors_prod (fun p hp => hQp p (Finset.mem_of_mem_filter p hp))
    have hodd : ∀ p ∈ (sfun i).primeFactors, 3 ≤ p := by
      rw [hpf]; intro p hp; exact hQ3 p (Finset.mem_of_mem_filter p hp)
    rw [gMult_cast hodd, hpf]
  have hprodg : ∏ i ∈ Finset.univ.erase m, (gMult (sfun i) : ℝ) = ∏ p ∈ Q, ((p : ℝ) - 2) := by
    rw [Finset.prod_congr rfl hgcast]
    exact Finset.prod_fiberwise_of_maps_to
      (fun p hp => Finset.mem_erase.mpr ⟨hslot p hp, Finset.mem_univ _⟩)
      (fun p => ((p : ℝ) - 2))
  -- STEP 1: rewrite the summand as a full `univ`-product of `f`
  have hfeq : ∀ u : Fin k → ℕ,
      (1 : ℝ) / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) = ∏ i, f i (u i) := by
    intro u
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i (u i)) (Finset.mem_univ m),
      hf_m (u m), one_mul, one_div, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun i hi => (hf_ne i (u i) (Finset.ne_of_mem_erase hi)).symm)
  -- STEP 2: the marked box is contained in the per-coordinate product box
  have hsub : (kSieveIndex k R W').filter
      (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slot p)) ⊆ Fintype.piFinset coordSet := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨hbox, hum, hmark⟩ := hu
    obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff u).mp hbox
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i = m
    · subst hi; rw [hcs_m, Finset.mem_singleton]; exact hum
    · rw [hcs_ne i hi, Finset.mem_filter, Finset.mem_range]
      refine ⟨kSieveIndex_coord_lt hbox i, hsqf i, hcop i, ?_⟩
      change (∏ p ∈ Q.filter (fun p => slot p = i), p) ∣ u i
      apply Finset.prod_primes_dvd
      · exact fun p hp => (hQp p (Finset.mem_of_mem_filter p hp)).prime
      · intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpQ, hpi⟩ := hp
        have := hmark p hpQ; rwa [hpi] at this
  -- STEP 3: enlarge, factor, split off `m`, and bound each coordinate
  calc ∑ u ∈ (kSieveIndex k R W').filter
          (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slot p)),
          1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ)
      = ∑ u ∈ (kSieveIndex k R W').filter
          (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slot p)),
          ∏ i, f i (u i) := Finset.sum_congr rfl (fun u _ => hfeq u)
    _ ≤ ∑ u ∈ Fintype.piFinset coordSet, ∏ i, f i (u i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun u _ _ => Finset.prod_nonneg (fun i _ => hfnn i (u i)))
    _ = ∏ i, ∑ x ∈ coordSet i, f i x := (Finset.prod_univ_sum coordSet f).symm
    _ = (∑ x ∈ coordSet m, f m x)
          * ∏ i ∈ Finset.univ.erase m, (∑ x ∈ coordSet i, f i x) :=
        (Finset.mul_prod_erase Finset.univ (fun i => ∑ x ∈ coordSet i, f i x)
          (Finset.mem_univ m)).symm
    _ = ∏ i ∈ Finset.univ.erase m, (∑ x ∈ coordSet i, f i x) := by
        rw [hcs_m, Finset.sum_singleton, hf_m, one_mul]
    _ ≤ ∏ i ∈ Finset.univ.erase m,
          ((gMult (sfun i) : ℝ)⁻¹ * (2 * Salt.Maynard.phiAtomSum R W')) := by
        apply Finset.prod_le_prod
        · intro i _; exact Finset.sum_nonneg (fun x _ => hfnn i x)
        · intro i hi
          have hine : i ≠ m := Finset.ne_of_mem_erase hi
          rw [hcs_ne i hine]
          have hbound := marked_sqf_g_rel W' hW' hpos 0 D (sfun i) R hD hDW
            (hsfunpos i) hR2
          calc ∑ x ∈ (Finset.range R).filter
                  (fun x => Squarefree x ∧ x.Coprime W' ∧ sfun i ∣ x), f i x
              = ∑ x ∈ (Finset.range R).filter
                  (fun x => Squarefree x ∧ x.Coprime W' ∧ sfun i ∣ x),
                  (Real.log x) ^ 0 / (gMult x : ℝ) :=
                Finset.sum_congr rfl (fun x _ => by rw [hf_ne i x hine, pow_zero, one_div])
            _ ≤ (1 / (gMult (sfun i) : ℝ)) * 2 * (Real.log R) ^ 0
                  * Salt.Maynard.phiAtomSum R W' := hbound
            _ = (gMult (sfun i) : ℝ)⁻¹ * (2 * Salt.Maynard.phiAtomSum R W') := by
                rw [pow_zero, one_div]; ring
    _ = (∏ i ∈ Finset.univ.erase m, (gMult (sfun i) : ℝ)⁻¹)
          * (2 * Salt.Maynard.phiAtomSum R W') ^ (k - 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    _ = (∏ p ∈ Q, ((p : ℝ) - 2)⁻¹) * (2 * Salt.Maynard.phiAtomSum R W') ^ (k - 1) := by
        congr 1
        rw [Finset.prod_inv_distrib, hprodg, ← Finset.prod_inv_distrib]

/-! ## Deliverable 4 — the S₂ termwise `V`-bound and `s2_inner_yF`

The port of NC-1's `s1_inner_bounded` to the `g`/`V` side (design's S₂ termwise
derivation).  The two S₂-specific ingredients are the `g`-side `lcm`-split and the
termwise `V`-bound `∏g(w)·|V(w)| ≤ PAS+ε` (both below); the contamination
partition then mirrors `s1_inner_bounded` verbatim with `φ→g`, `(p−1)→(p−2)`,
`M→(2·PAS)⁴`. -/

/-- `gMult` is multiplicative on coprime arguments (local copy of the `private`
`gMult_mul_coprime`). -/
private lemma gMult_mul_cop {a b : ℕ} (h : Nat.Coprime a b) :
    gMult (a * b) = gMult a * gMult b := by
  unfold gMult
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]

/-- **`g`-side `lcm`-split** (the `g`-analog of `totient_lcm_split`): for
squarefree `a`, `g(lcm b a) = g(b)·g(a/gcd(a,b))` with coprime factors. -/
private lemma gMult_lcm_split {a b : ℕ} (ha : Squarefree a) :
    gMult (Nat.lcm b a) = gMult b * gMult (a / Nat.gcd a b) := by
  obtain ⟨heq, hcop⟩ := lcm_split (a := a) (b := b) ha
  rw [heq, gMult_mul_cop hcop]

/-- **The S₂ termwise `V`-bound.**  `∏ᵢg(wᵢ)·|V(w)| ≤ PAS + ε`, where
`ε = lemma53Const·5·log R/D`.  Off the pinned box `V(w) = 0` (`lamPhiContractM_vanish`);
on it, `∏g(w)·|V(w)| = |yM(w)|` (from `yM = (∏μ·g)·V`, `μ²=1`, `g ≥ 0`), and
`|yM(w)| ≤ |Inn(w)| + ε ≤ PAS + ε` by the LANDED `yM_sub_inn_le` (contraction
error) + `absInn_le_pas` (`|Inn| ≤ PAS`). -/
theorem y_V_mul_g_le_gen (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hyB : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (hR2 : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W')
    (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hDk : 12 * k ^ 2 ≤ D) (w : Fin k → ℕ) :
    (∏ i, (gMult (w i) : ℝ)) * |lamPhiContractM k R W' m y w|
      ≤ Salt.Maynard.phiAtomSum R W' + lemma53Const * (k : ℝ) * Real.log R / (D : ℝ) := by
  set ε : ℝ := lemma53Const * (k : ℝ) * Real.log R / (D : ℝ) with hεdef
  have hPASnn : 0 ≤ Salt.Maynard.phiAtomSum R W' := by
    unfold Salt.Maynard.phiAtomSum; exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hε0 : 0 ≤ ε := by
    rw [hεdef]; apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg lemma53Const_nonneg (Nat.cast_nonneg _)) (Real.log_nonneg
      (by exact_mod_cast (by omega : 1 ≤ R)))
  by_cases hcase : w ∈ kSieveIndex k R W' ∧ w m = 1
  · obtain ⟨hwbox, hwm⟩ := hcase
    have hsqf : ∀ i, Squarefree (w i) := fun i => ((mem_kSieveIndex_iff w).mp hwbox).1 i
    have hμabs : ∀ i, |((μ (w i) : ℤ) : ℝ)| = 1 := by
      intro i
      have hsq := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsqf i)
      have hc : ((μ (w i) : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hsq
      nlinarith [abs_nonneg ((μ (w i) : ℤ) : ℝ), sq_abs ((μ (w i) : ℤ) : ℝ)]
    have hidentity : (∏ i, (gMult (w i) : ℝ)) * |lamPhiContractM k R W' m y w|
        = |yM k R W' m y w| := by
      rw [yM, abs_mul]
      congr 1
      rw [Finset.abs_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [abs_mul, hμabs i, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    rw [hidentity]
    have hsub := yM_sub_inn_le_gen_s2 k R W' D m y hyB hysupp hR2 hW' hDW hDk w hwm hwbox
    have hInn := absInn_le_pas_gen_s2 k R W' m y hyB hysupp hR2 hW' hpos w
    have htri : |yM k R W' m y w|
        ≤ |∑ am ∈ Finset.range R,
              y (Function.update w m am) / (Nat.totient am : ℝ)| + ε := by
      have := abs_sub_abs_le_abs_sub (yM k R W' m y w)
        (∑ am ∈ Finset.range R, y (Function.update w m am) / (Nat.totient am : ℝ))
      rw [hεdef]; linarith [hsub, this]
    calc |yM k R W' m y w|
        ≤ |∑ am ∈ Finset.range R,
              y (Function.update w m am) / (Nat.totient am : ℝ)| + ε := htri
      _ ≤ Salt.Maynard.phiAtomSum R W' + ε := by linarith [hInn]
  · rw [lamPhiContractM_vanish k R W' m y w hcase, abs_zero, mul_zero]
    linarith [hPASnn, hε0]

/-- **NC-2 hterm_g** — the per-`u` termwise bound (S₁'s `hterm` ported to g/V).
For `u` in the pinned box, `|∏g(u)·V(u∨σ)·V(u∨τ)| ≤ K·(PAS+ε)²·((1/∏_{i≠m}g)·CT_u)`
with `K = ∏(q−2)⁻²`, `CT_u = ∏_{contam(u)}(q−2)`; via `yF_V_mul_g_le` + `gMult_lcm_split`
+ the g-`hcompl` contamination identity. -/
private lemma s2_term_bound (k : ℕ) (m : Fin k)
    (R W' D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hyB : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (hR2 : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W')
    (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hDk : 12 * k ^ 2 ≤ D)
    {s : ℕ} (hs : Squarefree s)
    (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k)
    (hα : α ∈ assignments k s)
    (u : Fin k → ℕ) (hu : u ∈ kSieveIndex k R W') (hum : u m = 1) :
    |(∏ i, (gMult (u i) : ℝ))
        * lamPhiContractM k R W' m y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
        * lamPhiContractM k R W' m y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))|
      ≤ (∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 2)⁻¹ ^ 2)
          * ((Salt.Maynard.phiAtomSum R W' + lemma53Const * (k : ℝ) * Real.log R / D) ^ 2)
          * ((1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ))
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 2)) := by
  classical
  have hD3 : 3 ≤ D := le_trans (by nlinarith [m.pos] : 3 ≤ 12 * k ^ 2) hDk
  set V := lamPhiContractM k R W' m y with hVdef
  set PE : ℝ := Salt.Maynard.phiAtomSum R W' + lemma53Const * (k : ℝ) * Real.log R / D with hPEdef
  set σ : Fin k → ℕ := slotProd s α Prod.fst with hσ0
  set τ : Fin k → ℕ := slotProd s α Prod.snd with hτ0
  set K : ℝ := ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 2)⁻¹ ^ 2 with hKdef
  set CT : ℝ := ∏ q ∈ s.primeFactors.attach.filter
      (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
        ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)), (((q : ℕ) : ℝ) - 2) with hCTdef
  have hPE0 : 0 ≤ PE := by
    rw [hPEdef]
    have h1 : 0 ≤ Salt.Maynard.phiAtomSum R W' := by
      unfold Salt.Maynard.phiAtomSum; exact Finset.sum_nonneg (fun _ _ => by positivity)
    have h2 : 0 ≤ lemma53Const * (k : ℝ) * Real.log R / D :=
      div_nonneg (mul_nonneg (mul_nonneg lemma53Const_nonneg (Nat.cast_nonneg _))
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R)))) (by positivity)
    linarith
  have hPprime : ∀ p ∈ s.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hσsq : ∀ (sel : Fin k × Fin k → Fin k) i, Squarefree (slotProd s α sel i) :=
    fun sel i => hs.squarefree_of_dvd (slotProd_dvd hs α sel i)
  have hgpos : ∀ (v : Fin k → ℕ), v ∈ kSieveIndex k R W' → ∀ i, (0:ℝ) < (gMult (v i) : ℝ) := by
    intro v hv i
    have hposN : (0:ℕ) < gMult (v i) := by
      rw [gMult]; apply Finset.prod_pos; intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpcop : p.Coprime W' :=
        (((mem_kSieveIndex_iff v).mp hv).2.2.1 i).coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)
      have hpW' : ¬ p ∣ W' := (Nat.Prime.coprime_iff_not_dvd hpp).mp hpcop
      have := hDW p hpp hpW'; omega
    exact_mod_cast hposN
  have hΦu_pos : 0 < ∏ i, (gMult (u i) : ℝ) := Finset.prod_pos (fun i _ => hgpos u hu i)
  have hgm1 : (gMult (u m) : ℝ) = 1 := by rw [hum]; simp [gMult, Nat.primeFactors_one]
  have hprodgu : (∏ i, (gMult (u i) : ℝ)) = ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (gMult (u i):ℝ)) (Finset.mem_univ m),
      hgm1, one_mul]
  have hKnn : 0 ≤ K := Finset.prod_nonneg fun q _ => sq_nonneg _
  have hq2 : ∀ q : {x // x ∈ s.primeFactors}, (2:ℝ) ≤ ((q:ℕ):ℝ) := by
    intro q; exact_mod_cast (hPprime _ q.2).two_le
  have hCTnn : 0 ≤ CT := Finset.prod_nonneg fun q _ => by have := hq2 q; linarith
  have hinvnn : 0 ≤ 1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) := by
    rw [← hprodgu]; positivity
  by_cases hbox : ((fun i => Nat.lcm (u i) (σ i)) ∈ kSieveIndex k R W'
      ∧ (fun i => Nat.lcm (u i) (σ i)) m = 1)
      ∧ ((fun i => Nat.lcm (u i) (τ i)) ∈ kSieveIndex k R W'
      ∧ (fun i => Nat.lcm (u i) (τ i)) m = 1)
  · obtain ⟨⟨hσbox, _hσm⟩, ⟨hτbox, _hτm⟩⟩ := hbox
    -- g > 0 on the cofactor products
    have hcofpos : ∀ (sel : Fin k × Fin k → Fin k),
        (fun i => Nat.lcm (u i) (slotProd s α sel i)) ∈ kSieveIndex k R W' →
        (0:ℝ) < ∏ i, (gMult (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)) : ℝ) := by
      intro sel hsb
      apply Finset.prod_pos; intro i _
      have hposN : (0:ℕ) < gMult (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)) := by
        rw [gMult]; apply Finset.prod_pos; intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpdvd : p ∣ slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i) :=
          Nat.dvd_of_mem_primeFactors hp
        -- p ∣ σᵢ/gcd ∣ σᵢ ∣ lcm(uᵢ,σᵢ) = (u∨σ)ᵢ, a box coord ⇒ p ∤ W'
        have hplcm : p ∣ Nat.lcm (u i) (slotProd s α sel i) :=
          (hpdvd.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))).trans (Nat.dvd_lcm_right _ _)
        have hpW' : ¬ p ∣ W' := (Nat.Prime.coprime_iff_not_dvd hpp).mp
          ((((mem_kSieveIndex_iff _).mp hsb).2.2.1 i).coprime_dvd_left hplcm)
        have := hDW p hpp hpW'; omega
      exact_mod_cast hposN
    have hGσpos := hcofpos Prod.fst hσbox
    have hGτpos := hcofpos Prod.snd hτbox
    -- ∏g(u∨sel) = ∏g(u) · Gsel  (g-lcm-split per coord)
    have hgsplit : ∀ (sel : Fin k × Fin k → Fin k),
        (∏ i, (gMult (Nat.lcm (u i) (slotProd s α sel i)) : ℝ))
          = (∏ i, (gMult (u i) : ℝ))
              * ∏ i, (gMult (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)) : ℝ) := by
      intro sel
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      rw [← Nat.cast_mul, ← gMult_lcm_split (hσsq sel i)]
    -- V-bound ⇒ |V(u∨sel)| ≤ PE / (∏g(u) · Gsel)
    have hVle : ∀ (sel : Fin k × Fin k → Fin k),
        (0:ℝ) < ∏ i, (gMult (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)) : ℝ) →
        |V (fun i => Nat.lcm (u i) (slotProd s α sel i))|
          ≤ PE / ((∏ i, (gMult (u i) : ℝ))
              * ∏ i, (gMult (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)) : ℝ)) := by
      intro sel hGsel
      rw [le_div_iff₀ (mul_pos hΦu_pos hGsel), ← hgsplit sel, mul_comm]
      rw [hPEdef]
      exact y_V_mul_g_le_gen k R W' D m y hyB hysupp hR2 hW' hpos hDW hDk _
    have hVσle := hVle Prod.fst hGσpos
    have hVτle := hVle Prod.snd hGτpos
    -- termwise chain
    have habsprod : |(∏ i, (gMult (u i) : ℝ))
        * V (fun i => Nat.lcm (u i) (σ i)) * V (fun i => Nat.lcm (u i) (τ i))|
        = (∏ i, (gMult (u i) : ℝ)) * |V (fun i => Nat.lcm (u i) (σ i))|
            * |V (fun i => Nat.lcm (u i) (τ i))| := by
      rw [abs_mul, abs_mul, abs_of_pos hΦu_pos]
    rw [habsprod]
    set Gσ : ℝ := ∏ i, (gMult (σ i / Nat.gcd (σ i) (u i)) : ℝ) with hGσdef
    set Gτ : ℝ := ∏ i, (gMult (τ i / Nat.gcd (τ i) (u i)) : ℝ) with hGτdef
    -- hchain: ∏g(u)|Vσ||Vτ| ≤ ∏g(u)·(PE/(∏g(u)Gσ))·(PE/(∏g(u)Gτ))
    have hchain : (∏ i, (gMult (u i) : ℝ)) * |V (fun i => Nat.lcm (u i) (σ i))|
          * |V (fun i => Nat.lcm (u i) (τ i))|
        ≤ (∏ i, (gMult (u i) : ℝ)) * (PE / ((∏ i, (gMult (u i) : ℝ)) * Gσ))
            * (PE / ((∏ i, (gMult (u i) : ℝ)) * Gτ)) := by
      have hNσ : 0 ≤ (∏ i, (gMult (u i) : ℝ)) * (PE / ((∏ i, (gMult (u i) : ℝ)) * Gσ)) :=
        mul_nonneg hΦu_pos.le (by positivity)
      refine mul_le_mul ?_ hVτle (abs_nonneg _) hNσ
      exact mul_le_mul_of_nonneg_left hVσle hΦu_pos.le
    refine le_trans hchain ?_
    -- halg: rewrite to K·PE²·(1/∏g(u))·(∏_{contam}(q-2))  via hcompl_g
    have halg : (∏ i, (gMult (u i) : ℝ)) * (PE / ((∏ i, (gMult (u i) : ℝ)) * Gσ))
          * (PE / ((∏ i, (gMult (u i) : ℝ)) * Gτ))
        = (1 / ∏ i, (gMult (u i) : ℝ)) * (Gσ⁻¹ * Gτ⁻¹) * PE ^ 2 := by
      have h1 := hΦu_pos.ne'
      have h2 := hGσpos.ne'
      have h3 := hGτpos.ne'
      field_simp
    rw [halg]
    -- hcompl_g: Gσ⁻¹Gτ⁻¹ = K · CT
    have hslots : ∀ (q : {x // x ∈ s.primeFactors}), (α q.1 q.2).1 ≠ (α q.1 q.2).2 := by
      intro q
      have hmem := (Finset.mem_pi.mp hα) q.1 q.2
      rw [Finset.mem_offDiag] at hmem; exact hmem.2.2
    -- every prime of s divides a box coord, hence ≥ 3 (coprime W', > D ≥ 300)
    have hs3 : ∀ (q : {x // x ∈ s.primeFactors}), 3 ≤ (q : ℕ) := by
      intro q
      have hqp : ((q:ℕ)).Prime := hPprime _ q.2
      have hqσ : (q:ℕ) ∣ slotProd s α Prod.fst ((α q.1 q.2).1) :=
        (prime_dvd_slotProd_iff α Prod.fst hqp _).mpr ⟨q.2, rfl⟩
      have hqlcm : (q:ℕ) ∣ Nat.lcm (u ((α q.1 q.2).1)) (slotProd s α Prod.fst ((α q.1 q.2).1)) :=
        hqσ.trans (Nat.dvd_lcm_right _ _)
      have hqW' : ¬ (q:ℕ) ∣ W' := (Nat.Prime.coprime_iff_not_dvd hqp).mp
        ((((mem_kSieveIndex_iff _).mp hσbox).2.2.1 ((α q.1 q.2).1)).coprime_dvd_left hqlcm)
      have := hDW (q:ℕ) hqp hqW'; omega
    have hqne0 : ∀ (q : {x // x ∈ s.primeFactors}), (((q:ℕ):ℝ) - 2) ≠ 0 := by
      intro q
      have h3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by exact_mod_cast hs3 q
      intro h; linarith
    have hT : (0:ℝ) < ∏ q ∈ s.primeFactors.attach, (((q:ℕ):ℝ) - 2) := by
      apply Finset.prod_pos; intro q _
      have h3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by exact_mod_cast hs3 q
      linarith
    -- hreindex_g: Gσ = ∏_{q : ¬q∣u(sel(αq))} (q-2)
    have hGsel_eq : ∀ (sel : Fin k × Fin k → Fin k),
        (fun i => Nat.lcm (u i) (slotProd s α sel i)) ∈ kSieveIndex k R W' →
        (∏ i, (gMult (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)) : ℝ))
          = ∏ q ∈ s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u (sel (α q.1 q.2))),
              (((q : ℕ) : ℝ) - 2) := by
      intro sel hsb
      have hcast : (∏ i, (gMult (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)) : ℝ))
          = ∏ i, ∏ p ∈ (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)).primeFactors,
              ((p : ℝ) - 2) := by
        apply Finset.prod_congr rfl; intro i _
        refine gMult_cast (fun p hp => ?_)
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hplcm : p ∣ Nat.lcm (u i) (slotProd s α sel i) :=
          ((Nat.dvd_of_mem_primeFactors hp).trans
            (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))).trans (Nat.dvd_lcm_right _ _)
        have hpW' : ¬ p ∣ W' := (Nat.Prime.coprime_iff_not_dvd hpp).mp
          ((((mem_kSieveIndex_iff _).mp hsb).2.2.1 i).coprime_dvd_left hplcm)
        have := hDW p hpp hpW'; omega
      rw [hcast]
      -- the S1 hreindex fiberwise structure, with (·-2)
      rw [← Finset.prod_fiberwise_of_maps_to
        (g := fun q : {x // x ∈ s.primeFactors} => sel (α q.1 q.2))
        (t := (Finset.univ : Finset (Fin k)))
        (fun q _ => Finset.mem_univ _)
        (fun q : {x // x ∈ s.primeFactors} => (((q : ℕ) : ℝ) - 2))]
      apply Finset.prod_congr rfl; intro i _
      have hcne : slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i) ≠ 0 := by
        have hσpos : 0 < slotProd s α sel i := Squarefree.pos (hσsq sel i)
        have hgpos' : 0 < Nat.gcd (slotProd s α sel i) (u i) :=
          Nat.gcd_pos_of_pos_left _ hσpos
        exact (Nat.div_pos (Nat.le_of_dvd hσpos (Nat.gcd_dvd_left _ _)) hgpos').ne'
      have hset : (slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i)).primeFactors
          = ((s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u (sel (α q.1 q.2)))).filter
              (fun q => sel (α q.1 q.2) = i)).image
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ)) := by
        ext p
        simp only [Nat.mem_primeFactors, Finset.mem_image, Finset.mem_filter,
          Finset.mem_attach, true_and]
        constructor
        · rintro ⟨hp, hpc, -⟩
          obtain ⟨hpσ, hpu⟩ := (prime_dvd_cofactor_iff (hσsq sel i) hp).mp hpc
          obtain ⟨hmem, hsel⟩ := (prime_dvd_slotProd_iff α sel hp i).mp hpσ
          refine ⟨⟨p, hmem⟩, ⟨?_, hsel⟩, rfl⟩
          simp only; rw [hsel]; exact hpu
        · rintro ⟨q, ⟨hqnot, hqsel⟩, rfl⟩
          have hqp : (q : ℕ).Prime := hPprime _ q.2
          refine ⟨hqp, ?_, hcne⟩
          apply (prime_dvd_cofactor_iff (hσsq sel i) hqp).mpr
          refine ⟨(prime_dvd_slotProd_iff α sel hqp i).mpr ⟨q.2, hqsel⟩, ?_⟩
          rw [← hqsel]; exact hqnot
      rw [hset, Finset.prod_image]
      intro q₁ _ q₂ _ h; exact Subtype.ext h
    have hGσ_eq : Gσ = ∏ q ∈ s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u ((α q.1 q.2).1)),
        (((q : ℕ) : ℝ) - 2) := hGsel_eq Prod.fst hσbox
    have hGτ_eq : Gτ = ∏ q ∈ s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u ((α q.1 q.2).2)),
        (((q : ℕ) : ℝ) - 2) := hGsel_eq Prod.snd hτbox
    set Bσ := s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)) with hBσ
    set Bτ := s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).2)) with hBτ
    have hsplitσ : (∏ q ∈ Bσ, (((q : ℕ) : ℝ) - 2)) * Gσ
        = ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 2) := by
      rw [hGσ_eq, hBσ]; exact Finset.prod_filter_mul_prod_filter_not _ _ _
    have hsplitτ : (∏ q ∈ Bτ, (((q : ℕ) : ℝ) - 2)) * Gτ
        = ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 2) := by
      rw [hGτ_eq, hBτ]; exact Finset.prod_filter_mul_prod_filter_not _ _ _
    have hdisj : Disjoint Bσ Bτ := by
      rw [Finset.disjoint_left]; intro q hqσ hqτ
      rw [hBσ, Finset.mem_filter] at hqσ; rw [hBτ, Finset.mem_filter] at hqτ
      exact hslots q (prime_dvd_coord_unique hu (hPprime _ q.2) hqσ.2 hqτ.2)
    have hunion : s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
          ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Bσ ∪ Bτ := by
      rw [hBσ, hBτ, Finset.filter_or]
    have hcompl_g : Gσ⁻¹ * Gτ⁻¹ = K * CT := by
      have hKinv : K = ((∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 2))⁻¹) ^ 2 := by
        rw [hKdef, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
      rw [hCTdef, hunion, Finset.prod_union hdisj, hKinv]
      have h1 : Gσ⁻¹ = (∏ q ∈ Bσ, (((q : ℕ) : ℝ) - 2))
          / ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 2) := by
        rw [eq_div_iff hT.ne', ← hsplitσ]; field_simp
      have h2 : Gτ⁻¹ = (∏ q ∈ Bτ, (((q : ℕ) : ℝ) - 2))
          / ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 2) := by
        rw [eq_div_iff hT.ne', ← hsplitτ]; field_simp
      rw [h1, h2]; ring
    rw [hcompl_g, hprodgu]
    apply le_of_eq; ring
  · have hz : V (fun i => Nat.lcm (u i) (σ i)) = 0 ∨ V (fun i => Nat.lcm (u i) (τ i)) = 0 := by
      by_cases h1 : (fun i => Nat.lcm (u i) (σ i)) ∈ kSieveIndex k R W'
          ∧ (fun i => Nat.lcm (u i) (σ i)) m = 1
      · right; exact lamPhiContractM_vanish k R W' m y _ (fun h => hbox ⟨h1, h⟩)
      · left; exact lamPhiContractM_vanish k R W' m y _ h1
    have hterm0 : (∏ i, (gMult (u i) : ℝ))
        * V (fun i => Nat.lcm (u i) (σ i)) * V (fun i => Nat.lcm (u i) (τ i)) = 0 := by
      rcases hz with h | h <;> rw [h] <;> ring
    rw [hterm0, abs_zero]
    exact mul_nonneg (mul_nonneg hKnn (sq_nonneg PE)) (mul_nonneg hinvnn hCTnn)

/-- **NC-2 hpart_g** — the contamination partition (S₁'s `hpart` ported to g), via
pairs-fibering `u ↦ (Bσ(u),Bτ(u))` over the landed `box_marked_gmoment`, giving `3^ω`. -/
private lemma s2_part_bound (k R W' D : ℕ) (hR2 : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W')
    (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hD : 3 ≤ D)
    (m : Fin k) {s : ℕ} (_hs : Squarefree s)
    (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k)
    (hα : α ∈ assignments k s)
    (hfstne : ∀ q : {x // x ∈ s.primeFactors}, (α q.1 q.2).1 ≠ m)
    (hsndne : ∀ q : {x // x ∈ s.primeFactors}, (α q.1 q.2).2 ≠ m) :
    ∑ u ∈ (kSieveIndex k R W').filter (fun u => u m = 1),
        (1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ))
          * ∏ q ∈ s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
              (((q : ℕ) : ℝ) - 2)
      ≤ 3 ^ s.primeFactors.card * (2 * Salt.Maynard.phiAtomSum R W') ^ (k - 1) := by
  classical
  set pf := s.primeFactors.attach with hpf
  set box1 := (kSieveIndex k R W').filter (fun u => u m = 1) with hbox1
  set wt : (Fin k → ℕ) → ℝ := fun u => 1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ) with hwt
  have hwtnn : ∀ u, 0 ≤ wt u := fun u => by rw [hwt]; positivity
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPASnn : 0 ≤ PAS := by
    rw [hPAS]; unfold Salt.Maynard.phiAtomSum; exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hPprime : ∀ p ∈ s.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  set Bσ : (Fin k → ℕ) → Finset {x // x ∈ s.primeFactors} := fun u =>
    pf.filter (fun q => (q : ℕ) ∣ u ((α q.1 q.2).1)) with hBσ
  set Bτ : (Fin k → ℕ) → Finset {x // x ∈ s.primeFactors} := fun u =>
    pf.filter (fun q => (q : ℕ) ∣ u ((α q.1 q.2).2)) with hBτ
  -- fiber map
  have hmaps : ∀ u ∈ box1, (Bσ u, Bτ u) ∈ pf.powerset ×ˢ pf.powerset := by
    intro u _
    rw [Finset.mem_product]
    exact ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun u => wt u * ∏ q ∈ s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
          ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
        (((q : ℕ) : ℝ) - 2))]
  -- per fiber (S,T) bound
  have hfiber : ∀ ST ∈ pf.powerset ×ˢ pf.powerset,
      (∑ u ∈ box1.filter (fun u => (Bσ u, Bτ u) = ST),
        wt u * ∏ q ∈ s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
            (((q : ℕ) : ℝ) - 2))
        ≤ (if Disjoint ST.1 ST.2 then (2 * PAS) ^ (k - 1) else 0) := by
    intro ST hST
    obtain ⟨S, T⟩ := ST
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hST
    obtain ⟨hSpf, hTpf⟩ := hST
    simp only
    -- Bσ(u), Bτ(u) are always disjoint (a prime divides ≤ 1 box coord, and slots differ)
    have hBdisj : ∀ u ∈ box1, Disjoint (Bσ u) (Bτ u) := by
      intro u hu
      rw [hbox1, Finset.mem_filter] at hu
      rw [Finset.disjoint_left]; intro q hqσ hqτ
      rw [hBσ, Finset.mem_filter] at hqσ; rw [hBτ, Finset.mem_filter] at hqτ
      have hslots : (α q.1 q.2).1 ≠ (α q.1 q.2).2 := by
        have hmem := (Finset.mem_pi.mp hα) q.1 q.2
        rw [Finset.mem_offDiag] at hmem; exact hmem.2.2
      exact hslots (prime_dvd_coord_unique hu.1 (hPprime _ q.2) hqσ.2 hqτ.2)
    by_cases hdisj : Disjoint S T
    · rw [if_pos hdisj]
      rcases (box1.filter (fun u => (Bσ u, Bτ u) = (S, T))).eq_empty_or_nonempty
        with hempty | ⟨u₀, hu₀⟩
      · rw [hempty, Finset.sum_empty]; positivity
      · rw [Finset.mem_filter] at hu₀
        obtain ⟨hu₀box1, hu₀eq⟩ := hu₀
        have hSeq : S = Bσ u₀ := (Prod.ext_iff.mp hu₀eq).1.symm
        have hTeq : T = Bτ u₀ := (Prod.ext_iff.mp hu₀eq).2.symm
        -- primes of S ∪ T exceed D (they divide a box coord of u₀)
        have hSTbig : ∀ q ∈ S ∪ T, D < (q : ℕ) := by
          intro q hq
          rw [Finset.mem_union] at hq
          rw [hbox1, Finset.mem_filter] at hu₀box1
          rcases hq with hq | hq
          · rw [hSeq, hBσ, Finset.mem_filter] at hq
            exact D_lt_of_prime_dvd_coordW hDW hu₀box1.1 (hPprime _ q.2) hq.2
          · rw [hTeq, hBτ, Finset.mem_filter] at hq
            exact D_lt_of_prime_dvd_coordW hDW hu₀box1.1 (hPprime _ q.2) hq.2
        set Q : Finset ℕ := (S ∪ T).image Subtype.val with hQ
        set slotf : ℕ → Fin k := fun p =>
          if hp : p ∈ s.primeFactors then
            (if (⟨p, hp⟩ : {x // x ∈ s.primeFactors}) ∈ S then (α p hp).1 else (α p hp).2)
          else m with hslotf
        have hQmem : ∀ p ∈ Q, ∃ hp : p ∈ s.primeFactors,
            (⟨p, hp⟩ : {x // x ∈ s.primeFactors}) ∈ S ∪ T := by
          intro p hp
          rw [hQ] at hp
          obtain ⟨q, hqST, hqe⟩ := Finset.mem_image.mp hp
          have hpp : p ∈ s.primeFactors := hqe ▸ q.2
          refine ⟨hpp, ?_⟩
          have hqq : (⟨p, hpp⟩ : {x // x ∈ s.primeFactors}) = q := Subtype.ext hqe.symm
          rw [hqq]; exact hqST
        -- box_marked_gmoment hyps
        have hslotne : ∀ p ∈ Q, slotf p ≠ m := by
          intro p hp
          obtain ⟨hp', _⟩ := hQmem p hp
          rw [hslotf]; simp only [dif_pos hp']
          split_ifs
          · exact hfstne ⟨p, hp'⟩
          · exact hsndne ⟨p, hp'⟩
        have hQprime : ∀ p ∈ Q, p.Prime := by
          intro p hp; obtain ⟨hp', _⟩ := hQmem p hp; exact hPprime p hp'
        have hQdlt : ∀ p ∈ Q, D < p := by
          intro p hp; obtain ⟨hp', hpST⟩ := hQmem p hp; exact hSTbig _ hpST
        have hbmg := box_marked_gmoment_gen k R W' D m Q slotf hslotne hQprime hQdlt hW' hpos
          (by omega) hDW hR2
        -- the marked set matches: box.filter(uₘ=1 ∧ ∀p∈Q, p∣u(slotf p)) ⊇ fiber
        have hsubset : box1.filter (fun u => (Bσ u, Bτ u) = (S, T))
            ⊆ (kSieveIndex k R W').filter
                (fun u => u m = 1 ∧ ∀ p ∈ Q, p ∣ u (slotf p)) := by
          intro u hu
          rw [Finset.mem_filter, hbox1, Finset.mem_filter] at hu
          obtain ⟨⟨hubox, hum⟩, hueq⟩ := hu
          rw [Finset.mem_filter]
          refine ⟨hubox, hum, ?_⟩
          intro p hp
          obtain ⟨hp', hpST⟩ := hQmem p hp
          have hBσu : Bσ u = S := (Prod.ext_iff.mp hueq).1
          have hBτu : Bτ u = T := (Prod.ext_iff.mp hueq).2
          rw [hslotf]; simp only [dif_pos hp']
          rw [Finset.mem_union] at hpST
          split_ifs with hin
          · -- ⟨p,hp'⟩ ∈ S = Bσ u ⇒ p ∣ u ((α p hp').1)
            have : (⟨p, hp'⟩ : {x // x ∈ s.primeFactors}) ∈ Bσ u := hBσu ▸ hin
            rw [hBσ, Finset.mem_filter] at this; exact this.2
          · -- ⟨p,hp'⟩ ∈ T = Bτ u
            rcases hpST with h | h
            · exact absurd h hin
            · have : (⟨p, hp'⟩ : {x // x ∈ s.primeFactors}) ∈ Bτ u := hBτu ▸ h
              rw [hBτ, Finset.mem_filter] at this; exact this.2
        -- CT_u = ∏_{S∪T}(q-2) on the fiber
        have hCTeq : ∀ u ∈ box1.filter (fun u => (Bσ u, Bτ u) = (S, T)),
            (∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)), (((q : ℕ) : ℝ) - 2))
              = ∏ q ∈ S ∪ T, (((q : ℕ) : ℝ) - 2) := by
          intro u hu
          rw [Finset.mem_filter] at hu
          have hBσu : Bσ u = S := (Prod.ext_iff.mp hu.2).1
          have hBτu : Bτ u = T := (Prod.ext_iff.mp hu.2).2
          congr 1
          rw [← hBσu, ← hBτu, hBσ, hBτ, ← Finset.filter_or]
        rw [Finset.sum_congr rfl (fun u hu => by rw [hCTeq u hu])]
        rw [← Finset.sum_mul]
        -- ∏_{S∪T}(q-2) ≠ 0 and = ∏_Q(p-2)
        have hprodQ : (∏ q ∈ S ∪ T, (((q : ℕ) : ℝ) - 2)) = ∏ p ∈ Q, ((p : ℝ) - 2) := by
          rw [hQ, Finset.prod_image (fun q₁ _ q₂ _ h => Subtype.ext h)]
        have hSTpos : (0:ℝ) < ∏ q ∈ S ∪ T, (((q : ℕ) : ℝ) - 2) := by
          apply Finset.prod_pos; intro q hq
          have := hSTbig q hq
          have : (D:ℝ) < ((q:ℕ):ℝ) := by exact_mod_cast this
          have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
          linarith
        calc (∑ u ∈ box1.filter (fun u => (Bσ u, Bτ u) = (S, T)),
              1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ))
              * ∏ q ∈ S ∪ T, (((q : ℕ) : ℝ) - 2)
            ≤ ((∏ p ∈ Q, ((p : ℝ) - 2)⁻¹) * (2 * PAS) ^ (k - 1))
                * ∏ q ∈ S ∪ T, (((q : ℕ) : ℝ) - 2) := by
              apply mul_le_mul_of_nonneg_right _ hSTpos.le
              refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
                (fun u _ _ => by rw [hwt] at hwtnn; positivity)) ?_
              rw [hPAS]; exact hbmg
          _ = (2 * PAS) ^ (k - 1) := by
              have hQ0 : (∏ p ∈ Q, ((p : ℝ) - 2)) ≠ 0 := hprodQ ▸ hSTpos.ne'
              rw [hprodQ, Finset.prod_inv_distrib, mul_right_comm, inv_mul_cancel₀ hQ0, one_mul]
    · rw [if_neg hdisj]
      rw [Finset.sum_eq_zero]
      intro u hu
      exfalso
      rw [Finset.mem_filter] at hu
      have hBσu : Bσ u = S := (Prod.ext_iff.mp hu.2).1
      have hBτu : Bτ u = T := (Prod.ext_iff.mp hu.2).2
      exact hdisj (hBσu ▸ hBτu ▸ hBdisj u hu.1)
  calc ∑ ST ∈ pf.powerset ×ˢ pf.powerset,
        ∑ u ∈ box1.filter (fun u => (Bσ u, Bτ u) = ST),
          wt u * ∏ q ∈ s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
              (((q : ℕ) : ℝ) - 2)
      ≤ ∑ ST ∈ pf.powerset ×ˢ pf.powerset, (if Disjoint ST.1 ST.2 then (2 * PAS) ^ (k
              - 1) else 0) :=
        Finset.sum_le_sum hfiber
    _ = 3 ^ s.primeFactors.card * (2 * PAS) ^ (k - 1) := by
        have hfactor : ∀ ST : Finset {x // x ∈ s.primeFactors} × Finset {x // x ∈ s.primeFactors},
            (if Disjoint ST.1 ST.2 then (2 * PAS) ^ (k - 1) else 0)
              = (if Disjoint ST.1 ST.2 then (1:ℝ) else 0) * (2 * PAS) ^ (k - 1) := by
          intro ST; split_ifs <;> ring
        rw [Finset.sum_congr rfl (fun ST _ => hfactor ST), ← Finset.sum_mul]
        congr 1
        rw [Finset.sum_product]
        have hinner : ∀ S ∈ pf.powerset,
            (∑ T ∈ pf.powerset, (if Disjoint S T then (1:ℝ) else 0))
              = (2:ℝ) ^ (pf \ S).card := by
          intro S hS
          rw [Finset.sum_boole]
          have hset : pf.powerset.filter (fun T => Disjoint S T) = (pf \ S).powerset := by
            ext T
            simp only [Finset.mem_filter, Finset.mem_powerset]
            constructor
            · rintro ⟨hTpf, hdisj⟩
              intro x hx
              rw [Finset.mem_sdiff]
              exact ⟨hTpf hx, fun hxS => (Finset.disjoint_left.mp hdisj) hxS hx⟩
            · intro hT
              refine ⟨hT.trans Finset.sdiff_subset, ?_⟩
              rw [Finset.disjoint_left]; intro x hxS hxT
              exact (Finset.mem_sdiff.mp (hT hxT)).2 hxS
          rw [hset, Finset.card_powerset]; push_cast; ring
        rw [Finset.sum_congr rfl hinner]
        have hprodadd : (∑ S ∈ pf.powerset, (2:ℝ) ^ (pf \ S).card)
            = ∏ _p ∈ pf, ((1:ℝ) + 2) := by
          rw [Finset.prod_add]
          apply Finset.sum_congr rfl
          intro S hS
          rw [Finset.prod_const_one, one_mul, Finset.prod_const]
        rw [hprodadd, Finset.prod_const, hpf, Finset.card_attach]
        norm_num

/-- **The pointwise S₂ inner bound at general `k`** — the full termwise + partition bound:
the S₂ inner form is `≤ 3^ω · ∏(p−2)⁻² · ((PAS+ε)²·(2·PAS)^(k−1))`. Combines the termwise
and partition bounds, with the whole-`s` vanishing cases (`σₘ ≠ 1 ∨ τₘ ≠ 1 ⇒` sum `= 0` via
`lamPhiContractM_eq_zero_of_coord_ne_one`). It is stated pointwise so that a comparison
`hQd` at a single `(W', D)` can be fed in directly (`s2_inner_y_gen`). -/
lemma s2_inner_termwise_gen (k : ℕ) (m : Fin k)
    (R W' D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hyB : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (hR2 : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W')
    (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hDk : 12 * k ^ 2 ≤ D)
    {s : ℕ} (hs : Squarefree s)
    (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k) (hα : α ∈ assignments k s) :
    |∑ u ∈ kSieveIndex k R W', (∏ i, (gMult (u i) : ℝ))
        * lamPhiContractM k R W' m y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
        * lamPhiContractM k R W' m y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))|
      ≤ 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2)
          * ((Salt.Maynard.phiAtomSum R W' + lemma53Const * (k : ℝ) * Real.log R / D) ^ 2
              * (2 * Salt.Maynard.phiAtomSum R W') ^ (k - 1)) := by
  classical
  have hD3 : 3 ≤ D := le_trans (by nlinarith [m.pos] : 3 ≤ 12 * k ^ 2) hDk
  set V := lamPhiContractM k R W' m y with hVdef
  set PE : ℝ := Salt.Maynard.phiAtomSum R W' + lemma53Const * (k : ℝ) * Real.log R / D with hPEdef
  set K : ℝ := ∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2 with hKdef
  have hPASnn : 0 ≤ Salt.Maynard.phiAtomSum R W' := by
    unfold Salt.Maynard.phiAtomSum; exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hPE0 : 0 ≤ PE := by
    rw [hPEdef]
    have h2 : 0 ≤ lemma53Const * (k : ℝ) * Real.log R / D :=
      div_nonneg (mul_nonneg (mul_nonneg lemma53Const_nonneg (Nat.cast_nonneg _))
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R)))) (by positivity)
    linarith
  have hKnn : 0 ≤ K := Finset.prod_nonneg fun p _ => sq_nonneg _
  -- σ m = 1 extraction ⇒ slots ≠ m
  by_cases hcase : slotProd s α Prod.fst m = 1 ∧ slotProd s α Prod.snd m = 1
  · obtain ⟨hσm1, hτm1⟩ := hcase
    have hslotm : ∀ (sel : Fin k × Fin k → Fin k), slotProd s α sel m = 1 →
        ∀ (q : {x // x ∈ s.primeFactors}), sel (α q.1 q.2) ≠ m := by
      intro sel hsm q hbad
      have hpdvd : (q : ℕ) ∣ slotProd s α sel m :=
        (prime_dvd_slotProd_iff α sel (Nat.prime_of_mem_primeFactors q.2) m).mpr ⟨q.2, hbad⟩
      rw [hsm] at hpdvd
      exact (Nat.prime_of_mem_primeFactors q.2).one_lt.ne' (Nat.dvd_one.mp hpdvd)
    have hfstne : ∀ q : {x // x ∈ s.primeFactors}, (α q.1 q.2).1 ≠ m := hslotm Prod.fst hσm1
    have hsndne : ∀ q : {x // x ∈ s.primeFactors}, (α q.1 q.2).2 ≠ m := hslotm Prod.snd hτm1
    -- drop uₘ ≠ 1 terms (V(u∨σ) = 0 since (u∨σ)ₘ = uₘ ≠ 1)
    have hdrop : (∑ u ∈ kSieveIndex k R W', (∏ i, (gMult (u i) : ℝ))
          * V (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
          * V (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i)))
        = ∑ u ∈ (kSieveIndex k R W').filter (fun u => u m = 1), (∏ i, (gMult (u i) : ℝ))
          * V (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
          * V (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i)) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u hu hunf
      have hum : u m ≠ 1 := fun h => hunf (Finset.mem_filter.mpr ⟨hu, h⟩)
      have hV0 : V (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i)) = 0 := by
        apply lamPhiContractM_eq_zero_of_coord_ne_one
        show Nat.lcm (u m) (slotProd s α Prod.fst m) ≠ 1
        rw [hσm1, Nat.lcm_one_right]; exact hum
      rw [hV0]; ring
    rw [hdrop]
    calc |∑ u ∈ (kSieveIndex k R W').filter (fun u => u m = 1), (∏ i, (gMult (u i) : ℝ))
            * V (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            * V (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))|
        ≤ ∑ u ∈ (kSieveIndex k R W').filter (fun u => u m = 1),
            |(∏ i, (gMult (u i) : ℝ))
              * V (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
              * V (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ (kSieveIndex k R W').filter (fun u => u m = 1),
            (K * PE ^ 2) * ((1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ))
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 2)) := by
          apply Finset.sum_le_sum
          intro u hu
          rw [Finset.mem_filter] at hu
          have hterm
                  := s2_term_bound k m R W' D y hyB hysupp hR2 hW' hpos hDW hDk hs α hα u hu.1 hu.2
          -- s2_term_bound's K is ∏_{attach}(q-2)⁻¹^2 = K (prod_attach)
          have hKeq : (∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 2)⁻¹ ^ 2) = K := by
            rw [hKdef]; exact Finset.prod_attach s.primeFactors (fun p => (((p:ℝ)-2)⁻¹)^2)
          rw [hKeq] at hterm
          exact hterm
      _ = (K * PE ^ 2) * ∑ u ∈ (kSieveIndex k R W').filter (fun u => u m = 1),
            ((1 / ∏ i ∈ Finset.univ.erase m, (gMult (u i) : ℝ))
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 2)) := by rw [Finset.mul_sum]
      _ ≤ (K * PE ^ 2) * (3 ^ s.primeFactors.card * (2 * Salt.Maynard.phiAtomSum R W') ^ (k
              - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact s2_part_bound k R W' D hR2 hW' hpos hDW hD3 m hs α hα hfstne hsndne
      _ = 3 ^ s.primeFactors.card * K
            * (PE ^ 2 * (2 * Salt.Maynard.phiAtomSum R W') ^ (k - 1)) := by ring
  · -- σₘ ≠ 1 or τₘ ≠ 1 ⇒ the whole sum is 0
    have hsum0 : (∑ u ∈ kSieveIndex k R W', (∏ i, (gMult (u i) : ℝ))
          * V (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
          * V (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))) = 0 := by
      apply Finset.sum_eq_zero; intro u _
      rw [not_and_or] at hcase
      rcases hcase with h | h
      · have hV0 : V (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i)) = 0 := by
          apply lamPhiContractM_eq_zero_of_coord_ne_one
          show Nat.lcm (u m) (slotProd s α Prod.fst m) ≠ 1
          intro hc
          exact h (Nat.dvd_one.mp (hc ▸ Nat.dvd_lcm_right _ _))
        rw [hV0]; ring
      · have hV0 : V (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i)) = 0 := by
          apply lamPhiContractM_eq_zero_of_coord_ne_one
          show Nat.lcm (u m) (slotProd s α Prod.snd m) ≠ 1
          intro hc
          exact h (Nat.dvd_one.mp (hc ▸ Nat.dvd_lcm_right _ _))
        rw [hV0]; ring
    rw [hsum0, abs_zero]
    positivity

/-- **B4.3b — a bounded weight `y` satisfies the S₂ inner atom at general `k`.**
Termwise + contamination partition (`s2_inner_termwise_gen`) plus the step-(d)
payload `hQd : (PAS + ε)²·(2·PAS)^{k−1} ≤ CF·Qdiag_gv k R W' m y`,
`ε = lemma53Const·k·log R/D`. -/
theorem s2_inner_y_gen (k R W' D : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hyB : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R W' → y s = 0)
    (hR2 : 2 ≤ R) (hW' : Squarefree W') (hpos : 0 < W')
    (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hDk : 12 * k ^ 2 ≤ D) (CF : ℝ)
    (hQd : (Salt.Maynard.phiAtomSum R W' + lemma53Const * (k : ℝ) * Real.log R / D) ^ 2
            * (2 * Salt.Maynard.phiAtomSum R W') ^ (k - 1)
          ≤ CF * Qdiag_gv k R W' m y) :
    S2InnerBoundQC k R W' m y CF := by
  intro s hs α hα
  have htw := s2_inner_termwise_gen k m R W' D y hyB hysupp hR2 hW' hpos hDW hDk hs α hα
  refine le_trans htw ?_
  have hA : (0 : ℝ) ≤ 3 ^ s.primeFactors.card
      * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2) := by positivity
  have hreassoc : 3 ^ s.primeFactors.card
        * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2) * CF * Qdiag_gv k R W' m y
      = (3 ^ s.primeFactors.card * (∏ p ∈ s.primeFactors, (((p : ℝ) - 2)⁻¹) ^ 2))
          * (CF * Qdiag_gv k R W' m y) := by ring
  rw [hreassoc]
  exact mul_le_mul_of_nonneg_left hQd hA

end Salt.MaynardK

