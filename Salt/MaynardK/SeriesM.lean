/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Series
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.Nat.Factorial.BigOperators

open Finset Nat Salt.Twelve

namespace Salt.MaynardK

/-!
# C1 bridge B1 at general `M` — the series `GM` and the table `TM`

The `M`-variable generalisation of `Series` (`G`, `symCollect`, `T`, `T_eq_coeff`), for bases
`(1 − P₁)^a · Π_{m < M} P_{2(m+1)}^{C m}` in place of `(1 − P₁)^b · P₂^c`.

* `weight C = Σ_m 2(m+1)·C m` is the degree of `Π_m P_{2(m+1)}^{C m}`;
* `GM M` is the `M`-variable series with `[x^j] GM = (weight j)! / Π_m (j m)!` (`coeff_GM`);
* `symCollectM`: the Dirichlet main term (`DInt'`) of `(1 − P₁)^a · Π_m P_{2(m+1)}^{C m}`, summed
  over its multinomial expansion, is `a!·Π_m (C m)!·[x^C] GM^k / (k + a + weight C)!`;
* `TM M k wmax` is a computable list table of `[x^C] GM^k` for `weight C ≤ wmax`, keyed by the
  base-64 code `enc C`; `T_eq_coeffM` states that its lookups are those coefficients.

At `M = 1` these are `G`, `symCollect`, `T` and `T_eq_coeff` (the controls are in
`ControlsSeriesM`). Pure polynomial and series algebra: nothing here bears on twin primes.
-/

/-! ## The weight and the series `GM` -/

/-- The weight of an exponent vector, `Σ_m 2(m+1)·j m`: the degree of `Π_m P_{2(m+1)}^{j m}`. -/
def weight {M : ℕ} (j : Fin M → ℕ) : ℕ := ∑ m : Fin M, 2 * ((m : ℕ) + 1) * j m

/-- `GM M = Σ_j (weight j)! / Π_m (j m)! · xʲ`, the `M`-variable twin of `G`. -/
noncomputable def GM (M : ℕ) : MvPowerSeries (Fin M) ℚ :=
  fun j => (((weight ⇑j)! : ℕ) : ℚ) / ∏ m, (((j m)! : ℕ) : ℚ)

theorem coeff_GM {M : ℕ} (j : Fin M →₀ ℕ) :
    MvPowerSeries.coeff j (GM M) = (((weight ⇑j)! : ℕ) : ℚ) / ∏ m, (((j m)! : ℕ) : ℚ) := rfl

lemma two_mul_le_weight {M : ℕ} (C : Fin M → ℕ) (m : Fin M) : 2 * C m ≤ weight C := by
  have h : 2 * ((m : ℕ) + 1) * C m = 2 * C m + 2 * (m : ℕ) * C m := by ring
  calc 2 * C m ≤ 2 * ((m : ℕ) + 1) * C m := by rw [h]; exact Nat.le_add_right _ _
    _ ≤ weight C :=
      Finset.single_le_sum (f := fun m : Fin M => 2 * ((m : ℕ) + 1) * C m)
        (fun _ _ => Nat.zero_le _) (mem_univ m)

lemma weight_mono {M : ℕ} {A C : Fin M → ℕ} (h : ∀ m, A m ≤ C m) : weight A ≤ weight C :=
  Finset.sum_le_sum fun m _ => Nat.mul_le_mul_left _ (h m)

/-! ## B1(a′) at general `M` -/

/-- The transpose of an assignment tuple: `(trM e) i m = e m i`. -/
noncomputable def trM {M k : ℕ} (e : Fin M → (Fin k →₀ ℕ)) : Fin k →₀ (Fin M →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm fun i => Finsupp.equivFunOnFinite.symm fun m => e m i

lemma trM_apply {M k : ℕ} (e : Fin M → (Fin k →₀ ℕ)) (i : Fin k) (m : Fin M) :
    trM e i m = e m i := rfl

/-- **B1(a′) at general `M`** (Lemma 7.2 of Polymath8b reorganised): the Dirichlet main term of
`(1 − P₁)^a · Π_m P_{2(m+1)}^{C m}`, summed over its multinomial expansion (one antidiagonal per
`m`), equals `a!·Π_m (C m)!·[x^C] GM^k / (k + a + weight C)!`. At `M = 1` it is `symCollect`. -/
theorem symCollectM (M k a : ℕ) (C : Fin M → ℕ) :
    ∑ e ∈ Fintype.piFinset (fun m => finsuppAntidiag (univ : Finset (Fin k)) (C m)),
        (∏ m, (((C m)! : ℕ) : ℚ) / ∏ i, (((e m i)! : ℕ) : ℚ)) *
          DInt' (fun i => ∑ m : Fin M, 2 * ((m : ℕ) + 1) * e m i) a
      = ((a ! : ℕ) : ℚ) * (∏ m, (((C m)! : ℕ) : ℚ)) *
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm C) (GM M ^ k)
          / (((k + a + weight C)! : ℕ) : ℚ) := by
  have hG : GM M ^ k = ∏ _i : Fin k, GM M := by rw [Finset.prod_const, Finset.card_fin]
  rw [hG, MvPowerSeries.coeff_prod, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_nbij' trM (fun l m => Finsupp.equivFunOnFinite.symm fun i => l i m)
    ?_ ?_ ?_ ?_ ?_
  · intro e he
    rw [Fintype.mem_piFinset] at he
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    ext m
    rw [Finsupp.finsetSum_apply]
    simp only [trM_apply, Finsupp.coe_equivFunOnFinite_symm]
    exact (mem_finsuppAntidiag.mp (he m)).1
  · intro l hl
    rw [mem_finsuppAntidiag] at hl
    rw [Fintype.mem_piFinset]
    intro m
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    have h := DFunLike.congr_fun hl.1 m
    rw [Finsupp.finsetSum_apply] at h
    simpa [Finsupp.coe_equivFunOnFinite_symm] using h
  · intro e _
    funext m
    ext i
    rfl
  · intro l _
    ext i m
    rfl
  · intro e he
    rw [Fintype.mem_piFinset] at he
    have hsum : ∀ m, ∑ i, e m i = C m := fun m => (mem_finsuppAntidiag.mp (he m)).1
    have hw : ∑ i, ∑ m : Fin M, 2 * ((m : ℕ) + 1) * e m i = weight C := by
      rw [Finset.sum_comm]
      unfold weight
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.mul_sum, hsum m]
    have hcoe : ∀ i, ⇑(trM e i) = fun m => e m i := fun i => rfl
    have hwi : ∀ i, weight (fun m => e m i) = ∑ m : Fin M, 2 * ((m : ℕ) + 1) * e m i :=
      fun i => rfl
    simp only [coeff_GM, hcoe, hwi]
    unfold DInt'
    simp only [hw]
    have hpos : ∀ m i, (((e m i)! : ℕ) : ℚ) ≠ 0 := fun m i => by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hD : (((k + a + weight C)! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hP : (∏ i, ∏ m, (((e m i)! : ℕ) : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun m _ => hpos m i
    have hcomm : (∏ m, ∏ i, (((e m i)! : ℕ) : ℚ)) = ∏ i, ∏ m, (((e m i)! : ℕ) : ℚ) :=
      Finset.prod_comm
    push_cast
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib, hcomm]
    field_simp
    try ring

/-! ## B1(b) at general `M`: the computable table `TM` -/

/-- Base-64 digits from position `0`. -/
def enc0 {M : ℕ} (C : Fin M → ℕ) : ℕ := ∑ m : Fin M, C m * 64 ^ (m : ℕ)

/-- The table key of an exponent vector, `enc C = Σ_m C m · 64^(m+1)` (the code A1's emitter uses).
It is injective on the keys the table meets: `weight C ≤ wmax` gives `2·C m ≤ wmax`, so every digit
is `< 64` whenever `wmax ≤ 127` (at the certificate's `wmax = 46, 48`, `C m ≤ 24`), and base-64
digits below `64` determine the vector (`enc_injective`). -/
def enc {M : ℕ} (C : Fin M → ℕ) : ℕ := ∑ m : Fin M, C m * 64 ^ ((m : ℕ) + 1)

lemma enc_eq {M : ℕ} (C : Fin M → ℕ) : enc C = 64 * enc0 C := by
  unfold enc enc0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma enc0_succ {M : ℕ} (C : Fin (M + 1) → ℕ) : enc0 C = C 0 + 64 * enc0 (Fin.tail C) := by
  unfold enc0
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, Fin.tail]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma enc0_inj {M : ℕ} (C D : Fin M → ℕ) (hC : ∀ m, C m < 64) (hD : ∀ m, D m < 64)
    (h : enc0 C = enc0 D) : C = D := by
  induction M with
  | zero => funext m; exact m.elim0
  | succ M ih =>
    rw [enc0_succ, enc0_succ] at h
    have hc0 := hC 0
    have hd0 := hD 0
    have h0 : C 0 = D 0 := by omega
    have ht : enc0 (Fin.tail C) = enc0 (Fin.tail D) := by omega
    have htail := ih (Fin.tail C) (Fin.tail D) (fun m => hC _) (fun m => hD _) ht
    funext m
    refine Fin.cases ?_ (fun j => ?_) m
    · exact h0
    · exact congrFun htail j

lemma lt_64_of_weight {M wmax : ℕ} (hw : wmax ≤ 127) {C : Fin M → ℕ} (hC : weight C ≤ wmax)
    (m : Fin M) : C m < 64 := by
  have := two_mul_le_weight C m
  omega

theorem enc_injective {M wmax : ℕ} (hw : wmax ≤ 127) {C D : Fin M → ℕ}
    (hC : weight C ≤ wmax) (hD : weight D ≤ wmax) (h : enc C = enc D) : C = D := by
  rw [enc_eq, enc_eq] at h
  exact enc0_inj C D (lt_64_of_weight hw hC) (lt_64_of_weight hw hD) (by omega)

/-- All vectors with every entry `≤ b`. -/
def allLE : (M : ℕ) → ℕ → List (Fin M → ℕ)
  | 0, _ => [fun i => i.elim0]
  | M + 1, b => (List.range (b + 1)).flatMap fun c =>
      (allLE M b).map fun v => (Fin.cons c v : Fin (M + 1) → ℕ)

lemma mem_allLE {M b : ℕ} (C : Fin M → ℕ) (hC : ∀ m, C m ≤ b) : C ∈ allLE M b := by
  induction M with
  | zero =>
    simp only [allLE, List.mem_singleton]
    funext i
    exact i.elim0
  | succ M ih =>
    simp only [allLE, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨C 0, by have := hC 0; omega, Fin.tail C, ih _ (fun m => hC _),
      Fin.cons_self_tail C⟩

/-- The table's keys: every exponent vector of weight `≤ wmax`. -/
def keysM (M wmax : ℕ) : List (Fin M → ℕ) :=
  (allLE M (wmax / 2)).filter fun C => weight C ≤ wmax

lemma mem_keysM {M wmax : ℕ} {C : Fin M → ℕ} : C ∈ keysM M wmax ↔ weight C ≤ wmax := by
  unfold keysM
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨mem_allLE C fun m => by have := two_mul_le_weight C m; omega, h⟩

/-- `[x^B] GM` as a natural number: `(weight B)! / Π_m (B m)!` (an exact quotient, `gN_cast`). -/
def gN {M : ℕ} (B : Fin M → ℕ) : ℕ := (weight B)! / ∏ m, (B m)!

lemma gN_cast {M : ℕ} (B : Fin M → ℕ) :
    ((gN B : ℕ) : ℚ) = (((weight B)! : ℕ) : ℚ) / ∏ m, (((B m)! : ℕ) : ℚ) := by
  have hle : ∑ m, B m ≤ weight B := by
    unfold weight
    refine Finset.sum_le_sum fun m _ => ?_
    have h : 2 * ((m : ℕ) + 1) * B m = B m + (2 * (m : ℕ) + 1) * B m := by ring
    rw [h]
    exact Nat.le_add_right _ _
  have hdvd : ∏ m, (B m)! ∣ (weight B)! :=
    (Nat.prod_factorial_dvd_factorial_sum univ B).trans (Nat.factorial_dvd_factorial hle)
  have hpos : ((∏ m, (B m)! : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos fun m _ => Nat.factorial_pos (B m)).ne'
  unfold gN
  rw [Nat.cast_div hdvd hpos, Nat.cast_prod]

/-- The box `{A | A ≤ C}`. -/
def boxM {M : ℕ} (C : Fin M → ℕ) : Finset (Fin M → ℕ) :=
  Fintype.piFinset fun m => range (C m + 1)

/-- One truncated multiplication by `GM`: `[x^C] (P · GM) = Σ_{A ≤ C} [x^A] P · [x^{C−A}] GM`,
reading `[x^A] P` from the previous table. -/
def tstep {M : ℕ} (prev : List (ℕ × ℕ)) (C : Fin M → ℕ) : ℕ :=
  ∑ A ∈ boxM C, (prev.lookup (enc A)).getD 0 * gN (C - A)

/-- `TM M k wmax`: the table of `[x^C] GM^k` over the keys `weight C ≤ wmax`, as `(enc C, value)`
pairs — the `M`-variable twin of `T k`. -/
def TM (M : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, wmax => (keysM M wmax).map fun C => (enc C, if C = 0 then 1 else 0)
  | k + 1, wmax => (keysM M wmax).map fun C => (enc C, tstep (TM M k wmax) C)

lemma lookup_map_key {α : Type*} (key : α → ℕ) (f : α → ℕ) (x : α) :
    ∀ l : List α, x ∈ l → (∀ y ∈ l, key y = key x → y = x) →
      (l.map fun y => (key y, f y)).lookup (key x) = some (f x)
  | [], hx, _ => by simp at hx
  | y :: l, hx, hinj => by
    by_cases hk : key x = key y
    · have hyx := hinj y List.mem_cons_self hk.symm
      subst hyx
      simp
    · have hne : (key x == key y) = false := by simpa using hk
      have hx' : x ∈ l := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd (congrArg key h) hk
        · exact h
      simp only [List.map_cons, List.lookup_cons, hne]
      exact lookup_map_key key f x l hx' fun z hz => hinj z (List.mem_cons_of_mem _ hz)

lemma lookup_keysM {M wmax : ℕ} (hw : wmax ≤ 127) (f : (Fin M → ℕ) → ℕ) {C : Fin M → ℕ}
    (hC : weight C ≤ wmax) :
    ((keysM M wmax).map fun D => (enc D, f D)).lookup (enc C) = some (f C) :=
  lookup_map_key enc f C _ (mem_keysM.mpr hC)
    fun _ hD he => enc_injective hw (mem_keysM.mp hD) hC he

lemma TM_zero_lookup {M wmax : ℕ} (hw : wmax ≤ 127) {C : Fin M → ℕ} (hC : weight C ≤ wmax) :
    (TM M 0 wmax).lookup (enc C) = some (if C = 0 then 1 else 0) :=
  lookup_keysM hw (fun C => if C = 0 then 1 else 0) hC

lemma TM_succ_lookup {M k wmax : ℕ} (hw : wmax ≤ 127) {C : Fin M → ℕ} (hC : weight C ≤ wmax) :
    (TM M (k + 1) wmax).lookup (enc C) = some (tstep (TM M k wmax) C) :=
  lookup_keysM hw (fun C => tstep (TM M k wmax) C) hC

/-- **B1(b) at general `M`**, Option-correct: every key of weight `≤ wmax` is present in the
table, and its value is `[x^C] GM^k`. At `M = 1` it is `T_eq_coeff`. -/
theorem T_eq_coeffM (M k wmax : ℕ) (hw : wmax ≤ 127) :
    ∀ C : Fin M → ℕ, weight C ≤ wmax → ∃ n, (TM M k wmax).lookup (enc C) = some n ∧
      (n : ℚ) = MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm C) (GM M ^ k) := by
  induction k with
  | zero =>
    intro C hC
    refine ⟨_, TM_zero_lookup hw hC, ?_⟩
    rw [pow_zero, MvPowerSeries.coeff_one]
    have hiff : Finsupp.equivFunOnFinite.symm C = 0 ↔ C = 0 := by
      constructor
      · intro h
        funext m
        exact DFunLike.congr_fun h m
      · intro h
        subst h
        ext m
        rfl
    by_cases h : C = 0
    · simp only [if_pos h, if_pos (hiff.mpr h), Nat.cast_one]
    · simp only [if_neg h, if_neg (mt hiff.mp h), Nat.cast_zero]
  | succ k ih =>
    intro C hC
    refine ⟨_, TM_succ_lookup hw hC, ?_⟩
    rw [pow_succ, MvPowerSeries.coeff_mul]
    unfold tstep
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun A => (Finsupp.equivFunOnFinite.symm A,
        Finsupp.equivFunOnFinite.symm (C - A))) (fun p => ⇑p.1) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      rw [boxM, Fintype.mem_piFinset] at hA
      rw [Finset.mem_antidiagonal]
      ext m
      have := Finset.mem_range.mp (hA m)
      simp only [Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm, Pi.sub_apply]
      omega
    · intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rw [boxM, Fintype.mem_piFinset]
      intro m
      have := DFunLike.congr_fun hp m
      simp only [Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm] at this
      rw [Finset.mem_range]
      omega
    · intro A _
      rfl
    · intro p hp
      rw [Finset.mem_antidiagonal] at hp
      refine Prod.ext (Finsupp.equivFunOnFinite_symm_coe _) ?_
      ext m
      have := DFunLike.congr_fun hp m
      simp only [Finsupp.add_apply, Finsupp.coe_equivFunOnFinite_symm] at this
      simp only [Finsupp.coe_equivFunOnFinite_symm, Pi.sub_apply]
      omega
    · intro A hA
      rw [boxM, Fintype.mem_piFinset] at hA
      have hle : ∀ m, A m ≤ C m := fun m => by have := Finset.mem_range.mp (hA m); omega
      obtain ⟨n, hn, hn'⟩ := ih A ((weight_mono hle).trans hC)
      dsimp only
      rw [hn, Option.getD_some, Nat.cast_mul, hn', gN_cast, coeff_GM]
      try rfl

/-- `T_eq_coeffM` in the `getD` form. -/
theorem T_eq_coeffM_getD (M k wmax : ℕ) (hw : wmax ≤ 127) (C : Fin M → ℕ)
    (hC : weight C ≤ wmax) :
    ((((TM M k wmax).lookup (enc C)).getD 0 : ℕ) : ℚ)
      = MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm C) (GM M ^ k) := by
  obtain ⟨n, hn, hn'⟩ := T_eq_coeffM M k wmax hw C hC
  rw [hn, Option.getD_some, hn']

end Salt.MaynardK
