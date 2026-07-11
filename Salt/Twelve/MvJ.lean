/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.BudgetMoment
import Salt.Twelve.W3Prep
import Salt.Maynard.KSieve
import Salt.Twelve.MvMomentG
import Salt.Twelve.MvMoment
import Salt.Twelve.BudgetMomentG
import Salt.Twelve.BudgetPoly

/-!
# W3-5 (inner contraction) — `Salt/Twelve/MvJ.lean` (blueprint P3, card W3-5)

The `∫dtₘ` peel of a single sieve coordinate `m`.  For a fixed outer tuple
`r ∈ kSieveIndex 5 R W'` with `r m = 1`, the inner one-dimensional sum

  `∑_{u < R} yF R W' F (update r m u) / φ(u)`

is a one-dimensional budget moment at the ℕ-cap `z_r = (R−1)/∏r + 1` with the
extra coprimality constraint `u ⊥ ∏r`.  Dropping that constraint (its cost is
the r-dependent marked-prime error budget), applying `budget_moment` per
monomial at `(c, b) = (α m, 0)`, and converting the ℕ-cap back to the real
budget `log R − log ∏r` via `log_natCap_slip`, the main term reassembles into
`X · eval (contractAt m F) t'`, `X = (φW'/W')·log R`,
`t' i = log (r (m.succAbove i)) / log R`.

`inner_contract` is the per-`r` estimate; node W3-6 (`mv_J`) squares it and sums
the 4-dim g-weighted outer sum.
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-- **Frozen definition (card W3-5).** The explicit12 sieve weight: `F`
evaluated at `t(s)`, supported on the sieve box. -/
noncomputable def yF (R W' : ℕ) (F : Poly) (s : Fin 5 → ℕ) : ℝ :=
  if s ∈ kSieveIndex 5 R W'
  then eval (ofPoly F) (fun i => Real.log (s i) / Real.log R) else 0

/-! ## List-sum plumbing -/

/-- Swap a `Finset` sum with an inner `List` sum. -/
private lemma sum_finset_list_sum {ι γ : Type*} (S : Finset ι) (L : List γ)
    (f : ι → γ → ℝ) :
    ∑ u ∈ S, (L.map (fun x => f u x)).sum = (L.map (fun x => ∑ u ∈ S, f u x)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

/-- Triangle inequality for a `List.sum` of reals. -/
private lemma list_abs_sum_le {γ : Type*} (L : List γ) (f : γ → ℝ) :
    |(L.map f).sum| ≤ (L.map (fun a => |f a|)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      calc |f a + (L.map f).sum| ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
        _ ≤ |f a| + (L.map (fun a => |f a|)).sum := by linarith [ih]

/-- Additivity of `List.sum` over a pointwise sum of the mapped functions. -/
private lemma list_sum_map_add {γ : Type*} (L : List γ) (f g : γ → ℝ) :
    (L.map (fun a => f a + g a)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ## Membership of the updated tuple in the sieve box -/

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

/-! ## A Lipschitz estimate for powers on the unit interval -/

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

/-! ## The one-dimensional inner-sum estimate -/

/-- The inner one-dimensional sum for a single monomial power `c`: it is the
budget moment at cap `z_r = (R−1)/∏r + 1` with the extra constraint `u ⊥ ∏r`.
Dropping that constraint (marked-prime error), applying `budget_moment` and the
floor-slip conversion, the main term is
`X · ((log R − log ∏r)/log R)^{c+1}/(c+1)`, with an absolute error plus an
r-dependent marked-prime error `∑_{p ∣ ∏r} 1/(p−1)`. -/
private lemma inner_sum_estimate (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') {R : ℕ} (hR : 1 ≤ Real.log R)
    {r : Fin 5 → ℕ} (hr : r ∈ kSieveIndex 5 R W') {m : Fin 5} (hrm : r m = 1) (c : ℕ) :
    |(∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
      - ((W'.totient : ℝ) / W' * Real.log R)
          * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + 1) / ((c : ℝ) + 1)|
    ≤ (budget_moment W' hW' hpos hUpper c 0).choose * 4 ^ c + Real.log 2
      + (marked_sqf_phi W' hW' hpos c).choose * Real.log R
          * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
  classical
  obtain ⟨hCatom0, hbudgetspec⟩ := (budget_moment W' hW' hpos hUpper c 0).choose_spec
  obtain ⟨hCm0, hmarkedspec⟩ := (marked_sqf_phi W' hW' hpos c).choose_spec
  set Catom := (budget_moment W' hW' hpos hUpper c 0).choose with hCatomdef
  set Cm := (marked_sqf_phi W' hW' hpos c).choose with hCmdef
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
  -- The index-set identity: the sieve-box filter is the capped box with `u ⊥ ∏r`.
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
  -- Real-log facts on the cap.
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hzR' : Real.log (z : ℝ) ≤ Real.log R := Real.log_le_log hzpos (by exact_mod_cast hzR)
  have hzlog0 : (0 : ℝ) ≤ Real.log (z : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  have hQlog0 : (0 : ℝ) ≤ Real.log (∏ i, r i) :=
    Real.log_nonneg (by exact_mod_cast hQpos)
  have hQlogR : Real.log (∏ i, r i) ≤ Real.log R :=
    Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQltR.le)
  -- === The budget bound ===
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
  -- === The slip bound (main term A vs B) ===
  have hslip :
      |((Nat.totient W' : ℝ) / W' * Real.log R)
            * (Real.log z / Real.log R) ^ (c + 1) / ((c : ℝ) + 1)
        - ((Nat.totient W' : ℝ) / W' * Real.log R)
            * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + 1) / ((c : ℝ) + 1)|
      ≤ Real.log 2 := by
    set A := Real.log (z : ℝ) / Real.log R with hA
    set B := (Real.log R - Real.log (∏ i, r i)) / Real.log R with hB
    set X := (Nat.totient W' : ℝ) / W' * Real.log R with hX
    have hX0 : 0 ≤ X := by
      rw [hX]; positivity
    have hXle : X ≤ Real.log R := by
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
    calc |X * A ^ (c + 1) / ((c : ℝ) + 1) - X * B ^ (c + 1) / ((c : ℝ) + 1)|
        = (X / ((c : ℝ) + 1)) * |A ^ (c + 1) - B ^ (c + 1)| := by
          rw [show X * A ^ (c + 1) / ((c:ℝ)+1) - X * B ^ (c + 1) / ((c:ℝ)+1)
                = (X / ((c:ℝ)+1)) * (A ^ (c + 1) - B ^ (c + 1)) from by ring, abs_mul,
            abs_of_nonneg (div_nonneg hX0 (by positivity))]
      _ ≤ (X / ((c : ℝ) + 1)) * (((c + 1 : ℕ) : ℝ) * |A - B|) :=
            mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le_unit hA0 hA1 hB0 hB1 (c + 1))
              (div_nonneg hX0 (by positivity))
      _ ≤ (X / ((c : ℝ) + 1)) * (((c + 1 : ℕ) : ℝ) * (Real.log 2 / Real.log R)) := by
            apply mul_le_mul_of_nonneg_left _ (div_nonneg hX0 (by positivity))
            exact mul_le_mul_of_nonneg_left hAB (by positivity)
      _ = X / Real.log R * Real.log 2 := by
            have hcne : ((c:ℝ) + 1) ≠ 0 := by positivity
            have hLne : Real.log R ≠ 0 := ne_of_gt hLpos
            push_cast
            field_simp
      _ ≤ 1 * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
            rw [div_le_one hLpos]; exact hXle
      _ = Real.log 2 := one_mul _
  -- === The drop bound (marked primes) ===
  -- rewrite each summand to factor out `1/(log R)^c`.
  have hmarked_p : ∀ p ∈ (∏ i, r i).primeFactors,
      (∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
            (fun u => p ∣ u), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ Cm * Real.log R * (1 / ((p : ℝ) - 1)) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpQ, _⟩ := hp
    have hp0 : 0 < p := hpp.pos
    have hpge2 : 2 ≤ p := hpp.two_le
    -- the filtered set is the marked-sqf set
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
    -- factor out 1/(log R)^c
    have hfac : ∀ u : ℕ, (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ)
        = (1 / (Real.log R) ^ c) * ((Real.log u) ^ c / (Nat.totient u : ℝ)) := by
      intro u; rw [div_pow]; ring
    rw [Finset.sum_congr rfl (fun u _ => hfac u), ← Finset.mul_sum]
    have hmark := hmarkedspec p z hp0 hz2
    have hLcpos : (0 : ℝ) < (Real.log R) ^ c := pow_pos hLpos c
    have htotp : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.totient_prime hpp]; push_cast [Nat.cast_sub hp0]; ring
    calc (1 / (Real.log R) ^ c)
          * ∑ u ∈ (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W' ∧ p ∣ u),
              (Real.log u) ^ c / (Nat.totient u : ℝ)
        ≤ (1 / (Real.log R) ^ c) * ((1 / (Nat.totient p : ℝ)) * Cm * (Real.log z) ^ (c + 1)) := by
          apply mul_le_mul_of_nonneg_left hmark (by positivity)
      _ = (1 / ((p : ℝ) - 1)) * Cm * ((Real.log z) ^ (c + 1) / (Real.log R) ^ c) := by
          rw [htotp]; ring
      _ ≤ (1 / ((p : ℝ) - 1)) * Cm * Real.log R := by
          apply mul_le_mul_of_nonneg_left _ (by
            have : (0:ℝ) ≤ 1 / ((p:ℝ) - 1) := by
              apply div_nonneg zero_le_one; have : (2:ℝ) ≤ p := by exact_mod_cast hpge2
              linarith
            positivity)
          rw [div_le_iff₀ hLcpos]
          have hzc1 : (Real.log z) ^ (c + 1) ≤ (Real.log R) ^ (c + 1) :=
            pow_le_pow_left₀ hzlog0 hzR' (c + 1)
          calc (Real.log z) ^ (c + 1) ≤ (Real.log R) ^ (c + 1) := hzc1
            _ = Real.log R * (Real.log R) ^ c := by rw [pow_succ]; ring
      _ = Cm * Real.log R * (1 / ((p : ℝ) - 1)) := by ring
  -- assemble the drop bound via the covering by prime factors
  have hg0 : ∀ u : ℕ, (0 : ℝ) ≤ (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) := by
    intro u; positivity
  have hcover :
      (∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
            (fun u => ¬ u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ ∑ p ∈ (∏ i, r i).primeFactors,
            ∑ u ∈ ((Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W')).filter
              (fun u => p ∣ u), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) := by
    -- termwise: each `u` with ¬coprime has some prime factor of ∏r dividing it
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
        ≤ Cm * Real.log R * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
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
      _ ≤ ∑ p ∈ (∏ i, r i).primeFactors, Cm * Real.log R * (1 / ((p : ℝ) - 1)) :=
            Finset.sum_le_sum hmarked_p
      _ = Cm * Real.log R * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
            rw [Finset.mul_sum]
  -- === Combine ===
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
      ≤ Cm * Real.log R * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hSfull_le])]
    exact hdrop
  -- triangle inequality
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

/-! ## `eval` expansions and further list plumbing -/

/-- `eval (ofPoly F) t` as an explicit monomial `List.sum` (budget power `0`). -/
private lemma eval_ofPoly (F : Poly) (t : Fin 5 → ℝ) :
    eval (ofPoly F) t = (F.map (fun a => (a.2 : ℝ) * ∏ i, t i ^ a.1 i)).sum := by
  simp only [eval, ofPoly, List.map_map, Function.comp_def, pow_zero, mul_one]

/-- `eval (contractAt m F) t` as an explicit monomial `List.sum`, with the
`succAbove`-aligned exponents and the `αₘ+1` budget power. -/
private lemma eval_contractAt (m : Fin 5) (F : Poly) (t : Fin 4 → ℝ) :
    eval (contractAt m F) t
      = (F.map (fun a => ((a.2 / ((a.1 m + 1 : ℕ) : ℚ) : ℚ) : ℝ)
          * (∏ i, t i ^ a.1 (m.succAbove i)) * (1 - ∑ i, t i) ^ (a.1 m + 1))).sum := by
  simp only [eval, contractAt, List.map_map, Function.comp_def, Fin.removeNth_apply]

/-- The product `∏ᵢ (log (update r m u) i / RR)^{α i}` splits off the `m`-th
factor `(log u / RR)^{α m}`, leaving the `succAbove`-indexed constant. -/
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

/-- Division distributes into a mapped `List.sum`. -/
private lemma list_sum_div {γ : Type*} (L : List γ) (g : γ → ℝ) (c : ℝ) :
    (L.map g).sum / c = (L.map (fun a => g a / c)).sum := by
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]
  simp only [div_eq_mul_inv]

/-- Subtractivity of `List.sum` over a pointwise difference. -/
private lemma list_sum_map_sub {γ : Type*} (L : List γ) (f g : γ → ℝ) :
    (L.map f).sum - (L.map g).sum = (L.map (fun a => f a - g a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

/-- Monotonicity of `List.sum` under a pointwise `≤`. -/
private lemma list_sum_le_sum {γ : Type*} (L : List γ) (f g : γ → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-! ## The frozen theorem -/

/-- **W3-5 (inner contraction, card W3-5).** The `∫dtₘ`-peel of one sieve
coordinate: the inner sum over `u` reassembles into `X · eval (contractAt m F)`
up to an absolute error plus the r-dependent marked-prime budget
`∑_{p ∣ ∏r} 1/(p−1)`. -/
theorem inner_contract (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) (m : Fin 5) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      ∀ r ∈ kSieveIndex 5 R W', r m = 1 →
      |(∑ u ∈ Finset.range R,
            yF R W' F (Function.update r m u) / (Nat.totient u : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R)
            * eval (contractAt m F)
                (fun i => Real.log (r (m.succAbove i)) / Real.log R)|
      ≤ c * (1 + ((W'.totient : ℝ) / W' * Real.log R)
              * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1))) := by
  classical
  have hφpos : 0 < (Nat.totient W' : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hpos
  have hWposR : 0 < (W' : ℝ) := by exact_mod_cast hpos
  set Cb : ℕ → ℝ := fun k => (budget_moment W' hW' hpos hUpper k 0).choose with hCbdef
  set Cm : ℕ → ℝ := fun k => (marked_sqf_phi W' hW' hpos k).choose with hCmdef
  have hCb0 : ∀ k, 0 ≤ Cb k := fun k => (budget_moment W' hW' hpos hUpper k 0).choose_spec.1
  have hCm0 : ∀ k, 0 ≤ Cm k := fun k => (marked_sqf_phi W' hW' hpos k).choose_spec.1
  set Cabs : ℝ :=
    (F.map (fun a => |(a.2 : ℝ)| * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2))).sum with hCabsdef
  set C3 : ℝ := (F.map (fun a => |(a.2 : ℝ)| * Cm (a.1 m))).sum with hC3def
  have hCabs0 : 0 ≤ Cabs := by
    rw [hCabsdef]; apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx
    exact mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (hCb0 _) (by positivity)) (Real.log_nonneg (by norm_num)))
  have hC30 : 0 ≤ C3 := by
    rw [hC3def]; apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx
    exact mul_nonneg (abs_nonneg _) (hCm0 _)
  have hq0 : 0 ≤ (W' : ℝ) / (Nat.totient W' : ℝ) := by positivity
  refine ⟨Cabs + C3 * ((W' : ℝ) / (Nat.totient W' : ℝ)),
    add_nonneg hCabs0 (mul_nonneg hC30 hq0), ?_⟩
  intro D R _hD _hDp hR r hr hrm
  have hLpos : 0 < Real.log R := lt_of_lt_of_le zero_lt_one hR
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
  -- === Rewrite the target ===
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
    rw [e1, Finset.sum_congr rfl (fun u _ => by rw [eval_ofPoly, list_sum_div]),
      sum_finset_list_sum]
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
  -- === The per-monomial bound ===
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
      ≤ |(a.2 : ℝ)| * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2
          + Cm (a.1 m) * Real.log R
              * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1))) := by
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
    have hest := inner_sum_estimate W' hW' hpos hUpper hR hr hrm (a.1 m)
    calc |(a.2 : ℝ)|
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * |(∑ u ∈ (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex 5 R W'),
                (Real.log u / Real.log R) ^ a.1 m / (Nat.totient u : ℝ))
              - ((W'.totient : ℝ) / W' * Real.log R)
                  * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (a.1 m + 1)
                  / ((a.1 m : ℝ) + 1)|
        ≤ |(a.2 : ℝ)| * 1 * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2
            + Cm (a.1 m) * Real.log R
                * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hK1 (abs_nonneg _)) hest (abs_nonneg _)
          exact mul_nonneg (abs_nonneg _) zero_le_one
      _ = |(a.2 : ℝ)| * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2
            + Cm (a.1 m) * Real.log R
                * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1))) := by rw [mul_one]
  -- === Assemble ===
  set S : ℝ := ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; apply Finset.sum_nonneg
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hbndsum :
      (F.map (fun a => |(a.2 : ℝ)| * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2
          + Cm (a.1 m) * Real.log R * S))).sum
        = Cabs + C3 * (Real.log R * S) := by
    have hsplit : (fun a : Mono => |(a.2 : ℝ)| * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2
          + Cm (a.1 m) * Real.log R * S))
        = fun a => (|(a.2 : ℝ)| * (Cb (a.1 m) * 4 ^ (a.1 m) + Real.log 2))
          + (|(a.2 : ℝ)| * Cm (a.1 m)) * (Real.log R * S) := by
      funext a; ring
    rw [hsplit, list_sum_map_add, List.sum_map_mul_right, ← hCabsdef, ← hC3def]
  have hXnn : 0 ≤ (Nat.totient W' : ℝ) / W' * Real.log R :=
    mul_nonneg (by positivity) hLpos.le
  have hXSnn : 0 ≤ ((Nat.totient W' : ℝ) / W' * Real.log R) * S := mul_nonneg hXnn hSnn
  have hqX : (W' : ℝ) / (Nat.totient W' : ℝ)
      * ((Nat.totient W' : ℝ) / W' * Real.log R) = Real.log R := by
    field_simp
  rw [hFull, hTarget, list_sum_map_sub]
  refine le_trans (list_abs_sum_le F _) ?_
  refine le_trans (list_sum_le_sum F _ _ hpera) ?_
  rw [hbndsum]
  -- final numeric inequality
  have hmul : Real.log R * S
      = (W' : ℝ) / (Nat.totient W' : ℝ) * (((Nat.totient W' : ℝ) / W' * Real.log R) * S) := by
    rw [← mul_assoc, hqX]
  rw [hmul]
  nlinarith [mul_nonneg hCabs0 hXSnn, mul_nonneg hC30 hq0, hCabs0, hC30, hq0, hXSnn]


/-! ## W3-6 (keystone J) — the outer square-and-sum assembly (`mv_J`) -/

-- The reindex bijection: filtered 5-tuples (r m = 1) ↔ kSieveIndex 4.
lemma sum_filt_removeNth {M : Type*} [AddCommMonoid M] (R W' : ℕ) (m : Fin 5)
    (h : (Fin 4 → ℕ) → M) :
    ∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1), h (Fin.removeNth m r)
      = ∑ ρ ∈ kSieveIndex 4 R W', h ρ := by
  classical
  refine Finset.sum_bij' (fun r _ => Fin.removeNth m r) (fun ρ _ => Fin.insertNth m 1 ρ)
    ?hi ?hj ?li ?ri ?val
  case hi =>
    intro r hr
    rw [Finset.mem_filter, mem_kSieveIndex_iff] at hr
    obtain ⟨⟨hsqf, hpc, hcop, hprod⟩, hrm⟩ := hr
    rw [mem_kSieveIndex_iff]
    refine ⟨fun i => hsqf _, fun i j hij => hpc _ _ ?_, fun i => hcop _, ?_⟩
    · exact fun heq => hij (Fin.succAbove_right_injective heq)
    · have : ∏ i : Fin 4, Fin.removeNth m r i = ∏ j : Fin 5, r j := by
        rw [Fin.prod_univ_succAbove (fun j => r j) m, hrm, one_mul]
        rfl
      rw [this]; exact hprod
  case hj =>
    intro ρ hρ
    rw [mem_kSieveIndex_iff] at hρ
    obtain ⟨hsqf, hpc, hcop, hprod⟩ := hρ
    rw [Finset.mem_filter, mem_kSieveIndex_iff]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro j
      rcases eq_or_ne j m with rfl | hjm
      · rw [Fin.insertNth_apply_same]; exact squarefree_one
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjm
        rw [Fin.insertNth_apply_succAbove]; exact hsqf i
    · intro j k hjk
      rcases eq_or_ne j m with rfl | hjm
      · rw [Fin.insertNth_apply_same]; exact Nat.coprime_one_left _
      · rcases eq_or_ne k m with rfl | hkm
        · rw [Fin.insertNth_apply_same]; exact Nat.coprime_one_right _
        · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjm
          obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hkm
          rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
          exact hpc i l (fun heq => hjk (by rw [heq]))
    · intro j
      rcases eq_or_ne j m with rfl | hjm
      · rw [Fin.insertNth_apply_same]; exact Nat.coprime_one_left _
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjm
        rw [Fin.insertNth_apply_succAbove]; exact hcop i
    · have : ∏ j : Fin 5, Fin.insertNth m 1 ρ j = ∏ i : Fin 4, ρ i := by
        rw [Fin.prod_univ_succAbove (fun j => Fin.insertNth m 1 ρ j) m,
          Fin.insertNth_apply_same]
        simp only [Fin.insertNth_apply_succAbove, one_mul]
      rw [this]; exact hprod
    · rw [Fin.insertNth_apply_same]
  case li =>
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Fin.insertNth_removeNth]
    exact Function.update_eq_self_iff.mpr hr.2.symm
  case ri =>
    intro ρ _
    simp only [Fin.removeNth_insertNth]
  case val =>
    intro r _; rfl

-- ==== tail lemmas (ported from MvI, which are private there) ====
private lemma int_tail' (D R : ℕ) (hD : 3 ≤ D) :
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

private lemma prime_tail' (D R : ℕ) (hD : 3 ≤ D) :
    ∑ p ∈ (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p), 1 / ((p:ℝ) - 1)^2
      ≤ 2 / (D:ℝ) := by
  have hsub : (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p)
      ⊆ (Finset.range R).filter (fun k => D < k) := by
    intro p hp; rw [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩
  have h1 : ∑ p ∈ (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p), 1 / ((p:ℝ) - 1)^2
      ≤ ∑ k ∈ (Finset.range R).filter (fun k => D < k), 1 / ((k:ℝ) - 1)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub; intro k _ _; positivity
  have h2 : (1:ℝ) / ((D:ℝ) - 1) ≤ 2 / (D:ℝ) := by
    have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  linarith [int_tail' D R hD, h1, h2]

-- gMult of a prime and of 1
private lemma gMult_prime_cast {p : ℕ} (hp : Nat.Prime p) : (gMult p : ℝ) = (p : ℝ) - 2 := by
  have : gMult p = p - 2 := by
    rw [gMult, Nat.Prime.primeFactors hp, Finset.prod_singleton]
  rw [this, Nat.cast_sub hp.two_le]; norm_num

private lemma gMult_one_cast : (gMult 1 : ℝ) = 1 := by
  rw [gMult, Nat.primeFactors_one, Finset.prod_empty]; norm_num

-- g-side pairwise collision bound (n = 4)
private lemma badpair_bound_g (W' : ℕ) (cg : ℝ) (hcg0 : 0 ≤ cg)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ))
        ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD3 : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    (hR2 : 2 ≤ R) (hlogR0 : 0 ≤ Real.log R)
    (i j : Fin 4) (hij : i ≠ j) (p : ℕ) (hp : Nat.Prime p) (hpD : D < p) :
    ∑ r ∈ (decBox 4 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (gMult (r k) : ℝ))
      ≤ cg ^ 4 * (Real.log R) ^ 4 / ((p:ℝ) - 2) ^ 2 := by
  classical
  set g : Fin 4 → ℕ := fun k => if k = i ∨ k = j then p else 1 with hg
  have hp2 : 2 ≤ p := hp.two_le
  have hp2R : (0:ℝ) < (p:ℝ) - 2 := by
    have h3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
    linarith
  have hgpos : ∀ k, 0 < g k := by
    intro k; simp only [hg]; split
    · exact hp.pos
    · exact one_pos
  set coordSet : Fin 4 → Finset ℕ := fun k =>
    (Finset.range R).filter (fun s => Squarefree s ∧ s.Coprime W' ∧ g k ∣ s) with hcoord
  have hstepA : ∑ r ∈ (decBox 4 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (gMult (r k) : ℝ))
      ≤ ∏ k, ∑ s ∈ coordSet k, (1 / (gMult s : ℝ)) := by
    rw [Finset.prod_univ_sum coordSet (fun _ s => 1 / (gMult s : ℝ))]
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
  set h : Fin 4 → ℝ := fun k => ∑ s ∈ coordSet k, (1 / (gMult s : ℝ)) with hh
  have hhnn : ∀ k, 0 ≤ h k := fun k => Finset.sum_nonneg (fun s _ => by positivity)
  have hhle : ∀ k, h k ≤ (1 / (gMult (g k) : ℝ)) * cg * Real.log R := by
    intro k
    have hkey := hcg D (g k) R hD3 hDW (hgpos k) hR2
    have hrw : ∑ s ∈ coordSet k, (Real.log s) ^ 0 / (gMult s : ℝ) = h k := by
      simp only [hh, hcoord, pow_zero]
    rw [hrw] at hkey
    simpa using hkey
  have hgi : g i = p := by simp [hg]
  have hgj : g j = p := by simp [hg]
  have hgp : (gMult p : ℝ) = (p:ℝ) - 2 := gMult_prime_cast hp
  have hi_le : h i ≤ cg * Real.log R / ((p:ℝ) - 2) := by
    have := hhle i; rw [hgi, hgp] at this
    calc h i ≤ 1 / ((p:ℝ) - 2) * cg * Real.log R := this
      _ = cg * Real.log R / ((p:ℝ) - 2) := by ring
  have hj_le : h j ≤ cg * Real.log R / ((p:ℝ) - 2) := by
    have := hhle j; rw [hgj, hgp] at this
    calc h j ≤ 1 / ((p:ℝ) - 2) * cg * Real.log R := this
      _ = cg * Real.log R / ((p:ℝ) - 2) := by ring
  have hother : ∀ k ∈ (Finset.univ.erase i).erase j, h k ≤ cg * Real.log R := by
    intro k hk
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    obtain ⟨hkj, hki, _⟩ := hk
    have hgk : g k = 1 := by simp only [hg]; rw [if_neg (by tauto)]
    have := hhle k; rw [hgk, gMult_one_cast] at this; simpa using this
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hsplit : ∏ k, h k = h i * (h j * ∏ k ∈ (Finset.univ.erase i).erase j, h k) := by
    rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ i),
        ← Finset.mul_prod_erase (Finset.univ.erase i) h hjmem]
  have hcard : ((Finset.univ.erase i).erase j).card = 2 := by
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have hprodrest : ∏ k ∈ (Finset.univ.erase i).erase j, h k ≤ (cg * Real.log R) ^ 2 := by
    calc ∏ k ∈ (Finset.univ.erase i).erase j, h k
        ≤ ∏ _k ∈ (Finset.univ.erase i).erase j, (cg * Real.log R) :=
          Finset.prod_le_prod (fun k _ => hhnn k) hother
      _ = (cg * Real.log R) ^ 2 := by rw [Finset.prod_const, hcard]
  have hclogR0 : 0 ≤ cg * Real.log R := mul_nonneg hcg0 hlogR0
  have hbnd : ∏ k, h k
      ≤ (cg * Real.log R / ((p:ℝ) - 2))
        * ((cg * Real.log R / ((p:ℝ) - 2)) * (cg * Real.log R) ^ 2) := by
    rw [hsplit]
    apply mul_le_mul hi_le _ (mul_nonneg (hhnn j) (Finset.prod_nonneg (fun k _ => hhnn k)))
      (div_nonneg hclogR0 hp2R.le)
    apply mul_le_mul hj_le hprodrest (Finset.prod_nonneg (fun k _ => hhnn k))
      (div_nonneg hclogR0 hp2R.le)
  have hfinal : (cg * Real.log R / ((p:ℝ) - 2))
        * ((cg * Real.log R / ((p:ℝ) - 2)) * (cg * Real.log R) ^ 2)
      = cg ^ 4 * (Real.log R) ^ 4 / ((p:ℝ) - 2) ^ 2 := by
    have hne : (p:ℝ) - 2 ≠ 0 := ne_of_gt hp2R
    field_simp
  calc ∑ r ∈ (decBox 4 R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (gMult (r k) : ℝ))
      ≤ ∏ k, h k := hstepA
    _ ≤ _ := hbnd
    _ = cg ^ 4 * (Real.log R) ^ 4 / ((p:ℝ) - 2) ^ 2 := hfinal

set_option maxHeartbeats 1600000 in
-- Bundles `mv_monomial_g` at `z = R` with the 6-pair g-weighted coprimality drop
-- and the κ-power absorption in one elaboration; exceeds the default budget.
private lemma box4_g_moment (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (e : Fin 4 → ℕ) (d : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ ρ ∈ kSieveIndex 4 R W',
            (∏ i, (Real.log (ρ i) / Real.log R) ^ e i)
              * ((Real.log R - ∑ i, Real.log (ρ i)) / Real.log R) ^ d
              / ∏ i, (gMult (ρ i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 4 * ((DInt' e d : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 4 * (1 / Real.log R + 1 / D) := by
  classical
  obtain ⟨cg, hcg0, hcg⟩ := marked_sqf_g W' hW' hpos 0
  obtain ⟨c1, hc1_0, hc1⟩ := mv_monomial_g W' hW' hpos hUpper 4 e d
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  have hκle1 : κ ≤ 1 := by
    rw [hκdef, div_le_one (by exact_mod_cast hpos)]; exact_mod_cast Nat.totient_le W'
  refine ⟨96 * cg ^ 4 / κ ^ 4 + c1 / κ, by positivity, ?_⟩
  intro D R hD hDW hlogR
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
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXκL : X = κ * L := by rw [hXdef, hκdef, hLdef]
  have hX0 : 0 ≤ X := by rw [hXκL]; exact mul_nonneg hκpos.le hLpos.le
  have hκL1X : κ * L ≤ 1 + X := by rw [← hXκL]; linarith
  have hDpos : (0:ℝ) < (D : ℝ) := by
    have : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    linarith
  -- the two box sums and the drop
  set MSK : ℝ := ∑ ρ ∈ kSieveIndex 4 R W',
      (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
        / ∏ i, (gMult (ρ i) : ℝ) with hMSKdef
  set MSD : ℝ := ∑ ρ ∈ decBox 4 R W',
      (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
        / ∏ i, (gMult (ρ i) : ℝ) with hMSDdef
  set Drop : ℝ := ∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
      ∏ i, (1 / (gMult (ρ i) : ℝ)) with hDropdef
  -- Stage 3: mv_monomial_g at z = R
  have hStage3 : |MSD - X ^ 4 * ((DInt' e d : ℚ) : ℝ)| ≤ c1 * (1 + X) ^ 3 * (1 + L / D) := by
    have hspec := hc1 D R R hD hDW hR2 le_rfl hlogR
    rw [← hXdef, ← hLdef, div_self hLne, one_pow, mul_one] at hspec
    simpa [hMSDdef, hLdef] using hspec
  -- subset
  have hsubset : kSieveIndex 4 R W' ⊆ decBox 4 R W' := by
    intro r hr
    have hmem := (mem_kSieveIndex_iff r).mp hr
    obtain ⟨hsqf, _, hcop, hprod⟩ := hmem
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
  -- per-tuple weight facts on decBox4 (nonneg, ≤ ∏(1/g))
  have hbdd : ∀ ρ ∈ decBox 4 R W',
      0 ≤ (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
            / ∏ i, (gMult (ρ i) : ℝ)
      ∧ (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
            / ∏ i, (gMult (ρ i) : ℝ) ≤ ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
    intro ρ hr
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
    obtain ⟨hlt, hsqf, hcop, hprod⟩ := hr
    have hr1 : ∀ i, 1 ≤ ρ i := fun i => Nat.pos_of_ne_zero (hsqf i).ne_zero
    have hlogr0 : ∀ i, 0 ≤ Real.log (ρ i) := fun i => Real.log_nonneg (by exact_mod_cast hr1 i)
    have hlogrL : ∀ i, Real.log (ρ i) ≤ L := fun i => by
      rw [hLdef]; exact Real.log_le_log (by exact_mod_cast hr1 i) (by exact_mod_cast (le_of_lt (hlt i)))
    have hgpos : (0:ℝ) < ∏ i, (gMult (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
      have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this)
    have hti0 : ∀ i, 0 ≤ Real.log (ρ i) / L := fun i => div_nonneg (hlogr0 i) hLpos.le
    have hti1 : ∀ i, Real.log (ρ i) / L ≤ 1 := fun i => (div_le_one hLpos).mpr (hlogrL i)
    have hprodt0 : 0 ≤ ∏ i, (Real.log (ρ i) / L) ^ (e i) :=
      Finset.prod_nonneg (fun i _ => pow_nonneg (hti0 i) _)
    have hprodt1 : ∏ i, (Real.log (ρ i) / L) ^ (e i) ≤ 1 :=
      Finset.prod_le_one (fun i _ => pow_nonneg (hti0 i) _)
        (fun i _ => pow_le_one₀ (hti0 i) (hti1 i))
    have hSL : ∑ i, Real.log (ρ i) = Real.log ((∏ i, ρ i : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact (Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (by have := hr1 i; omega))).symm
    have hprodpos : 0 < ∏ i, ρ i := Finset.prod_pos (fun i _ => by have := hr1 i; omega)
    have hSLL : ∑ i, Real.log (ρ i) ≤ L := by
      rw [hSL, hLdef]; exact Real.log_le_log (by exact_mod_cast hprodpos) (by exact_mod_cast (le_of_lt hprod))
    have hSL0 : 0 ≤ ∑ i, Real.log (ρ i) := Finset.sum_nonneg (fun i _ => hlogr0 i)
    have hbud0 : 0 ≤ (L - ∑ i, Real.log (ρ i)) / L := div_nonneg (by linarith) hLpos.le
    have hbud1 : (L - ∑ i, Real.log (ρ i)) / L ≤ 1 := (div_le_one hLpos).mpr (by linarith)
    have hnum0 : 0 ≤ (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d :=
      mul_nonneg hprodt0 (pow_nonneg hbud0 _)
    have hnum1 : (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d ≤ 1 := by
      calc (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
          ≤ 1 * 1 := mul_le_mul hprodt1 (pow_le_one₀ hbud0 hbud1) (pow_nonneg hbud0 _) (by norm_num)
        _ = 1 := by ring
    have hprodinv : (∏ i, (1 / (gMult (ρ i) : ℝ))) = 1 / ∏ i, (gMult (ρ i) : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
    refine ⟨div_nonneg hnum0 hgpos.le, ?_⟩
    rw [hprodinv, div_le_div_iff₀ hgpos hgpos]
    nlinarith [mul_le_mul_of_nonneg_right hnum1 hgpos.le]
  have hDropPer : |MSK - MSD| ≤ Drop := by
    have hsdiff : MSD - MSK = ∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
        (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
          / ∏ i, (gMult (ρ i) : ℝ) := by
      have h := Finset.sum_sdiff (f := fun ρ => (∏ i, (Real.log (ρ i) / L) ^ (e i))
        * ((L - ∑ i, Real.log (ρ i)) / L) ^ d / ∏ i, (gMult (ρ i) : ℝ)) hsubset
      simp only [hMSDdef, hMSKdef]; linarith [h]
    have hnn : 0 ≤ ∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
        (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
          / ∏ i, (gMult (ρ i) : ℝ) :=
      Finset.sum_nonneg (fun ρ hr => (hbdd ρ (Finset.mem_sdiff.mp hr).1).1)
    have hle : (∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
        (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
          / ∏ i, (gMult (ρ i) : ℝ)) ≤ Drop := by
      rw [hDropdef]; exact Finset.sum_le_sum (fun ρ hr => (hbdd ρ (Finset.mem_sdiff.mp hr).1).2)
    have hneg : MSK - MSD = -(∑ ρ ∈ decBox 4 R W' \ kSieveIndex 4 R W',
        (∏ i, (Real.log (ρ i) / L) ^ (e i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ d
          / ∏ i, (gMult (ρ i) : ℝ)) := by rw [← hsdiff]; ring
    rw [hneg, abs_neg, abs_of_nonneg hnn]; exact hle
  -- Drop bound: 12 ordered pairs × prime tail
  have hDropBound : Drop ≤ 96 * cg ^ 4 * L ^ 4 / (D : ℝ) := by
    set Pairs : Finset (Fin 4 × Fin 4) :=
      (Finset.univ : Finset (Fin 4 × Fin 4)).filter (fun q => q.1 ≠ q.2) with hPairsdef
    set Primes : Finset ℕ :=
      (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimesdef
    set T : Finset ((Fin 4 × Fin 4) × ℕ) := Pairs ×ˢ Primes with hTdef
    set Bad : (Fin 4 × Fin 4) × ℕ → Finset (Fin 4 → ℕ) := fun x =>
      (decBox 4 R W').filter (fun r => x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2) with hBaddef
    set ind : (Fin 4 × Fin 4) × ℕ → (Fin 4 → ℕ) → ℝ := fun x r =>
      if x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2 then ∏ i, (1 / (gMult (r i) : ℝ)) else 0 with hinddef
    have hindnn : ∀ x r, 0 ≤ ind x r := by
      intro x r; simp only [hinddef]; split_ifs
      · exact Finset.prod_nonneg (fun i _ => by positivity)
      · exact le_refl 0
    have hcover : Drop ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (gMult (r i) : ℝ))) := by
      rw [hDropdef]
      have hpt : ∀ r ∈ decBox 4 R W' \ kSieveIndex 4 R W',
          (∏ i, (1 / (gMult (r i) : ℝ))) ≤ ∑ x ∈ T, ind x r := by
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
        have hindeq : ind ((i, j), p) r = ∏ i, (1 / (gMult (r i) : ℝ)) := by
          rw [hinddef]; simp only [if_pos (And.intro hpi hpj)]
        rw [← hindeq]
        exact Finset.single_le_sum (fun x _ => hindnn x r) hx0
      calc ∑ r ∈ decBox 4 R W' \ kSieveIndex 4 R W', (∏ i, (1 / (gMult (r i) : ℝ)))
          ≤ ∑ r ∈ decBox 4 R W' \ kSieveIndex 4 R W', ∑ x ∈ T, ind x r :=
            Finset.sum_le_sum hpt
        _ = ∑ x ∈ T, ∑ r ∈ decBox 4 R W' \ kSieveIndex 4 R W', ind x r := Finset.sum_comm
        _ ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (gMult (r i) : ℝ))) := by
            apply Finset.sum_le_sum
            intro x _
            rw [hinddef, ← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · rw [hBaddef]; exact Finset.filter_subset_filter _ Finset.sdiff_subset
            · intro r _ _; exact Finset.prod_nonneg (fun i _ => by positivity)
    have hPairsCard : Pairs.card = 12 := by rw [hPairsdef]; decide
    have hfinal : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (gMult (r i) : ℝ))))
        ≤ 96 * cg ^ 4 * L ^ 4 / (D : ℝ) := by
      have h1 : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (gMult (r i) : ℝ))))
          ≤ ∑ x ∈ T, cg ^ 4 * L ^ 4 / ((x.2 : ℝ) - 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [hTdef, Finset.mem_product] at hx
        obtain ⟨hq, hpx⟩ := hx
        rw [hPairsdef, Finset.mem_filter] at hq
        rw [hPrimesdef, Finset.mem_filter] at hpx
        have hbp := badpair_bound_g W' cg hcg0 hcg D R hD hDW hR2 hLpos.le
          x.1.1 x.1.2 hq.2 x.2 hpx.2.1 hpx.2.2
        rw [← hLdef] at hbp
        rw [hBaddef]; exact hbp
      refine le_trans h1 ?_
      rw [hTdef, Finset.sum_product]
      have hcL0 : 0 ≤ cg ^ 4 * L ^ 4 := mul_nonneg (pow_nonneg hcg0 4) (pow_nonneg hLpos.le 4)
      have hinner : ∀ q ∈ Pairs,
          (∑ p ∈ Primes, cg ^ 4 * L ^ 4 / (((q, p).2 : ℝ) - 2) ^ 2)
            ≤ cg ^ 4 * L ^ 4 * (8 / (D : ℝ)) := by
        intro q _
        simp only
        calc (∑ p ∈ Primes, cg ^ 4 * L ^ 4 / ((p : ℝ) - 2) ^ 2)
            ≤ ∑ p ∈ Primes, cg ^ 4 * L ^ 4 * (4 / ((p : ℝ) - 1) ^ 2) := by
              apply Finset.sum_le_sum
              intro p hp
              rw [hPrimesdef, Finset.mem_filter, Finset.mem_range] at hp
              have hp4 : 4 ≤ p := by have := hp.2.2; omega
              have hp4R : (4:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp4
              have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
              have hp2 : (0:ℝ) < (p:ℝ) - 2 := by linarith
              have hfrac : (1:ℝ) / ((p:ℝ) - 2) ^ 2 ≤ 4 / ((p:ℝ) - 1) ^ 2 := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
              calc cg ^ 4 * L ^ 4 / ((p:ℝ) - 2) ^ 2
                  = cg ^ 4 * L ^ 4 * (1 / ((p:ℝ) - 2) ^ 2) := by ring
                _ ≤ cg ^ 4 * L ^ 4 * (4 / ((p:ℝ) - 1) ^ 2) :=
                    mul_le_mul_of_nonneg_left hfrac hcL0
          _ = cg ^ 4 * L ^ 4 * (4 * ∑ p ∈ Primes, 1 / ((p : ℝ) - 1) ^ 2) := by
              rw [Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro p _; ring
          _ ≤ cg ^ 4 * L ^ 4 * (4 * (2 / (D : ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ hcL0
              apply mul_le_mul_of_nonneg_left (prime_tail' D R hD) (by norm_num)
          _ = cg ^ 4 * L ^ 4 * (8 / (D : ℝ)) := by ring
      calc (∑ q ∈ Pairs, ∑ p ∈ Primes, cg ^ 4 * L ^ 4 / (((q, p).2 : ℝ) - 2) ^ 2)
          ≤ ∑ q ∈ Pairs, cg ^ 4 * L ^ 4 * (8 / (D : ℝ)) := Finset.sum_le_sum hinner
        _ = (Pairs.card : ℝ) * (cg ^ 4 * L ^ 4 * (8 / (D : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = 96 * cg ^ 4 * L ^ 4 / (D : ℝ) := by rw [hPairsCard]; push_cast; ring
    exact le_trans hcover hfinal
  -- combine: |MSK - X^4 DInt'| ≤ Drop + main-error, then absorb
  have htri : |MSK - X ^ 4 * ((DInt' e d : ℚ) : ℝ)| ≤ Drop + c1 * (1 + X) ^ 3 * (1 + L / D) := by
    calc |MSK - X ^ 4 * ((DInt' e d : ℚ) : ℝ)|
        ≤ |MSK - MSD| + |MSD - X ^ 4 * ((DInt' e d : ℚ) : ℝ)| := abs_sub_le _ _ _
      _ ≤ Drop + c1 * (1 + X) ^ 3 * (1 + L / D) := add_le_add hDropPer hStage3
  -- absorption facts
  have hB1 : (1:ℝ) ≤ 1 + X := by linarith
  have hB0 : (0:ℝ) ≤ 1 + X := by linarith
  have hLmax : L ≤ (1 + X) / κ := by rw [le_div_iff₀ hκpos]; nlinarith [hκL1X]
  -- Drop absorption: 96 cg⁴ L⁴ / D ≤ (96 cg⁴/κ⁴)(1+X)⁴/D
  have hL4 : L ^ 4 ≤ (1 + X) ^ 4 / κ ^ 4 := by
    rw [le_div_iff₀ (pow_pos hκpos 4)]
    calc L ^ 4 * κ ^ 4 = (κ * L) ^ 4 := by ring
      _ ≤ (1 + X) ^ 4 := pow_le_pow_left₀ (mul_nonneg hκpos.le hLpos.le) hκL1X 4
  have hMSKgoal : |MSK - X ^ 4 * ((DInt' e d : ℚ) : ℝ)|
      ≤ (96 * cg ^ 4 / κ ^ 4 + c1 / κ) * (1 + X) ^ 4 * (1 / L + 1 / (D : ℝ)) := by
    refine le_trans htri ?_
    have hRHSeq : (96 * cg ^ 4 / κ ^ 4 + c1 / κ) * (1 + X) ^ 4 * (1 / L + 1 / (D : ℝ))
        = (96 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 4 * (1 / (D:ℝ))
          + (c1 / κ) * (1 + X) ^ 4 * (1 / L)
          + ((96 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 4 * (1 / L)
            + (c1 / κ) * (1 + X) ^ 4 * (1 / (D:ℝ))) := by ring
    rw [hRHSeq]
    -- Drop ≤ (96 cg⁴/κ⁴)(1+X)⁴/D
    have hP1 : Drop ≤ (96 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 4 * (1 / (D:ℝ)) := by
      refine le_trans hDropBound ?_
      have e1 : 96 * cg ^ 4 * L ^ 4 / (D : ℝ) = (96 * cg ^ 4 / (D:ℝ)) * L ^ 4 := by ring
      have e2 : (96 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 4 * (1 / (D:ℝ))
          = (96 * cg ^ 4 / (D:ℝ)) * ((1 + X) ^ 4 / κ ^ 4) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hL4
        (div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hcg0 4)) hDpos.le)
    -- main-error ≤ (c1/κ)(1+X)⁴/L + (c1/κ)(1+X)⁴/D
    have hP2 : c1 * (1 + X) ^ 3 * (1 + L / D)
        ≤ (c1 / κ) * (1 + X) ^ 4 * (1 / L) + (c1 / κ) * (1 + X) ^ 4 * (1 / (D:ℝ)) := by
      have hkey : L * (1 + X) ^ 3 ≤ (1 / κ) * (1 + X) ^ 4 := by
        rw [mul_comm (1/κ)]
        calc L * (1 + X) ^ 3 ≤ ((1 + X) / κ) * (1 + X) ^ 3 :=
              mul_le_mul_of_nonneg_right hLmax (by positivity)
          _ = (1 + X) ^ 4 * (1 / κ) := by ring
      have hcore : c1 * (1 + X) ^ 3 * L ≤ c1 / κ * (1 + X) ^ 4 := by
        calc c1 * (1 + X) ^ 3 * L = c1 * (L * (1 + X) ^ 3) := by ring
          _ ≤ c1 * ((1 / κ) * (1 + X) ^ 4) := mul_le_mul_of_nonneg_left hkey hc1_0
          _ = c1 / κ * (1 + X) ^ 4 := by ring
      -- expand (1 + L/D)
      have hexp : c1 * (1 + X) ^ 3 * (1 + L / D)
          = c1 * (1 + X) ^ 3 + (c1 * (1 + X) ^ 3) * L * (1 / (D:ℝ)) := by ring
      rw [hexp]
      have hA : c1 * (1 + X) ^ 3 ≤ (c1 / κ) * (1 + X) ^ 4 * (1 / L) := by
        rw [show (c1 / κ) * (1 + X) ^ 4 * (1 / L) = (c1 / κ * (1 + X) ^ 4) / L by ring,
          le_div_iff₀ hLpos]
        exact hcore
      have hBd : (c1 * (1 + X) ^ 3) * L * (1 / (D:ℝ)) ≤ (c1 / κ) * (1 + X) ^ 4 * (1 / (D:ℝ)) := by
        rw [show (c1 * (1 + X) ^ 3) * L * (1 / (D:ℝ)) = (c1 * (1 + X) ^ 3 * L) * (1 / (D:ℝ)) by ring,
          show (c1 / κ) * (1 + X) ^ 4 * (1 / (D:ℝ)) = (c1 / κ * (1 + X) ^ 4) * (1 / (D:ℝ)) by ring]
        exact mul_le_mul_of_nonneg_right hcore (by positivity)
      linarith [hA, hBd]
    have hR3 : (0:ℝ) ≤ (96 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 4 * (1 / L) := by positivity
    have hR4 : (0:ℝ) ≤ (c1 / κ) * (1 + X) ^ 4 * (1 / (D:ℝ)) :=
      mul_nonneg (mul_nonneg (div_nonneg hc1_0 hκpos.le) (by positivity)) (by positivity)
    linarith [hP1, hP2, hR3, hR4]
  simpa [hMSKdef, hLdef, hXdef, hκdef] using hMSKgoal

-- reuse MvJ's existing private list helpers by re-declaring the ones I need here
private lemma jlist_abs_sum_le {γ : Type*} (L : List γ) (f : γ → ℝ) :
    |(L.map f).sum| ≤ (L.map (fun a => |f a|)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      calc |f a + (L.map f).sum| ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
        _ ≤ |f a| + (L.map (fun a => |f a|)).sum := by linarith [ih]

private lemma jlist_sum_le {γ : Type*} (L : List γ) (f g : γ → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

private lemma jlist_sum_map_add {γ : Type*} (L : List γ) (f g : γ → ℝ) :
    (L.map (fun a => f a + g a)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private lemma jsum_finset_list_sum {ι γ : Type*} (S : Finset ι) (L : List γ)
    (f : ι → γ → ℝ) :
    ∑ u ∈ S, (L.map (fun x => f u x)).sum = (L.map (fun x => ∑ u ∈ S, f u x)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

private lemma jlist_sum_div {γ : Type*} (L : List γ) (g : γ → ℝ) (c : ℝ) :
    (L.map g).sum / c = (L.map (fun a => g a / c)).sum := by
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]; simp only [div_eq_mul_inv]

private lemma jlist_sum_map_sub {γ : Type*} (L : List γ) (f g : γ → ℝ) :
    (L.map f).sum - (L.map g).sum = (L.map (fun a => f a - g a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

-- the transport of the erase-product to a Fin 4 product
private lemma erase_prod_removeNth {M : Type*} [CommMonoid M] (m : Fin 5) (F : Fin 5 → M) :
    ∏ i ∈ Finset.univ.erase m, F i = ∏ i : Fin 4, F (m.succAbove i) := by
  have he : Finset.univ.erase m = ({m}ᶜ : Finset (Fin 5)) := by
    rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]
  rw [he, ← Fin.image_succAbove_univ m, Finset.prod_image
    (fun i _ j _ h => Fin.succAbove_right_injective h)]

set_option maxHeartbeats 1600000 in
-- The reindex + `eval_sq` list expansion + per-monomial `box4_g_moment` sum is a
-- single large elaboration exceeding the default heartbeat budget.
lemma mv_J_main (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) (m : Fin 5) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
            eval (contractAt m F) (fun i => Real.log (r (m.succAbove i)) / Real.log R) ^ 2
              / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 4 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 4 * (1 / Real.log R + 1 / D) := by
  classical
  set Q : BPoly 4 := sq (contractAt m F) with hQdef
  set Cfun : ((Fin 4 → ℕ) × ℕ × ℚ) → ℝ :=
    fun mo => Classical.choose (box4_g_moment W' hW' hpos hUpper mo.1 mo.2.1) with hCfundef
  have hCfunspec : ∀ mo, 0 ≤ Cfun mo ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ ρ ∈ kSieveIndex 4 R W',
            (∏ i, (Real.log (ρ i) / Real.log R) ^ (mo.1 i))
              * ((Real.log R - ∑ i, Real.log (ρ i)) / Real.log R) ^ (mo.2.1)
              / ∏ i, (gMult (ρ i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 4 * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)|
      ≤ Cfun mo * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 4 * (1 / Real.log R + 1 / D) :=
    fun mo => Classical.choose_spec (box4_g_moment W' hW' hpos hUpper mo.1 mo.2.1)
  have hCfun0 : ∀ mo, 0 ≤ Cfun mo := fun mo => (hCfunspec mo).1
  set Cmain : ℝ := (Q.map (fun mo => |(mo.2.2 : ℝ)| * Cfun mo)).sum with hCmaindef
  have hCmain0 : 0 ≤ Cmain := by
    rw [hCmaindef]; apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx; obtain ⟨mo, _, rfl⟩ := hx
    exact mul_nonneg (abs_nonneg _) (hCfun0 mo)
  refine ⟨Cmain, hCmain0, ?_⟩
  intro D R hD hDW hlogR
  set L : ℝ := Real.log R with hLdef
  set X : ℝ := (W'.totient : ℝ) / W' * L with hXdef
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hlogR
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- per-monomial box sum
  set MSK : ((Fin 4 → ℕ) × ℕ × ℚ) → ℝ := fun mo =>
    ∑ ρ ∈ kSieveIndex 4 R W',
      (∏ i, (Real.log (ρ i) / L) ^ (mo.1 i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1)
        / ∏ i, (gMult (ρ i) : ℝ) with hMSKdef
  -- Step 1: reindex LHS to a sum over kSieveIndex 4, expand into list-sum over Q.
  have hLHS : (∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
        eval (contractAt m F) (fun i => Real.log (r (m.succAbove i)) / L) ^ 2
          / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
      = (Q.map (fun mo => (mo.2.2 : ℝ) * MSK mo)).sum := by
    -- reindex
    have hreindex : (∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
          eval (contractAt m F) (fun i => Real.log (r (m.succAbove i)) / L) ^ 2
            / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
        = ∑ ρ ∈ kSieveIndex 4 R W',
            eval (contractAt m F) (fun i => Real.log (ρ i) / L) ^ 2 / ∏ i, (gMult (ρ i) : ℝ) := by
      rw [← sum_filt_removeNth R W' m
        (fun ρ => eval (contractAt m F) (fun i => Real.log (ρ i) / L) ^ 2 / ∏ i, (gMult (ρ i) : ℝ))]
      apply Finset.sum_congr rfl
      intro r _
      rw [erase_prod_removeNth m (fun i => (gMult (r i) : ℝ))]
      simp only [Fin.removeNth_apply]
    rw [hreindex]
    have hbudget : ∀ ρ : Fin 4 → ℕ, (1 : ℝ) - ∑ i, Real.log (ρ i) / L = (L - ∑ i, Real.log (ρ i)) / L := by
      intro ρ; rw [← Finset.sum_div, sub_div, div_self hLne]
    have hper : ∀ ρ ∈ kSieveIndex 4 R W',
        eval (contractAt m F) (fun i => Real.log (ρ i) / L) ^ 2 / ∏ i, (gMult (ρ i) : ℝ)
          = (Q.map (fun mo => (mo.2.2 : ℝ) * ((∏ i, (Real.log (ρ i) / L) ^ (mo.1 i))
              * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1)
              / ∏ i, (gMult (ρ i) : ℝ)))).sum := by
      intro ρ _
      rw [show eval (contractAt m F) (fun i => Real.log (ρ i) / L) ^ 2
          = eval Q (fun i => Real.log (ρ i) / L) from by rw [hQdef]; exact (eval_sq _ _).symm]
      have hev : eval Q (fun i => Real.log (ρ i) / L)
          = (Q.map (fun mo => (mo.2.2 : ℝ) * (∏ i, (Real.log (ρ i) / L) ^ (mo.1 i))
              * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1))).sum := by
        unfold eval
        refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
        dsimp only; rw [hbudget ρ]
      rw [hev, jlist_sum_div]
      refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
      ring
    rw [Finset.sum_congr rfl hper, jsum_finset_list_sum]
    refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
    rw [hMSKdef, ← Finset.mul_sum]
  -- Step 2: main term as list-sum
  have hMainSum : X ^ 4 * ((simplexInt Q : ℚ) : ℝ)
      = (Q.map (fun mo => X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)))).sum := by
    have hcast : ((simplexInt Q : ℚ) : ℝ)
        = (Q.map (fun mo => (mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))).sum := by
      rw [simplexInt, Rat.cast_list_sum, List.map_map]
      refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
      simp only [Function.comp_apply]; push_cast; ring
    rw [hcast, ← List.sum_map_mul_left]
  -- per-monomial bound
  have hPer : ∀ mo ∈ Q, |(mo.2.2 : ℝ) * MSK mo - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))|
      ≤ |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ)) := by
    intro mo _
    have hfac : (mo.2.2 : ℝ) * MSK mo - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))
        = (mo.2.2 : ℝ) * (MSK mo - X ^ 4 * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)) := by ring
    rw [hfac, abs_mul]
    have hspec := (hCfunspec mo).2 D R hD hDW hlogR
    rw [← hLdef, ← hXdef] at hspec
    have hspec2 : |MSK mo - X ^ 4 * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)|
        ≤ Cfun mo * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ)) := hspec
    calc |(mo.2.2 : ℝ)| * |MSK mo - X ^ 4 * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)|
        ≤ |(mo.2.2 : ℝ)| * (Cfun mo * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ))) :=
          mul_le_mul_of_nonneg_left hspec2 (abs_nonneg _)
      _ = |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ)) := by ring
  -- assemble
  rw [hLHS, hMainSum, jlist_sum_map_sub]
  calc |(Q.map (fun mo => (mo.2.2 : ℝ) * MSK mo
          - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)))).sum|
      ≤ (Q.map (fun mo => |(mo.2.2 : ℝ) * MSK mo
          - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))|)).sum := by
        have := jlist_abs_sum_le Q (fun mo => (mo.2.2 : ℝ) * MSK mo
          - X ^ 4 * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)))
        exact this
    _ ≤ (Q.map (fun mo => |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ)))).sum :=
        jlist_sum_le _ _ _ hPer
    _ = Cmain * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ)) := by
        rw [hCmaindef,
          show (fun mo : (Fin 4 → ℕ) × ℕ × ℚ => |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ)))
            = (fun mo => (|(mo.2.2 : ℝ)| * Cfun mo) * ((1 + X) ^ 4 * (1 / L + 1 / (D:ℝ)))) from by
              funext mo; ring,
          List.sum_map_mul_right]
        ring

-- primes on the box are > D and < R
private lemma box_PF_subset {W' D R : ℕ} (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
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

-- M0 : the crude coordinate g-moment
private lemma M0_bound (W' : ℕ) (cg : ℝ)
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
  rw [gMult_one_cast, hFeq] at hg1
  have hL : ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (Real.log x) ^ 0 / (gMult x : ℝ)
      = ∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'), (1 / (gMult x : ℝ)) := by
    apply Finset.sum_congr rfl; intro x _; rw [pow_zero]
  rw [hL] at hg1
  have hRw : (1:ℝ) / 1 * cg * (Real.log R) ^ (0 + 1) = cg * Real.log R := by norm_num
  rw [hRw] at hg1
  exact hg1

-- MQ : ∑ Q(x)/g(x) ≤ 4 cg logR / D, Q(x) = ∑_{p ∣ x} 1/(p-1)
private lemma MQ_bound (W' : ℕ) (cg : ℝ) (hcg0 : 0 ≤ cg)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R)
    (hlogR0 : 0 ≤ Real.log R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
      ≤ 4 * cg * Real.log R / (D : ℝ) := by
  classical
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set Primes := (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimes
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  -- swap
  have hswap : (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
      ≤ ∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
          ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)) := by
    have hstep : (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
        ≤ ∑ x ∈ F_R, ∑ p ∈ Primes, (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [hF_R, Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hxR, hxsf, hxcop⟩ := hx
      rw [Finset.sum_div]
      have hcongr : ∑ p ∈ x.primeFactors, 1 / ((p:ℝ) - 1) / (gMult x : ℝ)
          = ∑ p ∈ x.primeFactors, 1 / ((p:ℝ) - 1) * (1 / (gMult x : ℝ)) := by
        apply Finset.sum_congr rfl; intro p _; ring
      rw [hcongr, ← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter]
        refine ⟨box_PF_subset hDW hxR hxcop hp, Nat.dvd_of_mem_primeFactors hp⟩
      · intro p hp _
        rw [Finset.mem_filter, hPrimes, Finset.mem_filter, Finset.mem_range] at hp
        have hpD : D < p := hp.1.2.2
        have hp1 : (0:ℝ) < (p:ℝ) - 1 := by
          have : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
          linarith
        positivity
    calc (∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ))
        ≤ ∑ x ∈ F_R, ∑ p ∈ Primes, (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) := hstep
      _ = ∑ p ∈ Primes, ∑ x ∈ F_R, (if p ∣ x then (1 / ((p:ℝ) - 1)) * (1 / (gMult x : ℝ)) else 0) :=
          Finset.sum_comm
      _ = ∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) * ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)) := by
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.mul_sum, ← Finset.sum_filter]
  refine le_trans hswap ?_
  -- per-prime marked bound and tail
  have hper : ∀ p ∈ Primes, (1 / ((p:ℝ) - 1)) *
        ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ))
      ≤ cg * Real.log R * (2 / ((p:ℝ) - 1) ^ 2) := by
    intro p hp
    rw [hPrimes, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpR, hpp, hpD⟩ := hp
    have hp3 : 3 ≤ p := by omega
    have hp3R : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
    have hmk := hcg D p R hD hDW hpp.pos hR2
    rw [gMult_prime_cast hpp] at hmk
    have hfilt : F_R.filter (fun x => p ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨h1,h2,h3⟩
      · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1,h2⟩,h3⟩
    rw [hfilt]
    have hsum_le : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
          (1 / (gMult x : ℝ)) ≤ (1 / ((p:ℝ) - 2)) * cg * Real.log R := by
      have : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
          (Real.log x) ^ 0 / (gMult x : ℝ)
          = ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r),
            (1 / (gMult x : ℝ)) := by
        apply Finset.sum_congr rfl; intro x _; rw [pow_zero]
      rw [this] at hmk
      simpa using hmk
    have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
    have hp2 : (0:ℝ) < (p:ℝ) - 2 := by linarith
    have hfrac : (1 / ((p:ℝ) - 1)) * (1 / ((p:ℝ) - 2)) ≤ 2 / ((p:ℝ) - 1) ^ 2 := by
      rw [one_div_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc (1 / ((p:ℝ) - 1)) * ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r), (1 / (gMult x : ℝ))
        ≤ (1 / ((p:ℝ) - 1)) * ((1 / ((p:ℝ) - 2)) * cg * Real.log R) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = cg * Real.log R * ((1 / ((p:ℝ) - 1)) * (1 / ((p:ℝ) - 2))) := by ring
      _ ≤ cg * Real.log R * (2 / ((p:ℝ) - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hfrac (mul_nonneg hcg0 hlogR0)
  calc (∑ p ∈ Primes, (1 / ((p:ℝ) - 1)) * ∑ x ∈ F_R.filter (fun x => p ∣ x), (1 / (gMult x : ℝ)))
      ≤ ∑ p ∈ Primes, cg * Real.log R * (2 / ((p:ℝ) - 1) ^ 2) := Finset.sum_le_sum hper
    _ = cg * Real.log R * (2 * ∑ p ∈ Primes, 1 / ((p:ℝ) - 1) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ cg * Real.log R * (2 * (2 / (D:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hcg0 hlogR0)
        apply mul_le_mul_of_nonneg_left (prime_tail' D R hD) (by norm_num)
    _ = 4 * cg * Real.log R / (D : ℝ) := by ring

private lemma gMult_pq_cast {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (gMult (p * q) : ℝ) = ((p:ℝ) - 2) * ((q:ℝ) - 2) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hmul : gMult (p * q) = gMult p * gMult q := by
    rw [gMult, gMult, gMult, Nat.Coprime.primeFactors_mul hcop,
      Finset.prod_union hcop.disjoint_primeFactors]
  rw [hmul, Nat.cast_mul, gMult_prime_cast hp, gMult_prime_cast hq]

-- S(p,q): the doubly-marked g-mass
private lemma MQ2_bound (W' : ℕ) (cg : ℝ) (hcg0 : 0 ≤ cg)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R)
    (hlogR0 : 0 ≤ Real.log R) :
    (∑ x ∈ (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W'),
        (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / (gMult x : ℝ))
      ≤ 20 * cg * Real.log R / (D : ℝ) := by
  classical
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set Primes := (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimes
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have hclogR : 0 ≤ cg * Real.log R := mul_nonneg hcg0 hlogR0
  -- p∈Primes facts
  have hprime_facts : ∀ p ∈ Primes, Nat.Prime p ∧ D < p ∧ (0:ℝ) < (p:ℝ) - 1 ∧ (0:ℝ) < (p:ℝ) - 2 := by
    intro p hp
    rw [hPrimes, Finset.mem_filter, Finset.mem_range] at hp
    have hpge : (4:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 4 ≤ p)
    exact ⟨hp.2.1, hp.2.2, by linarith, by linarith⟩
  set c1 : ℕ → ℝ := fun p => 1 / ((p:ℝ) - 1) with hc1def
  -- S(p,q)
  set S : ℕ → ℕ → ℝ := fun p q =>
    ∑ x ∈ F_R.filter (fun x => p ∣ x ∧ q ∣ x), (1 / (gMult x : ℝ)) with hSdef
  have hSnn : ∀ p q, 0 ≤ S p q := fun p q => Finset.sum_nonneg (fun x _ => by positivity)
  -- Step 1: expand the square and swap to ∑_{p,q∈Primes} c1 p * c1 q * S p q
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
    have hsub : x.primeFactors ⊆ Primes := box_PF_subset hDW hxR hxcop
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
            (if p ∣ x then ∑ q ∈ Primes, (if q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) else 0) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; rw [Finset.mem_filter]
            exact ⟨hsub hp, Nat.dvd_of_mem_primeFactors hp⟩
          · intro p hp _
            apply Finset.sum_nonneg; intro q hq; split_ifs with hqx
            · exact hnnW p q (Finset.mem_of_mem_filter p hp) hq
            · exact le_refl 0
      _ = ∑ p ∈ Primes, ∑ q ∈ Primes, (if p ∣ x ∧ q ∣ x then c1 p * c1 q * (1 / (gMult x : ℝ)) else 0) := by
          apply Finset.sum_congr rfl; intro p _
          by_cases hpx : p ∣ x
          · rw [if_pos hpx]; apply Finset.sum_congr rfl; intro q _
            by_cases hqx : q ∣ x
            · rw [if_pos hqx, if_pos ⟨hpx, hqx⟩]
            · rw [if_neg hqx, if_neg (fun h => hqx h.2)]
          · rw [if_neg hpx]; symm; apply Finset.sum_eq_zero; intro q _
            rw [if_neg (fun h => hpx h.1)]
  -- swap to ∑_{p,q} c1 p c1 q S p q
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
  -- tail sum a p = 1/((p-1)(p-2))
  have htail_a : ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) ≤ 4 / (D:ℝ) := by
    have hpt : ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)))
        ≤ ∑ p ∈ Primes, (2 / ((p:ℝ) - 1) ^ 2) := by
      apply Finset.sum_le_sum; intro p hp
      obtain ⟨_, hpD, hp1, hp2⟩ := hprime_facts p hp
      have hp4 : (4:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 4 ≤ p)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hp1, hp2, hp4]
    calc ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)))
        ≤ ∑ p ∈ Primes, (2 / ((p:ℝ) - 1) ^ 2) := hpt
      _ = 2 * ∑ p ∈ Primes, (1 / ((p:ℝ) - 1) ^ 2) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ 2 * (2 / (D:ℝ)) := by apply mul_le_mul_of_nonneg_left (prime_tail' D R hD) (by norm_num)
      _ = 4 / (D:ℝ) := by ring
  -- S diag/off bounds
  have hmarked : ∀ s : ℕ, 0 < s →
      (∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r), (1 / (gMult x : ℝ)))
        ≤ (1 / (gMult s : ℝ)) * cg * Real.log R := by
    intro s hs
    have hmk := hcg D s R hD hDW hs hR2
    have hcv : ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r), (Real.log x)^0/(gMult x:ℝ)
        = ∑ x ∈ (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r), (1/(gMult x:ℝ)) := by
      apply Finset.sum_congr rfl; intro x _; rw [pow_zero]
    rw [hcv] at hmk; simpa using hmk
  have hS_diag : ∀ p ∈ Primes, S p p ≤ (1 / ((p:ℝ) - 2)) * cg * Real.log R := by
    intro p hp
    obtain ⟨hpp, _, _, _⟩ := hprime_facts p hp
    have hfe : F_R.filter (fun x => p ∣ x ∧ p ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3,_⟩; exact ⟨h1,h2,h3⟩
      · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1,h2⟩,h3,h3⟩
    simp only [hSdef]; rw [hfe]
    have := hmarked p hpp.pos; rw [gMult_prime_cast hpp] at this; exact this
  have hS_off : ∀ p ∈ Primes, ∀ q ∈ Primes, p ≠ q →
      S p q ≤ (1 / (((p:ℝ) - 2) * ((q:ℝ) - 2))) * cg * Real.log R := by
    intro p hp q hq hpq
    obtain ⟨hpp, _, _, _⟩ := hprime_facts p hp
    obtain ⟨hqp, _, _, _⟩ := hprime_facts q hq
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hpq
    have hfe : F_R.filter (fun x => p ∣ x ∧ q ∣ x)
        = (Finset.range R).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ p * q ∣ r) := by
      rw [hF_R, Finset.filter_filter]; apply Finset.filter_congr; intro x _
      constructor
      · rintro ⟨⟨h1,h2⟩,h3,h4⟩; exact ⟨h1,h2, hcop.mul_dvd_of_dvd_of_dvd h3 h4⟩
      · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1,h2⟩, (dvd_mul_right p q).trans h3, (dvd_mul_left q p).trans h3⟩
    simp only [hSdef]; rw [hfe]
    have := hmarked (p*q) (Nat.mul_pos hpp.pos hqp.pos)
    rw [gMult_pq_cast hpp hqp hpq] at this; exact this
  -- combine: split diag/off
  have hsplit : ∑ p ∈ Primes, ∑ q ∈ Primes, c1 p * c1 q * S p q
      = ∑ p ∈ Primes, c1 p * c1 p * S p p
        + ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p hp
    exact (Finset.add_sum_erase Primes (fun q => c1 p * c1 q * S p q) hp).symm
  rw [hsplit]
  -- diagonal bound ≤ cg logR * 4/D
  have hdiag : ∑ p ∈ Primes, c1 p * c1 p * S p p ≤ cg * Real.log R * (4 / (D:ℝ)) := by
    have hstep : ∑ p ∈ Primes, c1 p * c1 p * S p p
        ≤ ∑ p ∈ Primes, (cg * Real.log R) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by
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
        _ ≤ c1 p * ((1 / ((p:ℝ) - 2)) * cg * Real.log R) :=
            mul_le_mul_of_nonneg_left (hS_diag p hp) hc1nn
        _ = (cg * Real.log R) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by rw [← hap]; ring
    calc ∑ p ∈ Primes, c1 p * c1 p * S p p
        ≤ ∑ p ∈ Primes, (cg * Real.log R) * (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := hstep
      _ = (cg * Real.log R) * ∑ p ∈ Primes, (1 / (((p:ℝ) - 1) * ((p:ℝ) - 2))) := by rw [Finset.mul_sum]
      _ ≤ (cg * Real.log R) * (4 / (D:ℝ)) := mul_le_mul_of_nonneg_left htail_a hclogR
  -- off-diagonal bound ≤ cg logR * (4/D)^2
  have hoff : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
      ≤ cg * Real.log R * ((4 / (D:ℝ)) * (4 / (D:ℝ))) := by
    set a : ℕ → ℝ := fun p => 1 / (((p:ℝ) - 1) * ((p:ℝ) - 2)) with hadef
    have hann : ∀ p ∈ Primes, 0 ≤ a p := by
      intro p hp; obtain ⟨_,_,hp1,hp2⟩ := hprime_facts p hp; rw [hadef]; positivity
    have hstep1 : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (cg * Real.log R) * (a p * a q) := by
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
          ≤ c1 p * c1 q * ((1 / (((p:ℝ) - 2) * ((q:ℝ) - 2))) * cg * Real.log R) :=
            mul_le_mul_of_nonneg_left (hS_off p hp q hqP hne) hc1nn
        _ = (cg * Real.log R) * (a p * a q) := by rw [hc1def, hadef]; field_simp
    have hstep2 : ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (cg * Real.log R) * (a p * a q)
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes, (cg * Real.log R) * (a p * a q) := by
      apply Finset.sum_le_sum; intro p hp
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p Primes)
      intro q hq _
      exact mul_nonneg hclogR (mul_nonneg (hann p hp) (hann q hq))
    calc ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, c1 p * c1 q * S p q
        ≤ ∑ p ∈ Primes, ∑ q ∈ Primes.erase p, (cg * Real.log R) * (a p * a q) := hstep1
      _ ≤ ∑ p ∈ Primes, ∑ q ∈ Primes, (cg * Real.log R) * (a p * a q) := hstep2
      _ = (cg * Real.log R) * ((∑ p ∈ Primes, a p) * (∑ q ∈ Primes, a q)) := by
          rw [sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.mul_sum]
      _ ≤ (cg * Real.log R) * ((4 / (D:ℝ)) * (4 / (D:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hclogR
          apply mul_le_mul htail_a htail_a (Finset.sum_nonneg (fun q hq => hann q hq)) (by positivity)
  -- final: 4/D + 16/D^2 ≤ 20/D
  have hfinal : cg * Real.log R * (4 / (D:ℝ)) + cg * Real.log R * ((4 / (D:ℝ)) * (4 / (D:ℝ)))
      ≤ 20 * cg * Real.log R / (D:ℝ) := by
    have hD1 : (1:ℝ) ≤ (D:ℝ) := by linarith
    have hDsq : (4 / (D:ℝ)) * (4 / (D:ℝ)) ≤ 16 / (D:ℝ) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hDpos]; nlinarith
    have h2 : cg * Real.log R * ((4 / (D:ℝ)) * (4 / (D:ℝ))) ≤ cg * Real.log R * (16 / (D:ℝ)) :=
      mul_le_mul_of_nonneg_left hDsq hclogR
    have h3 : cg * Real.log R * (4 / (D:ℝ)) + cg * Real.log R * (16 / (D:ℝ))
        = 20 * cg * Real.log R / (D:ℝ) := by ring
    linarith
  linarith [hdiag, hoff, hfinal]

-- factor a single "marked" coordinate over the product box (n = 4)
private lemma factor_one (F_R : Finset ℕ) (i : Fin 4) (w : ℕ → ℝ) :
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
  have heval : ∀ k : Fin 4, (∑ x ∈ F_R, (if k = i then w x * (1 / (gMult x : ℝ)) else (1 / (gMult x : ℝ))))
      = if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ))) else (∑ x ∈ F_R, (1 / (gMult x : ℝ))) := by
    intro k; by_cases hk : k = i
    · simp only [hk, if_true]
    · simp only [hk, if_false]
  rw [Finset.prod_congr rfl (fun k _ => heval k)]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun k => if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ))) else (∑ x ∈ F_R, (1 / (gMult x : ℝ))))
      (Finset.mem_univ i)]
  rw [if_pos rfl]
  have hp2 : (∏ k ∈ Finset.univ.erase i,
      (if k = i then (∑ x ∈ F_R, w x * (1 / (gMult x : ℝ))) else (∑ x ∈ F_R, (1 / (gMult x : ℝ)))))
      = ∏ k ∈ Finset.univ.erase i, (∑ x ∈ F_R, (1 / (gMult x : ℝ))) :=
    Finset.prod_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))
  rw [hp2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

private lemma eval_bpoly_bound {n : ℕ} (P : BPoly n) (t : Fin n → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (hs : ∑ i, t i ≤ 1) :
    |eval P t| ≤ (P.map (fun mo => |(mo.2.2 : ℝ)|)).sum := by
  unfold eval
  refine le_trans (jlist_abs_sum_le P _) (jlist_sum_le _ _ _ (fun mo _ => ?_))
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

private lemma sum_biUnion_le {ι : Type*} (s : Finset ι) (t : ι → Finset ℕ)
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

-- subadditivity of the prime-factor weight over a product
private lemma P_subadd {n : ℕ} (ρ : Fin n → ℕ) (hρ : ∀ i, ρ i ≠ 0) :
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
        apply sum_biUnion_le
        intro i _ p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        have : (0:ℝ) < (p:ℝ) - 1 := by linarith
        positivity

-- common: enlarge a nonneg per-coordinate weighted sum from kSieveIndex4 (via decBox4) to the product box
private lemma enlarge_to_PB (W' D R : ℕ) (_hD : 3 ≤ D) (_hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p)
    (num : (Fin 4 → ℕ) → ℝ) (hnum0 : ∀ ρ, 0 ≤ num ρ) :
    (∑ ρ ∈ kSieveIndex 4 R W', num ρ / ∏ i, (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W')),
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

private lemma PFsum_nn (m : ℕ) : 0 ≤ ∑ p ∈ m.primeFactors, (1 / ((p:ℝ) - 1)) := by
  apply Finset.sum_nonneg; intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
  have : (0:ℝ) < (p:ℝ) - 1 := by linarith
  positivity

private lemma hT0_bound (W' : ℕ) (cg : ℝ)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R)
    (_hclogR : 0 ≤ cg * Real.log R) :
    (∑ ρ ∈ kSieveIndex 4 R W', (1:ℝ) / ∏ i, (gMult (ρ i) : ℝ)) ≤ (cg * Real.log R) ^ 4 := by
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ cg * Real.log R := M0_bound W' cg hcg D R hD hDW hR2
  have h1 := enlarge_to_PB W' D R hD hDW (fun _ => (1:ℝ)) (fun _ => zero_le_one)
  refine le_trans h1 ?_
  have hfac := factor_one F_R 0 (fun _ => (1:ℝ))
  simp only [one_mul] at hfac ⊢
  rw [hfac]
  calc (∑ x ∈ F_R, (1 / (gMult x : ℝ))) * (∑ x ∈ F_R, (1 / (gMult x : ℝ))) ^ 3
      = M0 ^ 4 := by rw [hM0def]; ring
    _ ≤ (cg * Real.log R) ^ 4 := pow_le_pow_left₀ hM0nn hM0le 4

private lemma hT1_bound (W' : ℕ) (cg : ℝ) (hcg0 : 0 ≤ cg)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R)
    (hlogR0 : 0 ≤ Real.log R) :
    (∑ ρ ∈ kSieveIndex 4 R W',
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) / ∏ i, (gMult (ρ i) : ℝ))
      ≤ 16 * cg ^ 4 * (Real.log R) ^ 4 / (D:ℝ) := by
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have hclogR : 0 ≤ cg * Real.log R := mul_nonneg hcg0 hlogR0
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ) with hMQdef
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ cg * Real.log R := M0_bound W' cg hcg D R hD hDW hR2
  have hMQnn : 0 ≤ MQ := Finset.sum_nonneg (fun x _ => div_nonneg (PFsum_nn _) (by positivity))
  have hMQle : MQ ≤ 4 * cg * Real.log R / (D:ℝ) := MQ_bound W' cg hcg0 hcg D R hD hDW hR2 hlogR0
  have h1 := enlarge_to_PB W' D R hD hDW
    (fun ρ => ∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) (fun ρ => PFsum_nn _)
  refine le_trans h1 ?_
  have hstep2 : ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R),
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ i, (1 / (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin 4 => F_R),
          (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
    apply Finset.sum_le_sum; intro ρ hr
    rw [Fintype.mem_piFinset] at hr
    have hρne : ∀ i, ρ i ≠ 0 := fun i => by
      have := hr i; rw [hF_R, Finset.mem_filter, Finset.mem_range] at this; exact this.2.1.ne_zero
    exact mul_le_mul_of_nonneg_right (P_subadd ρ hρne) (Finset.prod_nonneg (fun i _ => by positivity))
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
    rw [factor_one F_R i (fun x => ∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1)))]
    congr 1
    rw [hMQdef]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hM0cube : M0 ^ 3 ≤ (cg * Real.log R) ^ 3 := pow_le_pow_left₀ hM0nn hM0le 3
  have hMQM0 : MQ * M0 ^ 3 ≤ (4 * cg * Real.log R / (D:ℝ)) * (cg * Real.log R) ^ 3 :=
    mul_le_mul hMQle hM0cube (by positivity) (by positivity)
  calc (4:ℝ) * (MQ * M0 ^ 3) ≤ 4 * ((4 * cg * Real.log R / (D:ℝ)) * (cg * Real.log R) ^ 3) :=
        mul_le_mul_of_nonneg_left hMQM0 (by norm_num)
    _ = 16 * cg ^ 4 * (Real.log R) ^ 4 / (D:ℝ) := by ring

private lemma hT2_bound (W' : ℕ) (cg : ℝ) (hcg0 : 0 ≤ cg)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R)
    (hlogR0 : 0 ≤ Real.log R) :
    (∑ ρ ∈ kSieveIndex 4 R W',
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / ∏ i, (gMult (ρ i) : ℝ))
      ≤ 320 * cg ^ 4 * (Real.log R) ^ 4 / (D:ℝ) := by
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have hclogR : 0 ≤ cg * Real.log R := mul_nonneg hcg0 hlogR0
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set PB := Fintype.piFinset (fun _ : Fin 4 => F_R) with hPBdef
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ2 := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / (gMult x : ℝ) with hMQ2def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ cg * Real.log R := M0_bound W' cg hcg D R hD hDW hR2
  have hMQ2nn : 0 ≤ MQ2 := Finset.sum_nonneg (fun x _ => div_nonneg (sq_nonneg _) (by positivity))
  have hMQ2le : MQ2 ≤ 20 * cg * Real.log R / (D:ℝ) := MQ2_bound W' cg hcg0 hcg D R hD hDW hR2 hlogR0
  -- factor_one for Q^2 gives MQ2 * M0^3
  have hQsqmom : ∀ i : Fin 4,
      (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = MQ2 * M0 ^ 3 := by
    intro i
    rw [hPBdef, factor_one F_R i (fun x => (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2)]
    congr 1
    rw [hMQ2def]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  have h1 := enlarge_to_PB W' D R hD hDW
    (fun ρ => (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2) (fun ρ => sq_nonneg _)
  refine le_trans h1 ?_
  rw [← hPBdef]
  -- P̃^2 ≤ (∑ Q)^2 = ∑_i ∑_j Q_i Q_j ; then distribute and bound each pair
  have hstep2 : ∑ ρ ∈ PB,
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ i, (1 / (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ PB, (∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
              * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) := by
    apply Finset.sum_le_sum; intro ρ hr
    rw [hPBdef, Fintype.mem_piFinset] at hr
    have hρne : ∀ i, ρ i ≠ 0 := fun i => by
      have := hr i; rw [hF_R, Finset.mem_filter, Finset.mem_range] at this; exact this.2.1.ne_zero
    have hsub := P_subadd ρ hρne
    have hsq : (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
        ≤ (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) ^ 2 :=
      pow_le_pow_left₀ (PFsum_nn _) hsub 2
    have hexp : (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) ^ 2
        = ∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
              * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) := by rw [pow_two, sum_mul_sum]
    rw [hexp] at hsq
    exact mul_le_mul_of_nonneg_right hsq (Finset.prod_nonneg (fun k _ => by positivity))
  refine le_trans hstep2 ?_
  -- distribute ∏(1/g) and swap
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
  -- per (i,j): AM-GM
  have hij : ∀ i j : Fin 4,
      (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      ≤ MQ2 * M0 ^ 3 := by
    intro i j
    have hamgm : ∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
        ≤ ∑ ρ ∈ PB, (1/2) * ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ k, (1 / (gMult (ρ k) : ℝ))
            + (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ k, (1 / (gMult (ρ k) : ℝ))) := by
      apply Finset.sum_le_sum; intro ρ _
      have hprodnn : 0 ≤ ∏ k, (1 / (gMult (ρ k) : ℝ)) := Finset.prod_nonneg (fun k _ => by positivity)
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
    _ ≤ 320 * cg ^ 4 * (Real.log R) ^ 4 / (D:ℝ) := by
        have hM0cube : M0 ^ 3 ≤ (cg * Real.log R) ^ 3 := pow_le_pow_left₀ hM0nn hM0le 3
        have hMM : MQ2 * M0 ^ 3 ≤ (20 * cg * Real.log R / (D:ℝ)) * (cg * Real.log R) ^ 3 :=
          mul_le_mul hMQ2le hM0cube (by positivity) (by positivity)
        calc (16:ℝ) * (MQ2 * M0 ^ 3)
            ≤ 16 * ((20 * cg * Real.log R / (D:ℝ)) * (cg * Real.log R) ^ 3) :=
              mul_le_mul_of_nonneg_left hMM (by norm_num)
          _ = 320 * cg ^ 4 * (Real.log R) ^ 4 / (D:ℝ) := by ring

private lemma absorb6 (κ L X : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL1 : 1 ≤ L) (hX : X = κ * L) :
    (L ^ 4 ≤ (1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L))
    ∧ (X * L ^ 4 ≤ (1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L))
    ∧ (X ^ 2 * L ^ 4 ≤ (1 / κ ^ 4) * (1 + X) ^ 6)
    ∧ (X * L ^ 4 ≤ (1 / κ ^ 5) * (1 + X) ^ 6)
    ∧ (X ^ 2 * (1 + X) ^ 4 ≤ (1 + X) ^ 6) := by
  have hLpos : 0 < L := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hB0 : 0 ≤ 1 + X := by linarith
  have hκL : κ * L ≤ 1 + X := by rw [hX]; linarith
  have hbase : κ ^ 6 * L ^ 6 ≤ (1 + X) ^ 6 := by
    calc κ ^ 6 * L ^ 6 = (κ * L) ^ 6 := by ring
      _ ≤ (1 + X) ^ 6 := pow_le_pow_left₀ (by positivity) hκL 6
  have hκ0' : (0:ℝ) < κ ^ 6 := by positivity
  have hLL : L ^ 5 ≤ L ^ 6 := by
    have : L ^ 5 * 1 ≤ L ^ 5 * L := by
      apply mul_le_mul_of_nonneg_left hL1 (by positivity)
    calc L ^ 5 = L ^ 5 * 1 := by ring
      _ ≤ L ^ 5 * L := this
      _ = L ^ 6 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- L^4 ≤ (1/κ^6)(1+X)^6/L : clear to κ^6 L^5 ≤ (1+X)^6
    rw [show (1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L) = (1 + X) ^ 6 / (κ ^ 6 * L) by field_simp,
      le_div_iff₀ (by positivity)]
    calc L ^ 4 * (κ ^ 6 * L) = κ ^ 6 * L ^ 5 := by ring
      _ ≤ κ ^ 6 * L ^ 6 := by apply mul_le_mul_of_nonneg_left hLL (by positivity)
      _ ≤ (1 + X) ^ 6 := hbase
  · -- X L^4 ≤ (1/κ^6)(1+X)^6/L : clear to κ^6 X L^5 ≤ (1+X)^6, X=κL ⟹ κ^7 L^6
    rw [show (1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L) = (1 + X) ^ 6 / (κ ^ 6 * L) by field_simp,
      le_div_iff₀ (by positivity)]
    calc X * L ^ 4 * (κ ^ 6 * L) = κ * (κ ^ 6 * L ^ 6) := by rw [hX]; ring
      _ ≤ 1 * (κ ^ 6 * L ^ 6) := by apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = κ ^ 6 * L ^ 6 := by ring
      _ ≤ (1 + X) ^ 6 := hbase
  · -- X^2 L^4 ≤ (1/κ^4)(1+X)^6 : X=κL ⟹ κ^6 L^6
    rw [show (1 / κ ^ 4) * (1 + X) ^ 6 = (1 + X) ^ 6 / κ ^ 4 by field_simp,
      le_div_iff₀ (by positivity)]
    calc X ^ 2 * L ^ 4 * κ ^ 4 = κ ^ 6 * L ^ 6 := by rw [hX]; ring
      _ ≤ (1 + X) ^ 6 := hbase
  · -- X L^4 ≤ (1/κ^5)(1+X)^6 : X=κL ⟹ κ^6 L^5
    rw [show (1 / κ ^ 5) * (1 + X) ^ 6 = (1 + X) ^ 6 / κ ^ 5 by field_simp,
      le_div_iff₀ (by positivity)]
    calc X * L ^ 4 * κ ^ 5 = κ ^ 6 * L ^ 5 := by rw [hX]; ring
      _ ≤ κ ^ 6 * L ^ 6 := by apply mul_le_mul_of_nonneg_left hLL (by positivity)
      _ ≤ (1 + X) ^ 6 := hbase
  · -- X^2 (1+X)^4 ≤ (1+X)^6
    calc X ^ 2 * (1 + X) ^ 4 ≤ (1 + X) ^ 2 * (1 + X) ^ 4 := by
          apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX0 (by linarith) 2) (by positivity)
      _ = (1 + X) ^ 6 := by ring

set_option maxHeartbeats 2000000 in
-- The final square-expand assembly (inner_contract substitution, the three swap
-- sums, and the κ-power absorptions) is elaborated in one block; over budget.
theorem mv_J (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) (m : Fin 5) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
            (∑ u ∈ Finset.range R,
                yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
              / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
            * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6
          * (1 / Real.log R + 1 / D) := by
  classical
  obtain ⟨cic, hcic0, hcic⟩ := inner_contract W' hW' hpos hUpper F m
  obtain ⟨cmain, hcmain0, hcmain⟩ := mv_J_main W' hW' hpos hUpper F m
  obtain ⟨cg, hcg0, hcg⟩ := marked_sqf_g W' hW' hpos 0
  set cF : ℝ := ((contractAt m F).map (fun mo => |(mo.2.2 : ℝ)|)).sum with hcFdef
  have hcF0 : 0 ≤ cF := by
    rw [hcFdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨mo, _, rfl⟩ := hx; exact abs_nonneg _
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  have hκle1 : κ ≤ 1 := by
    rw [hκdef, div_le_one (by exact_mod_cast hpos)]; exact_mod_cast Nat.totient_le W'
  refine ⟨cmain + 2*cF*cic*cg^4/κ^6 + cic^2*cg^4/κ^6 + 32*cF*cic*cg^4/κ^4
            + 32*cic^2*cg^4/κ^5 + 320*cic^2*cg^4/κ^4, by positivity, ?_⟩
  intro D R hD hDW hlogR
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
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hDpos : (0:ℝ) < (D:ℝ) := by
    have : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    linarith
  have hclogR : 0 ≤ cg * L := mul_nonneg hcg0 hLpos.le
  -- abbreviations
  set filt := (kSieveIndex 5 R W').filter (fun r => r m = 1) with hfiltdef
  set Denom : (Fin 5 → ℕ) → ℝ := fun r => ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) with hDenomdef
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
  -- per-r product/log facts
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
    apply eval_bpoly_bound
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
  -- inner_contract per r
  have hInnbd : ∀ r ∈ filt, |Inn r - X * Ev r| ≤ cic * (1 + X * Pr r) := by
    intro r hr
    rw [hfiltdef, Finset.mem_filter] at hr
    have := hcic D R hD hDW hlogR r hr.1 hr.2
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
    rw [erase_prod_removeNth m (fun i => (gMult (r i):ℝ)), hprodeq r hrf]
  -- S0, S1, S2 bounds
  have hS0le : (∑ r ∈ filt, (1:ℝ) / Denom r) ≤ (cg * L) ^ 4 := by
    have key : (∑ r ∈ filt, (1:ℝ) / Denom r)
        = ∑ ρ ∈ kSieveIndex 4 R W', (1:ℝ) / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun _ => 1)
    rw [key]; exact hT0_bound W' cg hcg D R hD hDW hR2 hclogR
  have hS1le : (∑ r ∈ filt, Pr r / Denom r) ≤ 16 * cg ^ 4 * L ^ 4 / (D:ℝ) := by
    have key : (∑ r ∈ filt, Pr r / Denom r)
        = ∑ ρ ∈ kSieveIndex 4 R W',
            (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun N => ∑ p ∈ N.primeFactors, (1 / ((p:ℝ) - 1)))
    rw [key]; exact hT1_bound W' cg hcg0 hcg D R hD hDW hR2 hLpos.le
  have hS2le : (∑ r ∈ filt, (Pr r) ^ 2 / Denom r) ≤ 320 * cg ^ 4 * L ^ 4 / (D:ℝ) := by
    have key : (∑ r ∈ filt, (Pr r) ^ 2 / Denom r)
        = ∑ ρ ∈ kSieveIndex 4 R W',
            (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun N => (∑ p ∈ N.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2)
    rw [key]; exact hT2_bound W' cg hcg0 hcg D R hD hDW hR2 hLpos.le
  -- === main part via mv_J_main ===
  obtain ⟨hab1, hab2, hab3, hab4, hab5⟩ := absorb6 κ L X hκpos hκle1 hL1 hXdef
  have hEvSum : |(∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
        - X ^ 4 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ cmain * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ)) := by
    have h := hcmain D R hD hDW hlogR
    rw [hX_eq] at h
    exact h
  have hmainpart : |X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
        - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ cmain * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
    have hfac : X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
          - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)
        = X ^ 2 * ((∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
          - X ^ 4 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ X ^ 2)]
    have hLD : 0 ≤ 1 / L + 1 / (D:ℝ) := by positivity
    calc X ^ 2 * |(∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
            - X ^ 4 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ X ^ 2 * (cmain * (1 + X) ^ 4 * (1 / L + 1 / (D:ℝ))) :=
          mul_le_mul_of_nonneg_left hEvSum (by positivity)
      _ = cmain * (X ^ 2 * (1 + X) ^ 4) * (1 / L + 1 / (D:ℝ)) := by ring
      _ ≤ cmain * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hLD
          exact mul_le_mul_of_nonneg_left hab5 hcmain0
  -- === error part ===
  have hPrnn : ∀ r, 0 ≤ Pr r := fun r => by rw [hPrdef]; exact PFsum_nn _
  have hterm : ∀ r ∈ filt,
      |(Inn r) ^ 2 / Denom r - X ^ 2 * ((Ev r) ^ 2 / Denom r)|
      ≤ (2 * X * cF * cic * (1 + X * Pr r) + cic ^ 2 * (1 + X * Pr r) ^ 2) / Denom r := by
    intro r hr
    have hdpos := hDenompos r hr
    have hE := hEvbd r hr
    have hI := hInnbd r hr
    have hPr := hPrnn r
    have hbase : (1 + X * Pr r) ≥ 1 := by nlinarith [hX0, hPr]
    have hδbd : |Inn r - X * Ev r| ≤ cic * (1 + X * Pr r) := hI
    have hδnn : 0 ≤ cic * (1 + X * Pr r) := mul_nonneg hcic0 (by linarith)
    have hnum : (Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2
        = 2 * X * (Ev r) * (Inn r - X * Ev r) + (Inn r - X * Ev r) ^ 2 := by ring
    have habs : |(Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2|
        ≤ 2 * X * cF * cic * (1 + X * Pr r) + cic ^ 2 * (1 + X * Pr r) ^ 2 := by
      rw [hnum]
      have h1 : |2 * X * (Ev r) * (Inn r - X * Ev r)| = 2 * X * |Ev r| * |Inn r - X * Ev r| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * X)]
      have h2 : |2 * X * (Ev r) * (Inn r - X * Ev r)| ≤ 2 * X * cF * (cic * (1 + X * Pr r)) := by
        rw [h1]
        have hb : |Ev r| * |Inn r - X * Ev r| ≤ cF * (cic * (1 + X * Pr r)) :=
          mul_le_mul hE hδbd (abs_nonneg _) hcF0
        calc 2 * X * |Ev r| * |Inn r - X * Ev r| = 2 * X * (|Ev r| * |Inn r - X * Ev r|) := by ring
          _ ≤ 2 * X * (cF * (cic * (1 + X * Pr r))) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = 2 * X * cF * (cic * (1 + X * Pr r)) := by ring
      have h3 : |(Inn r - X * Ev r) ^ 2| ≤ cic ^ 2 * (1 + X * Pr r) ^ 2 := by
        rw [abs_pow, ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hδbd 2
      calc |2 * X * (Ev r) * (Inn r - X * Ev r) + (Inn r - X * Ev r) ^ 2|
          ≤ |2 * X * (Ev r) * (Inn r - X * Ev r)| + |(Inn r - X * Ev r) ^ 2| := abs_add_le _ _
        _ ≤ 2 * X * cF * (cic * (1 + X * Pr r)) + cic ^ 2 * (1 + X * Pr r) ^ 2 := add_le_add h2 h3
        _ = 2 * X * cF * cic * (1 + X * Pr r) + cic ^ 2 * (1 + X * Pr r) ^ 2 := by ring
    have heq : (Inn r) ^ 2 / Denom r - X ^ 2 * ((Ev r) ^ 2 / Denom r)
        = ((Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2) / Denom r := by ring
    rw [heq, abs_div, abs_of_pos hdpos]
    exact div_le_div_of_nonneg_right habs hdpos.le
  have herr : |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
        - X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)|
      ≤ ∑ r ∈ filt, (2 * X * cF * cic * (1 + X * Pr r)
          + cic ^ 2 * (1 + X * Pr r) ^ 2) / Denom r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  -- expand the error sum into S0, S1, S2
  have hbound_eq : (∑ r ∈ filt, (2 * X * cF * cic * (1 + X * Pr r)
          + cic ^ 2 * (1 + X * Pr r) ^ 2) / Denom r)
      = (2 * X * cF * cic + cic ^ 2) * (∑ r ∈ filt, 1 / Denom r)
        + (2 * X ^ 2 * cF * cic + 2 * cic ^ 2 * X) * (∑ r ∈ filt, Pr r / Denom r)
        + cic ^ 2 * X ^ 2 * (∑ r ∈ filt, (Pr r) ^ 2 / Denom r) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  -- bound the error sum
  have herr2 : (∑ r ∈ filt, (2 * X * cF * cic * (1 + X * Pr r)
          + cic ^ 2 * (1 + X * Pr r) ^ 2) / Denom r)
      ≤ (2 * X * cF * cic + cic ^ 2) * (cg * L) ^ 4
        + (2 * X ^ 2 * cF * cic + 2 * cic ^ 2 * X) * (16 * cg ^ 4 * L ^ 4 / (D:ℝ))
        + cic ^ 2 * X ^ 2 * (320 * cg ^ 4 * L ^ 4 / (D:ℝ)) := by
    rw [hbound_eq]
    have c0 : 0 ≤ 2 * X * cF * cic + cic ^ 2 := by positivity
    have c1 : 0 ≤ 2 * X ^ 2 * cF * cic + 2 * cic ^ 2 * X := by positivity
    have c2 : 0 ≤ cic ^ 2 * X ^ 2 := by positivity
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hS0le c0
    · exact mul_le_mul_of_nonneg_left hS1le c1
    · exact mul_le_mul_of_nonneg_left hS2le c2
  -- === absorptions to (1+X)^6*(1/L+1/D) ===
  have hUnn : (0:ℝ) ≤ (1 + X) ^ 6 := by positivity
  have hLLD : (1:ℝ) / L ≤ 1 / L + 1 / (D:ℝ) := by
    have : (0:ℝ) ≤ 1 / (D:ℝ) := by positivity
    linarith
  have hDLD : (1:ℝ) / (D:ℝ) ≤ 1 / L + 1 / (D:ℝ) := by
    have : (0:ℝ) ≤ 1 / L := by positivity
    linarith
  have ha_L : L ^ 4 ≤ (1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) :=
    le_trans hab1 (mul_le_mul_of_nonneg_left hLLD (by positivity))
  have ha_XL : X * L ^ 4 ≤ (1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) :=
    le_trans hab2 (mul_le_mul_of_nonneg_left hLLD (by positivity))
  have ha_X2L_D : X ^ 2 * L ^ 4 * (1 / (D:ℝ)) ≤ (1 / κ ^ 4) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
    calc X ^ 2 * L ^ 4 * (1 / (D:ℝ)) ≤ ((1 / κ ^ 4) * (1 + X) ^ 6) * (1 / (D:ℝ)) :=
          mul_le_mul_of_nonneg_right hab3 (by positivity)
      _ ≤ ((1 / κ ^ 4) * (1 + X) ^ 6) * (1 / L + 1 / (D:ℝ)) :=
          mul_le_mul_of_nonneg_left hDLD (by positivity)
      _ = (1 / κ ^ 4) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by ring
  have ha_XL_D : X * L ^ 4 * (1 / (D:ℝ)) ≤ (1 / κ ^ 5) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
    calc X * L ^ 4 * (1 / (D:ℝ)) ≤ ((1 / κ ^ 5) * (1 + X) ^ 6) * (1 / (D:ℝ)) :=
          mul_le_mul_of_nonneg_right hab4 (by positivity)
      _ ≤ ((1 / κ ^ 5) * (1 + X) ^ 6) * (1 / L + 1 / (D:ℝ)) :=
          mul_le_mul_of_nonneg_left hDLD (by positivity)
      _ = (1 / κ ^ 5) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by ring
  -- three grouped bounds
  have hm1 : (2 * X * cF * cic + cic ^ 2) * (cg * L) ^ 4
      ≤ (2 * cF * cic * cg ^ 4 / κ ^ 6 + cic ^ 2 * cg ^ 4 / κ ^ 6) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
    have e : (2 * X * cF * cic + cic ^ 2) * (cg * L) ^ 4
        = (2 * cF * cic * cg ^ 4) * (X * L ^ 4) + (cic ^ 2 * cg ^ 4) * (L ^ 4) := by ring
    rw [e]
    calc (2 * cF * cic * cg ^ 4) * (X * L ^ 4) + (cic ^ 2 * cg ^ 4) * (L ^ 4)
        ≤ (2 * cF * cic * cg ^ 4) * ((1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)))
          + (cic ^ 2 * cg ^ 4) * ((1 / κ ^ 6) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_left ha_XL (by positivity))
            (mul_le_mul_of_nonneg_left ha_L (by positivity))
      _ = (2 * cF * cic * cg ^ 4 / κ ^ 6 + cic ^ 2 * cg ^ 4 / κ ^ 6) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by ring
  have hm2 : (2 * X ^ 2 * cF * cic + 2 * cic ^ 2 * X) * (16 * cg ^ 4 * L ^ 4 / (D:ℝ))
      ≤ (32 * cF * cic * cg ^ 4 / κ ^ 4 + 32 * cic ^ 2 * cg ^ 4 / κ ^ 5) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
    have e : (2 * X ^ 2 * cF * cic + 2 * cic ^ 2 * X) * (16 * cg ^ 4 * L ^ 4 / (D:ℝ))
        = (32 * cF * cic * cg ^ 4) * (X ^ 2 * L ^ 4 * (1 / (D:ℝ)))
          + (32 * cic ^ 2 * cg ^ 4) * (X * L ^ 4 * (1 / (D:ℝ))) := by ring
    rw [e]
    calc (32 * cF * cic * cg ^ 4) * (X ^ 2 * L ^ 4 * (1 / (D:ℝ)))
          + (32 * cic ^ 2 * cg ^ 4) * (X * L ^ 4 * (1 / (D:ℝ)))
        ≤ (32 * cF * cic * cg ^ 4) * ((1 / κ ^ 4) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)))
          + (32 * cic ^ 2 * cg ^ 4) * ((1 / κ ^ 5) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_left ha_X2L_D (by positivity))
            (mul_le_mul_of_nonneg_left ha_XL_D (by positivity))
      _ = (32 * cF * cic * cg ^ 4 / κ ^ 4 + 32 * cic ^ 2 * cg ^ 4 / κ ^ 5) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by ring
  have hm3 : cic ^ 2 * X ^ 2 * (320 * cg ^ 4 * L ^ 4 / (D:ℝ))
      ≤ (320 * cic ^ 2 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
    have e : cic ^ 2 * X ^ 2 * (320 * cg ^ 4 * L ^ 4 / (D:ℝ))
        = (320 * cic ^ 2 * cg ^ 4) * (X ^ 2 * L ^ 4 * (1 / (D:ℝ))) := by ring
    rw [e]
    calc (320 * cic ^ 2 * cg ^ 4) * (X ^ 2 * L ^ 4 * (1 / (D:ℝ)))
        ≤ (320 * cic ^ 2 * cg ^ 4) * ((1 / κ ^ 4) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ))) :=
          mul_le_mul_of_nonneg_left ha_X2L_D (by positivity)
      _ = (320 * cic ^ 2 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by ring
  -- === final assembly ===
  have hgoal : |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
        - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ (cmain + 2 * cF * cic * cg ^ 4 / κ ^ 6 + cic ^ 2 * cg ^ 4 / κ ^ 6
          + 32 * cF * cic * cg ^ 4 / κ ^ 4 + 32 * cic ^ 2 * cg ^ 4 / κ ^ 5
          + 320 * cic ^ 2 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
    calc |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
            - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r) - X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)|
          + |X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
            - X ^ 6 * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)| := abs_sub_le _ _ _
      _ ≤ ((2 * X * cF * cic + cic ^ 2) * (cg * L) ^ 4
            + (2 * X ^ 2 * cF * cic + 2 * cic ^ 2 * X) * (16 * cg ^ 4 * L ^ 4 / (D:ℝ))
            + cic ^ 2 * X ^ 2 * (320 * cg ^ 4 * L ^ 4 / (D:ℝ)))
          + cmain * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) :=
          add_le_add (le_trans herr herr2) hmainpart
      _ ≤ (cmain + 2 * cF * cic * cg ^ 4 / κ ^ 6 + cic ^ 2 * cg ^ 4 / κ ^ 6
            + 32 * cF * cic * cg ^ 4 / κ ^ 4 + 32 * cic ^ 2 * cg ^ 4 / κ ^ 5
            + 320 * cic ^ 2 * cg ^ 4 / κ ^ 4) * (1 + X) ^ 6 * (1 / L + 1 / (D:ℝ)) := by
          nlinarith [hm1, hm2, hm3]
  exact hgoal

end Salt.Twelve
