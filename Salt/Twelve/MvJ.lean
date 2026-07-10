/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.BudgetMoment
import Salt.Twelve.W3Prep
import Salt.Maynard.KSieve

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

end Salt.Twelve
