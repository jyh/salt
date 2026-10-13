/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.MvSplit
import Salt.MaynardK.MvJGen

/-!
# C1 · B4.2b (E1) — `inner_contract_rel` at general `n` and budget power `d`

`inner_contract_rel_gen` proves `InnerContractRelGen` (the hypothesis the J-split engine consumes):
`MvJGen`'s budget-power-`d` inner estimate with `MvSplit`'s PAS-relative coprimality drop
(`marked_sqf_phi_rel` at `a = 0`); the cap slips stay in `c`, `A` is chosen before `W'`.
Ported by an Opus executor from a frozen brief (2026-10-11).
-/

open Finset

namespace Salt.MaynardK
variable [Salt.Maynard.TupleChoice]

open Salt.Twelve Salt.Maynard Salt.MaynardK

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
private lemma prod_update_eq {n : ℕ} {r : Fin (n + 1) → ℕ} {m : Fin (n + 1)} (hrm : r m = 1)
        (u : ℕ) :
    ∏ i, Function.update r m u i = u * ∏ i, r i := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ m)]
  congr 1
  rw [← Finset.erase_eq]
  exact Finset.prod_erase _ hrm

/-- Membership of `Function.update r m u` in the sieve box, unfolded to the
one-dimensional conditions on `u`. -/
private lemma update_mem_kSieveIndex_iff {R W' : ℕ} {n : ℕ} {r : Fin (n + 1) → ℕ}
    (hr : r ∈ kSieveIndex (n + 1) R W') {m : Fin (n + 1)} (hrm : r m = 1) (u : ℕ) :
    Function.update r m u ∈ kSieveIndex (n + 1) R W' ↔
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

/-! ## The one-dimensional inner-sum estimate, with the budget exponent `d` -/

/-- The inner one-dimensional sum for a budget monomial `t_m^c · (1 − Σt)^d`. -/
private lemma inner_sum_estimate_brel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') {n R : ℕ} (hR : 1 ≤ Real.log R)
    {r : Fin (n + 1) → ℕ} (hr : r ∈ kSieveIndex (n + 1) R W') {m : Fin (n + 1)} (hrm : r m = 1)
    (c d : ℕ) :
    |(∑ u ∈ (Finset.range R).filter
            (fun u => Function.update r m u ∈ kSieveIndex (n + 1) R W'),
          (Real.log u / Real.log R) ^ c
            * ((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ d
            / (Nat.totient u : ℝ))
      - ((W'.totient : ℝ) / W' * Real.log R)
          * ((c.factorial * d.factorial : ℝ) / (c + d + 1).factorial)
          * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + d + 1)|
    ≤ (budget_moment W' hW' hpos hUpper c d).choose * 4 ^ (d + c)
      + ((c.factorial * d.factorial : ℝ) / (c + d + 1).factorial) * ((c + d + 1 : ℕ) : ℝ)
          * Real.log 2
      + (d : ℝ) * Real.log 2 * (marked_sqf_phi W' hW' hpos 0).choose
      + Salt.Maynard.phiAtomSum R W'
          * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
  classical
  obtain ⟨hCatom0, hbudgetspec⟩ := (budget_moment W' hW' hpos hUpper c d).choose_spec
  obtain ⟨hC00, hm0spec⟩ := (marked_sqf_phi W' hW' hpos 0).choose_spec
  set Catom := (budget_moment W' hW' hpos hUpper c d).choose with hCatomdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set C0 := (marked_sqf_phi W' hW' hpos 0).choose with hC0def
  set β : ℝ := (c.factorial * d.factorial : ℝ) / (c + d + 1).factorial with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLpos : 0 < Real.log R := lt_of_lt_of_le zero_lt_one hR
  have hLne : Real.log R ≠ 0 := ne_of_gt hLpos
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
      (Finset.range R).filter (fun u => Function.update r m u ∈ kSieveIndex (n + 1) R W')
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
  have hzlog0 : (0 : ℝ) ≤ Real.log (z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  have hQR : (0:ℝ) < ∏ i, (r i : ℝ) := by rw [← Nat.cast_prod]; exact_mod_cast hQpos
  have hQlog0 : (0 : ℝ) ≤ Real.log (∏ i, r i) :=
    Real.log_nonneg (by rw [← Nat.cast_prod]; exact_mod_cast hQpos)
  have hQlogR : Real.log (∏ i, r i) ≤ Real.log R := by
    rw [← Nat.cast_prod]
    exact Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQltR.le)
  -- the cap slip `|log z − (log R − log ∏r)| ≤ log 2`
  have hAB0 : |Real.log (z : ℝ) - (Real.log R - Real.log (∏ i, r i))| ≤ Real.log 2 := by
    have hslipnat := log_natCap_slip (∏ i, r i) R hQpos hQltR
    rw [Nat.cast_prod] at hslipnat
    rw [← hzdef] at hslipnat
    exact hslipnat
  set T := (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W') with hTdef
  have hTmem : ∀ u ∈ T, 1 ≤ u ∧ u < z := by
    intro u hu
    rw [hTdef, Finset.mem_filter, Finset.mem_range] at hu
    exact ⟨Nat.pos_of_ne_zero hu.2.1.ne_zero, hu.1⟩
  -- per-u facts
  have hufacts : ∀ u ∈ T,
      (0:ℝ) < (Nat.totient u : ℝ) ∧ 0 ≤ (Real.log u / Real.log R) ^ c
        ∧ (Real.log u / Real.log R) ^ c ≤ 1
        ∧ 0 ≤ (Real.log z - Real.log u) / Real.log R
        ∧ (Real.log z - Real.log u) / Real.log R ≤ 1 := by
    intro u hu
    obtain ⟨hu1, huz⟩ := hTmem u hu
    have hφu : (0:ℝ) < (Nat.totient u : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hlu0 : 0 ≤ Real.log (u:ℝ) := Real.log_nonneg (by exact_mod_cast hu1)
    have hluz : Real.log (u:ℝ) ≤ Real.log z :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < u)) (by exact_mod_cast huz.le)
    have ha0 : 0 ≤ Real.log (u:ℝ) / Real.log R := div_nonneg hlu0 hLpos.le
    have ha1 : Real.log (u:ℝ) / Real.log R ≤ 1 := by rw [div_le_one hLpos]; linarith
    refine ⟨hφu, pow_nonneg ha0 _, pow_le_one₀ ha0 ha1, div_nonneg (by linarith) hLpos.le, ?_⟩
    rw [div_le_one hLpos]; linarith
  -- === (1) the budget slip: real budget vs ℕ-cap budget, on the coprime set ===
  have hbs : ∀ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
      |(Real.log u / Real.log R) ^ c
          * ((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ d
          / (Nat.totient u : ℝ)
        - (Real.log u / Real.log R) ^ c
          * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ)|
      ≤ (d : ℝ) * (Real.log 2 / Real.log R) * (1 / (Nat.totient u : ℝ)) := by
    intro u hu
    have huT : u ∈ T := Finset.mem_of_mem_filter u hu
    obtain ⟨hu1, huz⟩ := hTmem u huT
    obtain ⟨hφu, hac0, hac1, hB20, hB21⟩ := hufacts u huT
    have hlu0 : 0 ≤ Real.log (u:ℝ) := Real.log_nonneg (by exact_mod_cast hu1)
    have huQ : u * (∏ i, r i) < R := (hcap u).mpr huz
    have hluQ : Real.log (u:ℝ) + Real.log (∏ i, r i) ≤ Real.log R := by
      rw [← Real.log_mul (by exact_mod_cast (by omega : u ≠ 0)) hQR.ne', ← Nat.cast_prod,
        ← Nat.cast_mul]
      exact Real.log_le_log (by exact_mod_cast Nat.mul_pos (by omega) hQpos)
        (by exact_mod_cast huQ.le)
    have hB10 : 0 ≤ (Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R :=
      div_nonneg (by linarith) hLpos.le
    have hB11 : (Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R ≤ 1 := by
      rw [div_le_one hLpos]; linarith
    have hB12 : |(Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R
        - (Real.log z - Real.log u) / Real.log R| ≤ Real.log 2 / Real.log R := by
      have e : (Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R
          - (Real.log z - Real.log u) / Real.log R
          = -(Real.log z - (Real.log R - Real.log (∏ i, r i))) / Real.log R := by ring
      rw [e, abs_div, abs_neg, abs_of_pos hLpos]
      exact div_le_div_of_nonneg_right hAB0 hLpos.le
    have hpow := abs_pow_sub_pow_le_unit hB10 hB11 hB20 hB21 d
    have e2 : (Real.log u / Real.log R) ^ c
          * ((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ d
          / (Nat.totient u : ℝ)
        - (Real.log u / Real.log R) ^ c
          * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ)
        = (Real.log u / Real.log R) ^ c
          * (((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ d
            - ((Real.log z - Real.log u) / Real.log R) ^ d) / (Nat.totient u : ℝ) := by ring
    rw [e2, abs_div, abs_mul, abs_of_nonneg hac0, abs_of_pos hφu]
    calc (Real.log u / Real.log R) ^ c
          * |((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ d
            - ((Real.log z - Real.log u) / Real.log R) ^ d| / (Nat.totient u : ℝ)
        ≤ 1 * ((d : ℝ) * (Real.log 2 / Real.log R)) / (Nat.totient u : ℝ) := by
          apply div_le_div_of_nonneg_right _ hφu.le
          exact mul_le_mul hac1 (hpow.trans (mul_le_mul_of_nonneg_left hB12 (Nat.cast_nonneg _)))
            (abs_nonneg _) zero_le_one
      _ = (d : ℝ) * (Real.log 2 / Real.log R) * (1 / (Nat.totient u : ℝ)) := by ring
  have hsum1 : (∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)), (1 / (Nat.totient u : ℝ)))
      ≤ C0 * Real.log R := by
    have h := hm0spec 1 z one_pos hz2
    have hfe : (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W' ∧ 1 ∣ u) = T := by
      rw [hTdef]; apply Finset.filter_congr; intro u _; simp
    rw [hfe] at h
    have h' : (∑ u ∈ T, (1 / (Nat.totient u : ℝ))) ≤ C0 * Real.log z := by
      have e1 : (∑ u ∈ T, (1 / (Nat.totient u : ℝ)))
          = ∑ u ∈ T, (Real.log u) ^ 0 / (Nat.totient u : ℝ) := by
        apply Finset.sum_congr rfl; intro u _; rw [pow_zero]
      rw [e1]; refine h.trans (le_of_eq ?_); simp
    calc (∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)), (1 / (Nat.totient u : ℝ)))
        ≤ ∑ u ∈ T, (1 / (Nat.totient u : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ ≤ C0 * Real.log z := h'
      _ ≤ C0 * Real.log R := mul_le_mul_of_nonneg_left hzR' hC00
  have hbslip :
      |(∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c
            * ((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ d
            / (Nat.totient u : ℝ))
        - (∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c
            * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))|
      ≤ (d : ℝ) * Real.log 2 * C0 := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
            (d : ℝ) * (Real.log 2 / Real.log R) * (1 / (Nat.totient u : ℝ)) :=
          Finset.sum_le_sum hbs
      _ = (d : ℝ) * (Real.log 2 / Real.log R)
            * ∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)), (1 / (Nat.totient u : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ (d : ℝ) * (Real.log 2 / Real.log R) * (C0 * Real.log R) :=
          mul_le_mul_of_nonneg_left hsum1 (by positivity)
      _ = (d : ℝ) * Real.log 2 * C0 * (Real.log R / Real.log R) := by ring
      _ = (d : ℝ) * Real.log 2 * C0 := by rw [div_self hLne, mul_one]
  -- === (2) the coprimality drop (marked primes) ===
  have hmarked_p : ∀ p ∈ (∏ i, r i).primeFactors,
      (∑ u ∈ T.filter (fun u => p ∣ u), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ PAS * (1 / ((p : ℝ) - 1)) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpQ, _⟩ := hp
    have hp0 : 0 < p := hpp.pos
    have hpge2 : 2 ≤ p := hpp.two_le
    have hfilterEq : T.filter (fun u => p ∣ u)
          = (Finset.range z).filter (fun u => Squarefree u ∧ u.Coprime W' ∧ p ∣ u) := by
      rw [hTdef, Finset.filter_filter]
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
      (∑ u ∈ T.filter (fun u => ¬ u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ ∑ p ∈ (∏ i, r i).primeFactors,
            ∑ u ∈ T.filter (fun u => p ∣ u), (Real.log u / Real.log R) ^ c /
                    (Nat.totient u : ℝ) := by
    rw [Finset.sum_filter]
    have hswap :
        ∑ p ∈ (∏ i, r i).primeFactors,
            ∑ u ∈ T.filter (fun u => p ∣ u), (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ)
          = ∑ u ∈ T, ∑ p ∈ (∏ i, r i).primeFactors,
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
  have hdropfc :
      (∑ u ∈ T.filter (fun u => ¬ u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ))
        ≤ PAS * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
    calc _ ≤ _ := hcover
      _ ≤ ∑ p ∈ (∏ i, r i).primeFactors, PAS * (1 / ((p : ℝ) - 1)) :=
            Finset.sum_le_sum hmarked_p
      _ = PAS * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
            rw [Finset.mul_sum]
  have hgz_le : ∀ u ∈ T,
      0 ≤ (Real.log u / Real.log R) ^ c * ((Real.log z - Real.log u) / Real.log R) ^ d
            / (Nat.totient u : ℝ)
      ∧ (Real.log u / Real.log R) ^ c * ((Real.log z - Real.log u) / Real.log R) ^ d
            / (Nat.totient u : ℝ) ≤ (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) := by
    intro u hu
    obtain ⟨hφu, hac0, _, hB20, hB21⟩ := hufacts u hu
    refine ⟨div_nonneg (mul_nonneg hac0 (pow_nonneg hB20 _)) hφu.le, ?_⟩
    apply div_le_div_of_nonneg_right _ hφu.le
    calc (Real.log u / Real.log R) ^ c * ((Real.log z - Real.log u) / Real.log R) ^ d
        ≤ (Real.log u / Real.log R) ^ c * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hB20 hB21) hac0
      _ = (Real.log u / Real.log R) ^ c := mul_one _
  have hdrop :
      0 ≤ (∑ u ∈ T, (Real.log u / Real.log R) ^ c
              * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
          - (∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
              (Real.log u / Real.log R) ^ c
                * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
      ∧ (∑ u ∈ T, (Real.log u / Real.log R) ^ c
              * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
          - (∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
              (Real.log u / Real.log R) ^ c
                * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
        ≤ PAS * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not T
      (fun u => u.Coprime (∏ i, r i))
      (fun u => (Real.log u / Real.log R) ^ c
        * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
    have hnc0 : 0 ≤ ∑ u ∈ T.filter (fun u => ¬ u.Coprime (∏ i, r i)),
        (Real.log u / Real.log R) ^ c
          * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ) :=
      Finset.sum_nonneg (fun u hu => (hgz_le u (Finset.mem_of_mem_filter u hu)).1)
    have hncle : (∑ u ∈ T.filter (fun u => ¬ u.Coprime (∏ i, r i)),
        (Real.log u / Real.log R) ^ c
          * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
        ≤ ∑ u ∈ T.filter (fun u => ¬ u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c / (Nat.totient u : ℝ) :=
      Finset.sum_le_sum (fun u hu => (hgz_le u (Finset.mem_of_mem_filter u hu)).2)
    constructor <;> linarith [hsplit, hdropfc]
  -- === (3) the budget moment at the ℕ-cap ===
  have hbudget := hbudgetspec z R hz2 hzR hR
  rw [← hTdef] at hbudget
  -- === (4) the cap slip on the main term ===
  have hslip :
      |(W'.totient : ℝ) / W' * Real.log R * β * (Real.log z / Real.log R) ^ (c + d + 1)
        - (W'.totient : ℝ) / W' * Real.log R * β
            * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + d + 1)|
      ≤ β * ((c + d + 1 : ℕ) : ℝ) * Real.log 2 := by
    set A := Real.log (z : ℝ) / Real.log R with hA
    set B := (Real.log R - Real.log (∏ i, r i)) / Real.log R with hB
    set X := (Nat.totient W' : ℝ) / W' * Real.log R with hX
    have hX0 : 0 ≤ X := by rw [hX]; positivity
    have hXle : X ≤ Real.log R := by
      rw [hX]
      have hφle : (Nat.totient W' : ℝ) / W' ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hpos)]
        exact_mod_cast Nat.totient_le W'
      nlinarith only [hR, hφle]
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    have hA1 : A ≤ 1 := by rw [hA, div_le_one hLpos]; exact hzR'
    have hB0 : 0 ≤ B := by rw [hB]; apply div_nonneg (by linarith) hLpos.le
    have hB1 : B ≤ 1 := by rw [hB, div_le_one hLpos]; linarith
    have hAB : |A - B| ≤ Real.log 2 / Real.log R := by
      have hABeq : A - B = (Real.log (z : ℝ) - (Real.log R - Real.log (∏ i, r i))) / Real.log R
              := by
        rw [hA, hB, div_sub_div_same]
      rw [hABeq, abs_div, abs_of_pos hLpos]
      exact div_le_div_of_nonneg_right hAB0 hLpos.le
    have hXβ : 0 ≤ X * β := mul_nonneg hX0 hβ0
    calc |X * β * A ^ (c + d + 1) - X * β * B ^ (c + d + 1)|
        = (X * β) * |A ^ (c + d + 1) - B ^ (c + d + 1)| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hXβ]
      _ ≤ (X * β) * (((c + d + 1 : ℕ) : ℝ) * |A - B|) :=
          mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le_unit hA0 hA1 hB0 hB1 (c + d + 1)) hXβ
      _ ≤ (X * β) * (((c + d + 1 : ℕ) : ℝ) * (Real.log 2 / Real.log R)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAB (Nat.cast_nonneg _)) hXβ
      _ = (X / Real.log R) * (β * ((c + d + 1 : ℕ) : ℝ) * Real.log 2) := by ring
      _ ≤ 1 * (β * ((c + d + 1 : ℕ) : ℝ) * Real.log 2) := by
          apply mul_le_mul_of_nonneg_right _
            (mul_nonneg (mul_nonneg hβ0 (Nat.cast_nonneg _)) hlog2)
          rw [div_le_one hLpos]; exact hXle
      _ = β * ((c + d + 1 : ℕ) : ℝ) * Real.log 2 := one_mul _
  -- === combine ===
  have t1 := abs_sub_le
    (∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
      (Real.log u / Real.log R) ^ c
        * ((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ d
        / (Nat.totient u : ℝ))
    (∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
      (Real.log u / Real.log R) ^ c
        * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
    ((W'.totient : ℝ) / W' * Real.log R * β
      * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + d + 1))
  have t2 := abs_sub_le
    (∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
      (Real.log u / Real.log R) ^ c
        * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
    (∑ u ∈ T, (Real.log u / Real.log R) ^ c
        * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
    ((W'.totient : ℝ) / W' * Real.log R * β
      * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + d + 1))
  have t3 := abs_sub_le
    (∑ u ∈ T, (Real.log u / Real.log R) ^ c
        * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
    ((W'.totient : ℝ) / W' * Real.log R * β * (Real.log z / Real.log R) ^ (c + d + 1))
    ((W'.totient : ℝ) / W' * Real.log R * β
      * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (c + d + 1))
  have hdropabs :
      |(∑ u ∈ T.filter (fun u => u.Coprime (∏ i, r i)),
          (Real.log u / Real.log R) ^ c
            * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))
        - (∑ u ∈ T, (Real.log u / Real.log R) ^ c
            * ((Real.log z - Real.log u) / Real.log R) ^ d / (Nat.totient u : ℝ))|
      ≤ PAS * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1)) := by
    rw [abs_sub_comm, abs_of_nonneg hdrop.1]; exact hdrop.2
  linarith [hbudget, hslip, hbslip, hdropabs, t1, t2, t3]

/-! ## `eval` expansions and further list plumbing -/

private lemma eval_expand {k : ℕ} (P : BPoly k) (t : Fin k → ℝ) :
    eval P t = (P.map (fun a => (a.2.2 : ℝ) * (∏ i, t i ^ a.1 i) * (1 - ∑ i, t i) ^ a.2.1)).sum :=
  rfl

private lemma eval_contractB {n : ℕ} (m : Fin (n + 1)) (P : BPoly (n + 1)) (t : Fin n → ℝ) :
    eval (contractB m P) t
      = (P.map (fun a => ((a.2.2 * (((a.1 m).factorial * a.2.1.factorial : ℕ) : ℚ)
            / ((a.1 m + a.2.1 + 1).factorial : ℕ) : ℚ) : ℝ)
          * (∏ i, t i ^ a.1 (m.succAbove i)) * (1 - ∑ i, t i) ^ (a.1 m + a.2.1 + 1))).sum := by
  simp only [eval, contractB, List.map_map, Function.comp_def, Fin.removeNth_apply]

private lemma prod_update_split {n : ℕ} (r : Fin (n + 1) → ℕ) (m : Fin (n + 1)) (u : ℕ) (RR : ℝ)
    (a : Fin (n + 1) → ℕ) :
    ∏ i, (Real.log ((Function.update r m u) i) / RR) ^ a i
      = (Real.log u / RR) ^ a m
        * ∏ i : Fin n, (Real.log (r (m.succAbove i)) / RR) ^ a (m.succAbove i) := by
  rw [Fin.prod_univ_succAbove _ m]
  congr 1
  · rw [Function.update_self]
  · exact Finset.prod_congr rfl
      (fun i _ => by rw [Function.update_of_ne (Fin.succAbove_ne m i)])

private lemma sum_log_update {n : ℕ} (r : Fin (n + 1) → ℕ) (m : Fin (n + 1)) (u : ℕ) :
    ∑ j, Real.log ((Function.update r m u j : ℕ) : ℝ)
      = Real.log u + ∑ i : Fin n, Real.log (r (m.succAbove i)) := by
  rw [Fin.sum_univ_succAbove _ m, Function.update_self]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [Function.update_of_ne (Fin.succAbove_ne m i)])

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


/-- B4.2b hypothesis 2: `inner_contract_rel`'s statement, transformed (`F → P`, `yF → yFg`,
`contractAt m F → contractB m P`, `kSieveIndex 5 → kSieveIndex (n+1)`; the error shape
`c + A·PAS·Σ_{p ∣ ∏r} 1/(p−1)` is kept — `inner_contract_b`'s cap slip lands in `c`). -/
def InnerContractRelGen (n : ℕ) (P : BPoly (n + 1)) (m : Fin (n + 1)) : Prop :=
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
      ∀ r ∈ kSieveIndex (n + 1) R W', r m = 1 →
      |(∑ u ∈ Finset.range R,
            yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R)
            * eval (contractB m P)
                (fun i => Real.log (r (m.succAbove i)) / Real.log R)|
      ≤ c + A * Salt.Maynard.phiAtomSum R W'
              * ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p : ℝ) - 1))

/-- The `∫dtₘ`-peel of one sieve coordinate of a budget polynomial, with the PAS-relative
coprimality drop (`inner_contract_rel` at budget power `d`). -/
theorem inner_contract_rel_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1)) :
    InnerContractRelGen n P m := by
  classical
  have _hn := hn
  set A : ℝ := (P.map (fun a => |(a.2.2 : ℝ)|)).sum with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]; apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx; exact abs_nonneg _
  refine ⟨A, hA0, ?_⟩
  intro W' D hW' hpos hUpper _hD _hDW
  have hφpos : 0 < (Nat.totient W' : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hpos
  have hWposR : 0 < (W' : ℝ) := by exact_mod_cast hpos
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set Cabs : ℝ :=
    (P.map (fun a => |(a.2.2 : ℝ)|
      * ((budget_moment W' hW' hpos hUpper (a.1 m) a.2.1).choose * 4 ^ (a.2.1 + a.1 m)
        + (((a.1 m).factorial * a.2.1.factorial : ℝ) / (a.1 m + a.2.1 + 1).factorial)
            * ((a.1 m + a.2.1 + 1 : ℕ) : ℝ) * Real.log 2
        + (a.2.1 : ℝ) * Real.log 2 * (marked_sqf_phi W' hW' hpos 0).choose))).sum with hCabsdef
  have hCabs0 : 0 ≤ Cabs := by
    rw [hCabsdef]; apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx
    have h1 := (budget_moment W' hW' hpos hUpper (a.1 m) a.2.1).choose_spec.1
    have h2 := (marked_sqf_phi W' hW' hpos 0).choose_spec.1
    exact mul_nonneg (abs_nonneg _) (by positivity)
  refine ⟨Cabs, hCabs0, ?_⟩
  intro R hR r hr hrm
  have hLpos : 0 < Real.log R := lt_of_lt_of_le zero_lt_one hR
  have hLne : Real.log R ≠ 0 := ne_of_gt hLpos
  have hsumQ : ∑ i : Fin n, Real.log (r (m.succAbove i)) = Real.log (∏ i, (r i : ℝ)) := by
    have h5 : ∑ j : Fin (n + 1), Real.log (r j)
        = Real.log (r m) + ∑ i : Fin n, Real.log (r (m.succAbove i)) :=
      Fin.sum_univ_succAbove (fun j => Real.log (r j)) m
    have hlogprod : Real.log (∏ i, (r i : ℝ)) = ∑ j : Fin (n + 1), Real.log (r j) := by
      rw [Real.log_prod]
      intro j _
      exact_mod_cast (kSieveIndex_coord_pos hr j).ne'
    rw [hlogprod, h5, hrm]; simp
  -- The budget factor `B = 1 − Σ t'`.
  have hBval : (1 : ℝ) - ∑ i : Fin n, Real.log (r (m.succAbove i)) / Real.log R
      = (Real.log R - Real.log (∏ i, r i)) / Real.log R := by
    rw [← Finset.sum_div, hsumQ, sub_div, div_self hLne]
  have hbud : ∀ u : ℕ, (1 : ℝ) - ∑ j, Real.log ((Function.update r m u j : ℕ) : ℝ) / Real.log R
      = (Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R := by
    intro u
    rw [← Finset.sum_div, sum_log_update, hsumQ, sub_div, sub_div, div_self hLne]
    ring
  -- === Rewrite the target ===
  have hTarget : ((W'.totient : ℝ) / W' * Real.log R)
        * eval (contractB m P) (fun i => Real.log (r (m.succAbove i)) / Real.log R)
      = (P.map (fun a => (a.2.2 : ℝ)
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * (((W'.totient : ℝ) / W' * Real.log R)
              * (((a.1 m).factorial * a.2.1.factorial : ℝ) / (a.1 m + a.2.1 + 1).factorial)
              * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (a.1 m + a.2.1 + 1)))).sum := by
    rw [eval_contractB, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    rw [hBval]
    push_cast
    ring
  -- === Rewrite the full sum ===
  have hFull : (∑ u ∈ Finset.range R, yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ))
      = (P.map (fun a => (a.2.2 : ℝ)
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * (∑ u ∈ (Finset.range R).filter
                (fun u => Function.update r m u ∈ kSieveIndex (n + 1) R W'),
                (Real.log u / Real.log R) ^ a.1 m
                  * ((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ a.2.1
                  / (Nat.totient u : ℝ)))).sum := by
    have e1 : (∑ u ∈ Finset.range R, yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ))
        = ∑ u ∈ (Finset.range R).filter
              (fun u => Function.update r m u ∈ kSieveIndex (n + 1) R W'),
            eval P (fun i => Real.log ((Function.update r m u) i) / Real.log R)
              / (Nat.totient u : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      unfold yFg
      split_ifs with h
      · rfl
      · simp
    rw [e1, Finset.sum_congr rfl (fun u _ => by rw [eval_expand, list_sum_div]),
      sum_finset_list_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    have hre : ∀ u : ℕ,
        (a.2.2 : ℝ) * (∏ i, (Real.log ((Function.update r m u) i) / Real.log R) ^ a.1 i)
            * (1 - ∑ i, Real.log ((Function.update r m u) i) / Real.log R) ^ a.2.1
            / (Nat.totient u : ℝ)
          = ((a.2.2 : ℝ)
              * ∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
            * ((Real.log u / Real.log R) ^ a.1 m
                * ((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ a.2.1
                / (Nat.totient u : ℝ)) := by
      intro u
      rw [prod_update_split r m u (Real.log R) a.1, hbud u]; ring
    rw [Finset.sum_congr rfl (fun u _ => hre u), ← Finset.mul_sum]
  -- === The per-monomial bound ===
  have hpera : ∀ a ∈ P,
      |((a.2.2 : ℝ)
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * (∑ u ∈ (Finset.range R).filter
                (fun u => Function.update r m u ∈ kSieveIndex (n + 1) R W'),
                (Real.log u / Real.log R) ^ a.1 m
                  * ((Real.log R - Real.log (∏ i, r i) - Real.log u) / Real.log R) ^ a.2.1
                  / (Nat.totient u : ℝ)))
        - ((a.2.2 : ℝ)
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * (((W'.totient : ℝ) / W' * Real.log R)
              * (((a.1 m).factorial * a.2.1.factorial : ℝ) / (a.1 m + a.2.1 + 1).factorial)
              * ((Real.log R - Real.log (∏ i, r i)) / Real.log R) ^ (a.1 m + a.2.1 + 1)))|
      ≤ |(a.2.2 : ℝ)| * ((budget_moment W' hW' hpos hUpper (a.1 m) a.2.1).choose * 4 ^ (a.2.1
              + a.1 m)
        + (((a.1 m).factorial * a.2.1.factorial : ℝ) / (a.1 m + a.2.1 + 1).factorial)
            * ((a.1 m + a.2.1 + 1 : ℕ) : ℝ) * Real.log 2
        + (a.2.1 : ℝ) * Real.log 2 * (marked_sqf_phi W' hW' hpos 0).choose
        + Salt.Maynard.phiAtomSum R W'
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
    have hest := inner_sum_estimate_brel W' hW' hpos hUpper hR hr hrm (a.1 m) a.2.1
    rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg hKnn]
    calc |(a.2.2 : ℝ)|
          * (∏ i, (Real.log (r (m.succAbove i)) / Real.log R) ^ a.1 (m.succAbove i))
          * |_| ≤ |(a.2.2 : ℝ)| * 1 * _ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hK1 (abs_nonneg _)) hest (abs_nonneg _)
          exact mul_nonneg (abs_nonneg _) zero_le_one
      _ = _ := by rw [mul_one]
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
      (P.map (fun a => |(a.2.2 : ℝ)|
        * ((budget_moment W' hW' hpos hUpper (a.1 m) a.2.1).choose * 4 ^ (a.2.1 + a.1 m)
          + (((a.1 m).factorial * a.2.1.factorial : ℝ) / (a.1 m + a.2.1 + 1).factorial)
              * ((a.1 m + a.2.1 + 1 : ℕ) : ℝ) * Real.log 2
          + (a.2.1 : ℝ) * Real.log 2 * (marked_sqf_phi W' hW' hpos 0).choose
          + Salt.Maynard.phiAtomSum R W' * S))).sum
        = Cabs + A * (Salt.Maynard.phiAtomSum R W' * S) := by
    rw [hCabsdef, hAdef, ← List.sum_map_mul_right, ← list_sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    ring
  rw [hFull, hTarget, list_sum_map_sub]
  refine le_trans (list_abs_sum_le P _) ?_
  refine le_trans (list_sum_le_sum P _ _ hpera) ?_
  rw [hbndsum]
  apply le_of_eq
  ring



end Salt.MaynardK
