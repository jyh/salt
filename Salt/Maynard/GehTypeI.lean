/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehVaughan

/-!
# The GEH door — the elementary Type-I obligations (design node D-N2b, head branch)

Design freeze: `docs/exploration/s2-b3-design.md`; boundary recon adjudicated
`docs/exploration/pilot.md` (2026-07-17 ~12:50).  This file discharges the
*elementary* `PieceObligationU` obligations of the AP–Vaughan split — the ones
the boundary recon verified need no GEH and no deep (Kloosterman/dispersion)
technology, only elementary counting:

* **`head_obligation`** — the head correction `Ecorr = vErr (cbrt x) (cbrt x)`.
  The engine is the pointwise identity `vErr_eq_vonMangoldt_of_le`: on the head
  `n ≤ cbrt x = U = V` every divisor truncation is vacuous, so `vP3 = 0` and
  `vP1 = vP2`, whence `vErr n = Λ n`.  The head weight is therefore `Λ`
  supported on `[1, cbrt x]`, pointwise `≤ log x`, of total mass `≤ cbrt x · log x`.
  Summing the sequence discrepancy over `q ≤ x^θ` splits at `q = cbrt x`:
  small `q` use the crude mass bound (`≤ x^{2/3} log²`), large `q` use the
  at-most-one-element-per-class bound (`≤ x^θ log`); both are `≪ x/(log x)^A`
  because `x^{1/4000}` beats every polylog (`power_log_absorb`).

## The reusable per-`q` smooth machinery (the D-N2b supplier list)

* `seqDiscrepancy_le_two_mul_sum_abs` (landed in `GehVaughan`): the crude
  `≤ 2 · ℓ¹`-mass bound, used on the *small*-`q` range.
* `seqDiscrepancy_le_two_G_of_lt`: the *large*-`q` bound
  `seqDiscrepancy g y q ≤ 2 G` when the support `Z < q` (each reduced residue
  class holds at most one support point, and the coprime mean is an average of
  those single points).  This is the elementary Type-I saving.
* `power_log_absorb`: `x^{θ'} log x ≤ C x/(log x)^A` for any fixed `θ' < 1`,
  with the constant `C` chosen *outside* the `∀ x` quantifier (III.4).  Proved
  from the global `log t ≤ t^δ/δ` (`log_le_rpow_div`) — polylog beats power with
  an explicit, threshold-free constant.

## III.3″ (the margin arithmetic, recorded)

The head lives entirely at scale `cbrt x = x^{1/3}`; the Type-I *tail* pieces
(short factor `d < x^δ`, `δ = 1/8000`) live at the honest margin
`δ + θ = 1/8000 + 3999/4000 = 7999/8000 < 1`, so their trivial Type-I bound
`x^{7999/8000} · polylog` is `≪ x/(log x)^A`.  Every constant produced here is
existentially bound OUTSIDE `∀ x` (the `∃ C` precedes the `∀ x` in
`PieceObligationU`), per III.4.
-/

open Finset ArithmeticFunction

open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## Polylog beats power (the analytic absorber, constant outside `∀x`) -/

/-- **`log t ≤ t^δ/δ`** for `t, δ > 0`: the threshold-free "polylog beats power"
core.  Follows from `log (t^δ) ≤ t^δ - 1 ≤ t^δ` and `log (t^δ) = δ log t`. -/
theorem log_le_rpow_div {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    Real.log t ≤ t ^ δ / δ := by
  have h1 : Real.log (t ^ δ) ≤ t ^ δ - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht δ)
  rw [Real.log_rpow ht] at h1
  rw [le_div_iff₀ hδ]
  nlinarith [h1, Real.rpow_pos_of_pos ht δ]

/-- **The power-vs-polylog absorber (III.4 constant).**  For every fixed
`θ' < 1` and every `A > 0` there is a constant `C ≥ 0` — chosen once, *before*
`x` — with `x^{θ'} log x ≤ C x/(log x)^A` for all `x ≥ 2`.  Take
`δ = (1-θ')/(2(A+1))`, so `θ' + δ(A+1) = (θ'+1)/2 ≤ 1`; then `log x ≤ x^δ/δ`
raises to `(log x)^{A+1} ≤ x^{δ(A+1)}/δ^{A+1}`, leaving `x^{(θ'+1)/2} ≤ x`. -/
theorem power_log_absorb {θ' A : ℝ} (hθ1 : θ' < 1) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      (x : ℝ) ^ θ' * Real.log x ≤ C * (x : ℝ) / Real.log x ^ A := by
  have hApos : (0 : ℝ) < A + 1 := by linarith
  have hA1 : (A : ℝ) + 1 ≠ 0 := by positivity
  set δ : ℝ := (1 - θ') / (2 * (A + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; apply div_pos (by linarith) (by linarith)
  refine ⟨(δ⁻¹) ^ (1 + A), Real.rpow_nonneg (by positivity) _, fun x hx => ?_⟩
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hL : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hLnn : (0 : ℝ) ≤ Real.log x := le_of_lt hL
  have hLA : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hL A
  have hxδnn : (0 : ℝ) ≤ (x : ℝ) ^ δ := Real.rpow_nonneg (le_of_lt hxpos) δ
  rw [le_div_iff₀ hLA]
  have hLcomb : Real.log x * Real.log x ^ A = Real.log x ^ (1 + A) := by
    rw [Real.rpow_add hL, Real.rpow_one]
  have hLbound : Real.log x ^ (1 + A) ≤ ((x : ℝ) ^ δ * δ⁻¹) ^ (1 + A) := by
    refine Real.rpow_le_rpow hLnn ?_ (by positivity)
    rw [← div_eq_mul_inv]; exact log_le_rpow_div hxpos hδpos
  have hExp : θ' + δ * (1 + A) ≤ 1 := by
    have hval : δ * (1 + A) = (1 - θ') / 2 := by rw [hδdef]; field_simp; ring
    rw [hval]; linarith
  calc (x : ℝ) ^ θ' * Real.log x * Real.log x ^ A
      = (x : ℝ) ^ θ' * Real.log x ^ (1 + A) := by rw [mul_assoc, hLcomb]
    _ ≤ (x : ℝ) ^ θ' * ((x : ℝ) ^ δ * δ⁻¹) ^ (1 + A) :=
        mul_le_mul_of_nonneg_left hLbound (Real.rpow_nonneg (le_of_lt hxpos) θ')
    _ = (x : ℝ) ^ θ' * ((x : ℝ) ^ (δ * (1 + A)) * (δ⁻¹) ^ (1 + A)) := by
        rw [Real.mul_rpow hxδnn (by positivity), ← Real.rpow_mul (le_of_lt hxpos)]
    _ = (x : ℝ) ^ (θ' + δ * (1 + A)) * (δ⁻¹) ^ (1 + A) := by
        rw [← mul_assoc, ← Real.rpow_add hxpos]
    _ ≤ (x : ℝ) ^ (1 : ℝ) * (δ⁻¹) ^ (1 + A) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        exact Real.rpow_le_rpow_of_exponent_le hx1 hExp
    _ = (δ⁻¹) ^ (1 + A) * (x : ℝ) := by rw [Real.rpow_one]; ring

/-! ## The head identity `vErr = Λ` on `n ≤ V` -/

/-- **The head correction is the von Mangoldt weight on the head.**  For
`V ≤ U` and `n ≤ V`, every divisor `d ∣ n` has `d ≤ n ≤ V ≤ U`, so the outer
`d ≤ U` truncation is vacuous; likewise every `c ∣ (n/d)` has `c ≤ V`.  Hence
`vP3 U V n = 0` (its `d > U` sum is empty) and `vP2 U V n = vP1 U n` (the inner
`∑_{c ∣ n/d} Λ c = log (n/d)` collapses `vP2` onto `vP1`).  Therefore
`vErr U V n = Λ n − vP1 + vP1 − 0 = Λ n`. -/
theorem vErr_eq_vonMangoldt_of_le {U V n : ℕ} (hUV : V ≤ U) (hn : n ≤ V) :
    vErr U V n = ArithmeticFunction.vonMangoldt n := by
  have hvP3 : vP3 U V n = 0 := by
    have hempty : n.divisors.filter (fun d => U < d) = ∅ := by
      apply Finset.filter_false_of_mem
      intro d hd
      have hd' := Nat.mem_divisors.mp hd
      have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hd'.2) hd'.1
      omega
    unfold vP3
    rw [hempty, Finset.sum_empty]
  have hvP12 : vP2 U V n = vP1 U n := by
    unfold vP1 vP2
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.2) hd.1.1
    have hfilter : (n / d).divisors.filter (· ≤ V) = (n / d).divisors := by
      apply Finset.filter_true_of_mem
      intro c hc
      have hcnd : c ≤ n / d :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hc).2) (Nat.dvd_of_mem_divisors hc)
      have hndn : n / d ≤ n := Nat.div_le_self n d
      omega
    rw [hfilter, ← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
  unfold vErr
  rw [hvP3, hvP12]; ring

/-! ## The elementary per-`q` smooth machinery -/

/-- **At-most-one-element-per-class.**  For a weight `g` supported on `[1, Z]`
with `|g| ≤ G`, if the modulus `q` exceeds the support `Z`, then each residue
class holds at most one support point, so the residue-class sum is `≤ G`
(uniformly in the residue `a` and the cutoff `y`). -/
theorem abs_residueSum_le_G_of_lt
    {g : ℕ → ℝ} {Z : ℕ} {G : ℝ} (hG : 0 ≤ G)
    (hsupp : ∀ n, Z < n → g n = 0) (hbd : ∀ n, |g n| ≤ G)
    (y q a : ℕ) (hq : Z < q) :
    |∑ n ∈ Finset.Icc 1 y, if n % q = a then g n else 0| ≤ G := by
  have hrestrict : (∑ n ∈ Finset.Icc 1 y, if n % q = a then g n else 0)
      = ∑ n ∈ (Finset.Icc 1 y).filter (· ≤ Z), if n % q = a then g n else 0 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnf
    have hZn : Z < n := by
      by_contra h; exact hnf (Finset.mem_filter.mpr ⟨hn, by omega⟩)
    simp [hsupp n hZn]
  rw [hrestrict]
  have hcongr : ∀ n ∈ (Finset.Icc 1 y).filter (· ≤ Z),
      (if n % q = a then g n else 0) = (if n = a then g n else 0) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have : n % q = n := Nat.mod_eq_of_lt (by omega)
    rw [this]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
  split_ifs with h
  · exact hbd a
  · rw [abs_zero]; exact hG

/-- **The coprime mean is a sum over reduced residues.**  For `q > 0`, the
coprime-restricted sum equals the sum of the residue-class sums over reduced
residues (each `n` lands in the unique class `n % q`, coprime to `q` iff `n`
is). -/
theorem coprimeMeanSum_eq_sum_residues (g : ℕ → ℝ) (y q : ℕ) (hq : 0 < q) :
    (∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then g n else 0)
      = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ∑ n ∈ Finset.Icc 1 y, if n % q = a then g n else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_ite_eq]
  have hgcd : Nat.gcd (n % q) q = Nat.gcd n q := by
    rw [← Nat.gcd_rec q n]; exact Nat.gcd_comm q n
  refine if_congr ?_ rfl rfl
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨Nat.mod_lt n hq, by change Nat.gcd (n % q) q = 1; rw [hgcd]; exact h⟩
  · rintro ⟨_, h2⟩
    change Nat.gcd n q = 1
    rw [← hgcd]; exact h2

/-- **The coprime mean is `≤ φ(q) G`.**  Summing `abs_residueSum_le_G_of_lt`
over the `φ(q)` reduced residues. -/
theorem abs_coprimeMeanSum_le_totient_mul_G
    {g : ℕ → ℝ} {Z : ℕ} {G : ℝ} (hG : 0 ≤ G)
    (hsupp : ∀ n, Z < n → g n = 0) (hbd : ∀ n, |g n| ≤ G)
    (y q : ℕ) (hq : Z < q) :
    |∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then g n else 0| ≤ (q.totient : ℝ) * G := by
  have hqpos : 0 < q := by omega
  have hcard : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    apply Finset.filter_congr
    intro a _
    exact Nat.coprime_comm
  rw [coprimeMeanSum_eq_sum_residues g y q hqpos]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          |∑ n ∈ Finset.Icc 1 y, if n % q = a then g n else 0|
      ≤ ∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), G :=
        Finset.sum_le_sum (fun a _ => abs_residueSum_le_G_of_lt hG hsupp hbd y q a hq)
    _ = ((Finset.range q).filter (fun a => Nat.Coprime a q)).card • G := Finset.sum_const _
    _ = (q.totient : ℝ) * G := by rw [nsmul_eq_mul, hcard]

/-- **The large-`q` elementary Type-I bound.**  For `g` supported on `[1, Z]`
with `|g| ≤ G` and `Z < q`, the sequence discrepancy is `≤ 2 G`: the residue
sums are single support points (`≤ G`) and the coprime mean is their average
(`≤ G`). -/
theorem seqDiscrepancy_le_two_G_of_lt
    {g : ℕ → ℝ} {Z : ℕ} {G : ℝ} (hG : 0 ≤ G)
    (hsupp : ∀ n, Z < n → g n = 0) (hbd : ∀ n, |g n| ≤ G)
    (y q : ℕ) (hq : Z < q) :
    seqDiscrepancy g y q ≤ 2 * G := by
  have hq0 : q ≠ 0 := by omega
  have hqpos : 0 < q := by omega
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  rw [seqDiscrepancy_eq g y q hq0]
  apply Finset.sup'_le
  intro a _
  set R := ∑ n ∈ Finset.Icc 1 y, if n % q = a then g n else 0 with hRdef
  set Mn := ∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then g n else 0 with hMndef
  have hRa : |R| ≤ G := abs_residueSum_le_G_of_lt hG hsupp hbd y q a hq
  have hMean : |Mn| ≤ (q.totient : ℝ) * G :=
    abs_coprimeMeanSum_le_totient_mul_G hG hsupp hbd y q hq
  have hMeanDiv : |Mn / (q.totient : ℝ)| ≤ G := by
    rw [abs_div, abs_of_pos hφpos, div_le_iff₀ hφpos]
    calc |Mn| ≤ (q.totient : ℝ) * G := hMean
      _ = G * (q.totient : ℝ) := by ring
  calc |R - Mn / (q.totient : ℝ)|
      = |R + -(Mn / (q.totient : ℝ))| := by rw [sub_eq_add_neg]
    _ ≤ |R| + |Mn / (q.totient : ℝ)| := by
        refine (abs_add_le _ _).trans_eq ?_; rw [abs_neg]
    _ ≤ G + G := add_le_add hRa hMeanDiv
    _ = 2 * G := by ring

/-- **The head-mass bound.**  For `g` supported on `[1, Z]` with `|g| ≤ G`, the
total `ℓ¹` mass on any cutoff `y` is `≤ Z G`. -/
theorem sum_abs_le_Z_mul_G
    {g : ℕ → ℝ} {Z : ℕ} {G : ℝ} (hG : 0 ≤ G)
    (hsupp : ∀ n, Z < n → g n = 0) (hbd : ∀ n, |g n| ≤ G) (y : ℕ) :
    ∑ n ∈ Finset.Icc 1 y, |g n| ≤ (Z : ℝ) * G := by
  have hcardle : ((Finset.Icc 1 y).filter (· ≤ Z)).card ≤ Z := by
    calc ((Finset.Icc 1 y).filter (· ≤ Z)).card ≤ (Finset.Icc 1 Z).card := by
          apply Finset.card_le_card
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          exact Finset.mem_Icc.mpr ⟨hn.1.1, hn.2⟩
      _ = Z := by rw [Nat.card_Icc]; omega
  calc ∑ n ∈ Finset.Icc 1 y, |g n|
      ≤ ∑ n ∈ Finset.Icc 1 y, (if n ≤ Z then G else 0) := by
        apply Finset.sum_le_sum
        intro n _
        by_cases h : n ≤ Z
        · simp only [h, if_true]; exact hbd n
        · simp only [h, if_false]; rw [hsupp n (by omega), abs_zero]
    _ = ∑ _n ∈ (Finset.Icc 1 y).filter (· ≤ Z), G := by rw [Finset.sum_filter]
    _ = ((Finset.Icc 1 y).filter (· ≤ Z)).card • G := Finset.sum_const _
    _ ≤ (Z : ℝ) * G := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardle) hG

/-! ## The head obligation (`hHead`), discharged elementarily -/

/-- **`hHead` discharged (D-N2b, elementary).**  The head correction
`vErr (cbrt x) (cbrt x)` satisfies the `y`-uniform piece obligation at
`θ = 3999/4000`.  Route: `vErr = Λ` on `[1, cbrt x]` (`vErr_eq_vonMangoldt_of_le`)
and `0` beyond (`vErr_eq_zero`), so it is a weight of support `cbrt x ≤ x^{1/3}`,
pointwise `≤ log x`.  Splitting `∑_{q ≤ x^θ}` at `q = cbrt x`: small `q` via the
crude mass bound (`≤ 2 · cbrt x · log x` each, `cbrt x` of them → `x^{2/3} log`),
large `q` via `seqDiscrepancy_le_two_G_of_lt` (`≤ 2 log x` each, `≤ x^θ` of them
→ `x^θ log`).  Both `≪ x/(log x)^A` by `power_log_absorb` (`B = 0`, `C = 4C₀`). -/
theorem head_obligation :
    PieceObligationU (3999 / 4000) (fun x n => vErr (cbrt x) (cbrt x) n) := by
  intro A hA
  obtain ⟨Cabs, hCabs0, hCabs⟩ := power_log_absorb (θ' := (3999 / 4000 : ℝ)) (by norm_num) hA
  refine ⟨0, 4 * Cabs, le_refl 0, fun x y hx hyx => ?_⟩
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hlog0 : (0 : ℝ) ≤ Real.log x := le_of_lt hlogpos
  -- cbrt facts
  have hcbrtle : (cbrt x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    unfold cbrt; exact Nat.floor_le (Real.rpow_nonneg (le_of_lt hxpos) _)
  have hcbrtlex : (cbrt x : ℝ) ≤ (x : ℝ) := by
    refine le_trans hcbrtle ?_
    calc (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _
  have hone13 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := (Real.one_rpow _).symm
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by norm_num) hx1 (by norm_num)
  have hcbrt1 : 1 ≤ cbrt x := by unfold cbrt; exact Nat.le_floor (by exact_mod_cast hone13)
  -- support and pointwise bound
  have hsupp : ∀ n, cbrt x < n → vErr (cbrt x) (cbrt x) n = 0 :=
    fun n hn => vErr_eq_zero hcbrt1 hcbrt1 hn
  have hbd : ∀ n, |vErr (cbrt x) (cbrt x) n| ≤ Real.log x := by
    intro n
    by_cases hn : cbrt x < n
    · rw [hsupp n hn, abs_zero]; exact hlog0
    · rw [vErr_eq_vonMangoldt_of_le (le_refl _) (by omega), abs_of_nonneg vonMangoldt_nonneg]
      refine le_trans vonMangoldt_le_log ?_
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; rw [Nat.cast_zero, Real.log_zero]; exact hlog0
      · exact Real.log_le_log (by exact_mod_cast h0)
          (le_trans (by exact_mod_cast (show n ≤ cbrt x by omega)) hcbrtlex)
  -- scale bounds
  simp only [Real.rpow_zero, div_one]
  set Q := ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ with hQdef
  have hQx : (Q : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (le_of_lt hxpos) _)
  have hcc : (cbrt x : ℝ) * (cbrt x : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := by
    have h1 : (cbrt x : ℝ) * (cbrt x : ℝ)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) :=
      mul_le_mul hcbrtle hcbrtle (Nat.cast_nonneg _) (Real.rpow_nonneg (le_of_lt hxpos) _)
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3)
        = (x : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_add hxpos]; congr 1; norm_num
    have h3 : (x : ℝ) ^ ((2 : ℝ) / 3) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    calc (cbrt x : ℝ) * (cbrt x : ℝ)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) := h1
      _ = (x : ℝ) ^ ((2 : ℝ) / 3) := h2
      _ ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := h3
  -- small-q sum
  have hsmall : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q ≤ cbrt x),
      seqDiscrepancy (fun n => vErr (cbrt x) (cbrt x) n) y q
      ≤ (cbrt x : ℝ) * (2 * ((cbrt x : ℝ) * Real.log x)) := by
    calc ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q ≤ cbrt x),
            seqDiscrepancy (fun n => vErr (cbrt x) (cbrt x) n) y q
        ≤ ∑ _q ∈ (Finset.Icc 1 Q).filter (fun q => q ≤ cbrt x),
            (2 * ((cbrt x : ℝ) * Real.log x)) := by
          apply Finset.sum_le_sum
          intro q _
          calc seqDiscrepancy (fun n => vErr (cbrt x) (cbrt x) n) y q
              ≤ 2 * ∑ n ∈ Finset.Icc 1 y, |vErr (cbrt x) (cbrt x) n| :=
                seqDiscrepancy_le_two_mul_sum_abs _ y q
            _ ≤ 2 * ((cbrt x : ℝ) * Real.log x) :=
                mul_le_mul_of_nonneg_left (sum_abs_le_Z_mul_G hlog0 hsupp hbd y) (by norm_num)
      _ = ((Finset.Icc 1 Q).filter (fun q => q ≤ cbrt x)).card
            • (2 * ((cbrt x : ℝ) * Real.log x)) := Finset.sum_const _
      _ ≤ (cbrt x : ℝ) * (2 * ((cbrt x : ℝ) * Real.log x)) := by
          rw [nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hle : ((Finset.Icc 1 Q).filter (fun q => q ≤ cbrt x)).card ≤ cbrt x := by
            calc ((Finset.Icc 1 Q).filter (fun q => q ≤ cbrt x)).card
                ≤ (Finset.Icc 1 (cbrt x)).card := by
                  apply Finset.card_le_card
                  intro q hq
                  rw [Finset.mem_filter, Finset.mem_Icc] at hq
                  exact Finset.mem_Icc.mpr ⟨hq.1.1, hq.2⟩
              _ = cbrt x := by rw [Nat.card_Icc]; omega
          exact_mod_cast hle
  -- large-q sum
  have hlarge : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => ¬ q ≤ cbrt x),
      seqDiscrepancy (fun n => vErr (cbrt x) (cbrt x) n) y q
      ≤ (Q : ℝ) * (2 * Real.log x) := by
    calc ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => ¬ q ≤ cbrt x),
            seqDiscrepancy (fun n => vErr (cbrt x) (cbrt x) n) y q
        ≤ ∑ _q ∈ (Finset.Icc 1 Q).filter (fun q => ¬ q ≤ cbrt x), (2 * Real.log x) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_filter] at hq
          obtain ⟨-, hq2⟩ := hq
          exact seqDiscrepancy_le_two_G_of_lt hlog0 hsupp hbd y q (by omega)
      _ = ((Finset.Icc 1 Q).filter (fun q => ¬ q ≤ cbrt x)).card • (2 * Real.log x) :=
          Finset.sum_const _
      _ ≤ (Q : ℝ) * (2 * Real.log x) := by
          rw [nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hle : ((Finset.Icc 1 Q).filter (fun q => ¬ q ≤ cbrt x)).card ≤ Q := by
            calc ((Finset.Icc 1 Q).filter (fun q => ¬ q ≤ cbrt x)).card
                ≤ (Finset.Icc 1 Q).card := Finset.card_filter_le _ _
              _ = Q := by rw [Nat.card_Icc]; omega
          exact_mod_cast hle
  -- assemble
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 Q) (fun q => q ≤ cbrt x)]
  calc (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q ≤ cbrt x),
            seqDiscrepancy (fun n => vErr (cbrt x) (cbrt x) n) y q)
        + (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => ¬ q ≤ cbrt x),
            seqDiscrepancy (fun n => vErr (cbrt x) (cbrt x) n) y q)
      ≤ (cbrt x : ℝ) * (2 * ((cbrt x : ℝ) * Real.log x)) + (Q : ℝ) * (2 * Real.log x) :=
        add_le_add hsmall hlarge
    _ ≤ 4 * ((x : ℝ) ^ (3999 / 4000 : ℝ) * Real.log x) := by
        nlinarith [mul_le_mul_of_nonneg_right hcc hlog0,
          mul_le_mul_of_nonneg_right hQx hlog0, hlog0, hcc, hQx]
    _ ≤ 4 * (Cabs * (x : ℝ) / Real.log x ^ A) :=
        mul_le_mul_of_nonneg_left (hCabs x hx) (by norm_num)
    _ = 4 * Cabs * (x : ℝ) / Real.log x ^ A := by ring

/-! ## The Type-I tail pieces (short factor `d < x^δ`, `δ = 1/8000`)

The mid-block node subtracts these tails from the full Type-I pieces and routes
the remaining mid-range blocks through `GEH_min`.  The tail pieces are the
existing `vP1`/`vP2` at the *smaller* truncation `D = ⌊x^{1/8000}⌋` (short
factors only); the split is a partition of the divisor range `[1, cbrt x]` at
`d = D` (`vP1_eq_tail_add_mid`).  The honest tail *bound*
`∑_{q ≤ x^θ} seqDiscrepancy (vP1tail, y, q) ≪ x^{δ+θ} · polylog = x^{7999/8000}
· polylog ≪ x/(log x)^A` is NOT discharged here — see the executor report:
being long-supported (the truncation is on `d`, not `n`), it needs the smooth
Type-I AP equidistribution (Abel summation over `log (n/d)` reducing to the
interval residue count `#{m ≤ M : m ≡ b (q')} = M/q' + O(1)`), a C-tier build. -/

/-- Short-factor truncation scale `D = ⌊x^{1/8000}⌋` (`δ = 1/8000`). -/
noncomputable def dtrunc (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 8000)⌋₊

/-- **Type-I₁ tail piece**: `vP1` truncated to short factors `d ≤ x^{1/8000}`. -/
noncomputable def vP1tail (x n : ℕ) : ℝ := vP1 (dtrunc x) n

/-- **Type-I₂ tail piece**: `vP2` with the outer factor truncated to
`d ≤ x^{1/8000}` (the inner smooth factor kept at `c ≤ cbrt x`). -/
noncomputable def vP2tail (x n : ℕ) : ℝ := vP2 (dtrunc x) (cbrt x) n

/-- **Type-I₁ mid piece**: the complementary mid-range factors
`x^{1/8000} < d ≤ cbrt x` — the block routed through `GEH_min`. -/
noncomputable def vP1mid (x n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => dtrunc x < d ∧ d ≤ cbrt x),
    (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ)

/-- The short truncation is below the cube-root truncation (`x^{1/8000} ≤
x^{1/3}`). -/
theorem dtrunc_le_cbrt {x : ℕ} (hx : 1 ≤ x) : dtrunc x ≤ cbrt x := by
  unfold dtrunc cbrt
  apply Nat.floor_le_floor
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by norm_num)

/-- **The tail/mid split (the mid-block subtraction interface).**  The full
Type-I₁ piece at truncation `cbrt x` is its short-factor tail plus its
mid-range block: `vP1 (cbrt x) n = vP1tail x n + vP1mid x n`.  The mid-block
node bounds `vP1mid = vP1 (cbrt x) − vP1tail` through `GEH_min`. -/
theorem vP1_eq_tail_add_mid {x : ℕ} (hx : 1 ≤ x) (n : ℕ) :
    vP1 (cbrt x) n = vP1tail x n + vP1mid x n := by
  have hDle : dtrunc x ≤ cbrt x := dtrunc_le_cbrt hx
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (n.divisors.filter (· ≤ cbrt x)) (fun d => d ≤ dtrunc x)
    (fun d => (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ))
  have htail : (n.divisors.filter (· ≤ cbrt x)).filter (fun d => d ≤ dtrunc x)
      = n.divisors.filter (· ≤ dtrunc x) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro d _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨le_trans h hDle, h⟩
  have hmid : (n.divisors.filter (· ≤ cbrt x)).filter (fun d => ¬ d ≤ dtrunc x)
      = n.divisors.filter (fun d => dtrunc x < d ∧ d ≤ cbrt x) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro d _
    constructor
    · exact fun h => ⟨by omega, h.1⟩
    · exact fun h => ⟨h.2, by omega⟩
  rw [htail, hmid] at hsplit
  unfold vP1 vP1tail vP1mid vP1
  rw [← hsplit]
