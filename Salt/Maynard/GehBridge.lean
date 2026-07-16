/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehPiSeam
import Salt.Maynard.GehVaughan
import Salt.BV.AbelCore

/-!
# The GEH door's Λ→π Abel bridge (design node D-N2c, the deferred `hbridge`)

`GehPiSeam.lean` reduced `HasLevel θ` to the prime-indicator level `PiLevel θ`
(steps 2+3, complete), leaving the step-1 Abel transfer as the named `hbridge`
hypothesis of `hasLevel_of_lambdaDiscrepancy`.  `GehVaughan.lean` then supplied
the missing y-uniform strengthening `LambdaLevelU θ` (the summed von Mangoldt
sequence discrepancy at *every* prefix `y ≤ x`, over the fixed x-scaled modulus
range).  This file discharges the bridge from that supply:

`piLevel_of_lambdaLevelU : LambdaLevelU θ → PiLevel θ`.

## The transform

For each modulus `q` and reduced residue `a`, the prime-indicator discrepancy is
an Abel transform of the von Mangoldt discrepancies over prefixes, plus a
prime-power correction.  Concretely `1_prime = Λ/log − ppTerm` (`ppTerm` from
`Salt/BV/AbelCore.lean`), and summation by parts against the weight `1/log`
converts the residue-class prime count into `(1/log x)·(residue Λ) + ∑_i w_i·
(prefix residue Λ)`, where `w_i = 1/log i − 1/log(i+1) ≥ 0` telescopes to
`1/log 2 − 1/log x`.  Differencing the residue and coprime-mean forms (the Abel
identity is linear in the class selector) gives, per `q`,

`seqDiscrepancy 1_prime x q ≤ (1/log x)·seqDiscrepancy Λ x q`
`  + ∑_{1<i≤x-1} w_i·seqDiscrepancy Λ i q + seqDiscrepancy ppTerm x q`.

The first two groups are `LambdaLevelU`-controlled at *every* prefix `i ≤ x` with
the SAME `B, C`; the telescoping weight contributes only the constant
`1/log 2 − 1/log x`.  The prime-power correction `∑_q seqDiscrepancy ppTerm x q`
is the pp-in-AP sum (`√x·log² + x^θ·log ≪ x/log^A`), carried as the named
hypothesis `PpLevel θ` (its per-`q` count needs root-counting mod `q`; see
`docs/blueprints/flags.md`, the D-N2c-bridge entry).
-/

open Finset ArithmeticFunction

/-- **The Abel identity for the prime indicator, weighted by an arbitrary class
selector `c`.**  Summation by parts against `1/log` on `[1,x]`: the `c`-weighted
prime count equals `(1/log x)` times the `c`-weighted von Mangoldt sum, plus the
`w_i`-weighted prefix sums, minus the `c`-weighted prime-power correction.  The
identity is linear in `c`, so specialising `c` to the residue-class indicator and
to the coprime indicator (then differencing) yields the per-`q` discrepancy
bound.  Mirrors `Salt.BV.primesCount_abel`, but kept selector-generic. -/
theorem abel_prime_of_weight (c : ℕ → ℝ) {x : ℕ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 1 x, c n * (if n.Prime then (1 : ℝ) else 0))
      = (Real.log x)⁻¹ * (∑ n ∈ Finset.Icc 1 x, c n * vonMangoldt n)
        + ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * (∑ n ∈ Finset.Icc 1 i, c n * vonMangoldt n)
        - ∑ n ∈ Finset.Icc 1 x, c n * Salt.BV.ppTerm n := by
  have hpp1 : Salt.BV.ppTerm 1 = 0 := by
    unfold Salt.BV.ppTerm; simp [ArithmeticFunction.vonMangoldt_apply_one, Nat.not_prime_one]
  set f : ℕ → ℝ := fun n => (Real.log n)⁻¹ with hf
  set g : ℕ → ℝ := fun n => c n * vonMangoldt n with hg
  have hbp := Finset.sum_Ioc_by_parts f g (show 1 < x from hx)
  simp only [smul_eq_mul] at hbp
  -- partial sums of `g` over `range (k+1)` collapse to `Icc 1 k`
  have hG : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), g i
      = ∑ n ∈ Finset.Icc 1 k, c n * vonMangoldt n := by
    intro k
    induction k with
    | zero => rw [Finset.sum_range_one, hg]; simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
  -- bridge `Icc 1 · = Ioc 1 ·` for weights vanishing at `n = 1`
  have hIcc : ∀ h : ℕ → ℝ, h 1 = 0 →
      ∑ n ∈ Finset.Icc 1 x, h n = ∑ n ∈ Finset.Ioc 1 x, h n := by
    intro h h1
    have hins : Finset.Icc 1 x = insert 1 (Finset.Ioc 1 x) := by
      ext n; rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioc]; omega
    have hnotmem : 1 ∉ Finset.Ioc 1 x := by rw [Finset.mem_Ioc]; omega
    rw [hins, Finset.sum_insert hnotmem, h1, zero_add]
  -- LHS of by-parts: split `(1/log)·c·Λ = c·ppTerm + c·1_prime` on `Ioc 1 x`
  have hLHS : ∑ i ∈ Finset.Ioc 1 x, f i * g i
      = (∑ n ∈ Finset.Icc 1 x, c n * Salt.BV.ppTerm n)
        + ∑ n ∈ Finset.Icc 1 x, c n * (if n.Prime then (1 : ℝ) else 0) := by
    rw [hIcc (fun n => c n * Salt.BV.ppTerm n) (by simp [hpp1]),
      hIcc (fun n => c n * (if n.Prime then (1 : ℝ) else 0)) (by simp [Nat.not_prime_one]),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hf, hg]
    have hpp : (Real.log i)⁻¹ * vonMangoldt i
        = Salt.BV.ppTerm i + (if i.Prime then (1 : ℝ) else 0) := by
      unfold Salt.BV.ppTerm; ring
    calc (Real.log i)⁻¹ * (c i * vonMangoldt i)
        = c i * ((Real.log i)⁻¹ * vonMangoldt i) := by ring
      _ = c i * (Salt.BV.ppTerm i + (if i.Prime then (1 : ℝ) else 0)) := by rw [hpp]
      _ = c i * Salt.BV.ppTerm i + c i * (if i.Prime then (1 : ℝ) else 0) := by ring
  -- rewrite the boundary and inner partial sums, then reorient
  have hG2 : ∑ i ∈ Finset.range (1 + 1), g i = 0 := by
    rw [hG 1]; simp [ArithmeticFunction.vonMangoldt_apply_one]
  rw [hLHS, hG x, hG2, mul_zero, sub_zero] at hbp
  have hinner : ∑ i ∈ Finset.Ioc 1 (x - 1),
        (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)
      = ∑ i ∈ Finset.Ioc 1 (x - 1),
          ((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ - (Real.log i)⁻¹)
            * (∑ n ∈ Finset.Icc 1 i, c n * vonMangoldt n) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hG i, hf]
  rw [hinner] at hbp
  -- `hbp : c·pp + c·1_prime = (1/log x)·Λc(x) - ∑ ((1/log(i+1))−(1/log i))·Λc(i)`
  have hneg : ∑ i ∈ Finset.Ioc 1 (x - 1),
        ((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ - (Real.log i)⁻¹)
          * (∑ n ∈ Finset.Icc 1 i, c n * vonMangoldt n)
      = - ∑ i ∈ Finset.Ioc 1 (x - 1),
          ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
            * (∑ n ∈ Finset.Icc 1 i, c n * vonMangoldt n) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hneg] at hbp
  linarith [hbp]

/-- **The per-`q` Abel bound.**  Differencing the residue-class and coprime-mean
Abel identities (`abel_prime_of_weight` applied to the linear selector
`c n = 1_{n≡a} − 1_{coprime}/φq`), the prime-indicator sequence discrepancy is
controlled by the `1/log`-weighted von Mangoldt discrepancies over prefixes plus
the prime-power correction.  The `LambdaLevelU`-controlled quantities are exactly
`seqDiscrepancy Λ · q` at every prefix `i ≤ x`; the last term is the pp-in-AP
correction. -/
theorem seqDiscrepancy_prime_le_abel {x q : ℕ} (hx : 2 ≤ x) (hq : q ≠ 0) :
    seqDiscrepancy (fun n => if n.Prime then (1 : ℝ) else 0) x q
      ≤ (Real.log x)⁻¹ * seqDiscrepancy (fun n => vonMangoldt n) x q
        + (∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * seqDiscrepancy (fun n => vonMangoldt n) i q)
        + seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q := by
  have hLxpos : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  rw [seqDiscrepancy_eq _ x q hq]
  refine Finset.sup'_le _ _ (fun a ha => ?_)
  set c : ℕ → ℝ := fun n => (if n % q = a then (1 : ℝ) else 0)
    - (if Nat.Coprime n q then (1 : ℝ) else 0) / (q.totient : ℝ) with hc
  have hexpand : ∀ (w : ℕ → ℝ) (y : ℕ),
      (∑ n ∈ Finset.Icc 1 y, c n * w n)
        = (∑ n ∈ Finset.Icc 1 y, if n % q = a then w n else 0)
          - (∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then w n else 0) / (q.totient : ℝ) := by
    intro w y
    have hterm : ∀ n, c n * w n
        = (if n % q = a then w n else 0)
          - (if Nat.Coprime n q then w n else 0) / (q.totient : ℝ) := by
      intro n; simp only [hc]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_sub_distrib, ← Finset.sum_div]
  have hbound : ∀ (w : ℕ → ℝ) (y : ℕ),
      |∑ n ∈ Finset.Icc 1 y, c n * w n| ≤ seqDiscrepancy w y q := by
    intro w y
    rw [hexpand w y]
    exact seqDiscrepancy_apply_le w y q a hq ha
  have hw : ∀ i ∈ Finset.Ioc 1 (x - 1),
      0 ≤ (Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    have h1 : 0 < Real.log i := Real.log_pos (by exact_mod_cast hi.1)
    have hmono : Real.log i ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
        (by exact_mod_cast (by omega : i ≤ i + 1))
    have hinv : (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.log i)⁻¹ := by gcongr
    linarith
  have habel := abel_prime_of_weight c hx
  have hkey := (hexpand (fun n => if n.Prime then (1 : ℝ) else 0) x).symm.trans habel
  rw [hkey]
  set A := (Real.log x)⁻¹ * (∑ n ∈ Finset.Icc 1 x, c n * vonMangoldt n) with hA_def
  set Bsum := ∑ i ∈ Finset.Ioc 1 (x - 1),
      ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
        * (∑ n ∈ Finset.Icc 1 i, c n * vonMangoldt n) with hBsum_def
  set Cpp := ∑ n ∈ Finset.Icc 1 x, c n * Salt.BV.ppTerm n with hCpp_def
  have hAle : |A| ≤ (Real.log x)⁻¹ * seqDiscrepancy (fun n => vonMangoldt n) x q := by
    rw [hA_def, abs_mul, abs_of_nonneg (inv_nonneg.mpr hLxpos.le)]
    exact mul_le_mul_of_nonneg_left (hbound (fun n => vonMangoldt n) x) (inv_nonneg.mpr hLxpos.le)
  have hBle : |Bsum| ≤ ∑ i ∈ Finset.Ioc 1 (x - 1),
      ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
        * seqDiscrepancy (fun n => vonMangoldt n) i q := by
    rw [hBsum_def]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [abs_mul, abs_of_nonneg (hw i hi)]
    exact mul_le_mul_of_nonneg_left (hbound (fun n => vonMangoldt n) i) (hw i hi)
  have hCle : |Cpp| ≤ seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q := by
    rw [hCpp_def]; exact hbound (fun n => Salt.BV.ppTerm n) x
  have htri : |A + Bsum - Cpp| ≤ |A| + |Bsum| + |Cpp| := by
    have e1 : |A + Bsum - Cpp| ≤ |A + Bsum| + |Cpp| := by
      rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    linarith [abs_add_le A Bsum]
  linarith [hAle, hBle, hCle, htri]

/-- **The prime-power (pp-in-AP) level** `PpLevel θ`.  The summed sequence
discrepancy of the prime-power correction weight `ppTerm` over the haircut range.
Its discharge is the elementary but combinatorially heavy pp-in-AP count
(`√x·log² + x^θ·log ≪ x/log^A`), whose per-`q` step needs the number of roots of
`X^k ≡ a (mod q)` — a residue-class square/root count mathlib does not yet
provide.  Carried as a named hypothesis (the D-N2c-bridge floor); see
`docs/blueprints/flags.md`. -/
def PpLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
        seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q)
      ≤ C * x / Real.log x ^ A

/-- **The Abel bridge** (D-N2c step 1, discharged modulo `PpLevel`).  From the
y-uniform meeting point `LambdaLevelU θ` and the prime-power level `PpLevel θ`,
the prime-indicator level `PiLevel θ` follows: sum the per-`q` Abel bound
(`seqDiscrepancy_prime_le_abel`); the `1/log`-weighted von Mangoldt prefix sums
are `LambdaLevelU`-controlled at every prefix `i ≤ x` (the telescoping weight
`∑ w_i = 1/log 2 − 1/log x ≤ 2` folds into the constant), and the pp correction
is `PpLevel`. -/
theorem piLevel_of_lambdaLevelU_of_pp {θ : ℝ}
    (h : LambdaLevelU θ) (hpp : PpLevel θ) : PiLevel θ := by
  intro A hA
  obtain ⟨BΛ, CΛ, hBΛ0, hΛ⟩ := h A hA
  obtain ⟨Bpp, Cpp, hBpp0, hpb⟩ := hpp A hA
  set B := max BΛ Bpp with hBdef
  have hBΛle : BΛ ≤ B := le_max_left _ _
  have hBpple : Bpp ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := le_trans hBΛ0 hBΛle
  set Ksmall : ℕ := ⌊(2 : ℝ) ^ θ / Real.log 2 ^ B⌋₊ with hKs
  set Ctwo : ℝ :=
    (Ksmall : ℝ) * (∑ n ∈ Finset.Icc 1 2, |(if n.Prime then (1 : ℝ) else 0)|)
      * Real.log 2 ^ A
    with hCtwo
  refine ⟨B, max (3 * CΛ + Cpp) Ctwo, hB0, fun x hx => ?_⟩
  rcases lt_or_ge x 3 with hlt | hge
  · -- small-`x` corner: `x = 2`
    have hx2 : x = 2 := by omega
    subst hx2
    simp only [Nat.cast_ofNat]
    rw [← hKs]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2Apos : (0 : ℝ) < Real.log 2 ^ A := Real.rpow_pos_of_pos hlog2pos A
    have hle1 : (∑ q ∈ Finset.Icc 1 Ksmall,
          seqDiscrepancy (fun n => if n.Prime then (1 : ℝ) else 0) 2 q)
        ≤ (Ksmall : ℝ)
            * (2 * ∑ n ∈ Finset.Icc 1 2, |(if n.Prime then (1 : ℝ) else 0)|) := by
      refine (Finset.sum_le_sum (fun q _ =>
        seqDiscrepancy_le_two_mul_sum_abs (fun n => if n.Prime then (1 : ℝ) else 0) 2 q)).trans
        (le_of_eq ?_)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast [Nat.add_sub_cancel]; ring
    refine hle1.trans ?_
    have hchain : (Ksmall : ℝ)
          * (2 * ∑ n ∈ Finset.Icc 1 2, |(if n.Prime then (1 : ℝ) else 0)|)
        = Ctwo * 2 / Real.log 2 ^ A := by rw [hCtwo]; field_simp
    rw [hchain]
    exact (div_le_div_iff_of_pos_right hlog2Apos).mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by norm_num))
  · -- main regime: `x ≥ 3`
    have hx3 : 3 ≤ x := hge
    have hx2 : 2 ≤ x := by omega
    have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hlogx1 : 1 ≤ Real.log x := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      apply Real.log_le_log (Real.exp_pos 1)
      calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        _ ≤ (x : ℝ) := hxR
    have hlogxpos : 0 < Real.log x := by linarith
    have hlogxApos : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hlogxpos A
    have hxθnn : (0 : ℝ) ≤ (x : ℝ) ^ θ := by positivity
    have hinv1 : (Real.log x)⁻¹ ≤ 1 := (inv_anti₀ zero_lt_one hlogx1).trans_eq inv_one
    have hw : ∀ i ∈ Finset.Ioc 1 (x - 1),
        0 ≤ (Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ := by
      intro i hi
      rw [Finset.mem_Ioc] at hi
      have h1 : 0 < Real.log i := Real.log_pos (by exact_mod_cast hi.1)
      have hmono : Real.log i ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
          (by exact_mod_cast (by omega : i ≤ i + 1))
      have hinv : (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.log i)⁻¹ := by gcongr
      linarith
    have mkSub : ∀ Bi : ℝ, Bi ≤ B →
        Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊
          ⊆ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ Bi⌋₊ := by
      intro Bi hBi
      apply Finset.Icc_subset_Icc_right
      apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_left hxθnn (Real.rpow_pos_of_pos hlogxpos Bi)
        (Real.rpow_le_rpow_of_exponent_le hlogx1 hBi)
    set Q := ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊ with hQ
    have hΛtot : ∀ y : ℕ, y ≤ x →
        ∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => vonMangoldt n) y q
          ≤ CΛ * x / Real.log x ^ A :=
      fun y hyx => le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub BΛ hBΛle)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hΛ x y hx2 hyx)
    have hCΛnn : 0 ≤ CΛ * x / Real.log x ^ A :=
      le_trans (Finset.sum_nonneg (fun q _ => seqDiscrepancy_nonneg _ _ _)) (hΛtot x le_rfl)
    have hpptot : ∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q
        ≤ Cpp * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub Bpp hBpple)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hpb x hx2)
    have hsum : ∑ q ∈ Finset.Icc 1 Q,
          seqDiscrepancy (fun n => if n.Prime then (1 : ℝ) else 0) x q
        ≤ ∑ q ∈ Finset.Icc 1 Q,
            ((Real.log x)⁻¹ * seqDiscrepancy (fun n => vonMangoldt n) x q
              + (∑ i ∈ Finset.Ioc 1 (x - 1),
                  ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
                    * seqDiscrepancy (fun n => vonMangoldt n) i q)
              + seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q) :=
      Finset.sum_le_sum (fun q hq =>
        seqDiscrepancy_prime_le_abel hx2 (by have := (Finset.mem_Icc.mp hq).1; omega))
    have hT1 : ∑ q ∈ Finset.Icc 1 Q,
          (Real.log x)⁻¹ * seqDiscrepancy (fun n => vonMangoldt n) x q
        ≤ CΛ * x / Real.log x ^ A := by
      refine le_trans (Finset.sum_le_sum (fun q _ => ?_)) (hΛtot x le_rfl)
      calc (Real.log x)⁻¹ * seqDiscrepancy (fun n => vonMangoldt n) x q
          ≤ 1 * seqDiscrepancy (fun n => vonMangoldt n) x q :=
            mul_le_mul_of_nonneg_right hinv1 (seqDiscrepancy_nonneg _ _ _)
        _ = seqDiscrepancy (fun n => vonMangoldt n) x q := one_mul _
    have hT2 : ∑ q ∈ Finset.Icc 1 Q, ∑ i ∈ Finset.Ioc 1 (x - 1),
          ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
            * seqDiscrepancy (fun n => vonMangoldt n) i q
        ≤ 2 * (CΛ * x / Real.log x ^ A) := by
      rw [Finset.sum_comm]
      have hswap : ∑ i ∈ Finset.Ioc 1 (x - 1), ∑ q ∈ Finset.Icc 1 Q,
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * seqDiscrepancy (fun n => vonMangoldt n) i q
          ≤ ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * (CΛ * x / Real.log x ^ A) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hΛtot i (by rw [Finset.mem_Ioc] at hi; omega)) (hw i hi)
      refine hswap.trans ?_
      rw [← Finset.sum_mul, Salt.BV.sum_w_telescope hx2]
      refine mul_le_mul_of_nonneg_right ?_ hCΛnn
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hle2 : (Real.log 2)⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ hlog2]; nlinarith [Real.log_two_gt_d9]
      linarith [inv_nonneg.mpr hlogxpos.le]
    refine le_trans hsum ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have halg : CΛ * x / Real.log x ^ A + 2 * (CΛ * x / Real.log x ^ A)
        + Cpp * x / Real.log x ^ A = (3 * CΛ + Cpp) * x / Real.log x ^ A := by ring
    calc (∑ q ∈ Finset.Icc 1 Q, (Real.log x)⁻¹ * seqDiscrepancy (fun n => vonMangoldt n) x q)
          + (∑ q ∈ Finset.Icc 1 Q, ∑ i ∈ Finset.Ioc 1 (x - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
                * seqDiscrepancy (fun n => vonMangoldt n) i q)
          + (∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => Salt.BV.ppTerm n) x q)
        ≤ CΛ * x / Real.log x ^ A + 2 * (CΛ * x / Real.log x ^ A) + Cpp * x / Real.log x ^ A :=
          add_le_add (add_le_add hT1 hT2) hpptot
      _ = (3 * CΛ + Cpp) * x / Real.log x ^ A := halg
      _ ≤ max (3 * CΛ + Cpp) Ctwo * x / Real.log x ^ A :=
          (div_le_div_iff_of_pos_right hlogxApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hxpos.le)

/-- **`HasLevel θ` from the y-uniform meeting point** (D-N2c, discharged modulo
`PpLevel`).  Composes the Abel bridge `piLevel_of_lambdaLevelU_of_pp` with the
landed π-seam assembly `hasLevel_of_piLevel` (`Salt/Maynard/GehPiSeam.lean`).
This is the honest form of the D-N2c headline: the `hbridge` hypothesis of
`hasLevel_of_lambdaDiscrepancy` is now discharged from the GEH machinery's own
y-uniform supply `LambdaLevelU`, leaving only the elementary pp-in-AP count
`PpLevel` as the single named obligation. -/
theorem hasLevel_of_lambdaLevelU_of_pp {θ : ℝ} (hθ1 : θ ≤ 1)
    (h : LambdaLevelU θ) (hpp : PpLevel θ) : HasLevel θ :=
  hasLevel_of_piLevel hθ1 (piLevel_of_lambdaLevelU_of_pp h hpp)
