/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehDoor
import Salt.LS.Vaughan
import Salt.LS.TypeSums
import Salt.BV.Defs

/-!
# The GEH door — the AP–Vaughan split (design node D-N2a)

Design freeze: `docs/exploration/s2-b3-design.md`, RE-CUT block (2026-07-17).
This file performs the *Vaughan split* of the Λ-weighted sequence discrepancy at
truncation `U = V = x^{1/3}`, reducing the frozen meeting point `LambdaLevel θ`
to per-piece summed-discrepancy bounds.  Three of the four pieces are genuine
Dirichlet convolutions `dconv α β` (the two Type-I terms and the Type-II
bilinear term); the fourth is a correction supported on the head `n ≤ V`.

## The frozen meeting point

`LambdaLevel θ` (landed verbatim below; D-N2c consumes it) is the summed
sequence-discrepancy of the von Mangoldt weight over moduli `q ≤ x^θ/(log x)^B`,
bounded by `C x/(log x)^A`.  It is the Λ-side twin of `HasLevel`.

## The split (F1 — the pointwise decomposition)

Vaughan's identity (`Salt.LS.vaughan`) gives, for `n > V`,
`Λ n = P₁ n − P₂ n + P₃ n` with each `Pᵢ` a Dirichlet convolution:

* `P₁ = dconv (μ·1_{≤U}) log`      (Type I₁, `vaughanA₁`/`vaughanB₁`);
* `P₂ = dconv (typeICoeff U V) 1`  (Type I₂, `vaughanA₂`, via `sigma2_inner`);
* `P₃ = dconv (μ·1_{>U}) (typeIIData V)` (Type II, `vaughanA₃`).

Writing `Ecorr = Λ − P₁ + P₂ − P₃` (supported on `n ≤ V`, since Vaughan kills it
for `n > V`), the pointwise identity `Λ = Ecorr + P₁ − P₂ + P₃` holds for all
`n ≥ 1` (`vaughan_dconv`).  The sequence discrepancy is subadditive across it
(`seqDiscrepancy_lambda_le`), so `LambdaLevel` follows from a summed-discrepancy
bound on each of `Ecorr, P₁, P₂, P₃`.

## The obligations (the SW-supplier list — D-N2b's brief)

The headline `lambdaLevel_of_GEH_min` takes `GEH_min (3999/4000)` plus explicit
named hypotheses bounding the summed discrepancy of the head/Type-I pieces, and
routes the Type-II piece through `GEH_min`.  Each hypothesis is listed in the
executor report as its exact Lean statement; D-N2b discharges them from the
landed `siegelWalfisz_holds`.
-/

open Finset ArithmeticFunction

open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- **The frozen meeting point** `LambdaLevel θ` (house interface, landed
verbatim).  The summed sequence discrepancy of the von Mangoldt weight over
moduli `q ≤ x^θ/(log x)^B`, bounded by `C x/(log x)^A`.  The Λ-side twin of
`HasLevel`; D-N2c converts it to the π-based `HasLevel` via the landed π-seam
`maxDiscrepancy_le_seqDiscrepancy_prime`. -/
def LambdaLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
        seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) x q)
      ≤ C * x / Real.log x ^ A

/-! ## Subadditivity of `seqDiscrepancy` (F1 engine) -/

/-- `seqDiscrepancy` as a `sup'` over reduced residues (the `q ≠ 0` unfolding),
stated so it can be rewritten on a single occurrence. -/
theorem seqDiscrepancy_eq (f : ℕ → ℝ) (x q : ℕ) (hq : q ≠ 0) :
    seqDiscrepancy f x q
      = ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup'
          (exists_coprime_lt hq) (fun a =>
            |(∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
              - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0)
                / (q.totient : ℝ)|) := by
  rw [seqDiscrepancy, dif_neg hq]

/-- Negating the weight leaves the sequence discrepancy unchanged. -/
theorem seqDiscrepancy_neg (f : ℕ → ℝ) (x q : ℕ) :
    seqDiscrepancy (fun n => - f n) x q = seqDiscrepancy f x q := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; simp [seqDiscrepancy]
  · rw [seqDiscrepancy_eq _ x q hq, seqDiscrepancy_eq _ x q hq]
    refine congrArg _ (funext fun a => ?_)
    have h1 : (∑ n ∈ Finset.Icc 1 x, if n % q = a then - f n else 0)
        = - ∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0 := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun n _ => by split_ifs <;> ring)
    have h2 : (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then - f n else 0)
        = - ∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0 := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun n _ => by split_ifs <;> ring)
    rw [h1, h2, abs_eq_abs]
    right; ring

/-- **Subadditivity (add).**  The sequence discrepancy of a sum of weights is at
most the sum of the discrepancies (triangle inequality inside the `sup'`). -/
theorem seqDiscrepancy_add_le (f g : ℕ → ℝ) (x q : ℕ) :
    seqDiscrepancy (fun n => f n + g n) x q
      ≤ seqDiscrepancy f x q + seqDiscrepancy g x q := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; simp [seqDiscrepancy]
  · rw [seqDiscrepancy_eq _ x q hq]
    refine Finset.sup'_le _ _ (fun a ha => ?_)
    have hRf : (∑ n ∈ Finset.Icc 1 x, if n % q = a then f n + g n else 0)
        = (∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
          + (∑ n ∈ Finset.Icc 1 x, if n % q = a then g n else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => by split_ifs <;> ring)
    have hMf : (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n + g n else 0)
        = (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0)
          + (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then g n else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => by split_ifs <;> ring)
    have hbf := seqDiscrepancy_apply_le f x q a hq ha
    have hbg := seqDiscrepancy_apply_le g x q a hq ha
    rw [hRf, hMf, add_div]
    calc |(_ + _) - (_ + _)|
        = |((∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
              - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0) / (q.totient : ℝ))
            + ((∑ n ∈ Finset.Icc 1 x, if n % q = a then g n else 0)
              - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then g n else 0)
                / (q.totient : ℝ))| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hbf hbg)

/-- **Subadditivity (sub).**  `seqDiscrepancy (f − g) ≤ seqDiscrepancy f +
seqDiscrepancy g`, via `add_le` and `neg`. -/
theorem seqDiscrepancy_sub_le (f g : ℕ → ℝ) (x q : ℕ) :
    seqDiscrepancy (fun n => f n - g n) x q
      ≤ seqDiscrepancy f x q + seqDiscrepancy g x q := by
  have h := seqDiscrepancy_add_le f (fun n => - g n) x q
  rw [seqDiscrepancy_neg] at h
  simpa only [sub_eq_add_neg] using h

/-! ## The four Vaughan pieces (F1) -/

/-- Type I₁ dyadic-free factor: `μ(d)` truncated to `d ≤ U`. -/
noncomputable def vaughanA₁ (U d : ℕ) : ℝ := if d ≤ U then (μ d : ℝ) else 0

/-- Type II dyadic-free factor: `μ(d)` truncated to `d > U`. -/
noncomputable def vaughanA₃ (U d : ℕ) : ℝ := if U < d then (μ d : ℝ) else 0

/-- **Type I₁ piece** `P₁(n) = ∑_{d ∣ n, d ≤ U} μ(d) log(n/d)`.  A Dirichlet
convolution `dconv (μ·1_{≤U}) log` (`vP1_eq_dconv`); the long-smooth Type-I term. -/
noncomputable def vP1 (U n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (· ≤ U), (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ)

/-- **Type I₂ piece** `P₂(n) = ∑_{d ∣ n, d ≤ U} ∑_{c ∣ (n/d), c ≤ V} μ(d) Λ(c)`.
Collapses (via `Salt.LS.typeICoeff`) to `dconv (typeICoeff U V) 1`; the Type-I
term whose coefficient `a(t)` is `log`-bounded. -/
noncomputable def vP2 (U V n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (· ≤ U), ∑ c ∈ (n / d).divisors.filter (· ≤ V),
    (μ d : ℝ) * Λ c

/-- **Type II piece** `P₃(n) = ∑_{d ∣ n, d > U} ∑_{c ∣ (n/d), c > V} μ(d) Λ(c)`.
The genuine bilinear term: a Dirichlet convolution `dconv (μ·1_{>U}) (typeIIData V)`
(`vP3_eq_dconv`), fed to `GEH_min`. -/
noncomputable def vP3 (U V n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (U < ·), ∑ c ∈ (n / d).divisors.filter (V < ·),
    (μ d : ℝ) * Λ c

/-- **Head correction** `Ecorr(n) = Λ(n) − P₁(n) + P₂(n) − P₃(n)`.  By Vaughan's
identity it vanishes for `n > V` (`vErr_eq_zero`), so it is supported on the head
`n ≤ V`; its summed discrepancy is a head/Siegel–Walfisz obligation. -/
noncomputable def vErr (U V n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n - vP1 U n + vP2 U V n - vP3 U V n

/-- **The head correction vanishes off the head.**  For `U, V ≥ 1` and `n > V`,
Vaughan's identity gives `Λ n = P₁ n − P₂ n + P₃ n`, so `Ecorr n = 0`.  Hence
`Ecorr` is supported on `n ≤ V`. -/
theorem vErr_eq_zero {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) {n : ℕ} (hn : V < n) :
    vErr U V n = 0 := by
  have h := Salt.LS.vaughan hU hV hn
  unfold vErr vP1 vP2 vP3
  linarith [h]

/-- **The pointwise Vaughan decomposition (F1).**  For every `n`,
`Λ n = Ecorr n + P₁ n − P₂ n + P₃ n` — immediate from the definition of `Ecorr`.
The content is `vErr_eq_zero` (the correction is a head term). -/
theorem vaughan_dconv (U V n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ)
      = vErr U V n + vP1 U n - vP2 U V n + vP3 U V n := by
  unfold vErr; ring

/-- **Type I₁ is a Dirichlet convolution** `dconv (μ·1_{≤U}) log`.  Certifies the
honest-direction claim that `P₁` is the convolution `GEH_min`/dispersion controls. -/
theorem vP1_eq_dconv (U n : ℕ) :
    vP1 U n = dconv (vaughanA₁ U) (fun m => Real.log (m : ℝ)) n := by
  unfold vP1 dconv vaughanA₁
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  split_ifs <;> ring

/-- **Type II is a Dirichlet convolution** `dconv (μ·1_{>U}) (typeIIData V)`.  This
is the bilinear form fed to `GEH_min`; `vaughanA₃ U` is `μ`-bounded (`≤ 1`) and
`Salt.LS.typeIIData V` is `log`-bounded, so both factors meet `CoeffAt` after a
dyadic split. -/
theorem vP3_eq_dconv (U V n : ℕ) :
    vP3 U V n = dconv (vaughanA₃ U) (Salt.LS.typeIIData V) n := by
  unfold vP3 dconv vaughanA₃
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  split_ifs with h
  · rw [Salt.LS.typeIIData, Finset.mul_sum]
  · rw [zero_mul]

/-- **The Λ-discrepancy splits (F1 engine).**  By the pointwise decomposition and
subadditivity, the sequence discrepancy of the von Mangoldt weight is at most the
sum of the four piece discrepancies. -/
theorem seqDiscrepancy_lambda_le (U V x q : ℕ) :
    seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) x q
      ≤ seqDiscrepancy (vErr U V) x q + seqDiscrepancy (vP1 U) x q
        + seqDiscrepancy (vP2 U V) x q + seqDiscrepancy (vP3 U V) x q := by
  have hpt : (fun n => ArithmeticFunction.vonMangoldt n)
      = (fun n => vErr U V n + vP1 U n - vP2 U V n + vP3 U V n) := by
    funext n; exact vaughan_dconv U V n
  rw [hpt]
  have h1 := seqDiscrepancy_add_le (fun n => vErr U V n + vP1 U n - vP2 U V n) (vP3 U V) x q
  have h2 := seqDiscrepancy_sub_le (fun n => vErr U V n + vP1 U n) (vP2 U V) x q
  have h3 := seqDiscrepancy_add_le (vErr U V) (vP1 U) x q
  linarith

/-! ## The reduction to piece obligations -/

/-- **A crude universal discrepancy bound.**  The sequence discrepancy of any
weight `f` is at most twice its total `ℓ¹` mass on `[1,x]` (each residue sum and
the coprime mean are individually `≤ ∑|f|`, the mean divided by `φ(q) ≥ 1`).
Used to absorb the small-`x` corner where `log x < 1` breaks range monotonicity. -/
theorem seqDiscrepancy_le_two_mul_sum_abs (f : ℕ → ℝ) (x q : ℕ) :
    seqDiscrepancy f x q ≤ 2 * ∑ n ∈ Finset.Icc 1 x, |f n| := by
  have hsum : (0:ℝ) ≤ ∑ n ∈ Finset.Icc 1 x, |f n| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  rcases eq_or_ne q 0 with hq | hq
  · subst hq
    have h0 : seqDiscrepancy f x 0 = 0 := by simp [seqDiscrepancy]
    rw [h0]; linarith
  · rw [seqDiscrepancy_eq _ x q hq]
    refine Finset.sup'_le _ _ (fun a _ha => ?_)
    set R := ∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0 with hR
    set Mean := ∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0 with hMean
    have hφ : (1:ℝ) ≤ (q.totient : ℝ) := by
      have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq); exact_mod_cast this
    have hRle : |R| ≤ ∑ n ∈ Finset.Icc 1 x, |f n| := by
      rw [hR]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
      split_ifs
      · exact le_refl _
      · rw [abs_zero]; exact abs_nonneg _
    have hMle : |Mean| ≤ ∑ n ∈ Finset.Icc 1 x, |f n| := by
      rw [hMean]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
      split_ifs
      · exact le_refl _
      · rw [abs_zero]; exact abs_nonneg _
    have hMeanDiv : |Mean / (q.totient:ℝ)| ≤ ∑ n ∈ Finset.Icc 1 x, |f n| := by
      rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q.totient:ℝ))]
      exact (div_le_self (abs_nonneg _) hφ).trans hMle
    calc |R - Mean / (q.totient:ℝ)|
        ≤ |R| + |Mean / (q.totient:ℝ)| := by
          rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      _ ≤ (∑ n ∈ Finset.Icc 1 x, |f n|) + (∑ n ∈ Finset.Icc 1 x, |f n|) :=
          add_le_add hRle hMeanDiv
      _ = 2 * ∑ n ∈ Finset.Icc 1 x, |f n| := by ring

/-- The truncation `U = V = ⌊x^{1/3}⌋` used in the split (design: `U = V =
x^{1/3}`).  All piece obligations are stated at this truncation. -/
noncomputable def cbrt (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((1:ℝ)/3)⌋₊

/-- **A piece obligation** at level `θ` for a family of weights `g x`: the summed
sequence discrepancy of `g x` over moduli `q ≤ x^θ/(log x)^B` is `≤ C x/(log x)^A`.
This is the common shape of the four Vaughan-piece obligations (`LambdaLevel` is
the case `g x = Λ`).  D-N2b discharges the head/Type-I instances from
`siegelWalfisz_holds`; the Type-II instance is routed through `GEH_min`. -/
def PieceObligation (θ : ℝ) (g : ℕ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊, seqDiscrepancy (g x) x q)
      ≤ C * x / Real.log x ^ A

/-- **The four-piece reduction (F1 assembled).**  `LambdaLevel θ` follows from the
four Vaughan-piece obligations at truncation `U = V = ⌊x^{1/3}⌋` (head/`Ecorr`,
Type I₁/`vP1`, Type I₂/`vP2`, Type II/`vP3`).  The combined haircut is the max of
the four, and the constant is a max of the four-way sum (the `x ≥ 3` regime, via
range monotonicity) and a small-`x` term (the crude bound at `x = 2`, where
`log 2 < 1` reverses range monotonicity). -/
theorem lambdaLevel_of_pieceObligations {θ : ℝ}
    (hHead : PieceObligation θ (fun x n => vErr (cbrt x) (cbrt x) n))
    (hTypeI1 : PieceObligation θ (fun x n => vP1 (cbrt x) n))
    (hTypeI2 : PieceObligation θ (fun x n => vP2 (cbrt x) (cbrt x) n))
    (hTypeII : PieceObligation θ (fun x n => vP3 (cbrt x) (cbrt x) n)) :
    LambdaLevel θ := by
  intro A hA
  obtain ⟨B0, C0, hB0, hb0⟩ := hHead A hA
  obtain ⟨B1, C1, hB1, hb1⟩ := hTypeI1 A hA
  obtain ⟨B2, C2, hB2, hb2⟩ := hTypeI2 A hA
  obtain ⟨B3, C3, hB3, hb3⟩ := hTypeII A hA
  set B : ℝ := max (max B0 B1) (max B2 B3) with hBdef
  have hB0le : B0 ≤ B := le_trans (le_max_left B0 B1) (le_max_left _ _)
  have hB1le : B1 ≤ B := le_trans (le_max_right B0 B1) (le_max_left _ _)
  have hB2le : B2 ≤ B := le_trans (le_max_left B2 B3) (le_max_right _ _)
  have hB3le : B3 ≤ B := le_trans (le_max_right B2 B3) (le_max_right _ _)
  have hBge0 : 0 ≤ B := le_trans hB0 hB0le
  set Ksmall : ℕ := ⌊(2:ℝ) ^ θ / Real.log 2 ^ B⌋₊ with hKs
  set Ctwo : ℝ :=
    (Ksmall : ℝ) * (∑ n ∈ Finset.Icc 1 2, |ArithmeticFunction.vonMangoldt n|) * Real.log 2 ^ A
    with hCtwo
  refine ⟨B, max (C0 + C1 + C2 + C3) Ctwo, hBge0, fun x hx => ?_⟩
  rcases lt_or_ge x 3 with hlt | hge
  · -- Small-`x` corner: `x = 2`.
    have hx2 : x = 2 := by omega
    subst hx2
    simp only [Nat.cast_ofNat]
    rw [← hKs]
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2Apos : (0:ℝ) < Real.log 2 ^ A := Real.rpow_pos_of_pos hlog2pos A
    have hle1 : (∑ q ∈ Finset.Icc 1 Ksmall,
          seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) 2 q)
        ≤ (Ksmall : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 2, |ArithmeticFunction.vonMangoldt n|) := by
      refine (Finset.sum_le_sum
        (fun q _ => seqDiscrepancy_le_two_mul_sum_abs ArithmeticFunction.vonMangoldt 2 q)).trans
        (le_of_eq ?_)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast [Nat.add_sub_cancel]
      ring
    refine hle1.trans ?_
    have hchain : (Ksmall : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 2, |ArithmeticFunction.vonMangoldt n|)
        = Ctwo * 2 / Real.log 2 ^ A := by
      rw [hCtwo]; field_simp
    rw [hchain]
    exact (div_le_div_iff_of_pos_right hlog2Apos).mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by norm_num))
  · -- Main regime: `x ≥ 3`, so `log x ≥ 1` and range monotonicity holds.
    have hx3 : 3 ≤ x := hge
    have hxR : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
    have hxpos : (0:ℝ) < (x:ℝ) := by linarith
    have hlogx1 : 1 ≤ Real.log x := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      apply Real.log_le_log (Real.exp_pos 1)
      calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        _ ≤ (x:ℝ) := hxR
    have hlogxpos : 0 < Real.log x := by linarith
    have hlogxApos : (0:ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hlogxpos A
    have hxθnn : (0:ℝ) ≤ (x:ℝ) ^ θ := by positivity
    -- Range monotonicity for each piece: `B ≥ Bᵢ ⇒ range_B ⊆ range_{Bᵢ}`.
    have mkSub : ∀ Bi : ℝ, Bi ≤ B →
        Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊
          ⊆ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ Bi⌋₊ := by
      intro Bi hBi
      apply Finset.Icc_subset_Icc_right
      apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_left hxθnn (Real.rpow_pos_of_pos hlogxpos Bi)
        (Real.rpow_le_rpow_of_exponent_le hlogx1 hBi)
    have hc0 : (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (vErr (cbrt x) (cbrt x)) x q) ≤ C0 * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub B0 hB0le)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hb0 x hx)
    have hc1 : (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP1 (cbrt x)) x q) ≤ C1 * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub B1 hB1le)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hb1 x hx)
    have hc2 : (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP2 (cbrt x) (cbrt x)) x q) ≤ C2 * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub B2 hB2le)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hb2 x hx)
    have hc3 : (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP3 (cbrt x) (cbrt x)) x q) ≤ C3 * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub B3 hB3le)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hb3 x hx)
    calc (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
            seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) x q)
        ≤ ∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
            (seqDiscrepancy (vErr (cbrt x) (cbrt x)) x q + seqDiscrepancy (vP1 (cbrt x)) x q
              + seqDiscrepancy (vP2 (cbrt x) (cbrt x)) x q
              + seqDiscrepancy (vP3 (cbrt x) (cbrt x)) x q) :=
          Finset.sum_le_sum (fun q _ => seqDiscrepancy_lambda_le (cbrt x) (cbrt x) x q)
      _ = (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (vErr (cbrt x) (cbrt x)) x q)
            + (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (vP1 (cbrt x)) x q)
            + (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (vP2 (cbrt x) (cbrt x)) x q)
            + (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (vP3 (cbrt x) (cbrt x)) x q) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ C0 * x / Real.log x ^ A + C1 * x / Real.log x ^ A
            + C2 * x / Real.log x ^ A + C3 * x / Real.log x ^ A :=
          add_le_add (add_le_add (add_le_add hc0 hc1) hc2) hc3
      _ = (C0 + C1 + C2 + C3) * x / Real.log x ^ A := by ring
      _ ≤ max (C0 + C1 + C2 + C3) Ctwo * x / Real.log x ^ A :=
          (div_le_div_iff_of_pos_right hlogxApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hxpos))

/-! ## The `y`-uniform strengthening `LambdaLevelU` (house amendment, D-N2c seam)

D-N2c's Λ→π Abel bridge needs the discrepancy cutoff to range over prefixes
`y ≤ x` while the *modulus range* and the RHS stay pinned at `x` (the larger,
easier bound).  `LambdaLevelU θ` is that strengthening; it implies the pointwise
`LambdaLevel θ` by `y := x`. -/

/-- **The `y`-uniform meeting point** `LambdaLevelU θ` (house-amended interface,
D-N2c consumes it).  Same summed von Mangoldt discrepancy as `LambdaLevel`, but
the discrepancy cutoff is an arbitrary prefix `y ≤ x`; the modulus range
`q ≤ x^θ/(log x)^B` and the bound `C x/(log x)^A` stay at `x`. -/
def LambdaLevelU (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x y : ℕ, 2 ≤ x → y ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
        seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) y q)
      ≤ C * x / Real.log x ^ A

/-- `LambdaLevelU θ` implies the pointwise `LambdaLevel θ` (set `y := x`). -/
theorem lambdaLevel_of_lambdaLevelU {θ : ℝ} (h : LambdaLevelU θ) : LambdaLevel θ := by
  intro A hA
  obtain ⟨B, C, hB0, hb⟩ := h A hA
  exact ⟨B, C, hB0, fun x hx => hb x x hx (le_refl x)⟩

/-- **A `y`-uniform piece obligation** at level `θ` for a family `g x`: the summed
discrepancy of `g x` at every prefix cutoff `y ≤ x`, over moduli `q ≤ x^θ/(log x)^B`,
is `≤ C x/(log x)^A`.  The `y`-uniform twin of `PieceObligation`. -/
def PieceObligationU (θ : ℝ) (g : ℕ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 ≤ B ∧ ∀ x y : ℕ, 2 ≤ x → y ≤ x →
    (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊, seqDiscrepancy (g x) y q)
      ≤ C * x / Real.log x ^ A

/-- **The `y`-uniform four-piece reduction (amended headline core).**  `LambdaLevelU θ`
follows from the four `y`-uniform Vaughan-piece obligations at `U = V = ⌊x^{1/3}⌋`.
The Vaughan split is pointwise so it holds at every cutoff `y`; the modulus-range
monotonicity is over `x` (unchanged from the pointwise reduction), and the small-`x`
corner uses the crude bound with `Icc 1 y ⊆ Icc 1 2` for `y ≤ x = 2`. -/
theorem lambdaLevelU_of_pieceObligationsU {θ : ℝ}
    (hHead : PieceObligationU θ (fun x n => vErr (cbrt x) (cbrt x) n))
    (hTypeI1 : PieceObligationU θ (fun x n => vP1 (cbrt x) n))
    (hTypeI2 : PieceObligationU θ (fun x n => vP2 (cbrt x) (cbrt x) n))
    (hTypeII : PieceObligationU θ (fun x n => vP3 (cbrt x) (cbrt x) n)) :
    LambdaLevelU θ := by
  intro A hA
  obtain ⟨B0, C0, hB0, hb0⟩ := hHead A hA
  obtain ⟨B1, C1, hB1, hb1⟩ := hTypeI1 A hA
  obtain ⟨B2, C2, hB2, hb2⟩ := hTypeI2 A hA
  obtain ⟨B3, C3, hB3, hb3⟩ := hTypeII A hA
  set B : ℝ := max (max B0 B1) (max B2 B3) with hBdef
  have hB0le : B0 ≤ B := le_trans (le_max_left B0 B1) (le_max_left _ _)
  have hB1le : B1 ≤ B := le_trans (le_max_right B0 B1) (le_max_left _ _)
  have hB2le : B2 ≤ B := le_trans (le_max_left B2 B3) (le_max_right _ _)
  have hB3le : B3 ≤ B := le_trans (le_max_right B2 B3) (le_max_right _ _)
  have hBge0 : 0 ≤ B := le_trans hB0 hB0le
  set Ksmall : ℕ := ⌊(2:ℝ) ^ θ / Real.log 2 ^ B⌋₊ with hKs
  set Ctwo : ℝ :=
    (Ksmall : ℝ) * (∑ n ∈ Finset.Icc 1 2, |ArithmeticFunction.vonMangoldt n|) * Real.log 2 ^ A
    with hCtwo
  refine ⟨B, max (C0 + C1 + C2 + C3) Ctwo, hBge0, fun x y hx hyx => ?_⟩
  rcases lt_or_ge x 3 with hlt | hge
  · -- Small-`x` corner: `x = 2`, `y ≤ 2`.
    have hx2 : x = 2 := by omega
    subst hx2
    simp only [Nat.cast_ofNat]
    rw [← hKs]
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2Apos : (0:ℝ) < Real.log 2 ^ A := Real.rpow_pos_of_pos hlog2pos A
    have hterm : ∀ q : ℕ, seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) y q
        ≤ 2 * ∑ n ∈ Finset.Icc 1 2, |ArithmeticFunction.vonMangoldt n| := by
      intro q
      refine (seqDiscrepancy_le_two_mul_sum_abs ArithmeticFunction.vonMangoldt y q).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (by omega)) (fun n _ _ => abs_nonneg _)
    have hle1 : (∑ q ∈ Finset.Icc 1 Ksmall,
          seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) y q)
        ≤ (Ksmall : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 2, |ArithmeticFunction.vonMangoldt n|) := by
      refine (Finset.sum_le_sum (fun q _ => hterm q)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast [Nat.add_sub_cancel]
      ring
    refine hle1.trans ?_
    have hchain : (Ksmall : ℝ) * (2 * ∑ n ∈ Finset.Icc 1 2, |ArithmeticFunction.vonMangoldt n|)
        = Ctwo * 2 / Real.log 2 ^ A := by
      rw [hCtwo]; field_simp
    rw [hchain]
    exact (div_le_div_iff_of_pos_right hlog2Apos).mpr
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by norm_num))
  · -- Main regime: `x ≥ 3`, cutoff `y` arbitrary `≤ x`.
    have hx3 : 3 ≤ x := hge
    have hxR : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
    have hxpos : (0:ℝ) < (x:ℝ) := by linarith
    have hlogx1 : 1 ≤ Real.log x := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      apply Real.log_le_log (Real.exp_pos 1)
      calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        _ ≤ (x:ℝ) := hxR
    have hlogxpos : 0 < Real.log x := by linarith
    have hlogxApos : (0:ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos hlogxpos A
    have hxθnn : (0:ℝ) ≤ (x:ℝ) ^ θ := by positivity
    have mkSub : ∀ Bi : ℝ, Bi ≤ B →
        Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊
          ⊆ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ Bi⌋₊ := by
      intro Bi hBi
      apply Finset.Icc_subset_Icc_right
      apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_left hxθnn (Real.rpow_pos_of_pos hlogxpos Bi)
        (Real.rpow_le_rpow_of_exponent_le hlogx1 hBi)
    have hc0 : (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (vErr (cbrt x) (cbrt x)) y q) ≤ C0 * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub B0 hB0le)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hb0 x y hx hyx)
    have hc1 : (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP1 (cbrt x)) y q) ≤ C1 * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub B1 hB1le)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hb1 x y hx hyx)
    have hc2 : (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP2 (cbrt x) (cbrt x)) y q) ≤ C2 * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub B2 hB2le)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hb2 x y hx hyx)
    have hc3 : (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP3 (cbrt x) (cbrt x)) y q) ≤ C3 * x / Real.log x ^ A :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (mkSub B3 hB3le)
        (fun q _ _ => seqDiscrepancy_nonneg _ _ _)) (hb3 x y hx hyx)
    calc (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
            seqDiscrepancy (fun n => ArithmeticFunction.vonMangoldt n) y q)
        ≤ ∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
            (seqDiscrepancy (vErr (cbrt x) (cbrt x)) y q + seqDiscrepancy (vP1 (cbrt x)) y q
              + seqDiscrepancy (vP2 (cbrt x) (cbrt x)) y q
              + seqDiscrepancy (vP3 (cbrt x) (cbrt x)) y q) :=
          Finset.sum_le_sum (fun q _ => seqDiscrepancy_lambda_le (cbrt x) (cbrt x) y q)
      _ = (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (vErr (cbrt x) (cbrt x)) y q)
            + (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (vP1 (cbrt x)) y q)
            + (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (vP2 (cbrt x) (cbrt x)) y q)
            + (∑ q ∈ Finset.Icc 1 ⌊(x:ℝ) ^ θ / Real.log x ^ B⌋₊,
              seqDiscrepancy (vP3 (cbrt x) (cbrt x)) y q) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ C0 * x / Real.log x ^ A + C1 * x / Real.log x ^ A
            + C2 * x / Real.log x ^ A + C3 * x / Real.log x ^ A :=
          add_le_add (add_le_add (add_le_add hc0 hc1) hc2) hc3
      _ = (C0 + C1 + C2 + C3) * x / Real.log x ^ A := by ring
      _ ≤ max (C0 + C1 + C2 + C3) Ctwo * x / Real.log x ^ A :=
          (div_le_div_iff_of_pos_right hlogxApos).mpr
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hxpos))

/-! ## Feeding a piece to `GEH_min` (the SWAt-consuming mechanism)

`pieceObligationU_of_GEH_single` is where `GEH_min` does real work: given a
coefficient/SW-admissible balanced family `(α, β, N, M)` and a *domination* of a
weight `w`'s summed discrepancy by that family's `GEH_min`-controlled discrepancy,
it produces the `y`-uniform piece obligation for `w`.  The lemma is generic in
`w` and NON-VACUOUS (usable for any weight the family dominates); it consumes a
single clean `SWAt β M` — the exact analytic input D-N2b discharges.

For the Type-II piece `vP3`, `hdom` is the AP-Vaughan **dyadic reduction** of the
bilinear form to a `GEH_min` form.  In full it is a sum over `O(log² x)` dyadic
block pairs (each in the balanced window at `U = V = x^{1/3}`); this lemma
packages the single-block idealisation, so `hdom` is the flagged floor (the
multi-block bookkeeping is the remaining D-N2a content — see the executor report). -/
theorem pieceObligationU_of_GEH_single {θ ε : ℝ} (hε : 0 < ε)
    (hGEH : GEH_min θ) (w : ℕ → ℕ → ℝ)
    (k : ℕ) (α β : ℕ → ℕ → ℝ) (N M : ℕ → ℕ)
    (hα : CoeffAt α N k) (hβ : CoeffAt β M k) (hSW : SWAt β M)
    (hwin : ∀ x : ℕ, 2 ≤ x →
      (x : ℝ) ^ ε ≤ (N x : ℝ) ∧ (N x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      (x : ℝ) ^ ε ≤ (M x : ℝ) ∧ (M x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      N x * M x ≤ x ∧ x ≤ 4 * N x * M x)
    (hdom : ∀ (B : ℝ) (x y : ℕ), 2 ≤ x → y ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊, seqDiscrepancy (w x) y q)
        ≤ (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
            seqDiscrepancy (dconv (α x) (β x)) (4 * N x * M x) q)) :
    PieceObligationU θ w := by
  intro A hA
  obtain ⟨j, KF, hSWData⟩ := sWAtData_of_sWAt hSW
  obtain ⟨B, C, hB0, hbound⟩ := hGEH ε A hε hA k j KF
  refine ⟨B, C, hB0, fun x y hx hyx => ?_⟩
  refine (hdom B x y hx hyx).trans ?_
  obtain ⟨hN1, hN2, hM1, hM2, hNM, hx4⟩ := hwin x hx
  exact hbound α β N M hα hβ hSWData x (4 * N x * M x) hx (le_refl _)
    hN1 hN2 hM1 hM2 hNM hx4

/-- **The headline (amended target).**  `GEH_min (3999/4000)` plus the explicit
SW-supplier obligations implies the `y`-uniform meeting point
`LambdaLevelU (3999/4000)`.  The Type-II bilinear piece `vP3` is routed through
`GEH_min` (consuming `hSW : SWAt β M`, the single analytic obligation, via the
dyadic-reduction domination `hdom`); the head/`Ecorr` and the two Type-I pieces
are the remaining SW-supplier obligations `hHead`, `hTypeI1`, `hTypeI2`.  See the
executor report for the exact obligation list (D-N2b's contract). -/
theorem lambdaLevelU_of_GEH_min {ε : ℝ} (hε : 0 < ε)
    (hGEH : GEH_min (3999 / 4000))
    (k : ℕ) (α β : ℕ → ℕ → ℝ) (N M : ℕ → ℕ)
    (hα : CoeffAt α N k) (hβ : CoeffAt β M k) (hSW : SWAt β M)
    (hwin : ∀ x : ℕ, 2 ≤ x →
      (x : ℝ) ^ ε ≤ (N x : ℝ) ∧ (N x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      (x : ℝ) ^ ε ≤ (M x : ℝ) ∧ (M x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      N x * M x ≤ x ∧ x ≤ 4 * N x * M x)
    (hdom : ∀ (B : ℝ) (x y : ℕ), 2 ≤ x → y ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP3 (cbrt x) (cbrt x)) y q)
        ≤ (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ B⌋₊,
            seqDiscrepancy (dconv (α x) (β x)) (4 * N x * M x) q))
    (hHead : PieceObligationU (3999 / 4000) (fun x n => vErr (cbrt x) (cbrt x) n))
    (hTypeI1 : PieceObligationU (3999 / 4000) (fun x n => vP1 (cbrt x) n))
    (hTypeI2 : PieceObligationU (3999 / 4000) (fun x n => vP2 (cbrt x) (cbrt x) n)) :
    LambdaLevelU (3999 / 4000) :=
  lambdaLevelU_of_pieceObligationsU hHead hTypeI1 hTypeI2
    (pieceObligationU_of_GEH_single hε hGEH (fun x n => vP3 (cbrt x) (cbrt x) n)
      k α β N M hα hβ hSW hwin hdom)

/-- **The pointwise headline** `lambdaLevel_of_GEH_min`: the same hypotheses give
the frozen (pointwise) `LambdaLevel (3999/4000)`, via `lambdaLevel_of_lambdaLevelU`. -/
theorem lambdaLevel_of_GEH_min {ε : ℝ} (hε : 0 < ε)
    (hGEH : GEH_min (3999 / 4000))
    (k : ℕ) (α β : ℕ → ℕ → ℝ) (N M : ℕ → ℕ)
    (hα : CoeffAt α N k) (hβ : CoeffAt β M k) (hSW : SWAt β M)
    (hwin : ∀ x : ℕ, 2 ≤ x →
      (x : ℝ) ^ ε ≤ (N x : ℝ) ∧ (N x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      (x : ℝ) ^ ε ≤ (M x : ℝ) ∧ (M x : ℝ) ≤ (x : ℝ) ^ (1 - ε) ∧
      N x * M x ≤ x ∧ x ≤ 4 * N x * M x)
    (hdom : ∀ (B : ℝ) (x y : ℕ), 2 ≤ x → y ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ B⌋₊,
          seqDiscrepancy (vP3 (cbrt x) (cbrt x)) y q)
        ≤ (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ B⌋₊,
            seqDiscrepancy (dconv (α x) (β x)) (4 * N x * M x) q))
    (hHead : PieceObligationU (3999 / 4000) (fun x n => vErr (cbrt x) (cbrt x) n))
    (hTypeI1 : PieceObligationU (3999 / 4000) (fun x n => vP1 (cbrt x) n))
    (hTypeI2 : PieceObligationU (3999 / 4000) (fun x n => vP2 (cbrt x) (cbrt x) n)) :
    LambdaLevel (3999 / 4000) :=
  lambdaLevel_of_lambdaLevelU
    (lambdaLevelU_of_GEH_min hε hGEH k α β N M hα hβ hSW hwin hdom hHead hTypeI1 hTypeI2)
