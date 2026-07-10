/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.CongCount
import Salt.Maynard.CrossCollision
import Salt.Maynard.CollisionQuant
import Salt.Maynard.LamBoundSharp
import Salt.Maynard.DivisorCount
import Salt.Maynard.S1Error
import Salt.Maynard.Diagonal
import Salt.Maynard.Tuple

/-!
# N4.3 — the S₁ upper bound (first ASSEMBLY node)

We define the concrete Selberg sum `S₁` over the `W`-trick window and bound
it above by the diagonal main term plus an explicit trivial-error term.

The chain:

* `S1_eq_sum_dd` (L1) — square-expand `weightSq` and swap the `n`-sum inside
  to identify `S₁` with `∑_{d,e} λ_d λ_e · congCountTuple`.
* `S1_le_main_add_error` (L2) — split each `(d,e)` into the collision case
  (count `= 0`) and the compatible case (count `≈ ((K₀-1)N)/(W∏lcm)`), via
  `congCountTuple_collision` / `congCountTuple_approx`.
* `S1_le` (L3) — feed the compatible form through `compat_le_two_yside` to
  land the `2·((K₀-1)N/W)·yside` main term.
* `S1_trivial_error_le'` (L4) — the trivial error is
  `O_k(R²·(1+log R)^(4k+2))`, via `kSieveIndex_card_le` × `lam_abs_le_sharp`.
* `S1_upper` — the assembled headline.

PORT-BLOCKER: the CRT solvability hypothesis `hsol` of `congCountTuple_approx`
is threaded as a per-compatible-pair hypothesis (see the header of L2). It is
true (pairwise-coprime moduli ⇒ CRT-solvable) but its Lean construction over a
`Fin k`-indexed product of moduli is deferred.
-/

namespace Salt.Maynard

open Finset

/-! ## Concrete objects -/

/-- The `W`-trick window: `n ∈ (N, K₀N]` with `n ≡ ν₀ (mod W)`. -/
noncomputable def windowSet (K₀ N W ν₀ : ℕ) : Finset ℕ :=
  (Finset.Ioc N (K₀ * N)).filter (fun n => n % W = ν₀ % W)

/-- The squared Selberg weight at `n`: the square of the sum of `λ_d` over the
sieve tuples `d` all of whose coordinates divide the shifted `n + hᵢ`. -/
noncomputable def weightSq (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ (kSieveIndex k R W).filter (fun d => ∀ i, d i ∣ (n + hSeq k i)),
      lam k R W y d) ^ 2

/-- The Selberg sum `S₁` over the window. -/
noncomputable def S1 (k K₀ N R W ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ) : ℝ :=
  ∑ n ∈ windowSet K₀ N W ν₀, weightSq k R W y n

/-- `lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c` for naturals. -/
private theorem nat_lcm_dvd_iff (a b c : ℕ) : Nat.lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c :=
  ⟨fun h => ⟨(Nat.dvd_lcm_left a b).trans h, (Nat.dvd_lcm_right a b).trans h⟩,
    fun ⟨h1, h2⟩ => Nat.lcm_dvd h1 h2⟩

/-! ## L1 — square expansion + sum swap -/

/-- **L1.** Expanding the square in `weightSq` and swapping the window sum
inside identifies `S₁` with the count-weighted double `λ`-sum. (`W'` is the
window/sieve modulus, required to equal `W k`.) -/
theorem S1_eq_sum_dd (k K₀ N R W' ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ) (hW : W' = W k) :
    S1 k K₀ N R W' ν₀ y
      = ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
          lam k R W' y d * lam k R W' y e * (congCountTuple k K₀ N ν₀ d e : ℝ) := by
  classical
  subst hW
  unfold S1 weightSq
  -- Step 1: expand the square of the filtered sum into a double indicator sum.
  have step1 : ∀ n,
      (∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => ∀ i, d i ∣ (n + hSeq k i)),
          lam k R (W k) y d) ^ 2
        = ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
            (if ∀ i, d i ∣ (n + hSeq k i) then lam k R (W k) y d else 0) *
            (if ∀ i, e i ∣ (n + hSeq k i) then lam k R (W k) y e else 0) := by
    intro n
    rw [Finset.sum_filter, sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun n _ => step1 n)]
  -- Step 2: swap the window sum to the innermost position.
  have swap :
      (∑ n ∈ windowSet K₀ N (W k) ν₀, ∑ d ∈ kSieveIndex k R (W k),
          ∑ e ∈ kSieveIndex k R (W k),
            (if ∀ i, d i ∣ (n + hSeq k i) then lam k R (W k) y d else 0) *
            (if ∀ i, e i ∣ (n + hSeq k i) then lam k R (W k) y e else 0))
        = ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
            ∑ n ∈ windowSet K₀ N (W k) ν₀,
              (if ∀ i, d i ∣ (n + hSeq k i) then lam k R (W k) y d else 0) *
              (if ∀ i, e i ∣ (n + hSeq k i) then lam k R (W k) y e else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.sum_comm]
  rw [swap]
  -- Step 3: evaluate each inner window sum as `λ_d λ_e · congCountTuple`.
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro e _
  -- collapse the product of indicators to a single guarded value
  have inner_eq : ∀ n,
      (if ∀ i, d i ∣ (n + hSeq k i) then lam k R (W k) y d else 0) *
        (if ∀ i, e i ∣ (n + hSeq k i) then lam k R (W k) y e else 0)
        = if ((∀ i, d i ∣ (n + hSeq k i)) ∧ (∀ i, e i ∣ (n + hSeq k i)))
            then lam k R (W k) y d * lam k R (W k) y e else 0 := by
    intro n
    by_cases hd' : ∀ i, d i ∣ (n + hSeq k i) <;>
      by_cases he' : ∀ i, e i ∣ (n + hSeq k i) <;>
      simp [hd', he']
  rw [Finset.sum_congr rfl (fun n _ => inner_eq n), ← Finset.sum_filter]
  rw [Finset.sum_const]
  -- identify the filtered window with the congCountTuple filter
  have hcard :
      ((windowSet K₀ N (W k) ν₀).filter
          (fun n => (∀ i, d i ∣ (n + hSeq k i)) ∧ (∀ i, e i ∣ (n + hSeq k i)))).card
        = congCountTuple k K₀ N ν₀ d e := by
    unfold windowSet congCountTuple
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro n _
    constructor
    · rintro ⟨hmod, hd', he'⟩
      exact ⟨hmod, fun i => (nat_lcm_dvd_iff _ _ _).mpr ⟨hd' i, he' i⟩⟩
    · rintro ⟨hmod, hlcm⟩
      refine ⟨hmod, fun i => ((nat_lcm_dvd_iff _ _ _).mp (hlcm i)).1,
        fun i => ((nat_lcm_dvd_iff _ _ _).mp (hlcm i)).2⟩
  rw [hcard, nsmul_eq_mul]
  ring

/-! ## L2 — split compatible vs collision -/

/-- **L2.** Splitting each pair into the collision case (count `= 0`, via
`congCountTuple_collision`) and the compatible case (count `≈ main`, via
`congCountTuple_approx`) bounds `S₁` by `mainCoeff · s1CompatForm` plus the
trivial error. The CRT solvability `hsol` is threaded per compatible pair. -/
theorem S1_le_main_add_error (k K₀ N R W' ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hW : W' = W k) (hK₀ : 1 ≤ K₀)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    S1 k K₀ N R W' ν₀ y
      ≤ ((K₀ - 1) * N / W' : ℝ) * s1CompatForm k R W' y
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by
  classical
  subst hW
  rw [S1_eq_sum_dd k K₀ N R (W k) ν₀ y rfl]
  set 𝒟 := kSieveIndex k R (W k) with h𝒟
  -- Positivity of `W k`.
  have hWpos : 0 < W k := Nat.pos_of_ne_zero (W_squarefree k).ne_zero
  have hWR : (W k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hWpos.ne'
  -- Per-pair bound.
  have hterm : ∀ d ∈ 𝒟, ∀ e ∈ 𝒟,
      lam k R (W k) y d * lam k R (W k) y e * (congCountTuple k K₀ N ν₀ d e : ℝ)
        ≤ (if IsCollisionPair d e then 0 else
              ((K₀ - 1) * N / W k : ℝ) * s1Summand k R (W k) y d e)
          + 2 ^ (k + 1) * (|lam k R (W k) y d| * |lam k R (W k) y e|) := by
    intro d hd e he
    have hdpos : ∀ i, 0 < d i := fun i => kSieveIndex_coord_pos hd i
    have hepos : ∀ i, 0 < e i := fun i => kSieveIndex_coord_pos he i
    have hmemd := (mem_kSieveIndex_iff d).mp hd
    have hmeme := (mem_kSieveIndex_iff e).mp he
    by_cases hcol : IsCollisionPair d e
    · -- collision: the count is 0.
      obtain ⟨i, j, hij, hnc⟩ := id hcol
      have hzero : congCountTuple k K₀ N ν₀ d e = 0 :=
        congCountTuple_collision k K₀ N ν₀ d e hmemd.2.2.1 hmeme.2.2.1 hij hnc
      rw [if_pos hcol, hzero]
      simp only [Nat.cast_zero, mul_zero]
      positivity
    · -- compatible: use the approx.
      rw [if_neg hcol]
      have hcompat : ∀ a b, a ≠ b → Nat.Coprime (d a) (e b) := by
        intro a b hab; by_contra h; exact hcol ⟨a, b, hab, h⟩
      have hlcmpos : ∀ i, 0 < Nat.lcm (d i) (e i) := fun i =>
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdpos i).ne' (hepos i).ne')
      have hcopW : ∀ i, Nat.Coprime (W k) (Nat.lcm (d i) (e i)) := by
        intro i
        have hld : Nat.lcm (d i) (e i) ∣ d i * e i :=
          Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
        exact Nat.Coprime.coprime_dvd_right hld
          ((hmemd.2.2.1 i).symm.mul_right (hmeme.2.2.1 i).symm)
      have hcoplcm : ∀ i j, i ≠ j →
          Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) := by
        intro i j hij
        have hcop_prod : Nat.Coprime (d i * e i) (d j * e j) := by
          apply Nat.Coprime.mul_left
          · exact (hmemd.2.1 i j hij).mul_right (hcompat i j hij)
          · exact (hcompat j i (Ne.symm hij)).symm.mul_right (hmeme.2.1 i j hij)
        have hld : Nat.lcm (d i) (e i) ∣ d i * e i :=
          Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
        have hle : Nat.lcm (d j) (e j) ∣ d j * e j :=
          Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
        exact (hcop_prod.coprime_dvd_left hld).coprime_dvd_right hle
      have happrox := congCountTuple_approx k K₀ N ν₀ d e hK₀ hlcmpos hcopW hcoplcm
        (hsol d hd e he hcol)
      -- cast the denominator
      have hcast : ((W k * ∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ)
          = (W k : ℝ) * ∏ i, (Nat.lcm (d i) (e i) : ℝ) := by push_cast; ring
      rw [hcast] at happrox
      -- `mainCoeff · s1Summand = λλ · main`.
      have hmaineq : ((K₀ - 1) * N / W k : ℝ) * s1Summand k R (W k) y d e
          = lam k R (W k) y d * lam k R (W k) y e
              * (((K₀ - 1) * N : ℝ) / ((W k : ℝ) * ∏ i, (Nat.lcm (d i) (e i) : ℝ))) := by
        unfold s1Summand
        ring
      rw [hmaineq]
      set CT : ℝ := (congCountTuple k K₀ N ν₀ d e : ℝ) with hCT
      set main : ℝ := ((K₀ - 1) * N : ℝ) / ((W k : ℝ) * ∏ i, (Nat.lcm (d i) (e i) : ℝ))
        with hmain
      -- the discrepancy bound
      have hdisc : lam k R (W k) y d * lam k R (W k) y e * (CT - main)
          ≤ |lam k R (W k) y d| * |lam k R (W k) y e| * 2 ^ (k + 1) := by
        calc lam k R (W k) y d * lam k R (W k) y e * (CT - main)
            ≤ |lam k R (W k) y d * lam k R (W k) y e * (CT - main)| := le_abs_self _
          _ = |lam k R (W k) y d| * |lam k R (W k) y e| * |CT - main| := by
              rw [abs_mul, abs_mul]
          _ ≤ |lam k R (W k) y d| * |lam k R (W k) y e| * 2 ^ (k + 1) :=
              mul_le_mul_of_nonneg_left happrox
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hexp : lam k R (W k) y d * lam k R (W k) y e * (CT - main)
          = lam k R (W k) y d * lam k R (W k) y e * CT
            - lam k R (W k) y d * lam k R (W k) y e * main := by ring
      nlinarith [hdisc, hexp]
  -- Sum the per-pair bound and regroup.
  refine (Finset.sum_le_sum (fun d hd =>
    Finset.sum_le_sum (fun e he => hterm d hd e he))).trans ?_
  -- split the double sum
  rw [Finset.sum_congr rfl (fun d _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  apply add_le_add
  · -- main part: pull the coefficient out to reach `mainCoeff · s1CompatForm`.
    apply le_of_eq
    unfold s1CompatForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e _
    split_ifs <;> ring
  · -- error part: `∑∑ 2^(k+1)|λd||λe| = 2^(k+1) (∑|λ|)²`.
    apply le_of_eq
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]

/-! ## L3 — the main term via `compat_le_two_yside` -/

/-- **L3.** Feeding the compatible form through `compat_le_two_yside` lands the
`2·((K₀-1)N/W)·yside` main term. The tensor hypotheses `(f₀,hf01,hfmono,hy)`
and `(hW,hk,hD)` are exactly those of `compat_le_two_yside`. -/
theorem S1_le (k K₀ N R W' ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ) (f₀ : ℕ → ℝ)
    (hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW : W' = W k) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) (hK₀ : 1 ≤ K₀)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by
  have hL2 := S1_le_main_add_error k K₀ N R W' ν₀ y hW hK₀ hsol
  have hcompat := compat_le_two_yside k R W' y f₀ hf01 hfmono hy hW hk hD
  have hcoeff_nonneg : (0 : ℝ) ≤ ((K₀ - 1) * N / W' : ℝ) := by
    have h1 : (0 : ℝ) ≤ (K₀ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
      linarith
    exact div_nonneg (mul_nonneg h1 (by positivity)) (by positivity)
  calc S1 k K₀ N R W' ν₀ y
      ≤ ((K₀ - 1) * N / W' : ℝ) * s1CompatForm k R W' y
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := hL2
    _ ≤ ((K₀ - 1) * N / W' : ℝ)
          * (2 * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hcompat hcoeff_nonneg) (le_refl _)
    _ = 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by ring

/-! ## L4 — the trivial error is small -/

/-- **L4.** The trivial error is `O_k(R²·(1+log R)^(4k+2))`. The exponent is
`4k+2 = 2·(2k+1)`: `∑_d|λ_d| ≤ card·λ_max ≤ (R(1+logR)^k)·(Cl(1+logR)^(k+1))
= Cl·R·(1+logR)^(2k+1)`, and squaring doubles both the coefficient's power and
the log exponent. (The brief's "(2k+2)" is an arithmetic slip: `2·(2k+1)=4k+2`,
not `2k+2`; see the report.) -/
theorem S1_trivial_error_le' (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ r, |y r| ≤ 1) (hR : 2 ≤ R) (hW0 : W' ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2
      ≤ C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  obtain ⟨Cl, hCl1, hCl⟩ := lam_abs_le_sharp k R W' y hy1 hR hW0
  have hCl0 : (0 : ℝ) ≤ Cl := le_trans zero_le_one hCl1
  have hlog0 : (0 : ℝ) ≤ 1 + Real.log R := by
    have hR1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hR
    have := Real.log_pos hR1; linarith
  have hsum : ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
      ≤ (kSieveIndex k R W').card • (Cl * (1 + Real.log R) ^ (k + 1)) :=
    Finset.sum_le_card_nsmul _ _ _ (fun d hd => hCl d hd)
  rw [nsmul_eq_mul] at hsum
  have hcard := kSieveIndex_card_le k R W' hR
  have hsum0 : (0 : ℝ) ≤ ∑ d ∈ kSieveIndex k R W', |lam k R W' y d| :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  -- ∑|λ| ≤ Cl · R · (1+logR)^(2k+1)
  have hchain : ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
      ≤ Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1) := by
    have hexp : k + (k + 1) = 2 * k + 1 := by ring
    calc ∑ d ∈ kSieveIndex k R W', |lam k R W' y d|
        ≤ ((kSieveIndex k R W').card : ℝ) * (Cl * (1 + Real.log R) ^ (k + 1)) := hsum
      _ ≤ ((R : ℝ) * (1 + Real.log R) ^ k) * (Cl * (1 + Real.log R) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hCl0 (pow_nonneg hlog0 _))
      _ = Cl * (R : ℝ) * ((1 + Real.log R) ^ k * (1 + Real.log R) ^ (k + 1)) := by ring
      _ = Cl * (R : ℝ) * (1 + Real.log R) ^ (k + (k + 1)) := by rw [← pow_add]
      _ = Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1) := by rw [hexp]
  refine ⟨Cl ^ 2, by positivity, ?_⟩
  have hee : (2 * k + 1) * 2 = 4 * k + 2 := by ring
  calc (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2
      ≤ (Cl * (R : ℝ) * (1 + Real.log R) ^ (2 * k + 1)) ^ 2 :=
        pow_le_pow_left₀ hsum0 hchain 2
    _ = Cl ^ 2 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
        rw [mul_pow, mul_pow, ← pow_mul, hee]

/-! ## The headline S₁ upper bound -/

/-- **N4.3.** The assembled S₁ upper bound: `S₁` is at most the diagonal main
term `2·((K₀-1)N/W)·yside` plus an explicit trivial error of shape
`C·R²·(1+log R)^(4k+2)` (which is `o(N)` at `R = ⌊N^{1/5}⌋`). The constant is
`C = 2^(k+1)·Cl²` with `Cl` the `lam_abs_le_sharp` constant. -/
theorem S1_upper (k K₀ N R W' ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ) (f₀ : ℕ → ℝ)
    (hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW : W' = W k) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) (hK₀ : 1 ≤ K₀)
    (hR : 2 ≤ R)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W k = ν₀ % W k ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    ∃ C : ℝ, 0 ≤ C ∧ S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  -- `|y| ≤ 1` from the tensor structure.
  have hy1 : ∀ r, |y r| ≤ 1 := by
    intro r
    rw [hy r]
    split_ifs with h
    · rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hf01 _).1))]
      calc ∏ i, f₀ (r i) ≤ ∏ _i : Fin k, (1 : ℝ) :=
            Finset.prod_le_prod (fun i _ => (hf01 _).1) (fun i _ => (hf01 _).2)
        _ = 1 := by simp
    · simp
  have hW0 : W' ≠ 0 := by
    rw [hW]; exact (Nat.pos_of_ne_zero (W_squarefree k).ne_zero).ne'
  obtain ⟨C0, hC0, hC0le⟩ := S1_trivial_error_le' k R W' y hy1 hR hW0
  have hL3 := S1_le k K₀ N R W' ν₀ y f₀ hf01 hfmono hy hW hk hD hK₀ hsol
  refine ⟨2 ^ (k + 1) * C0, by positivity, ?_⟩
  calc S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := hL3
    _ ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2)) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hC0le (by positivity))
    _ = 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + (2 ^ (k + 1) * C0) * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by ring

/-! ## Free-modulus `(D, W')` generalization (explicit-gaps sweep W2-4)

The `S₁` chain with the `hW : W' = W k` pin DROPPED: `W'` is a genuinely free
squarefree modulus, and the collision/compat facts are supplied by the free-`D`
hypotheses `hDlt : ∀ p prime, p ∤ W' → D < p` and `hlt : ∀ i, hSeq k i < D`
(replacing `W k = primorial (D₀ k)`).  `S1`, `weightSq`, `s1CompatForm` and
`S1_trivial_error_le'` are already `W`-generic; only the counting/collision
inputs change.  Instantiate `W' := W k`, `D := D₀ k` (with `hDlt` from the
primorial and `hlt` from `hSeq_le_D₀`, using `D₀ 5 = 125 > 19 = (H 5).sup`) to
recover the pinned versions. -/

/-- Free-modulus form of `S1_eq_sum_dd` (no `hW`). -/
theorem S1_eq_sum_ddW (k K₀ N R W' ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ) :
    S1 k K₀ N R W' ν₀ y
      = ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
          lam k R W' y d * lam k R W' y e * (congCountTupleW k K₀ N ν₀ W' d e : ℝ) := by
  classical
  unfold S1 weightSq
  have step1 : ∀ n,
      (∑ d ∈ (kSieveIndex k R W').filter (fun d => ∀ i, d i ∣ (n + hSeq k i)),
          lam k R W' y d) ^ 2
        = ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
            (if ∀ i, d i ∣ (n + hSeq k i) then lam k R W' y d else 0) *
            (if ∀ i, e i ∣ (n + hSeq k i) then lam k R W' y e else 0) := by
    intro n
    rw [Finset.sum_filter, sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun n _ => step1 n)]
  have swap :
      (∑ n ∈ windowSet K₀ N W' ν₀, ∑ d ∈ kSieveIndex k R W',
          ∑ e ∈ kSieveIndex k R W',
            (if ∀ i, d i ∣ (n + hSeq k i) then lam k R W' y d else 0) *
            (if ∀ i, e i ∣ (n + hSeq k i) then lam k R W' y e else 0))
        = ∑ d ∈ kSieveIndex k R W', ∑ e ∈ kSieveIndex k R W',
            ∑ n ∈ windowSet K₀ N W' ν₀,
              (if ∀ i, d i ∣ (n + hSeq k i) then lam k R W' y d else 0) *
              (if ∀ i, e i ∣ (n + hSeq k i) then lam k R W' y e else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.sum_comm]
  rw [swap]
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro e _
  have inner_eq : ∀ n,
      (if ∀ i, d i ∣ (n + hSeq k i) then lam k R W' y d else 0) *
        (if ∀ i, e i ∣ (n + hSeq k i) then lam k R W' y e else 0)
        = if ((∀ i, d i ∣ (n + hSeq k i)) ∧ (∀ i, e i ∣ (n + hSeq k i)))
            then lam k R W' y d * lam k R W' y e else 0 := by
    intro n
    by_cases hd' : ∀ i, d i ∣ (n + hSeq k i) <;>
      by_cases he' : ∀ i, e i ∣ (n + hSeq k i) <;>
      simp [hd', he']
  rw [Finset.sum_congr rfl (fun n _ => inner_eq n), ← Finset.sum_filter]
  rw [Finset.sum_const]
  have hcard :
      ((windowSet K₀ N W' ν₀).filter
          (fun n => (∀ i, d i ∣ (n + hSeq k i)) ∧ (∀ i, e i ∣ (n + hSeq k i)))).card
        = congCountTupleW k K₀ N ν₀ W' d e := by
    unfold windowSet congCountTupleW
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro n _
    constructor
    · rintro ⟨hmod, hd', he'⟩
      exact ⟨hmod, fun i => (nat_lcm_dvd_iff _ _ _).mpr ⟨hd' i, he' i⟩⟩
    · rintro ⟨hmod, hlcm⟩
      refine ⟨hmod, fun i => ((nat_lcm_dvd_iff _ _ _).mp (hlcm i)).1,
        fun i => ((nat_lcm_dvd_iff _ _ _).mp (hlcm i)).2⟩
  rw [hcard, nsmul_eq_mul]
  ring

/-- Free-modulus form of `S1_le_main_add_error` (no `hW`). -/
theorem S1_le_main_add_errorW (k K₀ N R W' ν₀ D : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hW' : Squarefree W') (hK₀ : 1 ≤ K₀)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin k, hSeq k i < D)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    S1 k K₀ N R W' ν₀ y
      ≤ ((K₀ - 1) * N / W' : ℝ) * s1CompatForm k R W' y
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by
  classical
  rw [S1_eq_sum_ddW k K₀ N R W' ν₀ y]
  set 𝒟 := kSieveIndex k R W' with h𝒟
  have hWpos : 0 < W' := Nat.pos_of_ne_zero hW'.ne_zero
  have hWR : (W' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hWpos.ne'
  have hDle : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D ≤ p := fun p hp hpW => (hDlt p hp hpW).le
  have hterm : ∀ d ∈ 𝒟, ∀ e ∈ 𝒟,
      lam k R W' y d * lam k R W' y e * (congCountTupleW k K₀ N ν₀ W' d e : ℝ)
        ≤ (if IsCollisionPair d e then 0 else
              ((K₀ - 1) * N / W' : ℝ) * s1Summand k R W' y d e)
          + 2 ^ (k + 1) * (|lam k R W' y d| * |lam k R W' y e|) := by
    intro d hd e he
    have hdpos : ∀ i, 0 < d i := fun i => kSieveIndex_coord_pos hd i
    have hepos : ∀ i, 0 < e i := fun i => kSieveIndex_coord_pos he i
    have hmemd := (mem_kSieveIndex_iff d).mp hd
    have hmeme := (mem_kSieveIndex_iff e).mp he
    by_cases hcol : IsCollisionPair d e
    · obtain ⟨i, j, hij, hnc⟩ := id hcol
      have hzero : congCountTupleW k K₀ N ν₀ W' d e = 0 :=
        congCountTupleW_collision k K₀ N ν₀ W' D d e hDle hlt
          hmemd.2.2.1 hmeme.2.2.1 hij hnc
      rw [if_pos hcol, hzero]
      simp only [Nat.cast_zero, mul_zero]
      positivity
    · rw [if_neg hcol]
      have hcompat : ∀ a b, a ≠ b → Nat.Coprime (d a) (e b) := by
        intro a b hab; by_contra h; exact hcol ⟨a, b, hab, h⟩
      have hlcmpos : ∀ i, 0 < Nat.lcm (d i) (e i) := fun i =>
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdpos i).ne' (hepos i).ne')
      have hcopW : ∀ i, Nat.Coprime W' (Nat.lcm (d i) (e i)) := by
        intro i
        have hld : Nat.lcm (d i) (e i) ∣ d i * e i :=
          Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
        exact Nat.Coprime.coprime_dvd_right hld
          ((hmemd.2.2.1 i).symm.mul_right (hmeme.2.2.1 i).symm)
      have hcoplcm : ∀ i j, i ≠ j →
          Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) := by
        intro i j hij
        have hcop_prod : Nat.Coprime (d i * e i) (d j * e j) := by
          apply Nat.Coprime.mul_left
          · exact (hmemd.2.1 i j hij).mul_right (hcompat i j hij)
          · exact (hcompat j i (Ne.symm hij)).symm.mul_right (hmeme.2.1 i j hij)
        have hld : Nat.lcm (d i) (e i) ∣ d i * e i :=
          Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
        have hle : Nat.lcm (d j) (e j) ∣ d j * e j :=
          Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
        exact (hcop_prod.coprime_dvd_left hld).coprime_dvd_right hle
      have happrox := congCountTupleW_approx k K₀ N ν₀ W' d e hW' hK₀ hlcmpos hcopW hcoplcm
        (hsol d hd e he hcol)
      have hcast : ((W' * ∏ i, Nat.lcm (d i) (e i) : ℕ) : ℝ)
          = (W' : ℝ) * ∏ i, (Nat.lcm (d i) (e i) : ℝ) := by push_cast; ring
      rw [hcast] at happrox
      have hmaineq : ((K₀ - 1) * N / W' : ℝ) * s1Summand k R W' y d e
          = lam k R W' y d * lam k R W' y e
              * (((K₀ - 1) * N : ℝ) / ((W' : ℝ) * ∏ i, (Nat.lcm (d i) (e i) : ℝ))) := by
        unfold s1Summand
        ring
      rw [hmaineq]
      set CT : ℝ := (congCountTupleW k K₀ N ν₀ W' d e : ℝ) with hCT
      set main : ℝ := ((K₀ - 1) * N : ℝ) / ((W' : ℝ) * ∏ i, (Nat.lcm (d i) (e i) : ℝ))
        with hmain
      have hdisc : lam k R W' y d * lam k R W' y e * (CT - main)
          ≤ |lam k R W' y d| * |lam k R W' y e| * 2 ^ (k + 1) := by
        calc lam k R W' y d * lam k R W' y e * (CT - main)
            ≤ |lam k R W' y d * lam k R W' y e * (CT - main)| := le_abs_self _
          _ = |lam k R W' y d| * |lam k R W' y e| * |CT - main| := by
              rw [abs_mul, abs_mul]
          _ ≤ |lam k R W' y d| * |lam k R W' y e| * 2 ^ (k + 1) :=
              mul_le_mul_of_nonneg_left happrox
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hexp : lam k R W' y d * lam k R W' y e * (CT - main)
          = lam k R W' y d * lam k R W' y e * CT
            - lam k R W' y d * lam k R W' y e * main := by ring
      nlinarith [hdisc, hexp]
  refine (Finset.sum_le_sum (fun d hd =>
    Finset.sum_le_sum (fun e he => hterm d hd e he))).trans ?_
  rw [Finset.sum_congr rfl (fun d _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  apply add_le_add
  · apply le_of_eq
    unfold s1CompatForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e _
    split_ifs <;> ring
  · apply le_of_eq
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]

/-- Free-modulus form of `S1_le` (no `hW`). -/
theorem S1_leW (k K₀ N R W' ν₀ D : ℕ) (y : (Fin k → ℕ) → ℝ) (f₀ : ℕ → ℝ)
    (hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin k, hSeq k i < D)
    (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) (hK₀ : 1 ≤ K₀)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by
  have hL2 := S1_le_main_add_errorW k K₀ N R W' ν₀ D y hW' hK₀ hDlt hlt hsol
  have hcompat := compat_le_two_ysideW k R W' D y f₀ hf01 hfmono hy hDlt hk hDk
  have hcoeff_nonneg : (0 : ℝ) ≤ ((K₀ - 1) * N / W' : ℝ) := by
    have h1 : (0 : ℝ) ≤ (K₀ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
      linarith
    exact div_nonneg (mul_nonneg h1 (by positivity)) (by positivity)
  calc S1 k K₀ N R W' ν₀ y
      ≤ ((K₀ - 1) * N / W' : ℝ) * s1CompatForm k R W' y
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := hL2
    _ ≤ ((K₀ - 1) * N / W' : ℝ)
          * (2 * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hcompat hcoeff_nonneg) (le_refl _)
    _ = 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := by ring

/-- Free-modulus form of `S1_upper` (no `hW`). -/
theorem S1_upperW (k K₀ N R W' ν₀ D : ℕ) (y : (Fin k → ℕ) → ℝ) (f₀ : ℕ → ℝ)
    (hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin k, hSeq k i < D)
    (hk : 1 ≤ k) (hDk : 12 * k ^ 2 ≤ D) (hK₀ : 1 ≤ K₀)
    (hR : 2 ≤ R)
    (hsol : ∀ d ∈ kSieveIndex k R W', ∀ e ∈ kSieveIndex k R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq k i)) :
    ∃ C : ℝ, 0 ≤ C ∧ S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + C * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by
  have hy1 : ∀ r, |y r| ≤ 1 := by
    intro r
    rw [hy r]
    split_ifs with h
    · rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hf01 _).1))]
      calc ∏ i, f₀ (r i) ≤ ∏ _i : Fin k, (1 : ℝ) :=
            Finset.prod_le_prod (fun i _ => (hf01 _).1) (fun i _ => (hf01 _).2)
        _ = 1 := by simp
    · simp
  have hW0 : W' ≠ 0 := hW'.ne_zero
  obtain ⟨C0, hC0, hC0le⟩ := S1_trivial_error_le' k R W' y hy1 hR hW0
  have hL3 := S1_leW k K₀ N R W' ν₀ D y f₀ hf01 hfmono hy hW' hDlt hlt hk hDk hK₀ hsol
  refine ⟨2 ^ (k + 1) * C0, by positivity, ?_⟩
  calc S1 k K₀ N R W' ν₀ y
      ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (∑ d ∈ kSieveIndex k R W', |lam k R W' y d|) ^ 2 := hL3
    _ ≤ 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (k + 1) * (C0 * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2)) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hC0le (by positivity))
    _ = 2 * ((K₀ - 1) * N / W' : ℝ)
          * (∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
        + (2 ^ (k + 1) * C0) * (R : ℝ) ^ 2 * (1 + Real.log R) ^ (4 * k + 2) := by ring

end Salt.Maynard
