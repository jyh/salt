/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# B2 W3 — Jutila's pseudocharacters (L1)

`f_r(n) = f(gcd(r, n))` for a multiplicative `f` and a square-free level `r` (Jutila 1977, (1.2)
p.45), the two multiplicativities (in `n` on coprime pairs; in `r` on coprime levels), the
detection-identity input `f_r(dn) = f_r(d)·f_{r/(r,d)}(n)` (p.48 — the gcd identity holds for
EVERY `r`; square-freeness is what makes `f` split), and Selberg's instance `ψ = μ·φ` with
`ψ_r(p) = 1 − p` on `p ∣ r`. The non-square-free failure `ψ_4(4) = 0 ≠ ψ_4(2)·ψ_2(2) = 1` is
recorded as a `≠` row.

## The honest label

Every row here is an INPUT to Jutila's Lemma 6, which is NOT in this file: nothing below bears
on twin primes or on the crown's conditions. The coefficients are ℝ-valued (`pseudoChar`,
`selbergPsi`) and cast to ℂ once at the point of use, in `PseudoCharEuler.lean` — the corpus's
idiom. No von Mangoldt detour is formed anywhere: only `moebius` and `totient` values enter.

## The measured receipts behind these statements

The gcd identity `gcd(r, dn) = gcd(r, d)·gcd(r/(r,d), n)` was checked exhaustively over
`(r, d, n) ∈ [0,60]³` under Lean's zero conventions: 0 failures / 226,981 — it needs NO
square-freeness (`gcd_mul_eq_gcd_mul_gcd_div` carries no hypothesis). The `f`-split
`ψ_r(dn) = ψ_r(d)·ψ_{r/(r,d)}(n)` over `r ∈ [1,60]`, `d, n ∈ [1,40]`: 0 failures on square-free
`r`, 2,980 on non-square-free `r`, the first at `(r, d, n) = (4, 2, 2)` — that first failure is
the `≠` row `pseudoChar_selbergPsi_four_two_two` at the end of this file, so the hypothesis
`Squarefree r` on `pseudoChar_mul_of_squarefree` is recorded as load-bearing IN LEAN, not only
in prose. Also measured: `ψ_6(6) = 2 = ψ_6(2)·ψ_3(3)` (the exit row below), `ψ_30(5) = −4`,
`max |ψ_r(n)|/r = 1.000` over `r ≤ 60`, `n ≤ 200` (the sharpness of `abs_pseudoChar_selbergPsi_le`).
-/

open ArithmeticFunction

noncomputable section
namespace Salt.SW

/-- Jutila's pseudocharacter (1.2), p.45: `f_r(n) = f(gcd(r, n))`. -/
def pseudoChar (f : ArithmeticFunction ℝ) (r n : ℕ) : ℝ := f (Nat.gcd r n)

variable {f : ArithmeticFunction ℝ}

theorem pseudoChar_one_right (hf : f.IsMultiplicative) (r : ℕ) : pseudoChar f r 1 = 1 := by
  simp only [pseudoChar, Nat.gcd_one_right, hf.map_one]

theorem pseudoChar_one_left (hf : f.IsMultiplicative) (n : ℕ) : pseudoChar f 1 n = 1 := by
  simp only [pseudoChar, Nat.gcd_one_left, hf.map_one]

theorem pseudoChar_of_coprime (hf : f.IsMultiplicative) {r n : ℕ} (h : Nat.Coprime r n) :
    pseudoChar f r n = 1 := by
  simp only [pseudoChar, h.gcd_eq_one, hf.map_one]

theorem pseudoChar_mul_right_of_coprime (hf : f.IsMultiplicative) (r : ℕ) {m n : ℕ}
    (h : Nat.Coprime m n) : pseudoChar f r (m * n) = pseudoChar f r m * pseudoChar f r n := by
  have hcop : Nat.Coprime (Nat.gcd r m) (Nat.gcd r n) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right r m)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right r n) h)
  simp only [pseudoChar, Nat.Coprime.gcd_mul r h, hf.map_mul_of_coprime hcop]

theorem gcd_mul_eq_gcd_mul_gcd_div (r d n : ℕ) :
    Nat.gcd r (d * n) = Nat.gcd r d * Nat.gcd (r / Nat.gcd r d) n := by
  rcases Nat.eq_zero_or_pos (Nat.gcd r d) with hg | hg
  · have hr : r = 0 := Nat.eq_zero_of_gcd_eq_zero_left hg
    have hd : d = 0 := Nat.eq_zero_of_gcd_eq_zero_right hg
    subst hr; subst hd; simp
  · have hcop : Nat.Coprime (d / Nat.gcd r d) (r / Nat.gcd r d) :=
      (Nat.coprime_div_gcd_div_gcd hg).symm
    have hr : Nat.gcd r d * (r / Nat.gcd r d) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r d)
    have hd : Nat.gcd r d * (d / Nat.gcd r d) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right r d)
    calc Nat.gcd r (d * n)
        = Nat.gcd (Nat.gcd r d * (r / Nat.gcd r d))
            (Nat.gcd r d * (d / Nat.gcd r d * n)) := by rw [hr, ← Nat.mul_assoc, hd]
      _ = Nat.gcd r d * Nat.gcd (r / Nat.gcd r d) (d / Nat.gcd r d * n) :=
            Nat.gcd_mul_left _ _ _
      _ = Nat.gcd r d * Nat.gcd (r / Nat.gcd r d) n := by
            rw [Nat.Coprime.gcd_mul_left_cancel_right n hcop]

theorem pseudoChar_mul_of_squarefree (hf : f.IsMultiplicative) {r : ℕ} (hr : Squarefree r)
    (d n : ℕ) :
    pseudoChar f r (d * n) = pseudoChar f r d * pseudoChar f (r / Nat.gcd r d) n := by
  have hsplit : Nat.gcd r d * (r / Nat.gcd r d) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_left r d)
  have hsq : Squarefree (Nat.gcd r d * (r / Nat.gcd r d)) := by rw [hsplit]; exact hr
  have hc : Nat.Coprime (Nat.gcd r d) (r / Nat.gcd r d) := (Nat.squarefree_mul_iff.mp hsq).1
  have hcop : Nat.Coprime (Nat.gcd r d) (Nat.gcd (r / Nat.gcd r d) n) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left (r / Nat.gcd r d) n) hc
  simp only [pseudoChar, gcd_mul_eq_gcd_mul_gcd_div r d n, hf.map_mul_of_coprime hcop]

theorem pseudoChar_mul_left_of_coprime (hf : f.IsMultiplicative) {r₁ r₂ : ℕ}
    (h : Nat.Coprime r₁ r₂) (n : ℕ) :
    pseudoChar f (r₁ * r₂) n = pseudoChar f r₁ n * pseudoChar f r₂ n := by
  have hg : Nat.gcd (r₁ * r₂) n = Nat.gcd r₁ n * Nat.gcd r₂ n := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul n h, Nat.gcd_comm n r₁, Nat.gcd_comm n r₂]
  have hcop : Nat.Coprime (Nat.gcd r₁ n) (Nat.gcd r₂ n) :=
    Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left r₁ n)
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left r₂ n) h)
  simp only [pseudoChar, hg, hf.map_mul_of_coprime hcop]

theorem pseudoChar_prime_left (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    pseudoChar f p n = if p ∣ n then f p else 1 := by
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    simp only [pseudoChar, Nat.gcd_eq_left hpn]
  · rw [if_neg hpn]
    simp only [pseudoChar,
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn), hf.map_one]

theorem abs_pseudoChar_le_sum_divisors {r : ℕ} (hr : r ≠ 0) (n : ℕ) :
    |pseudoChar f r n| ≤ ∑ e ∈ r.divisors, |f e| := by
  simp only [pseudoChar]
  exact Finset.single_le_sum (f := fun e => |f e|) (fun e _ => abs_nonneg (f e))
    (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left r n, hr⟩)

/-- Selberg's `ψ = μ·φ` (p.45; the `f` of Theorem 1, of Lemma 3 and of Lemma 6). -/
def selbergPsi : ArithmeticFunction ℝ :=
  ⟨fun n => (moebius n : ℝ) * (Nat.totient n : ℝ), by simp⟩

theorem selbergPsi_apply (n : ℕ) : selbergPsi n = (moebius n : ℝ) * (Nat.totient n : ℝ) := by
  rfl

theorem selbergPsi_isMultiplicative : selbergPsi.IsMultiplicative := by
  refine ⟨by simp [selbergPsi_apply], fun {m n} h => ?_⟩
  simp only [selbergPsi_apply]
  rw [isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  ring

theorem selbergPsi_apply_prime {p : ℕ} (hp : p.Prime) : selbergPsi p = 1 - (p : ℝ) := by
  rw [selbergPsi_apply, moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le]
  push_cast
  ring

theorem abs_selbergPsi_le (n : ℕ) : |selbergPsi n| ≤ (n : ℝ) := by
  have h1 : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one (n := n)
  have h2 : (0 : ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  have h3 : (Nat.totient n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.totient_le n
  rw [selbergPsi_apply, abs_mul, abs_of_nonneg h2]
  nlinarith [abs_nonneg ((moebius n : ℤ) : ℝ)]

theorem abs_pseudoChar_selbergPsi_le (r n : ℕ) :
    |pseudoChar selbergPsi r n| ≤ (Nat.gcd r n : ℝ) := by
  simpa only [pseudoChar] using abs_selbergPsi_le (Nat.gcd r n)

theorem pseudoChar_selbergPsi_prime_of_dvd {r p : ℕ} (hp : p.Prime) (hpr : p ∣ r) :
    pseudoChar selbergPsi r p = 1 - (p : ℝ) := by
  simp only [pseudoChar, Nat.gcd_eq_right hpr]
  exact selbergPsi_apply_prime hp

theorem pseudoChar_selbergPsi_four_two_two :
    pseudoChar selbergPsi 4 (2 * 2)
      ≠ pseudoChar selbergPsi 4 2 * pseudoChar selbergPsi (4 / Nat.gcd 4 2) 2 := by
  have hnsf : ¬ Squarefree (4 : ℕ) := by
    intro h
    have h2 := h 2 (by decide)
    rw [Nat.isUnit_iff] at h2
    norm_num at h2
  have hL : pseudoChar selbergPsi 4 (2 * 2) = 0 := by
    have e0 : Nat.gcd 4 (2 * 2) = 4 := by norm_num
    simp only [pseudoChar, e0]
    rw [selbergPsi_apply, moebius_eq_zero_of_not_squarefree hnsf]
    norm_num
  have hp2 : pseudoChar selbergPsi 4 2 = -1 := by
    rw [pseudoChar_selbergPsi_prime_of_dvd Nat.prime_two (by norm_num : (2 : ℕ) ∣ 4)]
    norm_num
  have hq2 : pseudoChar selbergPsi (4 / Nat.gcd 4 2) 2 = -1 := by
    have e1 : 4 / Nat.gcd 4 2 = 2 := by norm_num
    rw [e1, pseudoChar_selbergPsi_prime_of_dvd Nat.prime_two (dvd_refl 2)]
    norm_num
  rw [hL, hp2, hq2]
  norm_num

/-- **The W3 exit row** (measured: both sides are `ψ_6(6) = 2 = ψ_6(2)·ψ_3(3)`). It INVOKES
`pseudoChar_mul_of_squarefree`; `Squarefree 6` goes through `Nat.squarefree_mul_iff`, since the
`DecidablePred (Squarefree ·)` instance runs through the well-founded `Nat.minSqFac` and the
kernel cannot reduce it (`by decide : Squarefree 6` does NOT close). -/
example : pseudoChar selbergPsi 6 (2 * 3)
    = pseudoChar selbergPsi 6 2 * pseudoChar selbergPsi (6 / Nat.gcd 6 2) 3 :=
  pseudoChar_mul_of_squarefree selbergPsi_isMultiplicative
    (by rw [show (6 : ℕ) = 2 * 3 from rfl]
        exact Nat.squarefree_mul_iff.mpr
          ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩) 2 3

end Salt.SW
