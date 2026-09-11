/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.CrownAssembly
import Salt.HB.Lemma10Chain
import Salt.Weil.RoadModulus
import Salt.Weil.Sawtooth

/-!
# HB 1983 §5 — the bilinear carrier, the dyadic/residue split, the CRT collapse, the ψ-reduction

Heath-Brown, *Prime twins and Siegel zeros* (Proc. LMS (3) 47 (1983) 193–224), §5, pp.210–214.
This is **Wave B of the N7 program**: the §5 lattice machine at HB's general pair of linear
forms, stated against the corpus and proved here.

What the file holds, block by block.

* **B-1 — the forms, the window, the carrier.** `HBForms` is HB's pair `l_i(n) = α_i n + β_i`
  (pp.193–194) carrying (1.4)–(1.9) as fields, with `β_i : ℕ` (no generality is lost: the
  shift `n ↦ n + t` carries any ℤ-β pair to an ℕ-β pair with the same `α_i` and determinant,
  and ℕ buys `1 ≤ l_i(n)` unconditionally, which every `Nat.divisors` sum in §5 needs).
  `HBForms.twin` is the twin-prime instance `(4n+1, 4n+3)` of p.195.  `truncChiSum`,
  `hbFormsWindow` and `bilinearS` are p.211's `S(δ₁,δ₂;V₁,V₂)`; the (5.1) vanishing clauses,
  the `V`-vanishing of p.218 and the `HBSieveData` transfer `hbDataForms` sit here too.
* **B-3 — the dyadic cells and the residue split.** `cellCount` is (5.3)'s `S`: the lattice
  count at one dyadic cell `(R_i, 2R_i] × (S_i, 2S_i]` in one residue class `(a_i, b_i)`.
  (5.18) decomposes the carrier into those cells exactly; (5.2) bounds a non-empty cell.
* **B-4 — the CRT collapse (5.5)–(5.13).** The four congruences in `X = v₂w₂` are ONE
  congruence modulo `D δ₁ w₁`, `D = roadModulus α₂ q`, with a residue coprime to the modulus;
  and the cells that carry no mass at all are named.
* **B-5 — the ψ-reduction (5.14)–(5.17).** `hbT₁`/`hbT₂` are (5.15)/(5.16); the `v₂`-count in
  an interval and a residue class is a length plus two sawtooths (`Salt.Weil.sawtooth`), and
  the assembled cell count is the double `(w₁, w₂)`-sum B-6 consumes.

Lemma 9 itself (the μ-sieve of `Λ′` over `Q`, the hyperbola identity, the log integrals) is the
sibling branch of this wave and lands in this same file afterwards; §6 (applying Lemma 10) is a
later wave and owes the `Salt.HB.Lemma10Seal` import, which is deliberately NOT taken here.

Nothing in this file bears on twin primes: §5 is a binder on a binder on the crown.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.N7

open Salt.HB Salt.Weil Salt.TwinBar

variable {q : ℕ}

/-! ## B-1 — the forms, the window, the carrier -/

/-- HB's pair of linear forms `l_i(n) = α_i n + β_i` (pp.193–194) under (1.4)–(1.9), `β_i ∈ ℕ`. -/
structure HBForms where
  α₁ : ℕ
  β₁ : ℕ
  α₂ : ℕ
  β₂ : ℕ
  /-- (1.4) -/
  cop₁ : Nat.Coprime α₁ β₁
  cop₂ : Nat.Coprime α₂ β₂
  /-- (1.5) -/
  even₁ : 2 ∣ α₁
  even₂ : 2 ∣ α₂
  /-- (1.6) -/
  det_ne : α₁ * β₂ ≠ α₂ * β₁
  /-- (1.7) -/
  det_dvd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ((α₁ : ℤ) * β₂ - (α₂ : ℤ) * β₁) → p ∣ α₁ ∧ p ∣ α₂
  /-- (1.8) -/
  same_primes : ∀ p : ℕ, p.Prime → (p ∣ α₁ ↔ p ∣ α₂)
  /-- (1.9) -/
  sq_dvd₁ : ∀ p : ℕ, p.Prime → p ∣ α₁ → p ^ 2 ∣ α₁
  sq_dvd₂ : ∀ p : ℕ, p.Prime → p ∣ α₂ → p ^ 2 ∣ α₂

namespace HBForms

def l₁ (F : HBForms) (n : ℕ) : ℕ := F.α₁ * n + F.β₁
def l₂ (F : HBForms) (n : ℕ) : ℕ := F.α₂ * n + F.β₂
/-- HB's `α = (α₁, α₂)`. -/
def α (F : HBForms) : ℕ := Nat.gcd F.α₁ F.α₂

/-- `α₁ ≠ 0`: if it were, (1.8) would force `α₂ = 0` (every prime divides `0`, and primes are
unbounded), and (1.6) would read `0 ≠ 0`. -/
theorem alpha₁_ne_zero (F : HBForms) : F.α₁ ≠ 0 := by
  intro h
  have h2 : F.α₂ = 0 := by
    by_contra hne
    have hpos : 0 < F.α₂ := Nat.pos_of_ne_zero hne
    obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (F.α₂ + 1)
    have hpd1 : p ∣ F.α₁ := by rw [h]; exact dvd_zero p
    have hpd : p ∣ F.α₂ := (F.same_primes p hp).mp hpd1
    have := Nat.le_of_dvd hpos hpd
    omega
  exact F.det_ne (by simp [h, h2])

/-- `α₂ ≠ 0`, the mirror. -/
theorem alpha₂_ne_zero (F : HBForms) : F.α₂ ≠ 0 := by
  intro h
  have h2 : F.α₁ = 0 := by
    by_contra hne
    have hpos : 0 < F.α₁ := Nat.pos_of_ne_zero hne
    obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (F.α₁ + 1)
    have hpd2 : p ∣ F.α₂ := by rw [h]; exact dvd_zero p
    have hpd : p ∣ F.α₁ := (F.same_primes p hp).mpr hpd2
    have := Nat.le_of_dvd hpos hpd
    omega
  exact F.det_ne (by simp [h, h2])

/-- (1.5)+(1.6)+(1.8): `α₁` is a nonzero even number. -/
theorem two_le_α₁ (F : HBForms) : 2 ≤ F.α₁ :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (alpha₁_ne_zero F)) F.even₁

theorem two_le_α₂ (F : HBForms) : 2 ≤ F.α₂ :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (alpha₂_ne_zero F)) F.even₂

/-- (1.4)+(1.5): `β₁ = 0` would make `(α₁, β₁) = α₁ = 1`, against `2 ∣ α₁`. -/
theorem one_le_β₁ (F : HBForms) : 1 ≤ F.β₁ := by
  rcases Nat.eq_zero_or_pos F.β₁ with h | h
  · exfalso
    have h1 : F.α₁ = 1 := by
      have hc := F.cop₁
      rw [Nat.Coprime, h, Nat.gcd_zero_right] at hc
      exact hc
    have h2 := F.even₁
    rw [h1] at h2
    omega
  · exact h

theorem one_le_β₂ (F : HBForms) : 1 ≤ F.β₂ := by
  rcases Nat.eq_zero_or_pos F.β₂ with h | h
  · exfalso
    have h1 : F.α₂ = 1 := by
      have hc := F.cop₂
      rw [Nat.Coprime, h, Nat.gcd_zero_right] at hc
      exact hc
    have h2 := F.even₂
    rw [h1] at h2
    omega
  · exact h

/-- What `β_i : ℕ` buys: `1 ≤ l_i(n)` for EVERY `n`, with no side condition — so every
`Nat.divisors` and `divisorsAntidiagonal` of `l_i(n)` below is a sum over a non-degenerate
index (`Nat.divisors 0 = ∅`). -/
theorem one_le_l₁ (F : HBForms) (n : ℕ) : 1 ≤ F.l₁ n := by
  have := one_le_β₁ F
  simp only [l₁]
  omega

theorem one_le_l₂ (F : HBForms) (n : ℕ) : 1 ≤ F.l₂ n := by
  have := one_le_β₂ F
  simp only [l₂]
  omega

/-- (1.4)+(1.5): `β_i` is odd, since `2 ∣ α_i` and `(α_i, β_i) = 1`. -/
theorem odd_β₁ (F : HBForms) : Odd F.β₁ := by
  rcases Nat.even_or_odd F.β₁ with he | ho
  · exfalso
    have hg : Nat.gcd F.α₁ F.β₁ = 1 := F.cop₁
    have h2 : (2 : ℕ) ∣ Nat.gcd F.α₁ F.β₁ := Nat.dvd_gcd F.even₁ he.two_dvd
    rw [hg] at h2
    omega
  · exact ho

theorem odd_β₂ (F : HBForms) : Odd F.β₂ := by
  rcases Nat.even_or_odd F.β₂ with he | ho
  · exfalso
    have hg : Nat.gcd F.α₂ F.β₂ = 1 := F.cop₂
    have h2 : (2 : ℕ) ∣ Nat.gcd F.α₂ F.β₂ := Nat.dvd_gcd F.even₂ he.two_dvd
    rw [hg] at h2
    omega
  · exact ho

/-- HB p.194: (1.4)+(1.5) make `l_i(n)` odd — an even `α_i` plus an odd `β_i`. -/
theorem odd_l₁ (F : HBForms) (n : ℕ) : Odd (F.l₁ n) := by
  obtain ⟨k, hk⟩ := F.even₁
  obtain ⟨m, hm⟩ := odd_β₁ F
  refine ⟨k * n + m, ?_⟩
  simp only [l₁]
  rw [hk, hm]; ring

theorem odd_l₂ (F : HBForms) (n : ℕ) : Odd (F.l₂ n) := by
  obtain ⟨k, hk⟩ := F.even₂
  obtain ⟨m, hm⟩ := odd_β₂ F
  refine ⟨k * n + m, ?_⟩
  simp only [l₂]
  rw [hk, hm]; ring

/-- `l_i(n) ≡ β_i (mod α_i)`, so (1.4) transfers: `(l_i(n), α_i) = 1`. -/
theorem coprime_l₁_α₁ (F : HBForms) (n : ℕ) : Nat.Coprime (F.l₁ n) F.α₁ := by
  have he : F.l₁ n = F.β₁ + F.α₁ * n := by simp only [l₁]; ring
  rw [he]
  exact (Nat.coprime_add_mul_left_left F.β₁ F.α₁ n).mpr F.cop₁.symm

theorem coprime_l₂_α₂ (F : HBForms) (n : ℕ) : Nat.Coprime (F.l₂ n) F.α₂ := by
  have he : F.l₂ n = F.β₂ + F.α₂ * n := by simp only [l₂]; ring
  rw [he]
  exact (Nat.coprime_add_mul_left_left F.β₂ F.α₂ n).mpr F.cop₂.symm

/-- `l_i` is monotone: B-1.8 needs `l_i(n) ≤ l_i(2x)` on the window. -/
theorem l₁_mono (F : HBForms) {m n : ℕ} (h : m ≤ n) : F.l₁ m ≤ F.l₁ n := by
  simp only [l₁]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

theorem l₂_mono (F : HBForms) {m n : ℕ} (h : m ≤ n) : F.l₂ m ≤ F.l₂ n := by
  simp only [l₂]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

/-- **B-1.3 — `(l₁(n), l₂(n)) = 1`** (HB p.194).  A common prime `p` divides
`α₁ l₂(n) − α₂ l₁(n) = α₁β₂ − α₂β₁`, so (1.7) gives `p ∣ α₁`, and then `p ∣ β₁` against (1.4).
⛔ This consumes (1.4) and (1.7) ONLY: `even₁`/`even₂` are never invoked, so the argument is
uniform in `p` and `p = 2` is not a case.  ((1.5) is spent on the ODDNESS half of p.194's
sentence, `odd_l₁`/`odd_l₂` above.) -/
theorem coprime_l (F : HBForms) (n : ℕ) : Nat.Coprime (F.l₁ n) (F.l₂ n) := by
  by_contra hc
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hz1 : (p : ℤ) ∣ (F.α₁ : ℤ) * (F.l₂ n : ℕ) := Dvd.dvd.mul_left
    (Int.natCast_dvd_natCast.mpr hp2) _
  have hz2 : (p : ℤ) ∣ (F.α₂ : ℤ) * (F.l₁ n : ℕ) := Dvd.dvd.mul_left
    (Int.natCast_dvd_natCast.mpr hp1) _
  have heq : (F.α₁ : ℤ) * ((F.l₂ n : ℕ) : ℤ) - (F.α₂ : ℤ) * ((F.l₁ n : ℕ) : ℤ)
      = (F.α₁ : ℤ) * F.β₂ - (F.α₂ : ℤ) * F.β₁ := by
    simp only [l₁, l₂]
    push_cast; ring
  have hdet : (p : ℤ) ∣ (F.α₁ : ℤ) * F.β₂ - (F.α₂ : ℤ) * F.β₁ := by
    rw [← heq]; exact dvd_sub hz1 hz2
  obtain ⟨hd1, _hd2⟩ := F.det_dvd p hp hdet
  have hl1 : p ∣ F.α₁ * n + F.β₁ := hp1
  have hb1 : p ∣ F.β₁ := (Nat.dvd_add_right (Dvd.dvd.mul_right hd1 n)).mp hl1
  have hg : p ∣ Nat.gcd F.α₁ F.β₁ := Nat.dvd_gcd hd1 hb1
  rw [show Nat.gcd F.α₁ F.β₁ = 1 from F.cop₁] at hg
  exact hp.one_lt.ne' (Nat.dvd_one.mp hg)


/-- **B-1.9 — the (1.8) radical transfer**: coprime to `α = (α₁, α₂)` ⇒ coprime to each `α_i`
(`same_primes`); FALSE without (1.8), e.g. `d = 4`, `α₁ = 4`, `α₂ = 3`. B-4 spends it five times. -/
theorem coprime_α_iff (F : HBForms) (d : ℕ) :
    Nat.Coprime d F.α ↔ Nat.Coprime d F.α₁ ∧ Nat.Coprime d F.α₂ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc
      obtain ⟨p, hp, hpd, hp1⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      have hp2 : p ∣ F.α₂ := (F.same_primes p hp).mp hp1
      have hpα : p ∣ F.α := Nat.dvd_gcd hp1 hp2
      have hg : p ∣ Nat.gcd d F.α := Nat.dvd_gcd hpd hpα
      rw [show Nat.gcd d F.α = 1 from h] at hg
      exact hp.one_lt.ne' (Nat.dvd_one.mp hg)
    · by_contra hc
      obtain ⟨p, hp, hpd, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      have hp1 : p ∣ F.α₁ := (F.same_primes p hp).mpr hp2
      have hpα : p ∣ F.α := Nat.dvd_gcd hp1 hp2
      have hg : p ∣ Nat.gcd d F.α := Nat.dvd_gcd hpd hpα
      rw [show Nat.gcd d F.α = 1 from h] at hg
      exact hp.one_lt.ne' (Nat.dvd_one.mp hg)
  · intro h
    exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left F.α₁ F.α₂) h.1

/-- The twin-prime instance `(4n+1, 4n+3)` (p.195): the forms W-a's `hbDataHB` uses. -/
def twin : HBForms where
  α₁ := 4
  β₁ := 1
  α₂ := 4
  β₂ := 3
  cop₁ := by decide
  cop₂ := by decide
  even₁ := by decide
  even₂ := by decide
  det_ne := by decide
  det_dvd := by
    intro p hp hdvd
    have h8 : p ∣ 8 := by
      have : (p : ℤ) ∣ (8 : ℤ) := by norm_num at hdvd ⊢; exact hdvd
      exact_mod_cast this
    have h2 : p = 2 := by
      have : p ∣ 2 ^ 3 := by norm_num; exact h8
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst h2; decide
  same_primes := fun _ _ => Iff.rfl
  sq_dvd₁ := by
    intro p hp hdvd
    have h2 : p = 2 := by
      have : p ∣ 2 ^ 2 := by norm_num; exact hdvd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst h2; decide
  sq_dvd₂ := by
    intro p hp hdvd
    have h2 : p = 2 := by
      have : p ∣ 2 ^ 2 := by norm_num; exact hdvd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst h2; decide

theorem twin_l₁ (n : ℕ) : twin.l₁ n = 4 * n + 1 := rfl
theorem twin_l₂ (n : ℕ) : twin.l₂ n = 4 * n + 3 := rfl
theorem twin_gcd_eq (q : ℕ) : Nat.gcd twin.α₁ q = Nat.gcd twin.α₂ q := rfl

end HBForms

/-- `Σ_{w v = N, v > V} χ(w)` (p.211): the inner truncated divisor sum of `S(δ₁,δ₂;V₁,V₂)`;
`p = (w, v)` runs over `N.divisorsAntidiagonal`. -/
noncomputable def truncChiSum (χ : DirichletCharacter ℂ q) (N : ℕ) (V : ℝ) : ℝ :=
  ∑ p ∈ N.divisorsAntidiagonal, if V < (p.2 : ℝ) then chiRe χ p.1 else 0

/-- HB's window `x < n ≤ 2x`, `(l, q) = 1` at the forms `F` (p.198). -/
noncomputable def hbFormsWindow (F : HBForms) (q x : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => Nat.Coprime (F.l₁ n * F.l₂ n) q)

/-- HB's `S(δ₁,δ₂;V₁,V₂)` (p.211). -/
noncomputable def bilinearS (χ : DirichletCharacter ℂ q) (F : HBForms) (x δ₁ δ₂ : ℕ)
    (V₁ V₂ : ℝ) : ℝ :=
  ∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
    truncChiSum χ (F.l₁ n / δ₁) V₁ * truncChiSum χ (F.l₂ n / δ₂) V₂

/-- (5.1), first clause: `S(δ₁,δ₂;V₁,V₂) = 0` unless `(δ₁, q) = 1`. -/
theorem bilinearS_eq_zero_of_not_coprime_q₁ (χ : DirichletCharacter ℂ q) (F : HBForms)
    (x δ₁ δ₂ : ℕ) (V₁ V₂ : ℝ) (h : ¬ Nat.Coprime δ₁ q) :
    bilinearS χ F x δ₁ δ₂ V₁ V₂ = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  exfalso
  rw [Finset.mem_filter, hbFormsWindow, Finset.mem_filter] at hn
  exact h (Nat.Coprime.coprime_dvd_left (Dvd.dvd.mul_right hn.2.1 (F.l₂ n)) hn.1.2)
theorem bilinearS_eq_zero_of_not_coprime_q₂ (χ : DirichletCharacter ℂ q) (F : HBForms)
    (x δ₁ δ₂ : ℕ) (V₁ V₂ : ℝ) (h : ¬ Nat.Coprime δ₂ q) :
    bilinearS χ F x δ₁ δ₂ V₁ V₂ = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  exfalso
  rw [Finset.mem_filter, hbFormsWindow, Finset.mem_filter] at hn
  exact h (Nat.Coprime.coprime_dvd_left (Dvd.dvd.mul_left hn.2.2 (F.l₁ n)) hn.1.2)
/-- (5.1), second clause: `= 0` unless `(δ_i, α) = 1`.  ⛔ These two need NO window filter:
`δ_i ∣ l_i(n)` and `(l_i(n), α_i) = 1` already give `(δ_i, α_i) = 1`, and `α ∣ α_i`. -/
theorem bilinearS_eq_zero_of_not_coprime_α₁ (χ : DirichletCharacter ℂ q) (F : HBForms)
    (x δ₁ δ₂ : ℕ) (V₁ V₂ : ℝ) (h : ¬ Nat.Coprime δ₁ F.α) :
    bilinearS χ F x δ₁ δ₂ V₁ V₂ = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  exfalso
  rw [Finset.mem_filter] at hn
  have h₁ : Nat.Coprime δ₁ F.α₁ :=
    Nat.Coprime.coprime_dvd_left hn.2.1 (F.coprime_l₁_α₁ n)
  exact h (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left F.α₁ F.α₂) h₁)
theorem bilinearS_eq_zero_of_not_coprime_α₂ (χ : DirichletCharacter ℂ q) (F : HBForms)
    (x δ₁ δ₂ : ℕ) (V₁ V₂ : ℝ) (h : ¬ Nat.Coprime δ₂ F.α) :
    bilinearS χ F x δ₁ δ₂ V₁ V₂ = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  exfalso
  rw [Finset.mem_filter] at hn
  have h₂ : Nat.Coprime δ₂ F.α₂ :=
    Nat.Coprime.coprime_dvd_left hn.2.2 (F.coprime_l₂_α₂ n)
  exact h (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right F.α₁ F.α₂) h₂)
/-- (5.1), third clause: `= 0` unless `(δ₁, δ₂) = 1`. -/
theorem bilinearS_eq_zero_of_not_coprime_δ (χ : DirichletCharacter ℂ q) (F : HBForms)
    (x δ₁ δ₂ : ℕ) (V₁ V₂ : ℝ) (h : ¬ Nat.Coprime δ₁ δ₂) :
    bilinearS χ F x δ₁ δ₂ V₁ V₂ = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  exfalso
  rw [Finset.mem_filter] at hn
  have h₁ : Nat.Coprime δ₁ (F.l₂ n) :=
    Nat.Coprime.coprime_dvd_left hn.2.1 (F.coprime_l n)
  exact h (Nat.Coprime.coprime_dvd_right hn.2.2 h₁)

/-- **B-1.8 — the `V`-vanishing** (p.218: "the sums vanish for `V_i ≫ x`"): every `v ∣ N` has
`v ≤ N`, so `truncChiSum χ N V = 0` once `N ≤ V`; on the window `l_i(n)/δ_i ≤ l_i(2x)`. -/
theorem truncChiSum_eq_zero_of_le (χ : DirichletCharacter ℂ q) (N : ℕ) {V : ℝ}
    (h : (N : ℝ) ≤ V) : truncChiSum χ N V = 0 := by
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have hdvd : p.2 ∣ N := Dvd.intro_left p.1 hp.1
  have hle : ((p.2 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hp.2) hdvd
  exact if_neg (not_lt.mpr (le_trans hle h))
theorem bilinearS_eq_zero_of_le₁ (χ : DirichletCharacter ℂ q) (F : HBForms) (x δ₁ δ₂ : ℕ)
    {V₁ : ℝ} (V₂ : ℝ) (h : ((F.l₁ (2 * x) : ℕ) : ℝ) ≤ V₁) :
    bilinearS χ F x δ₁ δ₂ V₁ V₂ = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter, hbFormsWindow, Finset.mem_filter, Finset.mem_Ioc] at hn
  have hstep : F.l₁ n / δ₁ ≤ F.l₁ (2 * x) :=
    le_trans (Nat.div_le_self _ _) (F.l₁_mono hn.1.1.2)
  have hcast : ((F.l₁ n / δ₁ : ℕ) : ℝ) ≤ V₁ := le_trans (by exact_mod_cast hstep) h
  rw [truncChiSum_eq_zero_of_le χ _ hcast, zero_mul]
theorem bilinearS_eq_zero_of_le₂ (χ : DirichletCharacter ℂ q) (F : HBForms) (x δ₁ δ₂ : ℕ)
    (V₁ : ℝ) {V₂ : ℝ} (h : ((F.l₂ (2 * x) : ℕ) : ℝ) ≤ V₂) :
    bilinearS χ F x δ₁ δ₂ V₁ V₂ = 0 := by
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter, hbFormsWindow, Finset.mem_filter, Finset.mem_Ioc] at hn
  have hstep : F.l₂ n / δ₂ ≤ F.l₂ (2 * x) :=
    le_trans (Nat.div_le_self _ _) (F.l₂_mono hn.1.1.2)
  have hcast : ((F.l₂ n / δ₂ : ℕ) : ℝ) ≤ V₂ := le_trans (by exact_mod_cast hstep) h
  rw [truncChiSum_eq_zero_of_le χ _ hcast, mul_zero]

/-- The `HBSieveData` at the forms `F`: HB's `S(d)` at general forms (support `hbFormsWindow`,
`val n = l₁ n · l₂ n`, `a n = Λ*(l₁ n)·Λ*(l₂ n)`); W-a's `hbDataHB` is this at `HBForms.twin`. -/
noncomputable def hbDataForms (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (F : HBForms) (x : ℕ) : HBSieveData :=
  HBSieveData.ofHbP (chiReChar χ hsq) (z := (z : ℝ)) (by exact_mod_cast hz)
    (hbFormsWindow F q x) (fun n => F.l₁ n * F.l₂ n)
    (fun n => LamStar χ z (F.l₁ n) * LamStar χ z (F.l₂ n))
    (fun n _ => mul_nonneg (LamStar_nonneg χ hsq z _) (LamStar_nonneg χ hsq z _))

/-- **B-1.7 — the transfer**: `hbDataForms`'s `S d` is literally HB's `S(d)` at the forms `F`
(true by `rfl` — the `HBSieveData.ofHbP` wire does not reshape the sum). -/
theorem hbDataForms_S (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (F : HBForms) (x d : ℕ) :
    (hbDataForms χ hsq hz F x).S d
      = ∑ n ∈ (hbFormsWindow F q x).filter (fun n => d ∣ F.l₁ n * F.l₂ n),
          LamStar χ z (F.l₁ n) * LamStar χ z (F.l₂ n) := rfl

/-! ## B-2 — Λ′, Q, the μ-sieve, the hyperbola, the log integral, LEMMA 9 (the defs) -/

/-- `Λ′(n) = Σ_{u ∣ n} χ(u) log(n/u)` (p.210): `LamTilde` without the `μ²`. -/
noncomputable def LamPrime (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, chiRe χ d * Real.log ((n / d : ℕ) : ℝ)

/-- HB's `Q = ∏_{p < z, χ(p) = −1} p` (p.210): the `χ = −1` sibling of `hbP`. -/
noncomputable def hbQ (χ : DirichletCharacter ℂ q) (z : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p = -1), p

/-- `Σ_{w v = N} χ(w) log(c·v)` — the log-weighted twisted divisor sum Lemma 9 integrates to. -/
noncomputable def logDivChiSum (χ : DirichletCharacter ℂ q) (N : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ N.divisorsAntidiagonal, chiRe χ p.1 * Real.log (c * (p.2 : ℝ))

/-- HB's TRUNCATED `Λ*_{<q}(n) = Σ_{m ∣ Q, m² ∣ n, m < q} μ(m) Λ′(n/m²)` (p.210, the form §6
consumes at (6.11) and (6.12)); `LamStar − LamStarTrunc` is the `m ≥ q` tail. -/
noncomputable def LamStarTrunc (χ : DirichletCharacter ℂ q) (z n : ℕ) : ℝ :=
  ∑ m ∈ (hbQ χ z).divisors.filter (fun m => m ^ 2 ∣ n ∧ m < q), (μ m : ℝ) * LamPrime χ (n / m ^ 2)

/-! ## B-3 — the dyadic cells, the residue split (5.2)–(5.4), (5.18) -/

/-- HB's `S` of (5.3): the lattice count at one dyadic cell `(R_i, 2R_i] × (S_i, 2S_i]` and one
residue class `(a_i, b_i)`; `p = (w, v)` with `w v = l_i(n)/δ_i`. -/
noncomputable def cellCount (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ)
    (a₁ b₁ a₂ b₂ : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
    ((F.l₁ n / δ₁).divisorsAntidiagonal.filter (fun p =>
        R₁ < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R₁ ∧ S₁ < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * S₁ ∧
        p.2 ≡ a₁ [MOD q] ∧ p.1 ≡ b₁ [MOD q])).card *
    ((F.l₂ n / δ₂).divisorsAntidiagonal.filter (fun p =>
        R₂ < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R₂ ∧ S₂ < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * S₂ ∧
        p.2 ≡ a₂ [MOD q] ∧ p.1 ≡ b₂ [MOD q])).card

/-- **The FULL extraction from a non-empty cell.**  A non-zero `cellCount` hands back a window
point `n`, a factorisation `δ_i · (w_i · v_i) = l_i(n)` of each form value, the two dyadic
ranges, and the two residue classes.  B-3b reads the ranges off it and B-4z the residues, so it
is authored ONCE here and consumed twice. -/
theorem cellCount_ne_zero_extract (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ)
    (a₁ b₁ a₂ b₂ : ℕ) (h : cellCount F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ ≠ 0) :
    ∃ n w₁ v₁ w₂ v₂ : ℕ, x < n ∧ n ≤ 2 * x ∧
      δ₁ * (w₁ * v₁) = F.l₁ n ∧ δ₂ * (w₂ * v₂) = F.l₂ n ∧
      R₁ < (v₁ : ℝ) ∧ (v₁ : ℝ) ≤ 2 * R₁ ∧ S₁ < (w₁ : ℝ) ∧ (w₁ : ℝ) ≤ 2 * S₁ ∧
      R₂ < (v₂ : ℝ) ∧ (v₂ : ℝ) ≤ 2 * R₂ ∧ S₂ < (w₂ : ℝ) ∧ (w₂ : ℝ) ≤ 2 * S₂ ∧
      v₁ ≡ a₁ [MOD q] ∧ w₁ ≡ b₁ [MOD q] ∧ v₂ ≡ a₂ [MOD q] ∧ w₂ ≡ b₂ [MOD q] := by
  rw [cellCount] at h
  obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn
  obtain ⟨⟨hx1, hx2⟩, hd₁, hd₂⟩ := hn
  obtain ⟨hc₁, hc₂⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨p₁, hp₁⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc₁)
  obtain ⟨p₂, hp₂⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc₂)
  rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp₁ hp₂
  obtain ⟨⟨hm₁, _⟩, hA₁, hB₁, hC₁, hD₁, hE₁, hF₁⟩ := hp₁
  obtain ⟨⟨hm₂, _⟩, hA₂, hB₂, hC₂, hD₂, hE₂, hF₂⟩ := hp₂
  refine ⟨n, p₁.1, p₁.2, p₂.1, p₂.2, hx1, hx2, ?_, ?_, hA₁, hB₁, hC₁, hD₁, hA₂, hB₂, hC₂, hD₂,
    hE₁, hF₁, hE₂, hF₂⟩
  · rw [hm₁]; exact Nat.mul_div_cancel' hd₁
  · rw [hm₂]; exact Nat.mul_div_cancel' hd₂

/-- **B-3b — (5.2)'s sizes**: a non-empty cell has `α_i x < 4 δ_i R_i S_i` and
`δ_i R_i S_i ≤ l_i(2x)`.  ⭐ The dyadic ranges give `0 < R_i` and `0 < S_i` for free
(`R_i < v_i ≤ 2R_i` forces `R_i < 2R_i`), and `δ_i ≥ 1` because `δ_i ∣ l_i(n) ≥ 1`; the strict
first conjunct is real, from `n > x` and `β_i ≥ 1`. -/
theorem cellCount_ne_zero_bounds (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ)
    (a₁ b₁ a₂ b₂ : ℕ) (h : cellCount F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ ≠ 0) :
    ((F.α₁ * x : ℕ) : ℝ) < 4 * δ₁ * R₁ * S₁ ∧ (δ₁ : ℝ) * R₁ * S₁ ≤ (F.l₁ (2 * x) : ℕ) ∧
    ((F.α₂ * x : ℕ) : ℝ) < 4 * δ₂ * R₂ * S₂ ∧ (δ₂ : ℝ) * R₂ * S₂ ≤ (F.l₂ (2 * x) : ℕ) := by
  obtain ⟨n, w₁, v₁, w₂, v₂, hx1, hx2, he₁, he₂,
    hR₁, hR₁', hS₁, hS₁', hR₂, hR₂', hS₂, hS₂', _, _, _, _⟩ :=
      cellCount_ne_zero_extract F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ h
  -- the two cells are non-degenerate
  have hRp₁ : (0 : ℝ) < R₁ := by linarith
  have hSp₁ : (0 : ℝ) < S₁ := by linarith
  have hRp₂ : (0 : ℝ) < R₂ := by linarith
  have hSp₂ : (0 : ℝ) < S₂ := by linarith
  have hvp₁ : (0 : ℝ) < (v₁ : ℝ) := lt_trans hRp₁ hR₁
  have hwp₁ : (0 : ℝ) < (w₁ : ℝ) := lt_trans hSp₁ hS₁
  have hvp₂ : (0 : ℝ) < (v₂ : ℝ) := lt_trans hRp₂ hR₂
  have hwp₂ : (0 : ℝ) < (w₂ : ℝ) := lt_trans hSp₂ hS₂
  -- `δ_i ≥ 1`, since `δ_i · (w_i v_i) = l_i(n) ≥ 1`
  have hl₁ : 1 ≤ F.l₁ n := F.one_le_l₁ n
  have hl₂ : 1 ≤ F.l₂ n := F.one_le_l₂ n
  have hδp₁ : (0 : ℝ) < (δ₁ : ℝ) := by
    have : δ₁ ≠ 0 := by rintro rfl; rw [Nat.zero_mul] at he₁; omega
    exact_mod_cast Nat.pos_of_ne_zero this
  have hδp₂ : (0 : ℝ) < (δ₂ : ℝ) := by
    have : δ₂ ≠ 0 := by rintro rfl; rw [Nat.zero_mul] at he₂; omega
    exact_mod_cast Nat.pos_of_ne_zero this
  -- the cast of the factorisation, and the two comparisons with `l_i`
  have hc₁ : ((F.l₁ n : ℕ) : ℝ) = (δ₁ : ℝ) * ((w₁ : ℝ) * (v₁ : ℝ)) := by exact_mod_cast he₁.symm
  have hc₂ : ((F.l₂ n : ℕ) : ℝ) = (δ₂ : ℝ) * ((w₂ : ℝ) * (v₂ : ℝ)) := by exact_mod_cast he₂.symm
  have hlow₁ : ((F.α₁ * x : ℕ) : ℝ) < ((F.l₁ n : ℕ) : ℝ) := by
    have hnat : F.α₁ * x < F.l₁ n := by
      have hmul : F.α₁ * (x + 1) ≤ F.α₁ * n := Nat.mul_le_mul_left _ hx1
      have hβ := F.one_le_β₁
      have hα := F.two_le_α₁
      simp only [HBForms.l₁]
      nlinarith
    exact_mod_cast hnat
  have hlow₂ : ((F.α₂ * x : ℕ) : ℝ) < ((F.l₂ n : ℕ) : ℝ) := by
    have hnat : F.α₂ * x < F.l₂ n := by
      have hmul : F.α₂ * (x + 1) ≤ F.α₂ * n := Nat.mul_le_mul_left _ hx1
      have hβ := F.one_le_β₂
      have hα := F.two_le_α₂
      simp only [HBForms.l₂]
      nlinarith
    exact_mod_cast hnat
  have htop₁ : ((F.l₁ n : ℕ) : ℝ) ≤ ((F.l₁ (2 * x) : ℕ) : ℝ) := by
    exact_mod_cast F.l₁_mono hx2
  have htop₂ : ((F.l₂ n : ℕ) : ℝ) ≤ ((F.l₂ (2 * x) : ℕ) : ℝ) := by
    exact_mod_cast F.l₂_mono hx2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc₁] at hlow₁; nlinarith
  · rw [hc₁] at htop₁; nlinarith
  · rw [hc₂] at hlow₂; nlinarith
  · rw [hc₂] at htop₂; nlinarith

/-! ## B-5 — the ψ-reduction (5.14)–(5.17) -/

/-- (5.15) -/
noncomputable def hbT₁ (F : HBForms) (x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ) (w₁ w₂ : ℕ) : ℝ :=
  max R₂
    (max (((F.α₂ * x + F.β₂ : ℕ) : ℝ) / (δ₂ * w₂))
      ((((F.α₂ * δ₁ * w₁ : ℕ) : ℝ) * R₁ + ((F.α₁ * F.β₂ : ℕ) : ℝ) - ((F.α₂ * F.β₁ : ℕ) : ℝ))
        / ((F.α₁ * δ₂ * w₂ : ℕ) : ℝ)))

/-- (5.16) -/
noncomputable def hbT₂ (F : HBForms) (x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ) (w₁ w₂ : ℕ) : ℝ :=
  min (2 * R₂)
    (min (((2 * F.α₂ * x + F.β₂ : ℕ) : ℝ) / (δ₂ * w₂))
      ((2 * ((F.α₂ * δ₁ * w₁ : ℕ) : ℝ) * R₁ + ((F.α₁ * F.β₂ : ℕ) : ℝ) - ((F.α₂ * F.β₁ : ℕ) : ℝ))
        / ((F.α₁ * δ₂ * w₂ : ℕ) : ℝ)))

end Salt.N7
