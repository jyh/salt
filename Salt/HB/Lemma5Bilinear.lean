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

/-- **B-2.1 — `Q` and `P` are coprime** (p.210): the two sifting moduli are products over
DISJOINT sets of primes, `χ(p) = −1` against `χ(p) = 1`, so no prime divides both. -/
theorem coprime_hbQ_hbP (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) :
    Nat.Coprime (hbQ χ z) (hbP (chiReChar χ hsq) (z : ℝ)) := by
  rw [hbQ, hbP, hbSiftSet_chiReChar]
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun p' hp' => ?_
  rw [Finset.mem_filter] at hp hp'
  refine (Nat.coprime_primes hp.2.1 hp'.2.1).mpr fun hpp => ?_
  have h1 : chiRe χ p = -1 := hp.2.2
  have h2 : chiRe χ p = 1 := by rw [hpp]; exact hp'.2.2.2
  rw [h1] at h2
  norm_num at h2

/-- `chiRe` is multiplicative over a `Finset` product — the bridge from a prime-by-prime
character value to the value at a squarefree number, written as its product of prime factors.
Introduced here for `chiRe_eq_one_of_dvd_hbP`; B-2a's χ step consumes it again. -/
lemma chiRe_finset_prod (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (s : Finset ℕ) :
    chiRe χ (∏ p ∈ s, p) = ∏ p ∈ s, chiRe χ p := by
  classical
  refine Finset.induction_on s (by simp [chiRe_one]) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, chiRe_mul χ hsq, ih, Finset.prod_insert ha]

/-- **B-2.1 — `χ = 1` on every divisor of `P`** (p.210): `P` is squarefree, so a divisor `d`
is the product of its prime factors, each a prime of `P` and so each with `χ(p) = 1`. -/
theorem chiRe_eq_one_of_dvd_hbP (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) {d : ℕ}
    (hd : d ∣ hbP (chiReChar χ hsq) (z : ℝ)) : chiRe χ d = 1 := by
  have hP0 : hbP (chiReChar χ hsq) (z : ℝ) ≠ 0 := (hbP_squarefree _ _).ne_zero
  have hsf : Squarefree d := (hbP_squarefree (chiReChar χ hsq) (z : ℝ)).squarefree_of_dvd hd
  have hd' : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsf
  have hsub : d.primeFactors ⊆ (hbP (chiReChar χ hsq) (z : ℝ)).primeFactors :=
    Nat.primeFactors_mono hd hP0
  calc chiRe χ d = chiRe χ (∏ p ∈ d.primeFactors, p) := by rw [hd']
    _ = ∏ p ∈ d.primeFactors, chiRe χ p := chiRe_finset_prod χ hsq _
    _ = 1 := Finset.prod_eq_one fun p hp => by
        have hp1 := hbP_chi (chiReChar χ hsq) (z : ℝ) p (hsub hp)
        rwa [chiReChar_prime] at hp1

/-- **B-2c — `log` as a ray integral of an indicator against `dV/V`** (p.211): the shape in
which the carrier's `V_i`-integrals deliver HB's logarithms. -/
theorem integral_Ioi_ite_inv {a v : ℝ} (ha : 0 < a) (hav : a ≤ v) :
    (∫ V in Set.Ioi a, (if V < v then V⁻¹ else 0)) = Real.log (v / a) := by
  have hfun : (fun V : ℝ => if V < v then V⁻¹ else 0)
      = Set.indicator (Set.Iio v) (fun V : ℝ => V⁻¹) := by
    funext V
    by_cases h : V < v <;> simp [h]
  have hint : (∫ V in Set.Ioi a, (if V < v then V⁻¹ else 0))
      = ∫ V, Set.indicator (Set.Iio v) (fun V : ℝ => V⁻¹) V
          ∂(MeasureTheory.volume.restrict (Set.Ioi a)) := by
    rw [hfun]
  rw [hint, MeasureTheory.integral_indicator measurableSet_Iio,
    MeasureTheory.Measure.restrict_restrict measurableSet_Iio]
  have hset : Set.Iio v ∩ Set.Ioi a = Set.Ioo a v := by
    ext x; simp [Set.mem_Ioo, and_comm]
  rw [hset, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hav]
  exact integral_inv_of_pos ha (lt_of_lt_of_le ha hav)

/-- **B-2c″ — the integrability `integral_finsetSum` demands at B-2c′ and Lemma 9's inner row
needs twice**: one term of the truncated divisor sum, against `dV/V` on a ray. -/
theorem integrable_term {a v c : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun V : ℝ => c * (if V < v then V⁻¹ else 0))
      (MeasureTheory.volume.restrict (Set.Ioi a)) := by
  have hIoo : MeasureTheory.IntegrableOn (fun V : ℝ => V⁻¹) (Set.Ioo a v) := by
    have hcont : ContinuousOn (fun V : ℝ => V⁻¹) (Set.Icc a v) := by
      apply continuousOn_inv₀.mono
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    exact (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hres : MeasureTheory.IntegrableOn (fun V : ℝ => V⁻¹) (Set.Iio v)
      (MeasureTheory.volume.restrict (Set.Ioi a)) := by
    have hset : Set.Iio v ∩ Set.Ioi a = Set.Ioo a v := by
      ext x; simp [Set.mem_Ioo, and_comm]
    rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_restrict measurableSet_Iio,
      hset]
    exact hIoo
  refine ((hres.integrable_indicator measurableSet_Iio).const_mul c).congr ?_
  filter_upwards with V
  by_cases h : V < v <;> simp [h]

/-- **B-2c″ — the aggregate**: the whole truncated divisor sum over `dV/V` is integrable on the
ray, by `integrable_finsetSum` over `integrable_term`. -/
theorem integrableOn_truncChiSum_div (χ : DirichletCharacter ℂ q) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun V : ℝ => truncChiSum χ N V / V) (Set.Ioi a) := by
  have key : (fun V : ℝ => truncChiSum χ N V / V)
      = fun V : ℝ =>
          ∑ p ∈ N.divisorsAntidiagonal, chiRe χ p.1 * (if V < (p.2 : ℝ) then V⁻¹ else 0) := by
    funext V
    rw [truncChiSum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : V < (p.2 : ℝ) <;> simp [h, div_eq_mul_inv]
  rw [MeasureTheory.IntegrableOn, key]
  exact MeasureTheory.integrable_finsetSum _ (fun p _ => integrable_term ha)

/-- **B-2c′ — the carrier's inner sum integrates to the log-weighted sum** (p.211), `a ≤ 1`:
each divisor pair's indicator integrates to `log(v/a)` by B-2c, and `a ≤ 1 ≤ v` is exactly
what the consumer's `(j_i k_i)⁻¹` supplies. -/
theorem integral_Ioi_truncChiSum (χ : DirichletCharacter ℂ q) (N : ℕ) {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) :
    (∫ V in Set.Ioi a, truncChiSum χ N V / V) = logDivChiSum χ N a⁻¹ := by
  have key : ∀ V : ℝ, truncChiSum χ N V / V
      = ∑ p ∈ N.divisorsAntidiagonal, chiRe χ p.1 * (if V < (p.2 : ℝ) then V⁻¹ else 0) := by
    intro V
    rw [truncChiSum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : V < (p.2 : ℝ) <;> simp [h, div_eq_mul_inv]
  simp_rw [key]
  rw [MeasureTheory.integral_finsetSum _ (fun p _ => integrable_term ha)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : (1 : ℝ) ≤ (p.2 : ℝ) := by
    have hmem := (Nat.mem_divisorsAntidiagonal.mp hp)
    have hne : p.2 ≠ 0 := by
      rintro h
      exact hmem.2 (by simp [← hmem.1, h])
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  rw [MeasureTheory.integral_const_mul, integral_Ioi_ite_inv ha (le_trans ha1 hp2)]
  congr 1
  rw [div_eq_inv_mul]

/-! ### The μ-sieve of `Λ*` over `Q` (p.210) — the radical of the `Q`-part of the square kernel,
the set identity it gives, the Möbius step, and the two χ facts `m ∣ Q` buys. -/

/-- The radical of the `Q`-part of the square kernel of `d`: the product of the primes `p < z`
with `χ(p) = −1` and `p² ∣ d`.  `Λ*`'s admissibility condition at `d` is exactly `hbQRad = 1`,
and the divisors of `hbQRad` are exactly the `m ∣ Q` with `m² ∣ d` — which is what turns the
admissibility indicator into a Möbius sum.  ⛔ Not `Salt.HB.hbG`, which is the ℝ-valued sieve
density numerator `G(d)` of p.199 and lives in the open cone under that name. -/
noncomputable def hbQRad (χ : DirichletCharacter ℂ q) (z d : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p = -1 ∧ p ^ 2 ∣ d), p

/-- `Q` is a product of distinct primes, hence squarefree. -/
lemma hbQ_squarefree (χ : DirichletCharacter ℂ q) (z : ℕ) : Squarefree (hbQ χ z) :=
  squarefree_prod_of_primes (fun _ hp => (Finset.mem_filter.mp hp).2.1)

/-- So is the radical, for the same reason. -/
lemma hbQRad_squarefree (χ : DirichletCharacter ℂ q) (z d : ℕ) : Squarefree (hbQRad χ z d) :=
  squarefree_prod_of_primes (fun _ hp => (Finset.mem_filter.mp hp).2.1)

/-- The radical's prime set is a subset of `Q`'s, so it divides `Q`. -/
lemma hbQRad_dvd_hbQ (χ : DirichletCharacter ℂ q) (z d : ℕ) : hbQRad χ z d ∣ hbQ χ z :=
  Finset.prod_dvd_prod_of_subset _ _ _ (by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩)

/-- The primes of `Q`, read off the product: `p ∣ Q ↔ p < z ∧ χ(p) = −1`. -/
lemma prime_dvd_hbQ_iff {χ : DirichletCharacter ℂ q} {z p : ℕ} (hp : p.Prime) :
    p ∣ hbQ χ z ↔ (p < z ∧ chiRe χ p = -1) := by
  constructor
  · intro h
    obtain ⟨p', hp', hdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp h
    rw [Finset.mem_filter, Finset.mem_range] at hp'
    have hpp : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp'.2.1).mp hdvd
    subst hpp
    exact ⟨hp'.1, hp'.2.2⟩
  · intro h
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, hp, h.2⟩)

/-- The primes of the radical, with the extra `p² ∣ d` conjunct. -/
lemma prime_dvd_hbQRad_iff {χ : DirichletCharacter ℂ q} {z d p : ℕ} (hp : p.Prime) :
    p ∣ hbQRad χ z d ↔ (p < z ∧ chiRe χ p = -1 ∧ p ^ 2 ∣ d) := by
  constructor
  · intro h
    obtain ⟨p', hp', hdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp h
    rw [Finset.mem_filter, Finset.mem_range] at hp'
    have hpp : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp'.2.1).mp hdvd
    subst hpp
    exact ⟨hp'.1, hp'.2.2.1, hp'.2.2.2⟩
  · intro h
    exact Finset.dvd_prod_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, hp, h.2.1, h.2.2⟩)

/-- `hbQRad² ∣ d` — the defining property, through the factorisation order
(`Nat.factorization_le_iff_dvd`): at each prime the radical contributes at most `1` and `d`
carries at least `2`.  ⛔ The ℕ `Finset.prod_dvd_of_coprime` route does NOT work here. -/
lemma hbQRad_sq_dvd (χ : DirichletCharacter ℂ q) (z d : ℕ) : (hbQRad χ z d) ^ 2 ∣ d := by
  rcases eq_or_ne d 0 with rfl | hd
  · exact dvd_zero _
  have hG : hbQRad χ z d ≠ 0 := (hbQRad_squarefree χ z d).ne_zero
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hG) hd, Finsupp.le_def]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos ((hbQRad χ z d).factorization p) with h0 | h0
  · simp [h0]
  · have hpmem : p ∈ (hbQRad χ z d).primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpG : p ∣ hbQRad χ z d := Nat.dvd_of_mem_primeFactors hpmem
    obtain ⟨-, -, hsqd⟩ := (prime_dvd_hbQRad_iff hp).mp hpG
    have h1 : (hbQRad χ z d).factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hG).mp (hbQRad_squarefree χ z d) p
    have h2 : 2 ≤ d.factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hp hd).mp hsqd
    omega

/-- **The set identity the Möbius step runs on**: `{m ∣ Q : m² ∣ d}` is exactly the set of
divisors of `hbQRad χ z d`.  `⊆` is squarefreeness of `m` plus `Nat.prod_primeFactors_of_squarefree`
(every prime of `m` is a prime of `Q` whose square divides `d`); `⊇` is `hbQRad_dvd_hbQ` and
`hbQRad_sq_dvd`. -/
lemma filter_divisors_hbQ (χ : DirichletCharacter ℂ q) (z d : ℕ) :
    (hbQ χ z).divisors.filter (fun m => m ^ 2 ∣ d) = (hbQRad χ z d).divisors := by
  ext m
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hmQ, -⟩, hm2⟩
    refine ⟨?_, (hbQRad_squarefree χ z d).ne_zero⟩
    have hsf : Squarefree m := (hbQ_squarefree χ z).squarefree_of_dvd hmQ
    have hsub : m.primeFactors ⊆
        (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p = -1 ∧ p ^ 2 ∣ d) := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨hpz, hpchi⟩ := (prime_dvd_hbQ_iff hpp).mp (hpm.trans hmQ)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hpz, hpp, hpchi, (pow_dvd_pow_of_dvd hpm 2).trans hm2⟩
    calc m = ∏ p ∈ m.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsf).symm
      _ ∣ hbQRad χ z d := Finset.prod_dvd_prod_of_subset _ _ _ hsub
  · rintro ⟨hmG, -⟩
    exact ⟨⟨hmG.trans (hbQRad_dvd_hbQ χ z d), (hbQ_squarefree χ z).ne_zero⟩,
      (pow_dvd_pow_of_dvd hmG 2).trans (hbQRad_sq_dvd χ z d)⟩

/-- `hbQRad = 1` is exactly `Λ*`'s admissibility condition at `d`. -/
lemma hbQRad_eq_one_iff (χ : DirichletCharacter ℂ q) (z d : ℕ) :
    hbQRad χ z d = 1 ↔ Admissible χ z d := by
  constructor
  · intro h p hp hpz hpchi hsqd
    have hdvd : p ∣ hbQRad χ z d := (prime_dvd_hbQRad_iff hp).mpr ⟨hpz, hpchi, hsqd⟩
    rw [h] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  · intro hA
    have hempty : (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p = -1 ∧ p ^ 2 ∣ d) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro p hp ⟨hpp, hpchi, hsqd⟩
      exact hA p hpp (Finset.mem_range.mp hp) hpchi hsqd
    rw [hbQRad, hempty, Finset.prod_empty]

/-- **The Möbius step**: `Σ_{m ∣ Q, m² ∣ d} μ(m)` is the indicator of admissibility at `d`.
The set identity turns the sum into `Σ_{m ∣ hbQRad} μ(m)`, which is `1` iff `hbQRad = 1`
(`Salt.SW.sum_divisors_moebius_real`), and `hbQRad = 1` is admissibility. -/
lemma moebius_step (χ : DirichletCharacter ℂ q) (z d : ℕ) :
    ∑ m ∈ (hbQ χ z).divisors.filter (fun m => m ^ 2 ∣ d), (μ m : ℝ)
      = if Admissible χ z d then (1 : ℝ) else 0 := by
  rw [filter_divisors_hbQ, Salt.SW.sum_divisors_moebius_real]
  by_cases hA : Admissible χ z d
  · rw [if_pos hA, if_pos ((hbQRad_eq_one_iff χ z d).mpr hA)]
  · rw [if_neg hA, if_neg (fun h => hA ((hbQRad_eq_one_iff χ z d).mp h))]

/-- **The χ step**: `m ∣ Q ⇒ χ(m)² = 1`.  Every prime of `Q` has `χ(p) = −1`, and `m ∣ Q` is
squarefree, so `χ(m) = (−1)^{ω(m)} = ±1`.  ⛔ FALSE for general `m` — `χ(m) = 0` at `m` sharing a
factor with the modulus; the hypothesis `m ∣ Q` is doing the work. -/
lemma chiRe_sq_of_dvd_hbQ (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z m : ℕ}
    (hm : m ∣ hbQ χ z) : (chiRe χ m) ^ 2 = 1 := by
  have hsf : Squarefree m := (hbQ_squarefree χ z).squarefree_of_dvd hm
  have hm' : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hsf
  have key : chiRe χ (∏ p ∈ m.primeFactors, p) = ∏ p ∈ m.primeFactors, chiRe χ p :=
    chiRe_finset_prod χ hsq _
  rw [hm'] at key
  have hall : ∀ p ∈ m.primeFactors, chiRe χ p = -1 := fun p hp =>
    ((prime_dvd_hbQ_iff (Nat.prime_of_mem_primeFactors hp)).mp
      ((Nat.dvd_of_mem_primeFactors hp).trans hm)).2
  rw [key, Finset.prod_congr rfl hall, Finset.prod_const, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- The χ step in the shape the reindex `d = m² v` needs. -/
lemma chiRe_sq_mul (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z m : ℕ}
    (hm : m ∣ hbQ χ z) (v : ℕ) : chiRe χ (m ^ 2 * v) = chiRe χ v := by
  rw [chiRe_mul χ hsq, chiRe_pow χ hsq, chiRe_sq_of_dvd_hbQ χ hsq hm, one_mul]

/-- **B-2a — `Λ*` as the μ-sieve of `Λ′` over `Q`, EXACT** (p.210, first display): no
truncation, every `m ∣ Q` with `m² ∣ n`.  The admissibility indicator inside `Λ*` becomes the
Möbius sum, the two sums swap (`Finset.sum_comm'` over the pairs `(d, m)` with `m² ∣ d ∣ n`),
and the inner sum is reindexed at `d = m² v` by `Finset.sum_nbij'`, where `χ(m²v) = χ(v)` is the
χ step and `n/(m²v) = (n/m²)/v` is `Nat.div_div_eq_div_mul`. -/
theorem LamStar_eq_moebius_hbQ (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z n : ℕ) :
    LamStar χ z n
      = ∑ m ∈ (hbQ χ z).divisors.filter (fun m => m ^ 2 ∣ n),
          (μ m : ℝ) * LamPrime χ (n / m ^ 2) := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LamStar, LamPrime]
  -- LHS: replace the admissibility indicator by the Moebius sum
  have hL : LamStar χ z n
      = ∑ d ∈ n.divisors, ∑ m ∈ (hbQ χ z).divisors.filter (fun m => m ^ 2 ∣ d),
          (μ m : ℝ) * (chiRe χ d * Real.log ((n / d : ℕ) : ℝ)) := by
    rw [LamStar]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_mul, moebius_step χ z d]
    by_cases hA : Admissible χ z d
    · rw [if_pos hA, if_pos hA, one_mul]
    · rw [if_neg hA, if_neg hA, zero_mul]
  rw [hL]
  -- swap the two sums
  rw [Finset.sum_comm' (t' := (hbQ χ z).divisors.filter (fun m => m ^ 2 ∣ n))
      (s' := fun m => n.divisors.filter (fun d => m ^ 2 ∣ d))
      (by
        intro d m
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hdn, hn0⟩, ⟨hmQ, hQ0⟩, hm2⟩
          exact ⟨⟨⟨hdn, hn0⟩, hm2⟩, ⟨hmQ, hQ0⟩, hm2.trans hdn⟩
        · rintro ⟨⟨⟨hdn, hn0⟩, hm2⟩, ⟨hmQ, hQ0⟩, -⟩
          exact ⟨⟨hdn, hn0⟩, ⟨hmQ, hQ0⟩, hm2⟩)]
  -- the inner reindex `d = m² v`
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hmdiv, hm2n⟩ := Finset.mem_filter.mp hm
  have hmQ : m ∣ hbQ χ z := (Nat.mem_divisors.mp hmdiv).1
  have hm0 : 0 < m := Nat.pos_of_mem_divisors hmdiv
  have hm2pos : 0 < m ^ 2 := pow_pos hm0 2
  rw [LamPrime, Finset.mul_sum]
  refine Finset.sum_nbij' (i := fun d => d / m ^ 2) (j := fun v => m ^ 2 * v) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    refine ⟨?_, ?_⟩
    · have h1 : m ^ 2 * (d / m ^ 2) ∣ m ^ 2 * (n / m ^ 2) := by
        rw [Nat.mul_div_cancel' hd.2, Nat.mul_div_cancel' hm2n]; exact hd.1.1
      exact (Nat.mul_dvd_mul_iff_left hm2pos).mp h1
    · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hm2n) hm2pos).ne'
  · intro v hv
    simp only [Nat.mem_divisors, Finset.mem_filter] at hv ⊢
    refine ⟨⟨?_, hn⟩, Dvd.intro v rfl⟩
    calc m ^ 2 * v ∣ m ^ 2 * (n / m ^ 2) := Nat.mul_dvd_mul_left _ hv.1
      _ = n := Nat.mul_div_cancel' hm2n
  · intro d hd
    simp only [Finset.mem_filter] at hd
    exact Nat.mul_div_cancel' hd.2
  · intro v _
    exact Nat.mul_div_cancel_left v hm2pos
  · intro d hd
    simp only [Finset.mem_filter] at hd
    have hd2 : m ^ 2 * (d / m ^ 2) = d := Nat.mul_div_cancel' hd.2
    have hchi : chiRe χ d = chiRe χ (d / m ^ 2) := by
      conv_lhs => rw [← hd2]
      exact chiRe_sq_mul χ hsq hmQ _
    have hlog : (n / d : ℕ) = (n / m ^ 2 / (d / m ^ 2) : ℕ) := by
      rw [Nat.div_div_eq_div_mul, hd2]
    rw [hchi, hlog]

/-! ### B-2b — the hyperbola identity (p.211): the nested enumeration, the fibre split of
`n.divisorsAntidiagonal` by `gcd(s, e)`, and the Möbius detector that selects the fibre. -/

/-- The nested antidiagonal enumeration IS the triple sum over `h j k = e`: `t = (h, jk)` runs
over `e.divisorsAntidiagonal` and `u = (j, k)` over `(jk).divisorsAntidiagonal`, and together they
hit each factorisation `h j k = e` exactly once. -/
theorem nested_antidiag (e : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ t ∈ e.divisorsAntidiagonal, ∑ u ∈ t.2.divisorsAntidiagonal, f t.1 u.1 u.2)
      = ∑ h ∈ e.divisors, ∑ j ∈ (e / h).divisors, f h j ((e / h) / j) := by
  rw [Nat.sum_divisorsAntidiagonal (fun h i => ∑ u ∈ i.divisorsAntidiagonal, f h u.1 u.2)]
  exact Finset.sum_congr rfl fun h _ =>
    Nat.sum_divisorsAntidiagonal (fun j k => f h j k)

/-- **The fibre facts.**  For `(s, t)` with `s t = n` and `gcd(s, e) = h`, write `E = e/h`,
`N = n/e` and `σ = s/h`.  Then `σ ∣ N`, `gcd(E, σ) = 1`, and `t = E · (N/σ)`.  The third is the
one that matters: on this fibre the second coordinate is FORCED to be a multiple of `E`, which is
what makes the reindexing below a bijection.  `σ ∣ N` is not automatic — it needs
`gcd(σ, E) = 1` together with `σ ∣ E N`. -/
theorem fiber_facts {n e h : ℕ} (hn : n ≠ 0) (he : e ∣ n) (hh : h ∣ e) {p : ℕ × ℕ}
    (hp : p ∈ n.divisorsAntidiagonal) (hg : Nat.gcd p.1 e = h) :
    p.1 / h ∣ n / e ∧ Nat.gcd (e / h) (p.1 / h) = 1 ∧
      p.2 = e / h * (n / e / (p.1 / h)) := by
  obtain ⟨hst, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have he0 : e ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd he)
  have hh0 : h ≠ 0 := by
    rw [← hg]; simp [Nat.gcd_eq_zero_iff, he0]
  have hhs : h ∣ p.1 := hg ▸ Nat.gcd_dvd_left _ _
  have heE : h * (e / h) = e := Nat.mul_div_cancel' hh
  have hnN : e * (n / e) = n := Nat.mul_div_cancel' he
  have hps : h * (p.1 / h) = p.1 := Nat.mul_div_cancel' hhs
  have hcop : Nat.gcd (p.1 / h) (e / h) = 1 := by
    have hkey : h * Nat.gcd (p.1 / h) (e / h) = h * 1 := by
      rw [mul_one, ← Nat.gcd_mul_left, hps, heE, hg]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh0) hkey
  have hs0 : p.1 / h ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hps
    exact hn (by rw [← hst, ← hps, zero_mul])
  have hmul : (p.1 / h) * p.2 = (e / h) * (n / e) := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh0) ?_
    calc h * ((p.1 / h) * p.2) = (h * (p.1 / h)) * p.2 := by ring
      _ = p.1 * p.2 := by rw [hps]
      _ = n := hst
      _ = e * (n / e) := hnN.symm
      _ = (h * (e / h)) * (n / e) := by rw [heE]
      _ = h * ((e / h) * (n / e)) := by ring
  have hdvdN : p.1 / h ∣ n / e :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop ⟨p.2, hmul.symm⟩
  refine ⟨hdvdN, Nat.Coprime.symm hcop, ?_⟩
  have hNs : (p.1 / h) * (n / e / (p.1 / h)) = n / e := Nat.mul_div_cancel' hdvdN
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs0) ?_
  calc (p.1 / h) * p.2 = (e / h) * (n / e) := hmul
    _ = (e / h) * ((p.1 / h) * (n / e / (p.1 / h))) := by rw [hNs]
    _ = (p.1 / h) * ((e / h) * (n / e / (p.1 / h))) := by ring

/-- **The `(j, v)` swap.**  `{(j, v) : j ∣ E, j ∣ N, v ∣ N/j}` and `{(v, j) : v ∣ N, j ∣ E,
j ∣ N/v}` are the same set — both say `j ∣ E` and `j v ∣ N` — so the double sum may be taken with
`v` outside, where the `j`-range is the divisors of `gcd(E, N/v)` and the Möbius sum collapses. -/
theorem second_reindex {E N : ℕ} (hE : E ≠ 0) (hN : N ≠ 0) (F : ℕ → ℕ → ℝ) :
    ∑ j ∈ E.divisors, (if j ∣ N then ∑ v ∈ (N / j).divisors, F j v else 0)
      = ∑ v ∈ N.divisors, ∑ j ∈ (Nat.gcd E (N / v)).divisors, F j v := by
  rw [← Finset.sum_filter (fun j => j ∣ N) (fun j => ∑ v ∈ (N / j).divisors, F j v)]
  refine Finset.sum_comm' ?_
  intro j v
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨⟨hjE, -⟩, hjN⟩, hvNj, -⟩
    have hjv : j * v ∣ N := (Nat.dvd_div_iff_mul_dvd hjN).mp hvNj
    have hvN : v ∣ N := (dvd_mul_left v j).trans hjv
    refine ⟨⟨⟨hjE, (Nat.dvd_div_iff_mul_dvd hvN).mpr (by rwa [mul_comm v j])⟩, ?_⟩, hvN, hN⟩
    simp [Nat.gcd_eq_zero_iff, hE]
  · rintro ⟨⟨⟨hjE, hjNv⟩, -⟩, hvN, -⟩
    have hvj : v * j ∣ N := (Nat.dvd_div_iff_mul_dvd hvN).mp hjNv
    have hjN : j ∣ N := (dvd_mul_left j v).trans hvj
    have hj0 : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hjN))
    refine ⟨⟨⟨hjE, hE⟩, hjN⟩, (Nat.dvd_div_iff_mul_dvd hjN).mpr (by rwa [mul_comm j v]), ?_⟩
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hjN) hj0).ne'

/-- **The fibre, reindexed by `v = t/E`.**  The map `v ↦ (h · (N/v), E · v)` is a bijection from
`{v ∣ N : gcd(E, N/v) = 1}` onto the fibre `{(s,t) ∈ n.divisorsAntidiagonal : gcd(s,e) = h}`, with
inverse `(s,t) ↦ t/E`.  `gcd(h σ, h E) = h · gcd(σ, E)` (`Nat.gcd_mul_left`) is what turns the
coprimality condition into the fibre condition. -/
theorem fiber_reindex (χ : DirichletCharacter ℂ q) {n e h : ℕ}
    (hn : n ≠ 0) (he : e ∣ n) (hh : h ∣ e) :
    ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => Nat.gcd p.1 e = h),
        chiRe χ p.1 * Real.log ((p.2 : ℝ))
      = ∑ v ∈ (n / e).divisors.filter (fun v => Nat.gcd (e / h) (n / e / v) = 1),
          chiRe χ (h * (n / e / v)) * Real.log (((e / h : ℕ) : ℝ) * (v : ℝ)) := by
  have he0 : e ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd he)
  have hh0 : h ≠ 0 := by rintro rfl; exact he0 (Nat.eq_zero_of_zero_dvd hh)
  have heE : h * (e / h) = e := Nat.mul_div_cancel' hh
  have hE0 : 0 < e / h := Nat.pos_of_ne_zero (by
    rintro h0; rw [h0, mul_zero] at heE; exact he0 heE.symm)
  have hnN : e * (n / e) = n := Nat.mul_div_cancel' he
  have hN0 : n / e ≠ 0 := by rintro h0; rw [h0, mul_zero] at hnN; exact hn hnN.symm
  refine Finset.sum_nbij' (i := fun p => p.2 / (e / h))
    (j := fun v => (h * (n / e / v), e / h * v)) ?_ ?_ ?_ ?_ ?_
  · -- i maps into the v-set
    intro p hp
    obtain ⟨hpmem, hpg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hsN, hcop, h2⟩ := fiber_facts hn he hh hpmem hpg
    rw [Finset.mem_filter, Nat.mem_divisors]
    rw [h2, Nat.mul_div_cancel_left _ hE0]
    refine ⟨⟨Nat.div_dvd_of_dvd hsN, hN0⟩, ?_⟩
    rw [Nat.div_div_self hsN hN0]
    exact hcop
  · -- j maps into the fibre
    intro v hv
    obtain ⟨hvmem, hvc⟩ := Finset.mem_filter.mp hv
    have hvN : v ∣ n / e := (Nat.mem_divisors.mp hvmem).1
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, hn⟩, ?_⟩
    · calc h * (n / e / v) * (e / h * v)
          = (h * (e / h)) * ((n / e / v) * v) := by ring
        _ = e * (n / e) := by rw [heE, Nat.div_mul_cancel hvN]
        _ = n := hnN
    · calc Nat.gcd (h * (n / e / v)) e
          = Nat.gcd (h * (n / e / v)) (h * (e / h)) := by rw [heE]
        _ = h * Nat.gcd (n / e / v) (e / h) := Nat.gcd_mul_left _ _ _
        _ = h * 1 := by rw [Nat.gcd_comm, hvc]
        _ = h := mul_one h
  · -- j ∘ i = id on the fibre
    intro p hp
    obtain ⟨hpmem, hpg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hsN, hcop, h2⟩ := fiber_facts hn he hh hpmem hpg
    have hhs : h ∣ p.1 := hpg ▸ Nat.gcd_dvd_left _ _
    refine Prod.ext ?_ ?_
    · change h * (n / e / (p.2 / (e / h))) = p.1
      rw [h2, Nat.mul_div_cancel_left _ hE0, Nat.div_div_self hsN hN0,
        Nat.mul_div_cancel' hhs]
    · change e / h * (p.2 / (e / h)) = p.2
      rw [h2, Nat.mul_div_cancel_left _ hE0]
  · -- i ∘ j = id on the v-set
    intro v _
    exact Nat.mul_div_cancel_left _ hE0
  · -- the summands agree
    intro p hp
    obtain ⟨hpmem, hpg⟩ := Finset.mem_filter.mp hp
    obtain ⟨hsN, hcop, h2⟩ := fiber_facts hn he hh hpmem hpg
    have hhs : h ∣ p.1 := hpg ▸ Nat.gcd_dvd_left _ _
    have h1 : h * (n / e / (p.2 / (e / h))) = p.1 := by
      rw [h2, Nat.mul_div_cancel_left _ hE0, Nat.div_div_self hsN hN0,
        Nat.mul_div_cancel' hhs]
    have h3 : ((e / h : ℕ) : ℝ) * ((p.2 / (e / h) : ℕ) : ℝ) = ((p.2 : ℕ) : ℝ) := by
      rw [h2, Nat.mul_div_cancel_left _ hE0]
      push_cast
      ring
    rw [h1, h3]

/-- **B-2b at one fibre.**  The `j`-sum of the hyperbola identity's right-hand side, at a fixed
`h ∣ e`, is exactly the fibre of `n.divisorsAntidiagonal` over `gcd(s, e) = h`.  Three moves: the
`j`-term's data is `n/(e j) = N/j` and `j · (E/j) = E` (so the log's constant does NOT depend on
`j`); the inner antidiagonal is reindexed by its SECOND coordinate, after which `χ(hj)·χ((N/j)/v)`
is `χ(h·(N/v))` — free of `j` — because `j · ((N/j)/v) = N/v`; and the `j`-sum, now carrying only
`μ(j)`, runs over the divisors of `gcd(E, N/v)` and is the indicator of `gcd(E, N/v) = 1`. -/
theorem hyperbola_fiber (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n e h : ℕ}
    (hn : n ≠ 0) (he : e ∣ n) (hh : h ∣ e) :
    ∑ j ∈ (e / h).divisors,
        (if j ∣ n / e then
          chiRe χ (h * j) * (μ j : ℝ) *
            logDivChiSum χ (n / (e * j)) ((j * ((e / h) / j) : ℕ) : ℝ)
        else 0)
      = ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => Nat.gcd p.1 e = h),
          chiRe χ p.1 * Real.log ((p.2 : ℝ)) := by
  have he0 : e ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd he)
  have heE : h * (e / h) = e := Nat.mul_div_cancel' hh
  have hE0 : e / h ≠ 0 := by rintro h0; rw [h0, mul_zero] at heE; exact he0 heE.symm
  have hnN : e * (n / e) = n := Nat.mul_div_cancel' he
  have hN0 : n / e ≠ 0 := by rintro h0; rw [h0, mul_zero] at hnN; exact hn hnN.symm
  rw [fiber_reindex χ hn he hh]
  have hAC : ∀ j ∈ (e / h).divisors,
      (if j ∣ n / e then
        chiRe χ (h * j) * (μ j : ℝ) *
          logDivChiSum χ (n / (e * j)) ((j * ((e / h) / j) : ℕ) : ℝ)
      else 0)
      = (if j ∣ n / e then
        ∑ v ∈ (n / e / j).divisors,
          (μ j : ℝ) * (chiRe χ (h * (n / e / v)) * Real.log (((e / h : ℕ) : ℝ) * (v : ℝ)))
      else 0) := by
    intro j hj
    have hjE : j ∣ e / h := (Nat.mem_divisors.mp hj).1
    by_cases hjN : j ∣ n / e
    · rw [if_pos hjN, if_pos hjN, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hjE,
        logDivChiSum, Nat.sum_divisorsAntidiagonal'
          (fun a b => chiRe χ a * Real.log (((e / h : ℕ) : ℝ) * (b : ℝ))), Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hvM : v ∣ n / e / j := (Nat.mem_divisors.mp hv).1
      have hv0 : 0 < v := Nat.pos_of_ne_zero (by
        rintro rfl
        exact (Nat.mem_divisors.mp hv).2 (Nat.eq_zero_of_zero_dvd hvM))
      have hjv : j * v ∣ n / e := (Nat.dvd_div_iff_mul_dvd hjN).mp hvM
      have hNjv : (j * v) * (n / e / (j * v)) = n / e := Nat.mul_div_cancel' hjv
      have hkey2 : n / e / v = j * (n / e / (j * v)) := by
        refine Nat.div_eq_of_eq_mul_left hv0 ?_
        calc n / e = (j * v) * (n / e / (j * v)) := hNjv.symm
          _ = (j * (n / e / (j * v))) * v := by ring
      have hkey : h * j * (n / e / j / v) = h * (n / e / v) := by
        rw [Nat.div_div_eq_div_mul (n / e) j v, hkey2, mul_assoc]
      have hchi : chiRe χ (h * (n / e / v)) = chiRe χ (h * j) * chiRe χ (n / e / j / v) := by
        rw [← hkey, chiRe_mul χ hsq]
      rw [hchi]
      ring
    · rw [if_neg hjN, if_neg hjN]
  rw [Finset.sum_congr rfl hAC, second_reindex hE0 hN0
    (fun j v => (μ j : ℝ) * (chiRe χ (h * (n / e / v)) * Real.log (((e / h : ℕ) : ℝ) * (v : ℝ)))),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_mul, Salt.SW.sum_divisors_moebius_real]
  by_cases hg : Nat.gcd (e / h) (n / e / v) = 1
  · rw [if_pos hg, if_pos hg, one_mul]
  · rw [if_neg hg, if_neg hg, zero_mul]

/-- **B-2b — the hyperbola identity** (p.211): for `e ∣ n`,
`Λ′(n) = Σ_{e = h j k, j ∣ n/e} χ(h j) μ(j) Σ_{n/(e j) = w v} χ(w) log(j k v)`.
⛔ The guard `j ∣ n/e` is LOAD-BEARING: `Nat` division truncates, so without it the terms at
`j ∤ n/e` are not zero but garbage, and the identity is false.  The proof splits
`n.divisorsAntidiagonal` into the fibres of `gcd(s, e)` and matches each fibre against the
`h`-block of the right-hand side. -/
theorem LamPrime_eq_hyperbola (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {n e : ℕ}
    (he : e ∣ n) :
    LamPrime χ n
      = ∑ t ∈ e.divisorsAntidiagonal, ∑ u ∈ t.2.divisorsAntidiagonal,
          if u.1 ∣ n / e then
            chiRe χ (t.1 * u.1) * (μ u.1 : ℝ) * logDivChiSum χ (n / (e * u.1)) ((u.1 * u.2 : ℕ) : ℝ)
          else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LamPrime, logDivChiSum]
  have he0 : e ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd he)
  calc LamPrime χ n
      = ∑ p ∈ n.divisorsAntidiagonal, chiRe χ p.1 * Real.log ((p.2 : ℝ)) := by
        rw [LamPrime]
        exact (Nat.sum_divisorsAntidiagonal (fun a b => chiRe χ a * Real.log ((b : ℕ) : ℝ))).symm
    _ = ∑ h ∈ e.divisors, ∑ p ∈ n.divisorsAntidiagonal.filter (fun p => Nat.gcd p.1 e = h),
          chiRe χ p.1 * Real.log ((p.2 : ℝ)) := by
        refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
        intro p _
        exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, he0⟩
    _ = ∑ h ∈ e.divisors, ∑ j ∈ (e / h).divisors,
          (if j ∣ n / e then
            chiRe χ (h * j) * (μ j : ℝ) *
              logDivChiSum χ (n / (e * j)) ((j * ((e / h) / j) : ℕ) : ℝ)
          else 0) :=
        Finset.sum_congr rfl fun h hh =>
          (hyperbola_fiber χ hsq hn he (Nat.mem_divisors.mp hh).1).symm
    _ = ∑ t ∈ e.divisorsAntidiagonal, ∑ u ∈ t.2.divisorsAntidiagonal,
          (if u.1 ∣ n / e then
            chiRe χ (t.1 * u.1) * (μ u.1 : ℝ) *
              logDivChiSum χ (n / (e * u.1)) ((u.1 * u.2 : ℕ) : ℝ)
          else 0) :=
        (nested_antidiag e (fun h j k => if j ∣ n / e then
          chiRe χ (h * j) * (μ j : ℝ) *
            logDivChiSum χ (n / (e * j)) ((j * k : ℕ) : ℝ) else 0)).symm

/-! ### B-2d′ — LEMMA 9's inner identity at one pair `(m₁, m₂)` of `Q`-divisors: the double ray
integral of the carrier, the unique split `d = d₁d₂`, and the two hyperbola expansions. -/

/-- **The carrier's double ray integral is a window sum of log-weighted divisor sums.**  Both
integrals are taken with the `n`-sum inside and come out by `integral_finsetSum` (each term
integrable by B-2c″); the inner `V₂`-integral goes FIRST, where the `V₁`-factor is constant and
leaves by `integral_const_mul`, and the outer `V₁`-integral then by `integral_mul_const`.
⛔ NO Fubini: the statement is iterated, as HB's own display is. -/
theorem bilinear_double_integral (χ : DirichletCharacter ℂ q) (F : HBForms) (x δ₁ δ₂ : ℕ)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₁1 : a₁ ≤ 1) (ha₂ : 0 < a₂) (ha₂1 : a₂ ≤ 1) :
    (∫ V₁ in Set.Ioi a₁, (∫ V₂ in Set.Ioi a₂, bilinearS χ F x δ₁ δ₂ V₁ V₂ / V₂) / V₁)
      = ∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
          logDivChiSum χ (F.l₁ n / δ₁) a₁⁻¹ * logDivChiSum χ (F.l₂ n / δ₂) a₂⁻¹ := by
  have hinner : ∀ V₁ : ℝ, (∫ V₂ in Set.Ioi a₂, bilinearS χ F x δ₁ δ₂ V₁ V₂ / V₂)
      = ∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
          truncChiSum χ (F.l₁ n / δ₁) V₁ * logDivChiSum χ (F.l₂ n / δ₂) a₂⁻¹ := by
    intro V₁
    have hsplit : ∀ V₂ : ℝ, bilinearS χ F x δ₁ δ₂ V₁ V₂ / V₂
        = ∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
            truncChiSum χ (F.l₁ n / δ₁) V₁ * (truncChiSum χ (F.l₂ n / δ₂) V₂ / V₂) := by
      intro V₂
      rw [bilinearS, Finset.sum_div]
      exact Finset.sum_congr rfl fun n _ => by ring
    simp_rw [hsplit]
    rw [MeasureTheory.integral_finsetSum _
      (fun n _ => ((integrableOn_truncChiSum_div χ (F.l₂ n / δ₂) ha₂).const_mul _))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MeasureTheory.integral_const_mul, integral_Ioi_truncChiSum χ _ ha₂ ha₂1]
  simp_rw [hinner]
  have houter : ∀ V₁ : ℝ,
      (∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
          truncChiSum χ (F.l₁ n / δ₁) V₁ * logDivChiSum χ (F.l₂ n / δ₂) a₂⁻¹) / V₁
      = ∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
          truncChiSum χ (F.l₁ n / δ₁) V₁ / V₁ * logDivChiSum χ (F.l₂ n / δ₂) a₂⁻¹ := by
    intro V₁
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [houter]
  rw [MeasureTheory.integral_finsetSum _
    (fun n _ => ((integrableOn_truncChiSum_div χ (F.l₁ n / δ₁) ha₁).mul_const _))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_mul_const, integral_Ioi_truncChiSum χ _ ha₁ ha₁1]

/-- **The unique split of `d` along a coprime pair.**  If `d ∣ L₁L₂` with `(L₁, L₂) = 1`, then
`d = d₁ d₂` with `d₁ ∣ L₁` and `d₂ ∣ L₂` in EXACTLY ONE way, namely `d₁ = gcd(d, L₁)`.  Existence
is `Nat.coprime_div_gcd_div_gcd` plus a cancellation; uniqueness is `gcd(d₁', d₂) ∣ gcd(L₁, L₂)`.
⛔ Without coprimality of `L₁` and `L₂` the split is NOT unique and Lemma 9's `d`-sum
double-counts. -/
theorem inner_split {d L₁ L₂ : ℕ} (hcop : Nat.Coprime L₁ L₂) (hd : d ∣ L₁ * L₂) (hd0 : d ≠ 0) :
    Nat.gcd d L₁ ∣ L₁ ∧ Nat.gcd d L₁ * (d / Nat.gcd d L₁) = d ∧ d / Nat.gcd d L₁ ∣ L₂ ∧
      ∀ a b : ℕ, a * b = d → a ∣ L₁ → b ∣ L₂ → a = Nat.gcd d L₁ := by
  have hgd : Nat.gcd d L₁ ∣ d := Nat.gcd_dvd_left d L₁
  have hgL : Nat.gcd d L₁ ∣ L₁ := Nat.gcd_dvd_right d L₁
  have hg0 : 0 < Nat.gcd d L₁ := Nat.pos_of_ne_zero (by
    intro h0
    exact hd0 (Nat.eq_zero_of_gcd_eq_zero_left h0))
  refine ⟨hgL, Nat.mul_div_cancel' hgd, ?_, ?_⟩
  · have hcp : Nat.Coprime (d / Nat.gcd d L₁) (L₁ / Nat.gcd d L₁) :=
      Nat.coprime_div_gcd_div_gcd hg0
    refine Nat.Coprime.dvd_of_dvd_mul_left hcp ?_
    refine (Nat.mul_dvd_mul_iff_left hg0).mp ?_
    calc Nat.gcd d L₁ * (d / Nat.gcd d L₁) = d := Nat.mul_div_cancel' hgd
      _ ∣ L₁ * L₂ := hd
      _ = Nat.gcd d L₁ * (L₁ / Nat.gcd d L₁) * L₂ := by rw [Nat.mul_div_cancel' hgL]
      _ = Nat.gcd d L₁ * (L₁ / Nat.gcd d L₁ * L₂) := by ring
  · intro a b hab haL hbL
    refine Nat.dvd_antisymm (Nat.dvd_gcd (hab ▸ Dvd.intro b rfl) haL) ?_
    have hcgb : Nat.Coprime (Nat.gcd d L₁) b := Nat.Coprime.coprime_dvd_left hgL
      (Nat.Coprime.coprime_dvd_right hbL hcop)
    refine Nat.Coprime.dvd_of_dvd_mul_right hcgb ?_
    rw [hab]
    exact hgd

/-- **B-2d′ — LEMMA 9's INNER identity at one `(m₁, m₂)`** (p.211): the `n`-sum over the window
at a single pair of `Q`-divisors.  Both `hb_lemma9_general` (all `m_i ∣ Q`) and `hb_lemma9_trunc`
(`m_i < q`) are a `Finset.sum_congr` of this row after the μ-sieve.

The route: the right-hand side's double integral is a window sum (above), so the whole right-hand
side is a window sum of five nested index sums after five `Finset.sum_comm`s; then, at each `n`,
the terms off the unique split `d = gcd(d, l₁ n) · (d / gcd(d, l₁ n))` vanish — `p.1 ∣ δ₁ ∣ l₁ n`
and `p.2 ∣ δ₂ ∣ l₂ n` force `p` to be that split — and at the split the four remaining index sums
factor into the two hyperbola expansions of `Λ′(l₁ n / m₁²)` and `Λ′(l₂ n / m₂²)` at
`e := d_i`.  The chained divisibility `m_i² d_i u_i ∣ l_i n ↔ u_i ∣ (l_i n / m_i²) / d_i` is
`Nat.dvd_div_iff_mul_dvd` twice, and `d_i ∣ l_i n / m_i²` needs `(m_i, d) = 1`, which is `hdQ`
with `m_i ∣ Q`.  `_hz` is unreferenced by this route and is mentioned, not edited. -/
theorem hb_lemma9_inner (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (_hz : 2 ≤ z)
    (F : HBForms) (x d : ℕ) (hdQ : Nat.Coprime d (hbQ χ z)) {m₁ m₂ : ℕ}
    (hm₁ : m₁ ∣ hbQ χ z) (hm₂ : m₂ ∣ hbQ χ z) :
    ∑ n ∈ (hbFormsWindow F q x).filter (fun n => d ∣ F.l₁ n * F.l₂ n),
        (if m₁ ^ 2 ∣ F.l₁ n ∧ m₂ ^ 2 ∣ F.l₂ n then
          LamPrime χ (F.l₁ n / m₁ ^ 2) * LamPrime χ (F.l₂ n / m₂ ^ 2) else 0)
      = ∑ p ∈ d.divisorsAntidiagonal,
            ∑ t₁ ∈ p.1.divisorsAntidiagonal, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal,
            ∑ t₂ ∈ p.2.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal,
              chiRe χ (t₁.1 * u₁.1) * chiRe χ (t₂.1 * u₂.1) * (μ u₁.1 : ℝ) * (μ u₂.1 : ℝ) *
              ∫ V₁ in Set.Ioi (((u₁.1 * u₁.2 : ℕ) : ℝ)⁻¹),
                (∫ V₂ in Set.Ioi (((u₂.1 * u₂.2 : ℕ) : ℝ)⁻¹),
                  bilinearS χ F x (m₁ ^ 2 * p.1 * u₁.1) (m₂ ^ 2 * p.2 * u₂.1) V₁ V₂ / V₂) / V₁ := by
  have _ := _hz
  rcases eq_or_ne d 0 with rfl | hd0
  · have hempty : (hbFormsWindow F q x).filter (fun n => (0 : ℕ) ∣ F.l₁ n * F.l₂ n) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n _
      rw [zero_dvd_iff]
      exact Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp (F.one_le_l₁ n))
        (Nat.one_le_iff_ne_zero.mp (F.one_le_l₂ n))
    rw [hempty, Finset.sum_empty, Nat.divisorsAntidiagonal_zero, Finset.sum_empty]
  -- the five-fold pull of the window sum
  have hpull : ∀ G : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → ℕ → ℝ,
      (∑ p ∈ d.divisorsAntidiagonal, ∑ t₁ ∈ p.1.divisorsAntidiagonal,
        ∑ u₁ ∈ t₁.2.divisorsAntidiagonal, ∑ t₂ ∈ p.2.divisorsAntidiagonal,
        ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, ∑ n ∈ hbFormsWindow F q x, G p t₁ u₁ t₂ u₂ n)
      = ∑ n ∈ hbFormsWindow F q x, ∑ p ∈ d.divisorsAntidiagonal,
          ∑ t₁ ∈ p.1.divisorsAntidiagonal, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal,
          ∑ t₂ ∈ p.2.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, G p t₁ u₁ t₂ u₂ n := by
    intro G
    calc ∑ p ∈ d.divisorsAntidiagonal, ∑ t₁ ∈ p.1.divisorsAntidiagonal,
            ∑ u₁ ∈ t₁.2.divisorsAntidiagonal, ∑ t₂ ∈ p.2.divisorsAntidiagonal,
            ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, ∑ n ∈ hbFormsWindow F q x, G p t₁ u₁ t₂ u₂ n
        = ∑ p ∈ d.divisorsAntidiagonal, ∑ t₁ ∈ p.1.divisorsAntidiagonal,
            ∑ u₁ ∈ t₁.2.divisorsAntidiagonal, ∑ t₂ ∈ p.2.divisorsAntidiagonal,
            ∑ n ∈ hbFormsWindow F q x, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, G p t₁ u₁ t₂ u₂ n :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ p ∈ d.divisorsAntidiagonal, ∑ t₁ ∈ p.1.divisorsAntidiagonal,
            ∑ u₁ ∈ t₁.2.divisorsAntidiagonal, ∑ n ∈ hbFormsWindow F q x,
            ∑ t₂ ∈ p.2.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, G p t₁ u₁ t₂ u₂ n :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ p ∈ d.divisorsAntidiagonal, ∑ t₁ ∈ p.1.divisorsAntidiagonal,
            ∑ n ∈ hbFormsWindow F q x, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal,
            ∑ t₂ ∈ p.2.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, G p t₁ u₁ t₂ u₂ n :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ p ∈ d.divisorsAntidiagonal, ∑ n ∈ hbFormsWindow F q x,
            ∑ t₁ ∈ p.1.divisorsAntidiagonal, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal,
            ∑ t₂ ∈ p.2.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, G p t₁ u₁ t₂ u₂ n :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  -- each index's double integral is a window sum
  have hstep1 : ∀ p t₁ u₁ t₂ u₂ : ℕ × ℕ, u₁ ∈ t₁.2.divisorsAntidiagonal →
      u₂ ∈ t₂.2.divisorsAntidiagonal →
      (∫ V₁ in Set.Ioi (((u₁.1 * u₁.2 : ℕ) : ℝ)⁻¹),
        (∫ V₂ in Set.Ioi (((u₂.1 * u₂.2 : ℕ) : ℝ)⁻¹),
          bilinearS χ F x (m₁ ^ 2 * p.1 * u₁.1) (m₂ ^ 2 * p.2 * u₂.1) V₁ V₂ / V₂) / V₁)
      = ∑ n ∈ hbFormsWindow F q x,
          (if m₁ ^ 2 * p.1 * u₁.1 ∣ F.l₁ n ∧ m₂ ^ 2 * p.2 * u₂.1 ∣ F.l₂ n then
            logDivChiSum χ (F.l₁ n / (m₁ ^ 2 * p.1 * u₁.1)) ((u₁.1 * u₁.2 : ℕ) : ℝ) *
            logDivChiSum χ (F.l₂ n / (m₂ ^ 2 * p.2 * u₂.1)) ((u₂.1 * u₂.2 : ℕ) : ℝ)
          else 0) := by
    have hone : ∀ (u : ℕ × ℕ) (N : ℕ), u ∈ N.divisorsAntidiagonal →
        (1 : ℝ) ≤ ((u.1 * u.2 : ℕ) : ℝ) := by
      intro u N hu
      obtain ⟨huu, hN⟩ := Nat.mem_divisorsAntidiagonal.mp hu
      have hne : u.1 * u.2 ≠ 0 := by rw [huu]; exact hN
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    intro p t₁ u₁ t₂ u₂ hu₁ hu₂
    have h1 := hone u₁ t₁.2 hu₁
    have h2 := hone u₂ t₂.2 hu₂
    have hp1 : (0:ℝ) < ((u₁.1 * u₁.2 : ℕ) : ℝ)⁻¹ := inv_pos.mpr (lt_of_lt_of_le one_pos h1)
    have hp2 : (0:ℝ) < ((u₂.1 * u₂.2 : ℕ) : ℝ)⁻¹ := inv_pos.mpr (lt_of_lt_of_le one_pos h2)
    have hq1 : ((u₁.1 * u₁.2 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le one_pos h1
    have hq2 : ((u₂.1 * u₂.2 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le one_pos h2
    rw [bilinear_double_integral χ F x (m₁ ^ 2 * p.1 * u₁.1) (m₂ ^ 2 * p.2 * u₂.1) hp1 hq1 hp2 hq2,
      inv_inv, inv_inv, Finset.sum_filter]
  -- the right-hand side, as a window sum of index sums
  have hR : (∑ p ∈ d.divisorsAntidiagonal, ∑ t₁ ∈ p.1.divisorsAntidiagonal,
        ∑ u₁ ∈ t₁.2.divisorsAntidiagonal, ∑ t₂ ∈ p.2.divisorsAntidiagonal,
        ∑ u₂ ∈ t₂.2.divisorsAntidiagonal,
          chiRe χ (t₁.1 * u₁.1) * chiRe χ (t₂.1 * u₂.1) * (μ u₁.1 : ℝ) * (μ u₂.1 : ℝ) *
          ∫ V₁ in Set.Ioi (((u₁.1 * u₁.2 : ℕ) : ℝ)⁻¹),
            (∫ V₂ in Set.Ioi (((u₂.1 * u₂.2 : ℕ) : ℝ)⁻¹),
              bilinearS χ F x (m₁ ^ 2 * p.1 * u₁.1) (m₂ ^ 2 * p.2 * u₂.1) V₁ V₂ / V₂) / V₁)
      = ∑ n ∈ hbFormsWindow F q x, ∑ p ∈ d.divisorsAntidiagonal,
          ∑ t₁ ∈ p.1.divisorsAntidiagonal, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal,
          ∑ t₂ ∈ p.2.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal,
            chiRe χ (t₁.1 * u₁.1) * chiRe χ (t₂.1 * u₂.1) * (μ u₁.1 : ℝ) * (μ u₂.1 : ℝ) *
            (if m₁ ^ 2 * p.1 * u₁.1 ∣ F.l₁ n ∧ m₂ ^ 2 * p.2 * u₂.1 ∣ F.l₂ n then
              logDivChiSum χ (F.l₁ n / (m₁ ^ 2 * p.1 * u₁.1)) ((u₁.1 * u₁.2 : ℕ) : ℝ) *
              logDivChiSum χ (F.l₂ n / (m₂ ^ 2 * p.2 * u₂.1)) ((u₂.1 * u₂.2 : ℕ) : ℝ)
            else 0) := by
    rw [← hpull (fun p t₁ u₁ t₂ u₂ n =>
      chiRe χ (t₁.1 * u₁.1) * chiRe χ (t₂.1 * u₂.1) * (μ u₁.1 : ℝ) * (μ u₂.1 : ℝ) *
        (if m₁ ^ 2 * p.1 * u₁.1 ∣ F.l₁ n ∧ m₂ ^ 2 * p.2 * u₂.1 ∣ F.l₂ n then
          logDivChiSum χ (F.l₁ n / (m₁ ^ 2 * p.1 * u₁.1)) ((u₁.1 * u₁.2 : ℕ) : ℝ) *
          logDivChiSum χ (F.l₂ n / (m₂ ^ 2 * p.2 * u₂.1)) ((u₂.1 * u₂.2 : ℕ) : ℝ)
        else 0))]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun t₁ _ =>
      Finset.sum_congr rfl fun u₁ hu₁ => Finset.sum_congr rfl fun t₂ _ =>
      Finset.sum_congr rfl fun u₂ hu₂ => ?_
    rw [hstep1 p t₁ u₁ t₂ u₂ hu₁ hu₂, Finset.mul_sum]
  rw [hR, Finset.sum_filter]
  -- the factorisation of a four-fold index sum into two two-fold ones
  have hfact : ∀ (A B : ℕ × ℕ → ℕ × ℕ → ℝ) (e₁ e₂ : ℕ),
      (∑ t₁ ∈ e₁.divisorsAntidiagonal, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal,
        ∑ t₂ ∈ e₂.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, A t₁ u₁ * B t₂ u₂)
      = (∑ t₁ ∈ e₁.divisorsAntidiagonal, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal, A t₁ u₁) *
        (∑ t₂ ∈ e₂.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal, B t₂ u₂) := by
    intro A B e₁ e₂
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t₁ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t₂ _ => ?_
    rw [Finset.mul_sum]
  -- pointwise in n
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hm : m₁ ^ 2 ∣ F.l₁ n ∧ m₂ ^ 2 ∣ F.l₂ n
  swap
  · rw [if_neg hm, ite_self]
    refine (Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun t₁ _ =>
      Finset.sum_eq_zero fun u₁ _ => Finset.sum_eq_zero fun t₂ _ =>
      Finset.sum_eq_zero fun u₂ _ => ?_).symm
    rw [if_neg, mul_zero]
    rintro ⟨hd₁, hd₂⟩
    exact hm ⟨((dvd_mul_right (m₁ ^ 2) p.1).mul_right u₁.1).trans hd₁,
      ((dvd_mul_right (m₂ ^ 2) p.2).mul_right u₂.1).trans hd₂⟩
  by_cases hdl : d ∣ F.l₁ n * F.l₂ n
  swap
  · rw [if_neg hdl]
    refine (Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun t₁ _ =>
      Finset.sum_eq_zero fun u₁ _ => Finset.sum_eq_zero fun t₂ _ =>
      Finset.sum_eq_zero fun u₂ _ => ?_).symm
    rw [if_neg, mul_zero]
    rintro ⟨hd₁, hd₂⟩
    refine hdl ?_
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1]
    exact mul_dvd_mul (((dvd_mul_left p.1 (m₁ ^ 2)).mul_right u₁.1).trans hd₁)
      (((dvd_mul_left p.2 (m₂ ^ 2)).mul_right u₂.1).trans hd₂)
  rw [if_pos hdl, if_pos hm]
  obtain ⟨hm1, hm2⟩ := hm
  obtain ⟨hg1, hgd, hg2, huniq⟩ := inner_split (F.coprime_l n) hdl hd0
  -- the coprimality of each `m_i` with the corresponding half of `d`
  have hcop₁ : Nat.Coprime (m₁ ^ 2) (Nat.gcd d (F.l₁ n)) :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left d (F.l₁ n))
      (Nat.Coprime.coprime_dvd_right hm₁ hdQ).symm)
  have hcop₂ : Nat.Coprime (m₂ ^ 2) (d / Nat.gcd d (F.l₁ n)) :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.coprime_dvd_right
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d (F.l₁ n)))
      (Nat.Coprime.coprime_dvd_right hm₂ hdQ).symm)
  have hmd₁ : m₁ ^ 2 * Nat.gcd d (F.l₁ n) ∣ F.l₁ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop₁ hm1 hg1
  have hmd₂ : m₂ ^ 2 * (d / Nat.gcd d (F.l₁ n)) ∣ F.l₂ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop₂ hm2 hg2
  have hL₁ : Nat.gcd d (F.l₁ n) ∣ F.l₁ n / m₁ ^ 2 := (Nat.dvd_div_iff_mul_dvd hm1).mpr hmd₁
  have hL₂ : d / Nat.gcd d (F.l₁ n) ∣ F.l₂ n / m₂ ^ 2 := (Nat.dvd_div_iff_mul_dvd hm2).mpr hmd₂
  -- only the split `d = gcd(d, l₁ n) · (d / gcd(d, l₁ n))` survives
  refine Eq.trans ?_ (Finset.sum_eq_single_of_mem
    (Nat.gcd d (F.l₁ n), d / Nat.gcd d (F.l₁ n))
    (Nat.mem_divisorsAntidiagonal.mpr ⟨hgd, hd0⟩) ?_).symm
  swap
  · intro b hb hne
    refine Finset.sum_eq_zero fun t₁ _ => Finset.sum_eq_zero fun u₁ _ =>
      Finset.sum_eq_zero fun t₂ _ => Finset.sum_eq_zero fun u₂ _ => ?_
    rw [if_neg, mul_zero]
    rintro ⟨hd₁, hd₂⟩
    refine hne ?_
    have hb1 : b.1 ∣ F.l₁ n := ((dvd_mul_left b.1 (m₁ ^ 2)).mul_right u₁.1).trans hd₁
    have hb2 : b.2 ∣ F.l₂ n := ((dvd_mul_left b.2 (m₂ ^ 2)).mul_right u₂.1).trans hd₂
    have hbd := (Nat.mem_divisorsAntidiagonal.mp hb).1
    have hfst : b.1 = Nat.gcd d (F.l₁ n) := huniq b.1 b.2 hbd hb1 hb2
    refine Prod.ext hfst ?_
    have hpos : 0 < Nat.gcd d (F.l₁ n) := Nat.pos_of_ne_zero (fun h0 =>
      hd0 (Nat.eq_zero_of_gcd_eq_zero_left h0))
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [hgd, ← hfst, hbd]
  -- the two hyperbola expansions, and the factorisation
  rw [LamPrime_eq_hyperbola χ hsq hL₁, LamPrime_eq_hyperbola χ hsq hL₂, ← hfact]
  refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun u₁ _ =>
    Finset.sum_congr rfl fun t₂ _ => Finset.sum_congr rfl fun u₂ _ => ?_
  -- the two guards agree, and so do the two logarithmic sums
  have harg₁ : F.l₁ n / (m₁ ^ 2 * Nat.gcd d (F.l₁ n) * u₁.1)
      = F.l₁ n / m₁ ^ 2 / (Nat.gcd d (F.l₁ n) * u₁.1) := by
    rw [Nat.div_div_eq_div_mul, mul_assoc]
  have harg₂ : F.l₂ n / (m₂ ^ 2 * (d / Nat.gcd d (F.l₁ n)) * u₂.1)
      = F.l₂ n / m₂ ^ 2 / (d / Nat.gcd d (F.l₁ n) * u₂.1) := by
    rw [Nat.div_div_eq_div_mul, mul_assoc]
  have hguard₁ : (m₁ ^ 2 * Nat.gcd d (F.l₁ n) * u₁.1 ∣ F.l₁ n)
      ↔ (u₁.1 ∣ F.l₁ n / m₁ ^ 2 / Nat.gcd d (F.l₁ n)) := by
    rw [Nat.dvd_div_iff_mul_dvd hL₁, Nat.div_div_eq_div_mul] at *
    rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_trans (dvd_mul_right _ _) hmd₁), mul_assoc]
  have hguard₂ : (m₂ ^ 2 * (d / Nat.gcd d (F.l₁ n)) * u₂.1 ∣ F.l₂ n)
      ↔ (u₂.1 ∣ F.l₂ n / m₂ ^ 2 / (d / Nat.gcd d (F.l₁ n))) := by
    rw [Nat.dvd_div_iff_mul_dvd hL₂, Nat.div_div_eq_div_mul] at *
    rw [Nat.dvd_div_iff_mul_dvd (Nat.dvd_trans (dvd_mul_right _ _) hmd₂), mul_assoc]
  dsimp only
  by_cases hP : m₁ ^ 2 * Nat.gcd d (F.l₁ n) * u₁.1 ∣ F.l₁ n
  · by_cases hQ : m₂ ^ 2 * (d / Nat.gcd d (F.l₁ n)) * u₂.1 ∣ F.l₂ n
    · rw [if_pos (And.intro hP hQ), if_pos (hguard₁.mp hP), if_pos (hguard₂.mp hQ), harg₁, harg₂]
      ring
    · rw [if_neg (fun h : _ ∧ _ => hQ h.2), if_neg (fun h => hQ (hguard₂.mpr h)),
        mul_zero, mul_zero]
  · rw [if_neg (fun h : _ ∧ _ => hP h.1), if_neg (fun h => hP (hguard₁.mpr h)),
      zero_mul, mul_zero]

/-- **B-2d — LEMMA 9, general `d`, EXACT** (p.211): for `(d, Q) = 1`, the sieve datum's `S d`
is the double `Q`-divisor sum of the inner identity — every `m_i ∣ Q`, no truncation.  The μ-sieve
expands both `Λ*` factors, `Finset.sum_mul_sum` merges the two `m`-sums, the `n`-sum moves outside
them by two `Finset.sum_comm`s, and B-2d′ closes each `(m₁, m₂)` term. -/
theorem hb_lemma9_general (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (F : HBForms) (x d : ℕ) (hdQ : Nat.Coprime d (hbQ χ z)) :
    (hbDataForms χ hsq hz F x).S d
      = ∑ m₁ ∈ (hbQ χ z).divisors, ∑ m₂ ∈ (hbQ χ z).divisors, (μ m₁ : ℝ) * (μ m₂ : ℝ) *
          ∑ p ∈ d.divisorsAntidiagonal,
            ∑ t₁ ∈ p.1.divisorsAntidiagonal, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal,
            ∑ t₂ ∈ p.2.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal,
              chiRe χ (t₁.1 * u₁.1) * chiRe χ (t₂.1 * u₂.1) * (μ u₁.1 : ℝ) * (μ u₂.1 : ℝ) *
              ∫ V₁ in Set.Ioi (((u₁.1 * u₁.2 : ℕ) : ℝ)⁻¹),
                (∫ V₂ in Set.Ioi (((u₂.1 * u₂.2 : ℕ) : ℝ)⁻¹),
                  bilinearS χ F x (m₁ ^ 2 * p.1 * u₁.1) (m₂ ^ 2 * p.2 * u₂.1) V₁ V₂ / V₂) / V₁ := by
  rw [hbDataForms_S χ hsq hz F x d]
  have hpt : ∀ n ∈ (hbFormsWindow F q x).filter (fun n => d ∣ F.l₁ n * F.l₂ n),
      LamStar χ z (F.l₁ n) * LamStar χ z (F.l₂ n)
      = ∑ m₁ ∈ (hbQ χ z).divisors, ∑ m₂ ∈ (hbQ χ z).divisors,
          ((μ m₁ : ℝ) * (μ m₂ : ℝ)) *
            (if m₁ ^ 2 ∣ F.l₁ n ∧ m₂ ^ 2 ∣ F.l₂ n then
              LamPrime χ (F.l₁ n / m₁ ^ 2) * LamPrime χ (F.l₂ n / m₂ ^ 2) else 0) := by
    intro n _
    rw [LamStar_eq_moebius_hbQ χ hsq z (F.l₁ n), LamStar_eq_moebius_hbQ χ hsq z (F.l₂ n),
      Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
    by_cases h1 : m₁ ^ 2 ∣ F.l₁ n
    · by_cases h2 : m₂ ^ 2 ∣ F.l₂ n
      · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]; ring
      · rw [if_neg h2, if_neg (fun h : _ ∧ _ => h2 h.2), mul_zero, mul_zero]
    · rw [if_neg h1, if_neg (fun h : _ ∧ _ => h1 h.1), zero_mul, mul_zero]
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₂ hm₂ => ?_
  rw [← Finset.mul_sum, hb_lemma9_inner χ hsq hz F x d hdQ (Nat.mem_divisors.mp hm₁).1
    (Nat.mem_divisors.mp hm₂).1]

/-- **B-2t′ — LEMMA 9 TRUNCATED at `m_i < q`, EXACT for `Λ*_{<q}`** (p.211): HB's own Lemma 9
display, without its `O(x^{1+ε}q^{−1})` — that term is the `Λ*`-level tail `S(d) − S_{<q}(d)`,
paid at p.210 and handed off, not established here.  The proof is B-2d's with one extra step:
`LamStarTrunc`'s index set `{m ∣ Q : m² ∣ l_i n ∧ m < q}` is re-read by `Finset.filter_filter` as
the `m² ∣ l_i n` part of `{m ∣ Q : m < q}`, so the outer `m`-sums are over the truncated divisor
set and the `m² ∣ l_i n` conjunct becomes the same `if` B-2d′ consumes.  `_hz` IS spent here — it
is what B-2d′ asks for. -/
theorem hb_lemma9_trunc (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (_hz : 2 ≤ z)
    (F : HBForms) (x d : ℕ) (hdQ : Nat.Coprime d (hbQ χ z)) :
    ∑ n ∈ (hbFormsWindow F q x).filter (fun n => d ∣ F.l₁ n * F.l₂ n),
        LamStarTrunc χ z (F.l₁ n) * LamStarTrunc χ z (F.l₂ n)
      = ∑ m₁ ∈ (hbQ χ z).divisors.filter (· < q), ∑ m₂ ∈ (hbQ χ z).divisors.filter (· < q),
          (μ m₁ : ℝ) * (μ m₂ : ℝ) *
          ∑ p ∈ d.divisorsAntidiagonal,
            ∑ t₁ ∈ p.1.divisorsAntidiagonal, ∑ u₁ ∈ t₁.2.divisorsAntidiagonal,
            ∑ t₂ ∈ p.2.divisorsAntidiagonal, ∑ u₂ ∈ t₂.2.divisorsAntidiagonal,
              chiRe χ (t₁.1 * u₁.1) * chiRe χ (t₂.1 * u₂.1) * (μ u₁.1 : ℝ) * (μ u₂.1 : ℝ) *
              ∫ V₁ in Set.Ioi (((u₁.1 * u₁.2 : ℕ) : ℝ)⁻¹),
                (∫ V₂ in Set.Ioi (((u₂.1 * u₂.2 : ℕ) : ℝ)⁻¹),
                  bilinearS χ F x (m₁ ^ 2 * p.1 * u₁.1) (m₂ ^ 2 * p.2 * u₂.1) V₁ V₂ / V₂) / V₁ := by
  have hset : ∀ N : ℕ, (hbQ χ z).divisors.filter (fun m => m ^ 2 ∣ N ∧ m < q)
      = ((hbQ χ z).divisors.filter (fun m => m < q)).filter (fun m => m ^ 2 ∣ N) := by
    intro N
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun m _ => and_comm
  have hpt : ∀ n ∈ (hbFormsWindow F q x).filter (fun n => d ∣ F.l₁ n * F.l₂ n),
      LamStarTrunc χ z (F.l₁ n) * LamStarTrunc χ z (F.l₂ n)
      = ∑ m₁ ∈ (hbQ χ z).divisors.filter (fun m => m < q),
          ∑ m₂ ∈ (hbQ χ z).divisors.filter (fun m => m < q),
          ((μ m₁ : ℝ) * (μ m₂ : ℝ)) *
            (if m₁ ^ 2 ∣ F.l₁ n ∧ m₂ ^ 2 ∣ F.l₂ n then
              LamPrime χ (F.l₁ n / m₁ ^ 2) * LamPrime χ (F.l₂ n / m₂ ^ 2) else 0) := by
    intro n _
    rw [LamStarTrunc, LamStarTrunc, hset (F.l₁ n), hset (F.l₂ n),
      Finset.sum_filter (fun m => m ^ 2 ∣ F.l₁ n)
        (fun m => (μ m : ℝ) * LamPrime χ (F.l₁ n / m ^ 2)),
      Finset.sum_filter (fun m => m ^ 2 ∣ F.l₂ n)
        (fun m => (μ m : ℝ) * LamPrime χ (F.l₂ n / m ^ 2)),
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
    by_cases h1 : m₁ ^ 2 ∣ F.l₁ n
    · by_cases h2 : m₂ ^ 2 ∣ F.l₂ n
      · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]; ring
      · rw [if_neg h2, if_neg (fun h : _ ∧ _ => h2 h.2), mul_zero, mul_zero]
    · rw [if_neg h1, if_neg (fun h : _ ∧ _ => h1 h.1), zero_mul, mul_zero]
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₂ hm₂ => ?_
  rw [← Finset.mul_sum, hb_lemma9_inner χ hsq _hz F x d hdQ
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hm₁).1).1
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hm₂).1).1]

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

/-! ### B-3a's cell-index helpers — one dyadic index, one unit representative -/

/-- **Each `v` in `(V, V·2^J]` lies in exactly one dyadic cell `(V·2^j, 2·(V·2^j)]`, `j < J`.**
Both the `v`-cells (at `V = V_i`) and the `w`-cells (at `V = 1/2`, where the cells are
`(2^k/2, 2^k]`) are instances of this one statement. -/
theorem exists_unique_dyadic {V v : ℝ} (hV : 0 < V) {J : ℕ} (h1 : V < v) (h2 : v ≤ V * 2 ^ J) :
    ∃! j : ℕ, j < J ∧ V * 2 ^ j < v ∧ v ≤ 2 * (V * 2 ^ j) := by
  classical
  have hmono : ∀ i j : ℕ, i ≤ j → V * 2 ^ i ≤ V * 2 ^ j := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) hV.le
  set P : ℕ → Prop := fun j => V * 2 ^ j < v with hP
  have hP0 : P 0 := by simpa [hP] using h1
  have hPJ : ¬ P J := by simpa [hP] using h2
  set j := Nat.findGreatest P J with hj
  have hPj : P j := Nat.findGreatest_spec (Nat.zero_le J) hP0
  have hjJ : j < J := by
    rcases lt_or_eq_of_le (Nat.findGreatest_le (P := P) J) with h | h
    · exact h
    · exact absurd (h ▸ hPj) hPJ
  have htop : v ≤ 2 * (V * 2 ^ j) := by
    by_contra hc
    have hnext : P (j + 1) := by
      have he : V * 2 ^ (j + 1) = 2 * (V * 2 ^ j) := by ring
      have hlt : V * 2 ^ (j + 1) < v := by rw [he]; exact lt_of_not_ge hc
      exact hlt
    exact Nat.findGreatest_is_greatest (lt_add_one j) (by omega) hnext
  refine ⟨j, ⟨hjJ, hPj, htop⟩, ?_⟩
  rintro j' ⟨_, h1', h2'⟩
  by_contra hne
  rcases Nat.lt_or_ge j' j with hlt | hge
  · have : v ≤ V * 2 ^ j := le_trans h2' (by
      have he : (2 : ℝ) * (V * 2 ^ j') = V * 2 ^ (j' + 1) := by ring
      rw [he]; exact hmono (j' + 1) j hlt)
    exact absurd hPj (not_lt.mpr this)
  · have hgt : j < j' := by omega
    have : v ≤ V * 2 ^ j' := le_trans htop (by
      have he : (2 : ℝ) * (V * 2 ^ j) = V * 2 ^ (j + 1) := by ring
      rw [he]; exact hmono (j + 1) j' hgt)
    exact absurd h1' (not_lt.mpr this)

/-- The unit representative of `v` modulo `q`, in `[1, q]` — the fibre map B-3a's residue split
runs on: `v % q`, except that `0` is represented by `q`. -/
def unitRep (q v : ℕ) : ℕ := if v % q = 0 then q else v % q

theorem unitRep_modEq (q v : ℕ) : v ≡ unitRep q v [MOD q] := by
  unfold unitRep
  split
  · rename_i h
    have he : v % q = q % q := by rw [h, Nat.mod_self]
    exact he
  · exact (Nat.mod_modEq v q).symm

theorem unitRep_mem_Icc {q v : ℕ} (hq : 0 < q) : unitRep q v ∈ Finset.Icc 1 q := by
  rw [Finset.mem_Icc]
  unfold unitRep
  split
  · exact ⟨hq, le_rfl⟩
  · rename_i h
    exact ⟨Nat.one_le_iff_ne_zero.mpr h, (Nat.mod_lt v hq).le⟩

theorem unitRep_coprime {q v : ℕ} (hv : Nat.Coprime v q) :
    Nat.Coprime (unitRep q v) q := by
  by_contra hcon
  obtain ⟨p, hp, hpr, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
  have h1 : v ≡ unitRep q v [MOD p] := Nat.ModEq.of_dvd hpq (unitRep_modEq q v)
  have h2 : unitRep q v ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hpr
  have h3 : p ∣ v := (Nat.modEq_zero_iff_dvd).mp (h1.trans h2)
  have h4 : p ∣ Nat.gcd v q := Nat.dvd_gcd h3 hpq
  rw [show Nat.gcd v q = 1 from hv] at h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

theorem unitRep_unique {q v a : ℕ} (hq : 0 < q) (ha : a ∈ Finset.Icc 1 q)
    (h : v ≡ a [MOD q]) : a = unitRep q v := by
  rw [Finset.mem_Icc] at ha
  have hmod : v % q = a % q := h
  unfold unitRep
  split
  · rename_i h0
    rw [h0] at hmod
    rcases Nat.lt_or_ge a q with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    · omega
  · rename_i h0
    rcases Nat.lt_or_ge a q with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    · have hae : a = q := le_antisymm ha.2 hge
      rw [hae, Nat.mod_self] at hmod
      omega

/-- Periodicity of `chiRe`: the reason a cell's residue `b` may stand in for `w`. -/
theorem chiRe_modEq (χ : DirichletCharacter ℂ q) {m n : ℕ} (h : m ≡ n [MOD q]) :
    chiRe χ m = chiRe χ n := by
  unfold chiRe
  rw [(ZMod.natCast_eq_natCast_iff m n q).mpr h]

/-- **The per-`N` cell identity** — the content of (5.18) at one form value.  Every divisor pair
`(w, v)` of `N` with `v > V` lies in exactly ONE dyadic cell `(V·2^j, 2V·2^j] × (2^k/2, 2^k]`
with `j < J`, `k < K`, and in exactly one pair of unit residue classes mod `q`; and `χ(w)` there
equals `χ(b)`.  `Coprime N q` is what makes the residues units; `hJ`/`hK` are exactly the covers.
-/
theorem truncChiSum_eq_sum_cells (χ : DirichletCharacter ℂ q) (hq : 0 < q) {N : ℕ}
    (hNq : Nat.Coprime N q) {V : ℝ} (hV : 0 < V) (J K : ℕ)
    (hJ : (N : ℝ) ≤ V * 2 ^ J) (hK : (N : ℝ) ≤ 2 ^ K / 2) :
    truncChiSum χ N V
      = ∑ j ∈ range J, ∑ k ∈ range K,
        ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ b ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
          chiRe χ b * ((N.divisorsAntidiagonal.filter (fun p =>
            V * 2 ^ j < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (V * 2 ^ j) ∧
            2 ^ k / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * (2 ^ k / 2) ∧
            p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q])).card : ℝ) := by
  classical
  -- ① every summand of the right side is an indicator sum over the whole antidiagonal
  have hcard : ∀ j k a b : ℕ,
      chiRe χ b * ((N.divisorsAntidiagonal.filter (fun p =>
          V * 2 ^ j < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (V * 2 ^ j) ∧
          2 ^ k / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * (2 ^ k / 2) ∧
          p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q])).card : ℝ)
        = ∑ p ∈ N.divisorsAntidiagonal,
            (if V * 2 ^ j < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (V * 2 ^ j) ∧
                2 ^ k / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * (2 ^ k / 2) ∧
                p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q] then chiRe χ b else 0) := by
    intro j k a b
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.mul_sum, mul_ite, mul_one, mul_zero]
  -- ② the pointwise identity on one divisor pair
  have key : ∀ p ∈ N.divisorsAntidiagonal,
      (∑ j ∈ range J, ∑ k ∈ range K,
        ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ b ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
          (if V * 2 ^ j < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (V * 2 ^ j) ∧
              2 ^ k / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * (2 ^ k / 2) ∧
              p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q] then chiRe χ b else 0))
        = (if V < (p.2 : ℝ) then chiRe χ p.1 else 0) := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨hmul, hNne⟩ := hp
    have hwd : p.1 ∣ N := ⟨p.2, hmul.symm⟩
    have hvd : p.2 ∣ N := ⟨p.1, by rw [← hmul]; ring⟩
    have hNpos : 0 < N := Nat.pos_of_ne_zero hNne
    have hwpos : 0 < p.1 := Nat.pos_of_dvd_of_pos hwd hNpos
    have hwle : (p.1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_dvd hNpos hwd
    have hvle : (p.2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_dvd hNpos hvd
    by_cases hVv : V < (p.2 : ℝ)
    · rw [if_pos hVv]
      -- the unique dyadic index of `v`
      obtain ⟨j₀, ⟨hj₀J, hj₀1, hj₀2⟩, hj₀u⟩ :=
        exists_unique_dyadic hV hVv (le_trans hvle hJ)
      -- the unique dyadic index of `w`, at `V = 1/2`
      have hw1 : (1 : ℝ) / 2 < (p.1 : ℝ) := by
        have h1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hwpos
        linarith
      have hwK : (p.1 : ℝ) ≤ 1 / 2 * 2 ^ K := by
        have h1 : (p.1 : ℝ) ≤ (2 : ℝ) ^ K / 2 := le_trans hwle hK
        linarith
      obtain ⟨k₀, ⟨hk₀K, hk₀1, hk₀2⟩, hk₀u⟩ :=
        exists_unique_dyadic (by norm_num : (0:ℝ) < 1/2) hw1 hwK
      have hk₀1' : (2 : ℝ) ^ k₀ / 2 < (p.1 : ℝ) := by linarith
      have hk₀2' : (p.1 : ℝ) ≤ 2 * ((2 : ℝ) ^ k₀ / 2) := by linarith
      -- the unique unit residues
      have hvq : Nat.Coprime p.2 q := Nat.Coprime.coprime_dvd_left hvd hNq
      have hwq : Nat.Coprime p.1 q := Nat.Coprime.coprime_dvd_left hwd hNq
      have ha₀ : unitRep q p.2 ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q) :=
        Finset.mem_filter.mpr ⟨unitRep_mem_Icc hq, unitRep_coprime hvq⟩
      have hb₀ : unitRep q p.1 ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q) :=
        Finset.mem_filter.mpr ⟨unitRep_mem_Icc hq, unitRep_coprime hwq⟩
      -- collapse the four sums
      rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_range.mpr hj₀J) ?_,
        Finset.sum_eq_single_of_mem k₀ (Finset.mem_range.mpr hk₀K) ?_,
        Finset.sum_eq_single_of_mem (unitRep q p.2) ha₀ ?_,
        Finset.sum_eq_single_of_mem (unitRep q p.1) hb₀ ?_,
        if_pos ⟨hj₀1, hj₀2, hk₀1', hk₀2', unitRep_modEq q p.2, unitRep_modEq q p.1⟩]
      · exact (chiRe_modEq χ (unitRep_modEq q p.1)).symm
      · intro b hb hbne
        refine if_neg (fun hc => hbne ?_)
        exact unitRep_unique hq (Finset.mem_filter.mp hb).1 hc.2.2.2.2.2
      · intro a ha hane
        refine Finset.sum_eq_zero (fun b _ => if_neg (fun hc => hane ?_))
        exact unitRep_unique hq (Finset.mem_filter.mp ha).1 hc.2.2.2.2.1
      · intro k hk hkne
        refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ =>
          if_neg (fun hc => hkne ?_)))
        refine hk₀u k ⟨Finset.mem_range.mp hk, ?_, ?_⟩
        · linarith [hc.2.2.1]
        · linarith [hc.2.2.2.1]
      · intro j hj hjne
        refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun a _ =>
          Finset.sum_eq_zero (fun b _ => if_neg (fun hc => hjne ?_))))
        exact hj₀u j ⟨Finset.mem_range.mp hj, hc.1, hc.2.1⟩
    · rw [if_neg hVv]
      refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun k _ =>
        Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => if_neg (fun hc => ?_)))))
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hle : V ≤ V * 2 ^ j := by nlinarith
      exact hVv (lt_of_le_of_lt hle hc.1)
  -- ③ assemble
  calc truncChiSum χ N V
      = ∑ p ∈ N.divisorsAntidiagonal, (if V < (p.2 : ℝ) then chiRe χ p.1 else 0) := rfl
    _ = ∑ p ∈ N.divisorsAntidiagonal, ∑ j ∈ range J, ∑ k ∈ range K,
          ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
          ∑ b ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
            (if V * 2 ^ j < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (V * 2 ^ j) ∧
                2 ^ k / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * (2 ^ k / 2) ∧
                p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q] then chiRe χ b else 0) :=
        (Finset.sum_congr rfl key).symm
    _ = ∑ j ∈ range J, ∑ k ∈ range K,
          ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
          ∑ b ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
          ∑ p ∈ N.divisorsAntidiagonal,
            (if V * 2 ^ j < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (V * 2 ^ j) ∧
                2 ^ k / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * (2 ^ k / 2) ∧
                p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q] then chiRe χ b else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))))
        exact (hcard j k a b).symm

/-- A residue class of a unit is a unit. -/
theorem coprime_of_modEq {m a : ℕ} (h : m ≡ a [MOD q]) (ha : Nat.Coprime a q) :
    Nat.Coprime m q := by
  by_contra hcon
  obtain ⟨p, hp, hpm, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
  have h1 : m ≡ a [MOD p] := Nat.ModEq.of_dvd hpq h
  have h2 : m ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hpm
  have h3 : p ∣ a := (Nat.modEq_zero_iff_dvd).mp (h1.symm.trans h2)
  have h4 : p ∣ Nat.gcd a q := Nat.dvd_gcd h3 hpq
  rw [show Nat.gcd a q = 1 from ha] at h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

/-- **The out-of-window cells carry no mass.**  `cellCount` runs over the BARE `Ioc` while the
carrier runs over the `(l, q) = 1` window; under `(δ, q) = 1` the gap between them is empty.
A non-empty cell puts `v` and `w` in UNIT classes mod `q`, so `(N/δ, q) = 1` and hence
`(N, q) = 1`: a cell at an `N` NOT coprime to `q` is empty. -/
theorem cell_card_eq_zero_of_not_coprime {δ N : ℕ} (hδq : Nat.Coprime δ q) (hd : δ ∣ N)
    (hNq : ¬ Nat.Coprime N q) (R S : ℝ) {a b : ℕ}
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b q) :
    ((N / δ).divisorsAntidiagonal.filter (fun p =>
        R < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R ∧ S < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * S ∧
        p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q])).card = 0 := by
  by_contra hc
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hu
  refine hNq ?_
  have hN : Nat.Coprime (N / δ) q := by
    rw [← hu.1.1]
    exact (coprime_of_modEq hu.2.2.2.2.2.2 hb).mul_left (coprime_of_modEq hu.2.2.2.2.2.1 ha)
  have he : δ * (N / δ) = N := Nat.mul_div_cancel' hd
  rw [← he]
  exact hδq.mul_left hN

/-- Off the window, one of the two form values shares a factor with `q`. -/
theorem not_coprime_of_not_mem_window (F : HBForms) (x : ℕ) {n : ℕ}
    (hn : n ∈ Finset.Ioc x (2 * x)) (hnw : n ∉ hbFormsWindow F q x) :
    ¬ Nat.Coprime (F.l₁ n) q ∨ ¬ Nat.Coprime (F.l₂ n) q := by
  by_cases h1 : Nat.Coprime (F.l₁ n) q
  · by_cases h2 : Nat.Coprime (F.l₂ n) q
    · exfalso
      refine hnw ?_
      simp only [hbFormsWindow, Finset.mem_filter]
      exact ⟨hn, h1.mul_left h2⟩
    · exact Or.inr h2
  · exact Or.inl h1

/-! ### Two `Finset.sum_comm` chains, stated once and used by B-3a's assembly -/

/-- Pulling the innermost of nine nested sums out to the front. -/
theorem sum_pull₈ {α : Type*} (S₁ S₂ S₃ S₄ S₅ S₆ S₇ S₈ : Finset ℕ) (t : Finset α)
    (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → α → ℝ) :
    (∑ i₁ ∈ S₁, ∑ i₂ ∈ S₂, ∑ i₃ ∈ S₃, ∑ i₄ ∈ S₄, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇,
      ∑ i₈ ∈ S₈, ∑ n ∈ t, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n)
      = ∑ n ∈ t, ∑ i₁ ∈ S₁, ∑ i₂ ∈ S₂, ∑ i₃ ∈ S₃, ∑ i₄ ∈ S₄, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆,
          ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n := by
  have h1 : ∀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ℕ,
      (∑ i₈ ∈ S₈, ∑ n ∈ t, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n)
        = ∑ n ∈ t, ∑ i₈ ∈ S₈, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n :=
    fun _ _ _ _ _ _ _ => Finset.sum_comm
  have h2 : ∀ i₁ i₂ i₃ i₄ i₅ i₆ : ℕ,
      (∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈, ∑ n ∈ t, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n)
        = ∑ n ∈ t, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n := by
    intro i₁ i₂ i₃ i₄ i₅ i₆
    rw [Finset.sum_congr rfl (fun i₇ _ => h1 i₁ i₂ i₃ i₄ i₅ i₆ i₇), Finset.sum_comm]
  have h3 : ∀ i₁ i₂ i₃ i₄ i₅ : ℕ,
      (∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈, ∑ n ∈ t, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n)
        = ∑ n ∈ t, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n := by
    intro i₁ i₂ i₃ i₄ i₅
    rw [Finset.sum_congr rfl (fun i₆ _ => h2 i₁ i₂ i₃ i₄ i₅ i₆), Finset.sum_comm]
  have h4 : ∀ i₁ i₂ i₃ i₄ : ℕ,
      (∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈, ∑ n ∈ t, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n)
        = ∑ n ∈ t, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈,
            g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n := by
    intro i₁ i₂ i₃ i₄
    rw [Finset.sum_congr rfl (fun i₅ _ => h3 i₁ i₂ i₃ i₄ i₅), Finset.sum_comm]
  have h5 : ∀ i₁ i₂ i₃ : ℕ,
      (∑ i₄ ∈ S₄, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈, ∑ n ∈ t,
        g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n)
        = ∑ n ∈ t, ∑ i₄ ∈ S₄, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈,
            g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n := by
    intro i₁ i₂ i₃
    rw [Finset.sum_congr rfl (fun i₄ _ => h4 i₁ i₂ i₃ i₄), Finset.sum_comm]
  have h6 : ∀ i₁ i₂ : ℕ,
      (∑ i₃ ∈ S₃, ∑ i₄ ∈ S₄, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈, ∑ n ∈ t,
        g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n)
        = ∑ n ∈ t, ∑ i₃ ∈ S₃, ∑ i₄ ∈ S₄, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈,
            g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n := by
    intro i₁ i₂
    rw [Finset.sum_congr rfl (fun i₃ _ => h5 i₁ i₂ i₃), Finset.sum_comm]
  have h7 : ∀ i₁ : ℕ,
      (∑ i₂ ∈ S₂, ∑ i₃ ∈ S₃, ∑ i₄ ∈ S₄, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇, ∑ i₈ ∈ S₈,
        ∑ n ∈ t, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n)
        = ∑ n ∈ t, ∑ i₂ ∈ S₂, ∑ i₃ ∈ S₃, ∑ i₄ ∈ S₄, ∑ i₅ ∈ S₅, ∑ i₆ ∈ S₆, ∑ i₇ ∈ S₇,
            ∑ i₈ ∈ S₈, g i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ n := by
    intro i₁
    rw [Finset.sum_congr rfl (fun i₂ _ => h6 i₁ i₂), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i₁ _ => h7 i₁), Finset.sum_comm]

/-- Swapping a block of two outer sums past a block of two inner sums. -/
theorem sum_swap_two_two (S₁ S₂ T₁ T₂ : Finset ℕ) (g : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ x ∈ S₁, ∑ y ∈ S₂, ∑ u ∈ T₁, ∑ v ∈ T₂, g x y u v)
      = ∑ u ∈ T₁, ∑ v ∈ T₂, ∑ x ∈ S₁, ∑ y ∈ S₂, g x y u v := by
  calc (∑ x ∈ S₁, ∑ y ∈ S₂, ∑ u ∈ T₁, ∑ v ∈ T₂, g x y u v)
      = ∑ x ∈ S₁, ∑ u ∈ T₁, ∑ y ∈ S₂, ∑ v ∈ T₂, g x y u v :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ u ∈ T₁, ∑ x ∈ S₁, ∑ y ∈ S₂, ∑ v ∈ T₂, g x y u v := Finset.sum_comm
    _ = ∑ u ∈ T₁, ∑ x ∈ S₁, ∑ v ∈ T₂, ∑ y ∈ S₂, g x y u v :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
    _ = ∑ u ∈ T₁, ∑ v ∈ T₂, ∑ x ∈ S₁, ∑ y ∈ S₂, g x y u v :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- The regrouping B-3a's assembly runs: eight cell indices and one `n`, into two blocks of
four with the `n`-sum outside. -/
theorem sum_cells_mul {α : Type*} (A B U : Finset ℕ) (t : Finset α)
    (P Q : ℕ → ℕ → ℕ → ℕ → α → ℝ) :
    (∑ j₁ ∈ A, ∑ k₁ ∈ B, ∑ j₂ ∈ A, ∑ k₂ ∈ B, ∑ a₁ ∈ U, ∑ b₁ ∈ U, ∑ a₂ ∈ U, ∑ b₂ ∈ U,
      ∑ n ∈ t, P j₁ k₁ a₁ b₁ n * Q j₂ k₂ a₂ b₂ n)
      = ∑ n ∈ t, (∑ j₁ ∈ A, ∑ k₁ ∈ B, ∑ a₁ ∈ U, ∑ b₁ ∈ U, P j₁ k₁ a₁ b₁ n) *
          (∑ j₂ ∈ A, ∑ k₂ ∈ B, ∑ a₂ ∈ U, ∑ b₂ ∈ U, Q j₂ k₂ a₂ b₂ n) := by
  rw [sum_pull₈ A B A B U U U U t
    (fun j₁ k₁ j₂ k₂ a₁ b₁ a₂ b₂ n => P j₁ k₁ a₁ b₁ n * Q j₂ k₂ a₂ b₂ n)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [show (∑ j₁ ∈ A, ∑ k₁ ∈ B, ∑ a₁ ∈ U, ∑ b₁ ∈ U, P j₁ k₁ a₁ b₁ n) *
        (∑ j₂ ∈ A, ∑ k₂ ∈ B, ∑ a₂ ∈ U, ∑ b₂ ∈ U, Q j₂ k₂ a₂ b₂ n)
      = ∑ j₁ ∈ A, ∑ k₁ ∈ B, ∑ a₁ ∈ U, ∑ b₁ ∈ U,
          ∑ j₂ ∈ A, ∑ k₂ ∈ B, ∑ a₂ ∈ U, ∑ b₂ ∈ U,
            P j₁ k₁ a₁ b₁ n * Q j₂ k₂ a₂ b₂ n from by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun j₁ _ => Finset.sum_congr rfl (fun k₁ _ => ?_))
  exact sum_swap_two_two A B U U
    (fun j₂ k₂ a₁ b₁ => ∑ a₂ ∈ U, ∑ b₂ ∈ U, P j₁ k₁ a₁ b₁ n * Q j₂ k₂ a₂ b₂ n)

/-- **B-3a — (5.18): the dyadic + residue decomposition, EXACT.** Cells `R_i = V_i 2^{j_i}`
(`j_i < J`), `S_i = 2^{k_i}/2` (`k_i < K`, so `k = 0` is the cell `{1}`); residues over the
units of `[1, q]`; the covers are guaranteed by `hJ`/`hK` at the window's largest form value.
`(δ_i, q) = 1` is HB's standing (5.1) (p.211, "as we henceforth assume") and is what closes the
gap between `cellCount`'s bare `Ioc` and the carrier's `(l,q) = 1` window. -/
theorem bilinearS_eq_sum_cells (χ : DirichletCharacter ℂ q) (F : HBForms)
    (x δ₁ δ₂ : ℕ) (hδ₁q : Nat.Coprime δ₁ q) (hδ₂q : Nat.Coprime δ₂ q)
    {V₁ V₂ : ℝ} (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) (J K : ℕ)
    (hJ₁ : ((F.l₁ (2 * x) : ℕ) : ℝ) ≤ V₁ * 2 ^ J) (hJ₂ : ((F.l₂ (2 * x) : ℕ) : ℝ) ≤ V₂ * 2 ^ J)
    (hK₁ : ((F.l₁ (2 * x) : ℕ) : ℝ) ≤ 2 ^ K / 2) (hK₂ : ((F.l₂ (2 * x) : ℕ) : ℝ) ≤ 2 ^ K / 2) :
    bilinearS χ F x δ₁ δ₂ V₁ V₂
      = ∑ j₁ ∈ range J, ∑ k₁ ∈ range K, ∑ j₂ ∈ range J, ∑ k₂ ∈ range K,
        ∑ a₁ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ b₁ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
        ∑ a₂ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ b₂ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
          chiRe χ b₁ * chiRe χ b₂ *
          (cellCount F q x δ₁ δ₂ (V₁ * 2 ^ j₁) (2 ^ k₁ / 2) (V₂ * 2 ^ j₂) (2 ^ k₂ / 2)
            a₁ b₁ a₂ b₂ : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · -- `q = 0`: the residue sums are empty, and so is the window
    have hL : bilinearS χ F x δ₁ δ₂ V₁ V₂ = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      exfalso
      rw [Finset.mem_filter, hbFormsWindow, Finset.mem_filter, Finset.mem_Ioc] at hn
      have hc : F.l₁ n * F.l₂ n = 1 := (Nat.coprime_zero_right _).mp hn.1.2
      have hx : x < n := hn.1.1.1
      have hα := F.two_le_α₁
      have hβ := F.one_le_β₁
      have h2 : 3 ≤ F.l₁ n := by
        simp only [HBForms.l₁]
        nlinarith
      have h3 : 1 ≤ F.l₂ n := F.one_le_l₂ n
      nlinarith
    rw [hL, Finset.Icc_eq_empty (by omega)]
    simp
  -- the two index sets, and the inclusion between them
  have hsub : (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n)
      ⊆ (Finset.Ioc x (2 * x)).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n) := by
    intro n hn
    rw [Finset.mem_filter, hbFormsWindow, Finset.mem_filter] at hn
    exact Finset.mem_filter.mpr ⟨hn.1.1, hn.2⟩
  -- the two block sums, as functions of `n`
  set P : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ := fun j k a b n =>
    chiRe χ b * (((F.l₁ n / δ₁).divisorsAntidiagonal.filter (fun p =>
      V₁ * 2 ^ j < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (V₁ * 2 ^ j) ∧
      2 ^ k / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * (2 ^ k / 2) ∧
      p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q])).card : ℝ) with hPdef
  set Q : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ := fun j k a b n =>
    chiRe χ b * (((F.l₂ n / δ₂).divisorsAntidiagonal.filter (fun p =>
      V₂ * 2 ^ j < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (V₂ * 2 ^ j) ∧
      2 ^ k / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * (2 ^ k / 2) ∧
      p.2 ≡ a [MOD q] ∧ p.1 ≡ b [MOD q])).card : ℝ) with hQdef
  have hU : ∀ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q), Nat.Coprime a q :=
    fun a ha => (Finset.mem_filter.mp ha).2
  -- ① on the window, each block sum is the truncated divisor sum
  have hwin : ∀ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
      truncChiSum χ (F.l₁ n / δ₁) V₁ * truncChiSum χ (F.l₂ n / δ₂) V₂
        = (∑ j₁ ∈ range J, ∑ k₁ ∈ range K,
            ∑ a₁ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
            ∑ b₁ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q), P j₁ k₁ a₁ b₁ n) *
          (∑ j₂ ∈ range J, ∑ k₂ ∈ range K,
            ∑ a₂ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
            ∑ b₂ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q), Q j₂ k₂ a₂ b₂ n) := by
    intro n hn
    rw [Finset.mem_filter, hbFormsWindow, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨⟨hx1, hx2⟩, hcop⟩, hd₁, hd₂⟩ := hn
    have hl₁q : Nat.Coprime (F.l₁ n) q :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_right (F.l₁ n) (F.l₂ n)) hcop
    have hl₂q : Nat.Coprime (F.l₂ n) q :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_left (F.l₂ n) (F.l₁ n)) hcop
    have hN₁ : Nat.Coprime (F.l₁ n / δ₁) q :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hd₁) hl₁q
    have hN₂ : Nat.Coprime (F.l₂ n / δ₂) q :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hd₂) hl₂q
    have hle₁ : ((F.l₁ n / δ₁ : ℕ) : ℝ) ≤ ((F.l₁ (2 * x) : ℕ) : ℝ) := by
      exact_mod_cast le_trans (Nat.div_le_self _ _) (F.l₁_mono hx2)
    have hle₂ : ((F.l₂ n / δ₂ : ℕ) : ℝ) ≤ ((F.l₂ (2 * x) : ℕ) : ℝ) := by
      exact_mod_cast le_trans (Nat.div_le_self _ _) (F.l₂_mono hx2)
    simp only [hPdef, hQdef]
    rw [truncChiSum_eq_sum_cells χ hq hN₁ hV₁ J K (le_trans hle₁ hJ₁) (le_trans hle₁ hK₁),
      truncChiSum_eq_sum_cells χ hq hN₂ hV₂ J K (le_trans hle₂ hJ₂) (le_trans hle₂ hK₂)]
  -- ② off the window, one block sum vanishes
  have hoff : ∀ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
      n ∉ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n) →
      (∑ j₁ ∈ range J, ∑ k₁ ∈ range K,
        ∑ a₁ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ b₁ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q), P j₁ k₁ a₁ b₁ n) *
      (∑ j₂ ∈ range J, ∑ k₂ ∈ range K,
        ∑ a₂ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ b₂ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q), Q j₂ k₂ a₂ b₂ n) = 0 := by
    intro n hn hnw
    rw [Finset.mem_filter] at hn
    have hnotw : n ∉ hbFormsWindow F q x := by
      intro hc
      exact hnw (Finset.mem_filter.mpr ⟨hc, hn.2⟩)
    rcases not_coprime_of_not_mem_window F x hn.1 hnotw with h | h
    · refine mul_eq_zero_of_left ?_ _
      refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun k _ =>
        Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero (fun b hb => ?_))))
      simp only [hPdef]
      rw [cell_card_eq_zero_of_not_coprime hδ₁q hn.2.1 h _ _ (hU a ha) (hU b hb)]
      simp
    · refine mul_eq_zero_of_right _ ?_
      refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun k _ =>
        Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero (fun b hb => ?_))))
      simp only [hQdef]
      rw [cell_card_eq_zero_of_not_coprime hδ₂q hn.2.2 h _ _ (hU a ha) (hU b hb)]
      simp
  -- ③ assemble
  calc bilinearS χ F x δ₁ δ₂ V₁ V₂
      = ∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
          truncChiSum χ (F.l₁ n / δ₁) V₁ * truncChiSum χ (F.l₂ n / δ₂) V₂ := rfl
    _ = ∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
          (∑ j₁ ∈ range J, ∑ k₁ ∈ range K,
            ∑ a₁ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
            ∑ b₁ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q), P j₁ k₁ a₁ b₁ n) *
          (∑ j₂ ∈ range J, ∑ k₂ ∈ range K,
            ∑ a₂ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
            ∑ b₂ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q), Q j₂ k₂ a₂ b₂ n) :=
        Finset.sum_congr rfl hwin
    _ = ∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
          (∑ j₁ ∈ range J, ∑ k₁ ∈ range K,
            ∑ a₁ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
            ∑ b₁ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q), P j₁ k₁ a₁ b₁ n) *
          (∑ j₂ ∈ range J, ∑ k₂ ∈ range K,
            ∑ a₂ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
            ∑ b₂ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q), Q j₂ k₂ a₂ b₂ n) :=
        Finset.sum_subset hsub hoff
    _ = ∑ j₁ ∈ range J, ∑ k₁ ∈ range K, ∑ j₂ ∈ range J, ∑ k₂ ∈ range K,
        ∑ a₁ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ b₁ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
        ∑ a₂ ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ∑ b₂ ∈ (Icc 1 q).filter (fun b => Nat.Coprime b q),
          ∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
            P j₁ k₁ a₁ b₁ n * Q j₂ k₂ a₂ b₂ n :=
        (sum_cells_mul (range J) (range K) ((Icc 1 q).filter (fun a => Nat.Coprime a q))
          ((Finset.Ioc x (2 * x)).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n)) P Q).symm
    _ = _ := by
        refine Finset.sum_congr rfl (fun j₁ _ => Finset.sum_congr rfl (fun k₁ _ =>
          Finset.sum_congr rfl (fun j₂ _ => Finset.sum_congr rfl (fun k₂ _ =>
          Finset.sum_congr rfl (fun a₁ _ => Finset.sum_congr rfl (fun b₁ _ =>
          Finset.sum_congr rfl (fun a₂ _ => Finset.sum_congr rfl (fun b₂ _ => ?_))))))))
        rw [cellCount]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        simp only [hPdef, hQdef]
        ring

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
  rw [hc₁] at hlow₁ htop₁
  rw [hc₂] at hlow₂ htop₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hprod : (w₁ : ℝ) * (v₁ : ℝ) ≤ (2 * S₁) * (2 * R₁) :=
      mul_le_mul hS₁' hR₁' hvp₁.le (by linarith)
    have hscale := mul_le_mul_of_nonneg_left hprod hδp₁.le
    linarith
  · have hprod : R₁ * S₁ ≤ (v₁ : ℝ) * (w₁ : ℝ) := mul_le_mul hR₁.le hS₁.le hSp₁.le hvp₁.le
    have hscale := mul_le_mul_of_nonneg_left hprod hδp₁.le
    linarith
  · have hprod : (w₂ : ℝ) * (v₂ : ℝ) ≤ (2 * S₂) * (2 * R₂) :=
      mul_le_mul hS₂' hR₂' hvp₂.le (by linarith)
    have hscale := mul_le_mul_of_nonneg_left hprod hδp₂.le
    linarith
  · have hprod : R₂ * S₂ ≤ (v₂ : ℝ) * (w₂ : ℝ) := mul_le_mul hR₂.le hS₂.le hSp₂.le hvp₂.le
    have hscale := mul_le_mul_of_nonneg_left hprod hδp₂.le
    linarith

/-- **B-3c — the `v ↔ w` swap symmetry of the cell count**: HB's "appropriate analogues"
(p.214) for §6's regimes (b)/(c) are B-5c/B-5f at swapped cell parameters.  Both sides count
the same divisor pairs, read through `Prod.swap`: the six conjuncts of the cell filter simply
permute. -/
theorem cellCount_swap₁ (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ) (a₁ b₁ a₂ b₂ : ℕ) :
    cellCount F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ = cellCount F q x δ₁ δ₂ S₁ R₁ R₂ S₂ b₁ a₁ a₂ b₂ :=
    by
    simp only [cellCount]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    congr 1
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp ⊢
      obtain ⟨⟨hmul, hne⟩, h1, h2, h3, h4, h5, h6⟩ := hp
      exact ⟨⟨by rw [← hmul]; exact Nat.mul_comm _ _, hne⟩, h3, h4, h1, h2, h6, h5⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp ⊢
      obtain ⟨⟨hmul, hne⟩, h1, h2, h3, h4, h5, h6⟩ := hp
      exact ⟨⟨by rw [← hmul]; exact Nat.mul_comm _ _, hne⟩, h3, h4, h1, h2, h6, h5⟩
    · intro p _; rfl
    · intro p _; rfl
theorem cellCount_swap₂ (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ) (a₁ b₁ a₂ b₂ : ℕ) :
    cellCount F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ = cellCount F q x δ₁ δ₂ R₁ S₁ S₂ R₂ a₁ b₁ b₂ a₂ :=
    by
    simp only [cellCount]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    congr 1
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp ⊢
      obtain ⟨⟨hmul, hne⟩, h1, h2, h3, h4, h5, h6⟩ := hp
      exact ⟨⟨by rw [← hmul]; exact Nat.mul_comm _ _, hne⟩, h3, h4, h1, h2, h6, h5⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp ⊢
      obtain ⟨⟨hmul, hne⟩, h1, h2, h3, h4, h5, h6⟩ := hp
      exact ⟨⟨by rw [← hmul]; exact Nat.mul_comm _ _, hne⟩, h3, h4, h1, h2, h6, h5⟩
    · intro p _; rfl
    · intro p _; rfl

/-! ## B-4 — the CRT collapse (5.5)–(5.13) -/

/-- **B-4.0 — the gcd/lcm distributive law**, absent from mathlib (`exact?` fails; `grind`,
`omega` and `simp` all fail).  The THIRD fold of `Nat.chineseRemainder'` in B-4 needs it: its
compatibility modulus `gcd (lcm m₁ m₂) (lcm m₃ m₄)` is none of the six pairwise gcds.  Route:
the degenerate cases by `Nat.dvd_antisymm`, then `Nat.factorization_gcd`/`Nat.factorization_lcm`
turn the claim into `(f ⊔ g) ⊓ h = (f ⊓ h) ⊔ (g ⊓ h)` on `ℕ →₀ ℕ`, which is pointwise
`inf_sup_right` in the linear order ℕ. -/
theorem gcd_lcm_distrib (a b c : ℕ) :
    Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.lcm_zero_left, Nat.gcd_zero_left]
    exact (Nat.dvd_antisymm (Nat.lcm_dvd dvd_rfl (Nat.gcd_dvd_right b c))
      (Nat.dvd_lcm_left _ _)).symm
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp only [Nat.lcm_zero_right, Nat.gcd_zero_left]
    exact (Nat.dvd_antisymm (Nat.lcm_dvd (Nat.gcd_dvd_right a c) dvd_rfl)
      (Nat.dvd_lcm_right _ _)).symm
  have hl : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha.ne' hb.ne'
  have hg₁ : Nat.gcd a c ≠ 0 := fun h => ha.ne' (Nat.gcd_eq_zero_iff.mp h).1
  have hg₂ : Nat.gcd b c ≠ 0 := fun h => hb.ne' (Nat.gcd_eq_zero_iff.mp h).1
  refine Nat.eq_of_factorization_eq (fun h => hl (Nat.gcd_eq_zero_iff.mp h).1)
    (Nat.lcm_ne_zero hg₁ hg₂) (fun p => ?_)
  rw [Nat.factorization_gcd hl hc.ne', Nat.factorization_lcm hg₁ hg₂,
    Nat.factorization_lcm ha.ne' hb.ne', Nat.factorization_gcd ha.ne' hc.ne',
    Nat.factorization_gcd hb.ne' hc.ne']
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  exact inf_sup_right _ _ _

/-- **B-4z — the cell count is zero unless (5.4) and (5.5) hold** (p.212, "S will be zero
unless"); the cells B-6 must skip.  (5.4) at `i = 1` is modulo `(α₁, q)`, which under `hΔ` is
`(α₂, q)` — spelled so to match B-4's and B-5f's `h54₁` token for token.  From B-3b's FULL
extraction: `δ_i a_i b_i ≡ δ_i w_i v_i = l_i(n) ≡ β_i` modulo `(α_i, q)`, and
`α₁ · (δ₂a₂b₂) ≡ α₁α₂n + α₁β₂`, `α₂ · (δ₁a₁b₁) ≡ α₁α₂n + α₂β₁` modulo `qα`, since `α ∣ α_i`. -/
theorem cellCount_eq_zero_of_not_congr (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ)
    (a₁ b₁ a₂ b₂ : ℕ) (_hq : 0 < q) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (hΔ : Nat.gcd F.α₁ q = Nat.gcd F.α₂ q)
    (_hab : Nat.Coprime (a₁ * b₁ * (a₂ * b₂)) q)
    (h : ¬ (δ₁ * a₁ * b₁ ≡ F.β₁ [MOD Nat.gcd F.α₂ q] ∧
            δ₂ * a₂ * b₂ ≡ F.β₂ [MOD Nat.gcd F.α₂ q] ∧
            F.α₁ * (δ₂ * a₂ * b₂) + F.α₂ * F.β₁
              ≡ F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ [MOD q * F.α])) :
    cellCount F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ = 0 := by
  -- ⚠ `hδ₁`/`hδ₂` are frozen binders this route never spends: the residues and the
  -- factorisation come from B-3b's extraction, which derives `0 < δ_i` itself.  They are
  -- consumed here so the unused-variable linter stays silent; the statement is untouched.
  have _ := hδ₁
  have _ := hδ₂
  by_contra hne
  obtain ⟨n, w₁, v₁, w₂, v₂, _, _, he₁, he₂, _, _, _, _, _, _, _, _, hv₁, hw₁, hv₂, hw₂⟩ :=
    cellCount_ne_zero_extract F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ hne
  -- `δ_i a_i b_i ≡ l_i(n)` modulo `q`, from the two residue classes
  have hq₁ : δ₁ * a₁ * b₁ ≡ F.l₁ n [MOD q] := by
    have hprod : δ₁ * a₁ * b₁ ≡ δ₁ * v₁ * w₁ [MOD q] :=
      Nat.ModEq.mul (Nat.ModEq.mul_left δ₁ hv₁.symm) hw₁.symm
    have hval : δ₁ * v₁ * w₁ = F.l₁ n := by rw [← he₁]; ring
    rwa [hval] at hprod
  have hq₂ : δ₂ * a₂ * b₂ ≡ F.l₂ n [MOD q] := by
    have hprod : δ₂ * a₂ * b₂ ≡ δ₂ * v₂ * w₂ [MOD q] :=
      Nat.ModEq.mul (Nat.ModEq.mul_left δ₂ hv₂.symm) hw₂.symm
    have hval : δ₂ * v₂ * w₂ = F.l₂ n := by rw [← he₂]; ring
    rwa [hval] at hprod
  -- `l_i(n) ≡ β_i` modulo `α_i`
  have hl₁ : F.l₁ n ≡ F.β₁ [MOD F.α₁] := by
    have hz : F.α₁ * n ≡ 0 [MOD F.α₁] := (Nat.modEq_zero_iff_dvd).mpr ⟨n, rfl⟩
    simp only [HBForms.l₁]
    have h1 := hz.add_right F.β₁
    rwa [Nat.zero_add] at h1
  have hl₂ : F.l₂ n ≡ F.β₂ [MOD F.α₂] := by
    have hz : F.α₂ * n ≡ 0 [MOD F.α₂] := (Nat.modEq_zero_iff_dvd).mpr ⟨n, rfl⟩
    simp only [HBForms.l₂]
    have h1 := hz.add_right F.β₂
    rwa [Nat.zero_add] at h1
  -- (5.4), both indices, modulo `(α₂, q)`
  have h54₁ : δ₁ * a₁ * b₁ ≡ F.β₁ [MOD Nat.gcd F.α₂ q] := by
    rw [← hΔ]
    exact (Nat.ModEq.of_dvd (Nat.gcd_dvd_right F.α₁ q) hq₁).trans
      (Nat.ModEq.of_dvd (Nat.gcd_dvd_left F.α₁ q) hl₁)
  have h54₂ : δ₂ * a₂ * b₂ ≡ F.β₂ [MOD Nat.gcd F.α₂ q] :=
    (Nat.ModEq.of_dvd (Nat.gcd_dvd_right F.α₂ q) hq₂).trans
      (Nat.ModEq.of_dvd (Nat.gcd_dvd_left F.α₂ q) hl₂)
  -- (5.5), modulo `q · α`, through `α ∣ α_i`
  have hdvd₁ : q * F.α ∣ F.α₁ * q := by
    rw [Nat.mul_comm F.α₁ q]
    exact Nat.mul_dvd_mul_left q (Nat.gcd_dvd_left F.α₁ F.α₂)
  have hdvd₂ : q * F.α ∣ F.α₂ * q := by
    rw [Nat.mul_comm F.α₂ q]
    exact Nat.mul_dvd_mul_left q (Nat.gcd_dvd_right F.α₁ F.α₂)
  have hA : F.α₁ * (δ₂ * a₂ * b₂) ≡ F.α₁ * F.l₂ n [MOD q * F.α] :=
    Nat.ModEq.of_dvd hdvd₁ (hq₂.mul_left' F.α₁)
  have hB : F.α₂ * (δ₁ * a₁ * b₁) ≡ F.α₂ * F.l₁ n [MOD q * F.α] :=
    Nat.ModEq.of_dvd hdvd₂ (hq₁.mul_left' F.α₂)
  have heq : F.α₁ * F.l₂ n + F.α₂ * F.β₁ = F.α₂ * F.l₁ n + F.α₁ * F.β₂ := by
    simp only [HBForms.l₁, HBForms.l₂]; ring
  have h55 : F.α₁ * (δ₂ * a₂ * b₂) + F.α₂ * F.β₁
      ≡ F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ [MOD q * F.α] := by
    have e1 := hA.add_right (F.α₂ * F.β₁)
    have e2 := hB.add_right (F.α₁ * F.β₂)
    rw [heq] at e1
    exact e1.trans e2.symm
  exact h ⟨h54₁, h54₂, h55⟩

/-- **The four-fold CRT B-4's collapse runs on** — a general lemma, stated in the shape the
three folds need: from the SIX pairwise compatibilities `X_i ≡ X_j [MOD gcd m_i m_j]` a common
solution exists.  The first two folds are `Nat.chineseRemainder'` at `(m₁,m₂)` and `(m₃,m₄)`;
the third needs `gcd (lcm m₁ m₂) (lcm m₃ m₄) ∣ k₁₂ − k₃₄`, which `gcd_lcm_distrib` turns into
the four CROSS compatibilities, each obtained by transferring `k₁₂ ≡ X_i [MOD m_i]` and
`k₃₄ ≡ X_j [MOD m_j]` down to `gcd m_i m_j` and composing with the `(i,j)` row. -/
theorem crt_four {m₁ m₂ m₃ m₄ X₁ X₂ X₃ X₄ : ℕ}
    (h₁₂ : X₁ ≡ X₂ [MOD Nat.gcd m₁ m₂]) (h₁₃ : X₁ ≡ X₃ [MOD Nat.gcd m₁ m₃])
    (h₁₄ : X₁ ≡ X₄ [MOD Nat.gcd m₁ m₄]) (h₂₃ : X₂ ≡ X₃ [MOD Nat.gcd m₂ m₃])
    (h₂₄ : X₂ ≡ X₄ [MOD Nat.gcd m₂ m₄]) (h₃₄ : X₃ ≡ X₄ [MOD Nat.gcd m₃ m₄]) :
    ∃ Z : ℕ, Z ≡ X₁ [MOD m₁] ∧ Z ≡ X₂ [MOD m₂] ∧ Z ≡ X₃ [MOD m₃] ∧ Z ≡ X₄ [MOD m₄] := by
  obtain ⟨k₁₂, hk₁, hk₂⟩ := Nat.chineseRemainder' h₁₂
  obtain ⟨k₃₄, hk₃, hk₄⟩ := Nat.chineseRemainder' h₃₄
  -- the four CROSS compatibilities
  have cross : ∀ {mi mj Xi Xj : ℕ}, k₁₂ ≡ Xi [MOD mi] → k₃₄ ≡ Xj [MOD mj] →
      Xi ≡ Xj [MOD Nat.gcd mi mj] → k₁₂ ≡ k₃₄ [MOD Nat.gcd mi mj] := by
    intro mi mj Xi Xj hi hj hij
    exact ((Nat.ModEq.of_dvd (Nat.gcd_dvd_left mi mj) hi).trans hij).trans
      (Nat.ModEq.of_dvd (Nat.gcd_dvd_right mi mj) hj).symm
  have c₁₃ := cross hk₁ hk₃ h₁₃
  have c₁₄ := cross hk₁ hk₄ h₁₄
  have c₂₃ := cross hk₂ hk₃ h₂₃
  have c₂₄ := cross hk₂ hk₄ h₂₄
  -- `gcd (lcm m₁ m₂) (lcm m₃ m₄)` is the lcm of the four cross gcds
  have hsplit : Nat.gcd (Nat.lcm m₁ m₂) (Nat.lcm m₃ m₄)
      = Nat.lcm (Nat.lcm (Nat.gcd m₃ m₁) (Nat.gcd m₄ m₁))
          (Nat.lcm (Nat.gcd m₃ m₂) (Nat.gcd m₄ m₂)) := by
    rw [gcd_lcm_distrib m₁ m₂ (Nat.lcm m₃ m₄), Nat.gcd_comm m₁ (Nat.lcm m₃ m₄),
      Nat.gcd_comm m₂ (Nat.lcm m₃ m₄), gcd_lcm_distrib m₃ m₄ m₁, gcd_lcm_distrib m₃ m₄ m₂]
  have hcompat : k₁₂ ≡ k₃₄ [MOD Nat.gcd (Nat.lcm m₁ m₂) (Nat.lcm m₃ m₄)] := by
    rw [hsplit]
    exact Nat.mod_lcm
      (Nat.mod_lcm (by rwa [Nat.gcd_comm m₃ m₁]) (by rwa [Nat.gcd_comm m₄ m₁]))
      (Nat.mod_lcm (by rwa [Nat.gcd_comm m₃ m₂]) (by rwa [Nat.gcd_comm m₄ m₂]))
  obtain ⟨Z, hZ₁₂, hZ₃₄⟩ := Nat.chineseRemainder' hcompat
  exact ⟨Z, (Nat.ModEq.of_dvd (Nat.dvd_lcm_left m₁ m₂) hZ₁₂).trans hk₁,
    (Nat.ModEq.of_dvd (Nat.dvd_lcm_right m₁ m₂) hZ₁₂).trans hk₂,
    (Nat.ModEq.of_dvd (Nat.dvd_lcm_left m₃ m₄) hZ₃₄).trans hk₃,
    (Nat.ModEq.of_dvd (Nat.dvd_lcm_right m₃ m₄) hZ₃₄).trans hk₄⟩

/-- **B-4 — (5.7)–(5.10) ⟺ (5.11)**: under (5.1), (5.3), (5.4), (5.5), (5.6) and
`(α₁,q) = (α₂,q)`, the four congruences in `X = v₂w₂` are ONE congruence modulo
`D δ₁ w₁`, `D = roadModulus α₂ q`, with a residue coprime to the modulus.

The four are one system in `Z = α₁δ₂X + α₂β₁` at the moduli `m₁ = α₁α₂`, `m₂ = α₂δ₁w₁`,
`m₃ = α₂q`, `m₄ = α₁δ₂q` — p.212's `(X_j; m_j)` — and `crt_four` solves it once the six
pairwise (5.13) rows are in hand.  `C` is read off the solution by shifting it above `α₂β₁`
(legitimate: every `m_j` divides `α₁δ₂·Dδ₁w₁`) and dividing by `α₁δ₂`.  The forward half of
the ⟺ does NOT go back through the lcm of the four: (5.7) cancels `δ₂` mod `α₂`, (5.10) is
already mod `q`, (5.8) cancels `α₁δ₂` mod `δ₁w₁`, and the three recombine on
`k = lcm(lcm(α₂,q), δ₁w₁) = Dδ₁w₁`.  The coprimality is p.213's three legs. -/
theorem crt_collapse (F : HBForms) (q δ₁ δ₂ w₁ a₁ b₁ a₂ b₂ : ℕ) (hq : 0 < q)
    (hδ₁ : 0 < δ₁) (hw₁ : 0 < w₁)
    (hΔ : Nat.gcd F.α₁ q = Nat.gcd F.α₂ q)
    (hδ₁q : Nat.Coprime δ₁ q) (_hδ₂q : Nat.Coprime δ₂ q)
    (hδ₁α : Nat.Coprime δ₁ F.α) (hδ₂α : Nat.Coprime δ₂ F.α) (hδ : Nat.Coprime δ₁ δ₂)
    (hw₁α : Nat.Coprime w₁ F.α) (hw₁δ₂ : Nat.Coprime w₁ δ₂) (hw₁q : Nat.Coprime w₁ q)
    (hab : Nat.Coprime (a₁ * b₁ * (a₂ * b₂)) q)
    (h54₁ : δ₁ * a₁ * b₁ ≡ F.β₁ [MOD Nat.gcd F.α₂ q])
    (h54₂ : δ₂ * a₂ * b₂ ≡ F.β₂ [MOD Nat.gcd F.α₂ q])
    (h55 : F.α₁ * (δ₂ * a₂ * b₂) + F.α₂ * F.β₁
            ≡ F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ [MOD q * F.α]) :
    ∃ C : ℕ, Nat.Coprime C (roadModulus F.α₂ q * δ₁ * w₁) ∧ ∀ X : ℕ,
      (δ₂ * X ≡ F.β₂ [MOD F.α₂] ∧
       F.α₁ * δ₂ * X + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD F.α₂ * δ₁ * w₁] ∧
       F.α₁ * δ₂ * X + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁ [MOD F.α₂ * q] ∧
       X ≡ a₂ * b₂ [MOD q])
      ↔ X ≡ C [MOD roadModulus F.α₂ q * δ₁ * w₁] := by
  ---- ① positivity, and the coprimalities B-1.9 transfers off `α`
  have hα₁ : 0 < F.α₁ := lt_of_lt_of_le (by norm_num) F.two_le_α₁
  have hα₂ : 0 < F.α₂ := lt_of_lt_of_le (by norm_num) F.two_le_α₂
  have hδ₂ : 0 < δ₂ := by
    rcases Nat.eq_zero_or_pos δ₂ with h | h
    · exfalso
      have h1 : F.α = 1 := by
        have hc := hδ₂α
        rw [h, Nat.Coprime, Nat.gcd_zero_left] at hc
        exact hc
      have h2 : (2 : ℕ) ∣ F.α := Nat.dvd_gcd F.even₁ F.even₂
      rw [h1] at h2
      omega
    · exact h
  obtain ⟨hδ₁α₁, hδ₁α₂⟩ := (F.coprime_α_iff δ₁).mp hδ₁α
  obtain ⟨hδ₂α₁, hδ₂α₂⟩ := (F.coprime_α_iff δ₂).mp hδ₂α
  obtain ⟨hw₁α₁, hw₁α₂⟩ := (F.coprime_α_iff w₁).mp hw₁α
  have hdwα₁ : Nat.Coprime (δ₁ * w₁) F.α₁ := hδ₁α₁.mul_left hw₁α₁
  have hdwα₂ : Nat.Coprime (δ₁ * w₁) F.α₂ := hδ₁α₂.mul_left hw₁α₂
  have hdwq : Nat.Coprime (δ₁ * w₁) q := hδ₁q.mul_left hw₁q
  have hdwδ₂ : Nat.Coprime (δ₁ * w₁) δ₂ := hδ.mul_left hw₁δ₂
  ---- ② the road modulus, the target modulus, and `Δ ∣ α₁`
  have hα₂D : F.α₂ ∣ roadModulus F.α₂ q := dvd_roadModulus_left F.α₂ q
  have hqD : q ∣ roadModulus F.α₂ q := dvd_roadModulus F.α₂ q
  have hΔα₁ : Nat.gcd F.α₂ q ∣ F.α₁ := by rw [← hΔ]; exact Nat.gcd_dvd_left F.α₁ q
  have hgl : Nat.gcd F.α₂ q * roadModulus F.α₂ q = F.α₂ * q := by
    rw [roadModulus_eq_lcm]; exact Nat.gcd_mul_lcm F.α₂ q
  obtain ⟨cD, hcD⟩ := hα₂D
  obtain ⟨cq, hcq⟩ := hqD
  obtain ⟨eΔ, heΔ⟩ := hΔα₁
  ---- ③ every `m_j` divides `α₁δ₂ · Dδ₁w₁`
  have hm₁AK : F.α₁ * F.α₂ ∣ F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) :=
    ⟨δ₂ * cD * δ₁ * w₁, by rw [hcD]; ring⟩
  have hm₂AK : F.α₂ * δ₁ * w₁ ∣ F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) :=
    ⟨F.α₁ * δ₂ * cD, by rw [hcD]; ring⟩
  have hm₃AK : F.α₂ * q ∣ F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) :=
    ⟨eΔ * δ₂ * δ₁ * w₁, by rw [heΔ, ← hgl]; ring⟩
  have hm₄AK : F.α₁ * δ₂ * q ∣ F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) :=
    ⟨cq * δ₁ * w₁, by rw [hcq]; ring⟩
  ---- ④ the six pairwise (5.13) rows
  have c₁₂ : F.α₁ * F.β₂ + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂
      [MOD Nat.gcd (F.α₁ * F.α₂) (F.α₂ * δ₁ * w₁)] := by
    have hco : Nat.Coprime (Nat.gcd (F.α₁ * F.α₂) (F.α₂ * δ₁ * w₁)) (δ₁ * w₁) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) (hdwα₁.mul_right hdwα₂).symm
    have hdd : Nat.gcd (F.α₁ * F.α₂) (F.α₂ * δ₁ * w₁) ∣ F.α₂ * (δ₁ * w₁) := by
      rw [show F.α₂ * (δ₁ * w₁) = F.α₂ * δ₁ * w₁ by ring]; exact Nat.gcd_dvd_right _ _
    refine Nat.ModEq.of_dvd (hco.dvd_of_dvd_mul_right hdd) ?_
    have h0 := (Nat.ModEq.refl (F.α₁ * F.β₂)).add
      ((Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right F.α₂ F.β₁))
    rwa [Nat.add_zero] at h0
  have c₁₃ : F.α₁ * F.β₂ + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ + F.α₂ * (δ₁ * a₁ * b₁)
      [MOD Nat.gcd (F.α₁ * F.α₂) (F.α₂ * q)] := by
    have hg : Nat.gcd (F.α₁ * F.α₂) (F.α₂ * q) ∣ F.α₂ * Nat.gcd F.α₂ q := by
      have h1 : Nat.gcd (F.α₁ * F.α₂) (F.α₂ * q) ∣ F.α₂ * F.α₁ := by
        rw [Nat.mul_comm F.α₂ F.α₁]; exact Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd (F.α₁ * F.α₂) (F.α₂ * q) ∣ F.α₂ * q := Nat.gcd_dvd_right _ _
      have h3 := Nat.dvd_gcd h1 h2
      rwa [Nat.gcd_mul_left, hΔ] at h3
    exact Nat.ModEq.of_dvd hg ((Nat.ModEq.refl _).add (h54₁.symm.mul_left' F.α₂))
  have c₁₄ : F.α₁ * F.β₂ + F.α₂ * F.β₁ ≡ F.α₁ * δ₂ * (a₂ * b₂) + F.α₂ * F.β₁
      [MOD Nat.gcd (F.α₁ * F.α₂) (F.α₁ * δ₂ * q)] := by
    have hg : Nat.gcd (F.α₁ * F.α₂) (F.α₁ * δ₂ * q) ∣ F.α₁ * Nat.gcd F.α₂ q := by
      have hcopδ₂ : Nat.Coprime (Nat.gcd (F.α₁ * F.α₂) (F.α₁ * δ₂ * q)) δ₂ :=
        (hδ₂α₁.mul_right hδ₂α₂).symm.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      have h2 : Nat.gcd (F.α₁ * F.α₂) (F.α₁ * δ₂ * q) ∣ F.α₁ * q := by
        have hdd : Nat.gcd (F.α₁ * F.α₂) (F.α₁ * δ₂ * q) ∣ F.α₁ * q * δ₂ := by
          rw [show F.α₁ * q * δ₂ = F.α₁ * δ₂ * q by ring]; exact Nat.gcd_dvd_right _ _
        exact hcopδ₂.dvd_of_dvd_mul_right hdd
      have h3 := Nat.dvd_gcd (Nat.gcd_dvd_left (F.α₁ * F.α₂) (F.α₁ * δ₂ * q)) h2
      rwa [Nat.gcd_mul_left] at h3
    refine Nat.ModEq.of_dvd hg ?_
    rw [show F.α₁ * δ₂ * (a₂ * b₂) = F.α₁ * (δ₂ * a₂ * b₂) by ring]
    exact (h54₂.symm.mul_left' F.α₁).add_right (F.α₂ * F.β₁)
  have c₂₃ : F.α₁ * F.β₂ ≡ F.α₁ * F.β₂ + F.α₂ * (δ₁ * a₁ * b₁)
      [MOD Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₂ * q)] := by
    have hco : Nat.Coprime (Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₂ * q)) (δ₁ * w₁) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (hdwα₂.mul_right hdwq).symm
    have hdd : Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₂ * q) ∣ F.α₂ * (δ₁ * w₁) := by
      rw [show F.α₂ * (δ₁ * w₁) = F.α₂ * δ₁ * w₁ by ring]; exact Nat.gcd_dvd_left _ _
    refine Nat.ModEq.of_dvd (hco.dvd_of_dvd_mul_right hdd) ?_
    have h0 := (Nat.ModEq.refl (F.α₁ * F.β₂)).add
      (((Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right F.α₂ (δ₁ * a₁ * b₁))).symm)
    rwa [Nat.add_zero] at h0
  have c₂₄ : F.α₁ * F.β₂ ≡ F.α₁ * δ₂ * (a₂ * b₂) + F.α₂ * F.β₁
      [MOD Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q)] := by
    have hcopdw : Nat.Coprime (Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q)) (δ₁ * w₁) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        ((hdwα₁.mul_right hdwδ₂).mul_right hdwq).symm
    have hgα₂ : Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q) ∣ F.α₂ := by
      have hdd : Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q) ∣ F.α₂ * (δ₁ * w₁) := by
        rw [show F.α₂ * (δ₁ * w₁) = F.α₂ * δ₁ * w₁ by ring]; exact Nat.gcd_dvd_left _ _
      exact hcopdw.dvd_of_dvd_mul_right hdd
    have hcopδ₂ : Nat.Coprime (Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q)) δ₂ :=
      hδ₂α₂.symm.coprime_dvd_left hgα₂
    have hgα₁q : Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q) ∣ F.α₁ * q := by
      have hdd : Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q) ∣ F.α₁ * q * δ₂ := by
        rw [show F.α₁ * q * δ₂ = F.α₁ * δ₂ * q by ring]; exact Nat.gcd_dvd_right _ _
      exact hcopδ₂.dvd_of_dvd_mul_right hdd
    have hgα₁Δ : Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q) ∣ F.α₁ * Nat.gcd F.α₂ q := by
      have h3 := Nat.dvd_gcd (Dvd.dvd.mul_left hgα₂ F.α₁) hgα₁q
      rwa [Nat.gcd_mul_left] at h3
    have e1 : F.α₁ * F.β₂ ≡ F.α₁ * (δ₂ * a₂ * b₂)
        [MOD Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q)] :=
      Nat.ModEq.of_dvd hgα₁Δ (h54₂.symm.mul_left' F.α₁)
    have e2 : (0 : ℕ) ≡ F.α₂ * F.β₁ [MOD Nat.gcd (F.α₂ * δ₁ * w₁) (F.α₁ * δ₂ * q)] :=
      (Nat.ModEq.of_dvd hgα₂ ((Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right F.α₂ F.β₁))).symm
    rw [show F.α₁ * δ₂ * (a₂ * b₂) = F.α₁ * (δ₂ * a₂ * b₂) by ring]
    have h0 := e1.add e2
    rwa [Nat.add_zero] at h0
  have c₃₄ : F.α₁ * F.β₂ + F.α₂ * (δ₁ * a₁ * b₁) ≡ F.α₁ * δ₂ * (a₂ * b₂) + F.α₂ * F.β₁
      [MOD Nat.gcd (F.α₂ * q) (F.α₁ * δ₂ * q)] := by
    have hg : Nat.gcd (F.α₂ * q) (F.α₁ * δ₂ * q) ∣ q * F.α := by
      have hstep : Nat.gcd (F.α₂ * q) (F.α₁ * δ₂ * q) ∣ q * Nat.gcd F.α₂ (F.α₁ * δ₂) := by
        have h1 : Nat.gcd (F.α₂ * q) (F.α₁ * δ₂ * q) ∣ q * F.α₂ := by
          rw [Nat.mul_comm q F.α₂]; exact Nat.gcd_dvd_left _ _
        have h2 : Nat.gcd (F.α₂ * q) (F.α₁ * δ₂ * q) ∣ q * (F.α₁ * δ₂) := by
          rw [show q * (F.α₁ * δ₂) = F.α₁ * δ₂ * q by ring]; exact Nat.gcd_dvd_right _ _
        have h3 := Nat.dvd_gcd h1 h2
        rwa [Nat.gcd_mul_left] at h3
      have hinner : Nat.gcd F.α₂ (F.α₁ * δ₂) ∣ F.α := by
        have hco : Nat.Coprime (Nat.gcd F.α₂ (F.α₁ * δ₂)) δ₂ :=
          hδ₂α₂.symm.coprime_dvd_left (Nat.gcd_dvd_left _ _)
        have hdd : Nat.gcd F.α₂ (F.α₁ * δ₂) ∣ F.α₁ * δ₂ := Nat.gcd_dvd_right _ _
        exact Nat.dvd_gcd (hco.dvd_of_dvd_mul_right hdd) (Nat.gcd_dvd_left _ _)
      exact hstep.trans (Nat.mul_dvd_mul_left q hinner)
    refine Nat.ModEq.of_dvd hg ?_
    rw [show F.α₁ * F.β₂ + F.α₂ * (δ₁ * a₁ * b₁) = F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ by ring,
      show F.α₁ * δ₂ * (a₂ * b₂) + F.α₂ * F.β₁ = F.α₁ * (δ₂ * a₂ * b₂) + F.α₂ * F.β₁ by ring]
    exact h55.symm
  ---- ⑤ the common solution, shifted above `α₂β₁`, divided by `α₁δ₂`
  obtain ⟨Z, hZ₁, hZ₂, hZ₃, hZ₄⟩ := crt_four c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄
  have hApos : 0 < F.α₁ * δ₂ := Nat.mul_pos hα₁ hδ₂
  have hDpos : 0 < roadModulus F.α₂ q := by
    rw [roadModulus_eq_lcm]
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero hα₂.ne' hq.ne')
  have hAKpos : 0 < F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) :=
    Nat.mul_pos hApos (Nat.mul_pos (Nat.mul_pos hDpos hδ₁) hw₁)
  have hZ₁ge : F.α₂ * F.β₁
      ≤ Z + F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) * (F.α₂ * F.β₁) := by
    have h := Nat.le_mul_of_pos_left (F.α₂ * F.β₁) hAKpos
    omega
  have shift : ∀ {m Y : ℕ}, m ∣ F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) → Z ≡ Y [MOD m] →
      Z + F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) * (F.α₂ * F.β₁) ≡ Y [MOD m] := by
    intro m Y hm hY
    refine Nat.ModEq.trans ?_ hY
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right Z _)).mpr
      (by rw [Nat.add_sub_cancel_left]; exact hm.mul_right _)).symm
  have hAdvdZ : F.α₁ * δ₂
      ∣ Z + F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) * (F.α₂ * F.β₁) - F.α₂ * F.β₁ := by
    have h4 := shift hm₄AK hZ₄
    have hA4 : Z + F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) * (F.α₂ * F.β₁)
        ≡ F.α₁ * δ₂ * (a₂ * b₂) + F.α₂ * F.β₁ [MOD F.α₁ * δ₂] :=
      Nat.ModEq.of_dvd (dvd_mul_right (F.α₁ * δ₂) q) h4
    have hzero : F.α₁ * δ₂ * (a₂ * b₂) + F.α₂ * F.β₁ ≡ F.α₂ * F.β₁ [MOD F.α₁ * δ₂] := by
      have h0 := ((Nat.modEq_zero_iff_dvd).mpr
        (dvd_mul_right (F.α₁ * δ₂) (a₂ * b₂))).add_right (F.α₂ * F.β₁)
      rwa [Nat.zero_add] at h0
    exact (Nat.modEq_iff_dvd' hZ₁ge).mp (hA4.trans hzero).symm
  obtain ⟨C, hCdef⟩ := hAdvdZ
  have hCeq : F.α₁ * δ₂ * C + F.α₂ * F.β₁
      = Z + F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁) * (F.α₂ * F.β₁) := by omega
  ---- ⑥ `C` satisfies the four
  have hC7 : δ₂ * C ≡ F.β₂ [MOD F.α₂] := by
    have h1 : F.α₁ * δ₂ * C + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ + F.α₂ * F.β₁ [MOD F.α₁ * F.α₂] := by
      rw [hCeq]; exact shift hm₁AK hZ₁
    have h2 : F.α₁ * (δ₂ * C) ≡ F.α₁ * F.β₂ [MOD F.α₁ * F.α₂] := by
      have h3 := Nat.ModEq.add_right_cancel' (F.α₂ * F.β₁) h1
      rwa [show F.α₁ * δ₂ * C = F.α₁ * (δ₂ * C) by ring] at h3
    exact Nat.ModEq.mul_left_cancel' hα₁.ne' h2
  have hC8 : F.α₁ * δ₂ * C + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD F.α₂ * δ₁ * w₁] := by
    rw [hCeq]; exact shift hm₂AK hZ₂
  have hC9 : F.α₁ * δ₂ * C + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁
      [MOD F.α₂ * q] := by
    rw [hCeq, show F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁
      = F.α₁ * F.β₂ + F.α₂ * (δ₁ * a₁ * b₁) by ring]
    exact shift hm₃AK hZ₃
  have hC10 : C ≡ a₂ * b₂ [MOD q] := by
    have h1 : F.α₁ * δ₂ * C + F.α₂ * F.β₁ ≡ F.α₁ * δ₂ * (a₂ * b₂) + F.α₂ * F.β₁
        [MOD F.α₁ * δ₂ * q] := by rw [hCeq]; exact shift hm₄AK hZ₄
    exact Nat.ModEq.mul_left_cancel' hApos.ne'
      (Nat.ModEq.add_right_cancel' (F.α₂ * F.β₁) h1)
  ---- ⑦ p.213's three coprimality legs
  have hab₂ : Nat.Coprime (a₂ * b₂) q :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left (a₂ * b₂) (a₁ * b₁)) hab
  have hCα₂ : Nat.Coprime C F.α₂ := by
    by_contra hcon
    obtain ⟨p, hp, hpC, hpα₂⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    have h1 : δ₂ * C ≡ F.β₂ [MOD p] := Nat.ModEq.of_dvd hpα₂ hC7
    have h2 : δ₂ * C ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr (Dvd.dvd.mul_left hpC δ₂)
    have h3 : p ∣ F.β₂ := (Nat.modEq_zero_iff_dvd).mp (h1.symm.trans h2)
    have h4 : p ∣ Nat.gcd F.α₂ F.β₂ := Nat.dvd_gcd hpα₂ h3
    rw [show Nat.gcd F.α₂ F.β₂ = 1 from F.cop₂] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  have hCq : Nat.Coprime C q := by
    by_contra hcon
    obtain ⟨p, hp, hpC, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    have h1 : C ≡ a₂ * b₂ [MOD p] := Nat.ModEq.of_dvd hpq hC10
    have h2 : C ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hpC
    have h3 : p ∣ a₂ * b₂ := (Nat.modEq_zero_iff_dvd).mp (h1.symm.trans h2)
    have h4 : p ∣ Nat.gcd (a₂ * b₂) q := Nat.dvd_gcd h3 hpq
    rw [show Nat.gcd (a₂ * b₂) q = 1 from hab₂] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  have hdet : ∀ p : ℕ, p.Prime → p ∣ C → p ∣ δ₁ * w₁ → False := by
    intro p hp hpC hpd
    have hpm₂ : p ∣ F.α₂ * δ₁ * w₁ := by
      rw [show F.α₂ * δ₁ * w₁ = F.α₂ * (δ₁ * w₁) by ring]
      exact Dvd.dvd.mul_left hpd F.α₂
    have h1 : F.α₁ * δ₂ * C + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD p] := Nat.ModEq.of_dvd hpm₂ hC8
    have h2 : F.α₁ * δ₂ * C ≡ 0 [MOD p] :=
      (Nat.modEq_zero_iff_dvd).mpr (Dvd.dvd.mul_left hpC (F.α₁ * δ₂))
    have h3 : F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD p] := by
      have h4 := (h2.add_right (F.α₂ * F.β₁)).symm.trans h1
      rwa [Nat.zero_add] at h4
    have hz : (p : ℤ) ∣ (F.α₁ : ℤ) * F.β₂ - (F.α₂ : ℤ) * F.β₁ := by
      have h5 := Nat.modEq_iff_dvd.mp h3
      push_cast at h5
      exact h5
    obtain ⟨hd1, hd2⟩ := F.det_dvd p hp hz
    have hα : p ∣ F.α := Nat.dvd_gcd hd1 hd2
    have hpdw : p ∣ δ₁ ∨ p ∣ w₁ := (Nat.Prime.dvd_mul hp).mp hpd
    rcases hpdw with h | h
    · have h6 := Nat.dvd_gcd h hα
      rw [show Nat.gcd δ₁ F.α = 1 from hδ₁α] at h6
      exact hp.one_lt.ne' (Nat.dvd_one.mp h6)
    · have h6 := Nat.dvd_gcd h hα
      rw [show Nat.gcd w₁ F.α = 1 from hw₁α] at h6
      exact hp.one_lt.ne' (Nat.dvd_one.mp h6)
  have hCdw : Nat.Coprime C (δ₁ * w₁) := by
    by_contra hcon
    obtain ⟨p, hp, hpC, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    exact hdet p hp hpC hpd
  have hCD : Nat.Coprime C (roadModulus F.α₂ q) := by
    refine Nat.Coprime.coprime_dvd_right ?_ (hCα₂.mul_right hCq)
    rw [roadModulus_eq_lcm]
    exact Nat.lcm_dvd (dvd_mul_right F.α₂ q) (dvd_mul_left q F.α₂)
  have hCk : Nat.Coprime C (roadModulus F.α₂ q * δ₁ * w₁) := by
    have h1 : Nat.Coprime C (roadModulus F.α₂ q * (δ₁ * w₁)) := hCD.mul_right hCdw
    rwa [← Nat.mul_assoc] at h1
  ---- ⑧ the equivalence
  have hα₂k : F.α₂ ∣ roadModulus F.α₂ q * δ₁ * w₁ :=
    ⟨cD * δ₁ * w₁, by rw [hcD]; ring⟩
  have hqk : q ∣ roadModulus F.α₂ q * δ₁ * w₁ := dvd_roadModulus_mul F.α₂ q δ₁ w₁
  have hdwk : δ₁ * w₁ ∣ F.α₂ * δ₁ * w₁ := ⟨F.α₂, by ring⟩
  have hcopDdw : Nat.Coprime (roadModulus F.α₂ q) (δ₁ * w₁) := by
    refine Nat.Coprime.coprime_dvd_left ?_ (hdwα₂.mul_right hdwq).symm
    rw [roadModulus_eq_lcm]
    exact Nat.lcm_dvd (dvd_mul_right F.α₂ q) (dvd_mul_left q F.α₂)
  refine ⟨C, hCk, fun X => ⟨?_, ?_⟩⟩
  · rintro ⟨h7, h8, _h9, h10⟩
    have eα₂ : X ≡ C [MOD F.α₂] :=
      Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime] using hδ₂α₂.symm)
        (h7.trans hC7.symm)
    have eq' : X ≡ C [MOD q] := h10.trans hC10.symm
    have e8a : F.α₁ * δ₂ * X + F.α₂ * F.β₁ ≡ F.α₁ * δ₂ * C + F.α₂ * F.β₁ [MOD δ₁ * w₁] :=
      (Nat.ModEq.of_dvd hdwk h8).trans (Nat.ModEq.of_dvd hdwk hC8).symm
    have edw : X ≡ C [MOD δ₁ * w₁] :=
      Nat.ModEq.cancel_left_of_coprime
        (by simpa [Nat.Coprime] using (hdwα₁.mul_right hdwδ₂))
        (Nat.ModEq.add_right_cancel' (F.α₂ * F.β₁) e8a)
    have eD : X ≡ C [MOD roadModulus F.α₂ q] := by
      rw [roadModulus_eq_lcm]; exact Nat.mod_lcm eα₂ eq'
    have hfin := Nat.mod_lcm eD edw
    rwa [hcopDdw.lcm_eq_mul, ← Nat.mul_assoc] at hfin
  · intro hXC
    have eα₂ : X ≡ C [MOD F.α₂] := Nat.ModEq.of_dvd hα₂k hXC
    have eq' : X ≡ C [MOD q] := Nat.ModEq.of_dvd hqk hXC
    have eA : F.α₁ * δ₂ * X ≡ F.α₁ * δ₂ * C
        [MOD F.α₁ * δ₂ * (roadModulus F.α₂ q * δ₁ * w₁)] := hXC.mul_left' (F.α₁ * δ₂)
    refine ⟨(eα₂.mul_left δ₂).trans hC7, ?_, ?_, eq'.trans hC10⟩
    · exact ((Nat.ModEq.of_dvd hm₂AK eA).add_right (F.α₂ * F.β₁)).trans hC8
    · exact ((Nat.ModEq.of_dvd hm₃AK eA).add_right (F.α₂ * F.β₁)).trans hC9

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

/-- The nested-floor helper B-5a's four rewrites run through: `⌊T⌋₊` inside a ℚ-quotient floor
is the same integer as the ℝ-quotient floor, for `0 ≤ T`. -/
theorem nested (k r : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ⌊(((⌊T⌋₊ : ℚ) - (r : ℚ)) / (k : ℚ))⌋ = ⌊(T - (r : ℝ)) / (k : ℝ)⌋ := by
  rw [Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_sub_natCast,
    Int.floor_sub_natCast, Int.floor_natCast, Int.natCast_floor_eq_floor hT]

/-- **B-5a — the residue-class count through the sawtooth** (the identity behind (5.17)). -/
theorem card_Ioc_filter_modEq_eq_sawtooth {k : ℕ} (hk : 0 < k) (r : ℕ) {T₁ T₂ : ℝ}
    (h0 : 0 ≤ T₁) (h12 : T₁ ≤ T₂) :
    (((Finset.Ioc ⌊T₁⌋₊ ⌊T₂⌋₊).filter (fun v : ℕ => v ≡ r [MOD k])).card : ℝ)
      = (T₂ - T₁) / k + sawtooth ((T₁ - r) / k) - sawtooth ((T₂ - r) / k) := by
  have h0₂ : (0 : ℝ) ≤ T₂ := h0.trans h12
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hmono : (T₁ - (r : ℝ)) / (k : ℝ) ≤ (T₂ - (r : ℝ)) / (k : ℝ) := by
    have hnn : (0 : ℝ) ≤ (T₂ - T₁) / (k : ℝ) := div_nonneg (by linarith) hkR.le
    have e : (T₂ - (r : ℝ)) / (k : ℝ) - (T₁ - (r : ℝ)) / (k : ℝ) = (T₂ - T₁) / (k : ℝ) := by
      ring
    linarith
  have key : (((Finset.Ioc ⌊T₁⌋₊ ⌊T₂⌋₊).filter (fun v : ℕ => v ≡ r [MOD k])).card : ℤ)
      = ⌊(T₂ - (r : ℝ)) / (k : ℝ)⌋ - ⌊(T₁ - (r : ℝ)) / (k : ℝ)⌋ := by
    rw [Nat.Ioc_filter_modEq_card _ _ hk r, nested k r h0₂, nested k r h0,
      max_eq_left (sub_nonneg.mpr (Int.floor_mono hmono))]
  have hf : ∀ y : ℝ, ((⌊y⌋ : ℤ) : ℝ) = y - Int.fract y := by
    intro y; have := Int.floor_add_fract y; linarith
  have hgoal : (((Finset.Ioc ⌊T₁⌋₊ ⌊T₂⌋₊).filter (fun v : ℕ => v ≡ r [MOD k])).card : ℝ)
      = ((⌊(T₂ - (r : ℝ)) / (k : ℝ)⌋ : ℤ) : ℝ) - ((⌊(T₁ - (r : ℝ)) / (k : ℝ)⌋ : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) key
  rw [hgoal, hf, hf]
  simp only [sawtooth]
  ring


/-- **B-5b — the inversion**: for `(w, k) = 1`, `v w ≡ C ⟺ v ≡ C·w̄`, `w̄ = invMod w k`.
`invMod w k` is `((w : ZMod k)⁻¹).val` cast to ℤ, hence `≥ 0` and its `.toNat` faithful. -/
theorem modEq_mul_iff_modEq_invMod {k : ℕ} [NeZero k] {w : ℕ} (hw : Nat.Coprime w k) (C v : ℕ) :
    v * w ≡ C [MOD k] ↔ v ≡ C * (invMod w k).toNat [MOD k] := by
  have hunit : IsUnit ((w : ℕ) : ZMod k) := (ZMod.isUnit_iff_coprime w k).mpr hw
  have hinv : (((invMod (w : ℤ) k).toNat : ℕ) : ZMod k) = ((w : ℕ) : ZMod k)⁻¹ := by
    have h0 : (invMod (w : ℤ) k).toNat = ((((w : ℕ) : ZMod k))⁻¹).val := by
      simp only [invMod, Int.toNat_natCast]
      norm_cast
    rw [h0, ZMod.natCast_val, ZMod.cast_id]
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_mul,
    hinv]
  constructor
  · intro hv
    rw [← hv, mul_assoc, ZMod.mul_inv_of_unit _ hunit, mul_one]
  · intro hv
    rw [hv, mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one]

/-- **B-5e — (5.17)**: for `(w₂, k) = 1`,
`#{v : T₁ < v ≤ T₂, v w₂ ≡ C (k)} = (T₂−T₁)/k + ψ((T₁ − C w̄₂)/k) − ψ((T₂ − C w̄₂)/k)`.
B-5b turns the filter into a bare residue class and B-5a is applied at `r := C · w̄₂` DIRECTLY
(`Nat.Ioc_filter_modEq_card` is general in the residue — no `r < k`, no periodicity step). -/
theorem card_count_eq_sawtooth (k : ℕ) [NeZero k] {w₂ : ℕ} (hw : Nat.Coprime w₂ k) (C : ℕ)
    {T₁ T₂ : ℝ} (h0 : 0 ≤ T₁) (h12 : T₁ ≤ T₂) :
    (((Finset.Ioc ⌊T₁⌋₊ ⌊T₂⌋₊).filter (fun v : ℕ => v * w₂ ≡ C [MOD k])).card : ℝ)
      = (T₂ - T₁) / k + sawtooth ((T₁ - C * invMod w₂ k) / k)
          - sawtooth ((T₂ - C * invMod w₂ k) / k) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hcongr : (Finset.Ioc ⌊T₁⌋₊ ⌊T₂⌋₊).filter (fun v : ℕ => v * w₂ ≡ C [MOD k])
      = (Finset.Ioc ⌊T₁⌋₊ ⌊T₂⌋₊).filter
          (fun v : ℕ => v ≡ C * (invMod w₂ k).toNat [MOD k]) :=
    Finset.filter_congr (fun v _ => modEq_mul_iff_modEq_invMod hw C v)
  have hnn : (0 : ℤ) ≤ invMod (w₂ : ℤ) k := by
    simp only [invMod]; exact Int.natCast_nonneg _
  have hcast : ((C * (invMod (w₂ : ℤ) k).toNat : ℕ) : ℝ) = (C : ℝ) * (invMod (w₂ : ℤ) k : ℝ) := by
    have h1 : (((invMod (w₂ : ℤ) k).toNat : ℕ) : ℤ) = invMod (w₂ : ℤ) k := Int.toNat_of_nonneg hnn
    have h2 : (((invMod (w₂ : ℤ) k).toNat : ℕ) : ℝ) = ((invMod (w₂ : ℤ) k : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
    push_cast
    rw [h2]
  rw [hcongr, card_Ioc_filter_modEq_eq_sawtooth hk _ h0 h12, hcast]

/-- **B-5g — `(w₂, D δ₁ w₁) = 1` is automatic**: with `(C, k) = 1` the class `v w₂ ≡ C (k)` is
empty unless `(w₂, k) = 1` — a prime on both `w₂` and `k` would land on `C`. -/
theorem count_eq_zero_of_not_coprime {k : ℕ} {w₂ C : ℕ} (hC : Nat.Coprime C k)
    (hw : ¬ Nat.Coprime w₂ k) (A B : ℕ) :
    ((Finset.Ioc A B).filter (fun v : ℕ => v * w₂ ≡ C [MOD k])).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ hv
  obtain ⟨p, hp, hpw, hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp hw
  have h1 : v * w₂ ≡ C [MOD p] := Nat.ModEq.of_dvd hpk hv
  have h2 : v * w₂ ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr (Dvd.dvd.mul_left hpw v)
  have h3 : p ∣ C := (Nat.modEq_zero_iff_dvd).mp (h1.symm.trans h2)
  have h4 : p ∣ Nat.gcd C k := Nat.dvd_gcd h3 hpk
  rw [show Nat.gcd C k = 1 from hC] at h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)


/-! ### B-5c's top-level pieces — the floor bridge, its degenerate corner, and (5.8) ⟺ δ₁w₁ ∣ l₁ n.

`five_eight_iff` is consumed by B-5d as well as by B-5c, so all three land here, above both.
-/

theorem R₂_le_hbT₁ (F : HBForms) (x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ) (w₁ w₂ : ℕ) :
    R₂ ≤ hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ := le_max_left _ _

theorem hbT₁_pos (F : HBForms) (x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ) (w₁ w₂ : ℕ) (hR₂ : 0 < R₂) :
    0 < hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ := lt_of_lt_of_le hR₂ (R₂_le_hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂)

theorem hbT₂_le_two_R₂ (F : HBForms) (x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ) (w₁ w₂ : ℕ) :
    hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w₂ ≤ 2 * R₂ := min_le_left _ _

/-- The floor bridge — an IFF from `0 ≤ T₁` ALONE; nothing is owed on `T₂`. -/
theorem mem_Ioc_floor_iff {T₁ T₂ : ℝ} (h0 : 0 ≤ T₁) (v : ℕ) :
    v ∈ Finset.Ioc ⌊T₁⌋₊ ⌊T₂⌋₊ ↔ (T₁ < (v : ℝ) ∧ (v : ℝ) ≤ T₂) := by
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    have hlt : T₁ < (v : ℝ) := (Nat.floor_lt h0).mp h1
    have hv1 : 1 ≤ v := by omega
    have hfl : 1 ≤ ⌊T₂⌋₊ := le_trans hv1 h2
    have hT₂ : (0 : ℝ) ≤ T₂ := by
      by_contra hc
      have hc' : T₂ < 0 := not_le.mp hc
      rw [Nat.floor_of_nonpos hc'.le] at hfl
      omega
    exact ⟨hlt, (Nat.le_floor_iff hT₂).mp h2⟩
  · rintro ⟨h1, h2⟩
    have hT₂ : (0 : ℝ) ≤ T₂ := le_trans (le_trans h0 h1.le) h2
    exact ⟨(Nat.floor_lt h0).mpr h1, (Nat.le_floor_iff hT₂).mpr h2⟩

/-- The degenerate corner: `T₂ < 0` is HARMLESS — both sides are empty.  It CAN happen, at
negative determinants. -/
theorem Ioc_floor_eq_empty_of_neg {T₁ T₂ : ℝ} (h0 : 0 ≤ T₁) (h : T₂ < 0) :
    Finset.Ioc ⌊T₁⌋₊ ⌊T₂⌋₊ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun v hv => ?_)
  rw [mem_Ioc_floor_iff h0] at hv
  have : (0 : ℝ) ≤ (v : ℝ) := Nat.cast_nonneg v
  linarith [hv.2]

/-- The hinge of B-5c's backward direction: (5.8) ⟺ `δ₁ w₁ ∣ l₁ n`, after cancelling `α₂`.
⛔ The two sides are `α₂·l₁(n) + α₁β₂` against `0 + α₁β₂`, NOT `c*a ≡ c*b`: cancel ADDITIVELY
first (`Nat.ModEq.add_right_cancel'`), THEN multiplicatively. -/
theorem five_eight_iff (F : HBForms) (δ₁ δ₂ w₁ X n : ℕ) (hα₂ : F.α₂ ≠ 0)
    (hn : F.α₂ * n + F.β₂ = δ₂ * X) :
    (F.α₁ * δ₂ * X + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD F.α₂ * δ₁ * w₁])
      ↔ δ₁ * w₁ ∣ F.l₁ n := by
  have key : F.α₁ * δ₂ * X + F.α₂ * F.β₁ = F.α₂ * F.l₁ n + F.α₁ * F.β₂ := by
    have : F.α₁ * (δ₂ * X) = F.α₁ * (F.α₂ * n + F.β₂) := by rw [hn]
    simp only [HBForms.l₁]
    ring_nf
    ring_nf at this
    omega
  rw [key, show F.α₂ * δ₁ * w₁ = F.α₂ * (δ₁ * w₁) by ring]
  constructor
  · intro h
    have h' : F.α₂ * F.l₁ n + F.α₁ * F.β₂
        ≡ F.α₂ * 0 + F.α₁ * F.β₂ [MOD F.α₂ * (δ₁ * w₁)] := by
      rw [Nat.mul_zero, Nat.zero_add]; exact h
    have h'' := Nat.ModEq.add_right_cancel' (F.α₁ * F.β₂) h'
    exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.mul_left_cancel' hα₂ h'')
  · intro h
    have h0 : F.l₁ n ≡ 0 [MOD δ₁ * w₁] := (Nat.modEq_zero_iff_dvd).mpr h
    have h' : F.α₂ * F.l₁ n ≡ F.α₂ * 0 [MOD F.α₂ * (δ₁ * w₁)] :=
      (Nat.ModEq.mul_left_cancel_iff' hα₂).mpr h0
    have h'' := h'.add_right (F.α₁ * F.β₂)
    rw [Nat.mul_zero, Nat.zero_add] at h''
    exact h''


/-- **The `v₂`-interval `(T₁, T₂]` IS the three pairs of cell conditions at once** — HB's (5.15)
and (5.16) read backwards.  Once `α₂n + β₂ = δ₂v₂w₂` (so `n` is the cell's point) and
`δ₁v₁w₁ = l₁(n)` (so `v₁` is the cell's first divisor), the three entries of `max`/`min` are, in
order, `R₂ < v₂ ≤ 2R₂`, `x < n ≤ 2x` and `R₁ < v₁ ≤ 2R₁`.  This is the whole content of the
elimination of `n` and `v₁`. -/
theorem hbT_mem_iff (F : HBForms) (x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ) (w₁ w₂ v₁ v₂ n : ℕ)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hn : F.α₂ * n + F.β₂ = δ₂ * (v₂ * w₂))
    (hv₁ : δ₁ * (v₁ * w₁) = F.l₁ n) :
    (hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ < (v₂ : ℝ) ∧ (v₂ : ℝ) ≤ hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w₂)
      ↔ (R₂ < (v₂ : ℝ) ∧ (v₂ : ℝ) ≤ 2 * R₂ ∧ x < n ∧ n ≤ 2 * x ∧
          R₁ < (v₁ : ℝ) ∧ (v₁ : ℝ) ≤ 2 * R₁) := by
  have hα₁ : 0 < F.α₁ := lt_of_lt_of_le (by norm_num) F.two_le_α₁
  have hα₂ : 0 < F.α₂ := lt_of_lt_of_le (by norm_num) F.two_le_α₂
  have hα₁R : (0 : ℝ) < (F.α₁ : ℝ) := by exact_mod_cast hα₁
  have hα₂R : (0 : ℝ) < (F.α₂ : ℝ) := by exact_mod_cast hα₂
  have hδ₁R : (0 : ℝ) < (δ₁ : ℝ) := by exact_mod_cast hδ₁
  have hδ₂R : (0 : ℝ) < (δ₂ : ℝ) := by exact_mod_cast hδ₂
  have hw₁R : (0 : ℝ) < (w₁ : ℝ) := by exact_mod_cast hw₁
  have hw₂R : (0 : ℝ) < (w₂ : ℝ) := by exact_mod_cast hw₂
  have hdw : (0 : ℝ) < (δ₂ : ℝ) * (w₂ : ℝ) := mul_pos hδ₂R hw₂R
  have hadw : (0 : ℝ) < ((F.α₁ * δ₂ * w₂ : ℕ) : ℝ) := by
    push_cast; positivity
  -- the two ℕ-identities, in ℝ
  have hnR : (F.α₂ : ℝ) * (n : ℝ) + (F.β₂ : ℝ) = (δ₂ : ℝ) * ((v₂ : ℝ) * (w₂ : ℝ)) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hn
  have hv₁R : (δ₁ : ℝ) * ((v₁ : ℝ) * (w₁ : ℝ)) = (F.α₁ : ℝ) * (n : ℝ) + (F.β₁ : ℝ) := by
    have h := congrArg (fun m : ℕ => (m : ℝ)) hv₁
    simp only [HBForms.l₁] at h
    push_cast at h
    exact h
  -- the six entries, one by one
  have e₂ : ((F.α₂ * x + F.β₂ : ℕ) : ℝ) / ((δ₂ : ℝ) * (w₂ : ℝ)) < (v₂ : ℝ) ↔ x < n := by
    rw [div_lt_iff₀ hdw]
    push_cast
    constructor
    · intro h
      have hx : (x : ℝ) < (n : ℝ) := by nlinarith
      exact_mod_cast hx
    · intro h
      have hx : (x : ℝ) < (n : ℝ) := by exact_mod_cast h
      nlinarith
  have e₂' : (v₂ : ℝ) ≤ ((2 * F.α₂ * x + F.β₂ : ℕ) : ℝ) / ((δ₂ : ℝ) * (w₂ : ℝ)) ↔ n ≤ 2 * x := by
    rw [le_div_iff₀ hdw]
    push_cast
    constructor
    · intro h
      have hx : (n : ℝ) ≤ 2 * (x : ℝ) := by nlinarith
      exact_mod_cast hx
    · intro h
      have hx : (n : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast h
      nlinarith
  have hprod : (0 : ℝ) < (F.α₂ : ℝ) * (δ₁ : ℝ) * (w₁ : ℝ) := by positivity
  have hexp₁ : (v₂ : ℝ) * ((F.α₁ : ℝ) * (δ₂ : ℝ) * (w₂ : ℝ))
      = (F.α₁ : ℝ) * (F.α₂ : ℝ) * (n : ℝ) + (F.α₁ : ℝ) * (F.β₂ : ℝ) := by
    linear_combination (-(F.α₁ : ℝ)) * hnR
  have hexp₂ : (F.α₂ : ℝ) * (δ₁ : ℝ) * (w₁ : ℝ) * (v₁ : ℝ)
      = (F.α₁ : ℝ) * (F.α₂ : ℝ) * (n : ℝ) + (F.α₂ : ℝ) * (F.β₁ : ℝ) := by
    linear_combination (F.α₂ : ℝ) * hv₁R
  have e₃ : (((F.α₂ * δ₁ * w₁ : ℕ) : ℝ) * R₁ + ((F.α₁ * F.β₂ : ℕ) : ℝ)
        - ((F.α₂ * F.β₁ : ℕ) : ℝ)) / ((F.α₁ * δ₂ * w₂ : ℕ) : ℝ) < (v₂ : ℝ)
      ↔ R₁ < (v₁ : ℝ) := by
    rw [div_lt_iff₀ hadw]
    push_cast
    constructor
    · intro h
      have h2 : (F.α₂ : ℝ) * (δ₁ : ℝ) * (w₁ : ℝ) * R₁
          < (F.α₂ : ℝ) * (δ₁ : ℝ) * (w₁ : ℝ) * (v₁ : ℝ) := by
        linarith [hexp₁, hexp₂]
      exact lt_of_mul_lt_mul_left h2 hprod.le
    · intro h
      have h2 := mul_lt_mul_of_pos_left h hprod
      linarith [hexp₁, hexp₂, h2]
  have e₃' : (v₂ : ℝ) ≤ (2 * ((F.α₂ * δ₁ * w₁ : ℕ) : ℝ) * R₁ + ((F.α₁ * F.β₂ : ℕ) : ℝ)
        - ((F.α₂ * F.β₁ : ℕ) : ℝ)) / ((F.α₁ * δ₂ * w₂ : ℕ) : ℝ)
      ↔ (v₁ : ℝ) ≤ 2 * R₁ := by
    rw [le_div_iff₀ hadw]
    push_cast
    constructor
    · intro h
      have h2 : (F.α₂ : ℝ) * (δ₁ : ℝ) * (w₁ : ℝ) * (v₁ : ℝ)
          ≤ (F.α₂ : ℝ) * (δ₁ : ℝ) * (w₁ : ℝ) * (2 * R₁) := by
        linarith [hexp₁, hexp₂]
      exact le_of_mul_le_mul_left h2 hprod
    · intro h
      have h2 := mul_le_mul_of_nonneg_left h hprod.le
      linarith [hexp₁, hexp₂, h2]
  rw [hbT₁, hbT₂, max_lt_iff, max_lt_iff, le_min_iff, le_min_iff, e₂, e₂', e₃, e₃']
  tauto

/-- **B-5c — the elimination of `n` and `v₁`** (p.212): the cell count as a double sum over
`(w₁, w₂)` in their cells and classes of the `v₂`-count under (5.7)–(5.10) on `T₁ < v₂ ≤ T₂`.

Both sides flatten to ONE `Finset.card` (`← Finset.card_product`, `← Finset.card_sigma`) and the
bijection is `Finset.card_nbij'` at `⟨n, ((w₁,v₁),(w₂,v₂))⟩ ↦ ⟨w₁, ⟨w₂, v₂⟩⟩`: `n` comes back
from `α₂n + β₂ = δ₂v₂w₂` and `v₁` from `δ₁w₁v₁ = l₁(n)`, which `five_eight_iff` makes an integer.
`hbT_mem_iff` carries the whole geometric content — the three entries of `T₁`/`T₂` ARE
`R₂ < v₂ ≤ 2R₂`, `x < n ≤ 2x` and `R₁ < v₁ ≤ 2R₁`. The three congruence binders are each
load-bearing: `hb₁`/`hb₂` are what let `v₁ ≡ a₁` and `v₂ ≡ a₂` be recovered from (5.9)/(5.10). -/
theorem cellCount_eq_sum_w (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ) (a₁ b₁ a₂ b₂ : ℕ)
    (hq : 0 < q) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hR₂ : 0 < R₂)
    (hδ₁q : Nat.Coprime δ₁ q) (hb₁ : Nat.Coprime b₁ q) (hb₂ : Nat.Coprime b₂ q) :
    cellCount F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂
      = ∑ w₁ ∈ (Finset.Icc 1 ⌊2 * S₁⌋₊).filter (fun w : ℕ => S₁ < (w : ℝ) ∧ w ≡ b₁ [MOD q]),
        ∑ w₂ ∈ (Finset.Icc 1 ⌊2 * S₂⌋₊).filter (fun w : ℕ => S₂ < (w : ℝ) ∧ w ≡ b₂ [MOD q]),
          ((Finset.Ioc ⌊hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂⌋₊ ⌊hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w₂⌋₊).filter
            (fun v₂ : ℕ =>
              δ₂ * (v₂ * w₂) ≡ F.β₂ [MOD F.α₂] ∧
              F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD F.α₂ * δ₁ * w₁] ∧
              F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁
                ≡ F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁ [MOD F.α₂ * q] ∧
              v₂ * w₂ ≡ a₂ * b₂ [MOD q])).card := by
  classical
  -- ⚠ `hq` is a frozen binder this route never spends: the residue cancellations run on
  -- `Coprime δ₁ q`, `Coprime b_i q` and `Coprime w_i q`, none of which needs `0 < q`.  It is
  -- consumed here so the unused-variable linter stays silent; the statement is untouched.
  have _ := hq
  have hα₁ : 0 < F.α₁ := lt_of_lt_of_le (by norm_num) F.two_le_α₁
  have hα₂ : 0 < F.α₂ := lt_of_lt_of_le (by norm_num) F.two_le_α₂
  simp only [cellCount, ← Finset.card_product, ← Finset.card_sigma]
  refine Finset.card_nbij'
    (fun z => ⟨z.2.1.1, ⟨z.2.2.1, z.2.2.2⟩⟩)
    (fun y => ⟨(δ₂ * (y.2.2 * y.2.1) - F.β₂) / F.α₂,
      ((y.1, F.l₁ ((δ₂ * (y.2.2 * y.2.1) - F.β₂) / F.α₂) / (δ₁ * y.1)), (y.2.1, y.2.2))⟩)
    ?_ ?_ ?_ ?_
  · -- ① forward: a cell point gives a `(w₁, w₂, v₂)` triple
    rintro ⟨n, ⟨w₁, v₁⟩, ⟨w₂, v₂⟩⟩ hz
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_product, Finset.mem_filter,
      Nat.mem_divisorsAntidiagonal, Finset.mem_Ioc] at hz
    obtain ⟨⟨⟨hx1, hx2⟩, hd₁, hd₂⟩, ⟨⟨hm₁, hne₁⟩, hR₁a, hR₁b, hS₁a, hS₁b, ha₁', hb₁'⟩,
      ⟨hm₂, hne₂⟩, hR₂a, hR₂b, hS₂a, hS₂b, ha₂', hb₂'⟩ := hz
    have he₁ : δ₁ * (w₁ * v₁) = F.l₁ n := by rw [hm₁]; exact Nat.mul_div_cancel' hd₁
    have he₂ : δ₂ * (w₂ * v₂) = F.l₂ n := by rw [hm₂]; exact Nat.mul_div_cancel' hd₂
    have hwv₁ : w₁ * v₁ ≠ 0 := by rw [hm₁]; exact hne₁
    have hwv₂ : w₂ * v₂ ≠ 0 := by rw [hm₂]; exact hne₂
    have hw₁ : 0 < w₁ := Nat.pos_of_ne_zero (fun h => hwv₁ (by rw [h, Nat.zero_mul]))
    have hw₂ : 0 < w₂ := Nat.pos_of_ne_zero (fun h => hwv₂ (by rw [h, Nat.zero_mul]))
    have hnE : F.α₂ * n + F.β₂ = δ₂ * (v₂ * w₂) := by
      rw [show δ₂ * (v₂ * w₂) = δ₂ * (w₂ * v₂) by ring, he₂]; rfl
    have hv₁E : δ₁ * (v₁ * w₁) = F.l₁ n := by
      rw [show δ₁ * (v₁ * w₁) = δ₁ * (w₁ * v₁) by ring]; exact he₁
    have hT₁nn : (0 : ℝ) ≤ hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ :=
      (hbT₁_pos F x δ₁ δ₂ R₁ R₂ w₁ w₂ hR₂).le
    have hkey : F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁ = F.α₂ * F.l₁ n + F.α₁ * F.β₂ := by
      have h : F.α₁ * (δ₂ * (v₂ * w₂)) = F.α₁ * (F.α₂ * n + F.β₂) := by rw [hnE]
      simp only [HBForms.l₁]
      ring_nf
      ring_nf at h
      omega
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨hw₁, Nat.le_floor hS₁b⟩, hS₁a, hb₁'⟩,
      ⟨⟨hw₂, Nat.le_floor hS₂b⟩, hS₂a, hb₂'⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_Ioc_floor_iff hT₁nn]
      exact (hbT_mem_iff F x δ₁ δ₂ R₁ R₂ w₁ w₂ v₁ v₂ n hδ₁ hδ₂ hw₁ hw₂ hnE hv₁E).mpr
        ⟨hR₂a, hR₂b, hx1, hx2, hR₁a, hR₁b⟩
    · rw [← hnE]
      have hz0 : F.α₂ * n ≡ 0 [MOD F.α₂] := (Nat.modEq_zero_iff_dvd).mpr ⟨n, rfl⟩
      have h1 := hz0.add_right F.β₂
      rwa [Nat.zero_add] at h1
    · exact (five_eight_iff F δ₁ δ₂ w₁ (v₂ * w₂) n hα₂.ne' hnE).mpr ⟨v₁, by rw [← hv₁E]; ring⟩
    · rw [hkey]
      have hl : F.l₁ n ≡ δ₁ * a₁ * b₁ [MOD q] := by
        rw [← hv₁E, show δ₁ * a₁ * b₁ = δ₁ * (a₁ * b₁) by ring]
        exact Nat.ModEq.mul_left δ₁ (Nat.ModEq.mul ha₁' hb₁')
      have h3 := (hl.mul_left' F.α₂).add_right (F.α₁ * F.β₂)
      rwa [show F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂
        = F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁ by ring] at h3
    · exact Nat.ModEq.mul ha₂' hb₂'
  · -- ② backward: a `(w₁, w₂, v₂)` triple gives a cell point
    rintro ⟨w₁, ⟨w₂, v₂⟩⟩ hy
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨⟨hw₁, hw₁2⟩, hS₁a, hb₁'⟩, ⟨⟨hw₂, hw₂2⟩, hS₂a, hb₂'⟩, hmem, c1, c2, c3, c4⟩ := hy
    have hS₁nn : (0 : ℝ) ≤ 2 * S₁ := by
      by_contra hc
      rw [Nat.floor_of_nonpos (not_le.mp hc).le] at hw₁2
      omega
    have hS₂nn : (0 : ℝ) ≤ 2 * S₂ := by
      by_contra hc
      rw [Nat.floor_of_nonpos (not_le.mp hc).le] at hw₂2
      omega
    have hw₁2' : (w₁ : ℝ) ≤ 2 * S₁ := (Nat.le_floor_iff hS₁nn).mp hw₁2
    have hw₂2' : (w₂ : ℝ) ≤ 2 * S₂ := (Nat.le_floor_iff hS₂nn).mp hw₂2
    have hT₁nn : (0 : ℝ) ≤ hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ :=
      (hbT₁_pos F x δ₁ δ₂ R₁ R₂ w₁ w₂ hR₂).le
    have hIoc := (mem_Ioc_floor_iff hT₁nn v₂).mp hmem
    have hv₂pos : 0 < v₂ := by
      have h : (0 : ℝ) < (v₂ : ℝ) := lt_of_le_of_lt hT₁nn hIoc.1
      exact_mod_cast h
    have hdw : (0 : ℝ) < (δ₂ : ℝ) * (w₂ : ℝ) :=
      mul_pos (by exact_mod_cast hδ₂) (by exact_mod_cast hw₂)
    have hA : ((F.α₂ * x + F.β₂ : ℕ) : ℝ) / ((δ₂ : ℝ) * (w₂ : ℝ))
        ≤ hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ := le_trans (le_max_left _ _) (le_max_right _ _)
    have hbigN : F.α₂ * x + F.β₂ < v₂ * (δ₂ * w₂) := by
      exact_mod_cast (div_lt_iff₀ hdw).mp (lt_of_le_of_lt hA hIoc.1)
    have hge : F.β₂ ≤ δ₂ * (v₂ * w₂) := by
      have hr : v₂ * (δ₂ * w₂) = δ₂ * (v₂ * w₂) := by ring
      omega
    obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' hge).mp c1.symm
    have hnE : F.α₂ * n + F.β₂ = δ₂ * (v₂ * w₂) := by omega
    have hn' : (δ₂ * (v₂ * w₂) - F.β₂) / F.α₂ = n := by
      rw [hn]; exact Nat.mul_div_cancel_left n hα₂
    obtain ⟨v₁, hv₁def⟩ := (five_eight_iff F δ₁ δ₂ w₁ (v₂ * w₂) n hα₂.ne' hnE).mp c2
    have hv₁' : F.l₁ n / (δ₁ * w₁) = v₁ := by
      rw [hv₁def]; exact Nat.mul_div_cancel_left v₁ (Nat.mul_pos hδ₁ hw₁)
    have hv₁E : δ₁ * (v₁ * w₁) = F.l₁ n := by rw [hv₁def]; ring
    have hl₁pos : 0 < F.l₁ n := F.one_le_l₁ n
    have hv₁pos : 0 < v₁ := by
      rcases Nat.eq_zero_or_pos v₁ with h | h
      · rw [h, Nat.zero_mul, Nat.mul_zero] at hv₁E; omega
      · exact h
    obtain ⟨hR₂a, hR₂b, hx1, hx2, hR₁a, hR₁b⟩ :=
      (hbT_mem_iff F x δ₁ δ₂ R₁ R₂ w₁ w₂ v₁ v₂ n hδ₁ hδ₂ hw₁ hw₂ hnE hv₁E).mp hIoc
    have hkey : F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁ = F.α₂ * F.l₁ n + F.α₁ * F.β₂ := by
      have h : F.α₁ * (δ₂ * (v₂ * w₂)) = F.α₁ * (F.α₂ * n + F.β₂) := by rw [hnE]
      simp only [HBForms.l₁]
      ring_nf
      ring_nf at h
      omega
    have hw₁q : Nat.Coprime w₁ q := coprime_of_modEq hb₁' hb₁
    have hw₂q : Nat.Coprime w₂ q := coprime_of_modEq hb₂' hb₂
    have hv₁a : v₁ ≡ a₁ [MOD q] := by
      rw [hkey, show F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁
        = F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ by ring] at c3
      have h1 := Nat.ModEq.add_right_cancel' (F.α₁ * F.β₂) c3
      have h2 : F.l₁ n ≡ δ₁ * a₁ * b₁ [MOD q] := Nat.ModEq.mul_left_cancel' hα₂.ne' h1
      rw [← hv₁E, show δ₁ * a₁ * b₁ = δ₁ * (a₁ * b₁) by ring] at h2
      have h3 : v₁ * w₁ ≡ a₁ * b₁ [MOD q] :=
        Nat.ModEq.cancel_left_of_coprime hδ₁q.symm h2
      exact Nat.ModEq.cancel_right_of_coprime hw₁q.symm
        (h3.trans (Nat.ModEq.mul_left a₁ hb₁'.symm))
    have hv₂a : v₂ ≡ a₂ [MOD q] :=
      Nat.ModEq.cancel_right_of_coprime hw₂q.symm
        (c4.trans (Nat.ModEq.mul_left a₂ hb₂'.symm))
    have hd₁ : δ₁ ∣ F.l₁ n := ⟨v₁ * w₁, hv₁E.symm⟩
    have hd₂ : δ₂ ∣ F.l₂ n := ⟨v₂ * w₂, hnE⟩
    have hq₁ : F.l₁ n / δ₁ = w₁ * v₁ := by
      have h : F.l₁ n = δ₁ * (w₁ * v₁) := by rw [← hv₁E]; ring
      rw [h]; exact Nat.mul_div_cancel_left _ hδ₁
    have hq₂ : F.l₂ n / δ₂ = w₂ * v₂ := by
      have h : F.l₂ n = δ₂ * (w₂ * v₂) := by
        rw [show F.l₂ n = F.α₂ * n + F.β₂ from rfl, hnE]; ring
      rw [h]; exact Nat.mul_div_cancel_left _ hδ₂
    simp only [hn', hv₁', Finset.mem_coe, Finset.mem_sigma, Finset.mem_product,
      Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_Ioc]
    exact ⟨⟨⟨hx1, hx2⟩, hd₁, hd₂⟩,
      ⟨⟨hq₁.symm, by rw [hq₁]; exact Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hw₁) hv₁pos.ne'⟩,
        hR₁a, hR₁b, hS₁a, hw₁2', hv₁a, hb₁'⟩,
      ⟨hq₂.symm, by rw [hq₂]; exact Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hw₂) hv₂pos.ne'⟩,
        hR₂a, hR₂b, hS₂a, hw₂2', hv₂a, hb₂'⟩
  · -- ③ `j ∘ i = id` on the cell points
    rintro ⟨n, ⟨w₁, v₁⟩, ⟨w₂, v₂⟩⟩ hz
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_product, Finset.mem_filter,
      Nat.mem_divisorsAntidiagonal, Finset.mem_Ioc] at hz
    obtain ⟨⟨⟨hx1, hx2⟩, hd₁, hd₂⟩, ⟨⟨hm₁, hne₁⟩, _⟩, ⟨hm₂, hne₂⟩, _⟩ := hz
    have he₁ : δ₁ * (w₁ * v₁) = F.l₁ n := by rw [hm₁]; exact Nat.mul_div_cancel' hd₁
    have he₂ : δ₂ * (w₂ * v₂) = F.l₂ n := by rw [hm₂]; exact Nat.mul_div_cancel' hd₂
    have hwv₁ : w₁ * v₁ ≠ 0 := by rw [hm₁]; exact hne₁
    have hw₁ : 0 < w₁ := Nat.pos_of_ne_zero (fun h => hwv₁ (by rw [h, Nat.zero_mul]))
    have hnE : F.α₂ * n + F.β₂ = δ₂ * (v₂ * w₂) := by
      rw [show δ₂ * (v₂ * w₂) = δ₂ * (w₂ * v₂) by ring, he₂]; rfl
    have hn' : (δ₂ * (v₂ * w₂) - F.β₂) / F.α₂ = n := by
      rw [← hnE, Nat.add_sub_cancel]; exact Nat.mul_div_cancel_left n hα₂
    have hv₁' : F.l₁ n / (δ₁ * w₁) = v₁ := by
      rw [show F.l₁ n = δ₁ * w₁ * v₁ by rw [← he₁]; ring]
      exact Nat.mul_div_cancel_left v₁ (Nat.mul_pos hδ₁ hw₁)
    simp only [hn', hv₁']
  · -- ④ `i ∘ j = id` on the triples
    rintro ⟨w₁, ⟨w₂, v₂⟩⟩ _
    rfl

/-- **B-5d — (5.6) is automatic**: a `w₁` with a non-empty `v₂`-count is coprime to `α`, `δ₂`
and `q`.  From the count's witness `v₂`: `w₂ > 0` (at `w₂ = 0` the first congruence forces
`α₂ ∣ β₂`, against (1.4) and `2 ≤ α₂`), so `T₁`'s second entry is the honest bound
`(α₂x+β₂)/(δ₂w₂)` and `v₂ > T₁` gives `δ₂v₂w₂ > α₂x+β₂ ≥ β₂`; that defines `n` with
`l₂(n) = δ₂v₂w₂`, and `five_eight_iff` turns (5.8) into `δ₁w₁ ∣ l₁(n)`.  The three legs then
read off `coprime_l₁_α₁`, `coprime_l` and the residue class of `w₁`. -/
theorem coprime_w₁_of_count_ne_zero (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ)
    (a₁ b₁ a₂ b₂ w₁ w₂ : ℕ) (_hq : 0 < q) (_hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (_hδ₁q : Nat.Coprime δ₁ q) (hb₁ : Nat.Coprime b₁ q) (_hb₂ : Nat.Coprime b₂ q)
    (hw₁b : w₁ ≡ b₁ [MOD q]) (_hw₂b : w₂ ≡ b₂ [MOD q])
    (h : ((Finset.Ioc ⌊hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂⌋₊ ⌊hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w₂⌋₊).filter
            (fun v₂ : ℕ =>
              δ₂ * (v₂ * w₂) ≡ F.β₂ [MOD F.α₂] ∧
              F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD F.α₂ * δ₁ * w₁] ∧
              F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁
                ≡ F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁ [MOD F.α₂ * q] ∧
              v₂ * w₂ ≡ a₂ * b₂ [MOD q])).card ≠ 0) :
    Nat.Coprime w₁ F.α ∧ Nat.Coprime w₁ δ₂ ∧ Nat.Coprime w₁ q := by
  obtain ⟨v₂, hv₂⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [Finset.mem_filter] at hv₂
  obtain ⟨hmem, h57, h58, _h59, _h510⟩ := hv₂
  have hα₂ : 0 < F.α₂ := lt_of_lt_of_le (by norm_num) F.two_le_α₂
  -- `w₂ > 0`, else (5.7) reads `α₂ ∣ β₂`
  have hw₂ : 0 < w₂ := by
    rcases Nat.eq_zero_or_pos w₂ with h0 | h0
    · exfalso
      rw [h0] at h57
      have hz : (0 : ℕ) ≡ F.β₂ [MOD F.α₂] := by simpa using h57
      have hd : F.α₂ ∣ F.β₂ := (Nat.modEq_zero_iff_dvd).mp hz.symm
      have hg : F.α₂ ∣ Nat.gcd F.α₂ F.β₂ := Nat.dvd_gcd dvd_rfl hd
      rw [show Nat.gcd F.α₂ F.β₂ = 1 from F.cop₂] at hg
      have h2 := F.two_le_α₂
      have h3 := Nat.le_of_dvd one_pos hg
      omega
    · exact h0
  have hδw : (0 : ℝ) < (δ₂ : ℝ) * (w₂ : ℝ) :=
    mul_pos (by exact_mod_cast hδ₂) (by exact_mod_cast hw₂)
  -- `T₁`'s second entry is a genuine lower bound, and it is nonnegative
  have hA : ((F.α₂ * x + F.β₂ : ℕ) : ℝ) / ((δ₂ : ℝ) * (w₂ : ℝ))
      ≤ hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hT₁nn : 0 ≤ hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ := le_trans (by positivity) hA
  have hmem' := (mem_Ioc_floor_iff hT₁nn v₂).mp hmem
  have hbig : ((F.α₂ * x + F.β₂ : ℕ) : ℝ) < (v₂ : ℝ) * ((δ₂ : ℝ) * (w₂ : ℝ)) :=
    (div_lt_iff₀ hδw).mp (lt_of_le_of_lt hA hmem'.1)
  have hbigN : F.α₂ * x + F.β₂ < v₂ * (δ₂ * w₂) := by exact_mod_cast hbig
  have hge : F.β₂ ≤ δ₂ * (v₂ * w₂) := by
    have hr : v₂ * (δ₂ * w₂) = δ₂ * (v₂ * w₂) := by ring
    omega
  -- the `n` the cell's witness names
  obtain ⟨n, hn⟩ := (Nat.modEq_iff_dvd' hge).mp h57.symm
  have hln : F.α₂ * n + F.β₂ = δ₂ * (v₂ * w₂) := by omega
  have hdvd : δ₁ * w₁ ∣ F.l₁ n :=
    (five_eight_iff F δ₁ δ₂ w₁ (v₂ * w₂) n hα₂.ne' hln).mp h58
  have hw₁l₁ : w₁ ∣ F.l₁ n := dvd_trans (dvd_mul_left w₁ δ₁) hdvd
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left F.α₁ F.α₂)
      (Nat.Coprime.coprime_dvd_left hw₁l₁ (F.coprime_l₁_α₁ n))
  · refine Nat.Coprime.coprime_dvd_right ?_
      (Nat.Coprime.coprime_dvd_left hw₁l₁ (F.coprime_l n))
    exact ⟨v₂ * w₂, by simp only [HBForms.l₂]; omega⟩
  · by_contra hcon
    obtain ⟨p, hp, hpw, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    have h1 : w₁ ≡ b₁ [MOD p] := Nat.ModEq.of_dvd hpq hw₁b
    have h2 : w₁ ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hpw
    have h3 : p ∣ b₁ := (Nat.modEq_zero_iff_dvd).mp (h1.symm.trans h2)
    have h4 : p ∣ Nat.gcd b₁ q := Nat.dvd_gcd h3 hpq
    rw [show Nat.gcd b₁ q = 1 from hb₁] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

/-! ### B-5f's four pieces — the `dite` construction of `C`, and the modulus facts -/

/-- **The residue `C` as a function of `w₁`.**  A bare `Classical.choose` does NOT type: B-4's
`∃` is fibred over `0 < w₁` and (5.6), so the choice is made under a `dite` whose fallback `1`
covers `w₁ = 0`.  This closes B-5f's FIRST conjunct. -/
noncomputable def kb5f_C (F : HBForms) (q δ₁ δ₂ a₁ b₁ a₂ b₂ : ℕ) (hq : 0 < q)
    (hδ₁ : 0 < δ₁)
    (hΔ : Nat.gcd F.α₁ q = Nat.gcd F.α₂ q)
    (hδ₁q : Nat.Coprime δ₁ q) (hδ₂q : Nat.Coprime δ₂ q)
    (hδ₁α : Nat.Coprime δ₁ F.α) (hδ₂α : Nat.Coprime δ₂ F.α) (hδ : Nat.Coprime δ₁ δ₂)
    (hab : Nat.Coprime (a₁ * b₁ * (a₂ * b₂)) q)
    (h54₁ : δ₁ * a₁ * b₁ ≡ F.β₁ [MOD Nat.gcd F.α₂ q])
    (h54₂ : δ₂ * a₂ * b₂ ≡ F.β₂ [MOD Nat.gcd F.α₂ q])
    (h55 : F.α₁ * (δ₂ * a₂ * b₂) + F.α₂ * F.β₁
            ≡ F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ [MOD q * F.α]) : ℕ → ℕ :=
  fun w₁ =>
    if h : 0 < w₁ ∧ Nat.Coprime w₁ F.α ∧ Nat.Coprime w₁ δ₂ ∧ Nat.Coprime w₁ q then
      Classical.choose (crt_collapse F q δ₁ δ₂ w₁ a₁ b₁ a₂ b₂ hq hδ₁ h.1 hΔ hδ₁q hδ₂q
        hδ₁α hδ₂α hδ h.2.1 h.2.2.1 h.2.2.2 hab h54₁ h54₂ h55)
    else 1

theorem kb5f_C_coprime (F : HBForms) (q δ₁ δ₂ a₁ b₁ a₂ b₂ : ℕ) (hq : 0 < q)
    (hδ₁ : 0 < δ₁)
    (hΔ : Nat.gcd F.α₁ q = Nat.gcd F.α₂ q)
    (hδ₁q : Nat.Coprime δ₁ q) (hδ₂q : Nat.Coprime δ₂ q)
    (hδ₁α : Nat.Coprime δ₁ F.α) (hδ₂α : Nat.Coprime δ₂ F.α) (hδ : Nat.Coprime δ₁ δ₂)
    (hab : Nat.Coprime (a₁ * b₁ * (a₂ * b₂)) q)
    (h54₁ : δ₁ * a₁ * b₁ ≡ F.β₁ [MOD Nat.gcd F.α₂ q])
    (h54₂ : δ₂ * a₂ * b₂ ≡ F.β₂ [MOD Nat.gcd F.α₂ q])
    (h55 : F.α₁ * (δ₂ * a₂ * b₂) + F.α₂ * F.β₁
            ≡ F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ [MOD q * F.α]) :
    ∀ w₁, Nat.Coprime w₁ F.α → Nat.Coprime w₁ δ₂ → Nat.Coprime w₁ q →
      Nat.Coprime (kb5f_C F q δ₁ δ₂ a₁ b₁ a₂ b₂ hq hδ₁ hΔ hδ₁q hδ₂q hδ₁α hδ₂α hδ hab h54₁ h54₂
        h55 w₁) (roadModulus F.α₂ q * δ₁ * w₁) := by
  intro w₁ hα hδ₂' hqq
  unfold kb5f_C
  split
  · rename_i h
    exact (Classical.choose_spec (crt_collapse F q δ₁ δ₂ w₁ a₁ b₁ a₂ b₂ hq hδ₁ h.1 hΔ hδ₁q hδ₂q
      hδ₁α hδ₂α hδ h.2.1 h.2.2.1 h.2.2.2 hab h54₁ h54₂ h55)).1
  · exact Nat.coprime_one_left _

/-- The ⟺ half of B-4, available at every `w₁` in the equation's filter — B-5f's termwise
rewrite through `Finset.filter_congr` has its input. -/
theorem kb5f_C_iff (F : HBForms) (q δ₁ δ₂ a₁ b₁ a₂ b₂ : ℕ) (hq : 0 < q)
    (hδ₁ : 0 < δ₁)
    (hΔ : Nat.gcd F.α₁ q = Nat.gcd F.α₂ q)
    (hδ₁q : Nat.Coprime δ₁ q) (hδ₂q : Nat.Coprime δ₂ q)
    (hδ₁α : Nat.Coprime δ₁ F.α) (hδ₂α : Nat.Coprime δ₂ F.α) (hδ : Nat.Coprime δ₁ δ₂)
    (hab : Nat.Coprime (a₁ * b₁ * (a₂ * b₂)) q)
    (h54₁ : δ₁ * a₁ * b₁ ≡ F.β₁ [MOD Nat.gcd F.α₂ q])
    (h54₂ : δ₂ * a₂ * b₂ ≡ F.β₂ [MOD Nat.gcd F.α₂ q])
    (h55 : F.α₁ * (δ₂ * a₂ * b₂) + F.α₂ * F.β₁
            ≡ F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ [MOD q * F.α]) :
    ∀ w₁, 0 < w₁ → Nat.Coprime w₁ F.α → Nat.Coprime w₁ δ₂ → Nat.Coprime w₁ q → ∀ X : ℕ,
      (δ₂ * X ≡ F.β₂ [MOD F.α₂] ∧
       F.α₁ * δ₂ * X + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD F.α₂ * δ₁ * w₁] ∧
       F.α₁ * δ₂ * X + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁ [MOD F.α₂ * q] ∧
       X ≡ a₂ * b₂ [MOD q])
      ↔ X ≡ kb5f_C F q δ₁ δ₂ a₁ b₁ a₂ b₂ hq hδ₁ hΔ hδ₁q hδ₂q hδ₁α hδ₂α hδ hab h54₁ h54₂ h55 w₁
            [MOD roadModulus F.α₂ q * δ₁ * w₁] := by
  intro w₁ hw hα hδ₂' hqq X
  unfold kb5f_C
  rw [dif_pos ⟨hw, hα, hδ₂', hqq⟩]
  exact (Classical.choose_spec (crt_collapse F q δ₁ δ₂ w₁ a₁ b₁ a₂ b₂ hq hδ₁ hw hΔ hδ₁q hδ₂q
    hδ₁α hδ₂α hδ hα hδ₂' hqq hab h54₁ h54₂ h55)).2 X

/-- `0 < k` at `k = D δ₁ w₁` — B-5e demands the `NeZero` instance and B-5f must build it. -/
theorem kb5f_k_pos (F : HBForms) (q δ₁ w₁ : ℕ) (hq : 0 < q) (hδ₁ : 0 < δ₁) (hw₁ : 0 < w₁) :
    0 < roadModulus F.α₂ q * δ₁ * w₁ := by
  have hα₂ : 0 < F.α₂ := lt_of_lt_of_le (by norm_num) F.two_le_α₂
  have : 0 < roadModulus F.α₂ q := by
    rw [roadModulus_eq_lcm]
    exact Nat.pos_of_ne_zero (fun h => by
      rcases Nat.lcm_eq_zero_iff.mp h with h' | h' <;> omega)
  positivity

/-- `2 ≤ k` — the next wave's own gate, recorded here where the modulus is built. -/
theorem kb5f_k_two (F : HBForms) (q δ₁ w₁ : ℕ) (hq : 0 < q) (hδ₁ : 0 < δ₁) (hw₁ : 0 < w₁) :
    2 ≤ roadModulus F.α₂ q * δ₁ * w₁ := by
  have h2 : 2 ≤ F.α₂ := F.two_le_α₂
  have hd : F.α₂ ∣ roadModulus F.α₂ q := dvd_roadModulus_left F.α₂ q
  have hpos : 0 < roadModulus F.α₂ q * δ₁ * w₁ := kb5f_k_pos F q δ₁ w₁ hq hδ₁ hw₁
  have : F.α₂ ≤ roadModulus F.α₂ q :=
    Nat.le_of_dvd (by rcases Nat.eq_zero_or_pos (roadModulus F.α₂ q) with h|h
                      · simp [h] at hpos
                      · exact h) hd
  calc 2 ≤ F.α₂ := h2
    _ ≤ roadModulus F.α₂ q := this
    _ ≤ roadModulus F.α₂ q * δ₁ := Nat.le_mul_of_pos_right _ hδ₁
    _ ≤ roadModulus F.α₂ q * δ₁ * w₁ := Nat.le_mul_of_pos_right _ hw₁

/-- `2 ∣ α`, the fact that makes B-5f's unrestricted `∀ w₁` harmless at `w₁ = 0`. -/
theorem kb5f_two_dvd_alpha (F : HBForms) : 2 ∣ F.α := Nat.dvd_gcd F.even₁ F.even₂


/-- **B-5f — (5.14)+(5.17) ASSEMBLED, the shape the next wave consumes**: under B-4's cell-level
hypotheses, the cell count is the double sum over `(w₁, w₂)` — `w₁` under (5.6), `w₂` coprime to
`k = D δ₁ w₁` — of `(T₂−T₁)/k + ψ((T₁ − C w̄₂)/k) − ψ((T₂ − C w̄₂)/k)`.

The chain: B-5c (in ℕ) cast to ℝ; B-5d restricts `w₁` (the zero-outside is the WHOLE inner
`w₂`-sum); B-4's ⟺ through `Finset.filter_congr` termwise, with `C` the `dite` choice `kb5f_C`;
B-5g restricts `w₂` to the classes coprime to `k`; the `T₂ ≤ T₁` terms drop because their `Ioc`
is empty; and B-5e closes each term, with `[NeZero k]` from `kb5f_k_pos` and `0 ≤ T₁` supplied as
an ASCRIBED `have` (inlined it unfolds `hbT₁` and B-5e stops matching).  `hb₁`/`hb₂` come from
`hab`; `hR₂` is redundant in truth and stays. -/
theorem cellCount_eq_sum_sawtooth (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ)
    (a₁ b₁ a₂ b₂ : ℕ) (hq : 0 < q) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hR₂ : 0 < R₂)
    (hΔ : Nat.gcd F.α₁ q = Nat.gcd F.α₂ q)
    (hδ₁q : Nat.Coprime δ₁ q) (hδ₂q : Nat.Coprime δ₂ q)
    (hδ₁α : Nat.Coprime δ₁ F.α) (hδ₂α : Nat.Coprime δ₂ F.α) (hδ : Nat.Coprime δ₁ δ₂)
    (hab : Nat.Coprime (a₁ * b₁ * (a₂ * b₂)) q)
    (h54₁ : δ₁ * a₁ * b₁ ≡ F.β₁ [MOD Nat.gcd F.α₂ q])
    (h54₂ : δ₂ * a₂ * b₂ ≡ F.β₂ [MOD Nat.gcd F.α₂ q])
    (h55 : F.α₁ * (δ₂ * a₂ * b₂) + F.α₂ * F.β₁
            ≡ F.α₂ * (δ₁ * a₁ * b₁) + F.α₁ * F.β₂ [MOD q * F.α]) :
    ∃ C : ℕ → ℕ,
      (∀ w₁, Nat.Coprime w₁ F.α → Nat.Coprime w₁ δ₂ → Nat.Coprime w₁ q →
        Nat.Coprime (C w₁) (roadModulus F.α₂ q * δ₁ * w₁)) ∧
      (cellCount F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ : ℝ)
        = ∑ w₁ ∈ (Finset.Icc 1 ⌊2 * S₁⌋₊).filter (fun w : ℕ => S₁ < (w : ℝ) ∧ w ≡ b₁ [MOD q] ∧
              Nat.Coprime w F.α ∧ Nat.Coprime w δ₂ ∧ Nat.Coprime w q),
          ∑ w₂ ∈ (Finset.Icc 1 ⌊2 * S₂⌋₊).filter (fun w : ℕ => S₂ < (w : ℝ) ∧ w ≡ b₂ [MOD q] ∧
              Nat.Coprime w (roadModulus F.α₂ q * δ₁ * w₁) ∧
              hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w < hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w),
            ((hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w₂ - hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂)
                / (roadModulus F.α₂ q * δ₁ * w₁ : ℕ)
              + sawtooth ((hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂
                  - C w₁ * invMod w₂ (roadModulus F.α₂ q * δ₁ * w₁))
                    / (roadModulus F.α₂ q * δ₁ * w₁ : ℕ))
              - sawtooth ((hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w₂
                  - C w₁ * invMod w₂ (roadModulus F.α₂ q * δ₁ * w₁))
                    / (roadModulus F.α₂ q * δ₁ * w₁ : ℕ))) := by
  classical
  have hb₁ : Nat.Coprime b₁ q :=
    Nat.Coprime.coprime_dvd_left (Dvd.dvd.mul_right (dvd_mul_left b₁ a₁) (a₂ * b₂)) hab
  have hb₂ : Nat.Coprime b₂ q :=
    Nat.Coprime.coprime_dvd_left ((dvd_mul_left b₂ a₂).mul_left (a₁ * b₁)) hab
  refine ⟨kb5f_C F q δ₁ δ₂ a₁ b₁ a₂ b₂ hq hδ₁ hΔ hδ₁q hδ₂q hδ₁α hδ₂α hδ hab h54₁ h54₂ h55,
    kb5f_C_coprime F q δ₁ δ₂ a₁ b₁ a₂ b₂ hq hδ₁ hΔ hδ₁q hδ₂q hδ₁α hδ₂α hδ hab h54₁ h54₂ h55,
    ?_⟩
  -- ① B-5c, cast to ℝ
  rw [cellCount_eq_sum_w F q x δ₁ δ₂ R₁ S₁ R₂ S₂ a₁ b₁ a₂ b₂ hq hδ₁ hδ₂ hR₂ hδ₁q hb₁ hb₂]
  push_cast
  -- ② B-5d restricts `w₁`
  rw [← Finset.sum_subset (s₁ := (Finset.Icc 1 ⌊2 * S₁⌋₊).filter
      (fun w : ℕ => S₁ < (w : ℝ) ∧ w ≡ b₁ [MOD q] ∧
        Nat.Coprime w F.α ∧ Nat.Coprime w δ₂ ∧ Nat.Coprime w q))
    (s₂ := (Finset.Icc 1 ⌊2 * S₁⌋₊).filter (fun w : ℕ => S₁ < (w : ℝ) ∧ w ≡ b₁ [MOD q]))
    ?_ ?_]
  · -- ③ termwise in `w₁`
    refine Finset.sum_congr rfl (fun w₁ hw₁mem => ?_)
    rw [Finset.mem_filter] at hw₁mem
    obtain ⟨hw₁Icc, hS₁a, hb₁', hw₁α, hw₁δ₂, hw₁q⟩ := hw₁mem
    have hw₁ : 0 < w₁ := (Finset.mem_Icc.mp hw₁Icc).1
    have hkpos : 0 < roadModulus F.α₂ q * δ₁ * w₁ := kb5f_k_pos F q δ₁ w₁ hq hδ₁ hw₁
    have hCcop := kb5f_C_coprime F q δ₁ δ₂ a₁ b₁ a₂ b₂ hq hδ₁ hΔ hδ₁q hδ₂q hδ₁α hδ₂α hδ hab
      h54₁ h54₂ h55 w₁ hw₁α hw₁δ₂ hw₁q
    have hCiff := kb5f_C_iff F q δ₁ δ₂ a₁ b₁ a₂ b₂ hq hδ₁ hΔ hδ₁q hδ₂q hδ₁α hδ₂α hδ hab
      h54₁ h54₂ h55 w₁ hw₁ hw₁α hw₁δ₂ hw₁q
    -- B-4's ⟺, termwise on the `v₂`-filter
    have hfilter : ∀ w₂ : ℕ,
        ((Finset.Ioc ⌊hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂⌋₊ ⌊hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w₂⌋₊).filter
          (fun v₂ : ℕ =>
            δ₂ * (v₂ * w₂) ≡ F.β₂ [MOD F.α₂] ∧
            F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD F.α₂ * δ₁ * w₁] ∧
            F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁
              ≡ F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁ [MOD F.α₂ * q] ∧
            v₂ * w₂ ≡ a₂ * b₂ [MOD q]))
        = (Finset.Ioc ⌊hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂⌋₊ ⌊hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w₂⌋₊).filter
          (fun v₂ : ℕ => v₂ * w₂
            ≡ kb5f_C F q δ₁ δ₂ a₁ b₁ a₂ b₂ hq hδ₁ hΔ hδ₁q hδ₂q hδ₁α hδ₂α hδ hab h54₁ h54₂ h55 w₁
              [MOD roadModulus F.α₂ q * δ₁ * w₁]) := by
      intro w₂
      exact Finset.filter_congr (fun v₂ _ => hCiff (v₂ * w₂))
    simp only [hfilter]
    -- ④ B-5g restricts `w₂` to the coprime classes, and the empty `Ioc`s drop
    rw [← Finset.sum_subset (s₁ := (Finset.Icc 1 ⌊2 * S₂⌋₊).filter
        (fun w : ℕ => S₂ < (w : ℝ) ∧ w ≡ b₂ [MOD q] ∧
          Nat.Coprime w (roadModulus F.α₂ q * δ₁ * w₁) ∧
          hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w < hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w))
      (s₂ := (Finset.Icc 1 ⌊2 * S₂⌋₊).filter (fun w : ℕ => S₂ < (w : ℝ) ∧ w ≡ b₂ [MOD q]))
      ?_ ?_]
    · -- ⑤ B-5e, termwise in `w₂`
      refine Finset.sum_congr rfl (fun w₂ hw₂mem => ?_)
      rw [Finset.mem_filter] at hw₂mem
      obtain ⟨_, _, _, hw₂k, hT⟩ := hw₂mem
      haveI : NeZero (roadModulus F.α₂ q * δ₁ * w₁) := ⟨hkpos.ne'⟩
      have h0 : (0 : ℝ) ≤ hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w₂ :=
        (hbT₁_pos F x δ₁ δ₂ R₁ R₂ w₁ w₂ hR₂).le
      have hkey := card_count_eq_sawtooth (roadModulus F.α₂ q * δ₁ * w₁) hw₂k
        (kb5f_C F q δ₁ δ₂ a₁ b₁ a₂ b₂ hq hδ₁ hΔ hδ₁q hδ₂q hδ₁α hδ₂α hδ hab h54₁ h54₂ h55 w₁)
        h0 hT.le
      push_cast at hkey ⊢
      linarith [hkey]
    · intro w hw
      rw [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, hw.2.1, hw.2.2.1⟩
    · intro w hwin hwout
      rw [Finset.mem_filter] at hwin
      by_cases hck : Nat.Coprime w (roadModulus F.α₂ q * δ₁ * w₁)
      · have hT : ¬ (hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w < hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w) := by
          intro hlt
          exact hwout (Finset.mem_filter.mpr ⟨hwin.1, hwin.2.1, hwin.2.2, hck, hlt⟩)
        have hfl : ⌊hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w⌋₊ ≤ ⌊hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w⌋₊ :=
          Nat.floor_le_floor (not_lt.mp hT)
        have hemp : Finset.Ioc ⌊hbT₁ F x δ₁ δ₂ R₁ R₂ w₁ w⌋₊ ⌊hbT₂ F x δ₁ δ₂ R₁ R₂ w₁ w⌋₊ = ∅ :=
          Finset.Ioc_eq_empty (by omega)
        rw [hemp, Finset.filter_empty, Finset.card_empty]
        norm_num
      · rw [count_eq_zero_of_not_coprime hCcop hck]
        norm_num
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, hw.2.1, hw.2.2.1⟩
  · intro w hwin hwout
    rw [Finset.mem_filter] at hwin
    refine Finset.sum_eq_zero (fun w₂ hw₂ => ?_)
    rw [Finset.mem_filter] at hw₂
    by_contra hc
    have hcard : ((Finset.Ioc ⌊hbT₁ F x δ₁ δ₂ R₁ R₂ w w₂⌋₊ ⌊hbT₂ F x δ₁ δ₂ R₁ R₂ w w₂⌋₊).filter
        (fun v₂ : ℕ =>
          δ₂ * (v₂ * w₂) ≡ F.β₂ [MOD F.α₂] ∧
          F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁ ≡ F.α₁ * F.β₂ [MOD F.α₂ * δ₁ * w] ∧
          F.α₁ * δ₂ * (v₂ * w₂) + F.α₂ * F.β₁
            ≡ F.α₁ * F.β₂ + F.α₂ * δ₁ * a₁ * b₁ [MOD F.α₂ * q] ∧
          v₂ * w₂ ≡ a₂ * b₂ [MOD q])).card ≠ 0 := by
      intro h0
      exact hc (by rw [h0]; norm_num)
    obtain ⟨hα, hδ₂', hqq⟩ := coprime_w₁_of_count_ne_zero F q x δ₁ δ₂ R₁ R₂ a₁ b₁ a₂ b₂ w w₂
      hq hδ₁ hδ₂ hδ₁q hb₁ hb₂ hwin.2.2 hw₂.2.2 hcard
    exact hwout (Finset.mem_filter.mpr ⟨hwin.1, hwin.2.1, hwin.2.2, hα, hδ₂', hqq⟩)

end Salt.N7
