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
  have hdwα₁ : Nat.Coprime (δ₁ * w₁) F.α₁ := hδ₁α₁.mul hw₁α₁
  have hdwα₂ : Nat.Coprime (δ₁ * w₁) F.α₂ := hδ₁α₂.mul hw₁α₂
  have hdwq : Nat.Coprime (δ₁ * w₁) q := hδ₁q.mul hw₁q
  have hdwδ₂ : Nat.Coprime (δ₁ * w₁) δ₂ := hδ.mul hw₁δ₂
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

end Salt.N7
