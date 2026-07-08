/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard

/-!
# The admissible tuple (blueprint M1)

`H k`, the concrete admissible `k`-tuple used by the Maynard track: the
first `k` primes strictly greater than `k`. Reproves the fixed-`W`-trick's
existence statement (`exists_nu0`) via a genuine (if small) CRT
construction over the finite set of primes dividing `W k`.
-/

namespace Salt.Maynard

open Finset

/-! ## N1.1 — admissibility -/

/-- A finite set of naturals `H` is *admissible*: for every prime `p`,
some residue class mod `p` is missed by every element of `H` (so `H`
can avoid all residues `0 (mod p)` simultaneously via a shift). -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

theorem Admissible.mono {H H' : Finset ℕ} (hH' : H' ⊆ H) (h : Admissible H) :
    Admissible H' := by
  intro p hp
  obtain ⟨a, ha⟩ := h p hp
  exact ⟨a, fun h hh => ha h (hH' hh)⟩

/-! ## N1.2 — the concrete tuple -/

/-- The index (in the increasing enumeration of all primes) of the first
prime strictly greater than `k`: `Nat.count Nat.Prime (k+1)` primes are
`≤ k`, so this is exactly that count. -/
def firstIdxAboveK (k : ℕ) : ℕ := Nat.count Nat.Prime (k + 1)

/-- The `k`-tuple: the first `k` primes strictly greater than `k`. -/
noncomputable def H (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => Nat.nth Nat.Prime (firstIdxAboveK k + i))

theorem H_card (k : ℕ) : (H k).card = k := by
  unfold H
  rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro a b hab
  have := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hab
  omega

theorem H_prime (k : ℕ) {h : ℕ} (hh : h ∈ H k) : h.Prime := by
  unfold H at hh
  simp only [Finset.mem_image, Finset.mem_range] at hh
  obtain ⟨i, _, rfl⟩ := hh
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

theorem firstIdxAboveK_gt (k : ℕ) : k < Nat.nth Nat.Prime (firstIdxAboveK k) := by
  unfold firstIdxAboveK
  by_contra hle
  push Not at hle
  have hmem : Nat.Prime (Nat.nth Nat.Prime (Nat.count Nat.Prime (k+1))) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
  have hle' : Nat.nth Nat.Prime (Nat.count Nat.Prime (k+1)) + 1 ≤ k + 1 := by omega
  have hcount_le : Nat.count Nat.Prime (Nat.nth Nat.Prime (Nat.count Nat.Prime (k+1)) + 1)
      ≤ Nat.count Nat.Prime (k + 1) := Nat.count_monotone Nat.Prime hle'
  have heq : Nat.count Nat.Prime (Nat.nth Nat.Prime (Nat.count Nat.Prime (k+1)) + 1)
      = Nat.count Nat.Prime (k+1) + 1 := by
    rw [Nat.count_succ, if_pos hmem]
    congr 1
    exact Nat.count_nth_of_infinite Nat.infinite_setOf_prime _
  omega

theorem H_gt_k (k : ℕ) {h : ℕ} (hh : h ∈ H k) : k < h := by
  unfold H at hh
  simp only [Finset.mem_image, Finset.mem_range] at hh
  obtain ⟨i, _, rfl⟩ := hh
  have hbase := firstIdxAboveK_gt k
  have hmono := (Nat.nth_strictMono Nat.infinite_setOf_prime)
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · simp [hi0]; omega
  · have : Nat.nth Nat.Prime (firstIdxAboveK k) < Nat.nth Nat.Prime (firstIdxAboveK k + i) :=
      hmono (by omega)
    omega

/-! ## N1.3 — `H k` is admissible -/

theorem H_admissible (k : ℕ) : Admissible (H k) := by
  intro p hp
  by_cases hpk : p ≤ k
  · exact ⟨0, fun h hh => by
      have hhp := H_prime k hh
      have hhk := H_gt_k k hh
      intro hcontra
      have hdvd : p ∣ h := (ZMod.natCast_eq_zero_iff h p).mp hcontra
      have := (Nat.prime_dvd_prime_iff_eq hp hhp).mp hdvd
      omega⟩
  · push Not at hpk
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    have hcard : ((H k).image (fun h : ℕ => (h : ZMod p))).card < Fintype.card (ZMod p) := by
      calc ((H k).image (fun h : ℕ => (h : ZMod p))).card ≤ (H k).card :=
            Finset.card_image_le
        _ = k := H_card k
        _ < p := hpk
        _ = Fintype.card (ZMod p) := (ZMod.card p).symm
    obtain ⟨a, ha⟩ : ∃ a : ZMod p, a ∉ (H k).image (fun h : ℕ => (h : ZMod p)) := by
      by_contra hc
      push Not at hc
      have : (H k).image (fun h : ℕ => (h : ZMod p)) = Finset.univ :=
        Finset.eq_univ_of_forall hc
      rw [this, Finset.card_univ] at hcard
      exact lt_irrefl _ hcard
    exact ⟨a, fun h hh hcontra => ha (hcontra ▸ Finset.mem_image_of_mem _ hh)⟩

/-! ## N1.4 — the W-trick: fixed modulus, existence of `ν₀` -/

/-- `D₀ k` is a fixed threshold `≥ k³` and `≥` every element of `H k`.
The `k³` floor is load-bearing (N2.0 design freeze, 2026-07-07): every
coprimality-correction estimate in M4/M5 has shape `poly(k)/D₀` and
needs `D₀ ≥ k³` to be `O(1/k)`; the original `max k (sup H) ≈ 2k log k`
was too small (caught by the N2.0 adversarial review — all downstream
M1 proofs are magnitude-agnostic, so only this def changed). -/
noncomputable def D₀ (k : ℕ) : ℕ := max (k ^ 3) ((H k).sup id)

/-- The fixed sieve modulus: the primorial of `D₀ k`. -/
noncomputable def W (k : ℕ) : ℕ := primorial (D₀ k)

/-- A finite product of (distinct) primes is squarefree. -/
private lemma prod_primes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hap (hsp p hp)).mpr (by rintro rfl; exact ha hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, hap.squarefree, ih hsp⟩

/-- The primorial is squarefree. Reproved locally (rather than importing
`Salt.Brun.M5Assembly`, whose import graph pulls in the whole Brun sieve
stack) — a 3-line induction, as anticipated by the brief. -/
theorem W_squarefree (k : ℕ) : Squarefree (W k) := by
  unfold W primorial
  exact prod_primes_squarefree (fun _p hp => (Finset.mem_filter.mp hp).2)

/-- **N1.4.** There is a residue `ν₀ mod W k` such that `ν₀ + h` is
coprime to `W k` for every `h ∈ H k`.

Route: strong induction on the (finite) `Finset` of prime factors of
`W k`, folding in one CRT step (`Nat.chineseRemainder`) per prime. For
each prime `p ∣ W k`, `H_admissible k` supplies a residue `a_p : ZMod p`
avoided by `H k`; taking `ν₀ ≡ -a_p (mod p)` (via `ZMod.val`) makes
`ν₀ + h ≢ 0 (mod p)` for every `h ∈ H k`. The final coprimality
statement is assembled from the per-prime non-divisibility facts via
`Nat.coprime_of_dvd` (`W k` squarefree, hence `Nat.Coprime m (W k) ↔
∀ p, p.Prime → p ∣ W k → ¬ p ∣ m` reduces to `Nat.coprime_of_dvd`'s
hypothesis directly, no squarefreeness needed beyond it not mattering
here). -/
theorem exists_nu0 (k : ℕ) :
    ∃ ν₀ : ℕ, ∀ h ∈ H k, Nat.Coprime (ν₀ + h) (W k) := by
  -- For each prime `p`, a residue `r p : ℕ` with `r p < p` (when `p ≠ 0`)
  -- such that `(r p + h) % p ≠ 0` for every `h ∈ H k` — obtained from the
  -- admissibility witness `a_p` by negating and taking `ZMod.val`.
  have hex : ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ h ∈ H k, ¬ p ∣ (r + h) := by
    intro p hp
    obtain ⟨a, ha⟩ := H_admissible k p hp
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    refine ⟨(-a).val, fun h hh hdvd => ?_⟩
    have : ((-a).val + h : ZMod p) = 0 := by
      have := (ZMod.natCast_eq_zero_iff ((-a).val + h) p).mpr hdvd
      exact_mod_cast this
    rw [ZMod.natCast_val, ZMod.cast_id] at this
    have haux : (h : ZMod p) = a := by linear_combination this
    exact ha h hh haux
  -- Strong induction over the (finite) Finset of prime factors of `W k`,
  -- combining the per-prime residues via `Nat.chineseRemainder`.
  suffices hgen : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      ∃ ν₀ : ℕ, ∀ h ∈ H k, ∀ p ∈ s, ¬ p ∣ (ν₀ + h) by
    obtain ⟨ν₀, hν₀⟩ := hgen (W k).primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    refine ⟨ν₀, fun h hh => ?_⟩
    apply Nat.coprime_of_dvd
    intro p hpp hpdvd hpdvdW
    have hWne : W k ≠ 0 := (W_squarefree k).ne_zero
    exact hν₀ h hh p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvdW, hWne⟩) hpdvd
  intro s
  induction s using Finset.induction with
  | empty => exact fun _ => ⟨0, fun _ _ p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert p s hps ih =>
    intro hprimes
    have hpp : p.Prime := hprimes p (Finset.mem_insert_self p s)
    have hsprimes : ∀ q ∈ s, q.Prime := fun q hq => hprimes q (Finset.mem_insert_of_mem hq)
    obtain ⟨ν₁, hν₁⟩ := ih hsprimes
    obtain ⟨r, hr⟩ := hex p hpp
    -- Combine modulus `p` (target residue `r`) with modulus `∏ q ∈ s, q`
    -- (target residue `ν₁`) via CRT; `p ∉ s` (all primes, `s`'s elements
    -- distinct from `p`) gives coprimality of the two moduli.
    set M := ∏ q ∈ s, q with hM
    have hMcop : p.Coprime M := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpp (hsprimes q hq)).mpr (by rintro rfl; exact hps hq)
    obtain ⟨ν₀, hν₀p, hν₀M⟩ := Nat.chineseRemainder hMcop r ν₁
    refine ⟨ν₀, fun h hh q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with hqp | hqs
    · -- `q = p`: `ν₀ ≡ r (mod p)`, and `r` was chosen so `p ∤ r + h`.
      intro hdvd
      rw [hqp] at hdvd
      have h1 : ν₀ + h ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdvd
      have h2 : ν₀ + h ≡ r + h [MOD p] := hν₀p.add_right h
      exact hr h hh (Nat.modEq_zero_iff_dvd.mp (h2.symm.trans h1))
    · -- `q ∈ s`: `ν₀ ≡ ν₁ (mod M)`, reduce mod `q` via `q ∣ M`.
      intro hdvd
      have hqM : q ∣ M := Finset.dvd_prod_of_mem _ hqs
      have h1 : ν₀ + h ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hdvd
      have h2 : ν₀ + h ≡ ν₁ + h [MOD q] := (hν₀M.of_dvd hqM).add_right h
      exact hν₁ h hh q hqs (Nat.modEq_zero_iff_dvd.mp (h2.symm.trans h1))

/-! ## Indexed enumeration of the tuple (shared M2/M4/M5 infrastructure)

`H k` is a `Finset`; the k-dimensional sieve needs it as an ordered tuple
`Fin k → ℕ`. `hSeq k i` is the `i`-th prime in the enumeration used to
build `H k` (so `hSeq k` is injective with image `H k`). Added here (not
in a downstream file) so every M2 node imports a stable definition. -/

/-- The `i`-th element of the tuple `H k`, as a function `Fin k → ℕ`. -/
noncomputable def hSeq (k : ℕ) (i : Fin k) : ℕ :=
  Nat.nth Nat.Prime (firstIdxAboveK k + (i : ℕ))

theorem hSeq_prime (k : ℕ) (i : Fin k) : (hSeq k i).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

theorem hSeq_injective (k : ℕ) : Function.Injective (hSeq k) := by
  intro i j hij
  unfold hSeq at hij
  have := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hij
  exact Fin.ext (by omega)

theorem hSeq_mem_H (k : ℕ) (i : Fin k) : hSeq k i ∈ H k := by
  unfold H hSeq
  rw [Finset.mem_image]
  exact ⟨(i : ℕ), Finset.mem_range.mpr i.isLt, rfl⟩

theorem hSeq_gt_k (k : ℕ) (i : Fin k) : k < hSeq k i := by
  unfold hSeq
  have hbase := firstIdxAboveK_gt k
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
  · rw [hi0, Nat.add_zero]; exact hbase
  · have : Nat.nth Nat.Prime (firstIdxAboveK k)
        < Nat.nth Nat.Prime (firstIdxAboveK k + (i : ℕ)) :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime) (by omega)
    omega

theorem hSeq_le_D₀ (k : ℕ) (i : Fin k) : hSeq k i ≤ D₀ k :=
  le_trans (Finset.le_sup (f := id) (hSeq_mem_H k i)) (le_max_right _ _)

end Salt.Maynard
