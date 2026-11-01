/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard

/-!
# The admissible tuple (blueprint M1)

The Maynard track's admissible `k`-tuple. The chain downstream of this file uses its tuple only
through the lemmas stated here (injectivity, membership, cardinality, admissibility, the `D₀`
bounds), so the tuple is a **choice**: the class `TupleChoice` carries it, and the default instance
`stdTuple` is the standard one, the first `k` primes strictly greater than `k`. A statement proved
under `[TupleChoice]` holds for every admissible choice; a caller with no other instance in scope
gets `stdTuple`.

Reproves the fixed-`W`-trick's existence statement (`exists_nu0`) via a genuine (if small) CRT
construction over the finite set of primes dividing `W k`.
-/

namespace Salt.Maynard

open Finset

-- A section `[TupleChoice]` is included in every declaration of the section; the ones that do not
-- use it (e.g. `prod_primes_squarefree`) would otherwise each raise `unusedSectionVars`.
set_option linter.unusedSectionVars false

/-! ## N1.1 — admissibility -/

/-- A finite set of naturals `H` is *admissible*: for every prime `p`,
some residue class mod `p` is missed by every element of `H` (so `H`
can avoid all residues `0 (mod p)` simultaneously via a shift). -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- A subset of an admissible set is admissible: the class `a` missed by every `h ∈ H` at a
prime `p` is missed by every `h ∈ H' ⊆ H` (`hH'`). -/
theorem Admissible.mono {H H' : Finset ℕ} (hH' : H' ⊆ H) (h : Admissible H) :
    Admissible H' := by
  intro p hp
  obtain ⟨a, ha⟩ := h p hp
  exact ⟨a, fun h hh => ha h (hH' hh)⟩

/-- **Admissibility is decided at the small primes.** A prime `p > #S` cannot be covered by the
`#S` residues of `S`, so only the primes `p ≤ #S` need a missed class. -/
theorem admissible_of_small_primes {S : Finset ℕ}
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ S.card → ∃ a : ZMod p, ∀ h ∈ S, (h : ZMod p) ≠ a) :
    Admissible S := by
  intro p hp
  by_cases hpk : p ≤ S.card
  · exact hsmall p hp hpk
  · push Not at hpk
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    have hcard : (S.image (fun h : ℕ => (h : ZMod p))).card < Fintype.card (ZMod p) := by
      calc (S.image (fun h : ℕ => (h : ZMod p))).card ≤ S.card := Finset.card_image_le
        _ < p := hpk
        _ = Fintype.card (ZMod p) := (ZMod.card p).symm
    obtain ⟨a, ha⟩ : ∃ a : ZMod p, a ∉ S.image (fun h : ℕ => (h : ZMod p)) := by
      by_contra hc
      push Not at hc
      have : S.image (fun h : ℕ => (h : ZMod p)) = Finset.univ :=
        Finset.eq_univ_of_forall hc
      rw [this, Finset.card_univ] at hcard
      exact lt_irrefl _ hcard
    exact ⟨a, fun h hh hcontra => ha (hcontra ▸ Finset.mem_image_of_mem _ hh)⟩

/-! ## N1.2 — the standard tuple -/

/-- The index (in the increasing enumeration of all primes) of the first
prime strictly greater than `k`: `Nat.count Nat.Prime (k+1)` primes are
`≤ k`, so this is exactly that count. -/
def firstIdxAboveK (k : ℕ) : ℕ := Nat.count Nat.Prime (k + 1)

/-- The standard tuple: its `i`-th entry is the `i`-th prime strictly greater than `k`. -/
noncomputable def stdSeq (k : ℕ) (i : Fin k) : ℕ :=
  Nat.nth Nat.Prime (firstIdxAboveK k + (i : ℕ))

/-- Every entry of the standard tuple is prime: `Nat.nth Nat.Prime n` is a prime for every `n`
because the primes are infinite (`Nat.nth_mem_of_infinite`, `Nat.infinite_setOf_prime`). -/
theorem stdSeq_prime (k : ℕ) (i : Fin k) : (stdSeq k i).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

/-- `stdSeq k` is injective: `Nat.nth Nat.Prime` is strictly monotone on the infinite set of
primes (`Nat.nth_strictMono`), so equal entries have equal indices `firstIdxAboveK k + i`, hence
`i = j` (`Fin.ext`, `omega`). The `inj` field of `stdTuple`. -/
theorem stdSeq_injective (k : ℕ) : Function.Injective (stdSeq k) := by
  intro i j hij
  unfold stdSeq at hij
  have := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hij
  exact Fin.ext (by omega)

/-- The prime at index `firstIdxAboveK k = count Prime (k + 1)` exceeds `k`: were it `≤ k`,
counting the primes below it and itself (`Nat.count_succ` at a prime,
`Nat.count_nth_of_infinite`) would read `count (k + 1) + 1 ≤ count (k + 1)` by
`Nat.count_monotone`. The base case of `stdSeq_gt_k`. -/
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

/-- Every entry of the standard tuple exceeds `k`: the entry at `i = 0` is `firstIdxAboveK_gt`,
and a later entry is larger by `Nat.nth_strictMono`. It supplies the missed class `0` at the
primes `p ≤ k` in `std_admissible`, and `hSeq_gt_k` · `H_gt_k` at `stdTuple`. -/
theorem stdSeq_gt_k (k : ℕ) (i : Fin k) : k < stdSeq k i := by
  unfold stdSeq
  have hbase := firstIdxAboveK_gt k
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
  · rw [hi0, Nat.add_zero]; exact hbase
  · have : Nat.nth Nat.Prime (firstIdxAboveK k)
        < Nat.nth Nat.Prime (firstIdxAboveK k + (i : ℕ)) :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime) (by omega)
    omega

/-- **N1.3 for the standard tuple.** Every entry is a prime `> k`, so at a prime `p ≤ k` the
class `0` is missed; the primes `p > k` are free (`admissible_of_small_primes`). -/
theorem std_admissible (k : ℕ) : Admissible ((Finset.univ : Finset (Fin k)).image (stdSeq k)) := by
  apply admissible_of_small_primes
  intro p hp hpS
  have hpk : p ≤ k :=
    hpS.trans (Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin]))
  refine ⟨0, fun h hh hcontra => ?_⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
  have hhp := stdSeq_prime k i
  have hhk := stdSeq_gt_k k i
  have hdvd : p ∣ stdSeq k i := (ZMod.natCast_eq_zero_iff _ p).mp hcontra
  have := (Nat.prime_dvd_prime_iff_eq hp hhp).mp hdvd
  omega

/-- Chebyshev count bound: `π(k) + k ≤ π(k³)` (there are `≥ k` primes in `(k, k³]`),
via `Chebyshev.pi_ge`.  Holds for `k ≥ 20`. (Moved here from `Lemma53Tight`, 2026-10-13.) -/
private lemma count_le_count_cube (k : ℕ) (hk : 20 ≤ k) :
    Nat.count Nat.Prime (k + 1) + k ≤ Nat.count Nat.Prime (k ^ 3 + 1) := by
  have hk1 : 1 < k := by omega
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk20R : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk : 0 < Real.log k := Real.log_pos hkR
  have hlogcube : Real.log ((k:ℝ)^3) = 3 * Real.log k := by rw [Real.log_pow]; push_cast; ring
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog2le : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hL : Real.log k ≤ (k:ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (k:ℝ) by linarith); linarith
  have hk3nn : (0:ℝ) ≤ (k:ℝ)^3 := by positivity
  have hk3one : (1:ℝ) ≤ (k:ℝ)^3 := one_le_pow₀ (by linarith)
  have hlogcube1 : Real.log ((k:ℝ)^3 + 1) ≤ Real.log 2 + 3 * Real.log k := by
    have h1 : (k:ℝ)^3 + 1 ≤ 2 * (k:ℝ)^3 := by linarith [hk3one]
    calc Real.log ((k:ℝ)^3+1) ≤ Real.log (2 * (k:ℝ)^3) := Real.log_le_log (by positivity) h1
      _ = Real.log 2 + Real.log ((k:ℝ)^3) := by rw [Real.log_mul (by norm_num) (by positivity)]
      _ = Real.log 2 + 3 * Real.log k := by rw [hlogcube]
  have hcubic : 6*(k:ℝ)^2 + 6*(k:ℝ) + 1 ≤ (k:ℝ)^3 / 2 := by
    nlinarith only [hk20R, mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) - 20 by linarith)
        (sq_nonneg (k : ℝ)), (Nat.cast_nonneg _ : 0 ≤ ↑k)]
  have e2 : 6*(k:ℝ)*Real.log k ≤ 6*(k:ℝ)^2 := by nlinarith only [hL, (Nat.cast_nonneg _ : 0 ≤ ↑k)]
  have e4 : Real.log ((k:ℝ)^3+1) ≤ 1 + 3*(k:ℝ) := by linarith only [hlogcube1, hL, hlog2le]
  have hk3log2 : (k:ℝ)^3/2 ≤ (k:ℝ)^3 * Real.log 2 := by nlinarith only [hlog2, hk3nn]
  have hkey : (2*(k:ℝ)+1)*(3*Real.log k) ≤ (k:ℝ)^3 * Real.log 2 - Real.log ((k:ℝ)^3+1) := by
    linarith only [hk3log2, e2, hcubic, hlogcube1, hL, hlog2le]
  have hpi := Chebyshev.pi_ge (k ^ 3)
  rw [show ((k ^ 3 : ℕ) : ℝ) = (k : ℝ) ^ 3 by norm_cast] at hpi
  rw [hlogcube] at hpi
  have h3logk : 0 < 3 * Real.log k := by linarith
  have hpi2 : 2*(k:ℝ)+1 ≤ (Nat.primeCounting (k^3):ℝ) := by
    refine le_trans ?_ hpi
    rw [le_div_iff₀ h3logk]; exact hkey
  have hpc : Nat.primeCounting (k ^ 3) = Nat.count Nat.Prime (k ^ 3 + 1) := rfl
  have hnat : 2 * k + 1 ≤ Nat.primeCounting (k^3) := by
    have : (2*k+1 : ℝ) ≤ (Nat.primeCounting (k^3):ℝ) := by linarith [hpi2]
    exact_mod_cast this
  have hcnt : Nat.count Nat.Prime (k + 1) ≤ k + 1 := Nat.count_le Nat.Prime
  rw [← hpc]; omega

/-- The largest entry of the standard tuple (the `k`-th prime above `k`) is `≤ k³`, since
`π(k³) − π(k) ≥ k`.  Holds for `k ≥ 20`. -/
theorem std_sup_le_cube (k : ℕ) (hk : 20 ≤ k) :
    ((Finset.univ : Finset (Fin k)).image (stdSeq k)).sup id ≤ k ^ 3 := by
  have hcnt := count_le_count_cube k hk
  apply Finset.sup_le
  intro h hh
  simp only [id_eq]
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
  rw [← Nat.lt_succ_iff]
  refine (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mp ?_
  change firstIdxAboveK k + (i : ℕ) < Nat.count Nat.Prime (k ^ 3 + 1)
  unfold firstIdxAboveK
  have := i.isLt
  omega

/-! ## The tuple as a choice -/

/-- **The tuple choice.** An injective `k`-tuple for every `k`, whose entry set is admissible and,
for `k ≥ 20`, lies under `k³` (the floor `D₀ k = k³` rests on it). -/
class TupleChoice where
  /-- The `k`-tuple. -/
  tup : (k : ℕ) → Fin k → ℕ
  inj : ∀ k, Function.Injective (tup k)
  admissible : ∀ k, Admissible ((Finset.univ : Finset (Fin k)).image (tup k))
  sup_cube : ∀ k, 20 ≤ k → ((Finset.univ : Finset (Fin k)).image (tup k)).sup id ≤ k ^ 3

/-- The default choice: the first `k` primes strictly greater than `k`. -/
noncomputable instance (priority := low) stdTuple : TupleChoice :=
  ⟨stdSeq, stdSeq_injective, std_admissible, std_sup_le_cube⟩

section Tuple

variable [TupleChoice]

/-- The `i`-th element of the chosen `k`-tuple, as a function `Fin k → ℕ`. -/
noncomputable def hSeq (k : ℕ) (i : Fin k) : ℕ := TupleChoice.tup k i

/-- The chosen `k`-tuple as a set. -/
noncomputable def H (k : ℕ) : Finset ℕ := (Finset.univ : Finset (Fin k)).image (hSeq k)

/-- The chosen tuple's `inj` field, stated for `hSeq k`: `hSeq k` is injective. The downstream
chain reads the tuple only through this and the lemmas below. -/
theorem hSeq_injective (k : ℕ) : Function.Injective (hSeq k) := TupleChoice.inj k

/-- `#(H k) = k`: the image of `univ : Finset (Fin k)` under the injective `hSeq k`
(`Finset.card_image_of_injective`, `Fintype.card_fin`). -/
theorem H_card (k : ℕ) : (H k).card = k := by
  unfold H
  rw [Finset.card_image_of_injective _ (hSeq_injective k), Finset.card_univ, Fintype.card_fin]

/-- `hSeq k i ∈ H k` for every `i`: `H k` is the image of `univ` (`Finset.mem_image_of_mem`);
the membership behind `hSeq_le_D₀` and `hSeq_lt_of_sup_lt`. -/
theorem hSeq_mem_H (k : ℕ) (i : Fin k) : hSeq k i ∈ H k :=
  Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-! ## N1.3 — `H k` is admissible -/

/-- `H k` is admissible — the chosen tuple's `admissible` field; the one property of the tuple
that `exists_nu0W`'s CRT construction spends (a missed class at every prime). -/
theorem H_admissible (k : ℕ) : Admissible (H k) := TupleChoice.admissible k

/-- `(H k).sup id ≤ k³` for `k ≥ 20`. -/
theorem H_sup_le_cube (k : ℕ) (hk : 20 ≤ k) : (H k).sup id ≤ k ^ 3 := TupleChoice.sup_cube k hk

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

/-- **N1.4, free-modulus form (`(D,W')` sweep).** For ANY nonzero modulus `W'`
there is a residue `ν₀` with `ν₀ + h` coprime to `W'` for every `h ∈ H k`.
Identical CRT construction to `exists_nu0`; the modulus is a free parameter,
so the explicit-gaps track can instantiate at `W' = primorial D`. -/
theorem exists_nu0W (k W' : ℕ) (hW' : W' ≠ 0) :
    ∃ ν₀ : ℕ, ∀ h ∈ H k, Nat.Coprime (ν₀ + h) W' := by
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
  suffices hgen : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      ∃ ν₀ : ℕ, ∀ h ∈ H k, ∀ p ∈ s, ¬ p ∣ (ν₀ + h) by
    obtain ⟨ν₀, hν₀⟩ := hgen W'.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    refine ⟨ν₀, fun h hh => ?_⟩
    apply Nat.coprime_of_dvd
    intro p hpp hpdvd hpdvdW
    exact hν₀ h hh p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvdW, hW'⟩) hpdvd
  intro s
  induction s using Finset.induction with
  | empty => exact fun _ => ⟨0, fun _ _ p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert p s hps ih =>
    intro hprimes
    have hpp : p.Prime := hprimes p (Finset.mem_insert_self p s)
    have hsprimes : ∀ q ∈ s, q.Prime := fun q hq => hprimes q (Finset.mem_insert_of_mem hq)
    obtain ⟨ν₁, hν₁⟩ := ih hsprimes
    obtain ⟨r, hr⟩ := hex p hpp
    set M := ∏ q ∈ s, q with hM
    have hMcop : p.Coprime M := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpp (hsprimes q hq)).mpr (by rintro rfl; exact hps hq)
    obtain ⟨ν₀, hν₀p, hν₀M⟩ := Nat.chineseRemainder hMcop r ν₁
    refine ⟨ν₀, fun h hh q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with hqp | hqs
    · intro hdvd
      rw [hqp] at hdvd
      have h1 : ν₀ + h ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdvd
      have h2 : ν₀ + h ≡ r + h [MOD p] := hν₀p.add_right h
      exact hr h hh (Nat.modEq_zero_iff_dvd.mp (h2.symm.trans h1))
    · intro hdvd
      have hqM : q ∣ M := Finset.dvd_prod_of_mem _ hqs
      have h1 : ν₀ + h ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hdvd
      have h2 : ν₀ + h ≡ ν₁ + h [MOD q] := (hν₀M.of_dvd hqM).add_right h
      exact hν₁ h hh q hqs (Nat.modEq_zero_iff_dvd.mp (h2.symm.trans h1))

/-- **N1.4.** There is a residue `ν₀ mod W k` such that `ν₀ + h` is
coprime to `W k` for every `h ∈ H k`. Specialization of `exists_nu0W` at
the concrete Maynard modulus `W k`. -/
theorem exists_nu0 (k : ℕ) :
    ∃ ν₀ : ℕ, ∀ h ∈ H k, Nat.Coprime (ν₀ + h) (W k) :=
  exists_nu0W k (W k) (W_squarefree k).ne_zero


/-- `hSeq k i ≤ D₀ k`: `hSeq k i ≤ (H k).sup id` by membership (`hSeq_mem_H`, `Finset.le_sup`)
and `(H k).sup id ≤ max (k ^ 3) ((H k).sup id) = D₀ k` (`le_max_right`). Every tuple entry lies
under the W-trick's threshold. -/
theorem hSeq_le_D₀ (k : ℕ) (i : Fin k) : hSeq k i ≤ D₀ k :=
  le_trans (Finset.le_sup (f := id) (hSeq_mem_H k i)) (le_max_right _ _)

/-- **`hSeq_le_D₀`-analog for a free cutoff `D`.** If the tuple's sup is
strictly below `D` (e.g. `(H 5).sup id = 19 < D`), every tuple entry is
`< D`. This is the strict-`<` bound the `(D,W')` collision/coprimality
tails consume (mirrors how `hSeq_le_D₀` bounds `hSeq k i` by `D₀ k`). -/
theorem hSeq_lt_of_sup_lt (k : ℕ) {D : ℕ} (hD : (H k).sup id < D) (i : Fin k) :
    hSeq k i < D :=
  lt_of_le_of_lt (Finset.le_sup (f := id) (hSeq_mem_H k i)) hD

end Tuple

/-! ## The standard tuple's own facts (at `stdTuple`) -/

/-- At the default instance `stdTuple`, `hSeq k i = Nat.nth Nat.Prime (firstIdxAboveK k + i)` by
`rfl` — the `i`-th prime strictly above `k`. -/
theorem hSeq_std (k : ℕ) (i : Fin k) :
    @hSeq stdTuple k i = Nat.nth Nat.Prime (firstIdxAboveK k + (i : ℕ)) := rfl

/-- At `stdTuple` every tuple entry is prime (`stdSeq_prime`). -/
theorem hSeq_prime (k : ℕ) (i : Fin k) : (@hSeq stdTuple k i).Prime := stdSeq_prime k i

/-- At `stdTuple` every tuple entry exceeds `k` (`stdSeq_gt_k`). -/
theorem hSeq_gt_k (k : ℕ) (i : Fin k) : k < @hSeq stdTuple k i := stdSeq_gt_k k i

/-- At `stdTuple` every element of `H k` is prime: it is `stdSeq k i` for some `i`
(`Finset.mem_image`), prime by `stdSeq_prime`. -/
theorem H_prime (k : ℕ) {h : ℕ} (hh : h ∈ @H stdTuple k) : h.Prime := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
  exact stdSeq_prime k i

/-- At `stdTuple` every element of `H k` exceeds `k`: it is `stdSeq k i` for some `i`
(`Finset.mem_image`), and `stdSeq_gt_k`. -/
theorem H_gt_k (k : ℕ) {h : ℕ} (hh : h ∈ @H stdTuple k) : k < h := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
  exact stdSeq_gt_k k i

end Salt.Maynard
