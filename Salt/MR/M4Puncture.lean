/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Band

/-!
# `M4Puncture` — ⟦WALL 1⟧'s datum side: the PER-BLOCK pair law at the door's own K-blocks

`M4Band` supplies the door datum's pair law on the Ramaré BAND `[P, Q]`, where every band
prime lies ABOVE every door block and the co-factor slot is the datum itself.  The capstone's
OTHER factorization binder — `hcoefBand`, at the door's own K-ladder blocks `[𝒫_j, 𝒬K_j]` —
is a different law, and it needs a different co-factor: a prime of block `j` **is** one of
the sieve's own block primes, so multiplying by it PUNCTURES the level-`j` condition.

## THE PUNCTURE (§1–§2)

At `p` prime with `𝒫_j ≤ p ≤ 𝒬K_j` and `¬ p ∣ m`,

  `1_𝒮(p·m) = 1_{𝒮∖j}(m)`,   `𝒮∖j := {n : 1 ≤ ω(n; 𝒫_i, 𝒬K_i) for every i ≠ j}`,

because `ω(·; 𝒫_i, 𝒬K_i)` is additive on coprimes (`RamWeight.blockOmega_mul_coprime`), the
prime `p` contributes `1` at level `j` — which discharges that level outright — and `0` at
every other level, PROVIDED the blocks are separated.  ⚠ This is the IN-BLOCK case and it is
the opposite direction from `M4Band` §1's shift-up (`memS_shift_up`, where the prime is above
every block and contributes nothing anywhere): do not use that law here.

So the capstone's level-dependent co-factor family is forced:

  `bfam j m := 1_{𝒮∖j}(m)·λχ̄(m)`   (`memSPunctCoeff`),

and it is the `b`-slot the ⟦W1⟧ generalization freed.  At `j = j` the law is `SeamCoefW`
verbatim, at the HALF-OPEN cut, with `M4Band` §4's forced endpoint binder `hend`.

## THE SEPARATION (§3)

The puncture needs the door's two K-blocks to be DISJOINT, which is one arithmetic fact:

  `𝒬K_1 = 2^{M·A} < 2^{4AG} = 𝒫_2`   whenever `M < 4G`,

and at the door's own calibration `G = 3072M` this is `M < 12288M`, i.e. nothing
(`door_block_separation`).  §4 assembles the door's own per-block pair law.

## ⚠ THE TRAPS

* `liouChi χ = liouvilleC·χ̄`, never `lamChi` (`M4Residue`'s trap);
* the cut is HALF-OPEN (`M4DoorRow.winCutH`), so the endpoint binder is carried, not assumed
  away — `M4Band.memSCoeff_endpoint_zero_of_seamCoefW` shows it is forced;
* the strict gates `p.Prime`, `¬ p ∣ m`, `m ≠ 0` are carried, never weakened.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — THE PUNCTURED SIEVE CONDITION -/

/-- **THE PUNCTURED BLOCK CONDITION** `𝒮∖j`: every level's block condition EXCEPT level `j`'s.
This is the co-factor's own membership set once a block-`j` prime has been split off. -/
def MemSPunct (Pseq Qseq : ℕ → ℕ) (J j n : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 J, i ≠ j → 1 ≤ blockOmega (Pseq i) (Qseq i) n

instance decidableMemSPunct (Pseq Qseq : ℕ → ℕ) (J j n : ℕ) :
    Decidable (MemSPunct Pseq Qseq J j n) := by
  unfold MemSPunct; infer_instance

/-- `𝒮` implies `𝒮∖j`: the puncture only deletes a demand. -/
theorem memSPunct_of_memS {Pseq Qseq : ℕ → ℕ} {J j n : ℕ} (h : MemS Pseq Qseq J n) :
    MemSPunct Pseq Qseq J j n :=
  fun i hi _ => h i hi

/-- **THE PUNCTURED COEFFICIENT** `1_{𝒮∖j}·a` — the capstone's level-dependent `b`-slot. -/
def memSPunctCoeff (Pseq Qseq : ℕ → ℕ) (J j : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun m => if MemSPunct Pseq Qseq J j m then a m else 0

theorem norm_memSPunctCoeff_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (Pseq Qseq : ℕ → ℕ)
    (J j m : ℕ) : ‖memSPunctCoeff Pseq Qseq J j a m‖ ≤ 1 := by
  simp only [memSPunctCoeff]
  split_ifs
  · exact ha m
  · simp

/-! ## §2 — THE IN-BLOCK MULTIPLICATION LAW -/

/-- A prime INSIDE the block has exactly one block prime divisor — itself. -/
theorem blockOmega_prime_in {P Q p : ℕ} (hp : p.Prime) (hlo : P ≤ p) (hhi : p ≤ Q) :
    blockOmega P Q p = 1 := by
  have hset : BlockPrimeDivs P Q p = {p} := by
    rw [BlockPrimeDivs, hp.primeFactors]
    exact Finset.filter_true_of_mem (by
      intro r hr
      rw [Finset.mem_singleton] at hr
      exact hr ▸ ⟨hlo, hhi⟩)
  rw [blockOmega, hset, Finset.card_singleton]

/-- A prime OUTSIDE the block has none. -/
theorem blockOmega_prime_out {P Q p : ℕ} (hp : p.Prime) (hout : ¬ (P ≤ p ∧ p ≤ Q)) :
    blockOmega P Q p = 0 := by
  have hset : BlockPrimeDivs P Q p = ∅ := by
    rw [BlockPrimeDivs, hp.primeFactors, Finset.filter_eq_empty_iff]
    intro r hr
    rw [Finset.mem_singleton] at hr
    exact hr ▸ hout
  rw [blockOmega, hset, Finset.card_empty]

/-- **THE PUNCTURE** (`memS_mul_prime_punct`).  At a prime of block `j` coprime to `m`, the
sieve condition on `p·m` is exactly the PUNCTURED condition on `m`: level `j` is discharged
by `p` itself, and no other level sees `p` — that is what `hsep` says. -/
theorem memS_mul_prime_punct {Pseq Qseq : ℕ → ℕ} {J j p m : ℕ}
    (hj : j ∈ Finset.Icc 1 J) (hp : p.Prime) (hlo : Pseq j ≤ p) (hhi : p ≤ Qseq j)
    (hpm : ¬ p ∣ m)
    (hsep : ∀ i ∈ Finset.Icc 1 J, i ≠ j → ¬ (Pseq i ≤ p ∧ p ≤ Qseq i)) :
    MemS Pseq Qseq J (p * m) ↔ MemSPunct Pseq Qseq J j m := by
  have hco : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  constructor
  · intro h i hi hij
    have hsum := h i hi
    rw [blockOmega_mul_coprime hco, blockOmega_prime_out hp (hsep i hi hij)] at hsum
    omega
  · intro h i hi
    rw [blockOmega_mul_coprime hco]
    by_cases hij : i = j
    · subst hij
      rw [blockOmega_prime_in hp hlo hhi]
      omega
    · rw [blockOmega_prime_out hp (hsep i hi hij)]
      have := h i hi hij
      omega

/-- **THE POINTWISE PAIR LAW, IN-BLOCK**: `1_𝒮(p·m)·g(p·m) = 1_{𝒮∖j}(m)·g(m)·g(p)` at a prime
of block `j`, for any completely multiplicative `g`.  The in-block sibling of
`M4Band.indicator_mul_shift_up`. -/
theorem indicator_mul_punct {g : ℕ → ℂ} (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {Pseq Qseq : ℕ → ℕ} {J j p m : ℕ} (hj : j ∈ Finset.Icc 1 J) (hp : p.Prime)
    (hlo : Pseq j ≤ p) (hhi : p ≤ Qseq j) (hpm : ¬ p ∣ m)
    (hsep : ∀ i ∈ Finset.Icc 1 J, i ≠ j → ¬ (Pseq i ≤ p ∧ p ≤ Qseq i)) :
    (if MemS Pseq Qseq J (p * m) then g (p * m) else 0)
      = (if MemSPunct Pseq Qseq J j m then g m else 0) * g p := by
  have hiff := memS_mul_prime_punct hj hp hlo hhi hpm hsep
  by_cases hS : MemSPunct Pseq Qseq J j m
  · rw [if_pos (hiff.mpr hS), if_pos hS, hg]; ring
  · rw [if_neg (fun hc => hS (hiff.mp hc)), if_neg hS, zero_mul]

/-! ## §3 — THE BLOCK SEPARATION, AS ARITHMETIC

The puncture's one new demand.  `𝒬K_1 = 2^{M·e₁}` and `𝒫_2 = 2^{e₂}` with `e₁ = A`,
`e₂ = 4AG`, so the two door blocks are disjoint as soon as `M < 4G` — and the door's own
calibration is `G = 3072M`. -/

/-- `e₂ = 4AG` (the ladder's second exponent, evaluated). -/
theorem calE_two (A G : ℕ) : calE A G 2 = 4 * (A * G) := by
  simp only [calE, Nat.factorial]
  ring

/-- **THE BLOCK SEPARATION** (`calQK_one_lt_calP_two`).  Level 1's TOP is strictly below level
2's BOTTOM whenever `M < 4G` — an inequality between exponents of `2`, nothing analytic. -/
theorem calQK_one_lt_calP_two {A G M : ℕ} (hA : 1 ≤ A) (hM : M < 4 * G) :
    calQK A G M 1 < calP A G 2 := by
  have hexp : (1 ^ 2 * M) * calE A G 1 < calE A G 2 := by
    rw [calE_one, calE_two]
    have : M * A < 4 * G * A := Nat.mul_lt_mul_of_lt_of_le hM le_rfl hA
    simpa [one_pow, one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  simpa only [calQK, calP] using Nat.pow_lt_pow_right (by norm_num) hexp

/-- **THE DOOR'S BLOCK SEPARATION** (`door_block_separation`).  At the door's calibration
`G = 3072M` the gate `M < 4G` reads `M < 12288M`, free at `1 ≤ M`. -/
theorem door_block_separation {M : ℕ} (hM : 1 ≤ M) :
    calQK (Adoor M) (3072 * M) M 1 < calP (Adoor M) (3072 * M) 2 :=
  calQK_one_lt_calP_two (one_le_Adoor M) (by omega)

/-- **THE DOOR'S TWO BLOCKS ARE SEPARATED, POINTWISE** (`door_block_sep_at`).  The `hsep`
binder of §2 discharged at the door's own two-level ladder, at every prime of block `j`. -/
theorem door_block_sep_at {M j p : ℕ} (hM : 1 ≤ M) (hj : j ∈ Finset.Icc 1 2)
    (hlo : calP (Adoor M) (3072 * M) j ≤ p) (hhi : p ≤ calQK (Adoor M) (3072 * M) M j) :
    ∀ i ∈ Finset.Icc 1 2, i ≠ j →
      ¬ (calP (Adoor M) (3072 * M) i ≤ p ∧ p ≤ calQK (Adoor M) (3072 * M) M i) := by
  have hsplit := door_block_separation hM
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  intro i hi hij
  rw [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  rintro ⟨hilo, hihi⟩
  -- `j` and `i` are the two distinct levels of `{1, 2}`
  interval_cases j <;> interval_cases i <;> omega

/-! ## §4 — THE DOOR'S PER-BLOCK PAIR LAW -/

/-- **THE PER-BLOCK PAIR LAW AT AN ABSTRACT CUT** (`memSCoeff_seamCoefW_punct_gen`).  The
in-block sibling of `M4Band.memSCoeff_seamCoefW_band_gen`: the sieved datum, cut anywhere that
agrees with it on the CLOSED dyadic window, factorizes at every prime of block `j` against the
PUNCTURED co-factor. -/
theorem memSCoeff_seamCoefW_punct_gen {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J j Xd : ℕ) (a : ℕ → ℂ) (hj : j ∈ Finset.Icc 1 J)
    (hsep : ∀ p : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
      ∀ i ∈ Finset.Icc 1 J, i ≠ j → ¬ (Pseq i ≤ p ∧ p ≤ Qseq i))
    (ha : ∀ n : ℕ, Xd ≤ n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J (liouChi χ) n) :
    SeamCoefW Xd (Pseq j) (Qseq j) a
      (memSPunctCoeff Pseq Qseq J j (liouChi χ)) (liouChi χ) := by
  intro p m hp hPp hpQ hpm hlo hhi
  have hloN : Xd ≤ p * m := by
    have : ((Xd : ℕ) : ℝ) ≤ ((p * m : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hhiN : p * m ≤ 2 * Xd := by
    have : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  rw [ha _ hloN hhiN]
  rcases Nat.eq_zero_or_pos m with rfl | _
  · -- ⟦`m = 0`⟧ both sides vanish: `λχ̄(0) = 0`, so both cut data do too
    have hl0 : memSCoeff Pseq Qseq J (liouChi χ) 0 = 0 := by
      unfold memSCoeff
      split_ifs
      · unfold liouChi; simp
      · rfl
    have hp0 : memSPunctCoeff Pseq Qseq J j (liouChi χ) 0 = 0 := by
      unfold memSPunctCoeff
      split_ifs
      · unfold liouChi; simp
      · rfl
    rw [mul_zero, hl0, hp0, zero_mul]
  · exact indicator_mul_punct (liouChi_mul χ) hj hp hPp hpQ hpm (hsep p hp hPp hpQ)

/-- **THE HALF-OPEN PER-BLOCK PAIR LAW** (`memSCoeff_seamCoefW_punct_H`) — §4's law at a cut
that agrees with the sieved datum only STRICTLY above the block bottom and vanishes AT it,
which is the shape `M4DoorRow`'s `hsupp0`/`hasupp` straddle forces.  The one extra binder
`hend` is `M4Band` §4's endpoint discharge, and it is forced there
(`M4Band.memSCoeff_endpoint_zero_of_seamCoefW`). -/
theorem memSCoeff_seamCoefW_punct_H {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J j Xd : ℕ) (a : ℕ → ℂ) (hj : j ∈ Finset.Icc 1 J)
    (hsep : ∀ p : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
      ∀ i ∈ Finset.Icc 1 J, i ≠ j → ¬ (Pseq i ≤ p ∧ p ≤ Qseq i))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J (liouChi χ) n)
    (ha0 : a Xd = 0) (hend : memSCoeff Pseq Qseq J (liouChi χ) Xd = 0) :
    SeamCoefW Xd (Pseq j) (Qseq j) a
      (memSPunctCoeff Pseq Qseq J j (liouChi χ)) (liouChi χ) :=
  memSCoeff_seamCoefW_punct_gen χ Pseq Qseq J j Xd a hj hsep (fun n hlo hhi => by
    rcases eq_or_lt_of_le hlo with rfl | hlt
    · rw [ha0, hend]
    · exact haH n hlt hhi)

/-- **`hcoefBand` AT THE DOOR, HALF-OPEN** (`doorChiCoeff_seamCoefW_punct_H`) — the whole
level family at once, in exactly the shape `M4MeanSq.m4_meansq_per_chi_gen`'s band binder
reads it: `∀ j ∈ [1,2], SeamCoefW X_d 𝒫_j 𝒬K_j a (bfam j) λχ̄`, with

  `bfam j := 1_{𝒮∖j}·λχ̄`   (`memSPunctCoeff … 2 j (liouChi χ)`).

The separation is `door_block_sep_at`, the endpoint `M4Band` §4's `hend`. -/
theorem doorChiCoeff_seamCoefW_punct_H {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd : ℕ}
    {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff χ M Xd = 0) :
    ∀ j ∈ Finset.Icc 1 2,
      SeamCoefW Xd (calP (Adoor M) (3072 * M) j) (calQK (Adoor M) (3072 * M) M j) a
        (memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 j
          (liouChi χ)) (liouChi χ) := by
  intro j hj
  exact memSCoeff_seamCoefW_punct_H χ (calP (Adoor M) (3072 * M))
    (calQK (Adoor M) (3072 * M) M) 2 j Xd a hj
    (fun p hp hlo hhi => door_block_sep_at hM hj hlo hhi) haH ha0 hend

/-! ### ⟦THE ENDPOINT WALL DISSOLVED⟧ — the STRICT per-block siblings

`M4Band`'s strict siblings, at the punctured co-factor: `SeamRowWindowed.SeamCoefWS` asks for
the factorization only STRICTLY above the block bottom, so `haH` alone suffices and both
`ha0` and `hend` drop.  The `m = 0` case is absurd (`X_d < p·0 = 0 ≤ X_d`) and is split off
BEFORE the agreement law is applied. -/

/-- **THE STRICT PER-BLOCK PAIR LAW AT AN ABSTRACT CUT** (`memSCoeff_seamCoefWS_punct_gen`). -/
theorem memSCoeff_seamCoefWS_punct_gen {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J j Xd : ℕ) (a : ℕ → ℂ) (hj : j ∈ Finset.Icc 1 J)
    (hsep : ∀ p : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
      ∀ i ∈ Finset.Icc 1 J, i ≠ j → ¬ (Pseq i ≤ p ∧ p ≤ Qseq i))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J (liouChi χ) n) :
    SeamCoefWS Xd (Pseq j) (Qseq j) a
      (memSPunctCoeff Pseq Qseq J j (liouChi χ)) (liouChi χ) := by
  intro p m hp hPp hpQ hpm hlo hhi
  rcases Nat.eq_zero_or_pos m with rfl | _
  · exfalso
    have h0 : (0 : ℝ) ≤ (Xd : ℝ) := Nat.cast_nonneg Xd
    rw [Nat.cast_zero, mul_zero] at hlo
    linarith
  · have hloN : Xd < p * m := by
      have h : ((Xd : ℕ) : ℝ) < ((p * m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    have hhiN : p * m ≤ 2 * Xd := by
      have h : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    rw [haH _ hloN hhiN]
    exact indicator_mul_punct (liouChi_mul χ) hj hp hPp hpQ hpm (hsep p hp hPp hpQ)

/-- **THE STRICT HALF-OPEN PER-BLOCK PAIR LAW** (`memSCoeff_seamCoefWS_punct_H`) — the name
`memSCoeff_seamCoefW_punct_H`'s consumers read, with `ha0`/`hend` gone. -/
theorem memSCoeff_seamCoefWS_punct_H {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J j Xd : ℕ) (a : ℕ → ℂ) (hj : j ∈ Finset.Icc 1 J)
    (hsep : ∀ p : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
      ∀ i ∈ Finset.Icc 1 J, i ≠ j → ¬ (Pseq i ≤ p ∧ p ≤ Qseq i))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J (liouChi χ) n) :
    SeamCoefWS Xd (Pseq j) (Qseq j) a
      (memSPunctCoeff Pseq Qseq J j (liouChi χ)) (liouChi χ) :=
  memSCoeff_seamCoefWS_punct_gen χ Pseq Qseq J j Xd a hj hsep haH

/-- **`hcoefBand` AT THE DOOR, STRICT** (`doorChiCoeff_seamCoefWS_punct_H`) — the whole level
family at once, in the shape the capstone's band binder reads it, with no endpoint
obligation. -/
theorem doorChiCoeff_seamCoefWS_punct_H {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd : ℕ}
    {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff χ M n) :
    ∀ j ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (Adoor M) (3072 * M) j) (calQK (Adoor M) (3072 * M) M j) a
        (memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 j
          (liouChi χ)) (liouChi χ) := by
  intro j hj
  exact memSCoeff_seamCoefWS_punct_H χ (calP (Adoor M) (3072 * M))
    (calQK (Adoor M) (3072 * M) M) 2 j Xd a hj
    (fun p hp hlo hhi => door_block_sep_at hM hj hlo hhi) haH

/-- The door's punctured co-factor family is `1`-bounded — the capstone's `hbf1` slot. -/
theorem norm_doorPunctCoeff_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (M j n : ℕ) :
    ‖memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 j
      (liouChi χ) n‖ ≤ 1 :=
  norm_memSPunctCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 j n

/-! ## §GK — the G-lever twin

The puncture page at `G := s13GK K M`.  Only ONE step is not a literal swap: the door's block
separation asks `M < 4G`, which at the landed base is `M < 12288M` (`by omega`) and at the
lever is that same fact pushed through `GLever.le_s13GK` — the lever only GROWS `G`, so the
separation gate survives a fortiori. -/

/-- **THE DOOR'S BLOCK SEPARATION, AT THE G-LEVER** (`door_block_separation_gk`).  `M < 4G`
at `G = s13GK K M` follows from `M < 4·(3072M)` and `3072M ≤ s13GK K M`. -/
theorem door_block_separation_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    calQK (Adoor M) (s13GK K M) M 1 < calP (Adoor M) (s13GK K M) 2 :=
  calQK_one_lt_calP_two (one_le_Adoor M)
    (lt_of_lt_of_le (show M < 4 * (3072 * M) by omega)
      (Nat.mul_le_mul_left 4 (le_s13GK K M)))

/-- **THE DOOR'S TWO BLOCKS ARE SEPARATED, POINTWISE, AT THE G-LEVER**
(`door_block_sep_at_gk`). -/
theorem door_block_sep_at_gk (K : ℕ) {M j p : ℕ} (hM : 1 ≤ M) (hj : j ∈ Finset.Icc 1 2)
    (hlo : calP (Adoor M) (s13GK K M) j ≤ p)
    (hhi : p ≤ calQK (Adoor M) (s13GK K M) M j) :
    ∀ i ∈ Finset.Icc 1 2, i ≠ j →
      ¬ (calP (Adoor M) (s13GK K M) i ≤ p ∧ p ≤ calQK (Adoor M) (s13GK K M) M i) := by
  have hsplit := door_block_separation_gk K hM
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  intro i hi hij
  rw [Finset.mem_Icc] at hi
  obtain ⟨hi1, hi2⟩ := hi
  rintro ⟨hilo, hihi⟩
  -- `j` and `i` are the two distinct levels of `{1, 2}`
  interval_cases j <;> interval_cases i <;> omega

/-- **`hcoefBand` AT THE DOOR, HALF-OPEN, AT THE G-LEVER**
(`doorChiCoeff_seamCoefW_punct_H_gk`). -/
theorem doorChiCoeff_seamCoefW_punct_H_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd : ℕ} {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_gk K χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_gk K χ M Xd = 0) :
    ∀ j ∈ Finset.Icc 1 2,
      SeamCoefW Xd (calP (Adoor M) (s13GK K M) j) (calQK (Adoor M) (s13GK K M) M j) a
        (memSPunctCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2 j
          (liouChi χ)) (liouChi χ) := by
  intro j hj
  exact memSCoeff_seamCoefW_punct_H χ (calP (Adoor M) (s13GK K M))
    (calQK (Adoor M) (s13GK K M) M) 2 j Xd a hj
    (fun p hp hlo hhi => door_block_sep_at_gk K hM hj hlo hhi) haH ha0 hend

/-- **`hcoefBand` AT THE DOOR, STRICT, AT THE G-LEVER**
(`doorChiCoeff_seamCoefWS_punct_H_gk`). -/
theorem doorChiCoeff_seamCoefWS_punct_H_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd : ℕ} {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_gk K χ M n) :
    ∀ j ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (Adoor M) (s13GK K M) j) (calQK (Adoor M) (s13GK K M) M j) a
        (memSPunctCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2 j
          (liouChi χ)) (liouChi χ) := by
  intro j hj
  exact memSCoeff_seamCoefWS_punct_H χ (calP (Adoor M) (s13GK K M))
    (calQK (Adoor M) (s13GK K M) M) 2 j Xd a hj
    (fun p hp hlo hhi => door_block_sep_at_gk K hM hj hlo hhi) haH

/-- The door's punctured co-factor family at the G-lever is `1`-bounded
(`norm_doorPunctCoeff_le_one_gk`). -/
theorem norm_doorPunctCoeff_le_one_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M j n : ℕ) :
    ‖memSPunctCoeff (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2 j
      (liouChi χ) n‖ ≤ 1 :=
  norm_memSPunctCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 j n

-- #audit (temporary)

end Salt.MR
