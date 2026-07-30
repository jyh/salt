/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Puncture
import Salt.MR.M4RowsChiZero

/-!
# ⟦S2-COEFWS⟧ — the UNTWISTED puncture pair law: `DoorRowZeroBase.coefWS`, witnessed

`M4RowsChiZero.DoorRowZeroBase` asks, as its ONE analytic field,

  `coefWS : ∀ i ∈ [1,2], SeamCoefWS X_d 𝒫_i 𝒬K_i (winCutH X_d (doorCoeffU M)) (bU i) cU`

— the STRICT relativized pair law at the **untwisted** door datum `1_𝒮·λ`.  After
`RamErrWS` discharged `E_binder` to this same field, it is the ONE witnessed-data family the
whole cap-wired terminal still carries; this file exhibits its witness.

## ⟦THE DEVICE⟧

`M4Puncture` §4′ carries the strict pair law at the **χ-twisted** datum
(`memSCoeff_seamCoefWS_punct_gen/_H`, `doorChiCoeff_seamCoefWS_punct_H`), and its engine
`M4Puncture.indicator_mul_punct` is GENERAL in the completely multiplicative factor `g`.  The
untwisted twins below are those three theorems at `g := liouvilleC` — `liouvilleC_mul` in
place of `liouChi_mul χ`, everything else verbatim — and the witness is the door family read
through `M4DoorRow.winCutH_of_mem` (the strict antecedent `X_d < p·m ≤ 2X_d` IS the half-open
cut's own support, so the agreement law fires with no endpoint obligation).

⚠ `M4Band`'s BAND pair law is the wrong device here: it is stated at primes ABOVE every
block, and its `hgate` is false at the door blocks' own windows.  The puncture law — a
block-`j` prime discharges level `j` and is invisible at every other level — is the one that
applies (see `M4Puncture`'s header).

The `b`-slot is therefore forced to be the PUNCTURED co-factor family
`bU i := memSPunctCoeff 𝒫 𝒬K 2 i liouvilleC` and the `c`-slot to be `liouvilleC` itself; both
are `1`-bounded, which is the socket's companion demand.

PURELY ADDITIVE: no landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the untwisted strict per-block pair law -/

/-- **THE UNTWISTED STRICT PER-BLOCK PAIR LAW AT AN ABSTRACT CUT**
(`memSCoeff_seamCoefWS_punct_gen_U`) — `M4Puncture.memSCoeff_seamCoefWS_punct_gen` at the
untwisted datum `1_𝒮·λ`: `indicator_mul_punct` is fired at `liouvilleC_mul` instead of
`liouChi_mul χ`, and nothing else changes. -/
theorem memSCoeff_seamCoefWS_punct_gen_U (Pseq Qseq : ℕ → ℕ) (J j Xd : ℕ) (a : ℕ → ℂ)
    (hj : j ∈ Finset.Icc 1 J)
    (hsep : ∀ p : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
      ∀ i ∈ Finset.Icc 1 J, i ≠ j → ¬ (Pseq i ≤ p ∧ p ≤ Qseq i))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J liouvilleC n) :
    SeamCoefWS Xd (Pseq j) (Qseq j) a
      (memSPunctCoeff Pseq Qseq J j liouvilleC) liouvilleC := by
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
    exact indicator_mul_punct liouvilleC_mul hj hp hPp hpQ hpm (hsep p hp hPp hpQ)

/-- **`hcoefBand` AT THE DOOR, UNTWISTED AND STRICT** (`doorCoeffU_seamCoefWS_punct_H`) — the
whole level family at once at `1_𝒮·λ`, the shape `DoorRowZeroBase.coefWS` reads.  The
separation is `M4Puncture.door_block_sep_at`; `doorCoeffU M` is `memSCoeff 𝒫 𝒬K 2 liouvilleC`
by definition. -/
theorem doorCoeffU_seamCoefWS_punct_H {M Xd : ℕ} {a : ℕ → ℂ} (hM : 1 ≤ M)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorCoeffU M n) :
    ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i) a
        (memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 i
          liouvilleC) liouvilleC := by
  intro i hi
  exact memSCoeff_seamCoefWS_punct_gen_U (calP (Adoor M) (3072 * M))
    (calQK (Adoor M) (3072 * M) M) 2 i Xd a hi
    (fun p hp hlo hhi => door_block_sep_at hM hi hlo hhi) haH

/-! ## §2 — THE WITNESS -/

/-- **⟦THE ONE WITNESSED-DATA FAMILY, WITNESSED⟧** (`doorRowZeroBase_coefWS_witness`).
`M4RowsChiZero.DoorRowZeroBase.coefWS` — equivalently `RamErrWS.DoorCapErrWS.coefWS`, the same
bytes — at

  `bU i := memSPunctCoeff 𝒫 𝒬K 2 i liouvilleC`,   `cU := liouvilleC`,

for EVERY `X_d`.  The agreement hypothesis of §1 is discharged by `M4DoorRow.winCutH_of_mem`:
the strict antecedent `X_d < p·m ≤ 2X_d` is exactly the half-open cut's own support, so no
endpoint datum is needed. -/
theorem doorRowZeroBase_coefWS_witness {M : ℕ} (Xd : ℕ) (hM : 1 ≤ M) :
    ∀ i ∈ Finset.Icc 1 2,
      SeamCoefWS Xd (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i)
        (winCutH Xd (doorCoeffU M))
        (memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 i
          liouvilleC) liouvilleC :=
  doorCoeffU_seamCoefWS_punct_H hM (fun _ h1 h2 => winCutH_of_mem _ h1 h2)

/-- The witness's `b`-slot is `1`-bounded — the socket's `∀ i m, ‖bU i m‖ ≤ 1`.  (Its
`c`-slot's bound is `M4Residue.liouvilleC_norm_le_one`, landed.) -/
theorem norm_doorPunctCoeffU_le_one (M i n : ℕ) :
    ‖memSPunctCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 i
      liouvilleC n‖ ≤ 1 :=
  norm_memSPunctCoeff_le_one liouvilleC_norm_le_one _ _ 2 i n

end Salt.MR

end
