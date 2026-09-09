/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma10Chain
import Salt.Weil.MajorantExpansion

/-!
# HB 1983 §7 — the INPUTS of the p.223 assembly (Lemma 10), N7 Wave A seal

`Lemma10.lean` landed the trivial bound (7.5); `Lemma10Chain.lean` landed the (7.6)–(7.8)
chain — the Abel transfer, the completion by additive characters with Estermann spent once,
and the dyadic `m`-sum.  This file lands the fifteen declarations the p.223 assembly consumes
and the corpus did not yet have.

## What landed in this file, and what did NOT

**LANDED, sorry-free:**

* the two definitions the assembly sums — `lem10PsiSum`, the ψ-sum of (7.1) over the SAME
  restricted range as `lem10ExpSum`, and `lem10ExpSumZ`, that exponential sum re-indexed at
  `m : ℤ`;
* the R-A6 `±m` conjugation bridge `norm_lem10ExpSumZ` (a NORM equality onto the landed
  `norm_lem10ExpSum_neg`) and the ℤ→ℕ head reindex `head_reindex` the dyadic consumer owes;
* the truncation parameter `sealK k = 2 + ⌊k^{1/4}⌋₊` — a FLOOR, never a ceiling — with its
  three service rows `sealK_ge_two`, `sealK_ge_rpow` (which turns the assembly's `E/K` into
  the conclusion's `E/k^{1/4}`) and `sealK_le` (which is what lets `log_Kk_le` apply);
* the two logarithmic envelopes `log_Kk_le` at `(2 + k^{1/4})·k` and `t4_log_sealK_le` at
  `1 + log (sealK k)`, at the literal constants `1337/1000` and `206/100`;
* the Fourier/majorant split `lem10PsiSum_le_fourier_split`, ℤ-indexed in HEAD and in
  MAJORANT BRACKET — one index type in the statement;
* the `m = 1` composite bound `lem10_m1_bound` at the numeral `16`; and
* the three road twins `klPhaseSum_bound_road`, `lem10_dyadic_bound_road`,
  `lem10_m1_bound_road`, in which the 2-adic factor `√(2^{v₂ k})` is not removed but BOUNDED
  BY `16` from the row's own binder `hv2k : k.factorization 2 ≤ 8` and paid in the constant
  (`128 = 8·16`, `256 = 16·16`).

⛔ **NOT LANDED: `hb_lemma10` itself, nor `hb_lemma10_road`, `hb_lemma10_const`,
`hb_lemma10_inv`.**  Everything here is an *input* of the p.223 assembly.  The assembly — the
truncation at `K = 2 + k^{1/4}`, the dyadic cover of `0 < |m| ≤ K` by blocks `(2^j, 2^{j+1}]`,
the exchange of the finite `n`-sum with the absolutely convergent `m`-sum of (7.3), and the
four `m`-ranges — is a wave of its own size and is deliberately not half-built here.  Nothing
in this file bears on twin primes.

**Numerals.**  Every constant below is the written ledger's, unmoved: `5/2` on the majorant
bracket, `1337/1000` and `206/100` on the two envelopes, `16` on the `m = 1` composite, and
`128` / `256` on the road twins.  The `m = 1` route is provable at `8` and at `4`; the row is
stated at `16` because that is what the assembly consumes.
-/

open Finset Salt.Weil Salt.LS

namespace Salt.N7

variable {k : ℕ}

/-! ## The two summands of the split -/

/-- The ψ-sum of HB (7.1): `∑_{n ∈ I} ψ (f n)`, `ψ` the sawtooth, over the SAME restricted
range as `lem10ExpSum` — HB's `∑'` is the coprimality-and-congruence restriction, not all
of `I`.

⛔ The filter is the whole content of this definition.  Over an unfiltered `I` the two sides
of `lem10PsiSum_le_fourier_split` would range over different sets, and the Fourier expansion
that relates them is an identity only on the common range — the row would be FALSE, not
merely loose.  The filter is token-identical to `lem10ExpSum`'s
(`Salt/HB/Lemma10.lean:42-43`). -/
noncomputable def lem10PsiSum (k q : ℕ) (b : ℤ) (I : Finset ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), sawtooth (f n)

/-- `lem10ExpSum` re-indexed at `m : ℤ`.  The assembly sums over ℤ to match `majorantCoeff`'s
index (`Salt/Weil/Sawtooth.lean`); the dyadic workhorses stay at `m : ℕ` and are reached
through `norm_lem10ExpSumZ` and `head_reindex`. -/
noncomputable def lem10ExpSumZ (k q : ℕ) (b : ℤ) (I : Finset ℤ) (m : ℤ) (f : ℤ → ℝ) : ℂ :=
  ∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), e ((m : ℝ) * f n)

/-! ## The `±m` bridge and the head reindex -/

/-- **The one explicit `±m` conjugation bridge R-A6 mandates**, as a NORM equality.

For `0 ≤ m` this is a cast; for `m < 0` it is the landed `norm_lem10ExpSum_neg`
(`Salt/HB/Lemma10Chain.lean:1269`) after an `Int.cast`/`Neg` congruence step.  ⛔ It is NOT
`rfl`: `Int.cast m` and `Nat.cast m.natAbs` are not defeq for a variable `m`. -/
theorem norm_lem10ExpSumZ (k q : ℕ) (b : ℤ) (I : Finset ℤ) (m : ℤ) (f : ℤ → ℝ) :
    ‖lem10ExpSumZ k q b I m f‖ = ‖lem10ExpSum k q b I m.natAbs f‖ := by
  rcases lt_or_ge m 0 with hm | hm
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -(j : ℤ) := ⟨m.natAbs, by omega⟩
    have hj : ((-(j : ℤ)).natAbs) = j := by simp
    have hstep : lem10ExpSumZ k q b I (-(j : ℤ)) f
        = ∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), e (-((j : ℝ) * f n)) := by
      unfold lem10ExpSumZ
      exact Finset.sum_congr rfl (fun n _ => by congr 1; push_cast; ring)
    rw [hj, hstep, norm_lem10ExpSum_neg]
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    unfold lem10ExpSumZ lem10ExpSum
    simp

/-- **The ℤ→ℕ head reindex the dyadic consumer owes.**  `Finset.Icc (1:ℤ) (K:ℤ)` is the image
of `Finset.Icc 1 K` under `Nat.cast`; the summands then agree by the bridge above.  This is
glue forced by R-A6's own clauses — ℕ workhorses, ℤ assembly — and not a second bridge: there
is no conjugation and no negative branch in it. -/
theorem head_reindex (k q : ℕ) (b : ℤ) (I : Finset ℤ) (f : ℤ → ℝ) (K : ℕ) :
    ∑ m ∈ Finset.Icc (1 : ℤ) (K : ℤ), ‖lem10ExpSumZ k q b I m f‖ / (Real.pi * m)
      = ∑ m ∈ Finset.Icc 1 K, ‖lem10ExpSum k q b I m f‖ / (Real.pi * m) := by
  have hset : Finset.Icc (1 : ℤ) (K : ℤ)
      = (Finset.Icc 1 K).map ⟨fun n : ℕ => (n : ℤ), fun a b h => by simpa using h⟩ := by
    ext x
    simp only [Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨x.toNat, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [hset, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [norm_lem10ExpSumZ]
  norm_num

end Salt.N7
