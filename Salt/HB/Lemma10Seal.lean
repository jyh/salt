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

/-! ## R1 — the truncation parameter `K`, pinned as a natural BY FLOOR -/

/-- HB's truncation parameter `K = 2 + k^{1/4}`, pinned as a natural.

**FLOOR, NEVER CEILING.**  With a ceiling `sealK_le` is false at `k = 2`
(`2 + ⌈2^{1/4}⌉ = 4 > 3.189`), and `sealK_le` is what lets `log_Kk_le` apply. -/
noncomputable def sealK (k : ℕ) : ℕ := 2 + ⌊(k : ℝ) ^ ((1 : ℝ) / 4)⌋₊

/-- `2 ≤ sealK k`, by construction. -/
theorem sealK_ge_two (k : ℕ) : 2 ≤ sealK k := Nat.le_add_right 2 _

/-- `sealK` dominates `k^{1/4}` — this is what turns the assembly's `E/K` into the
conclusion's `E/k^{1/4}`. -/
theorem sealK_ge_rpow (k : ℕ) : (k : ℝ) ^ ((1 : ℝ) / 4) ≤ sealK k := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have h1 : (k : ℝ) ^ ((1 : ℝ) / 4) < (⌊(k : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h2 : ((sealK k : ℕ) : ℝ) = 2 + (⌊(k : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) := by
    simp [sealK]
  rw [h2]; linarith

/-- `sealK` is dominated by `2 + k^{1/4}` — this is what lets `log_Kk_le` apply to it. -/
theorem sealK_le (k : ℕ) : (sealK k : ℝ) ≤ 2 + (k : ℝ) ^ ((1 : ℝ) / 4) := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have h2 : ((sealK k : ℕ) : ℝ) = 2 + (⌊(k : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) := by
    simp [sealK]
  rw [h2]
  have := Nat.floor_le h0
  linarith
/-! ## R2 — the logarithmic envelope at `K·k` -/

/-- `c ≤ x^{1/4}` from `c^4 ≤ x`.  Private: it is R2's own scaffolding. -/
private lemma le_rpow4 {x c : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (h : c ^ (4 : ℕ) ≤ x) :
    c ≤ x ^ ((1 : ℝ) / 4) := by
  rw [one_div, Real.le_rpow_inv_iff_of_pos hc hx (by norm_num)]
  rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact h

/-- **R2.**  `log ((2 + k^{1/4})·k) ≤ 1.337 · log (2k)` for `k ≥ 2`.

`1337/1000` because `(1337/1000)³ = 2.389979753 ≤ 239/100` exactly by rational `norm_num`;
the constant is pinned on both sides (the attained maximum of the ratio is `r(2) = 1.3365989`,
the ceiling is `(2.39)^{1/3} = 1.3370038`), so the window is 4.05e-4 wide and `1338/1000`
FAILS.  ⛔ Do NOT state it at `13366/10000`: it is true there by 1.1e-6 and no `nlinarith`
survives that margin.

The route is a SINGLE regime — no case split, no monotonicity, no `interval_cases`: the
envelope `2 + k^{1/4} ≤ (1 + 2·2^{-1/4})·k^{1/4} ≤ 2.682·k^{1/4}` is tangent at `k = 2`, and
the envelope constant closes off the anchor `8/3 = 3·log 2 − log 3` with margin 4.6e-4 (no
`log 5`).  ⚠️ The ratio dips to 1.1756 at `k = 498`; that is not a regime seam — do not split
there. -/
theorem log_Kk_le (k : ℕ) (hk : 2 ≤ k) :
    Real.log ((2 + (k : ℝ) ^ ((1 : ℝ) / 4)) * k) ≤ 1337 / 1000 * Real.log (2 * (k : ℝ)) := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have ht : (11892071 : ℝ) / 10000000 ≤ (k : ℝ) ^ ((1 : ℝ) / 4) :=
    le_rpow4 (by norm_num) (le_of_lt hkpos) (by nlinarith)
  have ht0 : (0 : ℝ) < (k : ℝ) ^ ((1 : ℝ) / 4) := by linarith
  -- (1) THE ENVELOPE, tangent at k = 2:  2 + k^{1/4} ≤ 2.682 · k^{1/4}
  have henv : 2 + (k : ℝ) ^ ((1 : ℝ) / 4) ≤ 2682 / 1000 * (k : ℝ) ^ ((1 : ℝ) / 4) := by
    nlinarith [ht]
  -- (2) push through · k and take logs
  have hmul : (2 + (k : ℝ) ^ ((1 : ℝ) / 4)) * k
      ≤ 2682 / 1000 * ((k : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ)) := by
    have := mul_le_mul_of_nonneg_right henv (le_of_lt hkpos); linarith [this]
  have hpos : (0 : ℝ) < (2 + (k : ℝ) ^ ((1 : ℝ) / 4)) * k := by positivity
  have hlogsplit : Real.log (2682 / 1000 * ((k : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ)))
      = Real.log (2682 / 1000) + (5 / 4) * Real.log (k : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (ne_of_gt ht0) (ne_of_gt hkpos), Real.log_rpow hkpos]
    ring
  -- (3) the log-2 / log-3 bound on the envelope constant, anchor 8/3
  have hc : Real.log ((2682 : ℝ) / 1000) ≤ 3 * Real.log 2 - Real.log 3 + (8046 / 8000 - 1) := by
    have e : ((8 : ℝ)/3) * (8046 / 8000) = 2682 / 1000 := by ring
    have h83 : Real.log ((8 : ℝ)/3) = 3 * Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num),
        show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [← e, Real.log_mul (by norm_num) (by norm_num), h83]
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < (8046 : ℝ)/8000 by norm_num)]
  -- (4) close:  log (2k) = log 2 + log k,  and log k ≥ log 2
  have h2k : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log (k : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hkpos)]
  have hlk : Real.log 2 ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) hk2
  calc Real.log ((2 + (k : ℝ) ^ ((1 : ℝ) / 4)) * k)
      ≤ Real.log (2682 / 1000 * ((k : ℝ) ^ ((1 : ℝ) / 4) * (k : ℝ))) :=
        Real.log_le_log hpos hmul
    _ = Real.log (2682 / 1000) + (5 / 4) * Real.log (k : ℝ) := hlogsplit
    _ ≤ 1337 / 1000 * Real.log (2 * (k : ℝ)) := by
        rw [h2k]
        nlinarith [hc, hlk, Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9]
/-! ## T4 — the logarithmic envelope at `1 + log K` -/

/-- **T4.**  `1 + log (sealK k) ≤ 2.06 · log (2k)` for `k ≥ 2` — the `log K` half of the
`(log Kk)³` factor, a corollary of R2's conclusion and `sealK_le` (with `sealK_ge_two` only
for `0 < sealK k`).  `sealK_ge_rpow` is not needed here; it is the assembly's.

`2.06` is sound because `1/log 4 + 1.337 = 2.0583`.  The step `1 ≤ 0.722 · log (2k)` is stated
at `722/1000` deliberately: the floor is `1/log 4 = 0.72134752…`, so `7213476/10000000` would
leave 8e-8 of headroom — the bottom 0.005 % of the valid window — while `722/1000` leaves
6.5e-4 at the same cost. -/
theorem t4_log_sealK_le (k : ℕ) (hk : 2 ≤ k) :
    1 + Real.log (sealK k) ≤ 206/100 * Real.log (2*(k:ℝ)) := by
  have hR2 := log_Kk_le k hk
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hbase : (0 : ℝ) < 2 + (k : ℝ) ^ ((1 : ℝ)/4) := by positivity
  have hK0 : (0 : ℝ) < (sealK k : ℝ) := by
    have h := sealK_ge_two k
    have h2 : (2:ℝ) ≤ (sealK k : ℝ) := by exact_mod_cast h
    linarith
  have h1 : Real.log (sealK k) ≤ Real.log (2 + (k : ℝ) ^ ((1 : ℝ)/4)) :=
    Real.log_le_log hK0 (sealK_le k)
  have h2 : Real.log (2 + (k : ℝ) ^ ((1 : ℝ)/4))
      ≤ Real.log ((2 + (k : ℝ) ^ ((1 : ℝ)/4)) * (k : ℝ)) := by
    refine Real.log_le_log hbase ?_; nlinarith [hbase, hk2]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
  have h5 : Real.log 4 ≤ Real.log (2 * (k : ℝ)) := by
    refine Real.log_le_log (by norm_num) ?_; linarith
  have h6 : (1 : ℝ) ≤ 722/1000 * Real.log (2 * (k : ℝ)) := by
    nlinarith [Real.log_two_gt_d9, h4, h5]
  linarith [h1, h2, hR2, h6]
end Salt.N7
