/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma10Chain
import Salt.Weil.MajorantExpansion
import Salt.Tactic.DyadicRec

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

⛔ **NOT LANDED: `hb_lemma10_road`, `hb_lemma10_const`,
`hb_lemma10_inv`.**  Everything above is an *input* of the p.223 assembly; the assembly
itself, `hb_lemma10`, is landed at the end of this file out of those inputs.  It splits the
majorant bracket at the cut `N = 2 ^ Nat.log 2 (sealK k * ⌈√k⌉₊)` into the five `m`-ranges
`m = 0`, `m = 1`, `2 ≤ m ≤ K`, `K < m ≤ N` and `m > N`, covers the two middle ranges
dyadically by blocks `(2^j, 2^{j+1}]`, and exchanges the finite `n`-sum with the absolutely
convergent `m`-sum of (7.3).  Nothing in this file bears on twin primes.

**Numerals.**  Every constant below is the written ledger's, unmoved: `5/2` on the majorant
bracket, `1337/1000` and `206/100` on the two envelopes, `16` on the `m = 1` composite, and
`128` / `256` on the road twins.  The `m = 1` route is provable at `8` and at `4`; the row is
stated at `16` because that is what the assembly consumes.  The R10 rows below add `2/π²` and
`8K` on the head `2 ≤ m ≤ K`, `4/π²` on the range `K < m ≤ N`, `K/(π²N)` on the tail `m > N`,
`2E` on the trivial-bound slot of (7.5), and `2^13` on the assembly — each of these is the
written ledger's too, unmoved.
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
/-! ## R3′ — the Fourier/majorant split of the ψ-sum, ℤ-indexed in HEAD and BRACKET -/

/-- `‖lem10ExpSumZ‖ ≤ #I`, off the landed ℕ row through the bridge. -/
private lemma norm_lem10ExpSumZ_le_card (k q : ℕ) (b : ℤ) (I : Finset ℤ) (m : ℤ) (f : ℤ → ℝ) :
    ‖lem10ExpSumZ k q b I m f‖ ≤ (I.card : ℝ) := by
  rw [norm_lem10ExpSumZ]
  exact norm_lem10ExpSum_le_card _ _ _ _ _ _

/-- The sawtooth majorant is nonnegative. -/
private lemma majorant_nonneg (K : ℕ) (hK : 1 ≤ K) (θ : ℝ) : 0 ≤ sawtoothMajorant K θ := by
  rw [sawtoothMajorant_eq_inv_max hK]
  have h : (0:ℝ) < max ((K : ℝ) * dist₁ θ 0) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  positivity

/-- The head: the truncated Fourier sum, bounded term by term by the ℤ-indexed exponential
sums over the punctured symmetric range. -/
private lemma fourier_norm (k q : ℕ) (b : ℤ) (I : Finset ℤ) (f : ℤ → ℝ) (K : ℕ) :
    ‖∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), sawtoothFourier K (f n)‖
      ≤ ∑ m ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0,
          ‖lem10ExpSumZ k q b I m f‖ / (2 * Real.pi * |(m:ℝ)|) := by
  set T := I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b) with hT
  set E := (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0
  have hd : ∀ m : ℤ, ‖(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))‖ = 2 * Real.pi * |(m:ℝ)| := by
    intro m
    simp [Complex.norm_I, abs_of_nonneg Real.pi_nonneg]
  have hstep : ∑ n ∈ T, sawtoothFourier K (f n)
      = ∑ m ∈ E, (-(lem10ExpSumZ k q b I m f / (2 * (Real.pi:ℂ) * Complex.I * (m:ℂ)))) := by
    simp only [sawtoothFourier, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [lem10ExpSumZ, ← Finset.sum_div, Finset.sum_neg_distrib]
    rw [hT]
  rw [hstep]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun m _ => ?_)
  rw [norm_neg, norm_div, hd m]

/-- The `±m` collapse, WITH the ℤ head: the punctured symmetric range folds onto
`Finset.Icc (1:ℤ) (K:ℤ)`, the head of the frozen statement. -/
private lemma foldZ (k q : ℕ) (b : ℤ) (I : Finset ℤ) (f : ℤ → ℝ) (K : ℕ) :
    ∑ m ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0,
        ‖lem10ExpSumZ k q b I m f‖ / (2 * Real.pi * |(m:ℝ)|)
      = ∑ m ∈ Finset.Icc (1:ℤ) (K:ℤ), ‖lem10ExpSumZ k q b I m f‖ / (Real.pi * m) := by
  have hE : (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0
      = Finset.Icc (-(K:ℤ)) (-1) ∪ Finset.Icc (1:ℤ) (K:ℤ) := by
    ext m; simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc (-(K:ℤ)) (-1)) (Finset.Icc (1:ℤ) (K:ℤ)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have hneg : ∑ m ∈ Finset.Icc (-(K:ℤ)) (-1),
        ‖lem10ExpSumZ k q b I m f‖ / (2 * Real.pi * |(m:ℝ)|)
      = ∑ m ∈ Finset.Icc (1:ℤ) (K:ℤ),
        ‖lem10ExpSumZ k q b I m f‖ / (2 * Real.pi * |(m:ℝ)|) := by
    refine Finset.sum_nbij' (i := fun m : ℤ => -m) (j := fun m : ℤ => -m) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a _; ring
    · intro a _; ring
    · intro a _
      rw [norm_lem10ExpSumZ, norm_lem10ExpSumZ, Int.natAbs_neg]
      congr 2
      push_cast
      rw [abs_neg]
  rw [hE, Finset.sum_union hdisj, hneg, ← two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  simp only [Finset.mem_Icc] at hm
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : (0:ℤ) < m)
  rw [abs_of_pos hm0]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The tail: the sawtooth remainder is bounded by `5/2` times the majorant, and the majorant
sum is bounded by the ℤ-indexed majorant bracket. -/
private lemma majorant_bracket (k q : ℕ) (b : ℤ) (I : Finset ℤ) (f : ℤ → ℝ) {K : ℕ}
    (hK : 2 ≤ K) :
    ∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), sawtoothMajorant K (f n)
      ≤ ∑' m : ℤ, ‖majorantCoeff K m‖ * ‖lem10ExpSumZ k q b I m f‖ := by
  set T := I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b) with hT
  have hsummable : Summable (fun m : ℤ => ‖majorantCoeff K m‖ * ‖lem10ExpSumZ k q b I m f‖) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_norm_majorantCoeff hK).mul_right (I.card : ℝ))
    exact mul_le_mul_of_nonneg_left (norm_lem10ExpSumZ_le_card k q b I m f) (norm_nonneg _)
  have hHS : HasSum (fun m : ℤ => majorantCoeff K m * lem10ExpSumZ k q b I m f)
      (((∑ n ∈ T, sawtoothMajorant K (f n) : ℝ)) : ℂ) := by
    have h := hasSum_sum (s := T)
      (f := fun (n : ℤ) (m : ℤ) => majorantCoeff K m * e ((m : ℝ) * f n))
      (a := fun n : ℤ => ((sawtoothMajorant K (f n) : ℝ) : ℂ))
      (fun n _ => hasSum_majorantCoeff hK (f n))
    have hfun : (fun m : ℤ => ∑ n ∈ T, majorantCoeff K m * e ((m : ℝ) * f n))
        = fun m : ℤ => majorantCoeff K m * lem10ExpSumZ k q b I m f := by
      funext m; rw [lem10ExpSumZ, Finset.mul_sum, hT]
    rw [hfun] at h
    have hc : ((∑ n ∈ T, sawtoothMajorant K (f n) : ℝ) : ℂ)
        = ∑ n ∈ T, ((sawtoothMajorant K (f n) : ℝ) : ℂ) := by push_cast; rfl
    rw [hc]
    exact h
  have hnn : (0:ℝ) ≤ ∑ n ∈ T, sawtoothMajorant K (f n) :=
    Finset.sum_nonneg (fun n _ => majorant_nonneg K (le_trans (by norm_num) hK) (f n))
  calc ∑ n ∈ T, sawtoothMajorant K (f n)
      = ‖(((∑ n ∈ T, sawtoothMajorant K (f n) : ℝ)) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    _ = ‖∑' m : ℤ, majorantCoeff K m * lem10ExpSumZ k q b I m f‖ := by rw [hHS.tsum_eq]
    _ ≤ ∑' m : ℤ, ‖majorantCoeff K m * lem10ExpSumZ k q b I m f‖ := by
        refine norm_tsum_le_tsum_norm ?_
        simpa only [norm_mul] using hsummable
    _ = ∑' m : ℤ, ‖majorantCoeff K m‖ * ‖lem10ExpSumZ k q b I m f‖ := by
        simp only [norm_mul]

/-- **R3′ — the split row.**  The ψ-sum of (7.1) is bounded by the truncated Fourier head over
`Finset.Icc (1:ℤ) (K:ℤ)` plus `5/2` times the majorant bracket.

⭐ **BOTH TERMS ARE ℤ-INDEXED.**  One index type in the statement, so R-A6 clause 3 — "never
mix the index types inside a single statement" — holds literally of the assembly statement,
not merely "in the bracket".  The ℕ workhorses (`lem10_m1_bound` at `m = 1`,
`lem10_dyadic_bound` on `Finset.Ioc M (2M)`) are reached through `norm_lem10ExpSumZ` and
`head_reindex` in the CONSUMER, which is precisely what R-A6's bridge is for. -/
theorem lem10PsiSum_le_fourier_split (k q : ℕ) (b : ℤ) (I : Finset ℤ) (f : ℤ → ℝ) {K : ℕ}
    (hK : 2 ≤ K) :
    |lem10PsiSum k q b I f|
      ≤ (∑ m ∈ Finset.Icc (1 : ℤ) (K : ℤ), ‖lem10ExpSumZ k q b I m f‖ / (Real.pi * m))
        + (5 / 2) * ∑' m : ℤ, ‖majorantCoeff K m‖ * ‖lem10ExpSumZ k q b I m f‖ := by
  have hcast : ((lem10PsiSum k q b I f : ℝ) : ℂ)
      = (∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), sawtoothFourier K (f n))
        + (∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), sawtoothRem K (f n)) := by
    rw [lem10PsiSum]
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => sawtooth_fourier_expansion K (f n))
  have h1 : |lem10PsiSum k q b I f|
      ≤ ‖∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), sawtoothFourier K (f n)‖
        + ‖∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), sawtoothRem K (f n)‖ := by
    have hn : |lem10PsiSum k q b I f| = ‖((lem10PsiSum k q b I f : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hn, hcast]
    exact norm_add_le _ _
  have hF := le_trans (fourier_norm k q b I f K) (le_of_eq (foldZ k q b I f K))
  have hR : ‖∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b), sawtoothRem K (f n)‖
      ≤ (5/2) * ∑' m : ℤ, ‖majorantCoeff K m‖ * ‖lem10ExpSumZ k q b I m f‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    have hstep : ∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b),
          ‖sawtoothRem K (f n)‖
        ≤ (5/2) * ∑ n ∈ I.filter (fun n => Int.gcd n k = 1 ∧ (q : ℤ) ∣ n - b),
          sawtoothMajorant K (f n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum
        (fun n _ => norm_sawtoothRem_le (le_trans (by norm_num) hK) (f n))
    refine le_trans hstep ?_
    exact mul_le_mul_of_nonneg_left (majorant_bracket k q b I f hK) (by norm_num)
  linarith
/-! ## R4 — the `m = 1` composite bound -/

/-- **R4.**  The `m = 1` term of the assembly, as its own row.

⛔ **WHY IT IS A ROW AND NOT A BLOCK:** `lem10_dyadic_bound` sums over `Finset.Ioc M (2M)`,
and no block of that shape contains `m = 1`; the `m = 1` term has to be composed from
`lem10_abel_transfer` and `klPhaseSum_bound` directly, and it carries no gcd SUM, so it pays
none of the dyadic row's averaging factor.

**The numeral.**  The route closes at `8` and even at `4` (the `C = 2` mutant fails in its
first `ring` identity, so `4` is this route's floor); the row is STATED at `16` because `16`
is what the p.223 assembly consumes, and a frozen statement is not moved to fit a proof.  The
last `calc` step is therefore `8·X ≤ 16·X` on a nonnegative product.  ⚠️ The `(1 + 4πV)`
factor is likewise weaker than the `(1 + 2πV)` that `lem10_abel_transfer` gives at `m = 1`;
it is the assembly's spelling and must not be read as load-bearing. -/
theorem lem10_m1_bound [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q)) :
    ‖lem10ExpSum k q b (Finset.Ioc A B) 1 (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (1 + 4 * Real.pi * V) * 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
          * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
          * (E + k) / Real.sqrt k := by
  classical
  have hkpos : 0 < k := by omega
  have hkne : k ≠ 0 := by omega
  have hk₀dvd : (k / q) ∣ k := Nat.div_dvd_of_dvd hqk
  have hk₀pos : 0 < k / q := Nat.div_pos (Nat.le_of_dvd hkpos hqk) hq
  have hV0 : (0 : ℝ) ≤ V :=
    le_trans (Finset.sum_nonneg (fun n _ => abs_nonneg _)) hvar
  have hE0 : (0 : ℝ) < E := lt_of_lt_of_le zero_lt_one hE
  -- the `m = 1` gcd is 1, by `hc`
  have hgcd1 : Nat.gcd (k / q) c.natAbs = 1 := Nat.Coprime.symm hc
  -- the (7.7) W
  have hW : ∀ n : ℤ, n ≤ B →
      ‖lem10ExpSum k q b (Finset.Ioc A n) 1 (fun x => (c : ℝ) * (invMod x k : ℝ) / k)‖
        ≤ 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
              * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
            * (E * Real.sqrt ((Nat.gcd (k / q) c.natAbs : ℕ) : ℝ)
                + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ))) := by
    intro n hnB
    have hlen' : (((n - A).toNat : ℕ) : ℝ) ≤ 2 * E := by
      have h1 : (n - A).toNat ≤ (B - A).toNat := by omega
      have h2 : (((n - A).toNat : ℕ) : ℝ) ≤ (((B - A).toNat : ℕ) : ℝ) := by exact_mod_cast h1
      linarith [hlen]
    exact klPhaseSum_bound (k := k) hk hq hqk b A n c hE hlen'
  have habel := lem10_abel_transfer k q b A B hAB 1 g
    (fun x => (c : ℝ) * (invMod x k : ℝ) / k) hW hvar
  refine le_trans habel ?_
  -- the numeric close: no factor 2, because there is no gcd SUM at `m = 1`
  rw [hgcd1]
  have hd1 : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by
    have : 1 ≤ k.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hkne⟩
    exact_mod_cast this
  have hlog1 : (1 : ℝ) ≤ Real.log (2 * (k : ℝ)) := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h4 : (4 : ℝ) ≤ 2 * (k : ℝ) := by linarith
    have h : Real.log 4 ≤ Real.log (2 * (k : ℝ)) := Real.log_le_log (by norm_num) h4
    have h4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h4eq] at h
    nlinarith [Real.log_two_gt_d9]
  have hKle : ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
        * Real.log (2 * ((k / q : ℕ) : ℝ))
      ≤ (k : ℝ) * (k.divisors.card : ℝ) * Real.log (2 * (k : ℝ)) := by
    have h1 : ((k / q : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hkpos hk₀dvd
    have h2 : (((k / q).divisors.card : ℕ) : ℝ) ≤ (k.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_le_of_dvd hkne hk₀dvd
    have h3 : Real.log (2 * ((k / q : ℕ) : ℝ)) ≤ Real.log (2 * (k : ℝ)) := by
      refine Real.log_le_log (by positivity) ?_
      linarith
    have h4 : (0 : ℝ) ≤ Real.log (2 * ((k / q : ℕ) : ℝ)) := by
      refine Real.log_nonneg ?_
      have : (1 : ℝ) ≤ ((k / q : ℕ) : ℝ) := by exact_mod_cast hk₀pos
      linarith
    have h5 : (0 : ℝ) ≤ ((k / q : ℕ) : ℝ) := by positivity
    have h6 : (0 : ℝ) ≤ (((k / q).divisors.card : ℕ) : ℝ) := by positivity
    have hkR0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    calc ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
            * Real.log (2 * ((k / q : ℕ) : ℝ))
        ≤ (k : ℝ) * ((k / q).divisors.card : ℝ) * Real.log (2 * ((k / q : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h6) h4
      _ ≤ (k : ℝ) * (k.divisors.card : ℝ) * Real.log (2 * ((k / q : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hkR0) h4
      _ ≤ (k : ℝ) * (k.divisors.card : ℝ) * Real.log (2 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  -- the inner bound, WITHOUT the factor 2 the dyadic row pays for its gcd average
  have hinner : (k.divisors.card : ℝ)
        * (E * Real.sqrt ((1 : ℕ) : ℝ)
            + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
              * Real.log (2 * ((k / q : ℕ) : ℝ)))
      ≤ (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (E + (k : ℝ)) := by
    have hs1 : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hs1, mul_one]
    have hd0 : (0 : ℝ) ≤ (k.divisors.card : ℝ) := by positivity
    have hL0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := by linarith
    have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hdsq : (1 : ℝ) ≤ (k.divisors.card : ℝ) ^ 2 := by nlinarith [hd1]
    have h1 : (1 : ℝ) ≤ (k.divisors.card : ℝ) ^ 2 * Real.log (2 * (k : ℝ)) := by
      nlinarith [hdsq, hlog1]
    have hA : (k.divisors.card : ℝ)
          * (E + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
              * Real.log (2 * ((k / q : ℕ) : ℝ)))
        ≤ (k.divisors.card : ℝ) * (E + (k : ℝ) * (k.divisors.card : ℝ)
              * Real.log (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith [hKle]) hd0
    have hC : (k.divisors.card : ℝ) * E
        ≤ (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * E := by
      have h2 : (k.divisors.card : ℝ) * (1 * E)
          ≤ (k.divisors.card : ℝ)
              * ((k.divisors.card : ℝ) ^ 2 * Real.log (2 * (k : ℝ)) * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hE0.le) hd0
      calc (k.divisors.card : ℝ) * E = (k.divisors.card : ℝ) * (1 * E) := by ring
        _ ≤ (k.divisors.card : ℝ)
              * ((k.divisors.card : ℝ) ^ 2 * Real.log (2 * (k : ℝ)) * E) := h2
        _ = (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * E := by ring
    have h3 : (k.divisors.card : ℝ) ^ 2 ≤ (k.divisors.card : ℝ) ^ 3 := by
      nlinarith [hd1, hd0]
    have hD : (k.divisors.card : ℝ) ^ 2 * ((k : ℝ) * Real.log (2 * (k : ℝ)))
        ≤ (k.divisors.card : ℝ) ^ 3 * ((k : ℝ) * Real.log (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right h3 (mul_nonneg hkR hL0)
    calc (k.divisors.card : ℝ)
          * (E + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
              * Real.log (2 * ((k / q : ℕ) : ℝ)))
        ≤ (k.divisors.card : ℝ) * (E + (k : ℝ) * (k.divisors.card : ℝ)
              * Real.log (2 * (k : ℝ))) := hA
      _ = (k.divisors.card : ℝ) * E
            + (k.divisors.card : ℝ) ^ 2 * ((k : ℝ) * Real.log (2 * (k : ℝ))) := by ring
      _ ≤ (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * E
            + (k.divisors.card : ℝ) ^ 3 * ((k : ℝ) * Real.log (2 * (k : ℝ))) := by
          linarith [hC, hD]
      _ = (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (E + (k : ℝ)) := by ring
  have hPre : (0 : ℝ) ≤ 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
      * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ) := by positivity
  have hstep : 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
          * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
        * (E * Real.sqrt ((1 : ℕ) : ℝ)
            + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
              * Real.log (2 * ((k / q : ℕ) : ℝ)))
      ≤ 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
          * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ))
          / Real.sqrt (k : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hinner hPre
    calc 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
          * (E * Real.sqrt ((1 : ℕ) : ℝ)
              + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                * Real.log (2 * ((k / q : ℕ) : ℝ)))
        = (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (q : ℝ) ^ ((3 : ℝ) / 2)
              / Real.sqrt (k : ℝ))
            * ((k.divisors.card : ℝ)
              * (E * Real.sqrt ((1 : ℕ) : ℝ)
                  + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                    * Real.log (2 * ((k / q : ℕ) : ℝ)))) := by ring
      _ ≤ (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (q : ℝ) ^ ((3 : ℝ) / 2)
              / Real.sqrt (k : ℝ))
            * ((k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (E + (k : ℝ))) := h
      _ = 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
            * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ))
            / Real.sqrt (k : ℝ) := by ring
  have hfac : (1 : ℝ) + 2 * Real.pi * ((1 : ℕ) : ℝ) * V ≤ 1 + 4 * Real.pi * V := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    push_cast
    nlinarith [mul_nonneg hpi.le hV0]
  have hnn : (0 : ℝ) ≤ 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
      * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ))
      / Real.sqrt (k : ℝ) := by
    have hL0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := by linarith
    have : (0 : ℝ) ≤ E + (k : ℝ) := by positivity
    positivity
  have hfac0 : (0 : ℝ) ≤ (1 : ℝ) + 2 * Real.pi * ((1 : ℕ) : ℝ) * V := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    push_cast
    nlinarith [mul_nonneg hpi.le hV0]
  -- the ONE licensed deviation from the receipt: its `8` is carried to the frozen `16`
  have hfac4 : (0 : ℝ) ≤ 1 + 4 * Real.pi * V := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [mul_nonneg hpi.le hV0]
  calc ((1 : ℝ) + 2 * Real.pi * ((1 : ℕ) : ℝ) * V)
        * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
            * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (k : ℝ)
          * (E * Real.sqrt ((1 : ℕ) : ℝ)
              + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                * Real.log (2 * ((k / q : ℕ) : ℝ))))
      ≤ ((1 : ℝ) + 2 * Real.pi * ((1 : ℕ) : ℝ) * V)
        * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
            * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ))
            / Real.sqrt (k : ℝ)) := mul_le_mul_of_nonneg_left hstep hfac0
    _ ≤ (1 + 4 * Real.pi * V)
        * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
            * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ))
            / Real.sqrt (k : ℝ)) := mul_le_mul_of_nonneg_right hfac hnn
    _ ≤ (1 + 4 * Real.pi * V)
        * (2 * (8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
            * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ))
            / Real.sqrt (k : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith [hnn]) hfac4
    _ = (1 + 4 * Real.pi * V) * 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
          * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
          * (E + (k : ℝ)) / Real.sqrt (k : ℝ) := by ring
/-! ## The road twins — the 2-adic factor bounded by `16` and paid in the constant

⛔ The factor `√(2^{v₂ k})` is **not removed** by these rows: it is BOUNDED BY `16` from the
row's own binder `hv2k : k.factorization 2 ≤ 8` and paid in the constant, which is exactly what
the literals `128 = 8·16` and `256 = 16·16` encode.  Each row is a `le_trans` onto its landed
twin (`klPhaseSum_bound`, `lem10_dyadic_bound`, and `lem10_m1_bound` above) through the one
shared helper below.  A genuine re-proof through the road modulus would deliver statements
`16×` sharper than these; that is a different row, and iron rule 1 forbids writing it here. -/

/-- `√(2^{v₂ k}) ≤ 16` from `hv2k : v₂ k ≤ 8` — the whole content of the road collapse. -/
private lemma sqrt_two_pow_v2_le_16 (hv2k : k.factorization 2 ≤ 8) :
    Real.sqrt ((2 : ℝ) ^ k.factorization 2) ≤ 16 := by
  have h1 : ((2 : ℝ) ^ k.factorization 2) ≤ (2 : ℝ) ^ (8 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) hv2k
  calc Real.sqrt ((2 : ℝ) ^ k.factorization 2)
      ≤ Real.sqrt ((2 : ℝ) ^ (8 : ℕ)) := Real.sqrt_le_sqrt h1
    _ = 16 := by
        rw [show ((2 : ℝ) ^ (8 : ℕ)) = (16 : ℝ) ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)

/-- **The road twin of `klPhaseSum_bound`** (HB (7.7)), at the constant `128 = 8·16`. -/
theorem klPhaseSum_bound_road [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (hv2k : k.factorization 2 ≤ 8)
    (b A B c : ℤ) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E) :
    ‖klPhaseSum k q b A B c‖
      ≤ 128 * (k.divisors.card : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt k
          * (E * Real.sqrt (Nat.gcd (k / q) c.natAbs : ℝ)
              + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
                  * Real.log (2 * ((k / q : ℕ) : ℝ))) := by
  have hk₀R : (1 : ℝ) ≤ ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_div_iff hq).mpr (Nat.le_of_dvd (by omega) hqk)
  have hBIG : 0 ≤ E * Real.sqrt (Nat.gcd (k / q) c.natAbs : ℝ)
      + ((k / q : ℕ) : ℝ) * ((k / q).divisors.card : ℝ)
          * Real.log (2 * ((k / q : ℕ) : ℝ)) :=
    add_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
  have hS := sqrt_two_pow_v2_le_16 (k := k) hv2k
  have hnum : 8 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ)
        * (q : ℝ) ^ ((3 : ℝ) / 2)
      ≤ 128 * (k.divisors.card : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) := by
    have hDQ : (0 : ℝ) ≤ (k.divisors.card : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) := by positivity
    nlinarith [hS, hDQ]
  refine le_trans (klPhaseSum_bound hk hq hqk b A B c hE hlen) ?_
  refine mul_le_mul_of_nonneg_right ?_ hBIG
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (by positivity)

/-- **The road twin of `lem10_dyadic_bound`** (HB (7.8)), at the constant `256 = 16·16`. -/
theorem lem10_dyadic_bound_road [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (hv2k : k.factorization 2 ≤ 8)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q)) (M : ℕ) :
    ∑ m ∈ Finset.Ioc M (2 * M),
        ‖lem10ExpSum k q b (Finset.Ioc A B) m
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (1 + 4 * Real.pi * M * V) * 256
          * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
          * M * (E + k) / Real.sqrt k := by
  have hV0 : (0 : ℝ) ≤ V := le_trans (Finset.sum_nonneg fun n _ => abs_nonneg _) hvar
  have hP : (0 : ℝ) ≤ 1 + 4 * Real.pi * (M : ℝ) * V := by positivity
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hL : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hW : (0 : ℝ) ≤ (1 + 4 * Real.pi * (M : ℝ) * V) * 16 * (k.divisors.card : ℝ) ^ 3
      * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) * (E + (k : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hP (by norm_num)) (by positivity)) hL) (by positivity))
      (by positivity)) (by linarith)
  have hS := sqrt_two_pow_v2_le_16 (k := k) hv2k
  refine le_trans (lem10_dyadic_bound hk hq hqk b A B hAB hE hlen g hvar c hc M) ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc (1 + 4 * Real.pi * (M : ℝ) * V) * 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
        * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
        * (M : ℝ) * (E + (k : ℝ))
      = Real.sqrt ((2 : ℝ) ^ k.factorization 2)
        * ((1 + 4 * Real.pi * (M : ℝ) * V) * 16 * (k.divisors.card : ℝ) ^ 3
          * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) * (E + (k : ℝ))) := by
        ring
    _ ≤ 16 * ((1 + 4 * Real.pi * (M : ℝ) * V) * 16 * (k.divisors.card : ℝ) ^ 3
          * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) * (E + (k : ℝ))) :=
        mul_le_mul_of_nonneg_right hS hW
    _ = (1 + 4 * Real.pi * (M : ℝ) * V) * 256 * (k.divisors.card : ℝ) ^ 3
          * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) * (E + (k : ℝ)) := by
        ring

/-- **The road twin of `lem10_m1_bound`** (BD3), at the constant `256 = 16·16`.

Without this row the road seal is not assemblable at all: its `m = 1` term would still carry a
`√(2^{v₂ k})` while every other term had been collapsed.  It is `le_trans` onto
`lem10_m1_bound` above — the missing *link*, not a missing convenience. -/
theorem lem10_m1_bound_road [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (hv2k : k.factorization 2 ≤ 8)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q)) :
    ‖lem10ExpSum k q b (Finset.Ioc A B) 1
        (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (1 + 4 * Real.pi * V) * 256
          * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
          * (E + k) / Real.sqrt k := by
  have hV0 : (0 : ℝ) ≤ V := le_trans (Finset.sum_nonneg fun n _ => abs_nonneg _) hvar
  have hP : (0 : ℝ) ≤ 1 + 4 * Real.pi * V := by positivity
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hL : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hW : (0 : ℝ) ≤ (1 + 4 * Real.pi * V) * 16 * (k.divisors.card : ℝ) ^ 3
      * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hP (by norm_num)) (by positivity)) hL) (by positivity)) (by linarith)
  have hS := sqrt_two_pow_v2_le_16 (k := k) hv2k
  refine le_trans (lem10_m1_bound hk hq hqk b A B hAB hE hlen g hvar c hc) ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc (1 + 4 * Real.pi * V) * 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
        * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
        * (E + (k : ℝ))
      = Real.sqrt ((2 : ℝ) ^ k.factorization 2)
        * ((1 + 4 * Real.pi * V) * 16 * (k.divisors.card : ℝ) ^ 3
          * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ))) := by ring
    _ ≤ 16 * ((1 + 4 * Real.pi * V) * 16 * (k.divisors.card : ℝ) ^ 3
          * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ))) :=
        mul_le_mul_of_nonneg_right hS hW
    _ = (1 + 4 * Real.pi * V) * 256 * (k.divisors.card : ℝ) ^ 3
          * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + (k : ℝ)) := by ring

/-! ## R10 — the p.223 assembly of Lemma 10

The majorant bracket of `lem10PsiSum_le_fourier_split` is split at the cut `N` into the five
`m`-ranges `m = 0`, `m = 1`, `2 ≤ m ≤ K`, `K < m ≤ N` and `m > N`; the two middle ranges and
the Fourier column are covered by ONE dyadic machine, `weighted_dyadic_block_sum_le`, invoked
three times at three weights.  `K` and `N` are free naturals in every row below, under `hK`
and the cut hypothesis each row needs; `hb_lemma10` instantiates them at `sealK k` and at
`N = 2 ^ Nat.log 2 (sealK k * ⌈√k⌉₊)`.

Each row carries the binder prefix of `lem10_dyadic_bound` whole, even where the linter reports
one of its binders unused: the rows compose with each other and with the landed chain, and a
prefix that varies row by row costs more at the assembly than the warnings cost here. -/

/-- Every partial sum of the majorant tail `m > N` is under `K/(π²N)·2E`.

Private: this is the whole content of row B, and it is stated at `Finset.range M` rather than
as the `tsum` because BOTH consumers below want it in that shape — the bound itself and the
summability companion that keeps the bound from being vacuously true. -/
private lemma majorant_tail_range_le [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    {K N : ℕ} (hK : 2 ≤ K) (hN : 1 ≤ N) (M : ℕ) :
    ∑ i ∈ Finset.range M, ‖majorantCoeff K ((i + N + 1 : ℕ) : ℤ)‖
        * ‖lem10ExpSum k q b (Finset.Ioc A B) (i + N + 1)
            (fun x => g x + (c : ℝ) * (invMod x k : ℝ) / k)‖
      ≤ ((K : ℝ) / (Real.pi ^ 2 * N)) * (2 * E) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- THE E-SLOT ADAPTER: `Int.card_Ioc` and `hlen`, with nothing left over.
  have hcard : ((Finset.Ioc A B).card : ℝ) ≤ 2 * E := by
    rw [Int.card_Ioc]; exact hlen
  -- the trivial bound (7.5) on every term
  have hS : ∀ m : ℕ, ‖lem10ExpSum k q b (Finset.Ioc A B) m
        (fun x => g x + (c : ℝ) * (invMod x k : ℝ) / k)‖ ≤ 2 * E :=
    fun m => le_trans (norm_lem10ExpSum_le_card k q b _ m _) hcard
  -- the `K/m²` arm on the coefficient
  have ha : ∀ n : ℕ, ‖majorantCoeff K ((n + N + 1 : ℕ) : ℤ)‖
      ≤ (K : ℝ) / (Real.pi ^ 2 * (((n + N + 1 : ℕ)) : ℝ) ^ 2) := by
    intro n
    have hm0 : (n + N + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero _
    have hm : ((n + N + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hm0
    have h := norm_majorantCoeff_le_sq hK hm
    have hc2 : ((((n + N + 1 : ℕ) : ℤ)) : ℝ) = (((n + N + 1 : ℕ)) : ℝ) := by push_cast; ring
    rwa [hc2] at h
  -- termwise
  have hterm : ∀ n : ℕ, ‖majorantCoeff K ((n + N + 1 : ℕ) : ℤ)‖
        * ‖lem10ExpSum k q b (Finset.Ioc A B) (n + N + 1)
            (fun x => g x + (c : ℝ) * (invMod x k : ℝ) / k)‖
      ≤ (2 * E) * ((K : ℝ) / Real.pi ^ 2) * ((((n + N + 1 : ℕ)) : ℝ) ^ 2)⁻¹ := by
    intro n
    have hmpos : (0 : ℝ) < (((n + N + 1 : ℕ)) : ℝ) := by
      have : 0 < n + N + 1 := Nat.succ_pos _
      exact_mod_cast this
    have key : ‖majorantCoeff K ((n + N + 1 : ℕ) : ℤ)‖
          * ‖lem10ExpSum k q b (Finset.Ioc A B) (n + N + 1)
              (fun x => g x + (c : ℝ) * (invMod x k : ℝ) / k)‖
        ≤ ((K : ℝ) / (Real.pi ^ 2 * (((n + N + 1 : ℕ)) : ℝ) ^ 2)) * (2 * E) :=
      mul_le_mul (ha n) (hS (n + N + 1)) (norm_nonneg _) (by positivity)
    refine le_trans key (le_of_eq ?_)
    have hne : (((n + N + 1 : ℕ)) : ℝ) ≠ 0 := ne_of_gt hmpos
    field_simp
  -- the reindexed p-series tail
  have hsum : ∑ i ∈ Finset.range M, ((((i + N + 1 : ℕ)) : ℝ) ^ 2)⁻¹ ≤ ((N : ℝ))⁻¹ := by
    have hre : ∑ i ∈ Finset.range M, ((((i + N + 1 : ℕ)) : ℝ) ^ 2)⁻¹
        = ∑ j ∈ Finset.Ioc N (N + M), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
      refine Finset.sum_nbij' (i := fun i => i + N + 1) (j := fun j => j - N - 1)
        ?_ ?_ ?_ ?_ ?_
      · intro a ha'; simp only [Finset.mem_range] at ha'; simp only [Finset.mem_Ioc]; omega
      · intro a ha'; simp only [Finset.mem_Ioc] at ha'; simp only [Finset.mem_range]; omega
      · intro a ha'; omega
      · intro a ha'; simp only [Finset.mem_Ioc] at ha'; omega
      · intro a _; rfl
    rw [hre]
    have h1 : ∑ j ∈ Finset.Ioc N (N + M), (((j : ℕ) : ℝ) ^ 2)⁻¹
        ≤ ((N : ℝ))⁻¹ - (((N + M : ℕ)) : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub (by omega) (by omega)
    have h2 : (0 : ℝ) ≤ (((N + M : ℕ)) : ℝ)⁻¹ := by positivity
    linarith
  have hYnn : (0 : ℝ) ≤ (2 * E) * ((K : ℝ) / Real.pi ^ 2) := by positivity
  calc ∑ i ∈ Finset.range M, ‖majorantCoeff K ((i + N + 1 : ℕ) : ℤ)‖
          * ‖lem10ExpSum k q b (Finset.Ioc A B) (i + N + 1)
              (fun x => g x + (c : ℝ) * (invMod x k : ℝ) / k)‖
      ≤ ∑ i ∈ Finset.range M,
          (2 * E) * ((K : ℝ) / Real.pi ^ 2) * ((((i + N + 1 : ℕ)) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (2 * E) * ((K : ℝ) / Real.pi ^ 2)
          * ∑ i ∈ Finset.range M, ((((i + N + 1 : ℕ)) : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (2 * E) * ((K : ℝ) / Real.pi ^ 2) * ((N : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hsum hYnn
    _ = ((K : ℝ) / Real.pi ^ 2 * ((N : ℝ))⁻¹) * (2 * E) := by ring
    _ = ((K : ℝ) / (Real.pi ^ 2 * N)) * (2 * E) := by
        rw [div_mul_eq_div_div, div_eq_mul_inv ((K : ℝ) / Real.pi ^ 2) ((N : ℝ))]

/-- The tail of the majorant bracket is summable.

⛔ Without this the row above would be true and EMPTY: in Lean `∑' n, f n = 0` by definition
when `f` is not summable, so a `tsum` bound on a non-summable family says nothing.  The corpus
names the trap at `Salt/Weil/Sawtooth.lean:1420-1423`; it is answered here by the same range
bound the row itself consumes. -/
private lemma majorant_tail_summable [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    {K N : ℕ} (hK : 2 ≤ K) (hN : 1 ≤ N) :
    Summable (fun n : ℕ => ‖majorantCoeff K ((n + N + 1 : ℕ) : ℤ)‖
      * ‖lem10ExpSum k q b (Finset.Ioc A B) (n + N + 1)
          (fun x => g x + (c : ℝ) * (invMod x k : ℝ) / k)‖) :=
  summable_of_sum_range_le (fun _ => by positivity)
    (fun M => majorant_tail_range_le hk hq hqk b A B hAB hE hlen g hvar c hc hK hN M)

/-- **R10 row B — the majorant tail `m > N`.**  `∑_{m > N} ‖a_m‖·‖S_m‖ ≤ K/(π²N)·2E`.

The `K/m²` arm of (7.4) on the coefficient, the trivial bound (7.5) on the exponential sum, and
`sum_Ioc_inv_sq_le_sub` on what is left.  It depends on nothing else in the assembly.

**The `2E` is tight, and the `2E + 1` a first draft carried is not needed.**  `#I ≤ 2E` comes
from `Int.card_Ioc` and `hlen` with nothing left over; `card_le_of_mem_Ioc`'s `E + 1` is a
different route, whose hypothesis says WHERE the interval sits and which this row's binders
never supply.  At the assembly's own worst point (`E = 1`) the difference is `1.5×`, so the
slack is worth naming rather than inheriting. -/
theorem majorant_tail_le [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    {K N : ℕ} (hK : 2 ≤ K) (hN : 1 ≤ N) :
    ∑' n : ℕ, ‖majorantCoeff K ((n + N + 1 : ℕ) : ℤ)‖
        * ‖lem10ExpSum k q b (Finset.Ioc A B) (n + N + 1)
            (fun x => g x + (c : ℝ) * (invMod x k : ℝ) / k)‖
      ≤ ((K : ℝ) / (Real.pi ^ 2 * N)) * (2 * E) :=
  Real.tsum_le_of_sum_range_le (fun _ => by positivity)
    (fun M => majorant_tail_range_le hk hq hqk b A B hAB hE hlen g hvar c hc hK hN M)

end Salt.N7
