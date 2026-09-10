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

⛔ **NOT LANDED: `hb_lemma10` itself, nor `hb_lemma10_road`, `hb_lemma10_const`,
`hb_lemma10_inv`.**  What the R10 section below adds are the *ranges* of the assembly, not the
assembly: the majorant bracket split at the cut `N = 2 ^ Nat.log 2 (sealK k * ⌈√k⌉₊)` into the
five `m`-ranges `m = 0` (inside `majorant_tsum_split`), `m = 1`, `2 ≤ m ≤ K`, `K < m ≤ N` and
`m > N`, with the two middle ranges and the Fourier column covered dyadically by blocks
`(2^j, 2^{j+1}]` through one machine.  ⛔ **The p.223 assembly does NOT close from these rows
as they stand**: at `V = 0` the `m = 1` and `2 ≤ m ≤ K` rows spend the `K/m²` arm of (7.4),
whose contribution grows like `K = 2 + ⌊k^{1/4}⌋`, against a budget growing like
`log(2k)²` — the two cross near `k ≈ 1.3·10²⁴`.  See `docs/blueprints/flags.md`.  Nothing in
this file bears on twin primes.

**Numerals.**  Every constant below is the written ledger's, unmoved: `5/2` on the majorant
bracket, `1337/1000` and `206/100` on the two envelopes, `16` on the `m = 1` composite, and
`128` / `256` on the road twins.  The `m = 1` route is provable at `8` and at `4`; the row is
stated at `16` because that is what the assembly consumes.  The R10 rows below add `2/π²` and
`8K` on the head `2 ≤ m ≤ K`, `4/π²` on the range `K < m ≤ N`, `K/(π²N)` on the tail `m > N`,
and `2E` on the trivial-bound slot of (7.5) — each of these is the written ledger's too,
unmoved.  The assembly's `2^13` is not here; the assembly is not here.
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


/-- **R10 row M — the weighted dyadic-block machine.**  A weight `w` dominated on each dyadic
block `(2^j, 2^{j+1}]` by a constant `cj j` turns `∑_{a ≤ m ≤ bN} w m ‖S_m‖` into a sum of
`lem10_dyadic_bound`'s per-block bound against those constants.

⭐ **THIS ROW IS THE COVER, AND IT IS PAID ONCE.**  Rows F, H and A are three instantiations of
it — at `w m = 1/(π m)`, at `w m = ‖a_m‖` on `2 ≤ m ≤ K`, and at `w m = ‖a_m‖` on `K < m ≤ N` —
and none of them re-proves a fibering.  `hcj` is where each consumer pays for its own weight.

⛔ **The block range is not a token match with the landed row and is not defeq.**
`lem10_dyadic_bound` sums over `Finset.Ioc M (2 * M)`; the fibering hands you
`Finset.Ioc (2^j) (2^(j+1))`, and `Nat.pow_succ` is not `rfl` here because `Nat.mul` recurses
on its second argument.  The two `congr 1; ring` lines are that step.

`hlo` is passed through to `dyadic_cover_sum_le` in one token: the cut form's conclusion is
already indexed by `Finset.Icc lo (Nat.log 2 (bN - 1))`. -/
theorem weighted_dyadic_block_sum_le [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    (w : ℕ → ℝ) (cj : ℕ → ℝ)
    (hcj : ∀ j, ∀ m ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), w m ≤ cj j) (hcj0 : ∀ j, 0 ≤ cj j)
    {a bN lo : ℕ} (ha : 2 ≤ a) (hlo : ∀ m ∈ Finset.Icc a bN, lo ≤ Nat.log 2 (m - 1)) :
    ∑ m ∈ Finset.Icc a bN, w m * ‖lem10ExpSum k q b (Finset.Ioc A B) m
        (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ ∑ j ∈ Finset.Icc lo (Nat.log 2 (bN - 1)),
          cj j * ((1 + 4 * Real.pi * (2 ^ j : ℕ) * V)
            * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
                * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k)
            * (2 ^ j : ℕ)) := by
  classical
  refine Salt.Tactic.dyadic_cover_sum_le (Finset.Subset.refl _) hlo _ _ ?_
  intro j _
  -- the fibre lands in the dyadic block
  have hsub : ((Finset.Icc a bN).filter (fun m => Nat.log 2 (m - 1) = j))
      ⊆ Finset.Ioc (2 ^ j) (2 ^ (j + 1)) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨ham, _⟩, hlogm⟩ := hm
    have h2m : 2 ≤ m := le_trans ha ham
    obtain ⟨h1, h2⟩ := Salt.Tactic.mem_dyadic_block h2m hlogm
    exact Finset.mem_Ioc.mpr ⟨h1, h2⟩
  have hblk : Finset.Ioc (2 ^ j) (2 ^ (j + 1)) = Finset.Ioc (2 ^ j) (2 * 2 ^ j) := by
    congr 1; ring
  have hland := lem10_dyadic_bound (k := k) hk hq hqk b A B hAB hE hlen g hvar c hc (2 ^ j)
  calc ∑ m ∈ (Finset.Icc a bN).filter (fun m => Nat.log 2 (m - 1) = j),
          w m * ‖lem10ExpSum k q b (Finset.Ioc A B) m
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ ∑ m ∈ (Finset.Icc a bN).filter (fun m => Nat.log 2 (m - 1) = j),
          cj j * ‖lem10ExpSum k q b (Finset.Ioc A B) m
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ := by
        refine Finset.sum_le_sum ?_
        intro m hm
        exact mul_le_mul_of_nonneg_right (hcj j m (hsub hm)) (norm_nonneg _)
    _ = cj j * ∑ m ∈ (Finset.Icc a bN).filter (fun m => Nat.log 2 (m - 1) = j),
          ‖lem10ExpSum k q b (Finset.Ioc A B) m
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ := by
        rw [Finset.mul_sum]
    _ ≤ cj j * ∑ m ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j),
          ‖lem10ExpSum k q b (Finset.Ioc A B) m
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (hcj0 j)
        refine Finset.sum_le_sum_of_subset_of_nonneg (hblk ▸ hsub) ?_
        intro i _ _; exact norm_nonneg _
    _ ≤ cj j * ((1 + 4 * Real.pi * (2 ^ j : ℕ) * V)
            * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
                * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k)
            * (2 ^ j : ℕ)) := by
        refine mul_le_mul_of_nonneg_left (le_trans hland ?_) (hcj0 j)
        ring_nf
        exact le_refl _


/-- `min a b ≤ √(ab)` for `a, b ≥ 0`.  The geometric-mean step of rows P′ and H′. -/
private lemma min_le_sqrt_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : min a b ≤ Real.sqrt (a * b) :=
  Real.le_sqrt_of_sq_le (by nlinarith [min_le_left a b, min_le_right a b, le_min ha hb])

/-- The √ algebra of the per-block geometric mean: `√((2(1+log K)/K)·(K/(π²4^j)))`
collapses to `√(2(1+log K))/(π·2^j)`, whose product with `2^j` is j-FREE.  Private: H′'s. -/
private lemma sqrt_block {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    Real.sqrt ((2 * (1 + Real.log K) / K) * ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
      = Real.sqrt (2 * (1 + Real.log K)) / (Real.pi * (2 : ℝ) ^ j) := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (K : ℝ) ≠ 0 := by linarith
  have h4 : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
    rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have hEq : (2 * (1 + Real.log K) / K) * ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j))
      = (2 * (1 + Real.log K)) / (Real.pi * (2 : ℝ) ^ j) ^ 2 := by
    rw [h4]; field_simp
  have hlogK : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
  rw [hEq, Real.sqrt_div (by linarith), Real.sqrt_sq (by positivity)]

/-- **R10 row P′ — the `m = 1` majorant term, min-composed.**
`‖a_1‖·‖S_1‖ ≤ (√(2(1+log K))/π + 4VK/π)·C`: the V-free half by the GEOMETRIC MEAN of
(7.4)'s two arms, the V half by the `K/m²` arm alone. -/
theorem majorant_m1_le [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    {K : ℕ} (hK : 2 ≤ K) :
    ‖majorantCoeff K (1 : ℤ)‖
        * ‖lem10ExpSum k q b (Finset.Ioc A B) 1
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (Real.sqrt (2 * (1 + Real.log K)) / Real.pi + 4 * V * (K : ℝ) / Real.pi)
          * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
              * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k) := by
  have hV0 : (0 : ℝ) ≤ V := le_trans (Finset.sum_nonneg (fun n _ => abs_nonneg _)) hvar
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  set C : ℝ := 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
      * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k with hCdef
  have hC0 : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  have hgm : min (2 * (1 + Real.log K) / K) ((K : ℝ) / Real.pi ^ 2)
      ≤ Real.sqrt (2 * (1 + Real.log K)) / Real.pi := by
    refine le_trans (min_le_sqrt_mul (by positivity) (by positivity)) (le_of_eq ?_)
    rw [show (2 * (1 + Real.log K) / K) * ((K : ℝ) / Real.pi ^ 2)
          = (2 * (1 + Real.log K)) / Real.pi ^ 2 by field_simp,
      Real.sqrt_div (by nlinarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ (K:ℝ))]),
      Real.sqrt_sq Real.pi_pos.le]
  refine le_trans (mul_le_mul (le_min (norm_majorantCoeff_le hK 1)
      (by simpa using norm_majorantCoeff_le_sq hK (m := (1 : ℤ)) one_ne_zero))
    (le_trans (lem10_m1_bound hk hq hqk b A B hAB hE hlen g hvar c hc)
      (le_of_eq (by rw [hCdef]; ring)) :
        ‖lem10ExpSum k q b (Finset.Ioc A B) 1
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ ≤ (1 + 4 * Real.pi * V) * C)
    (norm_nonneg _) (le_min (by positivity) (by positivity))) ?_
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc min (2 * (1 + Real.log K) / K) ((K : ℝ) / Real.pi ^ 2) * ((1 + 4 * Real.pi * V) * C)
      = min (2 * (1 + Real.log K) / K) ((K : ℝ) / Real.pi ^ 2) * C
        + min (2 * (1 + Real.log K) / K) ((K : ℝ) / Real.pi ^ 2) * (4 * Real.pi * V * C) := by ring
    _ ≤ Real.sqrt (2 * (1 + Real.log K)) / Real.pi * C
        + (K : ℝ) / Real.pi ^ 2 * (4 * Real.pi * V * C) :=
        add_le_add (mul_le_mul_of_nonneg_right hgm hC0)
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
    _ = (Real.sqrt (2 * (1 + Real.log K)) / Real.pi + 4 * V * (K : ℝ) / Real.pi) * C := by
        field_simp


/-- On the dyadic block `(2^j, 2^{j+1}]` the Fourier weight `1/(π m)` is dominated by its
value at the bottom of the block.  Private: row F's own direction check.

There is no boundary case and no `min`: on the block `2^j < m` is STRICT, so
`one_div_le_one_div_of_le` has all the room it needs. -/
private lemma direction_check (j : ℕ) :
    ∀ m ∈ Finset.Ioc ((2 : ℕ) ^ j) ((2 : ℕ) ^ (j + 1)),
      1 / (Real.pi * (m : ℝ)) ≤ 1 / (Real.pi * ((2 ^ j : ℕ) : ℝ)) := by
  intro m hm
  have h1 : (2 : ℕ) ^ j < m := (Finset.mem_Ioc.mp hm).1
  have hlt : ((2 ^ j : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast h1
  have hpos : (0 : ℝ) < Real.pi * ((2 ^ j : ℕ) : ℝ) := by positivity
  exact one_div_le_one_div_of_le hpos (by nlinarith [Real.pi_pos])

/-- **The dyadic block count as a real logarithm**: `log₂(K−1) + 1 ≤ logb 2 K + 1`.

Private, and SHARED by rows F and H: a dyadic block count is a base-2 logarithm, and every
consumer that turns one into an analytic bound pays this conversion once.  `Nat.log_mono_right`
then mathlib's `Real.natLog_le_logb` — whose argument order is `(n, b)`, i.e. `K` then `2`. -/
private lemma blockcount_le {K : ℕ} (hK : 2 ≤ K) :
    ((Nat.log 2 (K - 1) : ℕ) : ℝ) + 1 ≤ Real.logb 2 K + 1 := by
  have h1 : Nat.log 2 (K - 1) ≤ Nat.log 2 K := Nat.log_mono_right (by omega)
  have h2 : ((Nat.log 2 K : ℕ) : ℝ) ≤ Real.logb 2 K := Real.natLog_le_logb K 2
  have h3 : ((Nat.log 2 (K - 1) : ℕ) : ℝ) ≤ ((Nat.log 2 K : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

/-- **The geometric close of row F's `V`-part**: `∑_{j ≤ log₂(K−1)} 2^j ≤ 2K`.

Private.  The seam `Icc 0 J = range (J+1)` is not `rfl` and is taken by `ext`; then
`geom_two_pow_range_le` and `Nat.pow_log_le_self`, whose side condition `K − 1 ≠ 0` is `hK`
itself, so there is no corner case.  Nothing is surrendered here: the constant is exact. -/
private lemma geom_close {K : ℕ} (hK : 2 ≤ K) :
    ∑ j ∈ Finset.Icc 0 (Nat.log 2 (K - 1)), ((2 ^ j : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
  have hset : Finset.Icc 0 (Nat.log 2 (K - 1)) = Finset.range (Nat.log 2 (K - 1) + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  have hpow : ((2 : ℕ) ^ Nat.log 2 (K - 1)) ≤ K - 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowR : ((2 : ℝ)) ^ Nat.log 2 (K - 1) ≤ (K : ℝ) - 1 := by
    have h : (((2 : ℕ) ^ Nat.log 2 (K - 1) : ℕ) : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by exact_mod_cast hpow
    rw [Nat.cast_sub (by omega : 1 ≤ K)] at h
    push_cast at h ⊢
    linarith
  calc ∑ j ∈ Finset.Icc 0 (Nat.log 2 (K - 1)), ((2 ^ j : ℕ) : ℝ)
      = ∑ j ∈ Finset.range (Nat.log 2 (K - 1) + 1), (2 : ℝ) ^ j := by
        rw [hset]; push_cast; ring_nf
    _ ≤ (2 : ℝ) ^ (Nat.log 2 (K - 1) + 1) := Salt.Tactic.geom_two_pow_range_le _
    _ ≤ 2 * (K : ℝ) := by rw [pow_succ]; nlinarith

/-- **R10 row F — the Fourier column over `2 ≤ m ≤ K`** (HB's R6′).
`∑_{2 ≤ m ≤ K} ‖S_m‖/(π m) ≤ ((logb 2 K + 1)/π + 8KV)·C`.

The FIRST of the machine's three instantiations, at the weight `w m = 1/(π m)` and the block
constant `cj j = 1/(π 2^j)`.  The per-block term then collapses by `field_simp` to
`C/π + 4VC·2^j`: a `V`-free part whose block count is `blockcount_le`, and a `V`-part whose
geometric sum is `geom_close`.  The constant is EXACT — no slack is surrendered in the close.

⚠️ The `m = 1` term is NOT here.  It is peeled by the assembly and carried by the landed
`lem10_m1_bound` at the weight `1/π`; this row starts at `m = 2` because the dyadic cover
does. -/
theorem fourier_column_le [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    {K : ℕ} (hK : 2 ≤ K) :
    ∑ m ∈ Finset.Icc 2 K, ‖lem10ExpSum k q b (Finset.Ioc A B) m
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ / (Real.pi * (m : ℝ))
      ≤ ((Real.logb 2 K + 1) / Real.pi + 8 * (K : ℝ) * V)
          * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
              * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hV0 : (0 : ℝ) ≤ V := le_trans (Finset.sum_nonneg (fun n _ => abs_nonneg _)) hvar
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hEk : (0 : ℝ) ≤ E + (k : ℝ) := by positivity
  have hC0 : (0 : ℝ) ≤ 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
      * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k := by
    positivity
  -- (i) F's summand is a DIVISION; the machine's is a weight times a norm.
  have hL : ∑ m ∈ Finset.Icc 2 K, ‖lem10ExpSum k q b (Finset.Ioc A B) m
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ / (Real.pi * (m : ℝ))
      = ∑ m ∈ Finset.Icc 2 K, (1 / (Real.pi * (m : ℝ)))
          * ‖lem10ExpSum k q b (Finset.Ioc A B) m
              (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ :=
    Finset.sum_congr rfl (fun m _ => by ring)
  rw [hL]
  -- (ii) the machine, at `w m = 1/(π m)`, `cj j = 1/(π 2^j)`, `a = 2`, `bN = K`, `lo = 0`
  refine le_trans (weighted_dyadic_block_sum_le hk hq hqk b A B hAB hE hlen g hvar c hc
      (fun m => 1 / (Real.pi * (m : ℝ))) (fun j => 1 / (Real.pi * ((2 ^ j : ℕ) : ℝ)))
      direction_check (fun j => by positivity) (a := 2) (bN := K) (lo := 0)
      le_rfl (fun m _ => Nat.zero_le _)) ?_
  -- (iii) the per-block identity `(1/(π 2^j))·((1 + 4π 2^j V)·D·2^j) = D/π + 4VD·2^j`
  have hterm : ∀ (D : ℝ) (j : ℕ),
      (1 / (Real.pi * ((2 ^ j : ℕ) : ℝ)))
          * ((1 + 4 * Real.pi * ((2 ^ j : ℕ) : ℝ) * V) * D * ((2 ^ j : ℕ) : ℝ))
        = D / Real.pi + 4 * V * D * ((2 ^ j : ℕ) : ℝ) := by
    intro D j
    have h2 : ((2 ^ j : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    try ring
  rw [Finset.sum_congr rfl (fun j _ => hterm _ j), Finset.sum_add_distrib, Finset.sum_const,
    ← Finset.mul_sum, Nat.card_Icc, nsmul_eq_mul]
  -- (iv) the V-free close: the block count is a base-2 logarithm
  have hcount : ((Nat.log 2 (K - 1) + 1 - 0 : ℕ) : ℝ) ≤ Real.logb 2 K + 1 := by
    have h := blockcount_le hK
    simp only [Nat.sub_zero]
    push_cast
    linarith
  -- (v) the V part: the geometric sum of the block bottoms
  have hgeom := geom_close hK
  have hCpi : (0 : ℝ) ≤ (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
      * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
      * (E + k) / Real.sqrt k) / Real.pi := div_nonneg hC0 hpi.le
  have hVC : (0 : ℝ) ≤ 4 * V * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
      * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
      * (E + k) / Real.sqrt k) := mul_nonneg (by linarith) hC0
  have hA := mul_le_mul_of_nonneg_right hcount hCpi
  have hB := mul_le_mul_of_nonneg_left hgeom hVC
  have hfin : (Real.logb 2 K + 1)
        * ((16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
            * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k)
          / Real.pi)
      + 4 * V * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
          * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k)
        * (2 * (K : ℝ))
      = ((Real.logb 2 K + 1) / Real.pi + 8 * (K : ℝ) * V)
          * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
              * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k) := by
    ring
  linarith


/-- The `K/m²` arm of (7.4) at the BOTTOM of the dyadic block: on `(2^j, 2^{j+1}]` every
coefficient obeys `‖a_m‖ ≤ K/(π²4^j)`.  Private, and SHARED by rows H and A.

⛔ Stated as `∀ m : ℕ, m ∈ Finset.Ioc …` and not as `∀ m ∈ Finset.Ioc …`: the latter elaborates
`m` over `ℤ`, builds green, and then does not apply to the ℕ-indexed cover. -/
private lemma hcj_sq {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    ∀ m : ℕ, m ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)) →
      ‖majorantCoeff K ((m : ℕ) : ℤ)‖ ≤ (K : ℝ) / (Real.pi ^ 2 * 4 ^ j) := by
  intro m hm
  have hb := Finset.mem_Ioc.mp hm
  have hm0 : ((m : ℤ)) ≠ 0 := by have : 2 ^ j < m := hb.1; omega
  have h4 : ((4 : ℝ)) ^ j ≤ ((m : ℝ)) ^ 2 := by
    have h1 : (2 : ℕ) ^ j < m := hb.1
    have h2 : ((2 : ℝ)) ^ j ≤ (m : ℝ) := by
      have h2' : ((2 ^ j : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1.le
      simpa using h2'
    have hx : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
      rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
    nlinarith [hx, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
  refine (norm_majorantCoeff_le_sq hK hm0).trans ?_
  push_cast
  have hd1 : (0 : ℝ) < Real.pi ^ 2 * ((m : ℝ)) ^ 2 := by
    have : (0 : ℝ) < (m : ℝ) := by
      have : (0 : ℕ) < m := by omega
      exact_mod_cast this
    positivity
  have hd2 : (0 : ℝ) < Real.pi ^ 2 * (4 : ℝ) ^ j := by positivity
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ) * Real.pi ^ 2) (sub_nonneg.mpr h4)]

/-- **Row H′'s close** — the min-composed coefficient, bounded per block by the geometric
mean.  Private.  Both halves are j-FREE, so there is no geometric series: the block sum is
`(J+1)·(√(2(1+log K))/π + 4VK/π)·C`. -/
private lemma head_close_min {K : ℕ} (hK : 2 ≤ K) {V C : ℝ} (hV : 0 ≤ V) (hC : 0 ≤ C) :
    ∑ j ∈ Finset.range (Nat.log 2 (K - 1) + 1),
        (min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
          * ((1 + 4 * Real.pi * ((2 ^ j : ℕ) : ℝ) * V) * C * ((2 ^ j : ℕ) : ℝ))
      ≤ ((Real.logb 2 K + 1) * Real.sqrt (2 * (1 + Real.log K)) / Real.pi
          + 4 * V * (Real.logb 2 K + 1) * (K : ℝ) / Real.pi) * C := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hlogK : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
  set n : ℕ := Nat.log 2 (K - 1) + 1 with hn
  have hpt : ∀ j ∈ Finset.range n,
      (min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
          * ((1 + 4 * Real.pi * ((2 ^ j : ℕ) : ℝ) * V) * C * ((2 ^ j : ℕ) : ℝ))
        ≤ Real.sqrt (2 * (1 + Real.log K)) / Real.pi * C + 4 * V * (K : ℝ) * C / Real.pi := by
    intro j _
    have h2j : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
    have h4j : ((4 : ℝ)) ^ j = ((2 : ℝ) ^ j) * ((2 : ℝ) ^ j) := by
      rw [← mul_pow]; norm_num
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    -- the two arms
    have hA : (min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
        ≤ Real.sqrt (2 * (1 + Real.log K)) / (Real.pi * (2 : ℝ) ^ j) := by
      refine le_trans (min_le_sqrt_mul (by positivity) (by positivity)) ?_
      exact le_of_eq (sqrt_block hK j)
    have hB : (min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
        ≤ (K : ℝ) / (Real.pi ^ 2 * 4 ^ j) := min_le_right _ _
    have hsplit : (min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
          * ((1 + 4 * Real.pi * ((2 ^ j : ℕ) : ℝ) * V) * C * ((2 ^ j : ℕ) : ℝ))
        = (min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j))) * (C * (2 : ℝ) ^ j)
          + (min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
              * (4 * Real.pi * V * C * ((2 : ℝ) ^ j * (2 : ℝ) ^ j)) := by
      rw [h2j]; ring
    rw [hsplit]
    refine add_le_add ?_ ?_
    · refine le_trans (mul_le_mul_of_nonneg_right hA (by positivity)) (le_of_eq ?_)
      field_simp
    · refine le_trans (mul_le_mul_of_nonneg_right hB (by positivity)) (le_of_eq ?_)
      rw [h4j]
      field_simp
  calc ∑ j ∈ Finset.range n,
          (min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
            * ((1 + 4 * Real.pi * ((2 ^ j : ℕ) : ℝ) * V) * C * ((2 ^ j : ℕ) : ℝ))
      ≤ ∑ _j ∈ Finset.range n,
          (Real.sqrt (2 * (1 + Real.log K)) / Real.pi * C + 4 * V * (K : ℝ) * C / Real.pi) :=
        Finset.sum_le_sum hpt
    _ = (n : ℝ) * (Real.sqrt (2 * (1 + Real.log K)) / Real.pi * C
          + 4 * V * (K : ℝ) * C / Real.pi) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (Real.logb 2 K + 1) * (Real.sqrt (2 * (1 + Real.log K)) / Real.pi * C
          + 4 * V * (K : ℝ) * C / Real.pi) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hn]; push_cast; exact blockcount_le hK
    _ = ((Real.logb 2 K + 1) * Real.sqrt (2 * (1 + Real.log K)) / Real.pi
          + 4 * V * (Real.logb 2 K + 1) * (K : ℝ) / Real.pi) * C := by
        field_simp

/-- **R10 row H′ — the majorant head `2 ≤ m ≤ K`, min-composed.**  The SECOND instantiation
of the machine, at `w = ‖a_m‖` and `cj j = min (2(1+log K)/K) (K/(π²4^j))`; per block the
geometric mean bounds the V-free half and the `K/m²` arm the V half, so the block sum is
`(J+1)·(√(2(1+log K))/π + 4VK/π)·C` with no geometric series. -/
theorem majorant_head_le [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    {K : ℕ} (hK : 2 ≤ K) :
    ∑ m ∈ Finset.Icc 2 K, ‖majorantCoeff K (m : ℤ)‖
          * ‖lem10ExpSum k q b (Finset.Ioc A B) m
              (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ ((Real.logb 2 K + 1) * Real.sqrt (2 * (1 + Real.log K)) / Real.pi
          + 4 * V * (Real.logb 2 K + 1) * (K : ℝ) / Real.pi)
          * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
              * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k) := by
  have hV0 : (0 : ℝ) ≤ V := le_trans (Finset.sum_nonneg (fun n _ => abs_nonneg _)) hvar
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hEk : (0 : ℝ) ≤ E + (k : ℝ) := by positivity
  have hC0 : (0 : ℝ) ≤ 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
      * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k := by
    positivity
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hlogK : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
  refine le_trans (weighted_dyadic_block_sum_le hk hq hqk b A B hAB hE hlen g hvar c hc
      (fun m => ‖majorantCoeff K ((m : ℕ) : ℤ)‖)
      (fun j => min (2 * (1 + Real.log K) / K) ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j)))
      (fun j m hm => le_min (norm_majorantCoeff_le hK _) (hcj_sq hK j m hm))
      (fun j => le_min (by positivity) (by positivity)) (a := 2) (bN := K) (lo := 0)
      le_rfl (fun m _ => Nat.zero_le _)) ?_
  have hset : Finset.Icc 0 (Nat.log 2 (K - 1)) = Finset.range (Nat.log 2 (K - 1) + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  rw [hset]
  exact head_close_min hK hV0 hC0


/-- `K/2 ≤ 2^{log₂ K}`, from `Nat.lt_pow_succ_log_self`.  Private: row A's scaffolding. -/
private lemma two_pow_log_ge {K : ℕ} (_hK : 1 ≤ K) : (K : ℝ) / 2 ≤ (2 : ℝ) ^ (Nat.log 2 K) := by
  have h : K < 2 ^ (Nat.log 2 K + 1) := Nat.lt_pow_succ_log_self (by norm_num) K
  have hR : (K : ℝ) < (2 : ℝ) ^ (Nat.log 2 K + 1) := by exact_mod_cast h
  rw [pow_succ] at hR; linarith

/-- **Row A's block count**: `log₂(N−1) + 1 − log₂K ≤ logb 2 N − logb 2 K + 2`.  Private.

⛔ The `+2` is NOT slack: minimum slack `0.00070` at `(K, N) = (4095, 4097)`, and `+1` is FALSE
there.  BOTH log conversions are needed — forward on `N`, and the reverse
`logb 2 K < log₂K + 1` through `Real.natFloor_logb_natCast` — and so is the empty branch:
`Nat.card_Icc`'s subtraction is truncated, so the cast is `0` while the right side still needs
`logb 2 K ≤ logb 2 N`. -/
private lemma block_count_le {K N : ℕ} (hK : 2 ≤ K) (hN : K ≤ N) :
    ((Nat.log 2 (N - 1) + 1 - Nat.log 2 K : ℕ) : ℝ)
      ≤ Real.logb 2 N - Real.logb 2 K + 2 := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hb : (1 : ℝ) < 2 := by norm_num
  have hKN : Real.logb 2 (K : ℝ) ≤ Real.logb 2 (N : ℝ) :=
    Real.logb_le_logb_of_le hb (by linarith) (by exact_mod_cast hN)
  have hfl : (⌊Real.logb 2 (K : ℝ)⌋₊ : ℕ) = Nat.log 2 K := Real.natFloor_logb_natCast 2 K
  have hlt : Real.logb 2 (K : ℝ) < (Nat.log 2 K : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (Real.logb 2 (K : ℝ)); rwa [hfl] at h
  rcases le_or_gt (Nat.log 2 K) (Nat.log 2 (N - 1) + 1) with hle | hgt
  · have hcast : ((Nat.log 2 (N - 1) + 1 - Nat.log 2 K : ℕ) : ℝ)
        = ((Nat.log 2 (N - 1) : ℕ) : ℝ) + 1 - ((Nat.log 2 K : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hcast]
    have ha : ((Nat.log 2 (N - 1) : ℕ) : ℝ) ≤ Real.logb 2 ((N - 1 : ℕ) : ℝ) :=
      Real.natLog_le_logb (N - 1) 2
    have hb1R : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ N - 1 := by omega
      exact_mod_cast this
    have hb2 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : (N - 1 : ℕ) ≤ N := Nat.sub_le _ _
      exact_mod_cast this
    have hbb : Real.logb 2 ((N - 1 : ℕ) : ℝ) ≤ Real.logb 2 (N : ℝ) :=
      Real.logb_le_logb_of_le hb (by linarith) hb2
    linarith
  · have hz : (Nat.log 2 (N - 1) + 1 - Nat.log 2 K : ℕ) = 0 := by omega
    rw [hz]; push_cast; linarith

/-- **Row A's geometric close**: `∑_{log₂K ≤ j ≤ J} (D·K)(½)^j ≤ 4D`.  Private, and BOUNDED —
no logarithm survives.  The `4` is sharp: `3·D` is false as `K → 2^{m+1} − 1`.

Named `geom_close_lo` because it is the `Icc`-from-`log₂K` form; row F's `geom_close` is the
different, `V`-part sum from `0`. -/
private lemma geom_close_lo {K J : ℕ} (hK : 2 ≤ K) {D : ℝ} (hD : 0 ≤ D) :
    ∑ j ∈ Finset.Icc (Nat.log 2 K) J, (D * (K : ℝ)) * (1 / 2 : ℝ) ^ j ≤ 4 * D := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hc : (0 : ℝ) ≤ D * (K : ℝ) := by positivity
  refine (Salt.Tactic.geom_sum_le_bot_Icc (r := (1 / 2 : ℝ)) (c := D * (K : ℝ)) hc
      (by norm_num) (by norm_num) (Nat.log 2 K) J).trans ?_
  have h2 := two_pow_log_ge (K := K) (by omega)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 K) := by positivity
  have hhalf : (1 / 2 : ℝ) ^ (Nat.log 2 K) = 1 / (2 : ℝ) ^ (Nat.log 2 K) := by
    rw [div_pow]; norm_num
  have key : (K : ℝ) * (1 / 2 : ℝ) ^ (Nat.log 2 K) ≤ 2 := by
    rw [hhalf, mul_one_div, div_le_iff₀ hpos]; linarith
  have hrw : D * (K : ℝ) * (1 / 2 : ℝ) ^ (Nat.log 2 K) / (1 - 1 / 2)
      = 2 * (D * ((K : ℝ) * (1 / 2 : ℝ) ^ (Nat.log 2 K))) := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]; ring
  rw [hrw]
  have := mul_le_mul_of_nonneg_left key hD
  linarith

/-- **R10 row A — the majorant range `K < m ≤ N`.**
`∑_{K < m ≤ N} ‖a_m‖‖S_m‖ ≤ (4/π² + 4V(logb 2 N − logb 2 K + 2)K/π)·C`.

The THIRD instantiation of the machine, at `w m = ‖a_m‖`, `cj j = K/(π²4^j)`, from the cut
`lo = log₂K`.  The `K/m²` arm is the min on every block of THIS range too, and here the reason
is the cut: `4^j ≥ 4^{log₂K} > K²/4`, by a factor `≥ 4.93` at `K = 2`.  Without `lo ≤ j` the
domination is genuinely false (at `K = 100`, `j = 0`).

The `V`-free half is BOUNDED — `geom_close_lo` gives `4C/π²` with no logarithm — and the `V`
half carries the block count, which is HB's dyadic log. -/
theorem majorant_rangeA_le [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    {K N : ℕ} (hK : 2 ≤ K) (hN : K ≤ N) :
    ∑ m ∈ Finset.Ioc K N, ‖majorantCoeff K (m : ℤ)‖
          * ‖lem10ExpSum k q b (Finset.Ioc A B) m
              (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (4 / Real.pi ^ 2
          + 4 * V * (Real.logb 2 N - Real.logb 2 K + 2) * (K : ℝ) / Real.pi)
        * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
            * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k) := by
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hV0 : (0 : ℝ) ≤ V := le_trans (Finset.sum_nonneg (fun n _ => abs_nonneg _)) hvar
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hEk : (0 : ℝ) ≤ E + (k : ℝ) := by positivity
  have hC0 : (0 : ℝ) ≤ 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
      * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k := by
    positivity
  -- (i) `Ioc K N = Icc (K+1) N` is not defeq
  have hset : Finset.Ioc K N = Finset.Icc (K + 1) N := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  -- (ii) the machine, in the CUT form, from `lo = log₂K`
  rw [hset]
  refine le_trans (weighted_dyadic_block_sum_le hk hq hqk b A B hAB hE hlen g hvar c hc
      (fun m => ‖majorantCoeff K ((m : ℕ) : ℤ)‖) (fun j => (K : ℝ) / (Real.pi ^ 2 * 4 ^ j))
      (hcj_sq hK) (fun j => by positivity) (a := K + 1) (bN := N) (lo := Nat.log 2 K)
      (by omega) (fun m hm => by
        rw [Finset.mem_Icc] at hm; exact Nat.log_mono_right (by omega))) ?_
  -- (iii) the per-block identity `B j = (DK/π²)(½)^j + 4VDK/π`
  have hid : ∀ (D : ℝ) (j : ℕ),
      ((K : ℝ) / (Real.pi ^ 2 * 4 ^ j))
          * ((1 + 4 * Real.pi * ((2 ^ j : ℕ) : ℝ) * V) * D * ((2 ^ j : ℕ) : ℝ))
        = (D / Real.pi ^ 2 * (K : ℝ)) * (1 / 2 : ℝ) ^ j + 4 * V * D * (K : ℝ) / Real.pi := by
    intro D j
    have h2c : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
    have h4 : (4 : ℝ) ^ j = (2 : ℝ) ^ j * (2 : ℝ) ^ j := by rw [← mul_pow]; norm_num
    have hhalf : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j := by rw [div_pow]; norm_num
    have h2ne : ((2 : ℝ) ^ j) ≠ 0 := by positivity
    rw [h2c, h4, hhalf]
    field_simp
    try ring
  rw [Finset.sum_congr rfl (fun j _ => hid _ j), Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul]
  -- (iv) the two closes
  have hgeo := geom_close_lo (K := K) (J := Nat.log 2 (N - 1)) hK
      (D := (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
        * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k)
        / Real.pi ^ 2) (div_nonneg hC0 (by positivity))
  have hcnt := block_count_le hK hN
  have hcoef : (0 : ℝ) ≤ 4 * V * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
      * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2)
      * (E + k) / Real.sqrt k) * (K : ℝ) / Real.pi :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) hC0) (by positivity)) hpi0.le
  have hmul := mul_le_mul_of_nonneg_right hcnt hcoef
  have hfin : ∀ D : ℝ, (4 : ℝ) * (D / Real.pi ^ 2)
      + (Real.logb 2 N - Real.logb 2 K + 2) * (4 * V * D * (K : ℝ) / Real.pi)
      = (4 / Real.pi ^ 2
          + 4 * V * (Real.logb 2 N - Real.logb 2 K + 2) * (K : ℝ) / Real.pi) * D := by
    intro D; field_simp; try ring
  rw [← hfin]
  exact add_le_add hgeo hmul


/-- **R10 row R — the majorant's Fourier coefficients are even in modulus**: `‖a_{−m}‖ = ‖a_m‖`.

The ℤ-fold of the bracket needs this and the corpus did not have it.  ⛔ An ARM will not do:
`‖a_m‖ ≤ arm(|m|)` is an UPPER bound, so `negative half ≤ ∑ arm(m)‖S_m‖` does NOT give
`≤ ∑ ‖a_m‖‖S_m‖` — the inequality runs the wrong way, and the rows that consume the fold are
stated in literal coefficient norms.  Cheap because `intervalIntegral_conj` carries no
integrability hypothesis. -/
theorem norm_majorantCoeff_neg (K : ℕ) (m : ℤ) :
    ‖majorantCoeff K (-m)‖ = ‖majorantCoeff K m‖ := by
  have hstep : majorantCoeff K (-m) = (starRingEnd ℂ) (majorantCoeff K m) := by
    unfold majorantCoeff
    rw [← intervalIntegral.intervalIntegral_conj]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [map_mul, Complex.conj_ofReal, ← e_neg_eq_conj]
    congr 1
    push_cast
    ring
  rw [hstep, RCLike.norm_conj]


/-- The ℕ fold of row S, as an EQUALITY: every index is hit exactly once.  Private.
⛔ `Summable.sum_add_tsum_nat_add` is the PROTECTED form; the root-level
`sum_add_tsum_nat_add` is `ℝ≥0`-valued and will not unify. -/
private lemma tsum_nat_fold (F : ℕ → ℝ) (hF : Summable F) (K N : ℕ) (hK : 2 ≤ K) (hN : K ≤ N) :
    ∑' n : ℕ, F n
      = F 0 + F 1 + (∑ m ∈ Finset.Icc 2 K, F m) + (∑ m ∈ Finset.Ioc K N, F m)
        + ∑' n : ℕ, F (n + N + 1) := by
  have h1 : (∑ i ∈ Finset.range (N + 1), F i) + ∑' i : ℕ, F (i + (N + 1)) = ∑' i, F i :=
    hF.sum_add_tsum_nat_add (N + 1)
  have h2 : ∑' i : ℕ, F (i + (N + 1)) = ∑' n : ℕ, F (n + N + 1) := by
    refine tsum_congr (fun n => ?_); congr 1
  have e1 : (∑ m ∈ Finset.Ioc 0 1, F m) + ∑ m ∈ Finset.Ioc 1 K, F m
      = ∑ m ∈ Finset.Ioc 0 K, F m := Finset.sum_Ioc_consecutive F (by omega) (by omega)
  have e2 : (∑ m ∈ Finset.Ioc 0 K, F m) + ∑ m ∈ Finset.Ioc K N, F m
      = ∑ m ∈ Finset.Ioc 0 N, F m := Finset.sum_Ioc_consecutive F (by omega) hN
  have e3 : ∑ m ∈ Finset.Ioc 0 1, F m = F 1 := by
    have hs : Finset.Ioc 0 1 = ({1} : Finset ℕ) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
    rw [hs, Finset.sum_singleton]
  have e4 : Finset.Ioc 1 K = Finset.Icc 2 K := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hset : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
    ext x; simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_insert]; omega
  have e5 : ∑ i ∈ Finset.range (N + 1), F i = F 0 + ∑ m ∈ Finset.Ioc 0 N, F m := by
    rw [hset, Finset.sum_insert (by simp)]
  rw [e4] at e1
  rw [← h1, h2, e5, ← e2, ← e1, e3]
  ring

/-- The ℤ fold of row S: the negative half is dominated by the positive one, so the whole `tsum`
sits under the `m = 0` term plus TWICE the positive side.  Private.
⛔ `tsum_of_nat_of_neg_add_one` is the tool, not `tsum_nat_add_neg_add_one`: the latter delivers
one `tsum` of PAIRS, coupling `m = 0` with `m = −1`. -/
private lemma tsum_int_fold {f : ℤ → ℝ} (hf : Summable f)
    (hrefl : ∀ n : ℕ, f (-(n + 1)) ≤ f (n + 1)) {K N : ℕ} (hK : 2 ≤ K) (hN : K ≤ N) :
    ∑' m : ℤ, f m
      ≤ f 0 + 2 * (f 1 + (∑ m ∈ Finset.Icc 2 K, f (m : ℤ))
          + (∑ m ∈ Finset.Ioc K N, f (m : ℤ)) + ∑' n : ℕ, f ((n + N + 1 : ℕ) : ℤ)) := by
  have hnat : Summable (fun n : ℕ => f (n : ℤ)) := hf.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := hf.comp_injective (@Int.negSucc.inj)
  have hpos1 : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => f (n : ℤ)) 1).2 hnat
    simpa using h
  have hsplit : ∑' m : ℤ, f m = (∑' n : ℕ, f n) + ∑' n : ℕ, f (-(n + 1)) :=
    tsum_of_nat_of_neg_add_one hnat hneg
  have hle : ∑' n : ℕ, f (-(n + 1)) ≤ ∑' n : ℕ, f ((n : ℤ) + 1) :=
    Summable.tsum_le_tsum hrefl hneg hpos1
  have hB : ∑' m : ℤ, f m ≤ (∑' n : ℕ, f n) + ∑' n : ℕ, f ((n : ℤ) + 1) := by
    rw [hsplit]; linarith
  have hA := tsum_nat_fold (fun n : ℕ => f (n : ℤ)) hnat K N hK hN
  have hzero : ∑' n : ℕ, f (n : ℤ) = f 0 + ∑' n : ℕ, f (((n + 1 : ℕ) : ℤ)) :=
    hnat.tsum_eq_zero_add
  have hs1 : ∑' n : ℕ, f (((n + 1 : ℕ) : ℤ)) = ∑' n : ℕ, f ((n : ℤ) + 1) := by
    refine tsum_congr (fun n => ?_); push_cast; ring_nf
  simp only [Nat.cast_zero, Nat.cast_one] at hA
  rw [hzero, hs1] at hA
  rw [hzero, hs1] at hB
  linarith

/-- **R10 row S — the ℤ-tsum split of the majorant bracket.**  The bracket of
`lem10PsiSum_le_fourier_split` is bounded by its `m = 0` term at the uniform arm of (7.4), plus
TWICE the four positive-`m` pieces the rows above supply.
⛔ The `m = 0` term takes the UNIFORM arm `2(1 + log K)/K`; the `K/m²` arm is FALSE there. -/
theorem majorant_tsum_split [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q))
    {K N : ℕ} (hK : 2 ≤ K) (hN : K ≤ N) :
    ∑' m : ℤ, ‖majorantCoeff K m‖
        * ‖lem10ExpSumZ k q b (Finset.Ioc A B) m
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (2 * (1 + Real.log K) / K) * (2 * E)
        + 2 * (‖majorantCoeff K 1‖
                * ‖lem10ExpSum k q b (Finset.Ioc A B) 1
                    (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
              + (∑ m ∈ Finset.Icc 2 K, ‖majorantCoeff K (m : ℤ)‖
                  * ‖lem10ExpSum k q b (Finset.Ioc A B) m
                      (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖)
              + (∑ m ∈ Finset.Ioc K N, ‖majorantCoeff K (m : ℤ)‖
                  * ‖lem10ExpSum k q b (Finset.Ioc A B) m
                      (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖)
              + ∑' n : ℕ, ‖majorantCoeff K ((n + N + 1 : ℕ) : ℤ)‖
                  * ‖lem10ExpSum k q b (Finset.Ioc A B) (n + N + 1)
                      (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖) := by
  -- (i) summability of the bracket: `majorant_bracket`'s own `have`, re-proved as a hypothesis
  have hsummable : Summable (fun m : ℤ => ‖majorantCoeff K m‖
      * ‖lem10ExpSumZ k q b (Finset.Ioc A B) m
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_norm_majorantCoeff hK).mul_right ((Finset.Ioc A B).card : ℝ))
    exact mul_le_mul_of_nonneg_left (norm_lem10ExpSumZ_le_card k q b _ m _) (norm_nonneg _)
  -- (ii) the reflection, on both factors
  have hmnat : ∀ m : ℕ, ((m : ℤ)).natAbs = m := fun m => by omega
  have hrefl : ∀ n : ℕ, ‖majorantCoeff K (-((n : ℤ) + 1))‖
        * ‖lem10ExpSumZ k q b (Finset.Ioc A B) (-((n : ℤ) + 1))
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ ‖majorantCoeff K ((n : ℤ) + 1)‖
        * ‖lem10ExpSumZ k q b (Finset.Ioc A B) ((n : ℤ) + 1)
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ := by
    intro n
    have hnabs : ((-((n : ℤ) + 1))).natAbs = (((n : ℤ) + 1)).natAbs := by omega
    rw [norm_majorantCoeff_neg K ((n : ℤ) + 1), norm_lem10ExpSumZ, norm_lem10ExpSumZ, hnabs]
  -- (iii) the fold
  refine le_trans (tsum_int_fold hsummable hrefl hK hN) ?_
  -- (iv) the ℤ→ℕ bridge on every positive index
  have hZnat : ∀ m : ℕ, ‖lem10ExpSumZ k q b (Finset.Ioc A B) (m : ℤ)
        (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      = ‖lem10ExpSum k q b (Finset.Ioc A B) m
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ := by
    intro m; rw [norm_lem10ExpSumZ, hmnat m]
  have hZ1 : ‖lem10ExpSumZ k q b (Finset.Ioc A B) 1
        (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      = ‖lem10ExpSum k q b (Finset.Ioc A B) 1
          (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ := by
    rw [norm_lem10ExpSumZ]; norm_num
  simp only [hZnat, hZ1]
  -- (v) T2: the `m = 0` term at the UNIFORM arm
  have hcard : ((Finset.Ioc A B).card : ℝ) ≤ 2 * E := by rw [Int.card_Ioc]; exact hlen
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_trans (by norm_num) hK
  have hlogK : (0 : ℝ) ≤ Real.log K := Real.log_nonneg hKR
  have hT2 : ‖majorantCoeff K 0‖
        * ‖lem10ExpSumZ k q b (Finset.Ioc A B) 0
            (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (2 * (1 + Real.log K) / K) * (2 * E) :=
    mul_le_mul (norm_majorantCoeff_le hK 0)
      (le_trans (norm_lem10ExpSumZ_le_card k q b _ 0 _) hcard) (norm_nonneg _) (by positivity)
  linarith

/-! ## R10 — the p.223 assembly -/

set_option maxHeartbeats 1000000 in
-- the assembly threads nine landed rows through one linear close and then discharges
-- three real-numeral slot inequalities; each is within budget, the aggregate is not
/-- **R10 — HB's Lemma 10 (p.223), assembled from the landed rows of this file.**
The Fourier/majorant split at `K = sealK k` and the cut `N = 2^(log₂ (K·⌈√k⌉₊))`: the `m = 1`
peel, row F on the column, rows P′ · H′ · A · B on the bracket.  The close is three
inequalities of real numerals, one per slot — `V`-free, `V`, `E` — against the frozen `2^13`. -/
theorem hb_lemma10 [NeZero k] (hk : 2 ≤ k) {q : ℕ} (hq : 0 < q) (hqk : q ∣ k)
    (b A B : ℤ) (hAB : A ≤ B) {E : ℝ} (hE : 1 ≤ E) (hlen : ((B - A).toNat : ℝ) ≤ 2 * E)
    (g : ℤ → ℝ) {V : ℝ} (hvar : ∑ n ∈ Finset.Ioc A (B - 1), |g (n + 1) - g n| ≤ V)
    (c : ℤ) (hc : Nat.Coprime c.natAbs (k / q)) :
    |lem10PsiSum k q b (Finset.Ioc A B) (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)|
      ≤ 2 ^ 13 * Real.sqrt ((2 : ℝ) ^ k.factorization 2)
          * (k.divisors.card : ℝ) ^ 3 * Real.log (2 * (k : ℝ)) ^ 3
          * (E / (k : ℝ) ^ ((1 : ℝ) / 4)
             + (1 + (2 + (k : ℝ) ^ ((1 : ℝ) / 4)) * V) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k)
                 / Real.sqrt k) := by
  classical
  -- ═══ the two cut parameters ═══
  set K : ℕ := sealK k with hKdef
  set cc : ℕ := ⌈Real.sqrt (k : ℝ)⌉₊ with hccdef
  set N : ℕ := 2 ^ (Nat.log 2 (K * cc)) with hNdef
  -- ═══ elementary facts about k, K, cc, N ═══
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hK : 2 ≤ K := sealK_ge_two k
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hsqrtk_gt : (1 : ℝ) < Real.sqrt (k : ℝ) := by
    have h := (Real.sqrt_lt_sqrt_iff (le_of_lt zero_lt_one)).2 (show (1:ℝ) < (k:ℝ) by linarith)
    simpa using h
  have hsqrtk_le : Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
    have h : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (le_of_lt hkpos)] at h
  have hcc2 : 2 ≤ cc := by
    have h : 1 < cc := by rw [hccdef]; exact Nat.lt_ceil.2 (by simpa using hsqrtk_gt)
    omega
  have hcck : cc ≤ k := by rw [hccdef]; exact Nat.ceil_le.2 hsqrtk_le
  have hMlt : K * cc < 2 * N := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (K * cc)
    rw [hNdef]
    simpa [Nat.succ_eq_add_one, pow_succ, Nat.mul_comm] using h
  have hNleM : N ≤ K * cc := by
    rw [hNdef]; exact Nat.pow_log_le_self 2 (Nat.mul_ne_zero (by omega) (by omega))
  have hN1 : 1 ≤ N := by rw [hNdef]; exact Nat.one_le_pow _ _ (by norm_num)
  have hKN : K ≤ N := by
    have h1 : 2 * K ≤ K * cc := by
      calc 2 * K = K * 2 := Nat.mul_comm 2 K
        _ ≤ K * cc := Nat.mul_le_mul_left K hcc2
    exact le_of_lt (Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 hMlt))
  -- ═══ the nine landed rows, instantiated at this K and N ═══
  have hsplit := lem10PsiSum_le_fourier_split k q b (Finset.Ioc A B)
      (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k) hK
  rw [head_reindex k q b (Finset.Ioc A B)
      (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k) K] at hsplit
  rw [show Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp)] at hsplit
  simp only [Nat.cast_one, mul_one] at hsplit
  have hm1 : ‖lem10ExpSum k q b (Finset.Ioc A B) 1
        (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖
      ≤ (1 + 4 * Real.pi * V)
          * (16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
              * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k) :=
    le_trans (lem10_m1_bound hk hq hqk b A B hAB hE hlen g hvar c hc) (le_of_eq (by ring))
  have hF := fourier_column_le hk hq hqk b A B hAB hE hlen g hvar c hc hK
  have hS := majorant_tsum_split hk hq hqk b A B hAB hE hlen g hvar c hc hK hKN
  have hP := majorant_m1_le hk hq hqk b A B hAB hE hlen g hvar c hc hK
  have hH := majorant_head_le hk hq hqk b A B hAB hE hlen g hvar c hc hK
  have hA := majorant_rangeA_le hk hq hqk b A B hAB hE hlen g hvar c hc hK hKN
  have hB := majorant_tail_le hk hq hqk b A B hAB hE hlen g hvar c hc hK hN1
  set C : ℝ := 16 * Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3
      * Real.log (2 * (k : ℝ)) * (q : ℝ) ^ ((3 : ℝ) / 2) * (E + k) / Real.sqrt k with hCdef
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi0 : (0 : ℝ) < Real.pi := by linarith
  have hpi2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hV0 : (0 : ℝ) ≤ V := le_trans (Finset.sum_nonneg (fun n _ => abs_nonneg _)) hvar
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hC0 : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  have hm1' : ‖lem10ExpSum k q b (Finset.Ioc A B) 1
        (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)‖ / Real.pi
      ≤ C / Real.pi + 4 * V * C := by
    refine le_trans (div_le_div_of_nonneg_right hm1 (le_of_lt hpi0)) (le_of_eq ?_)
    field_simp
  -- ═══ THE CHAIN: seven terms, no double count and no drop ═══
  have hchain : |lem10PsiSum k q b (Finset.Ioc A B)
        (fun n => g n + (c : ℝ) * (invMod n k : ℝ) / k)|
      ≤ (C / Real.pi + 4 * V * C)
        + ((Real.logb 2 (K : ℝ) + 1) / Real.pi + 8 * (K : ℝ) * V) * C
        + 5 / 2 * (2 * (1 + Real.log (K : ℝ)) / (K : ℝ) * (2 * E)
            + 2 * ((Real.sqrt (2 * (1 + Real.log (K : ℝ))) / Real.pi
                      + 4 * V * (K : ℝ) / Real.pi) * C
                + ((Real.logb 2 (K : ℝ) + 1) * Real.sqrt (2 * (1 + Real.log (K : ℝ))) / Real.pi
                      + 4 * V * (Real.logb 2 (K : ℝ) + 1) * (K : ℝ) / Real.pi) * C
                + (4 / Real.pi ^ 2
                      + 4 * V * (Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2) * (K : ℝ)
                          / Real.pi) * C
                + (K : ℝ) / (Real.pi ^ 2 * (N : ℝ)) * (2 * E))) := by
    linarith [hsplit, hm1', hF, hS, hP, hH, hA, hB]
  have hgroup : (C / Real.pi + 4 * V * C)
        + ((Real.logb 2 (K : ℝ) + 1) / Real.pi + 8 * (K : ℝ) * V) * C
        + 5 / 2 * (2 * (1 + Real.log (K : ℝ)) / (K : ℝ) * (2 * E)
            + 2 * ((Real.sqrt (2 * (1 + Real.log (K : ℝ))) / Real.pi
                      + 4 * V * (K : ℝ) / Real.pi) * C
                + ((Real.logb 2 (K : ℝ) + 1) * Real.sqrt (2 * (1 + Real.log (K : ℝ))) / Real.pi
                      + 4 * V * (Real.logb 2 (K : ℝ) + 1) * (K : ℝ) / Real.pi) * C
                + (4 / Real.pi ^ 2
                      + 4 * V * (Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2) * (K : ℝ)
                          / Real.pi) * C
                + (K : ℝ) / (Real.pi ^ 2 * (N : ℝ)) * (2 * E)))
      = (1 / Real.pi + (Real.logb 2 (K : ℝ) + 1) / Real.pi
          + 5 * (Real.sqrt (2 * (1 + Real.log (K : ℝ))) / Real.pi
              + (Real.logb 2 (K : ℝ) + 1) * Real.sqrt (2 * (1 + Real.log (K : ℝ))) / Real.pi
              + 4 / Real.pi ^ 2)) * C
        + (4 + 8 * (K : ℝ)
            + 5 * (4 * (K : ℝ) / Real.pi + 4 * (Real.logb 2 (K : ℝ) + 1) * (K : ℝ) / Real.pi
                + 4 * (Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2) * (K : ℝ) / Real.pi))
            * (V * C)
        + (10 * (1 + Real.log (K : ℝ)) / (K : ℝ)
            + 10 * (K : ℝ) / (Real.pi ^ 2 * (N : ℝ))) * E := by
    ring
  rw [hgroup] at hchain
  refine le_trans hchain ?_
  -- ═══ THE NUMERIC CLOSE, slot by slot, on the crude route ═══
  clear hchain hgroup hsplit hS hB hm1 hm1' hF hP hH hA
  set L : ℝ := Real.log (2 * (k : ℝ)) with hLdef
  set kq : ℝ := (k : ℝ) ^ ((1 : ℝ) / 4) with hkqdef
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2 : (0 : ℝ) < Real.log 2 := by linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL4 : Real.log 4 ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith)
  have hLlo : (13862 / 10000 : ℝ) ≤ L := by rw [hlog4] at hL4; linarith
  have hL0' : (0 : ℝ) ≤ L := by linarith
  have hLL2 : (13862 / 10000 : ℝ) * L ≤ L ^ 2 := by nlinarith only [hLlo, hL0']
  have hL1 : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hLlo, hL0']
  have hL3 : (19215 / 10000 : ℝ) * L ≤ L ^ 3 := by nlinarith only [hLlo, hL0', hLL2]
  -- the two `K` envelopes, in base 2 where the rows emit them
  have ht : 1 + Real.log (K : ℝ) ≤ 206 / 100 * L := t4_log_sealK_le k hk
  have hlogK0 : (0 : ℝ) ≤ Real.log (K : ℝ) := Real.log_nonneg (by linarith)
  have hmulL : L * (0.6931471803 : ℝ) ≤ L * Real.log 2 :=
    mul_le_mul_of_nonneg_left (le_of_lt hlog2) hL0'
  have hlbu : Real.logb 2 (K : ℝ) * Real.log 2 = Real.log (K : ℝ) := by
    rw [← Real.log_div_log]; field_simp
  have hlb : Real.logb 2 (K : ℝ) + 1 ≤ 298 / 100 * L := by
    refine le_of_mul_le_mul_right ?_ hl2
    nlinarith only [hlbu, ht, hlog2', hmulL, hL0']
  have hlb0 : (0 : ℝ) ≤ Real.logb 2 (K : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ Real.logb 2 (K : ℝ) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    linarith
  -- the `N` envelope: `N ≤ K·⌈√k⌉₊` and `⌈√k⌉₊ ≤ k`
  have hNR0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hccR : (0 : ℝ) < (cc : ℝ) := by exact_mod_cast (show 0 < cc by omega)
  have hlnub : Real.logb 2 (N : ℝ) ≤ Real.logb 2 (K : ℝ) + Real.logb 2 (cc : ℝ) := by
    have h1 : (N : ℝ) ≤ (K : ℝ) * (cc : ℝ) := by exact_mod_cast hNleM
    have h2 : Real.logb 2 (N : ℝ) ≤ Real.logb 2 ((K : ℝ) * (cc : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) hNR0 h1
    rwa [Real.logb_mul (ne_of_gt hKpos) (ne_of_gt hccR)] at h2
  have hccu : Real.logb 2 (cc : ℝ) * Real.log 2 = Real.log (cc : ℝ) := by
    rw [← Real.log_div_log]; field_simp
  have hlogcc : Real.log (cc : ℝ) ≤ L := by
    rw [hLdef]
    refine Real.log_le_log hccR ?_
    have h : (cc : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcck
    linarith
  have hlbn : Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2 ≤ 289 / 100 * L := by
    have hstep : Real.logb 2 (cc : ℝ) + 2 ≤ 289 / 100 * L := by
      refine le_of_mul_le_mul_right ?_ hl2
      nlinarith only [hccu, hlogcc, hL4, hlog4, hmulL, hL0']
    linarith
  have hlbn0 : (0 : ℝ) ≤ Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2 := by
    have h : Real.logb 2 (K : ℝ) ≤ Real.logb 2 (N : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) hKpos (by exact_mod_cast hKN)
    linarith
  -- `π > 3`, spent as `x/π ≤ x/3` on every nonnegative numerator
  have hinvpi : ∀ x : ℝ, 0 ≤ x → x / Real.pi ≤ x / 3 := by
    intro x hx
    rw [div_le_div_iff₀ hpi0 (by norm_num : (0 : ℝ) < 3)]
    nlinarith only [hx, hpi]
  have hinvpi2 : (4 : ℝ) / Real.pi ^ 2 ≤ 4 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 9)]
    nlinarith only [hpi2]
  -- ── THE C-SLOT, in units of `C`: `Θ(L^{3/2})` demand against `512 L²` ──
  have hs0 : (0 : ℝ) ≤ Real.sqrt (2 * (1 + Real.log (K : ℝ))) := Real.sqrt_nonneg _
  have hs : Real.sqrt (2 * (1 + Real.log (K : ℝ))) ≤ 29134 / 10000 * L := by
    have h1 : 2 * (1 + Real.log (K : ℝ)) ≤ (29134 / 10000 * L) ^ 2 := by
      nlinarith only [ht, hLL2, hL0', hLlo]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 29134 / 10000 * L)] at h2
  have hprod : (Real.logb 2 (K : ℝ) + 1) * Real.sqrt (2 * (1 + Real.log (K : ℝ)))
      ≤ (298 / 100 * L) * (29134 / 10000 * L) :=
    mul_le_mul hlb hs hs0 (by linarith : (0 : ℝ) ≤ 298 / 100 * L)
  have hslotC : 1 / Real.pi + (Real.logb 2 (K : ℝ) + 1) / Real.pi
      + 5 * (Real.sqrt (2 * (1 + Real.log (K : ℝ))) / Real.pi
          + (Real.logb 2 (K : ℝ) + 1) * Real.sqrt (2 * (1 + Real.log (K : ℝ))) / Real.pi
          + 4 / Real.pi ^ 2) ≤ 512 * L ^ 2 := by
    have e1 := hinvpi 1 (by norm_num)
    have e2 := hinvpi (Real.logb 2 (K : ℝ) + 1) hlb0
    have e3 := hinvpi (Real.sqrt (2 * (1 + Real.log (K : ℝ)))) hs0
    have e4 := hinvpi ((Real.logb 2 (K : ℝ) + 1) * Real.sqrt (2 * (1 + Real.log (K : ℝ))))
      (mul_nonneg hlb0 hs0)
    linarith only [e1, e2, e3, e4, hinvpi2, hlb, hs, hprod, hLL2, hL1]
  -- ── THE V-SLOT, in units of `V·C`: the budget carries `K ≤ 2 + k^{1/4}` ──
  have hKkq : (K : ℝ) ≤ 2 + kq := sealK_le k
  have hslotV : 4 + 8 * (K : ℝ)
      + 5 * (4 * (K : ℝ) / Real.pi + 4 * (Real.logb 2 (K : ℝ) + 1) * (K : ℝ) / Real.pi
          + 4 * (Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2) * (K : ℝ) / Real.pi)
      ≤ 512 * L ^ 2 * (2 + kq) := by
    have e5 := hinvpi (4 * (K : ℝ)) (by linarith)
    have e6 := hinvpi (4 * (Real.logb 2 (K : ℝ) + 1) * (K : ℝ))
      (mul_nonneg (by linarith) (le_of_lt hKpos))
    have e7 := hinvpi (4 * (Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2) * (K : ℝ))
      (mul_nonneg (by linarith) (le_of_lt hKpos))
    have p6 : (Real.logb 2 (K : ℝ) + 1) * (K : ℝ) ≤ (298 / 100 * L) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right hlb (le_of_lt hKpos)
    have p7 : (Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2) * (K : ℝ)
        ≤ (289 / 100 * L) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right hlbn (le_of_lt hKpos)
    have hnum : (16667 / 1000 : ℝ) + 39134 / 1000 * L ≤ 512 * L ^ 2 := by
      nlinarith only [hLL2, hLlo, hL1]
    have hstep : 4 + 8 * (K : ℝ)
        + 5 * (4 * (K : ℝ) / Real.pi + 4 * (Real.logb 2 (K : ℝ) + 1) * (K : ℝ) / Real.pi
            + 4 * (Real.logb 2 (N : ℝ) - Real.logb 2 (K : ℝ) + 2) * (K : ℝ) / Real.pi)
        ≤ (K : ℝ) * (16667 / 1000 + 39134 / 1000 * L) := by
      have hLK : (0 : ℝ) ≤ L * (K : ℝ) := mul_nonneg hL0' (le_of_lt hKpos)
      linarith only [e5, e6, e7, p6, p7, hKR, hLK]
    have hfin : (K : ℝ) * (16667 / 1000 + 39134 / 1000 * L) ≤ (K : ℝ) * (512 * L ^ 2) :=
      mul_le_mul_of_nonneg_left hnum (le_of_lt hKpos)
    have hfin2 : (K : ℝ) * (512 * L ^ 2) ≤ (2 + kq) * (512 * L ^ 2) :=
      mul_le_mul_of_nonneg_right hKkq (by positivity)
    linarith only [hstep, hfin, hfin2]
  -- ── THE E-SLOT, in units of `E`: `K ≥ k^{1/4}` and `N > K·√k/2` ──
  have hkq0 : (0 : ℝ) < kq := by rw [hkqdef]; exact Real.rpow_pos_of_pos hkpos _
  have hkq1 : (1 : ℝ) ≤ kq := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ (k : ℝ))
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
    rwa [Real.one_rpow] at h
  have hkqK : kq ≤ (K : ℝ) := sealK_ge_rpow k
  have hkqsq : kq ^ 2 = Real.sqrt (k : ℝ) := by
    rw [hkqdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((k : ℝ) ^ ((1 : ℝ) / 4)) 2,
      ← Real.rpow_mul (le_of_lt hkpos)]
    norm_num
  have hkqs : kq ≤ Real.sqrt (k : ℝ) := by nlinarith only [hkq1, hkqsq]
  have hccge : Real.sqrt (k : ℝ) ≤ (cc : ℝ) := by rw [hccdef]; exact Nat.le_ceil _
  have hMltR : (K : ℝ) * (cc : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hMlt
  have hKsq : (K : ℝ) * Real.sqrt (k : ℝ) ≤ 2 * (N : ℝ) := by
    nlinarith only [hccge, hMltR, hKpos]
  have hd0 : 1 ≤ k.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  have hdR : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by exact_mod_cast hd0
  have h2v : (1 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ k.factorization 2) := by
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ (k.factorization 2) := one_le_pow₀ (by norm_num)
    have h2 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_one] at h2
  have hd3 : (1 : ℝ) ≤ (k.divisors.card : ℝ) ^ 3 := one_le_pow₀ hdR
  have hD1 : (1 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3 := by
    nlinarith only [h2v, hd3]
  have hslotE : 10 * (1 + Real.log (K : ℝ)) / (K : ℝ)
        + 10 * (K : ℝ) / (Real.pi ^ 2 * (N : ℝ))
      ≤ 8192 * (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3)
          * L ^ 3 / kq := by
    have hE1 : 10 * (1 + Real.log (K : ℝ)) / (K : ℝ) ≤ (206 / 10 * L) / kq := by
      rw [div_le_div_iff₀ hKpos hkq0]
      nlinarith only [mul_le_mul_of_nonneg_right ht (le_of_lt hkq0),
        mul_le_mul_of_nonneg_left hkqK (by linarith : (0 : ℝ) ≤ 206 / 100 * L)]
    have hE2 : 10 * (K : ℝ) / (Real.pi ^ 2 * (N : ℝ)) ≤ (20 / 9 : ℝ) / kq := by
      rw [div_le_div_iff₀ (by positivity) hkq0]
      nlinarith only [mul_le_mul_of_nonneg_left hkqs (le_of_lt hKpos), hKsq,
        mul_le_mul_of_nonneg_right (le_of_lt hpi2) (le_of_lt hNR0)]
    have hnumE : 206 / 10 * L + 20 / 9
        ≤ 8192 * (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3)
            * L ^ 3 := by
      nlinarith only [hD1, hL3, hLlo, hL0',
        mul_nonneg (sub_nonneg.2 hD1) (by positivity : (0 : ℝ) ≤ 8192 * L ^ 3)]
    have hE3 : (206 / 10 * L) / kq + (20 / 9 : ℝ) / kq
        ≤ 8192 * (Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) ^ 3)
            * L ^ 3 / kq := by
      have hcomb : (206 / 10 * L) / kq + (20 / 9 : ℝ) / kq = (206 / 10 * L + 20 / 9) / kq := by
        ring
      rw [hcomb, div_le_div_iff₀ hkq0 hkq0]
      exact mul_le_mul_of_nonneg_right hnumE (le_of_lt hkq0)
    linarith only [hE1, hE2, hE3]
  -- ── the three slots against `2^13`, and the budget written out ──
  have hVC0 : (0 : ℝ) ≤ V * C := mul_nonneg hV0 hC0
  refine le_trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hslotC hC0)
      (mul_le_mul_of_nonneg_right hslotV hVC0))
      (mul_le_mul_of_nonneg_right hslotE hE0)) (le_of_eq ?_)
  rw [hCdef]
  have h1 : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hkpos)
  have h2 : kq ≠ 0 := ne_of_gt hkq0
  field_simp
  ring

end Salt.N7
