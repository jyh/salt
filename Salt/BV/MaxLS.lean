/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.CharLS

/-!
# V3.0 — the maximal large sieve (`Salt/BV/MaxLS.lean`)

Design: `docs/blueprints/bv.md`, node `V3.0`. The mechanism that threads the
inner maximum `max_{y ≤ N} ‖∑_{n < y} cₙ·χ(n)‖²` through the character large
sieve `char_LS` (`Salt/LS/CharLS.lean`), paying a single squared-polylog factor.

## The route (dyadic-in-`y` subdivision)

For a coefficient sequence `c` and a character `χ` mod `q`, the deliverable
`char_LS_max` bounds the `(q/φq)`-weighted sum over primitive `χ` of the
*maximal* prefix energy by `(1 + log₂ N)²·(Q² + 13N)·∑‖cₙ‖²`.

1. **`blockCoeff` / dyadic blocks.** `blockCoeff c j k` restricts `c` to the
   dyadic block `Ico (2ʲ·k) (2ʲ·(k+1))`. `block_sum_eq` identifies its
   `range N` character sum with the plain block sum (blocks inside `[0,N)`).

2. **`interval_decomp` (the genuine work).** By induction on the level `m`,
   any interval `Ico a b` with `2ᵐ ∣ a` and length `< 2ᵐ` decomposes, using at
   most one block per level, into `≤ m` dyadic blocks:
   `‖∑_{Ico a b} cₙ·χ(n)‖ ≤ ∑_{j < m} sup'_k ‖σ_{j,k}(χ)‖`, where
   `σ_{j,k}(χ) = ∑_{n < N} blockCoeff c j k n · χ(n)`. Applied at
   `m = ⌊log₂ N⌋ + 1`, `a = 0`, `b = y` (any `y ≤ N < 2^{⌊log₂N⌋+1}`), it
   bounds every prefix.

3. **Cauchy–Schwarz + `char_LS` per level.** Squaring and Cauchy–Schwarz over
   the `≤ L+1` levels (`sq_sum_le_card_mul_sum_sq`), then `sup'_k ≤ ∑_k`
   (terms `≥ 0`), makes the `y`-max bound `y`-independent. The dyadic blocks at
   a fixed level are disjoint and cover `[0,N)`, so `char_LS` applied to each
   `blockCoeff c j k` and summed (`sum_blockCoeff_normSq`) recovers `∑‖cₙ‖²`
   per level. Total: `(L+1)²·(Q²+13N)·∑‖cₙ‖²`, with `L+1 ≤ 1 + log₂ N`
   (`Real.natLog_le_logb`).

Only `[propext, Classical.choice, Quot.sound]` are used (via `char_LS`).
-/

namespace Salt.BV

open Finset Salt.LS

/-- Coefficient sequence `c` restricted to the dyadic block `Ico (2ʲ·k)
(2ʲ·(k+1))`; zero elsewhere. The block character sums `σ_{j,k}(χ)` are the
`range N` sums of `blockCoeff c j k · χ`. -/
def blockCoeff (c : ℕ → ℂ) (j k : ℕ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ico (2 ^ j * k) (2 ^ j * (k + 1)) then c n else 0

/-- The `range N` character sum of `blockCoeff c j k` equals the plain block
character sum, provided the block sits inside `[0, N)`. -/
theorem block_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (c : ℕ → ℂ) (N j k : ℕ)
    (hsub : 2 ^ j * (k + 1) ≤ N) :
    ∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)
      = ∑ n ∈ Finset.Ico (2 ^ j * k) (2 ^ j * (k + 1)), c n * χ (n : ZMod q) := by
  have hblk_sub : Finset.Ico (2 ^ j * k) (2 ^ j * (k + 1)) ⊆ Finset.range N := by
    intro n hn
    rw [Finset.mem_range]
    have := (Finset.mem_Ico.mp hn).2
    omega
  calc ∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)
      = ∑ n ∈ Finset.range N,
          (if n ∈ Finset.Ico (2 ^ j * k) (2 ^ j * (k + 1)) then c n * χ (n : ZMod q) else 0) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [blockCoeff, ite_mul, zero_mul]
    _ = ∑ n ∈ Finset.range N ∩ Finset.Ico (2 ^ j * k) (2 ^ j * (k + 1)), c n * χ (n : ZMod q) :=
        Finset.sum_ite_mem _ _ _
    _ = ∑ n ∈ Finset.Ico (2 ^ j * k) (2 ^ j * (k + 1)), c n * χ (n : ZMod q) := by
        rw [Finset.inter_eq_right.mpr hblk_sub]

/-- A single dyadic block `Ico a (a + 2ᵐ)` (with `2ᵐ ∣ a` and the block inside
`[0, N)`) has character-sum norm bounded by the level-`m` supremum. -/
theorem single_block_le {q : ℕ} (χ : DirichletCharacter ℂ q) (c : ℕ → ℂ)
    (N : ℕ) (hNne : (Finset.range N).Nonempty) (m a : ℕ)
    (hdvd : 2 ^ m ∣ a) (hbound : a + 2 ^ m ≤ N) :
    ‖∑ n ∈ Finset.Ico a (a + 2 ^ m), c n * χ (n : ZMod q)‖ ≤
      (Finset.range N).sup' hNne
        (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c m k n * χ (n : ZMod q)‖) := by
  obtain ⟨k, hk⟩ := hdvd
  have hb2 : a + 2 ^ m = 2 ^ m * (k + 1) := by
    calc a + 2 ^ m = 2 ^ m * k + 2 ^ m := by rw [hk]
      _ = 2 ^ m * (k + 1) := by ring
  have hIco : Finset.Ico a (a + 2 ^ m) = Finset.Ico (2 ^ m * k) (2 ^ m * (k + 1)) := by
    rw [hb2, hk]
  have hsub : 2 ^ m * (k + 1) ≤ N := by rw [← hb2]; exact hbound
  have hkN : k ∈ Finset.range N := by
    rw [Finset.mem_range]
    have h1 : (0 : ℕ) < 2 ^ m := pow_pos (by norm_num) m
    have h2 : k + 1 ≤ 2 ^ m * (k + 1) := Nat.le_mul_of_pos_left (k + 1) h1
    omega
  rw [hIco, ← block_sum_eq χ c N m k hsub]
  exact Finset.le_sup'
    (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c m k n * χ (n : ZMod q)‖) hkN

/-- **The dyadic decomposition (the genuine work).** By induction on the level
`m`: any interval `Ico a b` with `2ᵐ ∣ a`, `a ≤ b`, length `b - a < 2ᵐ`, and
`b ≤ N` decomposes—using at most one dyadic block per level—into `≤ m` blocks,
so its character-sum norm is bounded by the sum over levels `j < m` of the
level-`j` supremum `sup'_k ‖σ_{j,k}(χ)‖`. -/
theorem interval_decomp {q : ℕ} (χ : DirichletCharacter ℂ q) (c : ℕ → ℂ)
    (N : ℕ) (hNne : (Finset.range N).Nonempty) (m : ℕ) :
    ∀ a b : ℕ, 2 ^ m ∣ a → a ≤ b → b < a + 2 ^ m → b ≤ N →
      ‖∑ n ∈ Finset.Ico a b, c n * χ (n : ZMod q)‖ ≤
        ∑ j ∈ Finset.range m, (Finset.range N).sup' hNne
          (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖) := by
  have hsup_nonneg : ∀ j : ℕ, 0 ≤ (Finset.range N).sup' hNne
      (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖) := by
    intro j
    obtain ⟨w, hw⟩ := hNne
    exact le_trans (norm_nonneg _)
      (Finset.le_sup' (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖) hw)
  induction m with
  | zero =>
    intro a b _ hab hb _
    have hba : b = a := by simp only [pow_zero] at hb; omega
    subst hba
    simp
  | succ m ih =>
    intro a b hdvd hab hb hbN
    have hdvd_m : 2 ^ m ∣ a := dvd_trans (pow_dvd_pow 2 (Nat.le_succ m)) hdvd
    by_cases hbc : b ≤ a + 2 ^ m
    · by_cases hbc2 : b < a + 2 ^ m
      · refine le_trans (ih a b hdvd_m hab hbc2 hbN) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (Nat.le_succ m)) ?_
        intro j _ _
        exact hsup_nonneg j
      · have hbeq : b = a + 2 ^ m := by omega
        subst hbeq
        refine le_trans (single_block_le χ c N hNne m a hdvd_m hbN) ?_
        exact Finset.single_le_sum (fun j _ => hsup_nonneg j)
          (Finset.mem_range.mpr (Nat.lt_succ_self m))
    · have hle1 : a ≤ a + 2 ^ m := Nat.le_add_right a _
      have hle2 : a + 2 ^ m ≤ b := by omega
      rw [← Finset.sum_Ico_consecutive (fun n => c n * χ (n : ZMod q)) hle1 hle2]
      refine le_trans (norm_add_le _ _) ?_
      have hblk : ‖∑ n ∈ Finset.Ico a (a + 2 ^ m), c n * χ (n : ZMod q)‖
          ≤ (Finset.range N).sup' hNne
              (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c m k n * χ (n : ZMod q)‖) :=
        single_block_le χ c N hNne m a hdvd_m (by omega)
      have hdvd_m' : 2 ^ m ∣ (a + 2 ^ m) := dvd_add hdvd_m (dvd_refl _)
      have hrest : ‖∑ n ∈ Finset.Ico (a + 2 ^ m) b, c n * χ (n : ZMod q)‖
          ≤ ∑ j ∈ Finset.range m, (Finset.range N).sup' hNne
              (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖) :=
        ih (a + 2 ^ m) b hdvd_m' hle2 (by rw [pow_succ] at hb; omega) hbN
      calc ‖∑ n ∈ Finset.Ico a (a + 2 ^ m), c n * χ (n : ZMod q)‖
            + ‖∑ n ∈ Finset.Ico (a + 2 ^ m) b, c n * χ (n : ZMod q)‖
          ≤ (Finset.range N).sup' hNne
              (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c m k n * χ (n : ZMod q)‖)
            + ∑ j ∈ Finset.range m, (Finset.range N).sup' hNne
                (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖) :=
            add_le_add hblk hrest
        _ = ∑ j ∈ Finset.range (m + 1), (Finset.range N).sup' hNne
              (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖) := by
            rw [Finset.sum_range_succ]; ring

/-- **Per-level coverage.** At a fixed level `j`, the dyadic blocks
`Ico (2ʲ·k) (2ʲ·(k+1))` for `k < N` are disjoint and cover `[0,N)`, so summing
`‖blockCoeff c j k n‖²` over `k` and `n` recovers `∑_{n < N} ‖cₙ‖²`. -/
theorem sum_blockCoeff_normSq (c : ℕ → ℂ) (N j : ℕ) :
    ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range N, ‖blockCoeff c j k n‖ ^ 2
      = ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  have hpow : (0 : ℕ) < 2 ^ j := pow_pos (by norm_num) j
  have key : ∀ k, ‖blockCoeff c j k n‖ ^ 2
      = if n ∈ Finset.Ico (2 ^ j * k) (2 ^ j * (k + 1)) then ‖c n‖ ^ 2 else 0 := by
    intro k
    simp only [blockCoeff]
    split_ifs <;> simp
  have hmem_main : n ∈ Finset.Ico (2 ^ j * (n / 2 ^ j)) (2 ^ j * (n / 2 ^ j + 1)) := by
    rw [Finset.mem_Ico]
    refine ⟨?_, ?_⟩
    · have := Nat.div_add_mod n (2 ^ j); omega
    · have h1 := Nat.div_add_mod n (2 ^ j)
      have h2 : n % 2 ^ j < 2 ^ j := Nat.mod_lt n hpow
      have h3 : 2 ^ j * (n / 2 ^ j + 1) = 2 ^ j * (n / 2 ^ j) + 2 ^ j := by ring
      omega
  simp_rw [key]
  rw [Finset.sum_eq_single (n / 2 ^ j)]
  · rw [if_pos hmem_main]
  · intro k _ hk
    rw [if_neg]
    intro hmem
    rw [Finset.mem_Ico] at hmem
    exact hk (Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hmem.1)
      (by rw [Nat.mul_comm]; exact hmem.2)).symm
  · intro hk
    exact absurd (Finset.mem_range.mpr (lt_of_le_of_lt (Nat.div_le_self n (2 ^ j)) hn)) hk

open Classical in
/-- **V3.0 — the maximal large sieve.** For `2 ≤ Q` and any coefficient
sequence `c : ℕ → ℂ`, the `(q/φq)`-weighted sum over primitive characters of the
*maximal* prefix energy `max_{y ≤ N} ‖∑_{n < y} cₙ·χ(n)‖²` obeys
```
∑ q ∈ Icc 1 Q, (q/φq) · ∑ χ prim, max_{y ≤ N} ‖∑_{n < y} cₙ·χ(n)‖²
  ≤ (1 + log₂ N)² · (Q² + 13N) · ∑_{n < N} ‖cₙ‖².
```
The inner max is packaged as `Finset.sup'` over `Icc 0 N` (the `y = 0` term is
`0`). Proof: the dyadic-in-`y` subdivision `interval_decomp` lifts the fixed-`N`
`char_LS` to maximal form at the cost of a squared factor `(L+1)²`,
`L = ⌊log₂ N⌋`. -/
theorem char_LS_max {N Q : ℕ} (hQ : 2 ≤ Q) (c : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          (Finset.Icc 0 N).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le N))
            (fun y => ‖∑ n ∈ Finset.range y, c n * χ (n : ZMod q)‖ ^ 2)
      ≤ (1 + Real.logb 2 N) ^ 2 * ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  · have hN1 : 1 ≤ N := hNpos
    set L := Nat.log 2 N with hL
    have hN_lt : N < 2 ^ (L + 1) := by rw [hL]; exact Nat.lt_pow_succ_log_self (by norm_num) N
    have hNne : (Finset.range N).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
    set P := Finset.range (L + 1) ×ˢ Finset.range N with hPdef
    -- Per (q, χ): the maximal prefix energy is bounded by (L+1)·(level energies).
    have main_bound : ∀ q ∈ Finset.Icc 1 Q, ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        (Finset.Icc 0 N).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le N))
            (fun y => ‖∑ n ∈ Finset.range y, c n * χ (n : ZMod q)‖ ^ 2)
          ≤ (↑(L + 1) : ℝ) *
              ∑ p ∈ P, ‖∑ n ∈ Finset.range N, blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2 := by
      intro q _ χ _
      refine Finset.sup'_le _ _ (fun y hy => ?_)
      rw [Finset.mem_Icc] at hy
      have hyN : y ≤ N := hy.2
      have hle : ‖∑ n ∈ Finset.range y, c n * χ (n : ZMod q)‖
          ≤ ∑ j ∈ Finset.range (L + 1), (Finset.range N).sup' hNne
              (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖) := by
        rw [Finset.range_eq_Ico]
        exact interval_decomp χ c N hNne (L + 1) 0 y (dvd_zero _) (Nat.zero_le y)
          (by rw [zero_add]; exact lt_of_le_of_lt hyN hN_lt) hyN
      calc ‖∑ n ∈ Finset.range y, c n * χ (n : ZMod q)‖ ^ 2
          ≤ (∑ j ∈ Finset.range (L + 1), (Finset.range N).sup' hNne
              (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
        _ ≤ (↑(Finset.range (L + 1)).card : ℝ) *
              ∑ j ∈ Finset.range (L + 1),
                ((Finset.range N).sup' hNne
                  (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖)) ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ = (↑(L + 1) : ℝ) *
              ∑ j ∈ Finset.range (L + 1),
                ((Finset.range N).sup' hNne
                  (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖)) ^ 2 := by
            rw [Finset.card_range]
        _ ≤ (↑(L + 1) : ℝ) *
              ∑ j ∈ Finset.range (L + 1), ∑ k ∈ Finset.range N,
                ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖ ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum fun j _ => ?_
            obtain ⟨k₀, hk₀mem, hk₀eq⟩ := Finset.exists_mem_eq_sup' hNne
              (fun k => ‖∑ n ∈ Finset.range N, blockCoeff c j k n * χ (n : ZMod q)‖)
            rw [hk₀eq]
            exact Finset.single_le_sum
              (fun k _ => sq_nonneg ‖∑ n ∈ Finset.range N,
                blockCoeff c j k n * χ (n : ZMod q)‖) hk₀mem
        _ = (↑(L + 1) : ℝ) *
              ∑ p ∈ P, ‖∑ n ∈ Finset.range N, blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2 := by
            rw [hPdef]
            congr 1
            exact (Finset.sum_product' (Finset.range (L + 1)) (Finset.range N)
              (fun i k => ‖∑ n ∈ Finset.range N,
                blockCoeff c i k n * χ (n : ZMod q)‖ ^ 2)).symm
    -- Assemble over q, χ and swap the level sum outside to apply char_LS per level.
    calc ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              (Finset.Icc 0 N).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le N))
                (fun y => ‖∑ n ∈ Finset.range y, c n * χ (n : ZMod q)‖ ^ 2)
        ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ((↑(L + 1) : ℝ) *
                ∑ p ∈ P, ‖∑ n ∈ Finset.range N, blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2) := by
          refine Finset.sum_le_sum fun q hq => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum fun χ hχ => ?_
          exact main_bound q hq χ (Finset.mem_filter.mp hχ).2
      _ = (↑(L + 1) : ℝ) * ∑ p ∈ P,
            ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
                ‖∑ n ∈ Finset.range N, blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2 := by
          calc ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
                    ((↑(L + 1) : ℝ) *
                      ∑ p ∈ P, ‖∑ n ∈ Finset.range N,
                        blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2)
              = ∑ q ∈ Finset.Icc 1 Q, (↑(L + 1) : ℝ) * (((q : ℝ) / (q.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
                    ∑ p ∈ P, ‖∑ n ∈ Finset.range N,
                      blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                rw [← Finset.mul_sum]; ring
            _ = (↑(L + 1) : ℝ) * ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
                  ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
                    ∑ p ∈ P, ‖∑ n ∈ Finset.range N,
                      blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2 := by
                rw [Finset.mul_sum]
            _ = (↑(L + 1) : ℝ) * ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
                  ∑ p ∈ P, ∑ χ ∈ Finset.univ.filter
                      (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
                    ‖∑ n ∈ Finset.range N, blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2 := by
                refine congrArg (fun x => (↑(L + 1) : ℝ) * x) (Finset.sum_congr rfl fun q _ => ?_)
                rw [Finset.sum_comm]
            _ = (↑(L + 1) : ℝ) * ∑ q ∈ Finset.Icc 1 Q,
                  ∑ p ∈ P, ((q : ℝ) / (q.totient : ℝ)) *
                    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
                      ‖∑ n ∈ Finset.range N, blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2 := by
                refine congrArg (fun x => (↑(L + 1) : ℝ) * x) (Finset.sum_congr rfl fun q _ => ?_)
                rw [Finset.mul_sum]
            _ = (↑(L + 1) : ℝ) * ∑ p ∈ P,
                  ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
                    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
                      ‖∑ n ∈ Finset.range N, blockCoeff c p.1 p.2 n * χ (n : ZMod q)‖ ^ 2 := by
                rw [Finset.sum_comm]
      _ ≤ (↑(L + 1) : ℝ) * ∑ p ∈ P,
            ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖blockCoeff c p.1 p.2 n‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum fun p _ => ?_
          exact char_LS hQ (blockCoeff c p.1 p.2)
      _ = (↑(L + 1) : ℝ) *
            (((Q : ℝ) ^ 2 + 13 * N) * ((↑(L + 1) : ℝ) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2)) := by
          congr 1
          rw [← Finset.mul_sum]
          congr 1
          rw [hPdef, Finset.sum_product' (Finset.range (L + 1)) (Finset.range N)
            (fun i k => ∑ n ∈ Finset.range N, ‖blockCoeff c i k n‖ ^ 2)]
          rw [Finset.sum_congr rfl (fun j _ => sum_blockCoeff_normSq c N j)]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (1 + Real.logb 2 N) ^ 2 * ((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
          have hL_le : (↑(L + 1) : ℝ) ≤ 1 + Real.logb 2 N := by
            have h := Real.natLog_le_logb N 2
            rw [hL]; push_cast at h ⊢; linarith
          have hLnn : (0 : ℝ) ≤ (↑(L + 1) : ℝ) := by positivity
          have hsq : (↑(L + 1) : ℝ) ^ 2 ≤ (1 + Real.logb 2 N) ^ 2 :=
            pow_le_pow_left₀ hLnn hL_le 2
          calc (↑(L + 1) : ℝ) *
                (((Q : ℝ) ^ 2 + 13 * N) * ((↑(L + 1) : ℝ) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2))
              = (↑(L + 1) : ℝ) ^ 2 *
                  (((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2) := by ring
            _ ≤ (1 + Real.logb 2 N) ^ 2 *
                  (((Q : ℝ) ^ 2 + 13 * N) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2) :=
                mul_le_mul_of_nonneg_right hsq (by positivity)
            _ = (1 + Real.logb 2 N) ^ 2 * ((Q : ℝ) ^ 2 + 13 * N) *
                  ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by ring

end Salt.BV
