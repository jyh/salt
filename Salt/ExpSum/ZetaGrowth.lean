/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.ZetaBlock
import Salt.ExpSum.Kusmin

/-!
# The dyadic assembly for the ζ-phase (`n^{-it}`) — Littlewood-grade growth

This file assembles the landed per-block bound (`zeta_block_bound`,
`Salt/ExpSum/ZetaBlock.lean`) over dyadic scales `N_j = 2^j·N₀` into a
power-saving bound on the **partial sum** `∑_{N₀ < n ≤ X} n^{−it}` (phase form
`∑ eR (phi t n)`), the checkpoint's second-to-last rung.

## The three rungs (the ZENO ladder)

1. **The geometric stone** (`geom_pow_sum_le`).  Pure real analysis:
   `∑_{j<J} (2^s)^j ≤ (2^s)^J / (2^s − 1)` for `s > 0`.  This is what turns the
   sum of per-block bounds `∑_j C·N_j^{1−α}` (a geometric series in the dyadic
   ratio `2^{1−α}`) into a single power `C'·X^{1−α}`.

2. **The dyadic split** (`dyadic_sum_split`).  `Ioc N₀ (2^J·N₀)` telescopes
   into the `J` consecutive dyadic blocks `Ioc (2^j·N₀) (2^{j+1}·N₀)`
   (`Finset.sum_Ioc_consecutive`), each of the exact shape `Ioc N (2N)` that
   `zeta_block_bound` consumes.

3. **The assembly** (`zeta_dyadic_assembly`, the node).  From abstract
   per-block bounds `‖block_j‖ ≤ C·N_j^{1−α}` (`α = 1/(2^k−2)`) it delivers
   `‖∑_{N₀<n≤X}‖ ≤ (C/(2^{1−α}−1))·X^{1−α}` — a genuine power
   saving `X^{−α}` over the trivial `X`.

The consumable corollary (`zeta_partial_growth`) discharges the abstract block
bounds from `zeta_block_bound` on the honest van der Corput window: for each
dyadic scale the k-th-derivative magnitude `λ_j` sits in `[N_j^{−3+8/2^k},
N_j^{−1}]`.  These window hypotheses are supplied per scale (the classical
statement); translating a *single* `t` into global coverage across all scales —
letting `k` grow with the scale to reach the `ζ(1+it) ≪ log t/loglog t`
refinement — is the σ-shift business of the next rung (recorded below).

## CATCH #72 (inherited from `zeta_block_bound`)

The k-window's honest range is `λ ∈ [N^{−3+8/2^k}, N^{−1}]`, i.e. in `t` a band
`t ∈ [c₁·N^{k−3+8/2^k}, c₂·N^{k−1}]`; `k = 2` is degenerate (`α = 1/2` but the
window is a point).  The assembly is stated with the window as an explicit
per-scale hypothesis, so this catch is discharged at the call site, not here.

## Residuals recorded (honest scope)

* **Global coverage from a single `t`** (turning `t` into the per-scale window
  hypotheses of `zeta_partial_growth`, with `k` varying by scale): residual
  `LITT-COVER` — the σ-shift / loglog refinement is the next rung's content.
* **Wire-in**: this module is not yet imported by `Salt/ExpSum/All.lean` (a
  landed file, left untouched here); a Fable/human wire-in step should add the
  import and the `#audit_axioms` entries for `zeta_partial_growth`,
  `zeta_dyadic_assembly`, `zeta_block_kusmin`.

The K-L large-block stone (`N ≥ t`) is **landed** below as `zeta_block_kusmin`
(Section 5): `‖∑_{N<n≤2N} n^{−it}‖ ≤ 2π(2N+1)/t`, the `N/t`-grade bound for the
large blocks the band assembly does not cover.
-/

namespace Salt.ExpSum

open Real Finset

/-! ## Section 1 — the geometric dyadic sum -/

/-- **The geometric stone.**  For `s > 0`, the dyadic geometric series is bounded
by its top term over `2^s − 1`: `∑_{j<J} (2^s)^j ≤ (2^s)^J / (2^s − 1)`.  Proved
by induction (the step is the exact identity `T/(r−1) + T = r·T/(r−1)`). -/
lemma geom_pow_sum_le {s : ℝ} (hs : 0 < s) (J : ℕ) :
    ∑ j ∈ Finset.range J, ((2 : ℝ) ^ s) ^ j
      ≤ ((2 : ℝ) ^ s) ^ J / ((2 : ℝ) ^ s - 1) := by
  have hr1 : 1 < (2 : ℝ) ^ s := Real.one_lt_rpow (by norm_num) hs
  have hd : 0 < (2 : ℝ) ^ s - 1 := by linarith
  have hdne : (2 : ℝ) ^ s - 1 ≠ 0 := ne_of_gt hd
  induction J with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
      exact le_of_lt (div_pos one_pos hd)
  | succ J ih =>
      rw [Finset.sum_range_succ]
      calc ∑ j ∈ Finset.range J, ((2 : ℝ) ^ s) ^ j + ((2 : ℝ) ^ s) ^ J
          ≤ ((2 : ℝ) ^ s) ^ J / ((2 : ℝ) ^ s - 1) + ((2 : ℝ) ^ s) ^ J := by linarith [ih]
        _ = ((2 : ℝ) ^ s) ^ (J + 1) / ((2 : ℝ) ^ s - 1) := by
            rw [pow_succ]; field_simp; ring

/-! ## Section 2 — the dyadic split -/

/-- The dyadic scale `(2^j·N₀)^s` splits multiplicatively: `= (2^s)^j · N₀^s`. -/
lemma dyadic_scale_rpow (N₀ : ℕ) (s : ℝ) (j : ℕ) :
    (((2 ^ j * N₀ : ℕ) : ℝ)) ^ s = ((2 : ℝ) ^ s) ^ j * ((N₀ : ℝ)) ^ s := by
  have hcast : ((2 ^ j * N₀ : ℕ) : ℝ) = (2 : ℝ) ^ j * (N₀ : ℝ) := by push_cast; ring
  rw [hcast, Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast ((2 : ℝ) ^ s) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]

/-- **The dyadic split.**  `Ioc N₀ (2^J·N₀)` telescopes into the `J` consecutive
dyadic blocks `Ioc (2^j·N₀) (2^{j+1}·N₀)` (each of the form `Ioc N (2N)`). -/
lemma dyadic_sum_split (t : ℝ) (N₀ : ℕ) : ∀ J : ℕ,
    ∑ n ∈ Finset.Ioc (N₀ : ℤ) ((2 ^ J * N₀ : ℕ) : ℤ), eR (phi t n)
      = ∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc ((2 ^ j * N₀ : ℕ) : ℤ) ((2 ^ (j + 1) * N₀ : ℕ) : ℤ),
            eR (phi t n) := by
  intro J
  induction J with
  | zero =>
      simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, Finset.Ioc_self]
  | succ J ih =>
      have hmono1 : (N₀ : ℤ) ≤ ((2 ^ J * N₀ : ℕ) : ℤ) := by
        have h : N₀ ≤ 2 ^ J * N₀ := Nat.le_mul_of_pos_left N₀ (by positivity)
        exact_mod_cast h
      have hmono2 : ((2 ^ J * N₀ : ℕ) : ℤ) ≤ ((2 ^ (J + 1) * N₀ : ℕ) : ℤ) := by
        have h : 2 ^ J * N₀ ≤ 2 ^ (J + 1) * N₀ :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)) (le_refl N₀)
        exact_mod_cast h
      have hdisj : Disjoint (Finset.Ioc (N₀ : ℤ) ((2 ^ J * N₀ : ℕ) : ℤ))
          (Finset.Ioc ((2 ^ J * N₀ : ℕ) : ℤ) ((2 ^ (J + 1) * N₀ : ℕ) : ℤ)) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_Ioc] at hx hx'
        omega
      rw [Finset.sum_range_succ, ← ih, ← Finset.Ioc_union_Ioc_eq_Ioc hmono1 hmono2,
        Finset.sum_union hdisj]

/-! ## Section 3 — the assembly (the node) -/

/-- **The dyadic assembly (the node).**  Given per-block bounds
`‖∑_{2^j·N₀ < n ≤ 2^{j+1}·N₀} eR (phi t n)‖ ≤ C·(2^j·N₀)^{1−α}` for every
scale `j < J` (`α = 1/(2^k−2)`, the exponent `zeta_block_bound` produces), the
whole partial sum over `Ioc N₀ (2^J·N₀)` obeys
`‖∑‖ ≤ (C/(2^{1−α}−1))·(2^J·N₀)^{1−α}` — the Littlewood-grade power saving
`X^{−α}` over the trivial `X`.

Route: `dyadic_sum_split` + triangle inequality + `dyadic_scale_rpow`-factoring
+ `geom_pow_sum_le`.  The constant `2^{1−α}−1 ≥ √2−1 > 0` is bounded since
`α ≤ 1/2` (so `1−α ≥ 1/2`). -/
theorem zeta_dyadic_assembly {k : ℕ} (hk : 2 ≤ k) {C : ℝ} (hC : 0 ≤ C)
    (t : ℝ) (N₀ J : ℕ)
    (hblock : ∀ j : ℕ, j < J →
      ‖∑ n ∈ Finset.Ioc ((2 ^ j * N₀ : ℕ) : ℤ) ((2 ^ (j + 1) * N₀ : ℕ) : ℤ),
          eR (phi t n)‖
        ≤ C * (((2 ^ j * N₀ : ℕ) : ℝ)) ^ (1 - 1 / ((2 : ℝ) ^ k - 2))) :
    ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) ((2 ^ J * N₀ : ℕ) : ℤ), eR (phi t n)‖
      ≤ (C / ((2 : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) - 1))
          * (((2 ^ J * N₀ : ℕ) : ℝ)) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) := by
  set s : ℝ := 1 - 1 / ((2 : ℝ) ^ k - 2) with hs_def
  have h2k : (4 : ℝ) ≤ (2 : ℝ) ^ k := four_le_two_pow k hk
  have hden : (0 : ℝ) < (2 : ℝ) ^ k - 2 := by linarith
  have hαle : 1 / ((2 : ℝ) ^ k - 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hαpos : (0 : ℝ) < 1 / ((2 : ℝ) ^ k - 2) := by positivity
  have hs0 : 0 < s := by rw [hs_def]; linarith
  have hgeo := geom_pow_sum_le hs0 J
  rw [dyadic_sum_split t N₀ J]
  refine le_trans (norm_sum_le _ _) ?_
  have hbnd : ∑ j ∈ Finset.range J,
      ‖∑ n ∈ Finset.Ioc ((2 ^ j * N₀ : ℕ) : ℤ) ((2 ^ (j + 1) * N₀ : ℕ) : ℤ),
          eR (phi t n)‖
      ≤ ∑ j ∈ Finset.range J, C * (((2 ^ j * N₀ : ℕ) : ℝ)) ^ s :=
    Finset.sum_le_sum (fun j hj => hblock j (Finset.mem_range.mp hj))
  refine le_trans hbnd ?_
  have hfact : ∑ j ∈ Finset.range J, C * (((2 ^ j * N₀ : ℕ) : ℝ)) ^ s
      = C * ((N₀ : ℝ)) ^ s * ∑ j ∈ Finset.range J, ((2 : ℝ) ^ s) ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [dyadic_scale_rpow N₀ s j]; ring)
  rw [hfact]
  have hCN0 : 0 ≤ C * ((N₀ : ℝ)) ^ s :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N₀) s)
  calc C * ((N₀ : ℝ)) ^ s * ∑ j ∈ Finset.range J, ((2 : ℝ) ^ s) ^ j
      ≤ C * ((N₀ : ℝ)) ^ s * (((2 : ℝ) ^ s) ^ J / ((2 : ℝ) ^ s - 1)) :=
        mul_le_mul_of_nonneg_left hgeo hCN0
    _ = (C / ((2 : ℝ) ^ s - 1)) * (((2 ^ J * N₀ : ℕ) : ℝ)) ^ s := by
        rw [dyadic_scale_rpow N₀ s J]
        have hne : (2 : ℝ) ^ s - 1 ≠ 0 :=
          ne_of_gt (by linarith [Real.one_lt_rpow (show (1 : ℝ) < 2 by norm_num) hs0])
        field_simp

/-! ## Section 4 — the growth corollary (the checkpoint's consumable) -/

/-- **The Littlewood-grade partial-sum growth bound (per-k band).**  For every
`k ≥ 2` there is a constant `C ≥ 1` such that, whenever every dyadic scale
`N_j = 2^j·N₀` (`j < J`) lies in the honest van der Corput k-window — i.e.
`k ≤ N_j` and the k-th-derivative magnitude
`λ_j = (t/2π)·(k−1)!·(2N_j+k)^{−k}` sits in `[N_j^{−3+8/2^k}, N_j^{−1}]` —
the ζ-phase partial sum over `Ioc N₀ (2^J·N₀)` obeys
`‖∑_{N₀<n≤X} n^{−it}‖ ≤ C·X^{1−1/(2^k−2)}` with `X = 2^J·N₀`.  A genuine power
saving `X^{−1/(2^k−2)}` over the trivial `X`.

Route: `zeta_block_bound` discharges each block hypothesis of
`zeta_dyadic_assembly` at `N = N_j`; the assembly's geometric factor
`1/(2^{1−α}−1)` folds into `C = Cb/(2^{1−α}−1)` (which is `≥ 1` since
`2^{1−α}−1 ≤ 1 ≤ Cb`).  The per-scale window hypotheses are the classical
statement; global coverage from a single `t` (with `k` growing by scale) is the
recorded residual `LITT-COVER`. -/
theorem zeta_partial_growth (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (t : ℝ) (N₀ J : ℕ), 0 < t →
      (∀ j : ℕ, j < J →
        k ≤ 2 ^ j * N₀ ∧
        (((2 ^ j * N₀ : ℕ) : ℝ)) ^ (-3 + 8 / (2 : ℝ) ^ k)
            ≤ t / (2 * π) * ((k - 1).factorial : ℝ)
                * (((2 * (2 ^ j * N₀) + k : ℕ) : ℝ) ^ k)⁻¹ ∧
        t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * (2 ^ j * N₀) + k : ℕ) : ℝ) ^ k)⁻¹
            ≤ (((2 ^ j * N₀ : ℕ) : ℝ)) ^ (-1 : ℝ)) →
      ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) ((2 ^ J * N₀ : ℕ) : ℤ), eR (phi t n)‖
        ≤ C * (((2 ^ J * N₀ : ℕ) : ℝ)) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) := by
  obtain ⟨Cb, hCb1, hCb⟩ := zeta_block_bound k hk
  refine ⟨Cb / ((2 : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) - 1), ?_, ?_⟩
  · have h2k : (4 : ℝ) ≤ (2 : ℝ) ^ k := four_le_two_pow k hk
    have hden : (0 : ℝ) < (2 : ℝ) ^ k - 2 := by linarith
    have hαle : 1 / ((2 : ℝ) ^ k - 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hαpos : (0 : ℝ) < 1 / ((2 : ℝ) ^ k - 2) := by positivity
    have hs0 : 0 < 1 - 1 / ((2 : ℝ) ^ k - 2) := by linarith
    have hs1 : 1 - 1 / ((2 : ℝ) ^ k - 2) ≤ 1 := by linarith
    have h2s_le : (2 : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2))
          ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
        _ = 2 := by rw [Real.rpow_one]
    have hd : 0 < (2 : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) - 1 := by
      linarith [Real.one_lt_rpow (show (1 : ℝ) < 2 by norm_num) hs0]
    rw [le_div_iff₀ hd, one_mul]
    linarith
  · intro t N₀ J ht hrange
    refine zeta_dyadic_assembly hk (le_trans zero_le_one hCb1) t N₀ J ?_
    intro j hj
    obtain ⟨hkN, hlo, hhi⟩ := hrange j hj
    have hb := hCb t (2 ^ j * N₀)
      (t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * (2 ^ j * N₀) + k : ℕ) : ℝ) ^ k)⁻¹)
      ht hkN rfl hlo hhi
    rwa [show (2 * ((2 ^ j * N₀ : ℕ) : ℤ)) = ((2 ^ (j + 1) * N₀ : ℕ) : ℤ) from by
      push_cast; ring] at hb

/-! ## Section 5 — the Kusmin–Landau large-block stone (`N ≥ t`) -/

/-- Lower sandwich for the consecutive log difference: `1/(n+1) ≤ log(n+1) − log n`
(from `1 − x⁻¹ ≤ log x` at `x = (n+1)/n`). -/
lemma log_succ_sub_ge (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hdiv : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := by positivity
  have hlog : Real.log (((n : ℝ) + 1) / (n : ℝ))
      = Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) :=
    Real.log_div (ne_of_gt hn1) (ne_of_gt hn0)
  have hkey := Real.one_sub_inv_le_log_of_pos hdiv
  rw [hlog, inv_div] at hkey
  have he : (1 : ℝ) - (n : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by field_simp; ring
  linarith [hkey, he]

/-- Upper sandwich for the consecutive log difference: `log(n+1) − log n ≤ 1/n`
(from `log x ≤ x − 1` at `x = (n+1)/n`). -/
lemma log_succ_sub_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hlog : Real.log (((n : ℝ) + 1) / (n : ℝ))
      = Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) :=
    Real.log_div (ne_of_gt hn1) (ne_of_gt hn0)
  have hkey :=
    Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) by positivity)
  rw [hlog] at hkey
  have he : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp; ring
  linarith [hkey, he]

/-- **The Kusmin–Landau large-block bound.**  On a dyadic block `Ioc N (2N)` with
`N ≥ t` (`N ≥ 1`), the ζ-phase sum obeys `‖∑_{N<n≤2N} n^{−it}‖ ≤ 2π(2N+1)/t`.

Route: the consecutive phase difference `g(n) = φ(n+1)−φ(n) = −(t/2π)(log(n+1)−log n)`
sits in the single unit interval `[−1+δ, −δ]` with `δ = t/(2π(2N+1)) ≤ 1/2`
(`log(n+1)−log n ∈ [1/(n+1), 1/n]`, sandwich lemmas above; `N ≥ t` keeps the
magnitude below `1/2`) and is monotone increasing (log has decreasing consecutive
differences), so `kusmin_landau` (`m = −1`) gives `‖block‖ ≤ 1/δ = 2π(2N+1)/t`.
The `ℤ→ℕ` reindex + `eR→eK` switch mirror `vdC_2nd_ZR`. -/
theorem zeta_block_kusmin (t : ℝ) (ht : 0 < t) (N : ℕ) (hN : t ≤ (N : ℝ)) (hN1 : 1 ≤ N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖
      ≤ 2 * π * (2 * (N : ℝ) + 1) / t := by
  set f : ℕ → ℝ := fun j => phi t (j : ℤ) with hf
  set δ : ℝ := t / (2 * π * (2 * (N : ℝ) + 1)) with hδ
  -- reindex the ℤ-window to a ℕ-window and switch eR → eK
  have hsum : ∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)
      = ∑ n ∈ Finset.Ioc N (2 * N), eK (f n) := by
    apply Finset.sum_nbij' (i := fun n : ℤ => n.toNat) (j := fun k : ℕ => (k : ℤ))
    · intro n hn; rw [Finset.mem_Ioc] at hn ⊢; omega
    · intro k hk; rw [Finset.mem_Ioc] at hk ⊢; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn; omega
    · intro k hk; rw [Finset.mem_Ioc] at hk; omega
    · intro n hn; rw [Finset.mem_Ioc] at hn
      rw [eR_eq_eK]; simp only [hf]
      rw [show ((n.toNat : ℤ)) = n from by omega]
  -- the phase and its consecutive difference in log form
  have hfval : ∀ j : ℕ, f j = -(t / (2 * π)) * Real.log (j : ℝ) := by
    intro j; simp only [hf, phi, Int.cast_natCast]
  have hgval : ∀ m : ℕ, f (m + 1) - f m
      = -(t / (2 * π)) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by
    intro m; rw [hfval (m + 1), hfval m]; push_cast; ring
  have hApos : 0 < t / (2 * π) := div_pos ht (by positivity)
  have hpi1 : (1 : ℝ) ≤ π := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
  -- δ ≤ 1/(2π) ≤ 1/2
  have hδ2π : δ ≤ 1 / (2 * π) := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by positivity)]
    have ht2N1 : t ≤ 2 * (N : ℝ) + 1 := by linarith [hN, Nat.cast_nonneg (α := ℝ) N]
    nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr ht2N1)]
  have hδ12 : δ ≤ 1 / 2 := by
    have h : 1 / (2 * π) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hpi1]
    linarith [hδ2π]
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos ht (by positivity)
  -- Kusmin–Landau window hypotheses (m = -1)
  have hg_ub : ∀ n : ℕ, N < n → n ≤ 2 * N →
      f (n + 1) - f n ≤ ((-1 : ℤ) : ℝ) + 1 - δ := by
    intro n hlt hle
    have hn1 : 1 ≤ n := by omega
    have hLlb := log_succ_sub_ge n hn1
    have hn12N : (n : ℝ) + 1 ≤ 2 * (N : ℝ) + 1 := by
      have : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hle
      linarith
    have hstep1 : t / (2 * π) * (1 / ((n : ℝ) + 1))
        ≤ t / (2 * π) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLlb (le_of_lt hApos)
    have hstep2 : δ ≤ t / (2 * π) * (1 / ((n : ℝ) + 1)) := by
      rw [mul_one_div, hδ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hn12N
        (mul_nonneg (le_of_lt ht) (le_of_lt (show (0 : ℝ) < 2 * π by positivity)))]
    have hcomb : δ ≤ t / (2 * π) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
      le_trans hstep2 hstep1
    rw [hgval n, neg_mul]; push_cast; linarith [hcomb]
  have hg_lb : ∀ n : ℕ, N < n → n ≤ 2 * N →
      ((-1 : ℤ) : ℝ) + δ ≤ f (n + 1) - f n := by
    intro n hlt hle
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hLub := log_succ_sub_le n hn1
    have htn : t ≤ (n : ℝ) := by
      have : (N : ℝ) < (n : ℝ) := by exact_mod_cast hlt
      linarith
    have hstep1 : t / (2 * π) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ t / (2 * π) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLub (le_of_lt hApos)
    have hbound : t / (2 * π) * (1 / (n : ℝ)) ≤ 1 - δ := by
      rw [mul_one_div, div_div]
      have h1 : t / (2 * π * (n : ℝ)) ≤ 1 / (2 * π) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr htn)]
      have h3 : 1 / (2 * π) + 1 / (2 * π) ≤ 1 := by
        rw [← add_div, div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
      linarith [h1, hδ2π, h3]
    have hcomb : t / (2 * π) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 - δ :=
      le_trans hstep1 hbound
    rw [hgval n, neg_mul]; push_cast; linarith [hcomb]
  have hmono : ∀ n : ℕ, N < n → n < 2 * N →
      f (n + 1) - f n ≤ f (n + 1 + 1) - f (n + 1) := by
    intro n hlt hlt2
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hratio : ((n : ℝ) + 2) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / (n : ℝ) := by
      rw [div_le_div_iff₀ hn1 hn0]; nlinarith
    have hlogle :=
      Real.log_le_log (show (0 : ℝ) < ((n : ℝ) + 2) / ((n : ℝ) + 1) by positivity) hratio
    rw [Real.log_div (by positivity) (ne_of_gt hn1),
      Real.log_div (ne_of_gt hn1) (ne_of_gt hn0)] at hlogle
    have he2 : f (n + 1 + 1) - f (n + 1)
        = -(t / (2 * π)) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
      rw [hfval (n + 1 + 1), hfval (n + 1)]; push_cast; ring
    rw [hgval n, he2, neg_mul, neg_mul]
    linarith [mul_le_mul_of_nonneg_left hlogle (le_of_lt hApos)]
  -- assemble via Kusmin–Landau
  have hkl := kusmin_landau (f := f) (a := N) (b := 2 * N) (δ := δ) (m := -1)
    hδ0 hδ12 hg_lb hg_ub hmono
  rw [hsum]
  refine le_trans hkl (le_of_eq ?_)
  rw [hδ, one_div_div]

end Salt.ExpSum
