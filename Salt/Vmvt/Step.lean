/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.HolderTwo

/-!
# Theorem 24.5 — the one-step recursion (VMVT nodes R3, R4)

This file assembles the fully-stocked larder of the VMVT campaign into the
one-step Linnik–Karatsuba recursion `VmvtBound k r x → VmvtBound k (r+1) x`
(the large-`x` p-adic step), following Vaughan PSU Chapter 24, Theorem 24.5.

## The two branches (source `S₁`/`S₂` split)

Fix `b = k(r+1)` coordinates and an injective designated block
`e : Fin k → Fin b`.  The transversality split `JkI_le_two_mul_split` gives
`J = J_k(x, b) ≤ 2(S₁ + S₂)` with `S₁ = Ncount(distinctBox)`,
`S₂ = Ncount(degenBox)`.  Whichever of `S₁, S₂` dominates, `J ≤ 4·max(S₁,S₂)`,
and we close each case:

* **`S₂`-dominant (degenerate) — landed here as `degen_dominant_self_improve`.**
  Chaining `degenBox_Ncount_le` and the honest `γ = 2` fractional bound
  `pairEq_Ncount_le_frac` gives the strictly-sublinear self-bound
  `J ≤ 4·(#offPairs)²·x²·J^{1−2/b}`, and the self-improvement engine
  `rpow_self_improve` collapses it to the `x`-power constant
  `J ≤ (4·(#offPairs)²·x²)^{b/2}`.  This is `≤ D·x^{E(k,r+1)}` for
  `r+1 ≥ (k+1)/2` (the exponent `b = k(r+1) ≤ E(k,r+1)` there).

* **`S₁`-dominant (transversal) — the Linnik route (R3 + R4).**  The pigeonhole
  `distinctBox_le_card_mul_sum` covers `S₁` by `#P·∑_p Ncount(transBox p)`, and
  R3's transversal count bounds each `Ncount(transBox p)` via `linnik_lemma` and
  the affine box `Jk_image_affine` at scale `x/p`.

## Status / resume map

* **R4-`S₂` — DONE (this session).**
  - `degen_dominant_self_improve` — the self-improvement to the `x`-power constant.
  - `mul_pred_le_two_pow`, `mul_pred_pow_le_vmvtC0` — the `S₂` constant fits `C₀`.
  - `vmvt_step_degen_branch` — the complete `S₂`-dominant branch to `VmvtBound k (r+1) x`
    (range `k(r+1) ≤ E(k,r+1)`).  This discharges the campaign's flagged "second named gap"
    (the `S₂` Hölder closure) at the *step* level.
* **R4 case-split — DONE (this session).**  `vmvt_step_of_transversal_dominant` reduces the
  full step to the transversal-dominant premise `J ≤ 4·Ncount(distinctBox)` (the degenerate
  case handled internally).  So the ONLY residual for `vmvt_step` is the `S₁`/Linnik route.
* **Prime input — DONE (this session).**  `exists_transversal_prime_set` supplies the
  pigeonhole cardinality `k·k·(k−1) < 2·#{p ∈ (y,2y] : prime}` for `y ≥ Y(k)` — the input
  to `distinctBox_le_card_mul_sum`.
* **R3 — RESIDUAL (flagged).**  The transversal count `Ncount(transBox p) ≤
  k!·p^{k(k−1)/2}·x^k·[IH box at scale x/p]`.  Needs NEW frame machinery: a block-split of
  the `Ncount`/`sig` counting object into the designated-`k` and rest-`kr` blocks, plus the
  p-adic reduction that lands the designated block in `LinnikSol` (feeding `linnik_lemma`)
  and the rest in an affine box (`Jk_image_affine`).  See `docs/blueprints/flags.md`.
* **R4-`S₁` assembly — RESIDUAL (flagged).**  Consumes R3 + `exists_transversal_prime_set`
  + `distinctBox_le_card_mul_sum` + the IH, converting the `p`-powers to `x`-powers with
  `p ∈ (x^{1/k}, 2x^{1/k}]` (the `x^{1/k}` construction) and the IH at scale `x/p`, matching
  the kernel-verified `vmvtExp_succ`.  See `docs/blueprints/flags.md`.
-/

namespace Salt.Vmvt

open Finset

/-! ## R4, the `S₂`-dominant branch: self-improvement to an `x`-power constant -/

/-- `#offPairs k ≥ 1` for `k ≥ 2` (from `2·#offPairs = k(k−1) ≥ 2`). -/
theorem one_le_offPairs_card {k : ℕ} (hk : 2 ≤ k) : 1 ≤ (offPairs k).card := by
  have h2 : 2 * (offPairs k).card = k * (k - 1) := two_mul_offPairs_card k
  have hkk : 2 ≤ k * (k - 1) := by
    calc 2 = 2 * 1 := rfl
      _ ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
  omega

/-- **R4, the `S₂`-dominant closure (the self-improving Hölder step).**  With
`b = k(r+1)`, an injective designated block `e`, `x ≥ 1`, and the degenerate-
dominant hypothesis `J ≤ 4·Ncount(degenBox)`, the mean value `J = J_k(x, b)` is
bounded by the `x`-power constant `(4·(#offPairs)²·x²)^{b/2}`.

Chain: `degenBox_Ncount_le` (the pair-collapse union) → `pairEq_Ncount_le_frac`
(the honest `γ = 2` fractional bound, needing `e` injective) →
`rpow_self_improve` (the self-improvement engine). -/
theorem degen_dominant_self_improve {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * (r + 1)))
    (hk : 2 ≤ k) (hx : 1 ≤ x) (hinj : Function.Injective e)
    (hdom : (JkI k (k * (r + 1)) x : ℝ)
              ≤ 4 * (Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e) : ℝ)) :
    (JkI k (k * (r + 1)) x : ℝ)
      ≤ (4 * (((offPairs k).card : ℝ) ^ 2 * (x : ℝ) ^ 2))
          ^ ((k : ℝ) * ((r : ℝ) + 1) / 2) := by
  classical
  have hb2 : 2 ≤ k * (r + 1) := by
    calc 2 = 2 * 1 := rfl
      _ ≤ k * (r + 1) := Nat.mul_le_mul hk (by omega)
  set J : ℝ := (JkI k (k * (r + 1)) x : ℝ) with hJdef
  set n : ℝ := ((offPairs k).card : ℝ) with hndef
  -- the fractional exponent, exactly as `pairEq_Ncount_le_frac` produces it
  set θ : ℝ := 2 / ((k : ℝ) * ((r + 1 : ℕ) : ℝ)) with hθdef
  have hbR : (0 : ℝ) < (k : ℝ) * ((r + 1 : ℕ) : ℝ) := by positivity
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  -- per-pair fractional bound
  have hpair : ∀ ab ∈ offPairs k,
      (Ncount k (k * (r + 1)) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
        ≤ (x : ℝ) ^ 2 * J ^ (1 - θ) := by
    intro ab hab
    have hne : e ab.1 ≠ e ab.2 := by
      rw [offPairs, Finset.mem_filter] at hab
      exact fun h => (ne_of_lt hab.2) (hinj h)
    have hp := pairEq_Ncount_le_frac (k := k) (r := r + 1) x e ab hne hb2
    exact hp
  -- aggregate: Ncount(degenBox) ≤ n² · x² · J^{1−θ}
  have hdegen : (Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e) : ℝ)
      ≤ n ^ 2 * ((x : ℝ) ^ 2 * J ^ (1 - θ)) := by
    have hsum : ∑ ab ∈ offPairs k,
        (Ncount k (k * (r + 1)) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
        ≤ n * ((x : ℝ) ^ 2 * J ^ (1 - θ)) := by
      calc ∑ ab ∈ offPairs k,
            (Ncount k (k * (r + 1)) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
          ≤ ∑ _ab ∈ offPairs k, (x : ℝ) ^ 2 * J ^ (1 - θ) := Finset.sum_le_sum hpair
        _ = n * ((x : ℝ) ^ 2 * J ^ (1 - θ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hndef]
    have hdcast : (Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e) : ℝ)
        ≤ n * ∑ ab ∈ offPairs k,
            (Ncount k (k * (r + 1)) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ) := by
      calc (Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e) : ℝ)
          ≤ (((offPairs k).card * ∑ ab ∈ offPairs k,
                Ncount k (k * (r + 1)) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℕ) : ℝ) := by
            exact_mod_cast degenBox_Ncount_le x e
        _ = n * ∑ ab ∈ offPairs k,
              (Ncount k (k * (r + 1)) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ) := by
            rw [hndef]; push_cast; ring
    calc (Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e) : ℝ)
        ≤ n * ∑ ab ∈ offPairs k,
            (Ncount k (k * (r + 1)) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ) := hdcast
      _ ≤ n * (n * ((x : ℝ) ^ 2 * J ^ (1 - θ))) :=
          mul_le_mul_of_nonneg_left hsum (by rw [hndef]; positivity)
      _ = n ^ 2 * ((x : ℝ) ^ 2 * J ^ (1 - θ)) := by ring
  -- the self-bound `J ≤ 4·K·J^{1−θ}`, `K = n²·x²`
  have hn1 : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast one_le_offPairs_card hk
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hK1 : (1 : ℝ) ≤ 4 * (n ^ 2 * (x : ℝ) ^ 2) := by
    nlinarith [hn1, hx1, sq_nonneg (n - 1), sq_nonneg ((x : ℝ) - 1)]
  have hstep : J ≤ 4 * (n ^ 2 * (x : ℝ) ^ 2) * J ^ (1 - θ) := by
    calc J ≤ 4 * (Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e) : ℝ) := hdom
      _ ≤ 4 * (n ^ 2 * ((x : ℝ) ^ 2 * J ^ (1 - θ))) :=
          mul_le_mul_of_nonneg_left hdegen (by norm_num)
      _ = 4 * (n ^ 2 * (x : ℝ) ^ 2) * J ^ (1 - θ) := by ring
  have hself := rpow_self_improve (J := J) (K := n ^ 2 * (x : ℝ) ^ 2) (θ := θ)
    (Nat.cast_nonneg _) hK1 hθ0 hstep
  -- rewrite `1/θ = b/2` to match the goal
  have hrecip : 1 / θ = (k : ℝ) * ((r : ℝ) + 1) / 2 := by
    rw [hθdef, one_div_div]; push_cast; ring
  rwa [hrecip] at hself

/-! ## The `S₂` constant fits under `C₀`

The self-improved bound carries the constant `(4·(#offPairs)²)^{b/2} = (k(k−1))^b`;
`mul_pred_pow_le_vmvtC0` shows the per-step piece `(k(k−1))^k` fits under `C₀(k)`
(via `(k(k−1))^k ≤ (2^k)^k = 2^{k²} ≤ C₀`), so the full constant fits under
`D(k,r+1) = C₀^{r+1}`. -/

/-- `k(k−1) ≤ 2^k` for every `k` (the crude bound feeding the `S₂` constant). -/
lemma mul_pred_le_two_pow (k : ℕ) : k * (k - 1) ≤ 2 ^ k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> decide
  · induction k, hk using Nat.le_induction with
    | base => decide
    | succ m hm IH =>
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
      have e1 : t + 2 + 1 - 1 = t + 2 := by omega
      have e2 : t + 2 - 1 = t + 1 := by omega
      rw [e1]; rw [e2] at IH
      have hpow : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
      have h2 : 2 * t + 4 ≤ 2 ^ (t + 2) := by
        have hpe : (2 : ℕ) ^ (t + 2) = 4 * 2 ^ t := by rw [pow_add]; ring
        rw [hpe]; nlinarith [hpow]
      calc (t + 2 + 1) * (t + 2)
          = (t + 2) * (t + 1) + (2 * t + 4) := by ring
        _ ≤ 2 ^ (t + 2) + 2 ^ (t + 2) := Nat.add_le_add IH h2
        _ = 2 ^ (t + 2 + 1) := by rw [pow_succ]; ring

/-- **The per-step `S₂` constant fits under `C₀`.**  `(k(k−1))^k ≤ C₀(k)`:
`(k(k−1))^k ≤ (2^k)^k = 2^{k²} ≤ k⁶·k!·2^{k²}·3 = C₀(k)`. -/
theorem mul_pred_pow_le_vmvtC0 {k : ℕ} (hk : 2 ≤ k) :
    (((k * (k - 1)) ^ k : ℕ) : ℝ) ≤ vmvtC0 k := by
  have hnat : (k * (k - 1)) ^ k ≤ 2 ^ (k ^ 2) := by
    calc (k * (k - 1)) ^ k ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (mul_pred_le_two_pow k) k
      _ = 2 ^ (k * k) := by rw [← pow_mul]
      _ = 2 ^ (k ^ 2) := by rw [pow_two]
  have h1 : (((k * (k - 1)) ^ k : ℕ) : ℝ) ≤ ((2 ^ (k ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  refine h1.trans ?_
  unfold vmvtC0
  rw [Nat.cast_pow, Nat.cast_ofNat]
  have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ (k ^ 2) := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ k))
  have hf1 : (1 : ℝ) ≤ (k.factorial : ℝ) := Nat.one_le_cast.mpr k.factorial_pos
  have hcof : (1 : ℝ) ≤ (k : ℝ) ^ 6 * (k.factorial : ℝ) * 3 := by nlinarith [hk1, hf1]
  have hrw : (k : ℝ) ^ 6 * (k.factorial : ℝ) * (2 : ℝ) ^ (k ^ 2) * 3
      = (2 : ℝ) ^ (k ^ 2) * ((k : ℝ) ^ 6 * (k.factorial : ℝ) * 3) := by ring
  rw [hrw]
  exact le_mul_of_one_le_right hbase hcof

/-! ## R4, the `S₂`-dominant branch to the target `VmvtBound` -/

/-- **R4, the `S₂`-dominant branch (complete).**  In the degenerate-dominant case
(`J ≤ 4·Ncount(degenBox)`) and the exponent range `b = k(r+1) ≤ E(k,r+1)`, the
self-improved constant bound closes to the target `VmvtBound k (r+1) x`.  The
exponent `b ≤ E(k,r+1)` and the constant `(k(k−1))^b ≤ C₀^{r+1}` are exactly the
`r+1 ≥ (k+1)/2` regime of the source. -/
theorem vmvt_step_degen_branch {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * (r + 1)))
    (hk : 2 ≤ k) (hx : 1 ≤ x) (hinj : Function.Injective e)
    (hrange : ((k * (r + 1) : ℕ) : ℝ) ≤ vmvtExp k (r + 1))
    (hdom : (JkI k (k * (r + 1)) x : ℝ)
              ≤ 4 * (Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e) : ℝ)) :
    VmvtBound k (r + 1) x := by
  classical
  set n : ℝ := ((offPairs k).card : ℝ) with hndef
  set E2 : ℝ := (k : ℝ) * ((r : ℝ) + 1) / 2 with hE2def
  set B : ℝ := ((k * (r + 1) : ℕ) : ℝ) with hBdef
  set M : ℝ := ((k * (k - 1) : ℕ) : ℝ) * (x : ℝ) with hMdef
  have hself := degen_dominant_self_improve x e hk hx hinj hdom
  -- 4·(n²·x²) = M², via 2n = k(k−1)
  have hcard : ((k * (k - 1) : ℕ) : ℝ) = 2 * n := by
    rw [hndef]; rw [← two_mul_offPairs_card k]; push_cast; ring
  have hkkx : (4 : ℝ) * (n ^ 2 * (x : ℝ) ^ 2) = M ^ 2 := by
    rw [hMdef, hcard]; ring
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  -- (M²)^E2 = M^B
  have hexpeq : ((2 : ℕ) : ℝ) * E2 = B := by rw [hE2def, hBdef]; push_cast; ring
  have hMB : (M ^ 2) ^ E2 = M ^ B := by
    rw [← Real.rpow_natCast M 2, ← Real.rpow_mul hM0, hexpeq]
  unfold VmvtBound
  refine hself.trans ?_
  rw [hkkx, hMB]
  -- M^B = (k(k−1))^b · x^B, split
  have hMsplit : M ^ B = ((k * (k - 1) : ℕ) : ℝ) ^ B * (x : ℝ) ^ B := by
    rw [hMdef, Real.mul_rpow (by positivity) (by positivity)]
  rw [hMsplit]
  -- the constant factor: (k(k−1))^B = (k(k−1))^{k(r+1)} ≤ C₀^{r+1} = D(k,r+1)
  have hCB : ((k * (k - 1) : ℕ) : ℝ) ^ B = (((k * (k - 1)) ^ (k * (r + 1)) : ℕ) : ℝ) := by
    rw [hBdef, Real.rpow_natCast, Nat.cast_pow]
  have hConst : (((k * (k - 1)) ^ (k * (r + 1)) : ℕ) : ℝ) ≤ vmvtConst k (r + 1) := by
    have hpm : ((k * (k - 1)) ^ (k * (r + 1)) : ℕ) = ((k * (k - 1)) ^ k) ^ (r + 1) := by
      rw [← pow_mul]
    rw [hpm, Nat.cast_pow]
    unfold vmvtConst
    exact pow_le_pow_left₀ (by positivity) (mul_pred_pow_le_vmvtC0 hk) (r + 1)
  -- the x-factor: x^B ≤ x^{E(k,r+1)} by exponent monotonicity (x ≥ 1, B ≤ E)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxB : (x : ℝ) ^ B ≤ (x : ℝ) ^ (vmvtExp k (r + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hBdef]; exact hrange)
  rw [hCB]
  refine mul_le_mul hConst hxB (Real.rpow_nonneg (by positivity) _) ?_
  exact le_trans (Nat.cast_nonneg _) hConst

/-! ## R4, the step reduced to the transversal-dominant case

The transversality split `JkI_le_two_mul_split` gives `J ≤ 2(S₁ + S₂)`; whichever
of `S₁ = Ncount(distinctBox)`, `S₂ = Ncount(degenBox)` dominates, `J ≤ 4·max`.
`vmvt_step_of_transversal_dominant` discharges the degenerate case by
`vmvt_step_degen_branch` and reduces the whole step to the transversal-dominant
premise (`J ≤ 4·S₁`) — the `S₁`/Linnik route (R3 + the `p`-adic assembly). -/

/-- **R4, the step reduced to the transversal route.**  Given the exponent range
`b = k(r+1) ≤ E(k,r+1)` and a handler `htrans` for the transversal-dominant case
(`J ≤ 4·Ncount(distinctBox)`), the full one-step bound `VmvtBound k (r+1) x`
holds.  The degenerate-dominant case is discharged internally by
`vmvt_step_degen_branch`; the only carried input is the `S₁`/Linnik route, whose
transversal count is R3. -/
theorem vmvt_step_of_transversal_dominant {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * (r + 1)))
    (hk : 2 ≤ k) (hx : 1 ≤ x) (hinj : Function.Injective e)
    (hrange : ((k * (r + 1) : ℕ) : ℝ) ≤ vmvtExp k (r + 1))
    (htrans : (JkI k (k * (r + 1)) x : ℝ)
                ≤ 4 * (Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e) : ℝ)
              → VmvtBound k (r + 1) x) :
    VmvtBound k (r + 1) x := by
  have hsplit : JkI k (k * (r + 1)) x
      ≤ 2 * (Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e)
             + Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e)) :=
    JkI_le_two_mul_split x e
  rcases le_total (Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e))
                  (Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e)) with hle | hle
  · -- transversal-dominant: `J ≤ 4·S₁`
    apply htrans
    have hnat : JkI k (k * (r + 1)) x
        ≤ 4 * Ncount k (k * (r + 1)) 0 (distinctBox x e) (distinctBox x e) := by omega
    exact_mod_cast hnat
  · -- degenerate-dominant: `J ≤ 4·S₂`, discharged by the landed `S₂` branch
    apply vmvt_step_degen_branch x e hk hx hinj hrange
    have hnat : JkI k (k * (r + 1)) x
        ≤ 4 * Ncount k (k * (r + 1)) 0 (degenBox x e) (degenBox x e) := by omega
    exact_mod_cast hnat

/-! ## The pigeonhole prime set (the analytic input to the transversal route)

`distinctBox_le_card_mul_sum` needs a prime set `P ⊆ (y, 2y]` with
`#P > ½k²(k−1)` (division-free `k·k·(k−1) < 2·#P`).
`exists_transversal_prime_set` supplies the threshold: for `y` large enough the
interval `(y, 2y]` holds that many primes.  Chains the Chebyshev-grade
`primes_in_Ioc_ge` (`#P ≥ c·y/log y`) through `log y ≤ 2√y` (so `#P ≥ c√y/2`),
which exceeds any fixed `½k²(k−1)` once `√y > (k²(k−1)+1)/c`. -/

/-- **The pigeonhole prime set exists for large `y`.**  For `k ≥ 2` there is a
threshold `Y ≥ 2` such that for every `y ≥ Y`, the interval `(y, 2y]` contains
more than `½k²(k−1)` primes (division-free `k·k·(k−1) < 2·#{p ∈ (y,2y] : p prime}`).
This is the pigeonhole cardinality hypothesis of `distinctBox_le_card_mul_sum`
(the surplus over the bad-prime bound), valid in the large-`x` regime `y ≈ x^{1/k}`. -/
theorem exists_transversal_prime_set {k : ℕ} (_hk : 2 ≤ k) :
    ∃ Y : ℕ, 2 ≤ Y ∧ ∀ y : ℕ, Y ≤ y →
      k * k * (k - 1) < 2 * ((Finset.Ioc y (2 * y)).filter Nat.Prime).card := by
  obtain ⟨c, hc0, y₀, hy₀⟩ := primes_in_Ioc_ge
  set M : ℝ := ((k * k * (k - 1) : ℕ) : ℝ) with hMdef
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (((M + 1) / c) ^ 2)
  refine ⟨max (max y₀ N) 2, le_max_right _ _, fun y hy => ?_⟩
  have hy0y : y₀ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hNy : N ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_max_right _ _) hy
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy2
  have hypos : (0 : ℝ) < (y : ℝ) := by linarith
  have hlogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hlog_le : Real.log (y : ℝ) ≤ 2 * Real.sqrt (y : ℝ) := Salt.SW.log_le_two_sqrt hypos
  set P : ℕ := ((Finset.Ioc y (2 * y)).filter Nat.Prime).card with hPdef
  have hPge : c * (y : ℝ) / Real.log (y : ℝ) ≤ (P : ℝ) := hy₀ y hy0y
  -- `c√y/2 ≤ #P`, from `log y ≤ 2√y`
  have hstep1 : c * Real.sqrt (y : ℝ) / 2 ≤ (P : ℝ) := by
    have hcross : c * Real.sqrt (y : ℝ) * Real.log (y : ℝ) ≤ 2 * (c * (y : ℝ)) := by
      have h1 : c * Real.sqrt (y : ℝ) * Real.log (y : ℝ)
          ≤ c * Real.sqrt (y : ℝ) * (2 * Real.sqrt (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_le (by positivity)
      nlinarith [h1, Real.mul_self_sqrt hypos.le]
    have hle2 : c * Real.sqrt (y : ℝ) / 2 ≤ c * (y : ℝ) / Real.log (y : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hlogpos]; linarith [hcross]
    exact le_trans hle2 hPge
  -- `M + 1 ≤ c√y`, from `√y ≥ (M+1)/c`
  have h2 : (M + 1) / c ≤ Real.sqrt (y : ℝ) := by
    have hsq : ((M + 1) / c) ^ 2 ≤ (y : ℝ) := le_trans hN (by exact_mod_cast hNy)
    calc (M + 1) / c = Real.sqrt (((M + 1) / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (y : ℝ) := Real.sqrt_le_sqrt hsq
  have hMc : M + 1 ≤ c * Real.sqrt (y : ℝ) := by
    have h := (div_le_iff₀ hc0).mp h2; linarith [h]
  -- assemble: `M < 2·#P`, then cast
  have hfinal : M < 2 * (P : ℝ) := by
    have hcs : c * Real.sqrt (y : ℝ) ≤ 2 * (P : ℝ) := by linarith [hstep1]
    linarith [hMc, hcs]
  have hcast : (((k * k * (k - 1) : ℕ) : ℝ)) < 2 * (P : ℝ) := by rw [← hMdef]; exact hfinal
  exact_mod_cast hcast

end Salt.Vmvt
