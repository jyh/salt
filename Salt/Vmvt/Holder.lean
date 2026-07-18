/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vmvt.Transversal
import Salt.Vmvt.MeanValue

/-!
# The self-improving fractional Hölder engine — the `S₂`-regime closure (VMVT R2-3)

This file supplies the toolkit around the **self-improving fractional Hölder**
step of Vaughan PSU Ch. 24 (Theorem 24.5, the `S₂ ≥ S₁` degenerate sub-case):
the mechanism by which a *strictly sublinear* bound on the degenerate count
`S₂` forces `J_k` down to an `x`-free constant.

## The source's `S₂` step (analytic) and what it needs

On the signature frame of `Shifted.lean`, `S₂ = Ncount(D₂)` where `D₂` is the
degenerate box; `degenBox_Ncount_le` (landed, `Transversal.lean`) collapses it to
the pair-boxes `D_{a=b}` (`pairEqBox`).  The source bounds each collapsed count by
the doubled-variable moment and applies **Hölder's inequality** to
`∫ |f(2α)|² |f(α)|^{2kr−4} dα`, giving the strictly-sublinear
`S₂ ≤ k⁴ · J_k(x,kr)^{1 − 1/(kr)}`
(the campaign's own resume map, `MeanValue.lean`, records the target exponent as
`1 − 1/(kr)`; the source OCR "`1 − 2/kr`" is a looser variant — **both**
self-improve, see below).

## Why the gain is analytic, not combinatorial (the flagged obstruction)

The gain lives in the **α-domain** (the exponential sum `f`), Fourier-dual to the
**h-domain** (signatures `h`) that the `rcount` frame inhabits.  The `Ncount`/`sig`
machinery was *deliberately* built Fourier-free (`Shifted.lean` docstring), so it
cannot mirror the α-domain Hölder — moving between the domains is exactly Parseval,
which the frame avoids.  Concretely, every purely-combinatorial route provably
fails to beat linear:

* **pointwise `r_D ≤ r_A`** (`D ⊆ A^{kr}`) feeds any Hölder split back into
  `Σ r_D²` on the right → self-referential, recovering only the linear `S₂ ≤ J`;
* **geometric interpolation** of the two crude true bounds (`S₂ ≤ J` and
  `S₂ ≤ |D|²`) gives `J^{1−1/kr} · x^{+}` with a **positive** `x`-power, which
  makes the self-improvement produce the `x`-dependent `x^{2kr−2}` (wrong side of
  `E(k,r)`, see `crude_exp_ge_vmvtExp`);
* **Cauchy–Schwarz on the collapsed-variable sum** (`Σ_{u,v} N_B(2σv−2σu)` with
  `N_B(ℓ) ≤ N_B(0)`) is linear-in-`J_k(x,kr−2)`, hence circular.

So the fractional bound is a genuine **analytic input**: `R4` must carry it as a
named hypothesis (this file's `PairEqFracBound`), or the whole `Vmvt` frame must be
extended with torus integration + Parseval.  What this file *does* mechanize, in
full and sorry-free:

1. **The self-improvement engine** `rpow_self_improve`: `J ≤ 4K·J^{1−θ}` ⟹
   `J ≤ (4K)^{1/θ}`, an `x`-free constant (pure `Real.rpow` arithmetic).
2. **The packaged consumer closure** `pairEqDominant_JkI_le_const`: given the
   per-pair fractional bound (`PairEqFracBound`, `θ` abstract so it covers both
   `1/kr` and `2/kr`) and the `S₂`-dominant hypothesis `J ≤ 4·S₂`, `J_k(x,kr)`
   is bounded by an `x`-free constant — exactly the R4 plug-in.
3. **The true weaker forms** `pairEq_Ncount_le_JkI` (linear) and
   `Ncount_le_card_sq` / `pairEq_Ncount_le_geomMean` (crude / CS ½-power).
4. **The sharp negative verification** `crude_exp_ge_vmvtExp`: the crude/CS route's
   effective `x`-exponent `2kr−2` satisfies `2kr−2 ≥ E(k,r)` for all `k ≥ 2`, so
   it is on the wrong side of the target — the CS fallback **does not** close R4 at
   any parameter shift; the full sublinear-in-`J` fractional form is required.
-/

namespace Salt.Vmvt

open Finset

/-! ## Part A — the self-improvement engine (pure `ℝ`) -/

/-- **The self-improvement engine.**  If a nonnegative `J` satisfies the
strictly-sublinear self-bound `J ≤ 4K · J^{1−θ}` with `0 < θ ≤ 1` and `4K ≥ 1`,
then `J` is bounded by the **`x`-free constant** `(4K)^{1/θ}`.  This is the exact
mechanism of Vaughan's `S₂ ≥ S₁` case: `J ≤ 4S₂ ≤ 4K·J^{1−θ}` forces
`J^θ ≤ 4K`, i.e. `J ≤ (4K)^{1/θ}`. -/
theorem rpow_self_improve {J K θ : ℝ} (hJ : 0 ≤ J) (hK1 : (1 : ℝ) ≤ 4 * K)
    (hθ0 : 0 < θ) (hstep : J ≤ 4 * K * J ^ (1 - θ)) :
    J ≤ (4 * K) ^ (1 / θ) := by
  have h4K : (0 : ℝ) ≤ 4 * K := le_trans zero_le_one hK1
  rcases eq_or_lt_of_le hJ with hJ0 | hJpos
  · -- `J = 0`: the constant is nonnegative.
    rw [← hJ0]; exact Real.rpow_nonneg h4K _
  · -- `J > 0`: divide out `J^{1−θ}` to isolate `J^θ ≤ 4K`, then raise to `1/θ`.
    have hpow_pos : (0 : ℝ) < J ^ (1 - θ) := Real.rpow_pos_of_pos hJpos _
    have hsplit : J = J ^ θ * J ^ (1 - θ) := by
      rw [← Real.rpow_add hJpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
    have hcancel : J ^ θ ≤ 4 * K := by
      have hs := hstep
      nth_rewrite 1 [hsplit] at hs
      exact le_of_mul_le_mul_right hs hpow_pos
    have hmono : (J ^ θ) ^ (1 / θ) ≤ (4 * K) ^ (1 / θ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hJ _) hcancel (by positivity)
    rwa [← Real.rpow_mul hJ, mul_one_div, div_self (ne_of_gt hθ0), Real.rpow_one] at hmono

/-! ## Part B — true combinatorial bounds on the pair-collapse count -/

/-- The shifted count is at most the product of the box cardinalities: the
solution set is a subset of `B ×ˢ C`. -/
theorem Ncount_le_card_sq (k b : ℕ) (ℓ : ℕ → ℤ) (B C : Finset (Fin b → ℤ)) :
    Ncount k b ℓ B C ≤ B.card * C.card := by
  unfold Ncount solSetN
  calc ((B ×ˢ C).filter fun mn => PowerSumShiftEq k b ℓ mn.1 mn.2).card
      ≤ (B ×ˢ C).card := Finset.card_filter_le _ _
    _ = B.card * C.card := Finset.card_product _ _

/-- The pair-collapse box is a sub-box of the full solution box. -/
theorem pairEqBox_subset_solBox {k b : ℕ} (x : ℕ) (e : Fin k → Fin b)
    (ab : Fin k × Fin k) : pairEqBox x e ab ⊆ solBox b x :=
  Finset.filter_subset _ _

/-- **The linear true form.**  `Ncount(D_{a=b}) ≤ J_k(x, kr)`: the pair-collapse
count is dominated by the full mean value, since `D_{a=b} ⊆ (0,x]^{kr}` (monotone
`Ncount`).  True and reusable — but *linear* in `J_k`, hence (per the flag)
circular for closing R4 on its own. -/
theorem pairEq_Ncount_le_JkI {k b : ℕ} (x : ℕ) (e : Fin k → Fin b)
    (ab : Fin k × Fin k) :
    Ncount k b 0 (pairEqBox x e ab) (pairEqBox x e ab) ≤ JkI k b x := by
  have hsub : pairEqBox x e ab ⊆ solBox b x := pairEqBox_subset_solBox x e ab
  calc Ncount k b 0 (pairEqBox x e ab) (pairEqBox x e ab)
      ≤ Ncount k b 0 (solBox b x) (solBox b x) := Ncount_mono k b 0 hsub hsub
    _ = Jk k b (Finset.Ioc (0 : ℤ) (x : ℤ)) := by
        rw [solBox]; exact Ncount_zero_eq_Jk k b _
    _ = JkI k b x := rfl

/-! ## Part C — the crude / Cauchy–Schwarz ½-power form and the `η′` negative check

The two crude true bounds `N ≤ J_k` (linear) and `N ≤ |D|²` combine to the
Cauchy–Schwarz ½-power form `N² ≤ J_k · |D|²`, i.e. `N ≤ (J_k)^{1/2}·|D|`.  This
*is* sublinear in `J_k` — but the `|D| ~ x^{kr−1}` factor makes its effective
`x`-exponent `2(kr−1) = 2kr−2` under the self-improvement, and
`crude_exp_ge_vmvtExp` shows `2kr−2 ≥ E(k,r)` for every `k ≥ 2`.  So the CS
fallback lands on the **wrong side** of the target exponent: it does *not* close
R4 at any parameter shift, and the honest analytic `1 − 1/(kr)` form is required. -/

/-- **The Cauchy–Schwarz ½-power form.**  `N² ≤ J_k(x,kr)·|D_{a=b}|²`, i.e.
`N ≤ (J_k)^{1/2}·|D|` — the `p = q = 2` Hölder case, from the two crude true
bounds `N ≤ J_k` and `N ≤ |D|²`.  Sublinear in `J_k`, but with an `x`-power that
(`crude_exp_ge_vmvtExp`) fails to beat the target. -/
theorem pairEq_Ncount_sq_le {k b : ℕ} (x : ℕ) (e : Fin k → Fin b) (ab : Fin k × Fin k) :
    (Ncount k b 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ) ^ 2
      ≤ (JkI k b x : ℝ) * ((pairEqBox x e ab).card : ℝ) ^ 2 := by
  set N := Ncount k b 0 (pairEqBox x e ab) (pairEqBox x e ab) with hN
  set c := (pairEqBox x e ab).card with hc
  have hlin : (N : ℝ) ≤ (JkI k b x : ℝ) := by exact_mod_cast pairEq_Ncount_le_JkI x e ab
  have hcrude : (N : ℝ) ≤ (c : ℝ) ^ 2 := by
    have h := Ncount_le_card_sq k b 0 (pairEqBox x e ab) (pairEqBox x e ab)
    calc (N : ℝ) ≤ ((c * c : ℕ) : ℝ) := by exact_mod_cast h
      _ = (c : ℝ) ^ 2 := by push_cast; ring
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hJ0 : (0 : ℝ) ≤ (JkI k b x : ℝ) := Nat.cast_nonneg _
  calc (N : ℝ) ^ 2 = (N : ℝ) * (N : ℝ) := by ring
    _ ≤ (JkI k b x : ℝ) * (c : ℝ) ^ 2 := mul_le_mul hlin hcrude hN0 hJ0

/-- `η(k,r) ≤ ½·k·(k−1)` for `r ≥ 1`: the exponent-decay term is largest at
`r = 1`, where `½k²(1−1/k) = ½k(k−1)`. -/
theorem vmvtEta_le {k r : ℕ} (hk : 1 ≤ k) (hr : 1 ≤ r) :
    vmvtEta k r ≤ (1 / 2) * (k : ℝ) * ((k : ℝ) - 1) := by
  unfold vmvtEta
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hinv0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one hkpos]; exact hk1
  have hbase1 : (1 - 1 / (k : ℝ)) ≤ 1 := by linarith
  have hpow : (1 - 1 / (k : ℝ)) ^ r ≤ (1 - 1 / (k : ℝ)) ^ 1 :=
    pow_le_pow_of_le_one hbase0 hbase1 hr
  rw [pow_one] at hpow
  have hk2 : (0 : ℝ) ≤ (1 / 2) * (k : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpow hk2
  refine hmul.trans_eq ?_
  field_simp

/-- **The `η′` negative verification.**  The crude / CS ½-power route's effective
`x`-exponent `2kr − 2` satisfies `E(k,r) ≤ 2kr − 2` for all `k ≥ 2`, `r ≥ 1`.
Since a bound `≤ x^{2kr−2}` therefore never beats the target `≤ D·x^{E(k,r)}`
(indeed `2kr−2 − E = ½k(k+1) − η − 2 ≥ k − 2 ≥ 0`), the CS fallback closes R4 at
*no* parameter shift — the strictly-sublinear-in-`J` fractional form is required. -/
theorem crude_exp_ge_vmvtExp {k r : ℕ} (hk : 2 ≤ k) (hr : 1 ≤ r) :
    vmvtExp k r ≤ 2 * ((k : ℝ) * (r : ℝ)) - 2 := by
  unfold vmvtExp
  have hη : vmvtEta k r ≤ (1 / 2) * (k : ℝ) * ((k : ℝ) - 1) := vmvtEta_le (by omega) hr
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [hη, hk2]

/-! ## Part D — the packaged consumer closure (the R4 plug-in)

The fractional bound is carried as the named hypothesis `PairEqFracBound` (`θ`
abstract, so a downstream proof of either the honest `θ = 1/(kr)` or the source's
`θ = 2/(kr)` slots in unchanged).  Given it and the `S₂`-dominant hypothesis
`J ≤ 4·S₂`, `pairEqDominant_JkI_le_const` delivers the `x`-free constant bound on
`J_k(x,kr)` — the entire content of Vaughan's `S₂ ≥ S₁` case, mechanized. -/

/-- **The per-pair fractional Hölder bound**, as a named hypothesis for R4.
`(Ncount(D_{a=b}) : ℝ) ≤ Cc · J_k(x,kr)^{1−θ}` for every off-diagonal pair.
`θ` is abstract (covers the honest `1/(kr)` and the source-OCR `2/(kr)`); `Cc` is
the `x`-free constant (`k⁴`-grade in the source). -/
def PairEqFracBound (k r x : ℕ) (e : Fin k → Fin (k * r)) (θ Cc : ℝ) : Prop :=
  ∀ ab ∈ offPairs k,
    (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
      ≤ Cc * (JkI k (k * r) x : ℝ) ^ (1 - θ)

/-- **Aggregation.**  The per-pair fractional bound lifts through the landed
`degenBox_Ncount_le` to `S₂ = Ncount(D₂) ≤ (#offPairs)²·Cc·J_k^{1−θ}` — the
`x`-free constant `K = (#offPairs)²·Cc` times the sublinear power. -/
theorem degen_Ncount_le_frac {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    {θ Cc : ℝ} (H : PairEqFracBound k r x e θ Cc) :
    (Ncount k (k * r) 0 (degenBox x e) (degenBox x e) : ℝ)
      ≤ ((offPairs k).card : ℝ) ^ 2 * Cc * (JkI k (k * r) x : ℝ) ^ (1 - θ) := by
  have hJpow0 : (0 : ℝ) ≤ (JkI k (k * r) x : ℝ) ^ (1 - θ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- sum over the pairs
  have hsum : ∑ ab ∈ offPairs k,
      (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
      ≤ ((offPairs k).card : ℝ) * (Cc * (JkI k (k * r) x : ℝ) ^ (1 - θ)) := by
    calc ∑ ab ∈ offPairs k,
          (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ)
        ≤ ∑ _ab ∈ offPairs k, Cc * (JkI k (k * r) x : ℝ) ^ (1 - θ) := Finset.sum_le_sum H
      _ = ((offPairs k).card : ℝ) * (Cc * (JkI k (k * r) x : ℝ) ^ (1 - θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- degenBox_Ncount_le, cast to ℝ
  have hdcast : (Ncount k (k * r) 0 (degenBox x e) (degenBox x e) : ℝ)
      ≤ ((offPairs k).card : ℝ)
          * ∑ ab ∈ offPairs k,
              (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ) := by
    calc (Ncount k (k * r) 0 (degenBox x e) (degenBox x e) : ℝ)
        ≤ (((offPairs k).card * ∑ ab ∈ offPairs k,
              Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℕ) : ℝ) := by
          exact_mod_cast degenBox_Ncount_le x e
      _ = ((offPairs k).card : ℝ)
            * ∑ ab ∈ offPairs k,
                (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ) := by
          push_cast; ring
  calc (Ncount k (k * r) 0 (degenBox x e) (degenBox x e) : ℝ)
      ≤ ((offPairs k).card : ℝ) * ∑ ab ∈ offPairs k,
          (Ncount k (k * r) 0 (pairEqBox x e ab) (pairEqBox x e ab) : ℝ) := hdcast
    _ ≤ ((offPairs k).card : ℝ)
          * (((offPairs k).card : ℝ) * (Cc * (JkI k (k * r) x : ℝ) ^ (1 - θ))) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = ((offPairs k).card : ℝ) ^ 2 * Cc * (JkI k (k * r) x : ℝ) ^ (1 - θ) := by ring

/-- **The packaged R4 closure.**  Given the per-pair fractional bound
`PairEqFracBound` and the `S₂`-dominant hypothesis `J ≤ 4·Ncount(D₂)`, the mean
value `J_k(x,kr)` is bounded by the **`x`-free constant** `(4·(#offPairs)²·Cc)^{1/θ}`.
This is the `S₂ ≥ S₁` case of Theorem 24.5, complete — the only missing ingredient
is the analytic fractional bound itself (see the file header). -/
theorem pairEqDominant_JkI_le_const {k r : ℕ} (x : ℕ) (e : Fin k → Fin (k * r))
    {θ Cc : ℝ} (hk : 2 ≤ k) (hθ0 : 0 < θ) (hCc : 1 ≤ Cc)
    (H : PairEqFracBound k r x e θ Cc)
    (hdom : (JkI k (k * r) x : ℝ)
              ≤ 4 * (Ncount k (k * r) 0 (degenBox x e) (degenBox x e) : ℝ)) :
    (JkI k (k * r) x : ℝ) ≤ (4 * (((offPairs k).card : ℝ) ^ 2 * Cc)) ^ (1 / θ) := by
  -- `#offPairs ≥ 1` from `2·#offPairs = k(k−1) ≥ 2`.
  have hoff1 : 1 ≤ (offPairs k).card := by
    have h2 : 2 * (offPairs k).card = k * (k - 1) := two_mul_offPairs_card k
    have hkk : 2 ≤ k * (k - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hoff1R : (1 : ℝ) ≤ ((offPairs k).card : ℝ) := by exact_mod_cast hoff1
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans zero_le_one hCc
  have hoffsq : (1 : ℝ) ≤ ((offPairs k).card : ℝ) ^ 2 := by
    nlinarith [hoff1R, sq_nonneg (((offPairs k).card : ℝ) - 1)]
  set K : ℝ := ((offPairs k).card : ℝ) ^ 2 * Cc with hKdef
  have hK1 : (1 : ℝ) ≤ 4 * K := by
    rw [hKdef]; nlinarith [hoffsq, hCc, hCc0, mul_nonneg (sub_nonneg.mpr hoffsq) hCc0]
  have hstep : (JkI k (k * r) x : ℝ) ≤ 4 * K * (JkI k (k * r) x : ℝ) ^ (1 - θ) := by
    calc (JkI k (k * r) x : ℝ)
        ≤ 4 * (Ncount k (k * r) 0 (degenBox x e) (degenBox x e) : ℝ) := hdom
      _ ≤ 4 * (K * (JkI k (k * r) x : ℝ) ^ (1 - θ)) := by
          have hfrac := degen_Ncount_le_frac x e H
          have hKrw : K * (JkI k (k * r) x : ℝ) ^ (1 - θ)
              = ((offPairs k).card : ℝ) ^ 2 * Cc * (JkI k (k * r) x : ℝ) ^ (1 - θ) := by
            rw [hKdef]
          rw [hKrw]; linarith [hfrac]
      _ = 4 * K * (JkI k (k * r) x : ℝ) ^ (1 - θ) := by ring
  exact rpow_self_improve (Nat.cast_nonneg _) hK1 hθ0 hstep

end Salt.Vmvt
