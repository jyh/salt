/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.CoprimeBV
import Salt.SW.MoebiusLog
import Salt.SW.DHMain

/-!
# ARM B part B2, wave **W6b-E** (S0–S4) — the coprime log-weighted Möbius sum `bvL`
# and its envelope `g/φ(g)`

The object the corpus declined twice, with the wrong envelope. `Salt/SW/CoprimeBV.lean`
built the telescope and aimed it at `h(g) = 3^{ω(g)}`; `docs/blueprints/flags.md` (DH-LCM)
then observed that `Σ_g φ(g)·9^{ω(g)}/g²` diverges. **The envelope the source actually
produces is `h(g) = g/φ(g)`** (Graham 1978 = An 2022 Lemma 3.10 at `k = ℚ`), and the same
telescope closes on it WITH EQUALITY at every step.

## The object

`bvL g w = Σ_{e ≤ ⌊w⌋, (e,g)=1} (μ(e)/e)·log(w/e)` — a REAL parameter `w`, so that the
recursion `w ↦ w/p` stays inside the object. It is exactly the bracket of the landed
`innerG_eq_coprime_sum` (`CoprimeBV.lean:184`): `innerG z g = (μ(g)/(g·log z))·bvL g (z/g)`.

## Rungs landed here

* **S0** `bvL_of_lt_one` (`⌊w⌋ = 0` kills the range) and `innerG_eq_bvL` (the bridge,
  `Nat.floor_div_natCast` for `⌊(z:ℝ)/g⌋₊ = z/g`).
* **S1** `abs_bvL_one_le` — the base `|bvL 1 w| ≤ C₀` on the REALS. For natural `w = n`,
  `bvL 1 n = log n · Σ_{e ≤ n} θ^{(n)}_e/e` is literally the landed
  `MoebiusLog.abs_sum_grahamTheta_div_le_inv_log` (`z ≥ 3`) times `log n`; the real-`w`
  transfer is `bvL 1 w = log(w/⌊w⌋)·Mw(⌊w⌋) + bvL 1 ⌊w⌋` with `|Mw| ≤ 1`
  (`DHMain.abs_mwWeighted_le_one`) and `0 ≤ log(w/⌊w⌋) ≤ 1`. The two small windows
  `⌊w⌋ ∈ {1,2}` go through the crude `|bvL g w| ≤ ⌊w⌋·log w`.
* **S2** `bvL_step` — THE TELESCOPE, at every prime `p ∤ g'`:
  `bvL (p g') w = bvL g' w + (1/p)·bvL (p g') (w/p)`. Split the coprime-to-`g'` range at
  `p ∣ e`, reindex `e = p·e'` (`CoprimeBV.sum_dvd_reindex`), and use `μ(p e') = −μ(e')`
  when `p ∤ e'`, `0` when `p ∣ e'`.
* **S3** `abs_bvL_le` — THE ENVELOPE `|bvL g w| ≤ C₀·g/φ(g)` for squarefree `g`, by a
  nested induction on the lexicographic measure `(g, ⌊w⌋₊)`: the outer strong induction
  peels a prime at the same `w`, the inner keeps `g` and drops `⌊w⌋₊` to `⌊w/p⌋₊ = ⌊w⌋₊/p`.
  The step is an IDENTITY: `g/φ(g) = (g'/φ(g'))·p/(p−1)` and `1 + 1/(p−1) = p/(p−1)`, so
  `C₀` never grows.
* **S4** `abs_innerG_le_sharp` — `|innerG z g| ≤ C₀/(φ(g)·log z)`, the sharp pointwise
  decay DH-COPBV declined (it aimed at `3^{ω(g)}/(g·log z)`, which the `g`-sum cannot pay
  for). Off squarefree `g`, `innerG z g = 0` outright.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

namespace Salt.SW

open ArithmeticFunction

/-- **The coprime log-weighted Möbius sum on the reals.**
`bvL g w = Σ_{e ≤ ⌊w⌋, (e,g)=1} (μ(e)/e)·log(w/e)`. The real parameter is what makes the
telescope `w ↦ w/p` (S2) an identity inside the object rather than between two objects. -/
noncomputable def bvL (g : ℕ) (w : ℝ) : ℝ :=
  ∑ e ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun e => Nat.Coprime e g),
    (moebius e : ℝ) / e * Real.log (w / e)

/-! ## S0 — the empty range and the bridge to `innerG` -/

/-- **S0a.** Below `1` the range `Icc 1 ⌊w⌋₊` is empty, so `bvL g w = 0`.
Exit-test row (§2(b)): `bvL g (1/2) = 0` — the off-line value is `0`. -/
theorem bvL_of_lt_one {g : ℕ} {w : ℝ} (hw : w < 1) : bvL g w = 0 := by
  have h : ⌊w⌋₊ = 0 := Nat.floor_eq_zero.mpr hw
  rw [bvL, h, Finset.Icc_eq_empty (by omega), Finset.filter_empty, Finset.sum_empty]

-- **S0's binder-shape row** (§2(b)): the hypothesis instantiates at `w = 1/2`; the
-- off-line value of `bvL g (1/2)` is `0`.
example (g : ℕ) : bvL g (1 / 2 : ℝ) = 0 := bvL_of_lt_one (by norm_num)

/-- **S0b (the bridge).** For squarefree `g ≥ 1` and `z ≥ 2`,
`innerG z g = (μ(g)/(g·log z))·bvL g (z/g)`. This is the landed
`CoprimeBV.innerG_eq_coprime_sum` read through `bvL`: the nat range `Icc 1 (z/g)` is the
real range `Icc 1 ⌊(z:ℝ)/g⌋₊` by `Nat.floor_div_natCast`, and `log(z/(g·e)) = log((z/g)/e)`. -/
theorem innerG_eq_bvL {z g : ℕ} (hz : 2 ≤ z) (hg : 1 ≤ g) (hsf : Squarefree g) :
    innerG z g = (moebius g : ℝ) / ((g : ℝ) * Real.log z) * bvL g ((z : ℝ) / g) := by
  rw [innerG_eq_coprime_sum hz hg hsf, bvL]
  have hfl : ⌊(z : ℝ) / (g : ℝ)⌋₊ = z / g := by
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  rw [hfl]
  refine congrArg _ (Finset.sum_congr rfl (fun e _ => ?_))
  rw [Nat.cast_mul, div_div]

/-! ## S1 — the base `|bvL 1 w| ≤ C₀` on the reals -/

/-- At `g = 1` the coprimality filter is vacuous (`Nat.Coprime e 1` always holds). -/
private lemma bvL_one_eq (w : ℝ) :
    bvL 1 w = ∑ e ∈ Finset.Icc 1 ⌊w⌋₊, (moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ)) := by
  rw [bvL, Finset.filter_true_of_mem (fun e _ => Nat.coprime_one_right e)]

/-- The crude size bound `|bvL g w| ≤ ⌊w⌋·log w` (triangle inequality, `|μ(e)/e| ≤ 1` and
`1 ≤ w/e ≤ w` on the range). It carries no cancellation; it serves the two small windows
`⌊w⌋ ∈ {1,2}` of S1, where the landed `z ≥ 3` rate is not available. -/
private lemma abs_bvL_le_crude {g : ℕ} {w : ℝ} (hw : 1 ≤ w) :
    |bvL g w| ≤ (⌊w⌋₊ : ℝ) * Real.log w := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw
  have hterm : ∀ e ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun e => Nat.Coprime e g),
      |(moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ))| ≤ Real.log w := by
    intro e he
    rw [Finset.mem_filter, Finset.mem_Icc] at he
    obtain ⟨⟨he1, hen⟩, -⟩ := he
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
    have he1R : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
    have hew : (e : ℝ) ≤ w :=
      le_trans (by exact_mod_cast hen : (e : ℝ) ≤ (⌊w⌋₊ : ℝ)) (Nat.floor_le hw0.le)
    have hmu : |((moebius e : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    have hlog1 : 0 ≤ Real.log (w / (e : ℝ)) := Real.log_nonneg ((one_le_div he0).mpr hew)
    have hlog2 : Real.log (w / (e : ℝ)) ≤ Real.log w :=
      Real.log_le_log (by positivity) (div_le_self hw0.le he1R)
    have hA : |((moebius e : ℤ) : ℝ)| / (e : ℝ) ≤ 1 := by
      rw [div_le_one he0]; linarith
    rw [abs_mul, abs_div, Nat.abs_cast, abs_of_nonneg hlog1]
    calc |((moebius e : ℤ) : ℝ)| / (e : ℝ) * Real.log (w / (e : ℝ))
        ≤ 1 * Real.log w := mul_le_mul hA hlog2 hlog1 (by norm_num)
      _ = Real.log w := one_mul _
  have hcard : (((Finset.Icc 1 ⌊w⌋₊).filter (fun e => Nat.Coprime e g)).card : ℝ)
      ≤ (⌊w⌋₊ : ℝ) := by
    have h := Finset.card_filter_le (Finset.Icc 1 ⌊w⌋₊) (fun e => Nat.Coprime e g)
    rw [Nat.card_Icc] at h
    exact_mod_cast le_trans h (by omega)
  calc |bvL g w|
      ≤ ∑ e ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun e => Nat.Coprime e g),
          |(moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun e => Nat.Coprime e g), Real.log w :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Icc 1 ⌊w⌋₊).filter (fun e => Nat.Coprime e g)).card : ℝ) * Real.log w := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (⌊w⌋₊ : ℝ) * Real.log w := mul_le_mul_of_nonneg_right hcard hlogw

/-- At a NATURAL parameter `n ≥ 2`, `bvL 1 n` is literally `log n` times the landed
Barban–Vehov value sum `Σ_{e ≤ n} θ^{(n)}_e/e` (`grahamTheta n e = μ(e)·log(n/e)/log n`). -/
private lemma bvL_one_natCast_eq {n : ℕ} (hn : 2 ≤ n) :
    bvL 1 (n : ℝ) = Real.log n * ∑ d ∈ Finset.Icc 1 n, grahamTheta n d / (d : ℝ) := by
  have hlogn : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
  rw [bvL_one_eq, Nat.floor_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
  rw [grahamTheta_of_le hd.2]
  field_simp

/-- **The real-parameter transfer.** `bvL 1 w = log(w/⌊w⌋)·Mw(⌊w⌋) + bvL 1 ⌊w⌋`, from
`log(w/e) = log(w/⌊w⌋) + log(⌊w⌋/e)` termwise. `Mw = mwWeighted` (`DHMain.lean:48`). -/
private lemma bvL_one_transfer {w : ℝ} (hw : 1 ≤ w) :
    bvL 1 w = Real.log (w / (⌊w⌋₊ : ℝ)) * mwWeighted ⌊w⌋₊ + bvL 1 ((⌊w⌋₊ : ℕ) : ℝ) := by
  have hn1 : 1 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw)
  have hnR : (1 : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < (⌊w⌋₊ : ℝ) := by linarith
  have hw0 : (0 : ℝ) < w := by linarith
  rw [bvL_one_eq, bvL_one_eq, Nat.floor_natCast, mwWeighted, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_Icc] at he
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he.1
  have hsplit : Real.log (w / (e : ℝ))
      = Real.log (w / (⌊w⌋₊ : ℝ)) + Real.log ((⌊w⌋₊ : ℝ) / (e : ℝ)) := by
    rw [← Real.log_mul (div_ne_zero (ne_of_gt hw0) (ne_of_gt hn0))
      (div_ne_zero (ne_of_gt hn0) (ne_of_gt he0))]
    congr 1
    field_simp
  rw [hsplit]
  ring

/-- **S1 (the base on the reals).** `∃ C₀ > 0, ∀ w ≥ 0, |bvL 1 w| ≤ C₀`.

`C₀` is NON-EFFECTIVE: it inherits `MoebiusLog.abs_sum_grahamTheta_div_le_inv_log`'s `C`,
which runs through `mmuRate_holds`'s threshold `x₀`. The route: for `⌊w⌋ ≥ 3`,
`|bvL 1 ⌊w⌋| = log⌊w⌋·|Σ_{e≤⌊w⌋} θ_e/e| ≤ C`; for `⌊w⌋ ∈ {1,2}` the crude bound gives
`≤ 2·log 2 ≤ 2`; and the transfer costs `|log(w/⌊w⌋)|·|Mw(⌊w⌋)| ≤ 1·1`. -/
theorem abs_bvL_one_le : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w : ℝ, 0 ≤ w → |bvL 1 w| ≤ C₀ := by
  obtain ⟨C, hC0, hC⟩ := abs_sum_grahamTheta_div_le_inv_log
  have hnat : ∀ m : ℕ, 1 ≤ m → |bvL 1 (m : ℝ)| ≤ C + 2 := by
    intro m hm
    rcases le_or_gt 3 m with h3 | h3
    · have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
      rw [bvL_one_natCast_eq (by omega), abs_mul, abs_of_pos hlogm]
      have hstep : Real.log (m : ℝ) * |∑ d ∈ Finset.Icc 1 m, grahamTheta m d / (d : ℝ)|
          ≤ Real.log (m : ℝ) * (C / Real.log (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (hC m h3) hlogm.le
      have hEq : Real.log (m : ℝ) * (C / Real.log (m : ℝ)) = C := by
        field_simp
      linarith
    · have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hm2 : (m : ℝ) ≤ 2 := by exact_mod_cast (by omega : m ≤ 2)
      have hcr := abs_bvL_le_crude (g := 1) (w := (m : ℝ)) hmR
      rw [Nat.floor_natCast] at hcr
      have hlogm : Real.log (m : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) by linarith)
        linarith
      have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
      have : (m : ℝ) * Real.log (m : ℝ) ≤ 2 * 1 :=
        mul_le_mul hm2 hlogm hlogm0 (by norm_num)
      linarith
  refine ⟨C + 3, by linarith, fun w _ => ?_⟩
  rcases lt_or_ge w 1 with hw1 | hw1
  · rw [bvL_of_lt_one hw1, abs_zero]; linarith
  · have hn1 : 1 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw1)
    have hnR : (1 : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < (⌊w⌋₊ : ℝ) := by linarith
    have hw0 : (0 : ℝ) < w := by linarith
    have hnw : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hw0.le
    have hwn : w < (⌊w⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one w
    have hge : (1 : ℝ) ≤ w / (⌊w⌋₊ : ℝ) := (one_le_div hn0).mpr hnw
    have hquo2 : w / (⌊w⌋₊ : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hn0]; linarith
    have hlogle : Real.log (w / (⌊w⌋₊ : ℝ)) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < w / (⌊w⌋₊ : ℝ) by linarith)
      linarith
    have h1 : |Real.log (w / (⌊w⌋₊ : ℝ))| ≤ 1 := by
      rw [abs_of_nonneg (Real.log_nonneg hge)]; exact hlogle
    have h2 : |mwWeighted ⌊w⌋₊| ≤ 1 := abs_mwWeighted_le_one hn1
    have h3 := hnat ⌊w⌋₊ hn1
    rw [bvL_one_transfer hw1]
    calc |Real.log (w / (⌊w⌋₊ : ℝ)) * mwWeighted ⌊w⌋₊ + bvL 1 ((⌊w⌋₊ : ℕ) : ℝ)|
        ≤ |Real.log (w / (⌊w⌋₊ : ℝ)) * mwWeighted ⌊w⌋₊| + |bvL 1 ((⌊w⌋₊ : ℕ) : ℝ)| :=
          abs_add_le _ _
      _ = |Real.log (w / (⌊w⌋₊ : ℝ))| * |mwWeighted ⌊w⌋₊| + |bvL 1 ((⌊w⌋₊ : ℕ) : ℝ)| := by
          rw [abs_mul]
      _ ≤ 1 * 1 + (C + 2) := by
          gcongr
      _ ≤ C + 3 := by linarith

/-! ## S2 — the telescope -/

/-- **S2 (THE TELESCOPE).** For a prime `p` not dividing `g'` and every real `w`,
`bvL (p g') w = bvL g' w + (1/p)·bvL (p g') (w/p)`.

The coprime-to-`g'` range splits at `p ∣ e`; the `p ∤ e` part IS `bvL (p g') w`, and the
`p ∣ e` part reindexes by `e = p e'` (`CoprimeBV.sum_dvd_reindex`, with
`⌊w/p⌋₊ = ⌊w⌋₊/p` by `Nat.floor_div_natCast`) into `−(1/p)·bvL (p g') (w/p)`, because
`μ(p e') = −μ(e')` when `p ∤ e'` and `μ(p e') = 0` when `p ∣ e'`.

The identity holds for EVERY real `w`; the binder `0 ≤ w` is harmless and is read below.

Exit-test rows (§2(b), BINDER-SHAPE — `Real.log` blocks `norm_num`, so the numerals live
in this docstring): at `(p, g', w) = (2, 1, 10)` the three values are
`1.7116778 = 0.9920965 + 0.7195814`; at `(3, 2, 30)` they are
`2.6092392 = 1.9049052 + 0.7043340`. -/
theorem bvL_step {g' p : ℕ} (hp : p.Prime) (hpg : ¬ p ∣ g') {w : ℝ} (hw : 0 ≤ w) :
    bvL (p * g') w = bvL g' w + (1 / (p : ℝ)) * bvL (p * g') (w / p) := by
  -- `hw` is not needed for the identity (it holds for every real `w`); it is read here.
  have _hw : (0 : ℝ) ≤ w := hw
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hfl : ⌊w / (p : ℝ)⌋₊ = ⌊w⌋₊ / p := Nat.floor_div_natCast w p
  -- `(e, p g') = 1  ↔  p ∤ e  ∧  (e, g') = 1`
  have hcopiff : ∀ e : ℕ, Nat.Coprime e (p * g') ↔ (¬ p ∣ e) ∧ Nat.Coprime e g' := by
    intro e
    rw [Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun hd => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1.symm hd), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨((hp.coprime_iff_not_dvd).mpr h1).symm, h2⟩
  -- the three objects, as `if`-sums over their nat ranges
  have hA : bvL (p * g') w
      = ∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
          (if Nat.Coprime e (p * g') then (moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ))
            else 0) := by
    rw [bvL, Finset.sum_filter]
  have hB : bvL g' w
      = ∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
          (if Nat.Coprime e g' then (moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ))
            else 0) := by
    rw [bvL, Finset.sum_filter]
  have hCp : bvL (p * g') (w / (p : ℝ))
      = ∑ e ∈ Finset.Icc 1 (⌊w⌋₊ / p),
          (if Nat.Coprime e (p * g')
            then (moebius e : ℝ) / (e : ℝ) * Real.log (w / (p : ℝ) / (e : ℝ)) else 0) := by
    rw [bvL, hfl, Finset.sum_filter]
  -- step 1: the coprime-to-`g'` range minus the coprime-to-`p g'` range is the `p ∣ e` part
  have hD : (∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
        (if Nat.Coprime e g' then (moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ)) else 0))
      - (∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
        (if Nat.Coprime e (p * g') then (moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ))
          else 0))
      = ∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
        (if p ∣ e then
          (if Nat.Coprime e g' then (moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ)) else 0)
          else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hpe : p ∣ e
    · have hnc : ¬ Nat.Coprime e (p * g') := by rw [hcopiff e]; tauto
      rw [if_pos hpe, if_neg hnc]
      ring
    · have h1 : Nat.Coprime e (p * g') ↔ Nat.Coprime e g' := by rw [hcopiff e]; tauto
      rw [if_neg hpe]
      by_cases hc : Nat.Coprime e g'
      · have hc2 : Nat.Coprime e (p * g') := h1.mpr hc
        rw [if_pos hc, if_pos hc2]; ring
      · have hc2 : ¬ Nat.Coprime e (p * g') := fun h => hc (h1.mp h)
        rw [if_neg hc, if_neg hc2]; ring
  -- step 2: reindex the `p ∣ e` part by the bijection `e = p·e'`
  have hE : (∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
        (if p ∣ e then
          (if Nat.Coprime e g' then (moebius e : ℝ) / (e : ℝ) * Real.log (w / (e : ℝ)) else 0)
          else 0))
      = ∑ e ∈ Finset.Icc 1 (⌊w⌋₊ / p),
        (if Nat.Coprime (p * e) g'
          then (moebius (p * e) : ℝ) / ((p * e : ℕ) : ℝ) * Real.log (w / ((p * e : ℕ) : ℝ))
          else 0) := by
    rw [← Finset.sum_filter]
    exact sum_dvd_reindex hp1
      (fun d => if Nat.Coprime d g' then (moebius d : ℝ) / (d : ℝ) * Real.log (w / (d : ℝ))
        else 0)
  -- step 3: `μ(p e') = −μ(e')` off `p ∣ e'` and `0` on it, so the reindexed part is
  -- `−(1/p)·bvL (p g') (w/p)`
  have hF : ∀ e ∈ Finset.Icc 1 (⌊w⌋₊ / p),
      (if Nat.Coprime (p * e) g'
        then (moebius (p * e) : ℝ) / ((p * e : ℕ) : ℝ) * Real.log (w / ((p * e : ℕ) : ℝ))
        else 0)
      = (-(1 / (p : ℝ))) * (if Nat.Coprime e (p * g')
        then (moebius e : ℝ) / (e : ℝ) * Real.log (w / (p : ℝ) / (e : ℝ)) else 0) := by
    intro e he
    rw [Finset.mem_Icc] at he
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he.1
    by_cases hpe : p ∣ e
    · have hnc : ¬ Nat.Coprime e (p * g') := by rw [hcopiff e]; tauto
      have hmu : ((moebius (p * e) : ℤ) : ℝ) = 0 := by
        have hns : ¬ Squarefree (p * e) := by
          intro hsf
          obtain ⟨k, hk⟩ := hpe
          exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p ⟨k, by rw [hk]; ring⟩))
        rw [moebius_eq_zero_of_not_squarefree hns]; norm_num
      rw [if_neg hnc, hmu]
      split_ifs <;> simp
    · have hiff : Nat.Coprime (p * e) g' ↔ Nat.Coprime e (p * g') := by
        rw [hcopiff e, Nat.coprime_mul_iff_left]
        constructor
        · rintro ⟨-, h2⟩; exact ⟨hpe, h2⟩
        · rintro ⟨-, h2⟩; exact ⟨(hp.coprime_iff_not_dvd).mpr hpg, h2⟩
      by_cases hc : Nat.Coprime (p * e) g'
      · have hcpe : Nat.Coprime p e := (hp.coprime_iff_not_dvd).mpr hpe
        have hmu : ((moebius (p * e) : ℤ) : ℝ) = -((moebius e : ℤ) : ℝ) := by
          have h := isMultiplicative_moebius.map_mul_of_coprime hcpe
          rw [moebius_apply_prime hp] at h
          have hcast : ((moebius (p * e) : ℤ) : ℝ) = ((-1 * moebius e : ℤ) : ℝ) := by
            exact_mod_cast h
          rw [hcast]; push_cast; ring
        have hlog : Real.log (w / ((p * e : ℕ) : ℝ)) = Real.log (w / (p : ℝ) / (e : ℝ)) := by
          rw [div_div, Nat.cast_mul]
        rw [if_pos hc, if_pos (hiff.mp hc), hmu, hlog, Nat.cast_mul]
        field_simp
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]
        ring
  have hG : (∑ e ∈ Finset.Icc 1 (⌊w⌋₊ / p),
        (if Nat.Coprime (p * e) g'
          then (moebius (p * e) : ℝ) / ((p * e : ℕ) : ℝ) * Real.log (w / ((p * e : ℕ) : ℝ))
          else 0))
      = (-(1 / (p : ℝ))) * bvL (p * g') (w / (p : ℝ)) := by
    rw [hCp, Finset.mul_sum]
    exact Finset.sum_congr rfl hF
  rw [hA, hB]
  linarith [hD.trans (hE.trans hG)]

-- **S2's binder-shape rows** (§2(b)): the hypotheses `p` prime, `p ∤ g'`, `0 ≤ w`
-- instantiate at `(p, g', w) = (2, 1, 10)` and `(3, 2, 30)`. The off-line values are in
-- `bvL_step`'s docstring (`1.7116778 = 0.9920965 + 0.7195814` and
-- `2.6092392 = 1.9049052 + 0.7043340`); `Real.log` blocks `norm_num`, so the EQUATION is
-- what lands, not the arithmetic.
example : bvL (2 * 1) (10 : ℝ)
    = bvL 1 (10 : ℝ) + (1 / ((2 : ℕ) : ℝ)) * bvL (2 * 1) ((10 : ℝ) / ((2 : ℕ) : ℝ)) :=
  bvL_step Nat.prime_two (by decide) (by norm_num)

example : bvL (3 * 2) (30 : ℝ)
    = bvL 2 (30 : ℝ) + (1 / ((3 : ℕ) : ℝ)) * bvL (3 * 2) ((30 : ℝ) / ((3 : ℕ) : ℝ)) :=
  bvL_step Nat.prime_three (by decide) (by norm_num)

/-! ## S3 — the envelope `g/φ(g)` -/

/-- **S3 (THE ENVELOPE).** `∃ C₀ > 0, ∀ squarefree g, ∀ w ≥ 0, |bvL g w| ≤ C₀·g/φ(g)`,
with the SAME `C₀` as S1 — the recursion closes with EQUALITY at every step.

Nested induction on `(g, ⌊w⌋₊)` (lexicographic): the outer strong induction on `g` peels
a prime `p ∣ g` at the same `w` (S2), the inner induction keeps `g` and drops `⌊w⌋₊` to
`⌊w/p⌋₊ = ⌊w⌋₊/p ≤ ⌊w⌋₊/2`. The arithmetic of the step:
`φ(p g') = (p−1)·φ(g')` (`Nat.totient_mul` on coprimes + `Nat.totient_prime`), so
`C₀·g'/φ(g') + (1/p)·C₀·(p g')/φ(p g') = C₀·(p g')/φ(p g')` EXACTLY — `1 + 1/(p−1) = p/(p−1)`.

**The must-FAIL mutation (§2(a)).** Replacing the envelope `g/φ(g)` by the constant `1` —
i.e. `∃ C₀, ∀ squarefree g, ∀ w ≥ 0, |bvL g w| ≤ C₀` — is FALSE. It breaks at THIS step:
the recursion demands `h(p g') = h(g') + h(p g')/p`, which `h ≡ 1` cannot satisfy
(`1 = 1 + 1/p`). And it is false as a statement, by UNBOUNDEDNESS over squarefree `g`:
`sup_w |bvL g w| = g/φ(g) → ∞` along the primorials — measured sups `2.000 / 3.000 /
3.749 / 4.373 / 4.807` at `g = 2 / 6 / 30 / 210 / 2310` (and, to `w ≤ 2·10⁴`,
`1.99987 / 2.99856 / 3.74431 / 4.36035` at `g = 2 / 6 / 30 / 210`). Already at `g = 2` the
envelope is non-trivial: `sup_w |bvL 2 w| → 2⁺` (`1.99987` by `w ≤ 2·10⁴`, `2.00002` by
`w = 1.4·10⁵`) against S1's `C₀ = 1.0030`. -/
theorem abs_bvL_le : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ g : ℕ, Squarefree g → ∀ w : ℝ, 0 ≤ w →
    |bvL g w| ≤ C₀ * ((g : ℝ) / Nat.totient g) := by
  obtain ⟨C₀, hC₀, hbase⟩ := abs_bvL_one_le
  have hzero : ∀ (g : ℕ) (w : ℝ), w < 1 → |bvL g w| ≤ C₀ * ((g : ℝ) / Nat.totient g) := by
    intro g w hw
    rw [bvL_of_lt_one hw, abs_zero]
    exact mul_nonneg hC₀.le (by positivity)
  have main : ∀ g : ℕ, Squarefree g → ∀ w : ℝ,
      |bvL g w| ≤ C₀ * ((g : ℝ) / Nat.totient g) := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ihg =>
      intro hg
      have inner : ∀ N : ℕ, ∀ w : ℝ, ⌊w⌋₊ ≤ N →
          |bvL g w| ≤ C₀ * ((g : ℝ) / Nat.totient g) := by
        intro N
        induction N with
        | zero =>
          intro w hwN
          exact hzero g w (Nat.floor_eq_zero.mp (Nat.le_zero.mp hwN))
        | succ N ihN =>
          intro w hwN
          rcases lt_or_ge w 1 with hw1 | hw1
          · exact hzero g w hw1
          · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hg.ne_zero) with h1 | hgt
            · -- `g = 1`: the base S1
              rw [← h1]
              simpa using hbase w (by linarith)
            · -- `g ≥ 2`: peel a prime
              obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : g ≠ 1)
              obtain ⟨g', rfl⟩ := hpd
              have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
              have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
              have hg'sf : Squarefree g' := Squarefree.squarefree_of_dvd (dvd_mul_left g' p) hg
              have hpg' : ¬ p ∣ g' := by
                rintro ⟨k, rfl⟩
                exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hg p ⟨k, by ring⟩))
              have hg'0 : 0 < g' := Nat.pos_of_ne_zero hg'sf.ne_zero
              have hg'lt : g' < p * g' := by
                calc g' = 1 * g' := (one_mul g').symm
                  _ < p * g' := (Nat.mul_lt_mul_right hg'0).mpr hp.one_lt
              have hφg' : 0 < Nat.totient g' := Nat.totient_pos.mpr hg'0
              have hφg'R : (0 : ℝ) < (Nat.totient g' : ℝ) := by exact_mod_cast hφg'
              have hcop : Nat.Coprime p g' := (hp.coprime_iff_not_dvd).mpr hpg'
              have htotR : ((Nat.totient (p * g') : ℕ) : ℝ)
                  = ((p : ℝ) - 1) * (Nat.totient g' : ℝ) := by
                rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul,
                  Nat.cast_sub hp.one_lt.le, Nat.cast_one]
              -- the inner IH applies at `w/p`
              have hflN : ⌊w / (p : ℝ)⌋₊ ≤ N := by
                rw [Nat.floor_div_natCast]
                have h2 : ⌊w⌋₊ / p ≤ ⌊w⌋₊ / 2 := Nat.div_le_div_left hp.two_le (by norm_num)
                have h3 : ⌊w⌋₊ / 2 ≤ (N + 1) / 2 := Nat.div_le_div_right hwN
                omega
              have hin := ihN (w / (p : ℝ)) hflN
              have hout := ihg g' hg'lt hg'sf w
              have hstep := bvL_step (g' := g') (p := p) hp hpg' (w := w) (by linarith)
              have hkey : C₀ * ((g' : ℝ) / Nat.totient g')
                    + (1 / (p : ℝ)) * (C₀ * (((p * g' : ℕ) : ℝ) / Nat.totient (p * g')))
                  = C₀ * (((p * g' : ℕ) : ℝ) / Nat.totient (p * g')) := by
                rw [htotR, Nat.cast_mul]
                have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
                have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
                field_simp
                ring
              calc |bvL (p * g') w|
                  ≤ |bvL g' w| + |(1 / (p : ℝ)) * bvL (p * g') (w / (p : ℝ))| := by
                    rw [hstep]; exact abs_add_le _ _
                _ = |bvL g' w| + (1 / (p : ℝ)) * |bvL (p * g') (w / (p : ℝ))| := by
                    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (p : ℝ))]
                _ ≤ C₀ * ((g' : ℝ) / Nat.totient g')
                    + (1 / (p : ℝ)) * (C₀ * (((p * g' : ℕ) : ℝ) / Nat.totient (p * g'))) := by
                    exact add_le_add hout
                      (mul_le_mul_of_nonneg_left hin (by positivity))
                _ = C₀ * (((p * g' : ℕ) : ℝ) / Nat.totient (p * g')) := hkey
      intro w
      exact inner ⌊w⌋₊ w le_rfl
  exact ⟨C₀, hC₀, fun g hg w _ => main g hg w⟩

/-! ## S4 — the sharp pointwise decay of `innerG` -/

/-- Off squarefree `g` the `g`-restricted Barban–Vehov sum vanishes outright: every `d`
with `g ∣ d` is non-squarefree, so `μ(d) = 0` and `θ_d = 0`. -/
theorem innerG_eq_zero_of_not_squarefree {z g : ℕ} (hg : ¬ Squarefree g) :
    innerG z g = 0 := by
  refine Finset.sum_eq_zero (fun d _ => ?_)
  split_ifs with hdvd
  · have hθ : grahamTheta z d = 0 := by
      by_contra h
      exact hg (Squarefree.squarefree_of_dvd hdvd (sqfree_of_grahamTheta_ne_zero h))
    rw [hθ, zero_div]
  · rfl

/-- **S4 (the sharp pointwise decay).** `∃ C₀ > 0, ∀ z ≥ 2, ∀ g ∈ [1, z],
`|innerG z g| ≤ C₀/(φ(g)·log z)`.

This is the estimate DH-COPBV (`docs/blueprints/flags.md`) declined: it aimed at
`C·3^{ω(g)}/(g·log z)`, an envelope the `g`-sum cannot pay for (DH-LCM's observation that
`Σ_g φ(g)·9^{ω(g)}/g²` diverges). With `g/φ(g)` in place of `3^{ω(g)}` the same telescope
closes, and `g/φ(g)/g = 1/φ(g)` is exactly the shape S5 needs. -/
theorem abs_innerG_le_sharp : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ z : ℕ, 2 ≤ z → ∀ g ∈ Finset.Icc 1 z,
    |innerG z g| ≤ C₀ / ((Nat.totient g : ℝ) * Real.log z) := by
  obtain ⟨C₀, hC₀, hL⟩ := abs_bvL_le
  refine ⟨C₀, hC₀, fun z hz g hg => ?_⟩
  obtain ⟨hg1, hgz⟩ := Finset.mem_Icc.mp hg
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg1
  by_cases hsf : Squarefree g
  · have hφ : 0 < Nat.totient g := Nat.totient_pos.mpr hg1
    have hφR : (0 : ℝ) < (Nat.totient g : ℝ) := by exact_mod_cast hφ
    have hmu : |((moebius g : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
    have hbnd := hL g hsf ((z : ℝ) / g) (by positivity)
    rw [innerG_eq_bvL hz hg1 hsf, abs_mul, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (g : ℝ) * Real.log (z : ℝ))]
    have hstep : |((moebius g : ℤ) : ℝ)| / ((g : ℝ) * Real.log (z : ℝ))
          * |bvL g ((z : ℝ) / g)|
        ≤ 1 / ((g : ℝ) * Real.log (z : ℝ)) * (C₀ * ((g : ℝ) / Nat.totient g)) := by
      gcongr
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  · rw [innerG_eq_zero_of_not_squarefree hsf, abs_zero]
    positivity

end Salt.SW
