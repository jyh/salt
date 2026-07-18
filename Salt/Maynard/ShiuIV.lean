/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.ShiuClasses
import Salt.Maynard.ShiuGraded
import Salt.Maynard.ShiuTuned
import Salt.Maynard.ShiuClose
import Salt.Maynard.ShiuFinal
import Salt.Maynard.Mertens

/-!
# ShiuIV — the Class IV binned assembly + the S5 close (wave W6)

This file closes the `N-SHIU-CORE` rung: `sum_tau_in_ap_le : ShiuCore`.  It lands
the last of the four per-class assemblies (Class IV, the r-binned tuned-Rankin
composition) and the S5 partition that glues deg + I + II + III + IV into the
Shiu core.

## The Class IV bin (wave W6 design)

Class IV is `shiuClassIIIIV` (`ρ = d.minFac ≤ W`, `c > W`) MINUS `shiuClassIII`
(`ρ ≤ P₀`), i.e. `P₀ < ρ ≤ W`.  We bin by the integer

    r(n) := ⌊ log z̃ / log ρ ⌋   (z̃ := W²)

so that every class-IV `n` lands in exactly one bin `r ∈ [2, R]` with
`R := ⌊ log z̃ / log P₀ ⌋` — the cover is automatic (no ladder comparison).  In
bin `r`:

* `ρ ≤ z̃^{1/r}`, so the smooth prefix `c` (primes `< ρ`) is `v_r`-smooth with
  `v_r := ⌊z̃^{1/r}⌋` and `r·log v_r ≤ log z̃` (the NEW-1′ calibration, floor);
* `ρ > z̃^{1/(r+1)}`, so `d` is `v_{r+1}`-rough and `v_{r+1}+1 > z̃^{1/(r+1)}`
  gives `Ω(d) ≤ (r+1)·log z/log z̃`, hence `τ(d) ≤ A₅^{r+1}` (`A₅ := 2^{log z/log z̃}`).

The c-sum is `sum_tau_smooth_gt_tuned_le′` (NEW-1′) at `v = v_r`, `σ_r`; the
d-count is `inner_count_le` (rough count in AP) at `t = v_{r+1}`; the fold lands
the `rsumTerm` shape summed by `rsum_tuned_le`.

## Structure

* `class_tau_sum_le_prod''` / `bigT_sum_split''` — the reindex + split carrying
  BOTH the c-domain `Sc` (smoothness) and the d-predicate `Dpred` (roughness).
-/

open Finset

namespace Salt.Maynard

/-! ## §1  The dual-predicate reindex (c-smoothness ∧ d-roughness)

`class_tau_sum_le_prod'` (ShiuFinal) carries only the `c`-domain; the class-I
`class_tau_sum_le_prod` carries only the `d`-predicate.  Class IV needs BOTH: `c`
restricted to the `v_r`-smooth prefix `> W`, and `d` restricted to the
`v_{r+1}`-rough cofactors (so the inner count is a `rough_count_in_ap_le`
instance).  These `''` variants carry both. -/

/-- **The dual-predicate reindex.**  Like `class_tau_sum_le_prod'` but the pair
set also filters `d` by `Dpred`; `hcov` must land `shiuC w n ∈ Sc ∧ Dpred (shiuD w
n)`.  Concrete decidability on both predicates (catch #73). -/
theorem class_tau_sum_le_prod'' (z q a w : ℕ) (Sc : Finset ℕ)
    (Npred : ℕ → Prop) [DecidablePred Npred]
    (Dpred : ℕ → Prop) [DecidablePred Dpred]
    (hcov : ∀ n, 1 ≤ n → n ≤ z → n % q = a → Npred n →
        shiuC w n ∈ Sc ∧ Dpred (shiuD w n)) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ Npred n),
        (n.divisors.card : ℝ)
      ≤ ∑ p ∈ ((Sc ×ˢ Finset.Icc 1 z).filter
          (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a ∧ Dpred p.2)),
          (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) := by
  classical
  set S := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ Npred n) with hSdef
  set φ : ℕ → ℕ × ℕ := fun n => (shiuC w n, shiuD w n) with hφ
  set BigT := (Sc ×ˢ Finset.Icc 1 z).filter
    (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a ∧ Dpred p.2) with hBigT
  set G : ℕ × ℕ → ℝ := fun p => (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) with hG
  have hmemS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ z ∧ n % q = a ∧ Npred n := by
    intro n hn
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨hn.1.1, hn.1.2, hn.2.1, hn.2.2⟩
  have hval : ∀ n ∈ S, (n.divisors.card : ℝ) = G (φ n) := by
    intro n hn
    obtain ⟨hn1, _, _, _⟩ := hmemS n hn
    have hn0 : n ≠ 0 := by omega
    have htau := tau_mul_shiu hn0 w
    simp only [hG, hφ]
    rw [htau]; push_cast; ring
  have hinj : Set.InjOn φ ↑S := by
    intro n hn m hm hnm
    simp only [Finset.mem_coe] at hn hm
    obtain ⟨hn1, _, _, _⟩ := hmemS n hn
    obtain ⟨hm1, _, _, _⟩ := hmemS m hm
    have hn0 : n ≠ 0 := by omega
    have hm0 : m ≠ 0 := by omega
    rw [hφ, Prod.mk.injEq] at hnm
    calc n = shiuC w n * shiuD w n := (shiuC_mul_shiuD hn0 w).symm
      _ = shiuC w m * shiuD w m := by rw [hnm.1, hnm.2]
      _ = m := shiuC_mul_shiuD hm0 w
  have hsub : S.image φ ⊆ BigT := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨n, hn, rfl⟩ := hp
    obtain ⟨hn1, hnz, hnq, hnP⟩ := hmemS n hn
    have hn0 : n ≠ 0 := by omega
    obtain ⟨hcSc, hDd⟩ := hcov n hn1 hnz hnq hnP
    have hd1 : 1 ≤ shiuD w n := shiuD_pos hn0 w
    have hc1 : 1 ≤ shiuC w n := shiuC_pos hn0 w
    have hcd : shiuC w n * shiuD w n = n := shiuC_mul_shiuD hn0 w
    have hdz : shiuD w n ≤ z := by
      have : shiuD w n ≤ shiuC w n * shiuD w n := Nat.le_mul_of_pos_left _ hc1
      omega
    rw [hBigT, hφ, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨hcSc, ⟨hd1, hdz⟩⟩, ?_, ?_, hDd⟩
    · rw [hcd]; exact hnz
    · rw [hcd]; exact hnq
  calc ∑ n ∈ S, (n.divisors.card : ℝ)
      = ∑ n ∈ S, G (φ n) := Finset.sum_congr rfl hval
    _ = ∑ p ∈ S.image φ, G p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ BigT, G p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)

/-- **The dual-predicate fibre split.**  Groups the reindexed product sum by the
smooth prefix `c ∈ Sc`, with the inner `d`-fibre carrying `Dpred`. -/
theorem bigT_sum_split'' (Sc : Finset ℕ) (z q a : ℕ) (Dpred : ℕ → Prop)
    [DecidablePred Dpred] (g : ℕ → ℝ) :
    ∑ p ∈ ((Sc ×ˢ Finset.Icc 1 z).filter
        (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a ∧ Dpred p.2)), g p.1
      = ∑ c ∈ Sc, g c *
          (((Finset.Icc 1 z).filter
            (fun d => c * d ≤ z ∧ (c * d) % q = a ∧ Dpred d)).card : ℝ) := by
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-! ## §2  The per-bin `τ(d) ≤ A₅^{r+1}` rough bound

For a `v_{r+1}`-rough cofactor `d ≤ z`, `Ω(d) ≤ (r+1)·log z/log z̃` because
`(v_{r+1}+1)^{Ω(d)} ≤ d ≤ z` and `log(v_{r+1}+1) ≥ log z̃/(r+1)`.  With the scale
hypothesis `log z ≤ Kd·log z̃` this is `Ω(d) ≤ (r+1)·Kd`, so
`τ(d) ≤ 2^{Ω(d)} ≤ exp((r+1)·Kd·log 2) = A₅^{r+1}` (`A₅ := exp(Kd·log 2)`, abstract).

The `card_div_le_two_pow_Omega` / `pow_Omega_le_of_rough` pieces are `private` in
`ShiuClasses`; reproved here (not blueprint statements). -/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

/-- `τ(m) ≤ 2^Ω(m)` (local reproof). -/
private lemma card_div_le_two_pow_Omega' {m : ℕ} (hm : m ≠ 0) :
    m.divisors.card ≤ 2 ^ Ω m := by
  rw [Nat.card_divisors hm, cardFactors_eq_sum_factorization, Finsupp.sum,
    ← Nat.support_factorization]
  calc m.factorization.support.prod (fun p => m.factorization p + 1)
      ≤ m.factorization.support.prod (fun p => 2 ^ m.factorization p) := by
        apply Finset.prod_le_prod (fun _ _ => by omega)
        intro p _
        exact Nat.succ_le_of_lt Nat.lt_two_pow_self
    _ = 2 ^ (∑ p ∈ m.factorization.support, m.factorization p) := by
        rw [← Finset.prod_pow_eq_pow_sum]

/-- If every prime factor of `d ≠ 0` is `≥ W+1`, then `(W+1)^Ω(d) ≤ d` (local reproof). -/
private lemma pow_Omega_le_of_rough' {d W : ℕ} (hd : d ≠ 0)
    (hrough : ∀ p ∈ d.primeFactors, W + 1 ≤ p) : (W + 1) ^ Ω d ≤ d := by
  have hself : ∏ p ∈ d.primeFactors, p ^ (d.factorization p) = d := by
    rw [← Nat.support_factorization, ← Finsupp.prod]
    exact Nat.prod_factorization_pow_eq_self hd
  have hOmega : Ω d = ∑ p ∈ d.primeFactors, d.factorization p := by
    rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  rw [hOmega, ← Finset.prod_pow_eq_pow_sum]
  calc ∏ p ∈ d.primeFactors, (W + 1) ^ (d.factorization p)
      ≤ ∏ p ∈ d.primeFactors, p ^ (d.factorization p) :=
        Finset.prod_le_prod' (fun p hp => Nat.pow_le_pow_left (hrough p hp) _)
    _ = d := hself

/-- **The per-bin `τ(d)` bound.**  For `1 ≤ d ≤ z` free of primes `≤ t` (`2 ≤ t`),
`Ω(d)·log(t+1) ≤ log d ≤ log z`; combined with the calibrated
`log z ≤ ((r:ℝ)+1)·K·log(t+1)` this gives `Ω(d) ≤ ((r:ℝ)+1)·K`, hence
`τ(d) ≤ exp(((r:ℝ)+1)·K·log 2)`. -/
theorem tau_rough_bin_le {d z t r : ℕ} {K : ℝ}
    (hd1 : 1 ≤ d) (hdz : d ≤ z) (ht2 : 2 ≤ t)
    (hrough : ∀ p, p.Prime → p ≤ t → ¬ p ∣ d)
    (hlogz : Real.log z ≤ ((r : ℝ) + 1) * K * Real.log ((t : ℝ) + 1)) :
    (d.divisors.card : ℝ) ≤ Real.exp (((r : ℝ) + 1) * K * Real.log 2) := by
  have hd0 : d ≠ 0 := by omega
  have hz1 : 1 ≤ z := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have htp1 : (2 : ℝ) < (t : ℝ) + 1 := by
    have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
    linarith
  have hlogtp1 : (0 : ℝ) < Real.log ((t : ℝ) + 1) := Real.log_pos (by linarith)
  -- rough ⟹ every prime factor ≥ t+1
  have hpf : ∀ p ∈ d.primeFactors, t + 1 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    by_contra h
    exact hrough p hpp (by omega) hpd
  have hpow : (t + 1) ^ Ω d ≤ d := pow_Omega_le_of_rough' hd0 hpf
  -- Ω d · log(t+1) ≤ log d ≤ log z
  have hΩlog : (Ω d : ℝ) * Real.log ((t : ℝ) + 1) ≤ Real.log z := by
    have hcast : (((t + 1) ^ Ω d : ℕ) : ℝ) ≤ (z : ℝ) := by
      exact_mod_cast (le_trans hpow hdz)
    have hlhs : (((t + 1) ^ Ω d : ℕ) : ℝ) = ((t : ℝ) + 1) ^ (Ω d) := by push_cast; ring
    rw [hlhs] at hcast
    have hlog := Real.log_le_log (by positivity) hcast
    rwa [Real.log_pow] at hlog
  -- Ω d ≤ (r+1)·K
  have hΩle : (Ω d : ℝ) ≤ ((r : ℝ) + 1) * K := by
    apply le_of_mul_le_mul_right _ hlogtp1
    calc (Ω d : ℝ) * Real.log ((t : ℝ) + 1) ≤ Real.log z := hΩlog
      _ ≤ ((r : ℝ) + 1) * K * Real.log ((t : ℝ) + 1) := hlogz
  -- τ(d) ≤ 2^{Ω d} = exp(Ω d · log 2) ≤ exp((r+1) K log 2)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc (d.divisors.card : ℝ) ≤ ((2 ^ Ω d : ℕ) : ℝ) := by
        exact_mod_cast card_div_le_two_pow_Omega' hd0
    _ = Real.exp ((Ω d : ℝ) * Real.log 2) := by
        rw [show ((2 ^ Ω d : ℕ) : ℝ) = (2 : ℝ) ^ (Ω d) by push_cast; ring,
          ← Real.rpow_natCast (2 : ℝ) (Ω d), Real.rpow_def_of_pos (by norm_num)]
        ring_nf
    _ ≤ Real.exp (((r : ℝ) + 1) * K * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hΩle hlog2.le

/-! ## §3  The bin predicate and the automatic cover

Class IV is `shiuClassIV := shiuClassIIIIV ∧ ¬shiuClassIII` (so `P₀ < ρ ≤ W`).  We
bin by `r(n) := ⌊2·log W / log ρ⌋` (`z̃ = W²`, `log z̃ = 2 log W`).  Each class-IV
`n` lands in bin `r(n) ∈ [2, R]` with `R := ⌊2·log W / log P₀⌋`, so the cover
`class IV ⊆ ⋃_{r=2}^{R} bin r` is automatic. -/

/-- Class IV: `shiuClassIIIIV` minus `shiuClassIII` (`P₀ < ρ ≤ W`). -/
def shiuClassIV (w W P₀ n : ℕ) : Prop :=
  shiuClassIIIIV w W n ∧ ¬ shiuClassIII w W P₀ n

instance (w W P₀ n : ℕ) : Decidable (shiuClassIV w W P₀ n) := by
  unfold shiuClassIV; infer_instance

/-- The bin index of `n`: `⌊2·log W / log ρ⌋` (`ρ = (shiuD w n).minFac`). -/
noncomputable def binIdx (w W n : ℕ) : ℕ :=
  ⌊(2 * Real.log W) / Real.log ((shiuD w n).minFac)⌋₊

/-- The upper bin limit `R := ⌊2·log W / log P₀⌋`. -/
noncomputable def Rbin (W P₀ : ℕ) : ℕ := ⌊(2 * Real.log W) / Real.log P₀⌋₊

/-- The bin predicate: class IV with bin index `r`. -/
def binIV (w W P₀ r n : ℕ) : Prop := shiuClassIV w W P₀ n ∧ binIdx w W n = r

noncomputable instance (w W P₀ r n : ℕ) : Decidable (binIV w W P₀ r n) := by
  unfold binIV; infer_instance

/-- **The Class IV cover.**  Every class-IV `n` lies in bin `binIdx w W n ∈ [2, R]`,
so the class-IV AP-restricted set is covered by the `biUnion` of the bins. -/
theorem shiu_classIV_cover {z q a w W P₀ : ℕ} (hW2 : 2 ≤ W) (hP2 : 2 ≤ P₀) :
    (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIV w W P₀ n)
      ⊆ (Finset.Icc 2 (Rbin W P₀)).biUnion
          (fun r => (Finset.Icc 1 z).filter (fun n => n % q = a ∧ binIV w W P₀ r n)) := by
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnz⟩, hnq, hcls⟩ := hn
  obtain ⟨⟨hd1, hρW, _hWc⟩, hnotIII⟩ := hcls
  have hn0 : n ≠ 0 := by omega
  set ρ := (shiuD w n).minFac with hρ
  have hρp : ρ.Prime := Nat.minFac_prime (by omega)
  have hρ2 : 2 ≤ ρ := hρp.two_le
  -- P₀ < ρ (from ¬shiuClassIII)
  have hP0ρ : P₀ < ρ := by
    by_contra h
    exact hnotIII ⟨⟨hd1, hρW, _hWc⟩, by omega⟩
  -- log positivity
  have hlogW : (0 : ℝ) < Real.log W := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hlogρ : (0 : ℝ) < Real.log ρ := Real.log_pos (by exact_mod_cast (by omega : 1 < ρ))
  have hlogP0 : (0 : ℝ) < Real.log P₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < P₀))
  have hlogρW : Real.log ρ ≤ Real.log W := by
    apply Real.log_le_log (by exact_mod_cast (by omega : (0:ℕ) < ρ))
    exact_mod_cast hρW
  have hlogP0ρ : Real.log P₀ ≤ Real.log ρ := by
    apply Real.log_le_log (by exact_mod_cast (by omega : (0:ℕ) < P₀))
    exact_mod_cast (le_of_lt hP0ρ)
  set r₀ := binIdx w W n with hr0
  -- r₀ ≥ 2
  have hr02 : 2 ≤ r₀ := by
    rw [hr0, binIdx, ← hρ]
    apply Nat.le_floor
    rw [Nat.cast_ofNat, le_div_iff₀ hlogρ]
    linarith [hlogρW]
  -- r₀ ≤ R
  have hr0R : r₀ ≤ Rbin W P₀ := by
    rw [hr0, binIdx, ← hρ, Rbin]
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_left (by positivity) hlogP0 hlogP0ρ
  rw [Finset.mem_biUnion]
  refine ⟨r₀, Finset.mem_Icc.mpr ⟨hr02, hr0R⟩, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hn1, hnz⟩, hnq, ⟨⟨⟨hd1, hρW, _hWc⟩, hnotIII⟩, rfl⟩⟩

/-! ## §4  The per-bin bound

For a fixed bin `r`, the smoothness cut is `v := ⌊W^{2/r}⌋` and the roughness cut
is `t := ⌊W^{2/(r+1)}⌋` (`= vCut W (r+1)`).  The reindex carries `c ∈ Sc` (the
`v`-smooth `> W` prefix) and `d` `t`-rough; `τ(d) ≤ A₅^{r+1}` pointwise, the
`c`-sum is the caller-supplied tuned Rankin `RankIV`, the `d`-count is
`inner_count_le`.  The fold lands the per-bin bound. -/

/-- The bin cut `⌊W^{2/r}⌋` (`= z̃^{1/r}` for `z̃ = W²`). -/
noncomputable def vCut (W r : ℕ) : ℕ := ⌊(W : ℝ) ^ ((2 : ℝ) / (r : ℝ))⌋₊

open Classical in
/-- **The per-bin bound.**  Parametric in the tuned Rankin `RankIV` (the NEW-1′
`c`-sum bound at `v = vCut W r`) and the rough-count constant `Crc` (via `hrc`).
`Kd` is the `τ(d)` calibration constant (`≈ log z/log z̃`). -/
theorem shiu_classIV_bin_le {z q a w W P₀ r : ℕ} (Kd Crc RankIV : ℝ)
    (hq : 1 ≤ q) (hW2 : 2 ≤ W) (hw1 : 1 ≤ w) (ha : Nat.Coprime a q)
    (hr2 : 2 ≤ r) (hCrc : 0 < Crc)
    (hrc : ∀ y q a t : ℕ, 1 ≤ q → 2 ≤ t → Nat.Coprime a q →
      (((Finset.Icc 1 y).filter (fun m => m % q = a ∧
          ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)).card : ℝ)
        ≤ Crc * ((y : ℝ) / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3))
    (ht2 : 2 ≤ vCut W (r + 1))
    (hNew : ∑ c ∈ (Finset.Icc 1 w).filter
        (fun c => (∀ p ∈ c.primeFactors, p ≤ vCut W r) ∧ W < c),
        (c.divisors.card : ℝ) / (c : ℝ) ≤ RankIV)
    (hlogz_td : Real.log z ≤ ((r : ℝ) + 1) * Kd *
        Real.log ((vCut W (r + 1) : ℝ) + 1)) :
    (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ binIV w W P₀ r n),
        (n.divisors.card : ℝ))
      ≤ Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) * Crc *
          (RankIV * ((z : ℝ) / (q.totient : ℝ) / Real.log (vCut W (r + 1)))
            + (vCut W (r + 1) : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))) := by
  classical
  set v := vCut W r with hvdef
  set t := vCut W (r + 1) with htdef
  set A5r := Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) with hA5r
  set Sc := (Finset.Icc 1 w).filter
    (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c) with hScdef
  set Dpred : ℕ → Prop := fun d => ∀ p, p.Prime → p ≤ t → ¬ p ∣ d with hDpred
  have hA5nn : 0 ≤ A5r := (Real.exp_pos _).le
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (by omega : 0 < W)
  have hlogW : (0 : ℝ) < Real.log W := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1pos : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  -- cover : the class-IV set restricted to bin r reindexes with c ∈ Sc ∧ d t-rough
  have hcov : ∀ n, 1 ≤ n → n ≤ z → n % q = a → binIV w W P₀ r n →
      shiuC w n ∈ Sc ∧ Dpred (shiuD w n) := by
    intro n hn1 _ _ hbin
    obtain ⟨⟨⟨hd1, hρW, hWc⟩, _hnotIII⟩, hidx⟩ := hbin
    have hn0 : n ≠ 0 := by omega
    set ρ := (shiuD w n).minFac with hρ
    have hρp : ρ.Prime := Nat.minFac_prime (by omega)
    have hρ2 : 2 ≤ ρ := hρp.two_le
    have hlogρ : (0 : ℝ) < Real.log ρ := Real.log_pos (by exact_mod_cast (by omega : 1 < ρ))
    -- from ⌊2logW/logρ⌋ = r : r ≤ 2logW/logρ < r+1
    have hidx' : ⌊(2 * Real.log W) / Real.log ρ⌋₊ = r := by
      have hh := hidx; unfold binIdx at hh; rw [← hρ] at hh; exact hh
    have hxnn : (0 : ℝ) ≤ (2 * Real.log W) / Real.log ρ := by positivity
    have hrle : (r : ℝ) ≤ (2 * Real.log W) / Real.log ρ := by
      have := Nat.floor_le hxnn; rw [hidx'] at this; exact this
    have hltr1 : (2 * Real.log W) / Real.log ρ < (r : ℝ) + 1 := by
      have := Nat.lt_floor_add_one ((2 * Real.log W) / Real.log ρ)
      rw [hidx'] at this; exact_mod_cast this
    -- ρ ≤ W^{2/r}
    have hρub : (ρ : ℝ) ≤ (W : ℝ) ^ ((2 : ℝ) / (r : ℝ)) := by
      have hlog : Real.log ρ ≤ Real.log ((W : ℝ) ^ ((2 : ℝ) / (r : ℝ))) := by
        rw [Real.log_rpow hWR]
        rw [le_div_iff₀ hlogρ] at hrle
        rw [div_mul_eq_mul_div, le_div_iff₀ hrpos]
        nlinarith [hrle]
      have := Real.exp_le_exp.mpr hlog
      rwa [Real.exp_log (by exact_mod_cast (by omega : 0 < ρ)),
        Real.exp_log (Real.rpow_pos_of_pos hWR _)] at this
    -- W^{2/(r+1)} < ρ
    have hρlb : (W : ℝ) ^ ((2 : ℝ) / ((r : ℝ) + 1)) < (ρ : ℝ) := by
      have hlog : Real.log ((W : ℝ) ^ ((2 : ℝ) / ((r : ℝ) + 1))) < Real.log ρ := by
        rw [Real.log_rpow hWR]
        rw [div_lt_iff₀ hlogρ] at hltr1
        rw [div_mul_eq_mul_div, div_lt_iff₀ hr1pos]
        nlinarith [hltr1]
      have := Real.exp_lt_exp.mpr hlog
      rwa [Real.exp_log (Real.rpow_pos_of_pos hWR _),
        Real.exp_log (by exact_mod_cast (by omega : 0 < ρ))] at this
    refine ⟨?_, ?_⟩
    · -- shiuC ∈ Sc
      rw [hScdef, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨shiuC_pos hn0 w, shiuC_le hw1 n⟩, ?_, hWc⟩
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpdvd := Nat.dvd_of_mem_primeFactors hp
      have hplt := shiuC_prime_lt_minFac hn0 hd1 hpp hpdvd
      rw [← hρ] at hplt
      -- p < ρ ≤ W^{2/r}, so p ≤ ⌊W^{2/r}⌋ = v
      have hpR : (p : ℝ) ≤ (W : ℝ) ^ ((2 : ℝ) / (r : ℝ)) := by
        have : (p : ℝ) < (ρ : ℝ) := by exact_mod_cast hplt
        linarith [hρub]
      rw [hvdef, vCut]
      exact Nat.le_floor hpR
    · -- shiuD t-rough
      rw [hDpred, htdef, vCut]
      intro p hpp hpt hpd
      have hmf : ρ ≤ p := by rw [hρ]; exact Nat.minFac_le_of_dvd hpp.two_le hpd
      have htlt : ((⌊(W : ℝ) ^ ((2 : ℝ) / ((r + 1 : ℕ) : ℝ))⌋₊ : ℕ) : ℝ) < (ρ : ℝ) := by
        have hfl : ((⌊(W : ℝ) ^ ((2 : ℝ) / ((r + 1 : ℕ) : ℝ))⌋₊ : ℕ) : ℝ)
            ≤ (W : ℝ) ^ ((2 : ℝ) / ((r + 1 : ℕ) : ℝ)) := Nat.floor_le (by positivity)
        have hcast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hfl ⊢; linarith [hρlb]
      have : (p : ℝ) < (ρ : ℝ) := lt_of_le_of_lt (by exact_mod_cast hpt) htlt
      have : p < ρ := by exact_mod_cast this
      omega
  -- reindex
  have hreindex := class_tau_sum_le_prod'' z q a w Sc (binIV w W P₀ r) Dpred hcov
  set BigT := (Sc ×ˢ Finset.Icc 1 z).filter
    (fun p => p.1 * p.2 ≤ z ∧ (p.1 * p.2) % q = a ∧ Dpred p.2) with hBigT
  -- τ(d) ≤ A5r on BigT
  have hstep : ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ)
      ≤ ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * A5r := by
    apply Finset.sum_le_sum
    intro p hp
    rw [hBigT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨_, hd1, hdz⟩, _, _, hrough⟩ := hp
    have htaud : (p.2.divisors.card : ℝ) ≤ A5r := by
      rw [hA5r]
      exact tau_rough_bin_le hd1 hdz ht2 hrough hlogz_td
    exact mul_le_mul_of_nonneg_left htaud (by positivity)
  -- split
  have hsplit := bigT_sum_split'' Sc z q a Dpred (fun c => (c.divisors.card : ℝ) * A5r)
  -- per-c count
  have hpercterm : ∀ c ∈ Sc, ((c.divisors.card : ℝ) * A5r) *
      (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a ∧ Dpred d)).card : ℝ)
      ≤ (c.divisors.card : ℝ) * A5r *
          (Crc * ((z : ℝ) / c / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3)) := by
    intro c hc
    rw [hScdef, Finset.mem_filter, Finset.mem_Icc] at hc
    have hc1 : 1 ≤ c := hc.1.1
    have hcount : (((Finset.Icc 1 z).filter
          (fun d => c * d ≤ z ∧ (c * d) % q = a ∧ Dpred d)).card : ℝ)
        ≤ Crc * ((z : ℝ) / c / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3) :=
      inner_count_le Crc hCrc hrc z q a c t hq hc1 ht2 ha
    have hnn : (0 : ℝ) ≤ (c.divisors.card : ℝ) * A5r := mul_nonneg (by positivity) hA5nn
    exact mul_le_mul_of_nonneg_left hcount hnn
  -- the two smooth sums
  have hTauSc : ∑ c ∈ Sc, (c.divisors.card : ℝ) ≤ (w : ℝ) * (1 + Real.log w) := by
    calc ∑ c ∈ Sc, (c.divisors.card : ℝ)
        ≤ ∑ c ∈ Finset.Icc 1 w, (c.divisors.card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (by rw [hScdef]; exact Finset.filter_subset _ _)
            (fun c _ _ => by positivity)
      _ ≤ (w : ℝ) * (1 + Real.log w) := Salt.BV.sum_card_divisors_le w hw1
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by
    have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
    linarith)
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  -- algebra
  have halg : ∑ c ∈ Sc, (c.divisors.card : ℝ) * A5r *
        (Crc * ((z : ℝ) / c / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3))
      = A5r * Crc * ((z : ℝ) / (q.totient : ℝ) / Real.log t)
            * (∑ c ∈ Sc, (c.divisors.card : ℝ) / (c : ℝ))
          + A5r * Crc * ((t : ℝ) ^ 3) * (∑ c ∈ Sc, (c.divisors.card : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro c _; ring
  -- assemble
  calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ binIV w W P₀ r n),
          (n.divisors.card : ℝ)
      ≤ ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * (p.2.divisors.card : ℝ) := hreindex
    _ ≤ ∑ p ∈ BigT, (p.1.divisors.card : ℝ) * A5r := hstep
    _ = ∑ c ∈ Sc, ((c.divisors.card : ℝ) * A5r) *
          (((Finset.Icc 1 z).filter (fun d => c * d ≤ z ∧ (c * d) % q = a ∧ Dpred d)).card : ℝ) :=
        hsplit
    _ ≤ ∑ c ∈ Sc, (c.divisors.card : ℝ) * A5r *
          (Crc * ((z : ℝ) / c / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3)) :=
        Finset.sum_le_sum hpercterm
    _ = A5r * Crc * ((z : ℝ) / (q.totient : ℝ) / Real.log t)
            * (∑ c ∈ Sc, (c.divisors.card : ℝ) / (c : ℝ))
          + A5r * Crc * ((t : ℝ) ^ 3) * (∑ c ∈ Sc, (c.divisors.card : ℝ)) := halg
    _ ≤ A5r * Crc * ((z : ℝ) / (q.totient : ℝ) / Real.log t) * RankIV
          + A5r * Crc * ((t : ℝ) ^ 3) * ((w : ℝ) * (1 + Real.log w)) := by
        have hcoef1 : (0 : ℝ) ≤ A5r * Crc * ((z : ℝ) / (q.totient : ℝ) / Real.log t) :=
          mul_nonneg (mul_nonneg hA5nn hCrc.le)
            (div_nonneg (div_nonneg (by positivity) hφpos.le) hlogt.le)
        have hcoef2 : (0 : ℝ) ≤ A5r * Crc * ((t : ℝ) ^ 3) :=
          mul_nonneg (mul_nonneg hA5nn hCrc.le) (by positivity)
        exact add_le_add (mul_le_mul_of_nonneg_left hNew hcoef1)
          (mul_le_mul_of_nonneg_left hTauSc hcoef2)
    _ = Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) * Crc *
          (RankIV * ((z : ℝ) / (q.totient : ℝ) / Real.log (vCut W (r + 1)))
            + (vCut W (r + 1) : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))) := by
        rw [← hA5r, ← htdef]; ring

/-! ## §5  `vCut` ladder helpers (for the assembly) -/

/-- `vCut W r ≤ W^{2/r}` (floor). -/
lemma vCut_le_rpow (W r : ℕ) : (vCut W r : ℝ) ≤ (W : ℝ) ^ ((2 : ℝ) / (r : ℝ)) :=
  Nat.floor_le (by positivity)

/-- `W^{2/r} < vCut W r + 1`. -/
lemma rpow_lt_vCut_succ (W r : ℕ) : (W : ℝ) ^ ((2 : ℝ) / (r : ℝ)) < (vCut W r : ℝ) + 1 :=
  Nat.lt_floor_add_one _

/-- `vCut` is antitone in the index (`2/r` decreasing, base `W ≥ 1`). -/
lemma vCut_antitone {W r s : ℕ} (hW : 1 ≤ W) (hr : 1 ≤ r) (hrs : r ≤ s) :
    vCut W s ≤ vCut W r := by
  unfold vCut
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW)
  apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast (by omega : 0 < r))
  exact_mod_cast hrs

/-- The calibration `r·log(vCut W r) ≤ 2·log W` (from `vCut W r ≤ W^{2/r}`). -/
lemma r_mul_log_vCut_le {W r : ℕ} (hW : 1 ≤ W) (hr : 1 ≤ r) (hv1 : 1 ≤ vCut W r) :
    (r : ℝ) * Real.log (vCut W r) ≤ 2 * Real.log W := by
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (by omega : 0 < W)
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlog : Real.log (vCut W r) ≤ (2 : ℝ) / (r : ℝ) * Real.log W := by
    calc Real.log (vCut W r) ≤ Real.log ((W : ℝ) ^ ((2 : ℝ) / (r : ℝ))) :=
          Real.log_le_log (by exact_mod_cast hv1) (vCut_le_rpow W r)
      _ = (2 : ℝ) / (r : ℝ) * Real.log W := Real.log_rpow hWR _
  rw [div_mul_eq_mul_div] at hlog
  rw [le_div_iff₀ hrpos] at hlog
  nlinarith [hlog]

/-- `log x ≤ 2·log⌊x⌋` for `⌊x⌋ ≥ 2` (via `⌊x⌋² ≥ x`). -/
lemma log_le_two_log_floor {x : ℝ} (hx : 0 < x) (hf : 2 ≤ ⌊x⌋₊) :
    Real.log x ≤ 2 * Real.log (⌊x⌋₊ : ℝ) := by
  have hfR : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hf
  have hxlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hsq : x ≤ (⌊x⌋₊ : ℝ) ^ 2 := by nlinarith [hxlt, hfR]
  calc Real.log x ≤ Real.log ((⌊x⌋₊ : ℝ) ^ 2) := Real.log_le_log hx hsq
    _ = 2 * Real.log (⌊x⌋₊ : ℝ) := by rw [Real.log_pow]; push_cast; ring

/-! ## §6  The per-bin collapse (NEW-1′ + per-bin + `rsumTerm` shape) -/

open Classical in
/-- **The per-bin collapse.**  Instantiates NEW-1′ (`hnew`, the `∀`-body of
`sum_tau_smooth_gt_tuned_le'` with constants `Cek, Cnk`) at `v = vCut W r`, feeds the
resulting Rankin into `shiu_classIV_bin_le`, and collapses the main term to the
`rsumTerm (2·A₅) Cnk r` shape (`A₅ := exp(Kd·log 2)`) via the grade bound
`log(W²) ≤ 2(r+1)·log(vCut W (r+1))` and `2(r+1)·A₅^{r+1} ≤ 4A₅·(2A₅)^r`. -/
theorem shiu_classIV_bin_collapse {z q a w W P₀ r : ℕ} (Kd Crc Cek Cnk : ℝ)
    (hq : 1 ≤ q) (hW2 : 2 ≤ W) (hw1 : 1 ≤ w) (ha : Nat.Coprime a q)
    (hr2 : 2 ≤ r) (hCrc : 0 < Crc) (hKd0 : 0 ≤ Kd)
    (hrc : ∀ y q a t : ℕ, 1 ≤ q → 2 ≤ t → Nat.Coprime a q →
      (((Finset.Icc 1 y).filter (fun m => m % q = a ∧
          ∀ p, p.Prime → p ≤ t → ¬ p ∣ m)).card : ℝ)
        ≤ Crc * ((y : ℝ) / (q.totient : ℝ) / Real.log t + (t : ℝ) ^ 3))
    (hnew : ∀ (N Z r v W : ℕ) (σ : ℝ),
      3 ≤ v → 2 ≤ r → 1 ≤ W → 1 < Z →
      (r : ℝ) * Real.log r ≤ Real.log Z →
      Real.log W = (1 / 2) * Real.log Z →
      (r : ℝ) * Real.log v ≤ Real.log Z →
      σ = 1 - (r : ℝ) * Real.log r / (4 * Real.log Z) →
      ∑ c ∈ (Finset.Icc 1 N).filter (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
          (c.divisors.card : ℝ) / (c : ℝ)
        ≤ Real.exp (-((r : ℝ) * Real.log r) / 8
              + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + Cnk))
          * Real.exp (2 * ∑ p ∈ (Finset.range (Z + 1)).filter Nat.Prime, (p : ℝ)⁻¹ + Cek))
    (hv3 : 3 ≤ vCut W r) (ht2 : 2 ≤ vCut W (r + 1))
    (hrr : (r : ℝ) * Real.log r ≤ 2 * Real.log W)
    (hKd : Real.log z ≤ Kd * Real.log ((W : ℝ) ^ 2)) :
    (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ binIV w W P₀ r n),
        (n.divisors.card : ℝ))
      ≤ Crc * Real.exp (2 * ∑ p ∈ (Finset.range (W ^ 2 + 1)).filter Nat.Prime, (p : ℝ)⁻¹ + Cek)
          * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
          * (4 * Real.exp (Kd * Real.log 2)) * rsumTerm (2 * Real.exp (Kd * Real.log 2)) Cnk r
        + Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))
            * Real.exp (Kd * Real.log 2) ^ (r + 1) := by
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (by omega : 0 < W)
  have hlogW : (0 : ℝ) < Real.log W := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  set A5 := Real.exp (Kd * Real.log 2) with hA5def
  have hA5pos : (0 : ℝ) < A5 := Real.exp_pos _
  have hA51 : (1 : ℝ) ≤ A5 := Real.one_le_exp (mul_nonneg hKd0 (Real.log_nonneg (by norm_num)))
  -- log (W²) facts
  have hlogW2 : Real.log ((W : ℝ) ^ 2) = 2 * Real.log W := by
    rw [Real.log_pow]; push_cast; ring
  have hlogW2pos : (0 : ℝ) < Real.log ((W : ℝ) ^ 2) := by rw [hlogW2]; linarith
  have hlogW2cast : Real.log ((W ^ 2 : ℕ) : ℝ) = Real.log ((W : ℝ) ^ 2) := by push_cast; ring
  -- NEW-1′ at (w, W², r, vCut W r, W, σ)
  set v := vCut W r with hvdef
  have hv1 : 1 ≤ vCut W r := by omega
  set σ := 1 - (r : ℝ) * Real.log r / (4 * Real.log ((W ^ 2 : ℕ) : ℝ)) with hσdef
  have hNew : ∑ c ∈ (Finset.Icc 1 w).filter
        (fun c => (∀ p ∈ c.primeFactors, p ≤ v) ∧ W < c),
        (c.divisors.card : ℝ) / (c : ℝ)
      ≤ Real.exp (-((r : ℝ) * Real.log r) / 8
            + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + Cnk))
        * Real.exp (2 * ∑ p ∈ (Finset.range (W ^ 2 + 1)).filter Nat.Prime, (p : ℝ)⁻¹ + Cek) := by
    have := hnew w (W ^ 2) r v W σ hv3 hr2 (by omega) (by nlinarith [hW2] : 1 < W ^ 2)
      (by rw [hlogW2cast, hlogW2]; exact hrr)
      (by rw [hlogW2cast, hlogW2]; ring)
      (by rw [hlogW2cast, hlogW2]; exact r_mul_log_vCut_le (by omega) (by omega) hv1)
      hσdef
    exact this
  -- the per-bin bound
  have hbin := shiu_classIV_bin_le (P₀ := P₀) Kd Crc _ hq hW2 hw1 ha hr2 hCrc hrc ht2 hNew
    (by
      -- hlogz_td : log z ≤ (r+1)·Kd·log(vCut W (r+1) + 1)
      have hsucc : (W : ℝ) ^ ((2 : ℝ) / ((r : ℝ) + 1)) < (vCut W (r + 1) : ℝ) + 1 := by
        have := rpow_lt_vCut_succ W (r + 1)
        rwa [show ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 by push_cast; ring] at this
      have hlogsucc : Real.log ((W : ℝ) ^ ((2 : ℝ) / ((r : ℝ) + 1)))
          ≤ Real.log ((vCut W (r + 1) : ℝ) + 1) :=
        Real.log_le_log (Real.rpow_pos_of_pos hWR _) hsucc.le
      rw [Real.log_rpow hWR] at hlogsucc
      -- (2/(r+1))·logW = log(W²)/(r+1)
      have hkey : Real.log ((W : ℝ) ^ 2) ≤ ((r : ℝ) + 1) * Real.log ((vCut W (r + 1) : ℝ) + 1) := by
        rw [hlogW2]
        have hr1pos : (0 : ℝ) < (r : ℝ) + 1 := by linarith
        rw [div_mul_eq_mul_div, div_le_iff₀ hr1pos] at hlogsucc
        nlinarith [hlogsucc]
      calc Real.log z ≤ Kd * Real.log ((W : ℝ) ^ 2) := hKd
        _ ≤ Kd * (((r : ℝ) + 1) * Real.log ((vCut W (r + 1) : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hkey hKd0
        _ = ((r : ℝ) + 1) * Kd * Real.log ((vCut W (r + 1) : ℝ) + 1) := by ring)
  -- collapse the per-bin bound
  set t := vCut W (r + 1) with htdef
  have htR : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have ht2R : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  set Efac := Real.exp (2 * ∑ p ∈ (Finset.range (W ^ 2 + 1)).filter Nat.Prime, (p : ℝ)⁻¹ + Cek)
    with hEfacdef
  have hEfacpos : (0 : ℝ) < Efac := Real.exp_pos _
  set G := Real.exp (-((r : ℝ) * Real.log r) / 8
    + (r : ℝ) ^ (1 / 4 : ℝ) * (Real.log r / 2 + Cnk)) with hGdef
  have hGpos : (0 : ℝ) < G := Real.exp_pos _
  -- A5^{r+1} = exp((r+1)Kd log2)
  have hA5pow : Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) = A5 ^ (r + 1) := by
    rw [hA5def, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  -- grade bound : log(W²) ≤ 2(r+1) log t
  have hgrade : Real.log ((W : ℝ) ^ 2) ≤ 2 * ((r : ℝ) + 1) * Real.log t := by
    have hx : (0 : ℝ) < (W : ℝ) ^ ((2 : ℝ) / ((r : ℝ) + 1)) := Real.rpow_pos_of_pos hWR _
    have hfloor : (⌊(W : ℝ) ^ ((2 : ℝ) / ((r : ℝ) + 1))⌋₊ : ℕ) = t := by
      rw [htdef, vCut]; congr 1; push_cast; ring
    have hlog2f := log_le_two_log_floor hx (by rw [hfloor]; exact ht2)
    rw [hfloor, Real.log_rpow hWR] at hlog2f
    -- (2/(r+1))·logW ≤ 2 log t  ⟹  log(W²) = 2 logW ≤ 2(r+1) log t
    have hr1pos : (0 : ℝ) < (r : ℝ) + 1 := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hr1pos] at hlog2f
    rw [hlogW2]; nlinarith [hlog2f]
  -- 1/log t ≤ 2(r+1)/log(W²)
  have hinvt : (1 : ℝ) / Real.log t ≤ 2 * ((r : ℝ) + 1) / Real.log ((W : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ hlogt hlogW2pos, one_mul]; linarith [hgrade]
  -- main term collapse
  have hcollapse : Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) * Crc * (G * Efac)
        * ((z : ℝ) / (q.totient : ℝ) / Real.log t)
      ≤ Crc * Efac * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
          * (4 * A5) * rsumTerm (2 * A5) Cnk r := by
    rw [hA5pow]
    -- z/φ/log t = (z/φ)·(1/log t) ≤ (z/φ)·2(r+1)/log(W²)
    have hzφ : (0 : ℝ) ≤ (z : ℝ) / (q.totient : ℝ) :=
      div_nonneg (by positivity) hφpos.le
    have hstep1 : (z : ℝ) / (q.totient : ℝ) / Real.log t
        ≤ (z : ℝ) / (q.totient : ℝ) * (2 * ((r : ℝ) + 1) / Real.log ((W : ℝ) ^ 2)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinvt hzφ
    have hcoefnn : (0 : ℝ) ≤ A5 ^ (r + 1) * Crc * (G * Efac) := by positivity
    calc A5 ^ (r + 1) * Crc * (G * Efac) * ((z : ℝ) / (q.totient : ℝ) / Real.log t)
        ≤ A5 ^ (r + 1) * Crc * (G * Efac)
            * ((z : ℝ) / (q.totient : ℝ) * (2 * ((r : ℝ) + 1) / Real.log ((W : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left hstep1 hcoefnn
      _ = Crc * Efac * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
            * (2 * ((r : ℝ) + 1) * A5 ^ (r + 1) * G) := by
          ring
      _ ≤ Crc * Efac * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
            * (4 * A5 * rsumTerm (2 * A5) Cnk r) := by
          have hbasenn : (0 : ℝ) ≤ Crc * Efac * ((z : ℝ) / (q.totient : ℝ))
              / Real.log ((W : ℝ) ^ 2) := by positivity
          apply mul_le_mul_of_nonneg_left _ hbasenn
          -- 2(r+1) A5^{r+1} G ≤ 4 A5 (2A5)^r G
          have hrpow : ((r : ℝ) + 1) ≤ (2 : ℝ) ^ (r + 1) := by
            have := Nat.lt_two_pow_self (n := r + 1)
            calc ((r : ℝ) + 1) = ((r + 1 : ℕ) : ℝ) := by push_cast; ring
              _ ≤ ((2 ^ (r + 1) : ℕ) : ℝ) := by exact_mod_cast this.le
              _ = (2 : ℝ) ^ (r + 1) := by push_cast; ring
          have hAr : (0 : ℝ) ≤ A5 ^ (r + 1) := by positivity
          have hkey2 : 2 * ((r : ℝ) + 1) * A5 ^ (r + 1) ≤ 4 * A5 * (2 * A5) ^ r := by
            have h1 : 2 * ((r : ℝ) + 1) * A5 ^ (r + 1) ≤ 2 * (2 : ℝ) ^ (r + 1) * A5 ^ (r + 1) := by
              apply mul_le_mul_of_nonneg_right _ hAr
              nlinarith [hrpow]
            calc 2 * ((r : ℝ) + 1) * A5 ^ (r + 1)
                ≤ 2 * (2 : ℝ) ^ (r + 1) * A5 ^ (r + 1) := h1
              _ = 4 * A5 * (2 * A5) ^ r := by rw [mul_pow]; ring
          rw [rsumTerm, ← hGdef]
          calc 2 * ((r : ℝ) + 1) * A5 ^ (r + 1) * G
              ≤ 4 * A5 * (2 * A5) ^ r * G := mul_le_mul_of_nonneg_right hkey2 hGpos.le
            _ = 4 * A5 * ((2 * A5) ^ r * G) := by ring
      _ = Crc * Efac * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
            * (4 * A5) * rsumTerm (2 * A5) Cnk r := by ring
  -- junk term
  have hjunk : Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) * Crc
        * ((t : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)))
      ≤ Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) * A5 ^ (r + 1) := by
    rw [hA5pow]
    have htW : (t : ℝ) ≤ (W : ℝ) := by
      rw [htdef, vCut]
      calc (⌊(W : ℝ) ^ ((2 : ℝ) / ((r + 1 : ℕ) : ℝ))⌋₊ : ℝ)
          ≤ (W : ℝ) ^ ((2 : ℝ) / ((r + 1 : ℕ) : ℝ)) := Nat.floor_le (by positivity)
        _ ≤ (W : ℝ) ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ W))
            rw [div_le_one (by positivity)]
            have hrge : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
            push_cast; linarith
        _ = (W : ℝ) := Real.rpow_one _
    have hwnn : (0 : ℝ) ≤ (w : ℝ) * (1 + Real.log w) := by
      have : (0 : ℝ) ≤ 1 + Real.log w := by
        have := Real.log_nonneg (by exact_mod_cast hw1 : (1 : ℝ) ≤ (w : ℝ)); linarith
      positivity
    have ht3W3 : (t : ℝ) ^ 3 ≤ (W : ℝ) ^ 3 := by gcongr
    have hAnn : (0 : ℝ) ≤ A5 ^ (r + 1) := by positivity
    calc A5 ^ (r + 1) * Crc * ((t : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)))
        ≤ A5 ^ (r + 1) * Crc * ((W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right ht3W3 hwnn
      _ = Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) * A5 ^ (r + 1) := by ring
  -- assemble
  calc (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ binIV w W P₀ r n),
          (n.divisors.card : ℝ))
      ≤ Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) * Crc *
          ((G * Efac) * ((z : ℝ) / (q.totient : ℝ) / Real.log (vCut W (r + 1)))
            + (vCut W (r + 1) : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))) := hbin
    _ = Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) * Crc * (G * Efac)
            * ((z : ℝ) / (q.totient : ℝ) / Real.log t)
          + Real.exp (((r : ℝ) + 1) * Kd * Real.log 2) * Crc
            * ((t : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))) := by rw [← htdef]; ring
    _ ≤ Crc * Efac * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
          * (4 * A5) * rsumTerm (2 * A5) Cnk r
        + Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) * A5 ^ (r + 1) :=
        add_le_add hcollapse hjunk

/-! ## §7  The Class IV assembly (`shiu_classIV_le`) -/

open Classical in
/-- **Class IV (the binned assembly).**  Summing the per-bin collapse over the bins
`r ∈ [2, R]` (`R := Rbin W P₀`), the tuned Rankin r-sum converges (`rsum_tuned_le`,
constant `B`), and the class-IV τ-mass in the reduced progression is bounded by a
main term of grade `(z/φ(q))·(Euler factor)/log(W²)` plus a `z^{o(1)}`-junk term
(`W³·w(1+log w)·Σ_r A₅^{r+1}`).  Parametric in `Kd` (`≈ log z/log z̃`); the scale
hypotheses (relating `W, P₀, R` to `z`) are discharged by S5. -/
theorem shiu_classIV_le (Kd : ℝ) (hKd0 : 0 ≤ Kd) :
    ∃ (Cmain Cjunk : ℝ), 0 ≤ Cmain ∧ 0 ≤ Cjunk ∧
    ∀ (z q a w W P₀ : ℕ),
      1 ≤ q → 2 ≤ W → 1 ≤ w → Nat.Coprime a q → 2 ≤ P₀ → 2 ≤ Rbin W P₀ →
      3 ≤ vCut W (Rbin W P₀) → 2 ≤ vCut W (Rbin W P₀ + 1) →
      (Rbin W P₀ : ℝ) * Real.log (Rbin W P₀) ≤ 2 * Real.log W →
      Real.log z ≤ Kd * Real.log ((W : ℝ) ^ 2) →
      (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIV w W P₀ n),
          (n.divisors.card : ℝ))
        ≤ Cmain
            * Real.exp (2 * ∑ p ∈ (Finset.range (W ^ 2 + 1)).filter Nat.Prime, (p : ℝ)⁻¹)
            * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
          + Cjunk * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))
            * (∑ r ∈ Finset.Icc 2 (Rbin W P₀), Real.exp (Kd * Real.log 2) ^ (r + 1)) := by
  obtain ⟨Cek, Cnk, hCek0, hCnk0, hnew⟩ := sum_tau_smooth_gt_tuned_le'
  obtain ⟨Crc, hCrc, hrc⟩ := rough_count_in_ap_le
  set A5 := Real.exp (Kd * Real.log 2) with hA5def
  have hA5pos : (0 : ℝ) < A5 := Real.exp_pos _
  have hA51 : (1 : ℝ) ≤ A5 :=
    Real.one_le_exp (mul_nonneg hKd0 (Real.log_nonneg (by norm_num)))
  have h2A51 : (1 : ℝ) ≤ 2 * A5 := by linarith
  obtain ⟨B, hB0, hBle⟩ := rsum_tuned_le h2A51 hCnk0
  have hCmain0 : (0 : ℝ) ≤ Crc * Real.exp Cek * 4 * A5 * B :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCrc.le (Real.exp_pos _).le)
      (by norm_num)) hA5pos.le) hB0
  refine ⟨Crc * Real.exp Cek * 4 * A5 * B, Crc, hCmain0, hCrc.le, ?_⟩
  intro z q a w W P₀ hq hW2 hw1 ha hP2 hR2 hvR3 htR2 hRlogR hKd
  set R := Rbin W P₀ with hRdef
  have hW1 : 1 ≤ W := by omega
  have hlogW : (0 : ℝ) < Real.log W := Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  set E := ∑ p ∈ (Finset.range (W ^ 2 + 1)).filter Nat.Prime, (p : ℝ)⁻¹ with hEdef
  set Efac := Real.exp (2 * E + Cek) with hEfacdef
  -- per-r scale facts
  have hv3r : ∀ r, 2 ≤ r → r ≤ R → 3 ≤ vCut W r := fun r hr2 hrR =>
    le_trans hvR3 (vCut_antitone hW1 (by omega) hrR)
  have ht2r : ∀ r, 2 ≤ r → r ≤ R → 2 ≤ vCut W (r + 1) := fun r hr2 hrR =>
    le_trans htR2 (vCut_antitone hW1 (by omega) (by omega))
  have hrrr : ∀ r, 2 ≤ r → r ≤ R → (r : ℝ) * Real.log r ≤ 2 * Real.log W := by
    intro r hr2 hrR
    have hrRr : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
    have hlogrR : Real.log r ≤ Real.log R :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < r)) hrRr
    have hlogr0 : (0 : ℝ) ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
    have hRr0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
    calc (r : ℝ) * Real.log r ≤ (R : ℝ) * Real.log R := mul_le_mul hrRr hlogrR hlogr0 hRr0
      _ ≤ 2 * Real.log W := hRlogR
  -- per-r collapse bound
  have hpb : ∀ r ∈ Finset.Icc 2 R,
      (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ binIV w W P₀ r n),
          (n.divisors.card : ℝ))
        ≤ Crc * Efac * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
            * (4 * A5) * rsumTerm (2 * A5) Cnk r
          + Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) * A5 ^ (r + 1) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    exact shiu_classIV_bin_collapse Kd Crc Cek Cnk hq hW2 hw1 ha hr.1 hCrc hKd0 hrc hnew
      (hv3r r hr.1 hr.2) (ht2r r hr.1 hr.2) (hrrr r hr.1 hr.2) hKd
  -- sum: cover, then bound each bin
  have hcover := shiu_classIV_cover (z := z) (q := q) (a := a) (w := w) (W := W) (P₀ := P₀) hW2 hP2
  set K := Crc * Efac * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2) * (4 * A5) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef, hA5def, hEfacdef]
    have hlogW2 : (0 : ℝ) < Real.log ((W : ℝ) ^ 2) := by
      rw [Real.log_pow]; positivity
    have : (0 : ℝ) ≤ Crc * Real.exp (2 * E + Cek) * ((z : ℝ) / (q.totient : ℝ)) := by positivity
    apply mul_nonneg (div_nonneg this hlogW2.le)
    positivity
  have hJ0 : (0 : ℝ) ≤ Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) := by
    have : (0 : ℝ) ≤ 1 + Real.log w :=
      by have := Real.log_nonneg (by exact_mod_cast hw1 : (1 : ℝ) ≤ (w : ℝ)); linarith
    positivity
  calc (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIV w W P₀ n),
          (n.divisors.card : ℝ))
      ≤ ∑ n ∈ (Finset.Icc 2 R).biUnion
          (fun r => (Finset.Icc 1 z).filter (fun n => n % q = a ∧ binIV w W P₀ r n)),
          (n.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => by positivity)
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
          ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ binIV w W P₀ r n),
            (n.divisors.card : ℝ) :=
        sum_biUnion_le_of_nonneg _ _ (fun n => by positivity)
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
          (K * rsumTerm (2 * A5) Cnk r
            + Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w)) * A5 ^ (r + 1)) :=
        Finset.sum_le_sum hpb
    _ = K * (∑ r ∈ Finset.Icc 2 R, rsumTerm (2 * A5) Cnk r)
          + Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))
            * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ K * B
          + Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))
            * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hBle R) hK0) (le_refl _)
    _ = (Crc * Real.exp Cek * 4 * A5 * B)
            * Real.exp (2 * E)
            * ((z : ℝ) / (q.totient : ℝ)) / Real.log ((W : ℝ) ^ 2)
          + Crc * (W : ℝ) ^ 3 * ((w : ℝ) * (1 + Real.log w))
            * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1)) := by
        rw [hKdef, hEfacdef, Real.exp_add]; ring

end Salt.Maynard
