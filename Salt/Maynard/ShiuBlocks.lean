/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehDecomp
import Salt.Maynard.GehTypeI
import Salt.Maynard.TauSpike
import Salt.Maynard.FrontierDischarge
import Salt.Maynard.GehPp2
import Salt.LS.PhiSum
import Salt.BV.DivisorSum

/-!
# The Shiu shallow interface (`N-SHIU`): discharging `hshiu` for the vP3 family

This file supplies the *shallow-block* analytic content of the anchored
multiblock combinator (`pieceObligationU_of_anchored_multiblock`,
`Salt/Maynard/GehAnchor.lean`).  For the double-dyadic vP3 family
(`α i = muBlock a`, `β i = tiiBlock b`, `N i = nScale a`, `M i = nScale b`), a
block is *shallow* when its anchor `s = 2·N·M` is `< x/(log x)^F`; those blocks
are routed through `hshiu` rather than `GEH_min`.

## Architecture (recon-verified two regimes; no divisor-summatory mass needed)

The key simplification over the naive plan: the coprime **mean** term of
`seqDiscrepancy` is an *average* over the `φ(q)` reduced residue classes, so
`|Mean|/φ(q) ≤ classBd(q)` for any per-class bound `classBd(q)` on the residue
sums (`seqDiscrepancy_le_two_classBd`).  Hence the whole summed obligation
reduces to `∑_q 2·classBd(q)`, and the crude `ℓ¹`-mass bound plays no role.

`f := dconv (muBlock a x) (tiiBlock b x)` is supported on `[1, z]`,
`z := 4·nScale a x·nScale b x = 2·s` (`dconv_block_eq_zero`), with the pointwise
bound `|f n| ≤ τ(n)·log x` for `1 ≤ n ≤ x` (`abs_dconv_block_le`).  For each
modulus `q` in the range `[1, ⌊x^θ/log^Bsh⌋]` (so `q ≤ x^θ`), the residue-class
sum splits at `q = z^{1-1/8000}`:

* **`q ≤ z^{1-1/8000}` (Shiu range)** — `|R_a| ≤ log x·∑_{n≤z,n≡a(q)} τ(n) ≤
  C·(z/φ(q))·log z·log x` via the **Shiu core** `sum_tau_in_ap_le` (milestone 2).
  Summed against `∑_q 1/φ(q) ≤ 4(1+log Q)`: `≈ z·log³x ≈ x/log^{F-3}`, closing
  vs `x/log^{A'}` for `F ≥ A'+3`.
* **`q > z^{1-1/8000}`** — crude count `#{n≤z,n≡a(q)} ≤ z/q+1 ≤ z^{1/8000}+1` and
  `|f| ≤ C_ε z^{1/16000} log x` (`card_divisors_le_rpow`).  Summed (`≤ Q` terms):
  `≈ x^{θ+1/8000+1/16000} log x = x^{1-1/16000} log x`, beaten by `x/log^{A'}`.

The elementary assembly (`shiu_for_blocks_of_core`) takes the Shiu core as an
explicit hypothesis; `sum_tau_in_ap_le` is the single named analytic residual.
-/

namespace Salt.Maynard

open Finset
open scoped ArithmeticFunction ArithmeticFunction.Moebius
open ArithmeticFunction

/-! ## §0  Elementary block-convolution facts -/

/-- `|μ|`-bound for the dyadic `μ`-block: `|muBlock a x d| ≤ 1`. -/
theorem abs_muBlock_le_one (a x d : ℕ) : |muBlock a x d| ≤ 1 := by
  simp only [muBlock]
  split_ifs with _h
  · exact_mod_cast abs_moebius_le_one
  · rw [abs_zero]; exact zero_le_one

/-- `|tiiBlock b x m| ≤ log m` for `m ≥ 1` (via `typeIIData ≤ log m`, `≥ 0`). -/
theorem abs_tiiBlock_le_log {b x m : ℕ} (hm : 1 ≤ m) :
    |tiiBlock b x m| ≤ Real.log m := by
  have hlogm : (0 : ℝ) ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  simp only [tiiBlock]
  split_ifs with _h
  · rw [abs_of_nonneg (Salt.LS.typeIIData_nonneg _ _)]
    exact Salt.LS.typeIIData_le_log _ _
  · rw [abs_zero]; exact hlogm

/-- **Support of the block convolution.**  `dconv (muBlock a x) (tiiBlock b x)`
vanishes above `z = 4·nScale a x·nScale b x` (the top of the product support). -/
theorem dconv_block_eq_zero {a b x n : ℕ}
    (hn : 4 * nScale a x * nScale b x < n) :
    dconv (muBlock a x) (tiiBlock b x) n = 0 :=
  dconv_eq_zero_of_support
    (fun m hm => (coeffAt_muBlock a x m).1 hm)
    (fun m hm => tiiBlock_support b x m hm) hn

/-- **The pointwise block bound.**  For `1 ≤ n ≤ x`,
`|dconv (muBlock a x) (tiiBlock b x) n| ≤ τ(n)·log x` (triangle over the divisor
sum; `|muBlock| ≤ 1`, `|tiiBlock (n/d)| ≤ log(n/d) ≤ log x`). -/
theorem abs_dconv_block_le {a b x n : ℕ} (hn1 : 1 ≤ n) (hnx : n ≤ x) :
    |dconv (muBlock a x) (tiiBlock b x) n| ≤ (n.divisors.card : ℝ) * Real.log x := by
  have hlogx0 : (0 : ℝ) ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (le_trans hn1 hnx))
  unfold dconv
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ d ∈ n.divisors, |muBlock a x d * tiiBlock b x (n / d)| ≤ Real.log x := by
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hnd1 : 1 ≤ n / d := Nat.one_le_div_iff (by omega) |>.mpr (Nat.le_of_dvd (by omega) hdvd)
    have hndn : n / d ≤ n := Nat.div_le_self n d
    have hndx : (n / d : ℕ) ≤ x := le_trans hndn hnx
    rw [abs_mul]
    calc |muBlock a x d| * |tiiBlock b x (n / d)|
        ≤ 1 * Real.log (n / d : ℕ) :=
          mul_le_mul (abs_muBlock_le_one a x d) (abs_tiiBlock_le_log hnd1)
            (abs_nonneg _) (by norm_num)
      _ = Real.log (n / d : ℕ) := one_mul _
      _ ≤ Real.log x :=
          Real.log_le_log (by exact_mod_cast hnd1) (by exact_mod_cast hndx)
  calc ∑ d ∈ n.divisors, |muBlock a x d * tiiBlock b x (n / d)|
      ≤ ∑ _d ∈ n.divisors, Real.log x := Finset.sum_le_sum hterm
    _ = (n.divisors.card : ℝ) * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §1  The reduced-class average bound -/

/-- Count of `[1, z]` in a residue class mod `q` (`q ≥ 1`): `≤ z/q + 1`. -/
theorem card_ap_le {z q : ℕ} (hq : 1 ≤ q) (a : ℕ) :
    (((Finset.Icc 1 z).filter (fun n => n % q = a)).card : ℝ) ≤ (z : ℝ) / q + 1 := by
  have hnat : ((Finset.Icc 1 z).filter (fun n => n % q = a)).card ≤ z / q + 1 := by
    classical
    have h : ((Finset.Icc 1 z).filter (fun n => n % q = a)).card
        ≤ (Finset.range (z / q + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun m => m / q)
      · intro m hm
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
        simp only [Finset.mem_coe, Finset.mem_range]
        have : m / q ≤ z / q := Nat.div_le_div_right hm.1.2
        omega
      · intro m₁ hm₁ m₂ hm₂ heq
        rw [Finset.mem_coe, Finset.mem_filter] at hm₁ hm₂
        have hqe : m₁ / q = m₂ / q := heq
        have h1 := Nat.div_add_mod m₁ q
        have h2 := Nat.div_add_mod m₂ q
        rw [hqe, hm₁.2] at h1
        rw [hm₂.2] at h2
        exact h1.symm.trans h2
    rwa [Finset.card_range] at h
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  calc (((Finset.Icc 1 z).filter (fun n => n % q = a)).card : ℝ)
      ≤ ((z / q + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((z / q : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (z : ℝ) / q + 1 := by have := Nat.cast_div_le (α := ℝ) (m := z) (n := q); linarith

/-- The reduced-residue count equals `φ(q)`. -/
theorem card_coprime_residues (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  apply Finset.filter_congr
  intro a _
  exact Nat.coprime_comm

/-- **The reduced-class average bound.**  If every reduced residue class sum of a
weight `f` (cutoff `y`, modulus `q ≠ 0`) is bounded by `Cb`, then the whole
`seqDiscrepancy` is `≤ 2·Cb`: the residue term is `≤ Cb`, and the coprime mean —
the average of the `φ(q)` reduced-class sums — is also `≤ Cb`. -/
theorem seqDiscrepancy_le_two_classBd {f : ℕ → ℝ} {y q : ℕ} {Cb : ℝ}
    (hq : q ≠ 0)
    (hCb : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        |∑ n ∈ Finset.Icc 1 y, if n % q = a then f n else 0| ≤ Cb) :
    seqDiscrepancy f y q ≤ 2 * Cb := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqpos
  rw [seqDiscrepancy_eq f y q hq]
  refine Finset.sup'_le _ _ (fun a ha => ?_)
  set R := fun a => ∑ n ∈ Finset.Icc 1 y, if n % q = a then f n else 0 with hRdef
  have hRa : |R a| ≤ Cb := hCb a ha
  have hMean : |∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0|
      ≤ (q.totient : ℝ) * Cb := by
    rw [coprimeMeanSum_eq_sum_residues f y q hqpos]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), |R a|
        ≤ ∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), Cb :=
          Finset.sum_le_sum hCb
      _ = (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) * Cb := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (q.totient : ℝ) * Cb := by rw [card_coprime_residues]
  have hMeanDiv : |(∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0)
      / (q.totient : ℝ)| ≤ Cb := by
    rw [abs_div, abs_of_pos hφpos, div_le_iff₀ hφpos]
    calc |∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0|
        ≤ (q.totient : ℝ) * Cb := hMean
      _ = Cb * (q.totient : ℝ) := by ring
  calc |R a - (∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0) / (q.totient : ℝ)|
      ≤ |R a| + |(∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0)
          / (q.totient : ℝ)| := abs_sub _ _
    _ ≤ Cb + Cb := add_le_add hRa hMeanDiv
    _ = 2 * Cb := by ring

/-! ## §2  The two per-class regime bounds (weight-generic) -/

/-- **Crude regime residue bound.**  For a weight `f` supported on `[1, z]` with
`|f| ≤ G`, and a modulus `q ≥ z^{1-1/8000}`, every residue-class sum is
`≤ (z^{1/8000} + 1)·G` (crude count `z/q + 1 ≤ z^{1/8000} + 1`). -/
theorem class_bound_crude {G : ℝ} (hG : 0 ≤ G)
    {f : ℕ → ℝ} {z : ℕ} (hsupp : ∀ n, z < n → f n = 0)
    (hbd : ∀ n, 1 ≤ n → |f n| ≤ G)
    {q r y : ℕ} (hq1 : 1 ≤ q) (hz1 : 1 ≤ z)
    (hqz : (z : ℝ) ^ (1 - (1 : ℝ) / 8000) ≤ (q : ℝ)) :
    |∑ n ∈ Finset.Icc 1 y, if n % q = r then f n else 0|
      ≤ ((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * G := by
  rw [← Finset.sum_filter]
  set S := (Finset.Icc 1 y).filter (fun n => n % q = r) with hS
  have step1 : |∑ n ∈ S, f n| ≤ ∑ n ∈ S.filter (fun n => n ≤ z), G := by
    calc |∑ n ∈ S, f n| ≤ ∑ n ∈ S, |f n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S, (if n ≤ z then G else 0) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
          by_cases hnz : n ≤ z
          · rw [if_pos hnz]; exact hbd n hn.1.1
          · rw [if_neg hnz, hsupp n (by omega)]; simp
      _ = ∑ n ∈ S.filter (fun n => n ≤ z), G := (Finset.sum_filter _ _).symm
  have hsub : S.filter (fun n => n ≤ z)
      ⊆ (Finset.Icc 1 z).filter (fun n => n % q = r) := by
    intro n hn
    rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn.1.1.1, hn.2⟩, hn.1.2⟩
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hzα : (0 : ℝ) < (z : ℝ) ^ (1 - (1 : ℝ) / 8000) := Real.rpow_pos_of_pos hzpos _
  have hzq : (z : ℝ) / q ≤ (z : ℝ) ^ ((1 : ℝ) / 8000) := by
    have h1 : (z : ℝ) / q ≤ (z : ℝ) / (z : ℝ) ^ (1 - (1 : ℝ) / 8000) :=
      div_le_div_of_nonneg_left hzpos.le hzα hqz
    have h2 : (z : ℝ) / (z : ℝ) ^ (1 - (1 : ℝ) / 8000) = (z : ℝ) ^ ((1 : ℝ) / 8000) := by
      rw [div_eq_iff hzα.ne', ← Real.rpow_add hzpos]
      have : (1 : ℝ) / 8000 + (1 - 1 / 8000) = 1 := by ring
      rw [this, Real.rpow_one]
    exact h1.trans_eq h2
  calc |∑ n ∈ S, f n|
      ≤ ∑ n ∈ S.filter (fun n => n ≤ z), G := step1
    _ = ((S.filter (fun n => n ≤ z)).card : ℝ) * G := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Finset.Icc 1 z).filter (fun n => n % q = r)).card : ℝ) * G :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hG
    _ ≤ ((z : ℝ) / q + 1) * G := mul_le_mul_of_nonneg_right (card_ap_le hq1 r) hG
    _ ≤ ((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * G :=
        mul_le_mul_of_nonneg_right (by linarith [hzq]) hG

/-- **Shiu regime residue bound.**  For a weight `f` supported on `[1, z]` with
`|f n| ≤ τ(n)·L`, a modulus `q ≤ z^{1-1/8000}`, and `(r, q) = 1`, the reduced
residue-class sum is `≤ C·(z/φ(q))·log z·L` — the Shiu core `hcore` bounding the
`τ`-summatory in the residue class. -/
theorem class_bound_shiu {C L : ℝ} (hL : 0 ≤ L)
    (hcore : ∀ z' q' a' : ℕ, 2 ≤ z' → 1 ≤ q' →
        (q' : ℝ) ≤ (z' : ℝ) ^ (1 - (1 : ℝ) / 8000) → Nat.Coprime a' q' →
        (∑ n ∈ (Finset.Icc 1 z').filter (fun n => n % q' = a'), (n.divisors.card : ℝ))
          ≤ C * ((z' : ℝ) / (q'.totient : ℝ)) * Real.log z')
    {f : ℕ → ℝ} {z : ℕ} (hsupp : ∀ n, z < n → f n = 0)
    (hbd : ∀ n, 1 ≤ n → |f n| ≤ (n.divisors.card : ℝ) * L)
    {q r y : ℕ} (hq1 : 1 ≤ q) (hz2 : 2 ≤ z)
    (hqz : (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000)) (hcop : Nat.Coprime r q) :
    |∑ n ∈ Finset.Icc 1 y, if n % q = r then f n else 0|
      ≤ C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L := by
  rw [← Finset.sum_filter]
  set S := (Finset.Icc 1 y).filter (fun n => n % q = r) with hS
  have step1 : |∑ n ∈ S, f n|
      ≤ ∑ n ∈ S.filter (fun n => n ≤ z), (n.divisors.card : ℝ) * L := by
    calc |∑ n ∈ S, f n| ≤ ∑ n ∈ S, |f n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S, (if n ≤ z then (n.divisors.card : ℝ) * L else 0) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
          by_cases hnz : n ≤ z
          · rw [if_pos hnz]; exact hbd n hn.1.1
          · rw [if_neg hnz, hsupp n (by omega)]; simp
      _ = ∑ n ∈ S.filter (fun n => n ≤ z), (n.divisors.card : ℝ) * L :=
          (Finset.sum_filter _ _).symm
  have hsub : S.filter (fun n => n ≤ z)
      ⊆ (Finset.Icc 1 z).filter (fun n => n % q = r) := by
    intro n hn
    rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hn.1.1.1, hn.2⟩, hn.1.2⟩
  have step2 : ∑ n ∈ S.filter (fun n => n ≤ z), (n.divisors.card : ℝ) * L
      ≤ ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = r), (n.divisors.card : ℝ) * L :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg (by positivity) hL)
  have hcore' := hcore z q r hz2 hq1 hqz hcop
  calc |∑ n ∈ S, f n|
      ≤ ∑ n ∈ S.filter (fun n => n ≤ z), (n.divisors.card : ℝ) * L := step1
    _ ≤ ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = r), (n.divisors.card : ℝ) * L := step2
    _ = (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = r), (n.divisors.card : ℝ)) * L := by
        rw [Finset.sum_mul]
    _ ≤ (C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z) * L :=
        mul_le_mul_of_nonneg_right hcore' hL
    _ = C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L := by ring

/-! ## §3  The Shiu core (analytic residual, milestone 2) and the assembly -/

/-- **The Shiu core** (`sum_tau_in_ap_le`, milestone 2): the divisor function
summed over a reduced residue class `n ≡ a (q)` in `[1, z]`, for `q ≤ z^{1-1/8000}`
and `(a,q) = 1`, is `≤ C·(z/φ(q))·log z`.  This is the single named analytic
residual the shallow interface depends on. -/
def ShiuCore : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z q a : ℕ, 2 ≤ z → 1 ≤ q →
    (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000) → Nat.Coprime a q →
    (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a), (n.divisors.card : ℝ))
      ≤ C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z

private lemma exists_log_ge (M : ℝ) : ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → M ≤ Real.log x := by
  refine ⟨⌈Real.exp M⌉₊ + 1, fun x hx => ?_⟩
  have hxR : Real.exp M ≤ (x : ℝ) := by
    have h1 : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp M⌉₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    push_cast at h2; linarith
  calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos M) hxR

/-- **The shallow interface, conditional on the Shiu core.**  For the vP3
double-dyadic family, every saving `A'` with `F ≥ A'+3` admits a haircut `Bsh = 0`
and constant `Csh` bounding the summed AP discrepancy of every shallow block by
`Csh·x/(log x)^{A'}`.  `ShiuCore` supplies the sliver regime; the bulk regime is
unconditional (`card_divisors_le_rpow`). -/
theorem shiu_for_blocks_of_core (hcore : ShiuCore) (A' F : ℝ)
    (hA' : 0 < A') (hFfloor : A' + 3 ≤ F) :
    ∃ Bsh Csh : ℝ, 0 ≤ Bsh ∧ ∀ x : ℕ, 3 ≤ x → ∀ a b : ℕ,
      ((2 * nScale a x * nScale b x : ℕ) : ℝ) < (x : ℝ) / Real.log x ^ F → ∀ y : ℕ, y ≤ x →
        (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (3999 / 4000 : ℝ) / Real.log x ^ Bsh⌋₊,
            seqDiscrepancy (dconv (muBlock a x) (tiiBlock b x)) y q)
          ≤ Csh * (x : ℝ) / Real.log x ^ A' := by
  obtain ⟨C, hC0, hcorebd⟩ := hcore
  obtain ⟨Cε, hCε0, hCεbd⟩ := card_divisors_le_rpow (1 / 16000) (by norm_num)
  have hposδ : (0 : ℝ) < 1 / 16000 := by norm_num
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually
      (eventually_poly_beats_polylog ⌈A' + 1⌉₊ (1 / 16000) (12 * Cε / (64 * C)) hposδ))
  obtain ⟨X2, hX2⟩ := exists_log_ge 2
  set XC : ℕ := max (max X1 X2) 3 with hXCdef
  have hXC3 : 3 ≤ XC := le_max_right _ _
  have hXCpos : (0 : ℝ) < (XC : ℝ) := by positivity
  have hlogXC : (0 : ℝ) < Real.log XC := Real.log_pos (by exact_mod_cast (by omega : 1 < XC))
  set Kc : ℝ :=
    2 * (XC : ℝ) * (1 + Real.log XC) * Real.log XC * Real.log XC ^ A' with hKcdef
  set Csh : ℝ := max Kc (128 * C) with hCshdef
  have hKc_le : Kc ≤ Csh := le_max_left _ _
  have h128_le : 128 * C ≤ Csh := le_max_right _ _
  refine ⟨0, Csh, le_refl 0, fun x hx a b hshallow y hyx => ?_⟩
  rw [Real.rpow_zero, div_one]
  -- Common notation.
  set f : ℕ → ℝ := dconv (muBlock a x) (tiiBlock b x) with hf
  set L : ℝ := Real.log x with hLdef
  set Q : ℕ := ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ with hQdef
  have hx1 : 1 ≤ x := by omega
  have hxR3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLpos : (0 : ℝ) < L := Real.log_pos (by linarith)
  have hL0 : (0 : ℝ) ≤ L := hLpos.le
  have hLA'pos : (0 : ℝ) < L ^ A' := Real.rpow_pos_of_pos hLpos A'
  have hxθ_le : (x : ℝ) ^ (3999 / 4000 : ℝ) ≤ (x : ℝ) := by
    calc (x : ℝ) ^ (3999 / 4000 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _
  have hQx : (Q : ℝ) ≤ (x : ℝ) :=
    le_trans (Nat.floor_le (Real.rpow_nonneg hxpos.le _)) hxθ_le
  rcases lt_or_ge x XC with hlt | hxge
  · -- Corner: 3 ≤ x < XC, crude universal bound folded into `Kc ≤ Csh`.
    have hxXC : (x : ℝ) < (XC : ℝ) := by exact_mod_cast hlt
    have hLXC : L < Real.log XC := Real.log_lt_log hxpos hxXC
    -- mass bound: `∑_{n≤x} |f n| ≤ L·x·(1+L)`.
    have hmass : ∑ n ∈ Finset.Icc 1 x, |f n| ≤ L * ((x : ℝ) * (1 + L)) := by
      calc ∑ n ∈ Finset.Icc 1 x, |f n|
          ≤ ∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ) * L := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_Icc] at hn
            exact abs_dconv_block_le hn.1 hn.2
        _ = L * ∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
        _ ≤ L * ((x : ℝ) * (1 + L)) :=
            mul_le_mul_of_nonneg_left (Salt.BV.sum_card_divisors_le x hx1) hL0
    -- ∑_q seqDiscrepancy ≤ Q · 2 · mass.
    have hsumcrude : (∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy f y q)
        ≤ (Q : ℝ) * (2 * (L * ((x : ℝ) * (1 + L)))) := by
      calc (∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy f y q)
          ≤ ∑ _q ∈ Finset.Icc 1 Q, 2 * (L * ((x : ℝ) * (1 + L))) := by
            apply Finset.sum_le_sum
            intro q _
            refine (seqDiscrepancy_le_two_mul_sum_abs f y q).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right hyx) (fun n _ _ => abs_nonneg _)) hmass
        _ = (Q : ℝ) * (2 * (L * ((x : ℝ) * (1 + L)))) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            push_cast [Nat.add_sub_cancel]; ring
    -- Fold into `Kc ≤ Csh`.
    have hcornerkey : (Q : ℝ) * (2 * (L * ((x : ℝ) * (1 + L)))) ≤ Csh * (x : ℝ) / L ^ A' := by
      have hbound : (2 : ℝ) * (Q : ℝ) * (1 + L) * L * L ^ A' ≤ Kc := by
        have h1 : (Q : ℝ) ≤ (XC : ℝ) := le_trans hQx (le_of_lt hxXC)
        have h2 : (1 : ℝ) + L ≤ 1 + Real.log XC := by linarith
        have h3 : L ≤ Real.log XC := le_of_lt hLXC
        have h4 : L ^ A' ≤ Real.log XC ^ A' :=
          Real.rpow_le_rpow hL0 (le_of_lt hLXC) hA'.le
        have hpos5 : (0 : ℝ) ≤ Real.log XC ^ A' := Real.rpow_nonneg hlogXC.le _
        calc (2 : ℝ) * (Q : ℝ) * (1 + L) * L * L ^ A'
            ≤ 2 * (XC : ℝ) * (1 + Real.log XC) * Real.log XC * Real.log XC ^ A' := by
              gcongr
        _ = Kc := by rw [hKcdef]
      have hid : (Q : ℝ) * (2 * (L * ((x : ℝ) * (1 + L))))
          = ((2 : ℝ) * (Q : ℝ) * (1 + L) * L * L ^ A') * ((x : ℝ) / L ^ A') := by
        field_simp
      rw [hid]
      calc ((2 : ℝ) * (Q : ℝ) * (1 + L) * L * L ^ A') * ((x : ℝ) / L ^ A')
          ≤ Kc * ((x : ℝ) / L ^ A') :=
            mul_le_mul_of_nonneg_right hbound (by positivity)
        _ ≤ Csh * ((x : ℝ) / L ^ A') :=
            mul_le_mul_of_nonneg_right hKc_le (by positivity)
        _ = Csh * (x : ℝ) / L ^ A' := by ring
    exact le_trans hsumcrude hcornerkey
  · -- Main regime: x ≥ XC.  The two-regime (Shiu / crude) split.
    -- Thresholds.
    have hL2 : (2 : ℝ) ≤ L := by
      have := hX2 x (le_trans (le_trans (le_max_right X1 X2) (le_max_left _ _)) hxge)
      rwa [← hLdef] at this
    have hcbrt1 : 1 ≤ cbrt x := by
      rw [cbrt]; apply Nat.le_floor; rw [Nat.cast_one]
      calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := (Real.one_rpow _).symm
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx1) (by norm_num)
    have hnScale1 : ∀ c, 1 ≤ nScale c x := fun c => by
      rw [nScale]
      calc (1 : ℕ) = 1 * 1 := by norm_num
        _ ≤ 2 ^ c * cbrt x := Nat.mul_le_mul (Nat.one_le_two_pow) hcbrt1
    obtain ⟨z, hzdef⟩ : ∃ z : ℕ, z = 4 * nScale a x * nScale b x := ⟨_, rfl⟩
    have hz4 : 4 ≤ z := by
      rw [hzdef]
      calc (4 : ℕ) = 4 * 1 * 1 := by norm_num
        _ ≤ 4 * nScale a x * nScale b x := by
            gcongr
            · exact hnScale1 a
            · exact hnScale1 b
    have hz2 : 2 ≤ z := by omega
    have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
    have hzlog0 : (0 : ℝ) ≤ Real.log z :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
    -- Shallow ⇒ `z < 2x/L^F`, and (with `L^F ≥ 2`) `z ≤ x`.
    have hzcast : (z : ℝ) = 2 * ((2 * nScale a x * nScale b x : ℕ) : ℝ) := by
      rw [hzdef]; push_cast; ring
    have hzR2x : (z : ℝ) < 2 * (x : ℝ) / L ^ F := by
      rw [hzcast, mul_div_assoc]; linarith [hshallow]
    have hLF1 : (1 : ℝ) ≤ L ^ F := by
      calc (1 : ℝ) = (1 : ℝ) ^ F := (Real.one_rpow F).symm
        _ ≤ L ^ F :=
            Real.rpow_le_rpow (by norm_num) (by linarith only [hL2])
              (by linarith only [hFfloor, hA'.le])
    have hLFge2 : (2 : ℝ) ≤ L ^ F := by
      calc (2 : ℝ) ≤ L := hL2
        _ = L ^ (1 : ℝ) := (Real.rpow_one L).symm
        _ ≤ L ^ F :=
            Real.rpow_le_rpow_of_exponent_le (by linarith only [hL2])
              (by linarith only [hFfloor, hA'.le])
    have hz2x : (z : ℝ) ≤ 2 * (x : ℝ) := by
      have hle : 2 * (x : ℝ) / L ^ F ≤ 2 * (x : ℝ) := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hLpos F)]; nlinarith [hLFge2, hxpos]
      linarith [hzR2x]
    have hzx : z ≤ x := by
      have : (z : ℝ) < (x : ℝ) := by
        have hle : 2 * (x : ℝ) / L ^ F ≤ (x : ℝ) := by
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hLpos F)]; nlinarith [hLFge2, hxpos]
        linarith [hzR2x]
      exact_mod_cast (by exact_mod_cast this : (z : ℝ) < (x : ℝ)).le
    -- Support and pointwise bounds for `f`.
    have hsupp : ∀ n, z < n → f n = 0 := fun n hn => by
      rw [hf]; exact dconv_block_eq_zero (by rw [hzdef] at hn; exact hn)
    have hbdτ : ∀ n, 1 ≤ n → |f n| ≤ (n.divisors.card : ℝ) * L := by
      intro n hn1
      rcases lt_or_ge x n with hnx | hnx
      · rw [hsupp n (by omega), abs_zero]; exact mul_nonneg (by positivity) hL0
      · rw [hf]; exact abs_dconv_block_le hn1 hnx
    have hbdG : ∀ n, 1 ≤ n → |f n| ≤ Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L := by
      intro n hn1
      rcases lt_or_ge z n with hnz | hnz
      · rw [hsupp n hnz, abs_zero]
        exact mul_nonneg (mul_nonneg hCε0.le (Real.rpow_nonneg hzpos.le _)) hL0
      · calc |f n| ≤ (n.divisors.card : ℝ) * L := hbdτ n hn1
          _ ≤ (Cε * (n : ℝ) ^ ((1 : ℝ) / 16000)) * L :=
              mul_le_mul_of_nonneg_right (hCεbd n hn1) hL0
          _ ≤ (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000)) * L := by
              apply mul_le_mul_of_nonneg_right _ hL0
              apply mul_le_mul_of_nonneg_left _ hCε0.le
              exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnz) (by norm_num)
          _ = Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L := by ring
    -- Q ≥ 1.
    have hxθ1 : (1 : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (3999 / 4000 : ℝ) := (Real.one_rpow _).symm
        _ ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith only [hxR3]) (by norm_num)
    have hQ1 : 1 ≤ Q := Nat.le_floor (by rw [Nat.cast_one]; exact hxθ1)
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
    have hQxθ : (Q : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    have hlogz2L : Real.log z ≤ 2 * L := by
      have h2xx : 2 * (x : ℝ) ≤ (x : ℝ) ^ 2 := by nlinarith only [hxR3]
      calc Real.log z ≤ Real.log (2 * (x : ℝ)) := Real.log_le_log (by positivity) hz2x
        _ ≤ Real.log ((x : ℝ) ^ 2) := Real.log_le_log (by positivity) h2xx
        _ = 2 * L := by rw [Real.log_pow, ← hLdef]; push_cast; ring
    have hlogQ2L : 1 + Real.log Q ≤ 2 * L := by
      have hlogQ : Real.log Q ≤ (3999 / 4000 : ℝ) * L := by
        calc Real.log Q ≤ Real.log ((x : ℝ) ^ (3999 / 4000 : ℝ)) := Real.log_le_log hQpos hQxθ
          _ = (3999 / 4000 : ℝ) * Real.log x := Real.log_rpow hxpos _
          _ = (3999 / 4000 : ℝ) * L := by rw [← hLdef]
      have : (3999 / 4000 : ℝ) * L ≤ L := by linarith only [hLpos]
      linarith [hlogQ, this, hL2]
    -- Per-modulus bound: `seqDiscrepancy f y q ≤ 2·shiuT q + 2·crudeT`.
    have hcrudeT0 : 0 ≤ ((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L) :=
        by
      apply mul_nonneg
      · positivity
      · exact mul_nonneg (mul_nonneg hCε0.le (Real.rpow_nonneg hzpos.le _)) hL0
    have hqbound : ∀ q ∈ Finset.Icc 1 Q,
        seqDiscrepancy f y q
          ≤ 2 * (C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L)
            + 2 * (((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L)) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      have hq1 : 1 ≤ q := hq.1
      have hq0 : q ≠ 0 := by omega
      rcases lt_or_ge (q : ℝ) ((z : ℝ) ^ (1 - (1 : ℝ) / 8000)) with hle | hgt
      · have hCb : ∀ r ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            |∑ n ∈ Finset.Icc 1 y, if n % q = r then f n else 0|
              ≤ C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L := by
          intro r hr
          rw [Finset.mem_filter] at hr
          exact class_bound_shiu hL0 hcorebd hsupp hbdτ hq1 hz2 hle.le hr.2
        have h := seqDiscrepancy_le_two_classBd hq0 hCb
        linarith [hcrudeT0]
      · have hGnn : (0 : ℝ) ≤ Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L :=
          mul_nonneg (mul_nonneg hCε0.le (Real.rpow_nonneg hzpos.le _)) hL0
        have hCb : ∀ r ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            |∑ n ∈ Finset.Icc 1 y, if n % q = r then f n else 0|
              ≤ ((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L) := by
          intro r _
          exact class_bound_crude hGnn hsupp hbdG hq1 (by omega : 1 ≤ z) hgt
        have h := seqDiscrepancy_le_two_classBd hq0 hCb
        have hshiuT0 : 0 ≤ C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L := by
          apply mul_nonneg (mul_nonneg (mul_nonneg hC0.le
            (div_nonneg hzpos.le (by positivity))) hzlog0) hL0
        linarith
    -- Sum the Shiu part.
    have hCzL0 : 0 ≤ C * (z : ℝ) * Real.log z * L :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0.le hzpos.le) hzlog0) hL0
    have hshiupart :
        (∑ q ∈ Finset.Icc 1 Q, 2 * (C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L))
          ≤ 64 * C * (x : ℝ) / L ^ A' := by
      have hfactor :
          (∑ q ∈ Finset.Icc 1 Q, 2 * (C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L))
            = (2 * (C * (z : ℝ) * Real.log z * L))
              * ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun q _ => by ring)
      have hsuminv : (∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ))) ≤ 4 * (1 + Real.log Q) :=
        Salt.LS.sum_inv_totient_le Q hQ1
      have hshiukey :
          8 * (C * (z : ℝ) * Real.log z * L) * (1 + Real.log Q) ≤ 64 * C * (x : ℝ) / L ^ A' := by
        have hrest : (z : ℝ) * Real.log z * L * (1 + Real.log Q)
            ≤ (2 * (x : ℝ) / L ^ F) * (2 * L) * L * (2 * L) := by
          have hzle : (z : ℝ) ≤ 2 * (x : ℝ) / L ^ F := le_of_lt hzR2x
          have hb1 : (0 : ℝ) ≤ 2 * (x : ℝ) / L ^ F := le_trans hzpos.le hzle
          have hb2 : (0 : ℝ) ≤ (2 * (x : ℝ) / L ^ F) * (2 * L) := by positivity
          have hb3 : (0 : ℝ) ≤ (2 * (x : ℝ) / L ^ F) * (2 * L) * L := by positivity
          exact mul_le_mul (mul_le_mul (mul_le_mul hzle hlogz2L hzlog0 hb1)
            (le_refl L) hL0 hb2) hlogQ2L
            (by have hh := Real.log_nonneg (show (1 : ℝ) ≤ (Q : ℝ) by exact_mod_cast hQ1);
                linarith) hb3
        have hLApos' : (0 : ℝ) < L ^ F := Real.rpow_pos_of_pos hLpos F
        have hfin : (L * L * L) / L ^ F ≤ 1 / L ^ A' := by
          rw [div_le_div_iff₀ hLApos' hLA'pos, one_mul]
          have hL3 : L * L * L = L ^ (3 : ℝ) := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
          rw [hL3, ← Real.rpow_add hLpos]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hL2])
            (by linarith only [hFfloor])
        calc 8 * (C * (z : ℝ) * Real.log z * L) * (1 + Real.log Q)
            = 8 * C * ((z : ℝ) * Real.log z * L * (1 + Real.log Q)) := by ring
          _ ≤ 8 * C * ((2 * (x : ℝ) / L ^ F) * (2 * L) * L * (2 * L)) :=
              mul_le_mul_of_nonneg_left hrest (by linarith only [hC0])
          _ = (64 * C * (x : ℝ)) * ((L * L * L) / L ^ F) := by ring
          _ ≤ (64 * C * (x : ℝ)) * (1 / L ^ A') :=
              mul_le_mul_of_nonneg_left hfin (by positivity)
          _ = 64 * C * (x : ℝ) / L ^ A' := by ring
      rw [hfactor]
      calc (2 * (C * (z : ℝ) * Real.log z * L)) * ∑ q ∈ Finset.Icc 1 Q, (1 / (q.totient : ℝ))
          ≤ (2 * (C * (z : ℝ) * Real.log z * L)) * (4 * (1 + Real.log Q)) :=
            mul_le_mul_of_nonneg_left hsuminv (by linarith only [hCzL0])
        _ = 8 * (C * (z : ℝ) * Real.log z * L) * (1 + Real.log Q) := by ring
        _ ≤ 64 * C * (x : ℝ) / L ^ A' := hshiukey
    -- Sum the crude part.
    have hcrudepart :
        (∑ q ∈ Finset.Icc 1 Q,
            2 * (((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L)))
          ≤ 64 * C * (x : ℝ) / L ^ A' := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast [Nat.add_sub_cancel]
      -- Now: `(Q:ℝ) * (2 * crudeT) ≤ 64 C x / L^A'`.
      have hz_alpha : (z : ℝ) ^ ((1 : ℝ) / 8000) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 8000) := by
        calc (z : ℝ) ^ ((1 : ℝ) / 8000) ≤ (2 * (x : ℝ)) ^ ((1 : ℝ) / 8000) :=
              Real.rpow_le_rpow hzpos.le hz2x (by norm_num)
          _ = 2 ^ ((1 : ℝ) / 8000) * (x : ℝ) ^ ((1 : ℝ) / 8000) :=
              Real.mul_rpow (by norm_num) hxpos.le
          _ ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 8000) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxpos.le _)
              calc (2 : ℝ) ^ ((1 : ℝ) / 8000) ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
      have hx_alpha1 : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8000) := by
        calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 8000) := (Real.one_rpow _).symm
          _ ≤ (x : ℝ) ^ ((1 : ℝ) / 8000) :=
              Real.rpow_le_rpow (by norm_num) (by linarith only [hxR3]) (by norm_num)
      have hzα3 : (z : ℝ) ^ ((1 : ℝ) / 8000) + 1 ≤ 3 * (x : ℝ) ^ ((1 : ℝ) / 8000) := by
        linarith [hz_alpha, hx_alpha1]
      have hz_eps : (z : ℝ) ^ ((1 : ℝ) / 16000) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 16000) := by
        calc (z : ℝ) ^ ((1 : ℝ) / 16000) ≤ (2 * (x : ℝ)) ^ ((1 : ℝ) / 16000) :=
              Real.rpow_le_rpow hzpos.le hz2x (by norm_num)
          _ = 2 ^ ((1 : ℝ) / 16000) * (x : ℝ) ^ ((1 : ℝ) / 16000) :=
              Real.mul_rpow (by norm_num) hxpos.le
          _ ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 16000) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxpos.le _)
              calc (2 : ℝ) ^ ((1 : ℝ) / 16000) ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
      have hzεL : Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L ≤ 2 * Cε * (x : ℝ) ^ ((1 : ℝ) / 16000) * L :=
          by
        calc Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L
            ≤ Cε * (2 * (x : ℝ) ^ ((1 : ℝ) / 16000)) * L :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz_eps hCε0.le) hL0
          _ = 2 * Cε * (x : ℝ) ^ ((1 : ℝ) / 16000) * L := by ring
      have hcT : ((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L)
          ≤ (3 * (x : ℝ) ^ ((1 : ℝ) / 8000)) * (2 * Cε * (x : ℝ) ^ ((1 : ℝ) / 16000) * L) :=
        mul_le_mul hzα3 hzεL
          (mul_nonneg (mul_nonneg hCε0.le (Real.rpow_nonneg hzpos.le _)) hL0)
          (by positivity)
      have hxpow : (x : ℝ) ^ (3999 / 4000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8000)
          * (x : ℝ) ^ ((1 : ℝ) / 16000) = (x : ℝ) ^ (1 - (1 : ℝ) / 16000) := by
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; norm_num
      have hxδ : (x : ℝ) ^ ((1 : ℝ) / 16000) * (x : ℝ) ^ (1 - (1 : ℝ) / 16000) = (x : ℝ) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have hLApow : L ^ (1 + A') ≤ (1 + L) ^ (⌈A' + 1⌉₊) := by
        calc L ^ (1 + A') ≤ (1 + L) ^ (1 + A') :=
              Real.rpow_le_rpow hL0 (by linarith only [hLpos]) (by linarith only [hA'.le])
          _ ≤ (1 + L) ^ (((⌈A' + 1⌉₊ : ℕ)) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith only [hLpos]) (by
                have := Nat.le_ceil (A' + 1); linarith only [this])
          _ = (1 + L) ^ (⌈A' + 1⌉₊) := by rw [Real.rpow_natCast]
      have hpoly : (12 * Cε / (64 * C)) * (1 + L) ^ (⌈A' + 1⌉₊) ≤ (x : ℝ) ^ ((1 : ℝ) / 16000) := by
        have := hX1 x (le_trans (le_trans (le_max_left X1 X2) (le_max_left _ _)) hxge)
        rwa [← hLdef] at this
      have h64C : (0 : ℝ) < 64 * C := by linarith only [hC0]
      have hpoly2 : 12 * Cε * (1 + L) ^ (⌈A' + 1⌉₊) ≤ 64 * C * (x : ℝ) ^ ((1 : ℝ) / 16000) := by
        have hh := hpoly
        rw [div_mul_eq_mul_div, div_le_iff₀ h64C] at hh
        calc 12 * Cε * (1 + L) ^ (⌈A' + 1⌉₊) ≤ (x : ℝ) ^ ((1 : ℝ) / 16000) * (64 * C) := hh
          _ = 64 * C * (x : ℝ) ^ ((1 : ℝ) / 16000) := by ring
      have hcore12 : 12 * Cε * L ^ (1 + A') ≤ 64 * C * (x : ℝ) ^ ((1 : ℝ) / 16000) :=
        le_trans (mul_le_mul_of_nonneg_left hLApow (by linarith only [hCε0.le])) hpoly2
      have hcrudefin : 12 * Cε * ((x : ℝ) ^ (1 - (1 : ℝ) / 16000)) * L
          ≤ 64 * C * (x : ℝ) / L ^ A' := by
        rw [le_div_iff₀ hLA'pos]
        have hLpow1 : L * L ^ A' = L ^ (1 + A') := by rw [Real.rpow_add hLpos, Real.rpow_one]
        have e1 : 12 * Cε * ((x : ℝ) ^ (1 - (1 : ℝ) / 16000)) * L * L ^ A'
            = (12 * Cε * L ^ (1 + A')) * (x : ℝ) ^ (1 - (1 : ℝ) / 16000) := by
          rw [← hLpow1]; ring
        rw [e1]
        calc (12 * Cε * L ^ (1 + A')) * (x : ℝ) ^ (1 - (1 : ℝ) / 16000)
            ≤ (64 * C * (x : ℝ) ^ ((1 : ℝ) / 16000)) * (x : ℝ) ^ (1 - (1 : ℝ) / 16000) :=
              mul_le_mul_of_nonneg_right hcore12 (Real.rpow_nonneg hxpos.le _)
          _ = 64 * C * (x : ℝ) := by rw [mul_assoc, hxδ]
      calc (Q : ℝ)
            * (2 * (((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L)))
          ≤ (x : ℝ) ^ (3999 / 4000 : ℝ)
              * (2 * ((3 * (x : ℝ) ^ ((1 : ℝ) / 8000))
                * (2 * Cε * (x : ℝ) ^ ((1 : ℝ) / 16000) * L))) := by
            apply mul_le_mul hQxθ _ (by positivity) (Real.rpow_nonneg hxpos.le _)
            exact mul_le_mul_of_nonneg_left hcT (by norm_num)
        _ = 12 * Cε * ((x : ℝ) ^ (3999 / 4000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8000)
              * (x : ℝ) ^ ((1 : ℝ) / 16000)) * L := by ring
        _ = 12 * Cε * ((x : ℝ) ^ (1 - (1 : ℝ) / 16000)) * L := by rw [hxpow]
        _ ≤ 64 * C * (x : ℝ) / L ^ A' := hcrudefin
    -- Combine.
    calc (∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy f y q)
        ≤ ∑ q ∈ Finset.Icc 1 Q,
            (2 * (C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L)
              + 2 * (((z : ℝ) ^ ((1 : ℝ) / 8000) + 1)
                * (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L))) := Finset.sum_le_sum hqbound
      _ = (∑ q ∈ Finset.Icc 1 Q, 2 * (C * ((z : ℝ) / (q.totient : ℝ)) * Real.log z * L))
          + (∑ q ∈ Finset.Icc 1 Q,
              2 * (((z : ℝ) ^ ((1 : ℝ) / 8000) + 1) * (Cε * (z : ℝ) ^ ((1 : ℝ) / 16000) * L))) :=
          Finset.sum_add_distrib
      _ ≤ 64 * C * (x : ℝ) / L ^ A' + 64 * C * (x : ℝ) / L ^ A' := add_le_add hshiupart hcrudepart
      _ ≤ Csh * (x : ℝ) / L ^ A' := by
          have heq : 64 * C * (x : ℝ) / L ^ A' + 64 * C * (x : ℝ) / L ^ A'
              = 128 * C * (x : ℝ) / L ^ A' := by ring
          rw [heq]
          exact (div_le_div_iff_of_pos_right hLA'pos).mpr
            (mul_le_mul_of_nonneg_right h128_le hxpos.le)

end Salt.Maynard
