/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehSmallQClose
import Salt.Chen.BetaSW

/-!
# The per-cofactor Siegel–Walfisz estimate (node SMALLQ-3)

Design: `docs/exploration/s3-a3-design.md` (the N-SMALLQ ruling + THE GIFT).
SMALLQ-2 (`Salt/Maynard/GehSmallQClose.lean`) reduced the small-`q` Type-II block
discrepancy to a sum of per-cofactor discrepancies
`seqDiscrepancy (smallQCofactor M V r x m) x q`.  This file discharges the
analytic residual: an actual Siegel–Walfisz–driven bound on those per-cofactor
pieces, built on the gate-backed cumulative discrepancy
`Salt.Chen.psiAP_sub_psiTot_bound`.

The four named sub-estimates and their status here:
1. **Windowed SW differencing** — LANDED (`window_psiAP_diff_SW`).  A window
   `Ioc u v` of a `Λ`-in-AP discrepancy is the difference of the two cumulative
   endpoint discrepancies `psiAP v q a − psiAP u q a`, each
   `Salt.Chen.psiAP_sub_psiTot_bound`-controlled; the reusable SW engine the
   survey identified as previously unwritten.
2. **The Ioc extraction** — LANDED (`window_lambda_residue_eq`, `psiAP_diff_eq`).
   The windowed residue sum as a difference of two cumulative `psiAP` prefixes.
   Fused with (1) in `window_lambda_disc_le`.
3. **The r-correction + τ absorption** — PARTIAL.  The GIFT case split is landed
   (`smallQCofactor_seqDiscrepancy_eq_zero_of_not_coprime`: `gcd(m,q)>1` cofactors
   contribute a discrepancy of *exactly* 0).  The clean `gcd(m,q)=1` branch — the
   `m⁻¹`-reindex onto a cofactor window, the Möbius expansion of the `coprime c r`
   twist onto moduli `q·d` (`d ∣ r`), and the `τ(qr)^j` absorption — is the NAMED
   RESIDUAL (see the catch below).
4. **The small-x threshold split** — engine LANDED
   (`smallQCofactor_seqDiscrepancy_le_trivial`: the unconditional
   `≤ 2·ψ(x/m)` mass bound, carrying the `1/m` scale via the multiples reindex
   `sum_multiples_quotient`).  The threshold *placement* compatible with the
   `A′ = A+1` bookkeeping is folded into the residual assembly.

## Residuals (Zeno halt)

* **R1 — the `gcd(m,q)=1` r-twist core (sub-estimate 3).**  The genuine analytic
  wall: after the `m⁻¹`-reindex the `coprime c r` factor Möbius-expands to
  `∑_{d∣r} μ(d)·(c-window at modulus q·d)`, each SW-bounded only while
  `q·d ≤ (log)^C`; the large-`d` tail needs the trivial bound + `τ(qr)^j`
  absorption.  No ready lemma exists; `window_lambda_disc_le` supplies the
  small-`d` engine.
* **R2 — the coprime-mean seam.**  `seqDiscrepancy`'s mean is the *coprime*
  `(∑_{gcd(n,q)=1} ·)/φ(q)`, whereas `window_lambda_disc_le` bounds against the
  *total* `(ψ(v)−ψ(u))/φ(q)`; they differ by the `ω(q)·log`-seam
  (`Salt.BV.norm_psiChi_one_sub_psiTot_le`, complex form).  This fifth,
  unlisted-in-the-house-decomposition correction is minor but load-bearing.

## CATCH against the house four-way decomposition (reported LOUDLY)

Sub-estimate 3 ("r-correction + τ absorption") is **not a single clean step**: it
is itself a Bombieri–Vinogradov-with-divisor-twist argument (Möbius expansion +
SW at *enlarged* moduli `q·d` beyond the small-`q` range + trivial-bound τ-slack
bookkeeping for `q·d > (log)^C` + the coprime-mean seam R2).  It is **at least as
hard as sub-estimate 4** — arguably the dominant difficulty — contrary to the
briefing's ranking of (4) as "THE DOMINANT DIFFICULTY".  The decomposition is
SOUND (SmallQTypeII is plausibly true for all `r`, the `τ(qr)^j` factor being
exactly the slack that absorbs the r-twist), but the four-way list understates the
weight of (3) and omits the seam (R2) entirely.
-/

open Finset ArithmeticFunction Salt.LS

namespace Salt.Maynard

/-! ## Sub-estimate 2 — the Ioc extraction (window = difference of cumulative prefixes) -/

/-- `Finset.Icc 1 n = Finset.Ioc 0 n` in `ℕ`. -/
private theorem Icc_one_eq_Ioc_zero (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
  ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- **The `psiAP` prefix difference.**  For `u ≤ v`, the cumulative `ψ`-in-AP
counts telescope: `psiAP v q a − psiAP u q a` is the windowed `Ioc u v` count of
`Λ` in the residue class `a mod q`. -/
theorem psiAP_diff_eq {u v : ℕ} (huv : u ≤ v) (q a : ℕ) :
    psiAP v q a - psiAP u q a
      = ∑ n ∈ Finset.Ioc u v, if n % q = a % q then vonMangoldt n else 0 := by
  have hcons := Finset.sum_Ioc_consecutive
    (fun n => if n % q = a % q then vonMangoldt n else 0) (Nat.zero_le u) huv
  have hpv : psiAP v q a = ∑ n ∈ Finset.Ioc 0 v, if n % q = a % q then vonMangoldt n else 0 := by
    rw [psiAP, ← Icc_one_eq_Ioc_zero, Finset.sum_filter]
  have hpu : psiAP u q a = ∑ n ∈ Finset.Ioc 0 u, if n % q = a % q then vonMangoldt n else 0 := by
    rw [psiAP, ← Icc_one_eq_Ioc_zero, Finset.sum_filter]
  rw [hpv, hpu]; linarith [hcons]

/-- **The windowed residue-sum extraction.**  For a reduced residue `a < q` and a
window `Ioc u v` inside the summation range (`u ≤ v ≤ x`), the `seqDiscrepancy`
residue-class sum of the windowed `Λ` weight equals the cumulative `psiAP`
difference `psiAP v q a − psiAP u q a`. -/
theorem window_lambda_residue_eq {u v x : ℕ} (huv : u ≤ v) (hvx : v ≤ x)
    {q a : ℕ} (haq : a < q) :
    (∑ n ∈ Finset.Icc 1 x,
        if n % q = a then (if n ∈ Finset.Ioc u v then vonMangoldt n else 0) else 0)
      = psiAP v q a - psiAP u q a := by
  rw [psiAP_diff_eq huv q a]
  have ham : a % q = a := Nat.mod_eq_of_lt haq
  have hsub : Finset.Ioc u v ⊆ Finset.Icc 1 x := by
    intro n hn; rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  -- the windowed weight vanishes off `Ioc u v`, so the `Icc 1 x` sum restricts
  have hrestrict :
      (∑ n ∈ Finset.Icc 1 x,
          if n % q = a then (if n ∈ Finset.Ioc u v then vonMangoldt n else 0) else 0)
        = ∑ n ∈ Finset.Ioc u v,
            if n % q = a then (if n ∈ Finset.Ioc u v then vonMangoldt n else 0) else 0 := by
    refine (Finset.sum_subset hsub (fun n _ hnf => ?_)).symm
    have hinner : (if n ∈ Finset.Ioc u v then vonMangoldt n else 0) = 0 := if_neg hnf
    simp only [hinner, ite_self]
  rw [hrestrict]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  simp only [hn, if_true, ham]

/-! ## Sub-estimate 1 — the windowed SW differencing -/

/-- **The windowed SW differencing.**  For a reduced residue `a < q`, the
windowed `Λ`-in-AP discrepancy `(psiAP v q a − psiAP u q a) − (psiTot v − psiTot u)/φ(q)`
— the difference of the two cumulative endpoint discrepancies — is bounded by
`4K·v/(log u)^A`, uniformly over windows `3 ≤ u ≤ v` with `q ≤ (log u)^C`.  Each
endpoint discrepancy `psiAP · q a − psiTot ·/φ(q)` is
`Salt.Chen.psiAP_sub_psiTot_bound`-controlled (`≤ 2K·(endpoint)/(log)^A`); the
triangle inequality and the interval monotonicities collapse the two endpoint
denominators onto the smaller `(log u)^A`. -/
theorem window_psiAP_diff_SW {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u v q a : ℕ), 3 ≤ u → u ≤ v → 0 < q → a < q →
      Nat.Coprime a q → ((q : ℝ) ≤ (Real.log u) ^ C) →
      |(psiAP v q a - psiAP u q a) - (psiTot v - psiTot u) / (q.totient : ℝ)|
        ≤ 4 * K * v / (Real.log u) ^ A := by
  obtain ⟨K, hK0, hK⟩ := Salt.Chen.psiAP_sub_psiTot_bound hA hC
  refine ⟨K, hK0, fun u v q a hu huv hq haq hcop hqlog => ?_⟩
  -- basic positivity facts on the two log scales
  have hu3 : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hv3 : 3 ≤ v := le_trans hu huv
  have hvR3 : (3 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv3
  have huvR : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
  have hlogu1 : 1 ≤ Real.log u := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      _ ≤ (u : ℝ) := hu3
  have hlogupos : 0 < Real.log u := by linarith
  have hloguv : Real.log u ≤ Real.log v :=
    Real.log_le_log (by linarith) huvR
  have hlogvpos : 0 < Real.log v := by linarith
  have hloguA : 0 < (Real.log u) ^ A := Real.rpow_pos_of_pos hlogupos A
  have hlogvA : 0 < (Real.log v) ^ A := Real.rpow_pos_of_pos hlogvpos A
  -- the range condition transports up to v
  have hqlogv : (q : ℝ) ≤ (Real.log v) ^ C :=
    le_trans hqlog (Real.rpow_le_rpow hlogupos.le hloguv hC.le)
  -- endpoint discrepancy bounds from the cumulative gate
  have hEv := hK v q a hv3 hq haq hcop hqlogv
  have hEu := hK u q a hu hq haq hcop hqlog
  -- rewrite the window discrepancy as the difference of endpoint discrepancies
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hsplit :
      (psiAP v q a - psiAP u q a) - (psiTot v - psiTot u) / (q.totient : ℝ)
        = (psiAP v q a - psiTot v / (q.totient : ℝ))
          - (psiAP u q a - psiTot u / (q.totient : ℝ)) := by
    field_simp; ring
  rw [hsplit]
  -- monotonicity collapses both endpoints onto `4 K v / (log u)^A`
  have hKvnn : (0 : ℝ) ≤ 2 * K * (v : ℝ) := by positivity
  set Ev : ℝ := psiAP v q a - psiTot v / (q.totient : ℝ) with hEvd
  set Eu : ℝ := psiAP u q a - psiTot u / (q.totient : ℝ) with hEud
  have hbEv : |Ev| ≤ 2 * K * v / (Real.log u) ^ A :=
    le_trans hEv (div_le_div_of_nonneg_left hKvnn hloguA
      (Real.rpow_le_rpow hlogupos.le hloguv hA.le))
  have hbEu : |Eu| ≤ 2 * K * v / (Real.log u) ^ A := by
    refine le_trans hEu ?_
    rw [div_le_div_iff_of_pos_right hloguA]
    exact mul_le_mul_of_nonneg_left huvR (mul_nonneg (by norm_num) hK0)
  have htri : |Ev - Eu| ≤ |Ev| + |Eu| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le Ev (-Eu)).trans_eq (by rw [abs_neg])
  have hcombine : |Ev| + |Eu| ≤ 4 * K * v / (Real.log u) ^ A := by
    have h := add_le_add hbEv hbEu
    have heq : 2 * K * (v : ℝ) / (Real.log u) ^ A + 2 * K * (v : ℝ) / (Real.log u) ^ A
        = 4 * K * (v : ℝ) / (Real.log u) ^ A := by ring
    linarith [h, heq]
  exact le_trans htri hcombine

/-- **The windowed Λ-in-AP discrepancy (sub-estimates 1+2 fused).**  For a reduced
residue `a < q`, the per-residue discrepancy of the windowed `Λ` weight
`n ↦ 1_{Ioc u v}(n)·Λ(n)` against the total mean `(ψ(v) − ψ(u))/φ(q)` is SW-bounded
by `4K·v/(log u)^A`, uniformly over `3 ≤ u ≤ v ≤ x` with `q ≤ (log u)^C`.  Route:
`window_lambda_residue_eq` (Ioc extraction) turns the residue sum into the
cumulative `psiAP` difference, then `window_psiAP_diff_SW` (SW differencing) bounds
it.  (The `seqDiscrepancy` coprime mean differs from this total mean by the
`ω(q)·log`-seam; see the module residuals note.) -/
theorem window_lambda_disc_le {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u v x q a : ℕ), 3 ≤ u → u ≤ v → v ≤ x → 0 < q → a < q →
      Nat.Coprime a q → ((q : ℝ) ≤ (Real.log u) ^ C) →
      |(∑ n ∈ Finset.Icc 1 x,
          if n % q = a then (if n ∈ Finset.Ioc u v then vonMangoldt n else 0) else 0)
        - (psiTot v - psiTot u) / (q.totient : ℝ)|
        ≤ 4 * K * v / (Real.log u) ^ A := by
  obtain ⟨K, hK0, hK⟩ := window_psiAP_diff_SW hA hC
  refine ⟨K, hK0, fun u v x q a hu huv hvx hq haq hcop hqlog => ?_⟩
  rw [window_lambda_residue_eq huv hvx haq]
  exact hK u v q a hu huv hq haq hcop hqlog

/-! ## Sub-estimate 4 — the small-x / trivial per-cofactor bound -/

/-- **The multiples reindex.**  For `m ≥ 1`, summing a weight of the quotient
`n/m` over the multiples of `m` in `[1,x]` reindexes (via `n = m·c`) to the plain
sum over `[1, x/m]`. -/
theorem sum_multiples_quotient (m x : ℕ) (hm : 0 < m) (g : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 x).filter (fun n => m ∣ n), g (n / m))
      = ∑ c ∈ Finset.Icc 1 (x / m), g c := by
  apply Finset.sum_bij' (fun n _ => n / m) (fun c _ => m * c)
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hdvd⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hm).mpr (Nat.le_of_dvd (by omega) hdvd),
      Nat.div_le_div_right hn2⟩
  · intro c hc
    rw [Finset.mem_Icc] at hc
    obtain ⟨hc1, hc2⟩ := hc
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos hm (by omega), ?_⟩, ⟨c, rfl⟩⟩
    calc m * c ≤ m * (x / m) := Nat.mul_le_mul_left m hc2
      _ ≤ x := Nat.mul_div_le x m
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]
  · intro c _
    rw [Nat.mul_div_cancel_left c hm]
  · intro n _
    rfl

/-- **The trivial per-cofactor bound (sub-estimate 4 engine).**  Unconditionally,
the per-cofactor discrepancy is at most twice the `Λ`-mass carried by the divisor
class `n = m·c`, which reindexes to `2·ψ(x/m)`.  This is the below-SW-threshold
corner: for `x` below the effective threshold `ψ(x/m) ≤ (x/m)·log(x/m)` is a
constant, and the `1/m` decay makes the sum over cofactors telescope to the block
mass.  The bound carries the crucial `x/m` scale (`Salt.BV.psiTot_le` gives the
explicit `(x/m)·log(x/m)` majorant). -/
theorem smallQCofactor_seqDiscrepancy_le_trivial (Mf Vf : ℕ → ℕ) (r x m q : ℕ)
    (hm : 0 < m) :
    seqDiscrepancy (smallQCofactor Mf Vf r x m) x q ≤ 2 * psiTot (x / m) := by
  refine le_trans (seqDiscrepancy_le_two_mul_sum_abs _ x q) ?_
  have hpt : ∀ n, |smallQCofactor Mf Vf r x m n|
      ≤ (if m ∣ n then vonMangoldt (n / m) else 0) := by
    intro n
    unfold smallQCofactor
    split_ifs with hc hd hd
    · rw [abs_of_nonneg vonMangoldt_nonneg]
    · exact absurd hc.1 hd
    · rw [abs_zero]; exact vonMangoldt_nonneg
    · rw [abs_zero]
  have hmass : (∑ n ∈ Finset.Icc 1 x, |smallQCofactor Mf Vf r x m n|) ≤ psiTot (x / m) := by
    calc ∑ n ∈ Finset.Icc 1 x, |smallQCofactor Mf Vf r x m n|
        ≤ ∑ n ∈ Finset.Icc 1 x, if m ∣ n then vonMangoldt (n / m) else 0 :=
          Finset.sum_le_sum (fun n _ => hpt n)
      _ = ∑ n ∈ (Finset.Icc 1 x).filter (fun n => m ∣ n), vonMangoldt (n / m) := by
          rw [Finset.sum_filter]
      _ = ∑ c ∈ Finset.Icc 1 (x / m), vonMangoldt c :=
          sum_multiples_quotient m x hm (fun c => vonMangoldt c)
      _ = psiTot (x / m) := by rw [psiTot]
  linarith [hmass]

/-! ## Sub-estimate 3 (partial) — THE GIFT case split: non-coprime cofactor vanishes -/

/-- **The non-coprime cofactor vanishes (THE GIFT, discrepancy form).**  When the
cofactor `m` is not coprime to the modulus `q`, the per-cofactor discrepancy is
*exactly* `0`: every reduced-residue class sum vanishes (`smallQ_class_vanish` —
no `m·c` lands in a class `a` coprime to `q`), and the coprime mean vanishes too
(a coprime-to-`q` multiple of `m` would force `gcd(m,q)=1`).  This is the
discrepancy-level realization of THE GIFT that kills the CRT machinery: only
`gcd(m,q)=1` cofactors contribute, so the `r`-twist reduction (sub-estimate 3)
only ever runs in the clean `m⁻¹`-bijection regime. -/
theorem smallQCofactor_seqDiscrepancy_eq_zero_of_not_coprime
    (Mf Vf : ℕ → ℕ) (r x m q : ℕ) (hmq : ¬ Nat.Coprime m q) :
    seqDiscrepancy (smallQCofactor Mf Vf r x m) x q = 0 := by
  rcases eq_or_ne q 0 with hq0 | hq0
  · subst hq0; simp [seqDiscrepancy]
  refine le_antisymm ?_ (seqDiscrepancy_nonneg _ x q)
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  rw [seqDiscrepancy_eq _ x q hq0]
  apply Finset.sup'_le
  intro a ha
  rw [Finset.mem_filter, Finset.mem_range] at ha
  -- every residue-class sum vanishes
  have hRa : (∑ n ∈ Finset.Icc 1 x,
      if n % q = a then smallQCofactor Mf Vf r x m n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    by_cases hn : n % q = a
    · rw [if_pos hn]
      unfold smallQCofactor
      split_ifs with hc
      · exfalso
        have hdvd := hc.1
        have hmc : (m * (n / m)) % q = a := by rw [Nat.mul_div_cancel' hdvd]; exact hn
        exact smallQ_class_vanish hqpos ha.2 hmq (n / m) hmc
      · rfl
    · rw [if_neg hn]
  -- the coprime mean vanishes
  have hMEAN : (∑ n ∈ Finset.Icc 1 x,
      if Nat.Coprime n q then smallQCofactor Mf Vf r x m n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    by_cases hn : Nat.Coprime n q
    · rw [if_pos hn]
      unfold smallQCofactor
      split_ifs with hc
      · exact absurd (Nat.Coprime.coprime_dvd_left hc.1 hn) hmq
      · rfl
    · rw [if_neg hn]
  rw [hRa, hMEAN]; simp

end Salt.Maynard
