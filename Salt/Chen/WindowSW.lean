/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WindowBV
import Salt.Chen.PairBijection

/-!
# WBV3 — the small-conductor window SW + the windowed identification

Design: `docs/blueprints/flags.md`, the `2026-07-13 C54-RECON` freeze (route (i)) and the
`2026-07-14 WBV1`/`WBV2` entries.  This file lands the WBV wave's one genuinely new estimate
(item 6) and the window-in-carrier identification (item 8).

## Item 6 — `smallconductor_window_perd` / `smallconductor_window_sum` (THE estimate)

For a small conductor `d ≤ D0`, the windowed AP discrepancy `apDiscBilinCutoff α (blockPrimeInd N)
X M R₀ d T` (residue-generalized to a per-`d` residue `r d` coprime to `d` — H-AMENDMENT 2 C4;
the landed consumers instantiate `r ≡ 2`) is expanded **by fixed `m`**: pulling `α m` out, the
inner `n`-sum is the residue-count minus `(1/φd)·`unit-count of the primes `n` over the CLEAN
`m`-interval `(N, min M ⌊T/m⌋]`.  For each `m` coprime to `d` the residue class
`n ≡ R₀·m⁻¹ (mod d)` is a single unit class, and the inner discrepancy is EXACTLY the interval
prime-AP discrepancy priced by C3b's `prime_indicator_SW`; for `(m, d) > 1` (with
`Coprime R₀ d`) both counts vanish (`R₀` is a unit, so a residue-`R₀` product forces `m` a
unit).  Summing over `m ≤ X` with `‖α‖ ≤ 1` gives `X ·` (the per-interval SW error), and summing
over `d ≤ D0` absorbs the `D0` factor into one `(log XM)^{C0}` via the recon's exponent
bookkeeping (mirroring `GeneralBV.small_perd` / `EnergyClose.smallConductor_energy_le`).

The window never enters this estimate — it lives in the carrier's cutoff `T` (route (i)); the
identification (item 8) turns the honest per-block discrepancy into a difference of two one-sided
cutoffs.

Only `[propext, Classical.choice, Quot.sound]` are used.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## The windowed interval prime count -/

open Classical in
/-- **The windowed interval prime class-count (`blockPrimeInd_classCount`, cutoff variant).**  For
`m ≥ 1` and any decidable class predicate `Q`, the `Q`-restricted sum of the block-`(N, ∞)` prime
indicator over the *cutoff* range `{n ≤ M : m·n ≤ T}` equals the count of primes `p` in the CLEAN
interval `(N, min M ⌊T/m⌋]` with `Q p`.  The cutoff `m·n ≤ T` combined with `n ≤ M` and `N < n`
collapses to the interval `(N, min M ⌊T/m⌋]` (via `Nat.le_div_iff_mul_le`).  Mirrors
`ConductorDescent.blockPrimeInd_classCount`, the un-cut version. -/
lemma windowed_blockPrimeInd_classCount (N M T m : ℕ) (hm : 1 ≤ m)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
        if Q n then blockPrimeInd N n else 0)
      = (((Finset.Ioc N (min M (T / m))).filter (fun p => p.Prime ∧ Q p)).card : ℂ) := by
  classical
  have hm0 : 0 < m := hm
  have hmerge : ∀ n : ℕ,
      (if Q n then blockPrimeInd N n else 0)
        = (if (Q n ∧ N < n ∧ n.Prime) then (1 : ℂ) else 0) := by
    intro n
    unfold blockPrimeInd
    by_cases h1 : Q n
    · by_cases h2 : N < n ∧ n.Prime
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  rw [Finset.sum_congr rfl (fun n _ => hmerge n), Finset.sum_boole]
  congr 1
  apply Finset.card_bij (fun n _ => n)
  · -- membership: the filtered-`Icc` witness lands in the interval
    intro n hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨_, hnM⟩, hmnT⟩, hQ, hNn, hprime⟩ := hn
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hNn, le_min hnM ((Nat.le_div_iff_mul_le hm0).mpr ?_)⟩, hprime, hQ⟩
    rw [Nat.mul_comm]; exact hmnT
  · intro n _ n' _ h; exact h
  · -- surjectivity: reconstruct the filtered-`Icc` witness from an interval prime
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hNp, hpU⟩, hprime, hQ⟩ := hp
    have hpM : p ≤ M := le_trans hpU (min_le_left _ _)
    have hpTm : p ≤ T / m := le_trans hpU (min_le_right _ _)
    have hmpT : m * p ≤ T := by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hm0).mp hpTm
    refine ⟨p, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨by omega, hpM⟩, hmpT⟩, hQ, hNp, hprime⟩

/-! ## Item 6 — the per-`d` small-conductor windowed SW estimate -/

open Classical in
/-- **`smallconductor_window_perd` — the per-`d` windowed small-conductor SW bound (FULL,
residue-generalized per H-AMENDMENT 2 C4).**  The genuinely new WBV estimate.  For `d ≤ N` below
the SW range (`d ≤ (log N)^C`) and ANY residue `R₀` coprime to `d`, the windowed AP discrepancy
at residue `R₀` is bounded by `X ·` (the interval SW error `K·N/(log N)^A`): expand
`apDiscBilinCutoff` by fixed `m`, identify each inner `n`-discrepancy with the prime-AP
discrepancy of the clean interval `(N, min M ⌊T/m⌋]` (priced by C3b's `prime_indicator_SW`), and
sum over `m ≤ X` with `‖α‖ ≤ 1`.  For `(m, d) > 1` the inner discrepancy vanishes (`R₀` a unit
forces `m` a unit); for `m` coprime to `d` the residue class `n ≡ R₀·m⁻¹ (mod d)` is a single
unit class, and (since block primes `> N ≥ d` are automatically coprime to `d`) the unit-count is
the total prime count — exactly the SW shape.  The residue enters ONLY through
`IsUnit (R₀ : ZMod d)`; the landed consumers instantiate `R₀ = 2`. -/
theorem smallconductor_window_perd {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T d R₀ : ℕ),
        (∀ m, ‖α m‖ ≤ 1) → N₀ ≤ N → M ≤ 2 * N → 1 ≤ d → d ≤ N →
        Nat.Coprime R₀ d → ((d : ℝ) ≤ (Real.log N) ^ C) →
        ‖apDiscBilinCutoff α (blockPrimeInd N) X M R₀ d T‖
          ≤ (X : ℝ) * (K * N / (Real.log N) ^ A) := by
  obtain ⟨K, N₀sw, hK0, hb⟩ := prime_indicator_SW hA hC
  refine ⟨K, max N₀sw 3, hK0, fun α X N M T d R₀ hα hN hM2N hd1 hdN hcop2 hdlog => ?_⟩
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hNsw : N₀sw ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLApos : (0 : ℝ) < (Real.log N) ^ A := Real.rpow_pos_of_pos hlogN A
  have hboundnn : (0 : ℝ) ≤ K * N / (Real.log N) ^ A := by positivity
  -- the per-`m` inner discrepancy is bounded by the interval SW error, uniformly in `m ≥ 1`.
  have hperm : ∀ m, 1 ≤ m →
      ‖(∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
            if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then blockPrimeInd N n else 0)
          - (1 / (d.totient : ℂ)) *
            (∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
              if IsUnit ((m * n : ℕ) : ZMod d) then blockPrimeInd N n else 0)‖
        ≤ K * N / (Real.log N) ^ A := by
    intro m hm
    rw [windowed_blockPrimeInd_classCount N M T m hm
          (fun n => ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)),
        windowed_blockPrimeInd_classCount N M T m hm
          (fun n => IsUnit ((m * n : ℕ) : ZMod d))]
    set U := min M (T / m) with hUdef
    by_cases hcopm : Nat.Coprime m d
    · -- coprime `m`: identify with the interval prime-AP discrepancy and apply SW.
      have hm_unit : IsUnit ((m : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime m d).mpr hcopm
      have h2_unit : IsUnit ((R₀ : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime R₀ d).mpr hcop2
      set rm : ZMod d := ((m : ℕ) : ZMod d)⁻¹ * ((R₀ : ℕ) : ZMod d) with hrmdef
      have hminv_unit : IsUnit (((m : ℕ) : ZMod d)⁻¹) := by
        rw [isUnit_iff_exists]
        exact ⟨((m : ℕ) : ZMod d), ZMod.inv_mul_of_unit _ hm_unit,
          ZMod.mul_inv_of_unit _ hm_unit⟩
      have hrm_unit : IsUnit rm := hminv_unit.mul h2_unit
      have hrmval : ((rm.val : ℕ) : ZMod d) = rm := ZMod.natCast_zmod_val rm
      have hcop_rm : Nat.Coprime rm.val d := by
        rw [← ZMod.isUnit_iff_coprime, hrmval]; exact hrm_unit
      -- the residue class `m·n ≡ 2` is the single class `n ≡ rm`.
      have hstep : ∀ p : ℕ,
          (((m : ℕ) : ZMod d) * ((p : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d))
            ↔ (((p : ℕ) : ZMod d) = rm) := by
        intro p
        constructor
        · intro h
          calc ((p : ℕ) : ZMod d)
              = (((m : ℕ) : ZMod d)⁻¹ * ((m : ℕ) : ZMod d)) * ((p : ℕ) : ZMod d) := by
                rw [ZMod.inv_mul_of_unit _ hm_unit, one_mul]
            _ = ((m : ℕ) : ZMod d)⁻¹ * (((m : ℕ) : ZMod d) * ((p : ℕ) : ZMod d)) := by ring
            _ = ((m : ℕ) : ZMod d)⁻¹ * ((R₀ : ℕ) : ZMod d) := by rw [h]
            _ = rm := by rw [hrmdef]
        · intro h
          rw [h, hrmdef]
          calc ((m : ℕ) : ZMod d) * (((m : ℕ) : ZMod d)⁻¹ * ((R₀ : ℕ) : ZMod d))
              = (((m : ℕ) : ZMod d) * ((m : ℕ) : ZMod d)⁻¹) * ((R₀ : ℕ) : ZMod d) := by ring
            _ = ((R₀ : ℕ) : ZMod d) := by rw [ZMod.mul_inv_of_unit _ hm_unit, one_mul]
      have hpr_iff : ∀ p : ℕ, (((p : ℕ) : ZMod d) = rm) ↔ (p % d = rm.val % d) := by
        intro p
        have h := ZMod.natCast_eq_natCast_iff' p rm.val d
        rwa [hrmval] at h
      have hres_pred : ∀ p : ℕ,
          (((m * p : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ↔ (p % d = rm.val % d) := by
        intro p
        rw [Nat.cast_mul, hstep p, hpr_iff p]
      -- block primes `p > N ≥ d` are coprime to `d`, hence `m·p` is a unit.
      have hunit_all : ∀ p : ℕ, N < p → p.Prime → IsUnit ((m * p : ℕ) : ZMod d) := by
        intro p hNp hprime
        have hpd : Nat.Coprime p d := by
          rw [Nat.Prime.coprime_iff_not_dvd hprime]
          intro hdvd
          have hple : p ≤ d := Nat.le_of_dvd (by omega) hdvd
          omega
        rw [Nat.cast_mul]
        exact hm_unit.mul ((ZMod.isUnit_iff_coprime p d).mpr hpd)
      -- rewrite both interval counts into the SW shape.
      have hResCard :
          ((Finset.Ioc N U).filter
              (fun p => p.Prime ∧ ((m * p : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d))).card
            = ((Finset.Ioc N U).filter (fun p => p.Prime ∧ p % d = rm.val % d)).card := by
        congr 1
        apply Finset.filter_congr
        intro p _
        exact and_congr_right (fun _ => hres_pred p)
      have hUnitCard :
          ((Finset.Ioc N U).filter
              (fun p => p.Prime ∧ IsUnit ((m * p : ℕ) : ZMod d))).card
            = ((Finset.Ioc N U).filter (fun p => p.Prime)).card := by
        congr 1
        apply Finset.filter_congr
        intro p hp
        rw [Finset.mem_Ioc] at hp
        constructor
        · exact fun h => h.1
        · intro hpr; exact ⟨hpr, hunit_all p hp.1 hpr⟩
      rw [hResCard, hUnitCard]
      by_cases hNU : N < U
      · -- non-degenerate interval: apply `prime_indicator_SW`.
        have hU2N : U ≤ 2 * N := le_trans (min_le_left _ _) hM2N
        have hbound_sw := hb N U d rm.val hNsw (le_of_lt hNU) hU2N (by omega) hcop_rm hdlog
        have hconv :
            (((Finset.Ioc N U).filter (fun p => p.Prime ∧ p % d = rm.val % d)).card : ℂ)
              - (1 / (d.totient : ℂ)) *
                (((Finset.Ioc N U).filter (fun p => p.Prime)).card : ℂ)
            = ((((Finset.Ioc N U).filter (fun p => p.Prime ∧ p % d = rm.val % d)).card : ℝ)
                - (((Finset.Ioc N U).filter (fun p => p.Prime)).card : ℝ)
                    / (d.totient : ℝ) : ℝ) := by
          push_cast; ring
        rw [hconv, Complex.norm_real, Real.norm_eq_abs]
        exact hbound_sw
      · -- degenerate interval `(N, U]` empty: both counts vanish.
        rw [Finset.Ioc_eq_empty hNU, Finset.filter_empty, Finset.filter_empty,
          Finset.card_empty]
        simp only [Nat.cast_zero, mul_zero, sub_zero, norm_zero]
        exact hboundnn
    · -- `(m, d) > 1`: the residue and unit counts both vanish (`2` a unit ⟹ `m` a unit).
      have hResEmpty :
          ((Finset.Ioc N U).filter
              (fun p => p.Prime ∧ ((m * p : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p _ ⟨_, hres⟩
        have h2u : IsUnit ((R₀ : ℕ) : ZMod d) := (ZMod.isUnit_iff_coprime R₀ d).mpr hcop2
        have hmpu : IsUnit ((m * p : ℕ) : ZMod d) := hres ▸ h2u
        rw [Nat.cast_mul] at hmpu
        exact hcopm ((ZMod.isUnit_iff_coprime m d).mp (isUnit_of_mul_isUnit_left hmpu))
      have hUnitEmpty :
          ((Finset.Ioc N U).filter
              (fun p => p.Prime ∧ IsUnit ((m * p : ℕ) : ZMod d))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p _ ⟨_, hu⟩
        rw [Nat.cast_mul] at hu
        exact hcopm ((ZMod.isUnit_iff_coprime m d).mp (isUnit_of_mul_isUnit_left hu))
      rw [hResEmpty, hUnitEmpty]
      simp only [Nat.cast_zero, mul_zero, sub_zero, norm_zero]
      exact hboundnn
  -- regroup `apDiscBilinCutoff` by fixed `m` (pull `α m` out of both guarded sums).
  have hregroup :
      apDiscBilinCutoff α (blockPrimeInd N) X M R₀ d T
        = ∑ m ∈ Finset.Icc 1 X, α m *
            ((∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
                  if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then blockPrimeInd N n else 0)
              - (1 / (d.totient : ℂ)) *
                (∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
                  if IsUnit ((m * n : ℕ) : ZMod d) then blockPrimeInd N n else 0)) := by
    unfold apDiscBilinCutoff
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_sub]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : IsUnit ((m * n : ℕ) : ZMod d)
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
  rw [hregroup]
  calc ‖∑ m ∈ Finset.Icc 1 X, α m *
            ((∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
                  if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then blockPrimeInd N n else 0)
              - (1 / (d.totient : ℂ)) *
                (∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
                  if IsUnit ((m * n : ℕ) : ZMod d) then blockPrimeInd N n else 0))‖
      ≤ ∑ m ∈ Finset.Icc 1 X, ‖α m *
            ((∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
                  if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then blockPrimeInd N n else 0)
              - (1 / (d.totient : ℂ)) *
                (∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ T),
                  if IsUnit ((m * n : ℕ) : ZMod d) then blockPrimeInd N n else 0))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 X, (K * N / (Real.log N) ^ A) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        rw [Finset.mem_Icc] at hm
        rw [norm_mul]
        calc ‖α m‖ * ‖_‖
            ≤ 1 * (K * N / (Real.log N) ^ A) :=
              mul_le_mul (hα m) (hperm m hm.1) (norm_nonneg _) (by norm_num)
          _ = K * N / (Real.log N) ^ A := one_mul _
    _ = (X : ℝ) * (K * N / (Real.log N) ^ A) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-! ## Item 6 — the summed small-conductor form -/

open Classical in
/-- **`smallconductor_window_sum` — the summed small-conductor windowed SW form (FULL).**  Summing
the per-`d` estimate over the small block `d ≤ D0` absorbs the `D0` factor into one `(log
XM)^{C0}` (there are `≤ D0` conductors), and the scale bookkeeping `K·(log XM)^{A+C0} ≤ Kβ·(log
N)^{A+2C0}` (`log XM`, `log N` the same order — the constant absorbs into `Kβ/K`; taken as a
hypothesis per the recon's exponent bookkeeping) converts the `(log N)`-saving into the target
`(log XM)^A`.  Mirrors `GeneralBV.general_BV_weak`'s small branch / `ConductorDescent`'s
`general_BV_closed` scale step. -/
theorem smallconductor_window_sum {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M T D0 : ℕ) (Dset : Finset ℕ) (r : ℕ → ℕ) (Kβ : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → N₀ ≤ N → M ≤ 2 * N → D0 ≤ N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime (r d) d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        ((N : ℝ) ≤ (M : ℝ)) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + C0) ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        ∑ d ∈ Dset.filter (fun d => d ≤ D0),
            ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
          ≤ Kβ * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hperd⟩ :=
    smallconductor_window_perd (A := A + 2 * C0) (C := C0) (by linarith) hC0
  refine ⟨K, max N₀ 3, hK0, fun α X N M T D0 Dset r Kβ hα hKβ hN hM2N hD0N hDge1 hcopSet
    hLpos hD0 hD0N' hNM hscale => ?_⟩
  classical
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hLApos : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos A
  have hLAC0pos : (0 : ℝ) < L ^ (A + C0) := Real.rpow_pos_of_pos hLpos (A + C0)
  have hlogNAC0pos : (0 : ℝ) < (Real.log N) ^ (A + 2 * C0) := Real.rpow_pos_of_pos hlogN _
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hLcomb : L ^ C0 * L ^ (A + C0) = L ^ (A + 2 * C0) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  -- per-`d` bound in the target shape `Kβ·XM/L^{A+C0}`.
  have hperd' : ∀ d ∈ Dset.filter (fun d => d ≤ D0),
      ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
        ≤ Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + C0) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have hd1 : 1 ≤ d := hDge1 d hd.1
    have hdN : d ≤ N := le_trans hd.2 hD0N
    have hdlogN : (d : ℝ) ≤ (Real.log N) ^ C0 := le_trans (by exact_mod_cast hd.2) hD0N'
    have hbase := hperd α X N M T d (r d) hα hNN₀ hM2N hd1 hdN (hcopSet d hd.1) hdlogN
    -- convert `X·K·N/(log N)^{A+2C0} ≤ Kβ·XM/L^{A+C0}`.
    refine le_trans hbase ?_
    have hXnn : (0 : ℝ) ≤ (X : ℝ) := by positivity
    have hRHS : Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + C0)
        = (X : ℝ) * (Kβ * (M : ℝ) / L ^ (A + C0)) := by rw [mul_div_assoc]; ring
    rw [hRHS]
    refine mul_le_mul_of_nonneg_left ?_ hXnn
    rw [div_le_div_iff₀ hlogNAC0pos hLAC0pos]
    calc K * (N : ℝ) * L ^ (A + C0)
        ≤ K * (M : ℝ) * L ^ (A + C0) := by
          have : K * (N : ℝ) ≤ K * (M : ℝ) := mul_le_mul_of_nonneg_left hNM hK0.le
          exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hLpos.le _)
      _ = (K * L ^ (A + C0)) * M := by ring
      _ ≤ (Kβ * (Real.log N) ^ (A + 2 * C0)) * M :=
          mul_le_mul_of_nonneg_right hscale hMnn
      _ = Kβ * (M : ℝ) * (Real.log N) ^ (A + 2 * C0) := by ring
  -- card of the small block ≤ D0 ≤ L^{C0}.
  have hcard : ((Dset.filter (fun d => d ≤ D0)).card : ℝ) ≤ (D0 : ℝ) := by
    have hsub : Dset.filter (fun d => d ≤ D0) ⊆ Finset.Icc 1 D0 := by
      intro d hd; rw [Finset.mem_filter] at hd; rw [Finset.mem_Icc]
      exact ⟨hDge1 d hd.1, hd.2⟩
    have h1 : (Dset.filter (fun d => d ≤ D0)).card ≤ (Finset.Icc 1 D0).card :=
      Finset.card_le_card hsub
    have h2 : (Finset.Icc 1 D0).card = D0 := by rw [Nat.card_Icc]; omega
    rw [h2] at h1; exact_mod_cast h1
  have hVsmall0 : (0 : ℝ) ≤ Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + C0) := by positivity
  calc ∑ d ∈ Dset.filter (fun d => d ≤ D0),
          ‖apDiscBilinCutoff α (blockPrimeInd N) X M (r d) d T‖
      ≤ ∑ _d ∈ Dset.filter (fun d => d ≤ D0),
          Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + C0) := Finset.sum_le_sum hperd'
    _ = ((Dset.filter (fun d => d ≤ D0)).card : ℝ)
          * (Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + C0)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D0 : ℝ) * (Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + C0)) :=
        mul_le_mul_of_nonneg_right hcard hVsmall0
    _ ≤ L ^ C0 * (Kβ * ((X : ℝ) * (M : ℝ)) / L ^ (A + C0)) :=
        mul_le_mul_of_nonneg_right hD0 hVsmall0
    _ = Kβ * ((X : ℝ) * (M : ℝ)) / L ^ A := by
        have hLA' : L ^ A ≠ 0 := ne_of_gt hLApos
        have hLC0' : L ^ C0 ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hLpos C0)
        rw [Real.rpow_add hLpos A C0]
        field_simp

/-! ## Item 8 — the window-in-carrier identification

The landed `PairBijection.blockBox_pair_card` bundles the *window corner* hypotheses
(`hwin_lo`/`hwin_hi`) and consumes them in its surjectivity branch to place the reconstructed
triple in `tripleSet` (whose membership carries the window `x/2+2 ≤ prod3 ≤ x`).  Its reusable
internals (`pairTerm_eq`, `summand_eq`, `prime_pair_unique`) are `private`.  In the
window-in-carrier route the box may cross the window boundary, so the corners are FALSE — the
window instead comes from the cutoff `T`.  We re-derive the corner-free bijection here: it enters as
a class-predicate hypothesis `hPwin` (from the cutoff), keeping only the ordering clearance `hord`
(available for high pieces `N ≥ y`, the recon's R1).  The two one-sided cutoffs are `T_hi = x` and
`T_lo = x/2+1` (`= (x/2+2) − 1`); their difference is the window `x/2+2 ≤ prod3 ≤ x`. -/

/-- Re-proof of `PairBijection.prime_pair_unique` (private there): the oriented `m ↦ {p₁,p₂}`
factorization at `y` is unique. -/
private lemma prime_pair_unique_win {y p₁ p₂ p₁' p₂' : ℕ}
    (h1 : p₁.Prime) (h1' : p₁'.Prime) (h2' : p₂'.Prime)
    (hp1 : p₁ ≤ y) (hp2' : y < p₂')
    (heq : p₁ * p₂ = p₁' * p₂') : p₁ = p₁' ∧ p₂ = p₂' := by
  have hdvd : p₁ ∣ p₁' * p₂' := heq ▸ dvd_mul_right p₁ p₂
  rcases (Nat.Prime.dvd_mul h1).mp hdvd with hd | hd
  · have heqp : p₁ = p₁' := (Nat.prime_dvd_prime_iff_eq h1 h1').mp hd
    refine ⟨heqp, ?_⟩
    rw [heqp] at heq
    exact Nat.eq_of_mul_eq_mul_left h1'.pos heq
  · have heqp : p₁ = p₂' := (Nat.prime_dvd_prime_iff_eq h1 h2').mp hd
    omega

open Classical in
/-- Re-proof of `PairBijection.summand_eq` (private there): the `apDiscBilin` summand is the
`pairPred` `0/1` indicator. -/
private lemma summand_eq_win (z y : ℕ) (ε₀ : ℝ) (j N a b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ × ℕ) :
    (if P (q.1 * q.2) then
        restrictAlpha (blockAlpha z y ε₀ j) a b q.1 * blockPrimeInd N q.2 else (0 : ℂ))
      = (if pairPred z y ε₀ j N a b P q then (1 : ℂ) else 0) := by
  classical
  unfold pairPred restrictAlpha blockAlpha blockPrimeInd
  by_cases hP : P (q.1 * q.2)
  · by_cases hbox : a ≤ q.1 ∧ q.1 < b
    · by_cases hf : (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧
          p₁ * p₂ = q.1 ∧ blockIdx z ε₀ p₁ = j)
      · by_cases hn : N < q.2 ∧ q.2.Prime
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_pos hn, if_pos ⟨hP, hbox, hf, hn⟩, mul_one]
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_neg hn, mul_zero,
            if_neg (fun h => hn h.2.2.2)]
      · rw [if_pos hP, if_pos hbox, if_neg hf, zero_mul, if_neg (fun h => hf h.2.2.1)]
    · rw [if_pos hP, if_neg hbox, zero_mul, if_neg (fun h => hbox h.2.1)]
  · rw [if_neg hP, if_neg (fun h => hP h.1)]

open Classical in
/-- Re-proof of `PairBijection.pairTerm_eq` (private there): the `apDiscBilin` double sum counts
the `pairPred` pairs. -/
private lemma pairTerm_eq_win (z y : ℕ) (ε₀ : ℝ) (j N a b X M : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 M,
        if P (m * n) then
          restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
            (fun q => pairPred z y ε₀ j N a b P q)).card : ℂ) := by
  classical
  rw [← Finset.sum_product']
  rw [Finset.sum_congr rfl (fun q _ => summand_eq_win z y ε₀ j N a b P q)]
  rw [Finset.sum_boole]

open Classical in
/-- **`blockBox_windowed_pair_card` — the corner-free pair bijection (window from the predicate).**
The analogue of `PairBijection.blockBox_pair_card` with the window corner hypotheses replaced by
`hPwin` (the class predicate carries the window, supplied by the cutoff).  Injectivity is
`prime_pair_unique_win`; surjectivity reconstructs the triple, deriving `p₂ ≤ p₃` from `hord`
(`p₂·z ≤ p₁p₂ = m < b ≤ zN+1`) and the window from `hPwin` (NOT from corners). -/
theorem blockBox_windowed_pair_card {x z y : ℕ} {ε₀ : ℝ} {j N M a b X : ℕ}
    (P : ℕ → Prop) [DecidablePred P]
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1)
    (hPwin : ∀ v : ℕ, P v → x / 2 + 2 ≤ v ∧ v ≤ x) :
    (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter (fun q => pairPred z y ε₀ j N a b P q)).card)
      = (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ P (prod3 t) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card) := by
  classical
  symm
  apply Finset.card_bij (fun t _ => (t.1 * t.2.1, t.2.2))
  · intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htri, hblk, hP, hNlt, hMle, hab_lo, hab_hi⟩ := ht
    rw [tripleSet, Finset.mem_filter] at htri
    obtain ⟨_, hzp1, hp1y, hyp2, _hp2p3, hp1prime, hp2prime, hp3prime, _hwlo, _hwhi⟩ := htri
    have hm1 : 1 ≤ t.1 * t.2.1 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hp1prime.pos.ne' hp2prime.pos.ne')
    have hmX : t.1 * t.2.1 ≤ X := by omega
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hm1, hmX⟩, ⟨hp3prime.pos, hMle⟩⟩,
      hP, ⟨hab_lo, hab_hi⟩,
      ⟨t.1, t.2.1, hp1prime, hp2prime, hzp1, hp1y, hyp2, rfl, hblk⟩, ⟨hNlt, hp3prime⟩⟩
  · intro t ht t' ht' heq
    rw [Finset.mem_filter] at ht ht'
    have htri := ht.1
    have htri' := ht'.1
    rw [tripleSet, Finset.mem_filter] at htri htri'
    obtain ⟨_, _, hp1y, _, _, hp1prime, _, _, _, _⟩ := htri
    obtain ⟨_, _, _, hyp2', _, hp1prime', hp2prime', _, _, _⟩ := htri'
    rw [Prod.mk.injEq] at heq
    obtain ⟨hmeq, hneq⟩ := heq
    obtain ⟨he1, he2⟩ := prime_pair_unique_win hp1prime hp1prime' hp2prime' hp1y hyp2' hmeq
    exact Prod.ext_iff.mpr ⟨he1, Prod.ext_iff.mpr ⟨he2, hneq⟩⟩
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨hq1lo, _hq1hi⟩, hq2lo, hq2hi⟩, hpp⟩ := hq
    obtain ⟨hP, ⟨ha_lo, ha_hi⟩, ⟨p₁, p₂, hp1prime, hp2prime, hzp1, hp1y, hyp2, hprod, hblk⟩,
      ⟨hNq2, hq2prime⟩⟩ := hpp
    have hp2z : p₂ * z ≤ p₁ * p₂ := by
      have h : p₂ * z ≤ p₂ * p₁ := Nat.mul_le_mul_left p₂ hzp1
      rwa [mul_comm p₂ p₁] at h
    have hp2N : p₂ ≤ N := by
      have h1 : p₂ * z ≤ b - 1 := by rw [hprod] at hp2z; omega
      have h2 : z * p₂ ≤ z * N := by rw [mul_comm z p₂]; omega
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    have hord3 : p₂ ≤ q.2 := by omega
    obtain ⟨hwlo, hwhi⟩ := hPwin (q.1 * q.2) hP
    have hprod3 : prod3 (p₁, p₂, q.2) = q.1 * q.2 := by
      change p₁ * p₂ * q.2 = q.1 * q.2; rw [hprod]
    have hq1x : q.1 ≤ x := le_trans (Nat.le_mul_of_pos_right q.1 (by omega)) hwhi
    have hq2x : q.2 ≤ x := le_trans (Nat.le_mul_of_pos_left q.2 (by omega)) hwhi
    have hp1le : p₁ ≤ q.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_right p₁ hp2prime.pos
    have hp2le : p₂ ≤ q.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_left p₂ hp1prime.pos
    refine ⟨(p₁, p₂, q.2), ?_, Prod.ext_iff.mpr ⟨hprod, rfl⟩⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hblk, ?_, hNq2, hq2hi, ?_, ?_⟩
    · rw [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨⟨hp1prime.pos, le_trans hp1le hq1x⟩, ⟨hp2prime.pos, le_trans hp2le hq1x⟩,
          ⟨hq2prime.pos, hq2x⟩⟩,
        hzp1, hp1y, hyp2, hord3, hp1prime, hp2prime, hq2prime, ?_, ?_⟩
      · rw [hprod3]; exact hwlo
      · rw [hprod3]; exact hwhi
    · rw [hprod3]; exact hP
    · change a ≤ p₁ * p₂
      rw [hprod]; exact ha_lo
    · change p₁ * p₂ < b
      rw [hprod]; exact ha_hi

open Classical in
/-- **The cutoff-difference is the windowed pair count.**  Subtracting the `T = x/2+1` cutoff term
from the `T = x` cutoff term leaves the window `x/2+2 ≤ m·n ≤ x` folded into the class predicate,
and `pairTerm_eq_win` counts the surviving pairs.  The `±1`: `T_lo = (x/2+2) − 1 = x/2+1`, so the
difference guard `x/2+1 < m·n ≤ x` is exactly `x/2+2 ≤ m·n ≤ x`. -/
private lemma cutoffDiff_eq_pairCard (x z y : ℕ) (ε₀ : ℝ) (j N M a b X : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (hxlo : x / 2 + 1 ≤ x) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
        if P (m * n) then
          restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else (0 : ℂ))
      - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
        if P (m * n) then
          restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
          (fun q => pairPred z y ε₀ j N a b
            (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ P v) q)).card : ℂ) := by
  classical
  rw [← pairTerm_eq_win z y ε₀ j N a b X M (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ P v),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hP : P (m * n)
  · by_cases hx : m * n ≤ x
    · by_cases hlo : m * n ≤ x / 2 + 1
      · have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨hw, _, _⟩ => by omega
        rw [if_pos hx, if_pos hlo, sub_self, if_neg hnw]
      · rw [if_pos hx, if_neg hlo, sub_zero, if_pos hP,
          if_pos (show x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n) from ⟨by omega, hx, hP⟩)]
    · have hlo : ¬ m * n ≤ x / 2 + 1 := by omega
      have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨_, hw, _⟩ => by omega
      rw [if_neg hx, if_neg hlo, sub_self, if_neg hnw]
  · have hnw : ¬ (x / 2 + 2 ≤ m * n ∧ m * n ≤ x ∧ P (m * n)) := fun ⟨_, _, hp⟩ => hP hp
    simp only [if_neg hP, if_neg hnw, ite_self, sub_self]

open Classical in
/-- **`blockBox_windowDisc_eq_res` — the window-in-carrier identification at a FREE residue
`R₀` (H-AMENDMENT 2 C4).**  The residue-generalized core of `blockBox_windowDisc_eq`: on an
ordering-cleared box the difference of the two one-sided cutoff carriers at residue `R₀` equals
the raw `tripleSet` class-count difference at the class `prod3 ≡ R₀ (mod d)`.  NO coprimality is
required — this is an exact counting identity (the residue never enters the bijection).  The
landed `R₀ = 2` wrapper below folds the counts into `blockBoxResCount`/`blockBoxUnitCount`; the
W-mirror instantiates `d := Q·d'`, `R₀ :=` the CRT class combining `a+2 (mod Q)`, `2 (mod d')`. -/
theorem blockBox_windowDisc_eq_res {x z y : ℕ} {ε₀ : ℝ} {j N M a b X d R₀ : ℕ}
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x) :
    apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M R₀ d x
      - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M R₀ d
          (x / 2 + 1)
      = (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) ∧
            N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ)
        - (1 / (d.totient : ℂ)) *
          (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            IsUnit ((prod3 t : ℕ) : ZMod d) ∧
            N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ) := by
  classical
  -- window redundancy: on `tripleSet` the folded window `x/2+2 ≤ prod3 ≤ x` is automatic.
  have hredRes : ((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        (x / 2 + 2 ≤ prod3 t ∧ prod3 t ≤ x ∧ ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card
      = ((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card := by
    apply congrArg
    apply Finset.filter_congr
    intro t ht
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hwlo, hwhi⟩ := ht
    constructor
    · rintro ⟨h1, ⟨_, _, hr⟩, hrest⟩; exact ⟨h1, hr, hrest⟩
    · rintro ⟨h1, hr, hrest⟩; exact ⟨h1, ⟨hwlo, hwhi, hr⟩, hrest⟩
  have hredUnit : ((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        (x / 2 + 2 ≤ prod3 t ∧ prod3 t ≤ x ∧ IsUnit ((prod3 t : ℕ) : ZMod d)) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card
      = ((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
        IsUnit ((prod3 t : ℕ) : ZMod d) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card := by
    apply congrArg
    apply Finset.filter_congr
    intro t ht
    rw [tripleSet, Finset.mem_filter] at ht
    obtain ⟨_, _, _, _, _, _, _, _, hwlo, hwhi⟩ := ht
    constructor
    · rintro ⟨h1, ⟨_, _, hr⟩, hrest⟩; exact ⟨h1, hr, hrest⟩
    · rintro ⟨h1, hr, hrest⟩; exact ⟨h1, ⟨hwlo, hwhi, hr⟩, hrest⟩
  -- the pair count → `tripleSet` count chains (corner-free bijection + redundancy).
  have hcardRes := (blockBox_windowed_pair_card
    (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d))
    (M := M) hz hbX hord (fun v hv => ⟨hv.1, hv.2.1⟩)).trans hredRes
  have hcardUnit := (blockBox_windowed_pair_card
    (fun v => x / 2 + 2 ≤ v ∧ v ≤ x ∧ IsUnit ((v : ℕ) : ZMod d))
    (M := M) hz hbX hord (fun v hv => ⟨hv.1, hv.2.1⟩)).trans hredUnit
  -- residue / unit cutoff differences equal the `tripleSet` counts.
  have hRes :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else 0)
        = (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            ((prod3 t : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) ∧
            N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ) := by
    rw [cutoffDiff_eq_pairCard x z y ε₀ j N M a b X
      (fun v => ((v : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d)) hxlo, hcardRes]
  have hUnit :
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else 0)
        - (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if IsUnit ((m * n : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else 0)
        = (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
            IsUnit ((prod3 t : ℕ) : ZMod d) ∧
            N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℂ) := by
    rw [cutoffDiff_eq_pairCard x z y ε₀ j N M a b X
      (fun v => IsUnit ((v : ℕ) : ZMod d)) hxlo, hcardUnit]
  -- unfold the two carriers (definitional), rearrange, and substitute.
  have hexpx : apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
        (blockPrimeInd N) X M R₀ d x
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else 0) :=
    rfl
  have hexplo : apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b)
        (blockPrimeInd N) X M R₀ d (x / 2 + 1)
      = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
          if ((m * n : ℕ) : ZMod d) = ((R₀ : ℕ) : ZMod d) then
            restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else 0)
        - (1 / (d.totient : ℂ)) *
          (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 M).filter (fun n => m * n ≤ x / 2 + 1),
            if IsUnit ((m * n : ℕ) : ZMod d) then
              restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else 0) :=
    rfl
  rw [hexpx, hexplo]
  rw [show ∀ (r1 u1 r2 u2 : ℂ),
      (r1 - (1 / (d.totient : ℂ)) * u1) - (r2 - (1 / (d.totient : ℂ)) * u2)
        = (r1 - r2) - (1 / (d.totient : ℂ)) * (u1 - u2) from fun r1 u1 r2 u2 => by ring]
  rw [hRes, hUnit]

open Classical in
/-- **`blockBox_windowDisc_eq` — the window-in-carrier identification (item 8, FULL).**  On a box
that is ordering-cleared (`hord : b ≤ zN+1`, automatic for high pieces `N ≥ y`) — but with NO
window corner hypotheses — the block's honest box discrepancy IS the difference of the two
one-sided cutoff carriers at `T = x` and `T = x/2+1`:
```
apDiscBilinCutoff (restrictAlpha (blockAlpha j) a b) (blockPrimeInd N) X M 2 d x
  − apDiscBilinCutoff (restrictAlpha (blockAlpha j) a b) (blockPrimeInd N) X M 2 d (x/2+1)
    = blockBoxResCount − (1/φd)·blockBoxUnitCount.
```
The window `x/2+2 ≤ prod3 ≤ x` now lives in the cutoff (route (i)): the difference of the two
cutoffs is exactly the window (`cutoffDiff_eq_pairCard`), the corner-free bijection
`blockBox_windowed_pair_card` identifies the surviving pairs with `tripleSet` triples, and the
`tripleSet` window makes the folded window redundant.  The `±1`: `T_hi = x`, `T_lo = (x/2+2) − 1
= x/2+1`.  Mirrors `PairBijection.blockBox_apDiscBilin_eq`, corner-free and cutoff-aware.
(The `R₀ = 2` instance of `blockBox_windowDisc_eq_res`, folded into the landed count objects.) -/
theorem blockBox_windowDisc_eq {x z y : ℕ} {ε₀ : ℝ} {j N M a b X d : ℕ}
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x) :
    apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d x
      - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d
          (x / 2 + 1)
      = ((blockBoxResCount x z y ε₀ j N M a b d : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) * ((blockBoxUnitCount x z y ε₀ j N M a b d : ℝ) : ℂ) := by
  rw [blockBox_windowDisc_eq_res hz hbX hord hxlo, blockBoxResCount, blockBoxUnitCount]
  push_cast
  ring

end Salt.Chen
