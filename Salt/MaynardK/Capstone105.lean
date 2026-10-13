/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.WinCore105
import Salt.Maynard.GehWindowPnt
import Salt.BV.AbelCore
import Salt.SW.Gate

/-!
# B4.6 — the k = 105 capstones over the slack (C1)

`SlackEv105` is the body of B4.5c's `winSlackM105_ev`. Generic in the tuple (`TupleChoice`):
the `105`-entries are assumed `≤ 743` (`hle`) and, for the gap forms, the diameter `≤ d` (`hdiam`).
Over it:

* `gaps_le_of_level_of_slack`: `WindowPNT → HasLevel (1/2) →` gaps `≤ d`, through
  `winFrontierMW105_of` and `gaps_le_of_frontier105` at `D = max D₀ (12·105²)`;
* `gaps_le_of_slack`: the same with `windowPNT_holds` and
  `hasLevel_half_of_siegelWalfisz siegelWalfisz_holds` discharged inside;
* `maynard_105_of_slack`: the tuple form — infinitely many `n` with at least two primes
  among `n + hSeq 105 i`.

Maynard's proof of Theorem 1.3 (arXiv:1311.4600v3, p. 3; Prop. 4.2 and Prop. 4.3(2),
`M₁₀₅ > 4`) run at k = 105; `Gaps636` instantiates these at the standard tuple (the first 105
primes greater than 105, diameter 636).
Nothing here bears on twin primes.
-/

open Finset Filter Topology

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Maynard Salt.Twelve Salt.MaynardK

/-- The slack proposition: the statement of `winSlackM105_ev` (`Slack105`), verbatim. -/
def SlackEv105 : Prop :=
  ∃ D₀ : ℕ, 744 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ C₀ : ℝ, 0 ≤ C₀ →
    ∀ᶠ N' : ℕ in atTop, WinSlackM105 D C₀ N'

/-- The frontier at a single admissible `D`, from the slack. -/
theorem frontier_of_slack (hS : SlackEv105) (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743) :
    ∃ D : ℕ, 744 ≤ D ∧ 12 * 105 ^ 2 ≤ D ∧ WinFrontierMW105 D := by
  obtain ⟨D₀, hD₀, hslack⟩ := hS
  refine ⟨max D₀ (12 * 105 ^ 2), le_trans hD₀ (le_max_left _ _), le_max_right _ _, ?_⟩
  exact winFrontierMW105_of (max D₀ (12 * 105 ^ 2)) (le_trans hD₀ (le_max_left _ _)) hle
    (fun C₀ hC₀ => hslack _ (le_max_left _ _) C₀ hC₀)

/-- **(1) Interface form.** -/
theorem gaps_le_of_level_of_slack (hS : SlackEv105) (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743)
    (d : ℤ) (hdiam : ∀ i j : Fin 105, (hSeq 105 j : ℤ) - (hSeq 105 i : ℤ) ∈ Set.Icc (-d) d)
    (hPNT : WindowPNT) (hLoD : HasLevel (1 / 2)) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-d) d := by
  obtain ⟨D, hD, hDk, hF⟩ := frontier_of_slack hS hle
  exact gaps_le_of_frontier105 D hD hDk hle d hdiam hPNT hLoD hF

/-- **(2) Gap form, over the slack only.** -/
theorem gaps_le_of_slack (hS : SlackEv105) (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743)
    (d : ℤ) (hdiam : ∀ i j : Fin 105, (hSeq 105 j : ℤ) - (hSeq 105 i : ℤ) ∈ Set.Icc (-d) d) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-d) d :=
  gaps_le_of_level_of_slack hS hle d hdiam windowPNT_holds
    (Salt.BV.hasLevel_half_of_siegelWalfisz Salt.SW.siegelWalfisz_holds)

/-- **(3) Tuple form, over the slack only.** -/
theorem maynard_105_of_slack (hS : SlackEv105) (hle : ∀ i : Fin 105, hSeq 105 i ≤ 743) :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧
      2 ≤ (Finset.univ.filter (fun i : Fin 105 => (n + hSeq 105 i).Prime)).card := by
  intro N
  obtain ⟨D, hD, hDk, hF⟩ := frontier_of_slack hS hle
  obtain ⟨N', R, ν₀, δ, errEH, cval, hNN', hsol, hφpos, hcvnn, hδ0, hDpi, hQlow,
    hS2low, hslack⟩ := hF windowPNT_holds
      (Salt.BV.hasLevel_half_of_siegelWalfisz Salt.SW.siegelWalfisz_holds) N
  have hgt := win_core_105 N' R ν₀ (primorial D) D δ errEH cval
    (primorial_sqf' D) (primorial_hDlt D) (fun i => lt_of_le_of_lt (hle i) hD)
    hDk hsol hφpos hcvnn hδ0 hDpi hQlow hS2low hslack
  obtain ⟨n, hn, hcard⟩ := exists_window_two_primesW_k 105 64 N' R ν₀ (primorial D) _ hgt
  have hnN : N' < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  exact ⟨n, by omega, hcard⟩


end Salt.MaynardK
