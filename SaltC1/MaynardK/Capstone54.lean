/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.WinCore54
import Salt.Maynard.GehWindowPnt
import Salt.BV.AbelCore
import Salt.SW.Gate

/-!
# B4.6 — the k = 54 capstones over the slack (C1)

`SlackEv54` is the body of B4.5c's `winSlackM54_ev`. Generic in the tuple (`TupleChoice`):
the `54`-entries are assumed `≤ 270` (`hle`) and, for the gap forms, the diameter `≤ d` (`hdiam`).
Over it:

* `gaps_le_of_level_of_slack`: `WindowPNT → HasLevel (1/2) →` gaps `≤ d`, through
  `winFrontierMW54_of` and `gaps_le_of_frontier54` at `D = max D₀ (12·54²)`;
* `gaps_le_of_slack`: the same with `windowPNT_holds` and
  `hasLevel_half_of_siegelWalfisz siegelWalfisz_holds` discharged inside;
* `maynard_54_of_slack`: the tuple form — infinitely many `n` with at least two primes
  among `n + hSeq 54 i`.

Maynard's argument (arXiv:1311.4600v3, Prop. 4.2 and Prop. 4.3) run at k = 54, towards DHL[54, 2]
(Polymath 8b, arXiv:1407.4897v4: Thm 3.9(vii), M₅₄ > 4.00238, p. 14, with the Bombieri–Vinogradov
theorem, p. 14), over the certificate `M₅₄ > 4.0015` (`ratio_cert_54`); the tuple itself is
instantiated elsewhere.
Nothing here bears on twin primes.
-/

open Finset Filter Topology

namespace SaltC1.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Maynard Salt.Twelve Salt.MaynardK

/-- The slack proposition: the statement of `winSlackM54_ev` (`Slack54`), verbatim. -/
def SlackEv54 : Prop :=
  ∃ D₀ : ℕ, 271 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ C₀ : ℝ, 0 ≤ C₀ →
    ∀ᶠ N' : ℕ in atTop, WinSlackM54 D C₀ N'

/-- The frontier at a single admissible `D`, from the slack. -/
theorem frontier_of_slack (hS : SlackEv54) (hle : ∀ i : Fin 54, hSeq 54 i ≤ 270) :
    ∃ D : ℕ, 271 ≤ D ∧ 12 * 54 ^ 2 ≤ D ∧ WinFrontierMW54 D := by
  obtain ⟨D₀, hD₀, hslack⟩ := hS
  refine ⟨max D₀ (12 * 54 ^ 2), le_trans hD₀ (le_max_left _ _), le_max_right _ _, ?_⟩
  exact winFrontierMW54_of (max D₀ (12 * 54 ^ 2)) (le_trans hD₀ (le_max_left _ _)) hle
    (fun C₀ hC₀ => hslack _ (le_max_left _ _) C₀ hC₀)

/-- **(1) Interface form.** -/
theorem gaps_le_of_level_of_slack (hS : SlackEv54) (hle : ∀ i : Fin 54, hSeq 54 i ≤ 270)
    (d : ℤ) (hdiam : ∀ i j : Fin 54, (hSeq 54 j : ℤ) - (hSeq 54 i : ℤ) ∈ Set.Icc (-d) d)
    (hPNT : WindowPNT) (hLoD : HasLevel (1 / 2)) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-d) d := by
  obtain ⟨D, hD, hDk, hF⟩ := frontier_of_slack hS hle
  exact gaps_le_of_frontier54 D hD hDk hle d hdiam hPNT hLoD hF

/-- **(2) Gap form, over the slack only.** -/
theorem gaps_le_of_slack (hS : SlackEv54) (hle : ∀ i : Fin 54, hSeq 54 i ≤ 270)
    (d : ℤ) (hdiam : ∀ i j : Fin 54, (hSeq 54 j : ℤ) - (hSeq 54 i : ℤ) ∈ Set.Icc (-d) d) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-d) d :=
  gaps_le_of_level_of_slack hS hle d hdiam windowPNT_holds
    (Salt.BV.hasLevel_half_of_siegelWalfisz Salt.SW.siegelWalfisz_holds)

/-- **(3) Tuple form, over the slack only.** -/
theorem maynard_54_of_slack (hS : SlackEv54) (hle : ∀ i : Fin 54, hSeq 54 i ≤ 270) :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧
      2 ≤ (Finset.univ.filter (fun i : Fin 54 => (n + hSeq 54 i).Prime)).card := by
  intro N
  obtain ⟨D, hD, hDk, hF⟩ := frontier_of_slack hS hle
  obtain ⟨N', R, ν₀, δ, errEH, cval, hNN', hsol, hφpos, hcvnn, hδ0, hDpi, hQlow,
    hS2low, hslack⟩ := hF windowPNT_holds
      (Salt.BV.hasLevel_half_of_siegelWalfisz Salt.SW.siegelWalfisz_holds) N
  have hgt := win_core_54 N' R ν₀ (primorial D) D δ errEH cval
    (primorial_sqf' D) (primorial_hDlt D) (fun i => lt_of_le_of_lt (hle i) hD)
    hDk hsol hφpos hcvnn hδ0 hDpi hQlow hS2low hslack
  obtain ⟨n, hn, hcard⟩ := exists_window_two_primesW_k 54 64 N' R ν₀ (primorial D) _ hgt
  have hnN : N' < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  exact ⟨n, by omega, hcard⟩


end SaltC1.MaynardK
