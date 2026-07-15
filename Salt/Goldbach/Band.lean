/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.SwitchBV
import Salt.Chen.PDiag

/-!
# G-BAND — the Goldbach band/pairing/aggregation layer (wave W3): S2 KERNELS + SCOPE FLAG

Design: `docs/exploration/q1-design.md`, node **G-BAND** (D3).  This layer sits between G-SW's
block identification (`Salt/Goldbach/SwitchBV.lean` — `goldBlockHonestDiscW`,
`gold_hBVblocksW_of_generalBV`) and the A₃ main-term discharge; its terminal target is the
Goldbach mirror of `Salt.Chen.hBVblocksW_discharge'` (`Salt/Chen/PDiag.lean:682`).

## SCOPE FINDING (flagged — see `docs/blueprints/flags.md`, the G-BAND entry)

An execution-time measurement against the twin templates shows the node as scoped
(one 380k-token, class-B node → the terminal `gold_hBVblocksW_discharge'`) is **≥ 2× over
budget** and must be re-cut by the house.  The internal machinery of the terminal
(`hBlockW_of_window_prices`, `hNum_at_opW`, `PloW_sym/low_of_box_disc`, `PloW_honest`, the band
close, and the diagonal aggregate) is NOT carrier-generic: it is stated over the twin
`Salt.Chen.tripleSet` and, crucially, the **window identification**
`Salt.Chen.blockBox_windowDisc_eq_res` (`WindowSW`) hard-wires the twin TOP-half window
`x/2+2 ≤ prod ≤ x` as the *difference* of two `apDiscBilinCutoff` cutoffs (`x` and `x/2+1`).
The Goldbach carrier `goldTripleSet` uses the BOTTOM-half window `2 ≤ prod ≤ N/2` (G-SW's
recorded structural novelty), which reshapes the identification to a SINGLE cutoff — so the
whole box/band/diagonal chain is a genuine re-derivation, not a class-instantiation.  The
generic bilinear/Kerr pricing engine (`apDiscBilinCutoff`, `box_disc_three_way`,
`medium_survivor_price_sqrtD`, `medium_support_floor_high`, `dyadicBoundary`, `blockAlpha`,
`blockPrimeInd`, `restrictAlpha`) IS carrier-agnostic and reuses verbatim; but the tripleSet-tied
mirrors (SwitchW2 Parts A–G + PDiag + the BandIdent/BandClose identifications + the WindowSW
identification) total ~1500–2500 lines.  Re-cut proposal + the reuse census are in the flags
entry.

## What this file LANDS (the S2-critical, self-contained kernels — de-risking the re-cut)

The task's item-2 kernel: the divisibility mirror of `Salt.Chen.dvd_sub_two_of_resW`
(`PDiag:277`) at the reflected switch class `prod ≡ N (mod d)` (vs the twin `≡ 2`), and the
diagonal residue-leg crumb it feeds (the residue side of the future `goldDiagAggW_le_honest`,
the hardest leg of the PDiag terminal).  Both are class-generic in the modulus and reuse the
N-free `Salt.Chen.rough_divisor_crumb` verbatim.  Mind the ℕ-subtraction: the twin's `prod − 2`
becomes `N − prod`, so the direction of `Nat.modEq_iff_dvd'` flips (`prod ≤ N`, free at the
window; matches how `gold_memClassG` handled saturation via `n ≤ N`).

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset ArithmeticFunction Salt.Chen

namespace Salt.Goldbach

/-! ## The S2-critical divisibility mirror (`dvd_sub_two_of_resW` at the Goldbach class) -/

/-- **`gold_dvd_sub_of_resG` — the residue-side kernel of the Goldbach diagonal crumb.**  The W
residue condition at modulus `Q·d` forces `d ∣ N − v`: the CRT class `crtClassG Q d N a` is
`≡ N (mod d)` (`crtClassG_modEq_right`), so the `d`-component of the congruence is the reflected
switch congruence `v ≡ N (mod d)`.  Mirrors `Salt.Chen.dvd_sub_two_of_resW` under
`prod − 2 ↦ N − prod` (the ℕ-subtraction flips: the twin needs `2 ≤ v`, here `v ≤ N`). -/
lemma gold_dvd_sub_of_resG {Q d N a v : ℕ} (hQd : Nat.Coprime Q d) (hvN : v ≤ N)
    (hres : ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d))) :
    d ∣ N - v := by
  have h1 : v ≡ crtClassG Q d N a [MOD Q * d] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hres
  have h2 : v ≡ N [MOD d] :=
    (Nat.ModEq.of_mul_left Q h1).trans (crtClassG_modEq_right N a hQd)
  exact (Nat.modEq_iff_dvd' hvN).mp h2

/-- **`gold_diag_residue_crumb` — the residue leg of the honest diagonal aggregate.**  At any
window point `v < N`, the admissible divisors `d ∣ Ps` whose Q-shifted residue class is met by
`v` number at most `2^{Nat.log w' N}` — NOT `τ(Ps)`: each such `d` divides `N − v`
(`gold_dvd_sub_of_resG`, `Coprime Q d` from `hQPs`), and a `w'`-rough squarefree `Ps` has at most
`2^{Nat.log w' N}` divisors of any `1 ≤ N − v ≤ N` (the N-free `rough_divisor_crumb`, reused
verbatim).  This is the Goldbach mirror of the residue leg inside `Salt.Chen.diagAggW_le_honest`
(`PDiag:397`) at the reflected class; the unit leg (`Σ ν(d)`) and the global support cap
(ingredient (i)) reuse the N-free `nuChen_sum_divisors_le`/`rough_divisor_crumb`. -/
lemma gold_diag_residue_crumb {Q Ps w' N v a : ℕ}
    (hPs : Squarefree Ps) (hw' : 2 ≤ w') (hPw' : ∀ p ∈ Ps.primeFactors, w' ≤ p)
    (hQPs : Nat.Coprime Q Ps) (hvlt : v < N) :
    ((Nat.divisors Ps).filter
        (fun d => ((v : ℕ) : ZMod (Q * d)) = ((crtClassG Q d N a : ℕ) : ZMod (Q * d)))).card
      ≤ 2 ^ Nat.log w' N := by
  refine le_trans (Finset.card_le_card ?_)
    (rough_divisor_crumb hPs hw' hPw' (by omega) (Nat.sub_le N v))
  intro d hd
  rw [Finset.mem_filter] at hd ⊢
  obtain ⟨hdPs, hres⟩ := hd
  have hQd : Nat.Coprime Q d := hQPs.coprime_dvd_right (Nat.mem_divisors.mp hdPs).1
  exact ⟨hdPs, gold_dvd_sub_of_resG hQd (le_of_lt hvlt) hres⟩

end Salt.Goldbach
