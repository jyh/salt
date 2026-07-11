/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.InnerS1
import Salt.Twelve.InnerS2
import Salt.Twelve.CollisionYF_S2
import Salt.Twelve.WinFrontierDischarge
import Salt.Twelve.MvSplit
import Salt.Twelve.PhiUpperReindex

/-!
# Node C, card NC-3 — `gaps_le_twelve` (THE CLOSURE)

Design: `docs/blueprints/explicit12-design.md`, card **NC-3** (in "# Node C — THE
CLOSURE"), the "Error budget" and "Archimedes" notes.

This module assembles the two now-discharged inner atoms
(`collision_yF_M` — NC-1, the *unconditional* S₁ collision bound; and
`s2_inner_yF`/`s2_collision_le_QdiagW_C` — NC-2, the S₂ collision bound) together
with the landed endgame scaffold (`WinCore`, `WinFrontierDischarge`,
`Pigeonhole12`) into the explicit bounded-prime-gaps theorem `gaps_le_twelve`.

The whole WinCore endgame is `W'`-generic, so it is re-threaded here at the
abstract Archimedean modulus `primorial Dfin` (rather than WinCore's numeral
`Dstar`); `primorial Dfin` is **never evaluated**.

## What is discharged here

* **S₁ inner atom — closed.**  WinCore's `sharp_S1_upperW` consumes the
  *yside*-based `S1InnerBound` hypothesis (`hInner`).  Here `win_core_M` mirrors
  that sharp bound using the NC-1 corollary `collision_yF_M`
  (`|s1CollisionForm| ≤ 12·5²/D · M`, `M = ∑ 1/∏φ`) — which is UNCONDITIONAL —
  so no S₁ inner-atom hypothesis survives.
* **S₂ collision — closed at `Fstar1`.**  `s2_collision_yF_C` folds
  `s2_inner_yF` (NC-2) + `qdiag_bridge`-based `hQd` discharge (`hQd_Fstar1`) +
  `s2_collision_le_QdiagW_C` into the `Qdiag`-relative S₂ collision bound
  `|Qdiag_mW − s2CompatFormM| ≤ 1200·CF/D · Qdiag_mW`.

The remaining `WinFrontierM` bundle is the mechanical `∀ N ∃ N' ≥ N` largeness
(the `Δπ` supply, the `Qdiag`/`S2mW` lower bounds, and the assembled ratio-slack)
— a mirror of `WinFrontier` with the *M-based* S₁ slack; its `∀ᶠ N` discharge is
the residual flagged in `flags.md`.
-/

namespace Salt.Twelve

open Salt.Maynard

/-- The abstract Archimedean cutoff.  `~10¹⁸` covers both collision-loss budgets
(S₁ `⟹ D ≥ 10¹³`, S₂ `⟹ D ≥ 7·10¹⁶`, see the design's "Endgame constants");
it is an ∃-witness — `primorial Dfin` is never evaluated, only `300 ≤ Dfin`,
`1200 ≤ Dfin` (numeric literal facts) are used. -/
def Dfin : ℕ := 10 ^ 18

/-! ## Modulus facts at `primorial Dfin` -/

private lemma prod_primes_sqf' {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hap (hsp p hp)).mpr (by rintro rfl; exact ha hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, hap.squarefree, ih hsp⟩

private lemma primorial_sqf' (D : ℕ) : Squarefree (primorial D) := by
  unfold primorial
  exact prod_primes_sqf' (fun p hp => (Finset.mem_filter.mp hp).2)

private lemma primorial_pos'' (D : ℕ) : 0 < primorial D := by
  unfold primorial
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)

private lemma hSeq_lt_Dfin (i : Fin 5) : hSeq 5 i < Dfin := by
  unfold Dfin
  fin_cases i <;>
    simp only [hSeq_five_zero, hSeq_five_one, hSeq_five_two, hSeq_five_three,
      hSeq_five_four] <;>
    norm_num

/-! ## The M-based sharp `S1` upper bound (S₁ inner atom KILLED)

Mirror of `sharp_S1_upperW`, but the collision estimate is the *unconditional*
NC-1 corollary `collision_yF_M` (`M`-based) instead of the `S1InnerBound`-fed
`collision_lower_orderW_of` (yside-based).  Hence no `S1InnerBound` hypothesis. -/
theorem sharp_S1_upperM (N R W' ν₀ D : ℕ) (F : Poly) (hQ : Qabs F ≤ 1)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin 5, hSeq 5 i < D)
    (hDk : 12 * 5 ^ 2 ≤ D)
    (hsol : ∀ d ∈ kSieveIndex 5 R W', ∀ e ∈ kSieveIndex 5 R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 5 i)) :
    S1 5 64 N R W' ν₀ (yF R W' F)
      ≤ ((64 - 1) * N / W' : ℝ)
          * ((∑ r ∈ kSieveIndex 5 R W', (yF R W' F r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (5 : ℝ) ^ 2 / D
                  * ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (5 + 1) * (∑ d ∈ kSieveIndex 5 R W', |lam 5 R W' (yF R W' F) d|) ^ 2 := by
  have hy0 : ∀ r, r ∉ kSieveIndex 5 R W' → yF R W' F r = 0 := by
    intro r hr; rw [yF]; simp only [if_neg hr]
  have hL2 := S1_le_main_add_errorW 5 64 N R W' ν₀ D (yF R W' F) hW' (by norm_num) hDlt hlt hsol
  have hcompat_eq := s1_compat_eq 5 R W' (yF R W' F) hy0
  have hcoll := collision_yF_M R W' D F hQ hDlt hDk
  set yside := ∑ r ∈ kSieveIndex 5 R W', (yF R W' F r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
    with hys
  set M := ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ) with hM
  have hcoeff : (0 : ℝ) ≤ ((64 - 1) * N / W' : ℝ) := by
    have h1 : (0 : ℝ) ≤ (64 : ℝ) - 1 := by norm_num
    exact div_nonneg (mul_nonneg h1 (by positivity)) (by positivity)
  have hcompat_le : s1CompatForm 5 R W' (yF R W' F) ≤ yside + 12 * (5 : ℝ) ^ 2 / D * M := by
    rw [hcompat_eq]
    have h1 : - s1CollisionForm 5 R W' (yF R W' F) ≤ |s1CollisionForm 5 R W' (yF R W' F)| :=
      neg_le_abs _
    linarith [hcoll, h1]
  calc S1 5 64 N R W' ν₀ (yF R W' F)
      ≤ ((64 - 1) * N / W' : ℝ) * s1CompatForm 5 R W' (yF R W' F)
        + 2 ^ (5 + 1) * (∑ d ∈ kSieveIndex 5 R W', |lam 5 R W' (yF R W' F) d|) ^ 2 := hL2
    _ ≤ ((64 - 1) * N / W' : ℝ) * (yside + 12 * (5 : ℝ) ^ 2 / D * M)
        + 2 ^ (5 + 1) * (∑ d ∈ kSieveIndex 5 R W', |lam 5 R W' (yF R W' F) d|) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hcompat_le hcoeff) (le_refl _)

/-! ## `win_core_M` — the sieve inequality `S₁ < Σ_m S₂ᵂ⁽ᵐ⁾` (S₁ atom discharged)

Mirror of `win_core'` with the S₁ inner-atom hypothesis `hInner` removed: the
sharp `S1` upper bound is `sharp_S1_upperM` (M-based, unconditional).  The slack
`hslack` is the M-based ratio-slack (with the `M`-collision term explicit). -/
theorem win_core_M (N' R ν₀ W' D : ℕ) (δ : ℝ) (errEH cval : Fin 5 → ℝ)
    (hW' : Squarefree W')
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hlt : ∀ i : Fin 5, hSeq 5 i < D)
    (hDk : 12 * 5 ^ 2 ≤ D)
    (hsol : ∀ d ∈ kSieveIndex 5 R W', ∀ e ∈ kSieveIndex 5 R W', ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % W' = ν₀ % W' ∧ ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 5 i))
    (hφpos : 0 < (Nat.totient W' : ℝ)) (hcval : ∀ m : Fin 5, 0 ≤ cval m) (hδ0 : 0 ≤ δ)
    (hDpi : ∀ m : Fin 5, δ ≤ deltaPi 5 64 N' m)
    (hQlow : ∀ m : Fin 5, cval m ≤ Qdiag_mW 5 R W' m (yF R W' Fstar1))
    (hS2low : ∀ m : Fin 5,
      deltaPi 5 64 N' m / (Nat.totient W' : ℝ) * Qdiag_mW 5 R W' m (yF R W' Fstar1) - errEH m
        ≤ S2mW 5 64 N' R ν₀ W' m (yF R W' Fstar1))
    (hslack :
      ((64 - 1) * N' / W' : ℝ)
          * ((∑ r ∈ kSieveIndex 5 R W',
                  (yF R W' Fstar1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (5 : ℝ) ^ 2 / D
                  * ∑ r ∈ kSieveIndex 5 R W', 1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (5 + 1) * (∑ d ∈ kSieveIndex 5 R W', |lam 5 R W' (yF R W' Fstar1) d|) ^ 2
        < (∑ m : Fin 5, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 5, errEH m) :
    S1 5 64 N' R W' ν₀ (yF R W' Fstar1)
      < ∑ m : Fin 5, S2mW 5 64 N' R ν₀ W' m (yF R W' Fstar1) := by
  have hQabs : Qabs Fstar1 ≤ 1 := le_of_eq Qabs_Fstar1
  have hS1sharp := sharp_S1_upperM N' R W' ν₀ D Fstar1 hQabs hW' hDlt hlt hDk hsol
  have hnum : S1 5 64 N' R W' ν₀ (yF R W' Fstar1)
      < (∑ m : Fin 5, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 5, errEH m :=
    lt_of_le_of_lt hS1sharp hslack
  exact S1_lt_sum_S2mW 64 N' R ν₀ W' (yF R W' Fstar1) δ errEH cval hφpos hcval hδ0 hDpi
    hQlow hS2low hnum

/-! ## The S₂ collision closure at `Fstar1` (NC-2 assembled)

The `Qdiag`-relative S₂ collision bound, CF-slotted.  Mirror of the landed
`collision_yF_le_S2` (`CollisionYF_S2.lean`) with the *conditional*
`S2InnerBoundQ` atom replaced by the NC-2 correction-slotted atom
`S2InnerBoundQC` and `s2_collision_le_QdiagW` replaced by
`s2_collision_le_QdiagW_C`.  The gap between the sharp S₂ diagonal `Qdiag_mW`
and the count-weighted compatible form `s2CompatFormM` is exactly the collision
form (`Qdiag_mW − s2CompatFormM = s2CollisionForm`), bounded by `4·Cs·CF·k²/D`
times the diagonal. -/
theorem s2_collision_yF_C (R W' D : ℕ) (m : Fin 5) (F : Poly) (CF : ℝ) (hCF : 0 ≤ CF)
    (hDlt : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hDk : 48 * 5 ^ 2 ≤ D)
    (hInner : S2InnerBoundQC 5 R W' m (yF R W' F) CF) :
    |Qdiag_mW 5 R W' m (yF R W' F) - s2CompatFormM 5 R W' m (yF R W' F)|
      ≤ (4 * Cs * CF * (5 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 5 R W' m (yF R W' F) := by
  have hfull : Qdiag_mW 5 R W' m (yF R W' F) = s2FullFormM 5 R W' m (yF R W' F) :=
    Qdiag_mW_eq_s2FullFormM 5 R W' m (yF R W' F)
  have hgv : s2FullFormM 5 R W' m (yF R W' F) = Qdiag_gv 5 R W' m (yF R W' F) :=
    s2FullFormM_eq_Qdiag 5 R W' m (yF R W' F)
  have hcompat : s2CompatFormM 5 R W' m (yF R W' F)
      = s2FullFormM 5 R W' m (yF R W' F) - s2CollisionForm 5 R W' m (yF R W' F) :=
    s2_compat_eq_M 5 R W' m (yF R W' F)
  have hcoll := s2_collision_le_QdiagW_C 5 R W' D m (yF R W' F) CF hCF hInner hDlt
    (by norm_num) hDk
  have hdiff : Qdiag_mW 5 R W' m (yF R W' F) - s2CompatFormM 5 R W' m (yF R W' F)
      = s2CollisionForm 5 R W' m (yF R W' F) := by rw [hcompat, hfull]; ring
  have hQeq : Qdiag_mW 5 R W' m (yF R W' F) = Qdiag_gv 5 R W' m (yF R W' F) := hfull.trans hgv
  rw [hdiff, hQeq]
  have hc : (4 * Cs * CF * (5 : ℝ) ^ 2 / (D : ℝ))
      = (4 * Cs * CF * ((5 : ℕ) : ℝ) ^ 2 / (D : ℝ)) := by norm_num
  rw [hc]
  exact hcoll

/-- **NC-2 assembled, GIVEN the `qdiag_bridge` lower-bound comparison `hQd`.**  The
S₂ collision at `Fstar1` is closed for all large `R`: `s2_inner_yF` (NC-2) turns
`hQd` into the `S2InnerBoundQC` atom, and `s2_collision_yF_C` converts it to the
`Qdiag`-relative bound.  The residual hypothesis `hQd` — the eventual comparison
`(PAS+ε)²(2·PAS)⁴ ≤ CF·Qdiag_gv` — is the flagged NC-3 slack input (see the NC-3
PB-floor: the `Qdiag ≥ X⁶·J/2` comparison is carried explicitly). -/
theorem s2_collision_Fstar1_of_hQd (m : Fin 5)
    (hQd : ∃ CF : ℝ, 0 ≤ CF ∧ ∀ W' D : ℕ,
      Squarefree W' → 0 < W' → PhiUpperAtom W' →
      300 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        (Salt.Maynard.phiAtomSum R W' + lemma53Const * 5 * Real.log R / D) ^ 2
            * (2 * Salt.Maynard.phiAtomSum R W') ^ 4
          ≤ CF * Qdiag_gv 5 R W' m (yF R W' Fstar1)) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' → PhiUpperAtom W' →
      1200 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' Fstar1) - s2CompatFormM 5 R W' m (yF R W' Fstar1)|
          ≤ (4 * Cs * CF * (5 : ℝ) ^ 2 / (D : ℝ)) * Qdiag_mW 5 R W' m (yF R W' Fstar1) := by
  obtain ⟨CF, hCF, hatom⟩ := s2_inner_yF Fstar1 m (le_of_eq Qabs_Fstar1) hQd
  refine ⟨CF, hCF, ?_⟩
  intro W' D hW' hpos hUpper hD hDlt hκ
  obtain ⟨R₀, hR₀⟩ := hatom W' D hW' hpos hUpper (by omega) hDlt hκ
  refine ⟨R₀, ?_⟩
  intro R hR hlogR
  exact s2_collision_yF_C R W' D m Fstar1 CF hCF hDlt (by omega) (hR₀ R hR hlogR)

/-! ## The abstract frontier `WinFrontierM`

Mirror of `WinFrontier` at the abstract modulus `primorial Dfin`, with the
M-based S₁ slack (conjunct 7).  Conjuncts 1–6 are IDENTICAL to `WinFrontier`
(they never mention the S₁ collision).  This is the mechanical `∀ᶠ N` largeness
bundle; its discharge (`win_ratio_core` + the vanishing `mv_I_split`/
`qdiag_bridge`/`herr` budget) is FABLE-QUEUE'd — see the NC-3 / W5-7 flag. -/
def WinFrontierM : Prop :=
  WindowPNT → EHall → ∀ N : ℕ,
    ∃ (N' R ν₀ : ℕ) (δ : ℝ) (errEH cval : Fin 5 → ℝ), N ≤ N' ∧
    (∀ d ∈ kSieveIndex 5 R (primorial Dfin), ∀ e ∈ kSieveIndex 5 R (primorial Dfin),
      ¬ IsCollisionPair d e →
      ∃ c : ℕ, c % (primorial Dfin) = ν₀ % (primorial Dfin) ∧
        ∀ i, Nat.lcm (d i) (e i) ∣ (c + hSeq 5 i)) ∧
    0 < (Nat.totient (primorial Dfin) : ℝ) ∧ (∀ m : Fin 5, 0 ≤ cval m) ∧ 0 ≤ δ ∧
    (∀ m : Fin 5, δ ≤ deltaPi 5 64 N' m) ∧
    (∀ m : Fin 5,
      cval m ≤ Qdiag_mW 5 R (primorial Dfin) m (yF R (primorial Dfin) Fstar1)) ∧
    (∀ m : Fin 5,
      deltaPi 5 64 N' m / (Nat.totient (primorial Dfin) : ℝ)
          * Qdiag_mW 5 R (primorial Dfin) m (yF R (primorial Dfin) Fstar1) - errEH m
        ≤ S2mW 5 64 N' R ν₀ (primorial Dfin) m (yF R (primorial Dfin) Fstar1)) ∧
    (((64 - 1) * N' / (primorial Dfin) : ℝ)
          * ((∑ r ∈ kSieveIndex 5 R (primorial Dfin),
                  (yF R (primorial Dfin) Fstar1 r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
              + 12 * (5 : ℝ) ^ 2 / Dfin
                  * ∑ r ∈ kSieveIndex 5 R (primorial Dfin),
                      1 / ∏ i, (Nat.totient (r i) : ℝ))
        + 2 ^ (5 + 1)
            * (∑ d ∈ kSieveIndex 5 R (primorial Dfin),
                |lam 5 R (primorial Dfin) (yF R (primorial Dfin) Fstar1) d|) ^ 2
        < (∑ m : Fin 5,
              δ / (Nat.totient (primorial Dfin) : ℝ) * cval m) - ∑ m : Fin 5, errEH m)

/-! ## The capstone `gaps_le_twelve`

The FROZEN top-of-doc target, matched verbatim in its conclusion; the S₁ inner
atom is discharged (via `collision_yF_M` inside `win_core_M`).  It remains
CONDITIONAL on the mechanical `WinFrontierM` largeness bundle (PB-floor #2 of the
NC-3 card: the `∀ᶠ N` slack threading is carried explicitly and flagged). -/
theorem gaps_le_twelve (hPNT : WindowPNT) (hEH : EHall) (hFrontier : WinFrontierM) :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-12 : ℤ) 12 := by
  refine bounded_gaps_reduces_twelve (primorial Dfin) (fun N => ?_)
  obtain ⟨N', R, ν₀, δ, errEH, cval, hNN', hsol, hφpos, hcvnn, hδ0, hDpi, hQlow,
    hS2low, hslack⟩ := hFrontier hPNT hEH N
  refine ⟨N', R, ν₀, yF R (primorial Dfin) Fstar1, hNN', ?_⟩
  exact win_core_M N' R ν₀ (primorial Dfin) Dfin δ errEH cval
    (primorial_sqf' Dfin) (primorial_hDlt Dfin) hSeq_lt_Dfin
    (by unfold Dfin; norm_num) hsol hφpos hcvnn hδ0 hDpi hQlow hS2low hslack

end Salt.Twelve
