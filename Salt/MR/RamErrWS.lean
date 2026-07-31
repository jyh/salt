/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4CapWire
import Salt.MR.M4ErrRewire
import Salt.MR.M4RowsChiEnd
import Salt.MR.M4RowsChiZero

/-!
# ⟦THE D5 TRANSPLANT ONE LEVEL DOWN — the `Σ_χ` Ramaré error at the STRICT pair law⟧
(`RamErrWS`)

`docs/blueprints/flags.md` ⟦HCAP-WAVE lands⟧ (2026-07-30), section ⟦THE E-BINDER WALL⟧.

## The wall

`M4CapWire.DoorCapBase.E_binder` asks for a bound on the `χ`-summed Lemma-12 error moment

`∑_{χ mod q} ∫_{−T_ann}^{T_ann} ‖ramErr H₈₃ (2N_d) X_d P Q (χ̄a) (χ̄b) (χ̄cf)‖² ≤ E`

at the door datum `a = winCutH N_d (doorCoeffU M)`.  The shape-correct landed supplier
`HybridMoments.ramErr_meanSq_all_chi` asks the **GLOBAL** block factorization

`∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬p∣m → a (p·m) = b m · cf p`,

and `M4Assembly.doorRows_global_hcoef_kills_block` proves that contract KILLS a window-cut
datum.  So `M4CapWire` §4c is stated CONDITIONALLY and `E_binder` stays carried.

## The cut that dissolves it — and WHERE it goes

The repair is the D5 device (`M4RowsChiEnd` §1 at the row; `SeamRowWindowed` §3′ at the
identity): re-cut at `SeamRowWindowed.SeamCoefWS`, the STRICT relativized pair law, which
asks the factorization only on `X_d < p·m ≤ 2X_d`.

⟦THE BYTE-PRECISE SPEND SITE⟧  `ramErr_meanSq_all_chi` spends its `hcoef` at exactly one
place: `RamareErr.ramErr_moment_split` (`HybridMoments`:629), which spends it at
`RamareWindows.ramErr_window_decomp`:392, which spends it at
`RamareWindows.spoly_ramare_split`:153.  **That split GENUINELY READS OUT-OF-WINDOW
PRODUCTS** — its clean term `clean_term` runs over the FULL eq-(16) cofactor range
`{m : p·m ∈ [1,N]}`, so for `p·m ≤ X_d` (below the window, where the door datum is `0` but
`b m · cf p` need not be) the identity substitutes `a (p·m) = b m · cf p` at a pair the
strict law never asserts.  The three-row split is therefore NOT recoverable at `SeamCoefWS`,
and no `hasupp` rescues it: the mismatch is on the CLEAN side, not the datum side.

⟦THE HONEST TRANSPLANT⟧  This is the same discovery `RamareMR` made at `q = 1`, and its
answer is the four-row split whose clean term is restricted to MR's own honest cofactor range
`ramHonMR N X p = {m : X ≤ p·m ≤ 2X}` — the window lives IN THE INDEX SET.  At the STRICT law
that is `SeamRowWindowed.ramErr_moment_split_mr_windowed_end`, with the released endpoint
cofactors fused into the `p²` row (`RamareP2End.ramP2corrEndMR`).  So the `Σ_χ` twin here is
built on the FOUR-row split, and the deviation is stated in the open:

| | landed `ramErr_meanSq_all_chi` | this file's `_ws` |
|---|---|---|
| pair law | GLOBAL `hcoef` (kills the door datum) | `SeamCoefWS` (the door datum's own) |
| datum | free | `hasupp` — dyadic support, free at `winCutH` |
| split | 3 rows, prefactor `3` | 4 rows, prefactor `4` (`moment_split4`) |
| seam | one row, `φ(q)·2T·windowMass²` | two rows, `φ(q)`-fold, collapsing at `520` |
| `p²` | `ramP2coeff` | the FUSED `ramP2coeffEndMR` (+ `M4ErrRewire.endMass`) |
| tail | verbatim | verbatim |

⟦WHAT IS *NOT* PAID⟧  The `1/q` saving of wave P-2's hybrid mean value is KEPT on both
mean-value rows (`hybrid_char_spoly_mvt` at grade `2φ(q)T + 7φ(q)N/q`) — R-P3's law, not
droppable.  Only the two seam rows, which are `χ`-uniform functions of `(χ̄b, χ̄cf)`, are
priced `φ(q)`-fold — exactly as the landed file prices its single window row `φ(q)`-fold.

⟦THE `φ(q)` RIDES, AND IT IS NOT NEW⟧  `DoorCapBase.E_row` (`E ≤ 3·(720·g/H₈₃ + EP2)`) is
`φ(q)`-blind, so meeting it against a `φ(q)`-fold seam price is the door supplier's
arithmetic.  This is NOT a regression introduced here: the landed conditional wire
`m4_capE_at_door_of_hcoef` carries the identical `φ(q)` on its window row.  The grade fit
itself (`M4ErrRewire.err_grade_fit`, `4·520 = 2080 ≤ 2160 = 3·720`) is untouched.

## Contents

* §1 — the twist lifts: the FUSED `p²` coefficient commutes with `χ̄`
  (`ramP2coeffEndMR_chiBar`), and the dyadic support pin survives it;
* §2 — **the deliverable**: `ramErr_meanSq_all_chi_ws`, the `Σ_χ` four-row error moment at
  `SeamCoefWS`, and `ramErr_meanSq_all_chi_ws_priced`, its fully explicit form (the seam rows
  collapsed at `RamareMR.seam_rows_grade`, the `p²` mass at `M4P2MR.ramP2massEndMR_direct`);
* §3 — `DoorCapErrWS` (the small per-base error bundle, whose `coefWS` field is
  `M4RowsChiZero.DoorRowZeroBase.coefWS` VERBATIM) and **`m4_capE_at_door`**: `E_binder`
  discharged from it;
* §4 — the composite `m4_socket_discharged_capwired_ws`: `M4CapWire`'s terminal with
  `E_binder` replaced by `DoorCapErrWS`.

⟦PURELY ADDITIVE⟧  No landed declaration is touched.  `DoorCapBase`,
`m4_socket_discharged_capwired`, `SeamCoefWS`, `DoorRowZeroBase` and the fused terminal are
met, never adjusted.

⟦THE FOUR LOG SCALES⟧ stay apart: nothing here evaluates `H₈₃ X θ₂₉₃`, and `log(q·T_ann)`,
`log(5T_ann+1)`, `L` and `log X` never meet.  `H ≤ X` (the `hHX` field) is a comparison of
the `H₈₃` window length with the BASE, which is `RamareMR.seam_rows_grade`'s own standing
hypothesis at `q = 1`, transplanted unchanged.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE TWIST LIFTS

`HybridMoments` §4's two lemmas at the FUSED family.  Both are the landed one-liners: the
Ramaré weight and `1/(ω(m)+1)` are character-blind, and `χ̄(p)·χ̄(m) = χ̄(pm)` is
unconditional (`conj_chi_natCast_mul`). -/

/-- **THE FUSED `p²` COEFFICIENT COMMUTES WITH THE TWIST**
(`ramP2coeffEndMR_chiBar`).  `HybridMoments.ramP2coeff_chiBar` at
`RamareP2End.ramP2coeffEndMR`: the enlarged inner filter `p ∣ m ∨ p·m = X` is a condition on
the INDEX, which the twist does not see, so the landed proof transplants verbatim. -/
theorem ramP2coeffEndMR_chiBar (q : ℕ) (χ : DirichletCharacter ℂ q) (N X P Q : ℕ)
    (a b c : ℕ → ℂ) (n : ℕ) :
    ramP2coeffEndMR N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ c) n
      = chiBarCoeff q χ (ramP2coeffEndMR N X P Q a b c) n := by
  rw [chiBarCoeff_apply, ramP2coeffEndMR, ramP2coeffEndMR, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  rw [Finset.mem_filter] at hσ
  rw [← hσ.2, chiBarCoeff_apply, chiBarCoeff_apply, chiBarCoeff_apply,
    conj_chi_natCast_mul q χ σ.1 σ.2]
  ring

/-- The FUSED `p²`-correction row of the twisted error, as a `σ = 1` polynomial with
`χ̄`-twisted coefficients — `HybridMoments.ramP2corr_chiBar_eq_spoly`'s twin.  Frequencies run
in `[1,N]`, so the hybrid mean value applies at the un-inflated cap. -/
lemma ramP2corrEndMR_chiBar_eq_spoly (q : ℕ) (χ : DirichletCharacter ℂ q) (N X P Q : ℕ)
    (hX : 1 ≤ X) (hN : 2 * X ≤ N) (a b c : ℕ → ℂ) (t : ℝ) :
    ramP2corrEndMR N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
        (chiBarCoeff q χ c) t
      = spoly N (chiBarCoeff q χ (ramP2coeffEndMR N X P Q a b c)) t := by
  rw [ramP2corrEndMR_eq_spoly N X P Q hX hN _ _ _ t]
  congr 1
  funext n
  exact ramP2coeffEndMR_chiBar q χ N X P Q a b c n

/-- The dyadic window pin survives the twist, at the REAL-cast shape the MR split asks
(`M4RowsChi.chiBarCoeff_dyadic_supp` is the `ℕ`-cast one).  The twisted support is a
SUBSET. -/
lemma chiBarCoeff_dyadic_suppR {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ℕ → ℂ} {X : ℕ}
    (h : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ)) :
    ∀ n : ℕ, chiBarCoeff q χ a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ) := by
  intro n hn
  refine h n (fun h0 => hn ?_)
  simp [chiBarCoeff_apply, h0]

/-! ## §2 — ⟦THE DELIVERABLE⟧ THE `Σ_χ` ERROR MOMENT AT THE STRICT PAIR LAW

`HybridMoments.ramErr_meanSq_all_chi` re-cut through
`SeamRowWindowed.ramErr_moment_split_mr_windowed_end`.  Row by row:

* the two SEAM rows depend only on `(χ̄b, χ̄cf)` and are priced by the `χ`-uniform
  `RamareMR.ramSeamLoPoly_moment` / `ramSeamUpPoly_moment` — `φ(q)`-fold, exactly as the
  landed file prices its window row;
* the FUSED `p²` row and the coprime tail are `spoly`s of twisted coefficients (§1), so wave
  P-2's `hybrid_char_spoly_mvt` prices them at `2φ(q)T + 7φ(q)N/q` — the `1/q` saving kept. -/

/-- **⟦THE STRICT-LAW `Σ_χ` ERROR MOMENT⟧** (`ramErr_meanSq_all_chi_ws`).
`HybridMoments.ramErr_meanSq_all_chi` with the GLOBAL block factorization replaced by the
STRICT relativized pair law `SeamRowWindowed.SeamCoefWS` plus MR's dyadic support pin — the
two conditions a window-cut door datum actually satisfies.

⟦IRON RULE 1 — THIS PAGE ASKS LESS ON THE PAIR AXIS⟧  the global law implies `SeamCoefWS`
(`SeamRowWindowed.seamCoefW_of_global` then `seamCoefWS_of_seamCoefW`), and the converse
fails exactly where `M4Assembly.doorRows_global_hcoef_kills_block` bites.  It asks MORE on
the datum axis (`hasupp`, `hb`, `hc`, `2X ≤ N`, `2 ≤ H`) — all free at the door.

⟦THE RIGHT-HAND SIDE MOVES, AND IT IS STATED⟧  four rows at prefactor `4`, the single window
row replaced by MR's two seam rows, and `ramP2coeff` by the FUSED `ramP2coeffEndMR`.  See the
header's table. -/
theorem ramErr_meanSq_all_chi_ws (q : ℕ) [NeZero q] (H : ℝ) (hH : 2 ≤ H) (N X P Q : ℕ)
    (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoefWS : SeamCoefWS X P Q a b c)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2)
      ≤ 4 * ((q.totient : ℝ)
              * ((2 * T + 20 * (N : ℝ))
                  * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2))
          + (q.totient : ℝ)
              * ((2 * T + 80 * (X : ℝ))
                  * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2))
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (∑ n ∈ Finset.Icc 1 N,
                  ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                  ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
  classical
  set S1 : DirichletCharacter ℂ q → ℝ := fun χ => ∫ t in (-T)..T,
    ‖ramSeamLoPoly H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) t‖ ^ 2 with hS1def
  set S2 : DirichletCharacter ℂ q → ℝ := fun χ => ∫ t in (-T)..T,
    ‖ramSeamUpPoly H N X P Q (chiBarCoeff q χ b) (chiBarCoeff q χ c) t‖ ^ 2 with hS2def
  set Cr : DirichletCharacter ℂ q → ℝ := fun χ => ∫ t in (-T)..T,
    ‖ramP2corrEndMR N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
      (chiBarCoeff q χ c) t‖ ^ 2 with hCdef
  set D : DirichletCharacter ℂ q → ℝ := fun χ => ∫ t in (-T)..T,
    ‖ramCopTail N P Q (chiBarCoeff q χ a) t‖ ^ 2 with hDdef
  -- the per-χ FOUR-row split at the STRICT law (the identity chain is character-blind)
  have hrow : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-T)..T, ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2) ≤ 4 * (S1 χ + S2 χ + Cr χ + D χ) := fun χ =>
    ramErr_moment_split_mr_windowed_end H hH N X P Q hX hN hP _ _ _
      (chiBarCoeff_seamCoefWS χ hcoefWS) (chiBarCoeff_dyadic_suppR χ hasupp) T hT
  -- the lower seam row: the χ-uniform moment, φ(q)-fold
  have hS1bound : (∑ χ : DirichletCharacter ℂ q, S1 χ)
      ≤ (q.totient : ℝ)
          * ((2 * T + 20 * (N : ℝ)) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2)) := by
    rw [← sum_const_dirichletChar q
      ((2 * T + 20 * (N : ℝ)) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2))]
    refine Finset.sum_le_sum (fun χ _ => ?_)
    exact ramSeamLoPoly_moment H hH N X P Q hX hN hP _ _ (norm_chiBarCoeff_le_one χ hb)
      (norm_chiBarCoeff_le_one χ hc) T hT
  -- the upper seam row: the χ-uniform moment, φ(q)-fold
  have hS2bound : (∑ χ : DirichletCharacter ℂ q, S2 χ)
      ≤ (q.totient : ℝ)
          * ((2 * T + 80 * (X : ℝ))
              * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2)) := by
    rw [← sum_const_dirichletChar q
      ((2 * T + 80 * (X : ℝ)) * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2))]
    refine Finset.sum_le_sum (fun χ _ => ?_)
    exact ramSeamUpPoly_moment H hH N X P Q hX hP _ _ (norm_chiBarCoeff_le_one χ hb)
      (norm_chiBarCoeff_le_one χ hc) T hT
  -- the FUSED p²-correction row: the hybrid mean value at the un-inflated cap
  have hCbound : (∑ χ : DirichletCharacter ℂ q, Cr χ)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
          * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
    have hpiece : ∀ χ : DirichletCharacter ℂ q,
        Cr χ = ∫ t in (-T)..T,
          ‖spoly N (chiBarCoeff q χ (ramP2coeffEndMR N X P Q a b c)) t‖ ^ 2 := by
      intro χ
      rw [hCdef]
      exact intervalIntegral.integral_congr
        (fun t _ => by rw [ramP2corrEndMR_chiBar_eq_spoly q χ N X P Q hX hN])
    rw [Finset.sum_congr rfl (fun χ _ => hpiece χ)]
    exact hybrid_char_spoly_mvt q N (ramP2coeffEndMR N X P Q a b c) hT
  -- the sieve-remainder row: the hybrid mean value, mass kept symbolic
  have hDbound : (∑ χ : DirichletCharacter ℂ q, D χ)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
    have hpiece : ∀ χ : DirichletCharacter ℂ q,
        D χ = ∫ t in (-T)..T,
          ‖spoly N (chiBarCoeff q χ
            (fun n => if blockOmega P Q n = 0 then a n else 0)) t‖ ^ 2 := by
      intro χ
      rw [hDdef]
      exact intervalIntegral.integral_congr (fun t _ => by rw [ramCopTail_chiBar_eq_spoly])
    rw [Finset.sum_congr rfl (fun χ _ => hpiece χ)]
    refine (hybrid_char_spoly_mvt q N
      (fun n => if blockOmega P Q n = 0 then a n else 0) hT).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) ?_
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : blockOmega P Q n = 0 <;> simp [h]
    · have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
      have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (N : ℝ) / q := by positivity
      linarith
  calc (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2)
      ≤ ∑ χ : DirichletCharacter ℂ q, 4 * (S1 χ + S2 χ + Cr χ + D χ) :=
        Finset.sum_le_sum (fun χ _ => hrow χ)
    _ = 4 * ((∑ χ : DirichletCharacter ℂ q, S1 χ) + (∑ χ : DirichletCharacter ℂ q, S2 χ)
          + (∑ χ : DirichletCharacter ℂ q, Cr χ) + ∑ χ : DirichletCharacter ℂ q, D χ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
    _ ≤ 4 * ((q.totient : ℝ)
              * ((2 * T + 20 * (N : ℝ))
                  * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2))
          + (q.totient : ℝ)
              * ((2 * T + 80 * (X : ℝ))
                  * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2))
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (∑ n ∈ Finset.Icc 1 N,
                  ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
                  ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) := by
        linarith

/-- **⟦THE STRICT-LAW `Σ_χ` ERROR MOMENT, PRICED⟧** (`ramErr_meanSq_all_chi_ws_priced`).
`ramErr_meanSq_all_chi_ws` with the two seam rows collapsed at `RamareMR.seam_rows_grade`
(MR's own `520·(T/X+1)/H` grade, both windows included) and the FUSED `p²` mass priced by
`M4P2MR.ramP2massEndMR_direct` (`16·log₂(2X)/(X·P)` plus `M4ErrRewire.endMass X`, the price
of releasing the window's lower endpoint).  The coprime-tail mass stays symbolic — ⟦R3a⟧'s
"priced, not pinned" pattern, verbatim from `M4ErrRewire.E_priced_mr_end`.

This is `E_priced_mr_end`'s `χ`-summed twin: the same right-hand side with `φ(q)` on the seam
row and the hybrid mean value's `2φ(q)T + 7φ(q)N/q` on the other two. -/
theorem ramErr_meanSq_all_chi_ws_priced (q : ℕ) [NeZero q] (H : ℝ) (hH : 2 ≤ H)
    (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hN2 : (N : ℝ) ≤ 2 * (X : ℝ))
    (hHX : H ≤ (X : ℝ)) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (hcoefWS : SeamCoefWS X P Q a b c)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (Mtail : ℝ)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (T : ℝ) (hT : 0 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2)
      ≤ 4 * ((q.totient : ℝ) * (520 * (T / (X : ℝ) + 1) / H)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (16 * Real.logb 2 (2 * (X : ℝ)) / ((X : ℝ) * (P : ℝ)) + endMass X)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q) * Mtail) := by
  refine (ramErr_meanSq_all_chi_ws q H hH N X P Q hX hN hP a b c hcoefWS hasupp hb hc
    T hT).trans ?_
  simp only [endMass]
  have hphi : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hfac : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q := by
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (N : ℝ) / q := by positivity
    linarith
  have hgrade := seam_rows_grade H hH N X hX hN2 hHX T hT
  have hmass := ramP2massEndMR_direct N X P Q hX hN hP a b c ha hb hc
  have hseam : (q.totient : ℝ)
        * ((2 * T + 20 * (N : ℝ)) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2))
      + (q.totient : ℝ)
        * ((2 * T + 80 * (X : ℝ))
            * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2))
      ≤ (q.totient : ℝ) * (520 * (T / (X : ℝ) + 1) / H) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hgrade hphi
  have hp2 : (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
        * (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
        * (16 * Real.logb 2 (2 * (X : ℝ)) / ((X : ℝ) * (P : ℝ))
          + 4 * (Real.logb 2 (2 * (X : ℝ))) ^ 2 / (X : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hmass hfac
  have htail : (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
        * (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
            ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q) * Mtail :=
    mul_le_mul_of_nonneg_left hMtail hfac
  linarith

/-- **⟦THE STRICT-LAW `Σ_χ` ERROR MOMENT, PRICED — R1⟧**
(`ramErr_meanSq_all_chi_ws_priced'`).  `ramErr_meanSq_all_chi_ws_priced` with the fused `p²`
row at the DIRECT `L²` grade (`M4P2MR.ramP2massEndMR_L2_direct`):

  `16·log₂(2X)/(X·P) + endMass X   ↦   24/(X·P) + endMass X` ,

the `X`-FREE numerator, at the floor `4 ≤ P` (free at the door: `𝒫₁ ≥ 64`).  This is the
`E_ge` row-2 retirement: the `E`-slack no longer has to cover a `log₂(2X)` that grows with
the base.  `endMass X = 4·(log₂(2X))²/X²` is untouched — it DECAYS, and it is the summand
`M4RowMR.logbsq_two_mul_P_le` absorbs on the row side. -/
theorem ramErr_meanSq_all_chi_ws_priced' (q : ℕ) [NeZero q] (H : ℝ) (hH : 2 ≤ H)
    (N X P Q : ℕ) (hX : 1 ≤ X) (hN : 2 * X ≤ N) (hN2 : (N : ℝ) ≤ 2 * (X : ℝ))
    (hHX : H ≤ (X : ℝ)) (hP : 4 ≤ P) (a b c : ℕ → ℂ)
    (hcoefWS : SeamCoefWS X P Q a b c)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → (X : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (X : ℝ))
    (Mtail : ℝ)
    (hMtail : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail)
    (T : ℝ) (hT : 0 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N X P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ c) t‖ ^ 2)
      ≤ 4 * ((q.totient : ℝ) * (520 * (T / (X : ℝ) + 1) / H)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
              * (24 / ((X : ℝ) * (P : ℝ)) + endMass X)
          + (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q) * Mtail) := by
  refine (ramErr_meanSq_all_chi_ws q H hH N X P Q hX hN (by omega) a b c hcoefWS hasupp hb hc
    T hT).trans ?_
  simp only [endMass]
  have hphi : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hfac : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q := by
    have h1 : (0 : ℝ) ≤ 2 * (q.totient : ℝ) * T := by positivity
    have h2 : (0 : ℝ) ≤ 7 * (q.totient : ℝ) * (N : ℝ) / q := by positivity
    linarith
  have hgrade := seam_rows_grade H hH N X hX hN2 hHX T hT
  have hmass := ramP2massEndMR_L2_direct N X P Q hX hN hP a b c ha hb hc
  have hseam : (q.totient : ℝ)
        * ((2 * T + 20 * (N : ℝ)) * ((2 * Real.exp 1 * (X : ℝ) / H + 1) / (X : ℝ) ^ 2))
      + (q.totient : ℝ)
        * ((2 * T + 80 * (X : ℝ))
            * ((4 * Real.exp 1 * (X : ℝ) / H + 1) / (2 * (X : ℝ)) ^ 2))
      ≤ (q.totient : ℝ) * (520 * (T / (X : ℝ) + 1) / H) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hgrade hphi
  have hp2 : (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
        * (∑ n ∈ Finset.Icc 1 N, ‖ramP2coeffEndMR N X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
        * (24 / ((X : ℝ) * (P : ℝ))
          + 4 * (Real.logb 2 (2 * (X : ℝ))) ^ 2 / (X : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hmass hfac
  have htail : (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q)
        * (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
            ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ (2 * (q.totient : ℝ) * T + 7 * (q.totient : ℝ) * (N : ℝ) / q) * Mtail :=
    mul_le_mul_of_nonneg_left hMtail hfac
  linarith

/-! ## §3 — ⟦THE DOOR DISCHARGE⟧ `DoorCapErrWS` and `m4_capE_at_door`

`M4CapWire.DoorCapBase.E_binder` at the door datum.  The analytic content — the block
factorization — is asked in EXACTLY the shape `M4RowsChiZero.DoorRowZeroBase.coefWS` already
supplies (`SeamCoefWS X_d P Q (winCutH X_d (doorCoeffU M)) (bU i) cU`); everything else in
the bundle is arithmetic on the door's own numerals, or the coprime-tail mass, which rides
symbolically exactly as in `M4ErrRewire.E_priced_mr_end`.

⟦THE ONE PIN⟧ `X_d = N_d`.  The door datum `winCutH N_d (doorCoeffU M)` is supported in
`(N_d, 2N_d]`, so MR's dyadic parameter of the SAME `ramErr` object must be `N_d` for the
support pin `hasupp` to hold at all.  This is not a new demand: the door's own row bundle
`DoorRowZeroBase M (A+s) j cU bU` already reads its `X_d` slot AS `A + s = N_d`. -/

/-- **⟦THE PER-BASE ERROR BUNDLE⟧** (`DoorCapErrWS`).  Everything `m4_capE_at_door` needs, as
ONE structure — the shape the S11 spine instantiates alongside `DoorCapBase`.

⟦THE ANALYTIC FIELD IS SHARED, NOT NEW⟧ `coefWS` is `DoorRowZeroBase.coefWS` at the door's
level-`i` block: any model of the row bundle supplies it at `P := calP (Adoor M) (3072M) i`,
`Q := calQK (Adoor M) (3072M) M i`, `b := bU i`, `cf := cU`.  The other nine fields are
arithmetic on `(N_d, P, H₈₃)` plus the coprime-tail mass and the `E` slack. -/
structure DoorCapErrWS (M Nd q Xd P Q : ℕ) (b cf : ℕ → ℂ) (Tann E Mtail : ℝ) : Prop where
  /-- ⟦THE PIN⟧ the ram-block dyadic parameter IS the socket base (the datum's own window). -/
  Xd_eq : Xd = Nd
  /-- `1 ≤ N_d`. -/
  Nd_one : 1 ≤ Nd
  /-- `2 ≤ H₈₃ X θ₂₉₃` — `DoorCapBase.H83_two`, verbatim. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `H₈₃ X θ₂₉₃ ≤ X` — `RamareMR.seam_rows_grade`'s standing window-vs-base hypothesis. -/
  H83_le : H83 ((Nd : ℕ) : ℝ) theta293 ≤ ((Nd : ℕ) : ℝ)
  /-- `1 ≤ P`. -/
  P_one : 1 ≤ P
  /-- `0 ≤ T_ann`. -/
  Tann_nonneg : 0 ≤ Tann
  /-- `‖b m‖ ≤ 1` — the co-factor sequence is `1`-bounded. -/
  b_one : ∀ m, ‖b m‖ ≤ 1
  /-- `‖cf p‖ ≤ 1` — `DoorCapBase.cf_one`, verbatim. -/
  cf_one : ∀ p, ‖cf p‖ ≤ 1
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law at the door datum —
  `M4RowsChiZero.DoorRowZeroBase.coefWS`'s shape. -/
  coefWS : SeamCoefWS Xd P Q (winCutH Nd (doorCoeffU M)) b cf
  /-- ⟦R3a⟧ the coprime-tail (sieve-remainder) mass, priced not pinned. -/
  tail : ∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
      ‖winCutH Nd (doorCoeffU M) n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail
  /-- `E` dominates the priced four-row bound (`ramErr_meanSq_all_chi_ws_priced` at the
  door's numerals). -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ))
            + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * Mtail) ≤ E

/-- **⟦THE `E_binder` WIRE — UNCONDITIONAL⟧** (`m4_capE_at_door`).
`M4CapWire.DoorCapBase.E_binder` at the door datum, from `DoorCapErrWS` alone.

This is `m4_capE_at_door_of_hcoef` with its fatal hypothesis GONE: where that theorem asks
the GLOBAL block factorization — the contract `M4Assembly.doorRows_global_hcoef_kills_block`
refutes at a window-cut datum — this one asks only the STRICT relativized law, which the door
datum satisfies (`M4RowsChiZero.DoorRowZeroBase.coefWS` is a landed carried field of the
existing bundle). -/
theorem m4_capE_at_door {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ} {Tann E Mtail : ℝ}
    (h : DoorCapErrWS M Nd q Xd P Q b cf Tann E Mtail) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ E := by
  obtain ⟨hXd, hNd, hH2, hHle, hP1, hT, hb1, hcf1, hcoef, htail, hE⟩ := h
  subst hXd
  refine le_trans ?_ hE
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hasupp : ∀ n : ℕ, winCutH Xd (doorCoeffU M) n ≠ 0 →
      ((Xd : ℕ) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := winCutH_asupp hn
    constructor
    · exact_mod_cast h1
    · have : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
  exact ramErr_meanSq_all_chi_ws_priced q (H83 ((Xd : ℕ) : ℝ) theta293) hH2 (2 * Xd) Xd P Q
    hNd le_rfl hN2 hHle hP1 (winCutH Xd (doorCoeffU M)) b cf hcoef
    (fun n => norm_doorRowDatumU_le_one M Xd n) hb1 hcf1 hasupp Mtail htail Tann hT

/-- **⟦THE PER-BASE ERROR BUNDLE — R1⟧** (`DoorCapErrWS'`).  `DoorCapErrWS` with `P_one`
strengthened to `4 ≤ P` (free at the door) and the `E_ge` field's `p²` row RETIRED to the
`X`-free constant:

  landed  `E_ge : … (16·log₂(2N_d)/(N_d·P) + endMass N_d) … ≤ E`
  R1      `E_ge : … (24/(N_d·P)          + endMass N_d) … ≤ E`

Everything else is byte-identical.  Since `24/(N_d·P) ≤ 16·log₂(2N_d)/(N_d·P)` at `N_d ≥ 2`,
this asks strictly LESS of `E` — the S13CapGate slack it consumed is returned. -/
structure DoorCapErrWS' (M Nd q Xd P Q : ℕ) (b cf : ℕ → ℂ) (Tann E Mtail : ℝ) : Prop where
  /-- ⟦THE PIN⟧ the ram-block dyadic parameter IS the socket base. -/
  Xd_eq : Xd = Nd
  /-- `1 ≤ N_d`. -/
  Nd_one : 1 ≤ Nd
  /-- `2 ≤ H₈₃ X θ₂₉₃`. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `H₈₃ X θ₂₉₃ ≤ X`. -/
  H83_le : H83 ((Nd : ℕ) : ℝ) theta293 ≤ ((Nd : ℕ) : ℝ)
  /-- ⟦R1's FLOOR⟧ `4 ≤ P` — the `24`-constant's binder, free at the door (`𝒫₁ ≥ 64`). -/
  P_four : 4 ≤ P
  /-- `0 ≤ T_ann`. -/
  Tann_nonneg : 0 ≤ Tann
  /-- `‖b m‖ ≤ 1`. -/
  b_one : ∀ m, ‖b m‖ ≤ 1
  /-- `‖cf p‖ ≤ 1`. -/
  cf_one : ∀ p, ‖cf p‖ ≤ 1
  /-- The STRICT relativized pair law at the door datum. -/
  coefWS : SeamCoefWS Xd P Q (winCutH Nd (doorCoeffU M)) b cf
  /-- The coprime-tail (sieve-remainder) mass, priced not pinned. -/
  tail : ∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
      ‖winCutH Nd (doorCoeffU M) n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail
  /-- `E` dominates the R1-priced four-row bound. -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (24 / (((Nd : ℕ) : ℝ) * (P : ℝ)) + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * Mtail) ≤ E

/-- **⟦THE `E_binder` WIRE — R1⟧** (`m4_capE_at_door'`).  `m4_capE_at_door` from the
R1-priced bundle. -/
theorem m4_capE_at_door' {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ} {Tann E Mtail : ℝ}
    (h : DoorCapErrWS' M Nd q Xd P Q b cf Tann E Mtail) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ E := by
  obtain ⟨hXd, hNd, hH2, hHle, hP4, hT, hb1, hcf1, hcoef, htail, hE⟩ := h
  subst hXd
  refine le_trans ?_ hE
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hasupp : ∀ n : ℕ, winCutH Xd (doorCoeffU M) n ≠ 0 →
      ((Xd : ℕ) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := winCutH_asupp hn
    constructor
    · exact_mod_cast h1
    · have : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
  exact ramErr_meanSq_all_chi_ws_priced' q (H83 ((Xd : ℕ) : ℝ) theta293) hH2 (2 * Xd) Xd P Q
    hNd le_rfl hN2 hHle hP4 (winCutH Xd (doorCoeffU M)) b cf hcoef
    (fun n => norm_doorRowDatumU_le_one M Xd n) hb1 hcf1 hasupp Mtail htail Tann hT

/-! ## §4 — ⟦THE COMPOSITE⟧ `m4_socket_discharged_capwired_ws`

`M4CapWire.m4_socket_discharged_capwired` with the `DoorCapBase` family's LAST analytic
field, `E_binder`, taken off the door supplier's hands.  The `hcapbase` slot becomes:

* `DoorCapErrWS` — the strict pair law and its arithmetic (§3), PLUS
* the bundle MINUS `E_binder`, written as the implication
  `(E_binder-shape) → DoorCapBase …`.

⟦IRON RULE 1⟧ the implication form asks strictly less than `DoorCapBase` itself
(`fun _ => hd` supplies it from any model), so the only genuinely new demand is
`DoorCapErrWS`, whose analytic content is a field the door's row bundle ALREADY carries. -/

set_option maxHeartbeats 1000000 in
-- The statement re-elaborates the cap-wired terminal's full binder list (same cause as
-- `M4CapWire` §5).
/-- **⟦THE CAP-WIRED TERMINAL AT THE STRICT PAIR LAW⟧**
(`m4_socket_discharged_capwired_ws`).  `M4CapWire.m4_socket_discharged_capwired` with
`DoorCapBase`'s `E_binder` DISCHARGED: the door family now supplies the STRICT relativized
pair law (`DoorCapErrWS.coefWS`, the shape `DoorRowZeroBase` already carries) and the bundle
minus that one field, and §3 manufactures `E_binder` from them.

⟦WHAT CHANGED FROM `m4_socket_discharged_capwired`⟧ ONE hypothesis: the `hcapbase` family.
Everything else — the three conjuncts, the five other carried binder groups, the `δ₀` side
(`0 < δ₀` alone), the pinned `t₁ ≡ 0`, the six leading constants — is byte-identical. -/
theorem m4_socket_discharged_capwired_ws (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct Cq cs T₀ Kq Ks : ℝ,
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ)
                  (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                  DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                    ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                          ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                            (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                            (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                        → DoorCapBase Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                            VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow R M
                (m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
                  m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, hwired⟩ :=
    m4_socket_discharged_capwired hMmu Aexp hAexp
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hterm⟩ := hwired Cp hCp R M C₁ M₀ hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapWS hbandbase harith
  refine hterm ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase ?_ hbandbase harith
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door hws)⟩

/-! ## §5 — ⟦KNOT-1 ARITY SURGERY⟧ the composite at the PER-BLOCK co-factor range

⟦`DoorCapErrWS` NEEDS NO ARITY CHANGE⟧ — confirmed by the KNOT-1 refuter: none of its eleven
fields mentions the co-factor range cap.  `Xd_eq`, `H83_two`, `H83_le`, `P_one`, `coefWS`,
`tail` and `E_ge` speak the base `N_d`, the block window `[P,Q]` and the coprime-tail mass;
`Mr` occurs nowhere.  So §3's `E_binder` wire is reused VERBATIM, and the only thing that
moves in the composite is the TYPE of the `Mr` existential.

**PURELY ADDITIVE.**  §4 stands. -/

set_option maxHeartbeats 1000000 in
-- Same cause as §4.
/-- **⟦THE CAP-WIRED TERMINAL AT THE STRICT PAIR LAW, PER-BLOCK⟧**
(`m4_socket_discharged_capwired_ws_perBlock`).  §4 over
`M4CapWire.m4_socket_discharged_capwired_perBlock`.  `DoorCapErrWS` and `m4_capE_at_door` are
used unchanged — the error bundle is range-cap-free — so the ONE difference from the landed
statement is that the `hcapWS` family's `Mr` existential has type `ℕ → ℕ`. -/
theorem m4_socket_discharged_capwired_ws_perBlock (hMmu : MmuChiRate) (Aexp : ℝ)
    (hAexp : 0 < Aexp) :
    ∃ Ct Cq cs T₀ Kq Ks : ℝ,
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
                  (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                  DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
                    ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                          ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                            (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                            (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                        → DoorCapBasePerBlock Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                            (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow R M
                (m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
                  m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, hwired⟩ :=
    m4_socket_discharged_capwired_perBlock hMmu Aexp hAexp
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hterm⟩ := hwired Cp hCp R M C₁ M₀ hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapWS hbandbase harith
  refine hterm ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase ?_ hbandbase harith
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door hws)⟩

/-! ## §GK — the G-lever twin

⚠ ⟦THE CORRECTION TO THE BRIEF⟧ this file carries NO `3072 * M` literal at all — its only
mentions of the landed base are in DOCSTRINGS (`:421-422`).  It still owes six twins, because
`DoorCapErrWS{,'}` read the levered door datum `winCutH Nd (doorCoeffU_gk K M)` through their
`coefWS` and `tail` fields, and the two composites carry `M4CapWire.DoorCapBase{,PerBlock}_gk`,
`M4RowsChiZero.DoorRowZeroBase_gk`, `M4SocketDischarge.DoorBandBase_gk` and
`M4Assembly.DoorFuseFrame_gk` in their hypothesis lists.

⟦RE-INSTANTIATED, NOT TWINNED⟧ §1's three twist lifts and §2's three `Σ_χ` error moments
(`ramErr_meanSq_all_chi_ws{,_priced,_priced'}`) are `(P, Q)`-ABSTRACT and datum-abstract;
they are re-fired at the levered datum with no new estimate.  `endMass`, `H83`, `blockOmega`
and `SeamCoefWS` read no door ladder.

⚠ ⟦THE BINDER SHADOW⟧ §4's and §5's landed statements bind a REAL `K` (⟦C3⟧'s margined-floor
constant); it is ALPHA-RENAMED to `Kar`.  Both composites carry the lever's own side condition
`hK : K ≤ 1.7·10⁸`, inherited from `M4CapWire.m4_socket_discharged_capwired{,_perBlock}_gk`. -/

/-- `DoorCapErrWS` (:424), at the lever.  Two of the eleven fields move — `coefWS` and `tail`,
both at the levered datum `winCutH Nd (doorCoeffU_gk K M)`; the other nine are VERBATIM. -/
structure DoorCapErrWS_gk (K : ℕ) (M Nd q Xd P Q : ℕ) (b cf : ℕ → ℂ)
    (Tann E Mtail : ℝ) : Prop where
  /-- ⟦THE PIN⟧ the ram-block dyadic parameter IS the socket base. -/
  Xd_eq : Xd = Nd
  /-- `1 ≤ N_d`. -/
  Nd_one : 1 ≤ Nd
  /-- `2 ≤ H₈₃ X θ₂₉₃`. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `H₈₃ X θ₂₉₃ ≤ X`. -/
  H83_le : H83 ((Nd : ℕ) : ℝ) theta293 ≤ ((Nd : ℕ) : ℝ)
  /-- `1 ≤ P`. -/
  P_one : 1 ≤ P
  /-- `0 ≤ T_ann`. -/
  Tann_nonneg : 0 ≤ Tann
  /-- `‖b m‖ ≤ 1`. -/
  b_one : ∀ m, ‖b m‖ ≤ 1
  /-- `‖cf p‖ ≤ 1`. -/
  cf_one : ∀ p, ‖cf p‖ ≤ 1
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law at the LEVERED door datum. -/
  coefWS : SeamCoefWS Xd P Q (winCutH Nd (doorCoeffU_gk K M)) b cf
  /-- ⟦R3a⟧ the coprime-tail mass at the levered datum, priced not pinned. -/
  tail : ∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
      ‖winCutH Nd (doorCoeffU_gk K M) n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail
  /-- `E` dominates the priced four-row bound. -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ))
            + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * Mtail) ≤ E

/-- `m4_capE_at_door` (:466), at the lever. -/
theorem m4_capE_at_door_gk (K : ℕ) {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ}
    {Tann E Mtail : ℝ}
    (h : DoorCapErrWS_gk K M Nd q Xd P Q b cf Tann E Mtail) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU_gk K M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ E := by
  obtain ⟨hXd, hNd, hH2, hHle, hP1, hT, hb1, hcf1, hcoef, htail, hE⟩ := h
  subst hXd
  refine le_trans ?_ hE
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hasupp : ∀ n : ℕ, winCutH Xd (doorCoeffU_gk K M) n ≠ 0 →
      ((Xd : ℕ) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := winCutH_asupp hn
    constructor
    · exact_mod_cast h1
    · have : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
  exact ramErr_meanSq_all_chi_ws_priced q (H83 ((Xd : ℕ) : ℝ) theta293) hH2 (2 * Xd) Xd P Q
    hNd le_rfl hN2 hHle hP1 (winCutH Xd (doorCoeffU_gk K M)) b cf hcoef
    (fun n => norm_doorRowDatumU_le_one_gk K M Xd n) hb1 hcf1 hasupp Mtail htail Tann hT

/-- `DoorCapErrWS'` (:499), at the lever. -/
structure DoorCapErrWS'_gk (K : ℕ) (M Nd q Xd P Q : ℕ) (b cf : ℕ → ℂ)
    (Tann E Mtail : ℝ) : Prop where
  /-- ⟦THE PIN⟧ the ram-block dyadic parameter IS the socket base. -/
  Xd_eq : Xd = Nd
  /-- `1 ≤ N_d`. -/
  Nd_one : 1 ≤ Nd
  /-- `2 ≤ H₈₃ X θ₂₉₃`. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `H₈₃ X θ₂₉₃ ≤ X`. -/
  H83_le : H83 ((Nd : ℕ) : ℝ) theta293 ≤ ((Nd : ℕ) : ℝ)
  /-- ⟦R1's FLOOR⟧ `4 ≤ P` — free at the levered door (`𝒫₁ ≥ 64`, K-INVARIANT). -/
  P_four : 4 ≤ P
  /-- `0 ≤ T_ann`. -/
  Tann_nonneg : 0 ≤ Tann
  /-- `‖b m‖ ≤ 1`. -/
  b_one : ∀ m, ‖b m‖ ≤ 1
  /-- `‖cf p‖ ≤ 1`. -/
  cf_one : ∀ p, ‖cf p‖ ≤ 1
  /-- The STRICT relativized pair law at the LEVERED door datum. -/
  coefWS : SeamCoefWS Xd P Q (winCutH Nd (doorCoeffU_gk K M)) b cf
  /-- The coprime-tail mass at the levered datum, priced not pinned. -/
  tail : ∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
      ‖winCutH Nd (doorCoeffU_gk K M) n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail
  /-- `E` dominates the R1-priced four-row bound. -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (24 / (((Nd : ℕ) : ℝ) * (P : ℝ)) + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * Mtail) ≤ E

/-- `m4_capE_at_door'` (:532), at the lever. -/
theorem m4_capE_at_door'_gk (K : ℕ) {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ}
    {Tann E Mtail : ℝ}
    (h : DoorCapErrWS'_gk K M Nd q Xd P Q b cf Tann E Mtail) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU_gk K M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ E := by
  obtain ⟨hXd, hNd, hH2, hHle, hP4, hT, hb1, hcf1, hcoef, htail, hE⟩ := h
  subst hXd
  refine le_trans ?_ hE
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hasupp : ∀ n : ℕ, winCutH Xd (doorCoeffU_gk K M) n ≠ 0 →
      ((Xd : ℕ) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := winCutH_asupp hn
    constructor
    · exact_mod_cast h1
    · have : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
  exact ramErr_meanSq_all_chi_ws_priced' q (H83 ((Xd : ℕ) : ℝ) theta293) hH2 (2 * Xd) Xd P Q
    hNd le_rfl hN2 hHle hP4 (winCutH Xd (doorCoeffU_gk K M)) b cf hcoef
    (fun n => norm_doorRowDatumU_le_one_gk K M Xd n) hb1 hcf1 hasupp Mtail htail Tann hT

set_option maxHeartbeats 1000000 in
-- The statement re-elaborates the cap-wired terminal's full binder list (same cause as §4).
/-- `m4_socket_discharged_capwired_ws` (:581), at the lever. -/
theorem m4_socket_discharged_capwired_ws_gk (K : ℕ) (hK : K ≤ 170000000) (hMmu : MmuChiRate)
    (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct Cq cs T₀ Kq Ks : ℝ,
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (Kar δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame_gk K M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase_gk K M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ)
                  (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                  DoorCapErrWS_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                    ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                          ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                            (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_gk K M)))
                            (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                        → DoorCapBase_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                            (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_gk K R M
                (m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
                  m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, hwired⟩ :=
    m4_socket_discharged_capwired_gk K hK hMmu Aexp hAexp
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hterm⟩ := hwired Cp hCp R M C₁ M₀ hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapWS hbandbase harith
  refine hterm ε cU bU Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase ?_ hbandbase harith
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door_gk K hws)⟩

set_option maxHeartbeats 1000000 in
-- Same cause as §4.
/-- `m4_socket_discharged_capwired_ws_perBlock` (:655), at the lever. -/
theorem m4_socket_discharged_capwired_ws_perBlock_gk (K : ℕ) (hK : K ≤ 170000000)
    (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct Cq cs T₀ Kq Ks : ℝ,
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (Kar δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame_gk K M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase_gk K M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
                  (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
                  DoorCapErrWS_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                    ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                          ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                            (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_gk K M)))
                            (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                        → DoorCapBasePerBlock_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b
                            cf (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase_gk K x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) Kar
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow_gk K R M
                (m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
                  m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, hwired⟩ :=
    m4_socket_discharged_capwired_perBlock_gk K hK hMmu Aexp hAexp
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hterm⟩ := hwired Cp hCp R M C₁ M₀ hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapWS hbandbase harith
  refine hterm ε cU bU Kar δ₀ hδ₀ hHreg hb1 hc1 hframe hbase ?_ hbandbase harith
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (m4_capE_at_door_gk K hws)⟩

end Salt.MR

end

-- #audit (temporary)
