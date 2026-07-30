/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetChi
import Salt.MR.USetGradedThin

/-!
# USetGChiCount — the PAIR Lemma-8 at the GRADED threshold (stone ⟦ii-2⟧)

`docs/blueprints/flags.md` ⟦C2-SCOPE⟧ / ⟦THE THRESHOLD WALL⟧ and
`docs/exploration/a4-bridge-freeze-0730.md` v2.3: A3/`UsetChi` lifts the **flat**
`δ`-partition (`Decomp.Uset`), while every landed row reaching the spine's `hrows` lives on
the **graded** one (`SeamGraded.UsetG`, MR eq (21)) — and the bridge `UsetG ⊆ Uset` is false
at the door family.  The forced repair is A3 re-lifted at the graded threshold, fibrewise
from the first line.  This file lands its first stone, dispatched as the ii-2 PROBE (the one
item the dossier priced with genuine risk): the `(χ, t)`-pair analogue of
`USetGradedThin.ramQ_graded_count` (:184).

## What the stone is

`ramQChi_graded_count` is the graded **uniformisation** of the landed raw pair count
`USetChi.ramQChi_large_count` (:440), exactly as `ramQ_graded_count` is the graded
uniformisation of `USetThinTL.ramQ_large_count` (:207).  The raw count is fed at the block's
own graded level `V_v := exp(α·v/H)` and the three `v`-dependencies are removed:

* **the exact-`α` collapse** `2·log V_v / log(base_v) ≤ 2α` — the base is `≥ e^{v/H}`
  (`exp_le_ramQbase`), so the height-power leg becomes `(qT)^{2α}` with no pigeonhole factor
  and no `α`-inflation (⟦V6⟧'s "log V/log base = α exactly", V4a respected: `α` is a free
  parameter carried in-statement, never a numeral, and the only fact asked of it is `0 ≤ α`);
* **the uniform level** `V_v² ≤ VJ²` at any uniform level bound `VJ`;
* **the base-`P` floor** in the `exp` leg — the base is `≥ P` (`ramQbase`'s `max`).

The window gates transfer from `[P,Q]` to the block base by
`USetGradedThin.ramQbase_le_of_mem_ramI`, uniformly in `v ∈ ramI H P Q`.

## The two shapes it has to match (checked byte-for-byte before proving)

* **the consumer template** — `ramQ_graded_count` at `q = 1`: argument order, the strict
  `<` lower bound `exp(-α·v/H) < ‖ramQ …‖` (the shape `not_blockSmallG_witness` hands out),
  `hv : v ∈ ramI H P Q`, `hVJ : exp(α·v/H) ≤ VJ`, and the exit product
  `C · S^{2α} · VJ² · exp(2·(log S/log P)·loglog S)`.  The eventual `UsetGChi_thin` (ii-3)
  will filter a pair set by the witnessed `v` and cover it by `|ramI|` copies of this bound,
  mirroring `usetG_thin`.
* **the instantiation source** — `ramQChi_large_count`'s pair genre: index sets are
  `Finset (DirichletCharacter ℂ q × ℝ)`, spacing is `FibreWellSpaced` (per-fibre, ordinates
  sharing a character `≥ 1` apart), the datum is the `χ̄`-twist `chiBarCoeff q r.1 f`, and
  the height is `qT`.  Hence the two `q = 1` gates `1 < T` / `log T` become the landed pair
  shapes `1 ≤ T`, `1 < qT`, `Q ≤ qT`, `30 ≤ log(qT)/log Q`, `5 ≤ loglog(qT)`, and the
  hybrid constant is `1680` (the `q = 1` `840`, doubled).  **No sign flip anywhere in this
  file**: `t` is the ordinate the seam row integrates over; the CATCH #B ∘ N1 involution
  `(χ,t) ↦ (χ⁻¹,−t)` is applied once, inside `ramQChi_large_count`.
* the two shapes are **compatible** — the pair genre changes the index type, the spacing
  predicate, the datum slot and the height argument, none of which the graded uniformisation
  touches: the collapse is a statement about `log V_v`, `log base_v`, `log P` alone.

**Law #253.**  Every growing-quantity gate rides the statement: `1 ≤ T`, `1 < qT`,
`3 ≤ P`, `P ≤ Q`, `Q ≤ qT`, `30 ≤ log(qT)/log Q` (the X₀ law), `5 ≤ loglog(qT)`, `2 ≤ H`,
`0 ≤ α`.  Four log scales stay apart: this file speaks only `log(qT)` (count/height) and the
block scales `log(base)`, `log P`, `log Q`; no `log X`, no `log(5T+1)`.
-/

namespace Salt.MR

open scoped BigOperators

/-- **⟦ii-2⟧ — the PAIR Lemma-8 at the block's own GRADED threshold.**  A per-fibre
well-spaced `ℰ ⊆ (characters) × [−T,T]` on which the `χ̄`-twisted Ramaré block polynomial
`Q_{v,H}(χ̄, 1+it)` EXCEEDS the graded threshold `exp(−α·v/H)` of MR (21) is counted with
the height-power exponent collapsed to exactly `2α` and every `v`-dependence removed:

  `|ℰ| ≤ 1680 · (qT)^{2α} · VJ² · exp(2·(log qT/log P)·loglog qT)`.

The pair analogue of `USetGradedThin.ramQ_graded_count`; obtained from the landed raw pair
count `ramQChi_large_count` at `V := exp(α·v/H)`.  All Lemma-8 gates are carried
in-statement (law #253), transferred from the window `[P,Q]` to the block base by
`ramQbase_le_of_mem_ramI`. -/
theorem ramQChi_graded_count (q : ℕ) [NeZero q] {H α : ℝ} (hH : 2 ≤ H) (hα : 0 ≤ α)
    (P Q v : ℕ) (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (T VJ : ℝ)
    (hP3 : 3 ≤ P) (hPQ : P ≤ Q) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hQT : (Q : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Q : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hv : v ∈ ramI H P Q) (hVJ : Real.exp (α * (v : ℝ) / H) ≤ VJ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hlb : ∀ r ∈ ℰ, Real.exp (-α * (v : ℝ) / H)
      < ‖ramQ H P Q v (chiBarCoeff q r.1 f) r.2‖) :
    (ℰ.card : ℝ)
      ≤ 1680 * ((q : ℝ) * T) ^ (2 * α) * VJ ^ 2
          * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log (P : ℝ))
              * Real.log (Real.log ((q : ℝ) * T))) := by
  set S : ℝ := (q : ℝ) * T with hSdef
  have hH0 : (0 : ℝ) < H := by linarith
  have hP1 : 1 ≤ P := by omega
  have hQ1 : 1 ≤ Q := le_trans hP1 hPQ
  -- the base and its window gates (transferred from `[P,Q]`, uniformly in `v`)
  have hPB : P ≤ ramQbase H P v := by rw [ramQbase]; exact le_max_left _ _
  have hB3 : 3 ≤ ramQbase H P v := le_trans hP3 hPB
  have hBQ : ramQbase H P v ≤ Q := ramQbase_le_of_mem_ramI hH0 hP1 hPQ hv
  have hBT : ((ramQbase H P v : ℕ) : ℝ) ≤ S := le_trans (by exact_mod_cast hBQ) hQT
  have hB3R : (3 : ℝ) ≤ ((ramQbase H P v : ℕ) : ℝ) := by exact_mod_cast hB3
  have hlogB : 0 < Real.log ((ramQbase H P v : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hP3R : (3 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP3
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hlogPB : Real.log (P : ℝ) ≤ Real.log ((ramQbase H P v : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hPB)
  have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hlogBQ : Real.log ((ramQbase H P v : ℕ) : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hBQ)
  have hlogS0 : (0 : ℝ) < Real.log S := Real.log_pos hqT
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log S) := by linarith
  -- the graded level `V_v = exp(α·v/H) ≥ 1`
  have hx0 : (0 : ℝ) ≤ α * (v : ℝ) / H :=
    div_nonneg (mul_nonneg hα (Nat.cast_nonneg v)) hH0.le
  have hV1 : (1 : ℝ) ≤ Real.exp (α * (v : ℝ) / H) := by
    have h := Real.exp_le_exp.mpr hx0
    rwa [Real.exp_zero] at h
  have hκ30B : 30 ≤ Real.log S / Real.log ((ramQbase H P v : ℕ) : ℝ) := by
    refine le_trans hκ30 ?_
    gcongr
  have hlb' : ∀ r ∈ ℰ, (Real.exp (α * (v : ℝ) / H))⁻¹
      ≤ ‖ramQ H P Q v (chiBarCoeff q r.1 f) r.2‖ := by
    intro r hr
    have hneg : Real.exp (-α * (v : ℝ) / H) = (Real.exp (α * (v : ℝ) / H))⁻¹ := by
      rw [show -α * (v : ℝ) / H = -(α * (v : ℝ) / H) by ring, Real.exp_neg]
    rw [← hneg]
    exact (hlb r hr).le
  have hcount := ramQChi_large_count q hH P Q v f hf1 T (Real.exp (α * (v : ℝ) / H))
    hB3 hT1 hqT hBT hV1 hκ30B hLL5 ℰ hws hsub hlb'
  -- (i) the EXACT-α collapse of the height-power leg
  have hvB : (v : ℝ) / H ≤ Real.log ((ramQbase H P v : ℕ) : ℝ) := by
    have h := exp_le_ramQbase H P v
    calc (v : ℝ) / H = Real.log (Real.exp ((v : ℝ) / H)) := (Real.log_exp _).symm
      _ ≤ Real.log ((ramQbase H P v : ℕ) : ℝ) := Real.log_le_log (Real.exp_pos _) h
  have hexpo : 2 * Real.log (Real.exp (α * (v : ℝ) / H))
      / Real.log ((ramQbase H P v : ℕ) : ℝ) ≤ 2 * α := by
    rw [Real.log_exp, div_le_iff₀ hlogB,
      show α * (v : ℝ) / H = α * ((v : ℝ) / H) by ring]
    have h1 : α * ((v : ℝ) / H) ≤ α * Real.log ((ramQbase H P v : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hvB hα
    linarith
  have h1 : S ^ (2 * Real.log (Real.exp (α * (v : ℝ) / H))
      / Real.log ((ramQbase H P v : ℕ) : ℝ)) ≤ S ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_le hqT.le hexpo
  -- (ii) the uniform level
  have h2 : Real.exp (α * (v : ℝ) / H) ^ 2 ≤ VJ ^ 2 := by
    have h0 : (0 : ℝ) ≤ Real.exp (α * (v : ℝ) / H) := (Real.exp_pos _).le
    nlinarith [hVJ, h0, hV1]
  -- (iii) the base-`P` floor in the `exp` leg
  have h3 : Real.exp (2 * (Real.log S / Real.log ((ramQbase H P v : ℕ) : ℝ))
        * Real.log (Real.log S))
      ≤ Real.exp (2 * (Real.log S / Real.log (P : ℝ)) * Real.log (Real.log S)) := by
    refine Real.exp_le_exp.mpr ?_
    have hd : Real.log S / Real.log ((ramQbase H P v : ℕ) : ℝ)
        ≤ Real.log S / Real.log (P : ℝ) := by gcongr
    nlinarith [hd, hLL0]
  -- the product
  have hSpow0 : (0 : ℝ) ≤ S ^ (2 * α) :=
    (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < S) _).le
  refine le_trans hcount ?_
  have step1 : (1680 : ℝ) * S ^ (2 * Real.log (Real.exp (α * (v : ℝ) / H))
      / Real.log ((ramQbase H P v : ℕ) : ℝ)) ≤ 1680 * S ^ (2 * α) := by linarith
  have step2 : (1680 : ℝ) * S ^ (2 * Real.log (Real.exp (α * (v : ℝ) / H))
        / Real.log ((ramQbase H P v : ℕ) : ℝ)) * Real.exp (α * (v : ℝ) / H) ^ 2
      ≤ 1680 * S ^ (2 * α) * VJ ^ 2 :=
    mul_le_mul step1 h2 (sq_nonneg _) (mul_nonneg (by norm_num) hSpow0)
  exact mul_le_mul step2 h3 (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg (by norm_num) hSpow0) (sq_nonneg _))

end Salt.MR
