/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetGChiCount
import Salt.MR.USetChiTS

/-!
# USetGChi — the PAIR `𝒰`-set at the GRADED threshold (stones ⟦ii-1⟧, ⟦ii-3⟧, ⟦ii-4⟧)

`docs/blueprints/flags.md` ⟦C2-SCOPE lands⟧ / ⟦THE THRESHOLD WALL⟧ and
`docs/exploration/a4-bridge-freeze-0730.md` v2.3, ratified as **council ruling C2** on the
morning of 2026-07-30 (the graded fibrewise re-lift); dispatched as the first-bank wave
**RELIFT-A** (items ii-1 + ii-3 + ii-4, on top of the ii-2 probe).

## Why this file exists (⟦THE THRESHOLD WALL⟧, in one paragraph)

A3 / `USetChi.UsetChi` is the `χ`-lift of the **flat** `δ`-partition (`Decomp.Uset`), while
every landed row reaching the spine's `hrows` lives on the **graded** partition
(`SeamGraded.UsetG`, MR eq (21)).  The bridging inclusion `UsetG ⊆ Uset` needs
`α_Jb·(log Q_Jb/log P_Jb) ≤ 1/4 − η`, i.e. `M ≤ 2/7` at the door family against `1 ≤ M` —
false by `3.5·M ≈ 6.6e62`, and not tunable (`η → 1/6` still demands `M ≤ 1/2`).  So the port
lifted the superseded route, and A3 must be re-lifted at the graded threshold.  This file is
that re-lift's pair-level core: the graded `𝒰`-set of PAIRS, its thinness, and its razor
bundle.  Written fibrewise from the first line, so C2's design (ii) (`Set (χ × ℝ)` with
fibrewise measurability) costs nothing extra.

## What is consumed and what is new

* **Consumed as landed, never restated.**  `USetGChiCount.ramQChi_graded_count` (⟦ii-2⟧, the
  probe) is THE per-block pair count at the graded level; `USetGradedThin`'s witness page
  (`not_blockSmallG_witness_of_mem_UsetG`, `ramI_div_le_log`, `gradeV_sq_le_rpow`) and
  `USetPrice.ramI_card_le_pin` are character-free and are reused VERBATIM at the twisted
  datum; `USetChi`'s pair-spacing page (`FibreWellSpaced`, `fibreWellSpaced_of_subset`) and
  `USetThinTS.thin_sqrt_kill` likewise; and `USetChiTS.charDebit_le_rpow` — the whole
  `φ(q)`-genre debit page — is reusable **verbatim** (it is a statement about `q^{2α}` and
  `log X` alone, blind to which partition produced the `α`).
* **New here.**  `UsetGChi` (ii-1) with its membership/fibre/measurability trio;
  `UsetGChi_thin` and the `_Q` / `_pin` variants (ii-3); `thinBundleGChi` and
  `UsetGChi_thin_sqrt_kill{,_absorbed,_at_debit}` (ii-4).

## Why the graded pair thinness is SIMPLER than the flat pair thinness

`USetChi.UsetChi_thin` reads the flat `¬ BlockSmallAt` as "*some* sub-block
`[P,Q] ⊆ [P_Jb,Q_Jb]` is large" and pays two devices for it: the ratio-2 `ratioChain`
refinement and a pigeonhole over its `K₀ = ⌊log₂(Q_Jb+1)⌋+1 pieces`, after which the union
runs over `dyadicPairs` and the level is degraded to `δ/K₀` (the `hVinv` gate).  At the
graded threshold **both devices disappear**: `¬ BlockSmallG` already names one of the finitely
many blocks of `ramI (H_Jb) (P_Jb) (Q_Jb)` — MR's own index set — and each block is a
ratio-`≤ 2` window by construction.  Hence

* the union runs over `I_Jb` itself, priced by `USetPrice.ramI_card_le_pin`;
* there is no `K₀` division, so no `hVinv`/`hδ0` gate and no `δ` at all;
* **the height-power leg is already EXACTLY `(qT)^{2α_Jb}`** (the exact-`α` collapse, done
  once and for all inside `ramQChi_graded_count`), so no `UsetChi_thin_alpha` analogue is
  needed or wanted: the flat file's `hVα : log V ≤ α·log P_Jb` gate has no graded counterpart
  because the collapse is an identity at the block's own scale, not an inequality at a free
  `α`.

The ⟦ii-2 PROBE⟧'s findings bind this file and are honoured: the exact-`α` collapse carries
NO inflation and NO `φ(q)` at the count (Lemma 6.5 counts PAIRS — there is no union over
characters anywhere below), and NO adapter is owed between `ramQChi_graded_count` and the
thinness (`not_blockSmallG_witness`'s strict `<` form matches the count's `hlb` slot with `v`
fixed in-statement).

## Sign convention (CATCH #B ∘ N1), byte-checked

`BlockSmallG` (`SeamGraded` :97) and `ramQ` are stated in the `+it` convention with no flip;
the CATCH #B ∘ N1 involution `(χ,t) ↦ (χ⁻¹,−t)` is applied **once**, inside
`USetChi.ramQChi_large_count`, and `ramQChi_graded_count` inherits it.  **Therefore this file
performs NO negation anywhere**: every `t` is the ordinate the seam row integrates over, and
`ℰ ⊆ (characters) × [−T,T]` is stated once per rung.

## Law #253 and the four log scales

Every growing-quantity gate rides the statement and is never absorbed: `1 ≤ T`, `1 < qT`,
`3 ≤ P_Jb`, `P_Jb ≤ Q_Jb`, `Q_Jb ≤ qT`, `30 ≤ log(qT)/log Q_Jb` (the X₀ law),
`5 ≤ loglog(qT)`, `2 ≤ H_Jb`, `0 ≤ α_Jb`.  §1–§3 speak **only** `log(qT)` (count/height) and
the block scales `log(base)`, `log P_Jb`, `log Q_Jb` — no `log X`, no `log(5T+1)`.  `log X`
enters exactly twice, both times explicitly gated and both times at the §8.3 pins where the
landed `q = 1` template already puts it: `UsetGChi_thin_pin` (through `H₈₃`/`Q₈₃` and the
`X^ε` level bound) and the razor's `T ≤ X` (through `thin_sqrt_kill`, MR Step 0).  Nothing is
ever silently swapped between the two.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), §8.3 p.29; MRT v3 App. A;
KMT §6 (Lemmas 6.2/6.5).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — ⟦ii-1⟧: the pair-level graded `𝒰`-set -/

/-- **⟦ii-1⟧ — `𝒰` at `(χ, t)`, at the GRADED threshold.**  The pair `(χ, t)` is exceptional
when NO index `j ∈ [1, J]` carries MR (21) across the whole block range `I_j` of the
`χ̄`-twisted datum.  Definitionally the `q = 1` graded set (`SeamGraded.UsetG`) of the twisted
datum, **fibre by fibre** — which is what makes `USetGradedThin`'s witness page reusable
verbatim, and what makes C2's design (ii) free.

Mirrors `USetChi.UsetChi` (:278) with `Uset ↝ UsetG`, i.e. with the flat `δ : ℝ` replaced by
MR (21)'s per-block pair of sequences `Hseq αseq : ℕ → ℝ`. -/
def UsetGChi (q : ℕ) (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ) :
    Set (DirichletCharacter ℂ q × ℝ) :=
  {r | r.2 ∈ UsetG (chiBarCoeff q r.1 f) Pseq Qseq Hseq αseq J}

/-- Membership unfolded (the `Iff.rfl` genre, as for the flat `mem_UsetChi`). -/
lemma mem_UsetGChi {q : ℕ} {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ} {J : ℕ}
    {r : DirichletCharacter ℂ q × ℝ} :
    r ∈ UsetGChi q f Pseq Qseq Hseq αseq J
      ↔ ∀ j, 1 ≤ j → j ≤ J →
          ¬ BlockSmallG (chiBarCoeff q r.1 f) Pseq Qseq Hseq αseq j r.2 :=
  Iff.rfl

/-- **The fibre is the `q = 1` graded `𝒰` of the twisted datum** — by definition, not by a
lemma about characters.  This single `rfl` is the reason the whole graded thinness/bundle
chain below is a retype and not a re-derivation. -/
lemma UsetGChi_fibre (q : ℕ) (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J : ℕ)
    (χ : DirichletCharacter ℂ q) :
    {t : ℝ | (χ, t) ∈ UsetGChi q f Pseq Qseq Hseq αseq J}
      = UsetG (chiBarCoeff q χ f) Pseq Qseq Hseq αseq J := rfl

/-- **⟦ii-1⟧ — FIBREWISE MEASURABILITY** (C2's design (ii), the pair spelling).  Every
character fibre of the graded pair `𝒰` is measurable, by `SeamGraded.measurableSet_UsetG` at
the `χ̄`-twisted datum.  The supply is FREE: `measurableSet_UsetG` is `∀ f`, and the fibre is
definitionally its value at `chiBarCoeff q χ f`. -/
lemma measurableSet_UsetGChi_fibre (q : ℕ) (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ)
    (Hseq αseq : ℕ → ℝ) (J : ℕ) (χ : DirichletCharacter ℂ q) :
    MeasurableSet {t : ℝ | (χ, t) ∈ UsetGChi q f Pseq Qseq Hseq αseq J} := by
  rw [UsetGChi_fibre]
  exact measurableSet_UsetG (chiBarCoeff q χ f) Pseq Qseq Hseq αseq J

/-- **The witness at the pair level.**  A pair of the graded `𝒰` violates MR (21) at every
level of `[1,J]`; in particular at a chosen `Jb`, where it NAMES a block index `v ∈ I_Jb` of
its own twisted datum.  This is `USetGradedThin.not_blockSmallG_witness_of_mem_UsetG` read at
`f := chiBarCoeff q r.1 f` — the "no adapter owed" of the ⟦ii-2 PROBE⟧'s finding (4), and the
strict `<` form `ramQChi_graded_count`'s `hlb` slot asks for. -/
lemma not_blockSmallG_witness_of_mem_UsetGChi {q : ℕ} {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ}
    {Hseq αseq : ℕ → ℝ} {J Jb : ℕ} {r : DirichletCharacter ℂ q × ℝ}
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hr : r ∈ UsetGChi q f Pseq Qseq Hseq αseq J) :
    ∃ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
        < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v (chiBarCoeff q r.1 f) r.2‖ :=
  not_blockSmallG_witness_of_mem_UsetG hJb1 hJbJ hr

/-! ## §2 — ⟦ii-3⟧: the GRADED `χ`-thinness -/

/-- **⟦ii-3⟧ — THE GRADED PAIR THINNESS (`UsetGChi_thin`).**  A per-fibre well-spaced
`ℰ ⊆ ((characters) × [−T,T]) ∩ 𝒰G_χ` is thin: each of its pairs violates MR (21) at some
block index `v ∈ I_Jb` **of its own fibre**, so `ℰ` is covered by the `|I_Jb|` per-block
large-value sets, each counted by `ramQChi_graded_count` at the *same* uniform bound.  Hence

  `|ℰ| ≤ |I_Jb| · 1680 · (qT)^{2α_Jb} · VJ² · exp(2·(log qT/log P_Jb)·loglog qT)`.

`VJ` is any uniform bound on the graded levels `exp(α_Jb·v/H_Jb)`, `v ∈ I_Jb`; the concrete
`VJ = Q_Jb^{α_Jb}` is supplied by `UsetGChi_thin_Q`.  Compare `USetChi.UsetChi_thin` (:300) —
same exit shape, with `dyadicPairs` replaced by MR's own `ramI`, the `K₀` pigeonhole gone,
and the `δ`/`hVinv` level degradation gone with it.  There is **no `φ(q)` union factor**: the
character count enters only through the hybrid height `qT`, because Lemma 6.5 counts pairs.

**Non-degeneracy** (the `G0` empty-block trap) is pinned by `2 ≤ H_Jb`, `3 ≤ P_Jb`,
`P_Jb ≤ Q_Jb`; `1 ≤ Jb ≤ J` keeps the `UsetGChi` hypothesis engaged. -/
theorem UsetGChi_thin (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J) :
    (ℰ.card : ℝ)
      ≤ ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ)
        * (1680 * ((q : ℝ) * T) ^ (2 * αseq Jb) * VJ ^ 2
            * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log ((Pseq Jb : ℕ) : ℝ))
                * Real.log (Real.log ((q : ℝ) * T)))) := by
  classical
  set B : ℝ := 1680 * ((q : ℝ) * T) ^ (2 * αseq Jb) * VJ ^ 2
      * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log ((Pseq Jb : ℕ) : ℝ))
          * Real.log (Real.log ((q : ℝ) * T))) with hBdef
  -- (i) every candidate block's count set is Lemma-6.5 bounded, uniformly in `v`
  have hpiece : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      (((ℰ.filter (fun r => Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
          < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v (chiBarCoeff q r.1 f) r.2‖)).card : ℝ))
        ≤ B := by
    intro v hv
    exact ramQChi_graded_count q hH2 hα0 (Pseq Jb) (Qseq Jb) v f hf1 T VJ hP3 hPQ hT1 hqT
      hQT hκ30 hLL5 hv (hVJ v hv) _
      (fibreWellSpaced_of_subset (Finset.filter_subset _ _) hws)
      (fun r hr => hsub r (Finset.mem_filter.mp hr).1)
      (fun r hr => (Finset.mem_filter.mp hr).2)
  -- (ii) the count sets cover `ℰ` (each pair names its own violating block, in its own fibre)
  have hcover : ℰ ⊆ (ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).biUnion
      (fun v => ℰ.filter (fun r => Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
        < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v (chiBarCoeff q r.1 f) r.2‖)) := by
    intro r hr
    obtain ⟨v, hv, hbig⟩ :=
      not_blockSmallG_witness_of_mem_UsetGChi hJb1 hJbJ (hU r hr)
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨hr, hbig⟩⟩
  -- (iii) the union bound over `I_Jb`
  calc (ℰ.card : ℝ)
      ≤ (((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).biUnion
          (fun v => ℰ.filter (fun r => Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
            < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v (chiBarCoeff q r.1 f) r.2‖))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          ((ℰ.filter (fun r => Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
            < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v (chiBarCoeff q r.1 f) r.2‖)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb), B := Finset.sum_le_sum hpiece
    _ = ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **⟦ii-3′⟧ — the graded pair thinness at the concrete level `VJ = Q_Jb^{α_Jb}`.**  The
uniform level bound is free: `v ∈ I_Jb` forces `v/H_Jb ≤ log Q_Jb`, hence
`exp(α_Jb·v/H_Jb) ≤ Q_Jb^{α_Jb}`.  The `q = 1` twin is `USetGradedThin.usetG_thin_Q`; the
supply lemma `ramI_div_le_log` is character-free and is reused verbatim. -/
theorem UsetGChi_thin_Q (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J) :
    (ℰ.card : ℝ)
      ≤ ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ)
        * (1680 * ((q : ℝ) * T) ^ (2 * αseq Jb)
            * (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2
            * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log ((Pseq Jb : ℕ) : ℝ))
                * Real.log (Real.log ((q : ℝ) * T)))) := by
  have hH0 : (0 : ℝ) < Hseq Jb := by linarith
  have hP1 : 1 ≤ Pseq Jb := by omega
  have hQ1 : 1 ≤ Qseq Jb := le_trans hP1 hPQ
  have hQ0R : (0 : ℝ) < ((Qseq Jb : ℕ) : ℝ) := by exact_mod_cast hQ1
  refine UsetGChi_thin q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T _ hT1 hqT hP3
    hPQ hQT hκ30 hLL5 ?_ ℰ hws hsub hU
  intro v hv
  have hdiv := ramI_div_le_log hH0 hQ1 hv
  have hle : αseq Jb * (v : ℝ) / Hseq Jb ≤ Real.log ((Qseq Jb : ℕ) : ℝ) * αseq Jb := by
    rw [show αseq Jb * (v : ℝ) / Hseq Jb = αseq Jb * ((v : ℝ) / Hseq Jb) by ring]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hα0]
  calc Real.exp (αseq Jb * (v : ℝ) / Hseq Jb)
      ≤ Real.exp (Real.log ((Qseq Jb : ℕ) : ℝ) * αseq Jb) := Real.exp_le_exp.mpr hle
    _ = ((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb) := (Real.rpow_def_of_pos hQ0R _).symm

/-- **⟦ii-3″⟧ — THE GRADED PAIR THINNESS AT THE §8.3 PINS (`UsetGChi_thin_pin`).**  With
`H_Jb = H₈₃ X θ₂₉₃ = (log X)^{θ}` and `Q_Jb ≤ Q₈₃ X`, the block count is priced by
`USetPrice.ramI_card_le_pin` and the graded level is `X^{o(1)}` by
`USetGradedThin.gradeV_sq_le_rpow` — both character-free, both reused verbatim:

  `|ℰ| ≤ 2(log X)^{1+θ₂₉₃} · 1680 · (qT)^{2α_Jb} · X^ε · exp(2·(log qT/log P_Jb)·loglog qT)`.

The `q = 1` twin is `USetGradedThin.usetG_thin_pin`.  **This is the ONE rung of §1–§3 where
`log X` appears**, and it appears exactly where the landed template puts it — the §8.3 pins —
with every gate in-statement (law #253): the X₀ law `30 ≤ log(qT)/log Q_Jb`, `5 ≤ loglog(qT)`,
`e ≤ log X`, `2/ε ≤ loglog X` (the `X^{o(1)}` threshold), `α_Jb ≤ 1` (the honest `α` gate — no
inflation, cf. ⟦V4a⟧), and the non-degeneracy pins `2 ≤ H_Jb`, `3 ≤ P_Jb ≤ Q_Jb`.  The
count/height scale stays `log(qT)` throughout; the two scales are never swapped. -/
theorem UsetGChi_thin_pin (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (X ε T : ℝ) (hX1 : 1 < X) (hε : 0 < ε)
    (hLe : Real.exp 1 ≤ Real.log X) (hLL : 2 / ε ≤ Real.log (Real.log X))
    (hHpin : Hseq Jb = H83 X theta293) (hH2 : 2 ≤ Hseq Jb)
    (hα0 : 0 ≤ αseq Jb) (hα1 : αseq Jb ≤ 1)
    (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQpin : ((Qseq Jb : ℕ) : ℝ) ≤ Q83 X) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J) :
    (ℰ.card : ℝ)
      ≤ 2 * (Real.log X) ^ (1 + theta293)
        * (1680 * ((q : ℝ) * T) ^ (2 * αseq Jb) * X ^ ε
            * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log ((Pseq Jb : ℕ) : ℝ))
                * Real.log (Real.log ((q : ℝ) * T)))) := by
  have hP1 : 1 ≤ Pseq Jb := by omega
  have hQ0 : 0 < Qseq Jb := lt_of_lt_of_le hP1 hPQ
  have hSpow0 : (0 : ℝ) ≤ ((q : ℝ) * T) ^ (2 * αseq Jb) :=
    (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < (q : ℝ) * T) _).le
  have hraw := UsetGChi_thin_Q q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T hT1 hqT
    hP3 hPQ hQT hκ30 hLL5 ℰ hws hsub hU
  -- the block count at the pin (character-free, verbatim)
  have hcard : ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ)
      ≤ 2 * (Real.log X) ^ (1 + theta293) := by
    rw [hHpin]
    exact ramI_card_le_pin X (Pseq Jb) (Qseq Jb) hQ0 hQpin hLe
  -- the graded level at the pin (character-free, verbatim)
  have hlev : (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2 ≤ X ^ ε :=
    gradeV_sq_le_rpow hX1 hQ0 hα0 hα1 hε hQpin hLL
  refine le_trans hraw ?_
  have hinner : 1680 * ((q : ℝ) * T) ^ (2 * αseq Jb)
        * (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2
        * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log ((Pseq Jb : ℕ) : ℝ))
            * Real.log (Real.log ((q : ℝ) * T)))
      ≤ 1680 * ((q : ℝ) * T) ^ (2 * αseq Jb) * X ^ ε
        * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log ((Pseq Jb : ℕ) : ℝ))
            * Real.log (Real.log ((q : ℝ) * T))) := by
    have hnn : (0 : ℝ) ≤ 1680 * ((q : ℝ) * T) ^ (2 * αseq Jb) :=
      mul_nonneg (by norm_num) hSpow0
    have h1 : 1680 * ((q : ℝ) * T) ^ (2 * αseq Jb)
          * (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2
        ≤ 1680 * ((q : ℝ) * T) ^ (2 * αseq Jb) * X ^ ε :=
      mul_le_mul_of_nonneg_left hlev hnn
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hinner0 : (0 : ℝ) ≤ 1680 * ((q : ℝ) * T) ^ (2 * αseq Jb)
      * (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2
      * Real.exp (2 * (Real.log ((q : ℝ) * T) / Real.log ((Pseq Jb : ℕ) : ℝ))
          * Real.log (Real.log ((q : ℝ) * T))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hSpow0) (sq_nonneg _))
      (Real.exp_pos _).le
  have hLX0 : (0 : ℝ) < Real.log X := by
    have he1 : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    linarith
  have hcard0 : (0 : ℝ) ≤ 2 * (Real.log X) ^ (1 + theta293) := by
    have := Real.rpow_nonneg hLX0.le (1 + theta293)
    linarith
  exact mul_le_mul hcard hinner hinner0 hcard0

/-! ## §3 — ⟦ii-4⟧: the razor bundle and the `√T` kill -/

/-- **⟦ii-4⟧ — the `X^{o(1)}` bundle of the GRADED `χ`-thinness count**, at the hybrid height
`S` (the consumer plugs `S := qT`): MR's own block count `|I_J|` (character-free — priced by
`USetPrice.ramI_card_le_pin`), Lemma 6.5's absolute `1680`, the uniform graded level `VJ²`,
and the count's `exp(2(log S/log P_J)·loglog S)` tail.  Explicit by construction (law #253).

The graded twin of `USetChiTS.thinBundleChi` (:190), with `dyadicPairs P_J Q_J` replaced by
`ramI H_J P_J Q_J` — hence the extra `H` argument, and hence the disappearance of the `K₀`
pigeonhole from everything downstream. -/
noncomputable def thinBundleGChi (S VJ H : ℝ) (Pj Qj : ℕ) : ℝ :=
  ((ramI H Pj Qj).card : ℝ)
    * (1680 * VJ ^ 2 * Real.exp (2 * (Real.log S / Real.log Pj) * Real.log (Real.log S)))

lemma thinBundleGChi_nonneg (S VJ H : ℝ) (Pj Qj : ℕ) : 0 ≤ thinBundleGChi S VJ H Pj Qj := by
  rw [thinBundleGChi]
  have h := Real.exp_pos (2 * (Real.log S / Real.log Pj) * Real.log (Real.log S))
  positivity

/-- **⟦ii-4⟧ — `UsetGChi_thin` in bundle form.**  A pure regrouping: the height-power leg is
already EXACTLY `(qT)^{2α_Jb}` (the exact-`α` collapse, discharged inside
`ramQChi_graded_count`), so the flat file's `UsetChi_thin_alpha` step — which spends an
in-statement gate `log V ≤ α·log P_Jb` to bound Lemma 6.5's `2·log V/log P_Jb` by `2α` — has
NO graded counterpart and is not needed.  That is the whole simplification the graded
threshold buys at this rung. -/
theorem UsetGChi_thin_bundle (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J) :
    (ℰ.card : ℝ)
      ≤ thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
          * ((q : ℝ) * T) ^ (2 * αseq Jb) := by
  have hraw := UsetGChi_thin q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T VJ hT1 hqT
    hP3 hPQ hQT hκ30 hLL5 hVJ ℰ hws hsub hU
  refine hraw.trans (le_of_eq ?_)
  rw [thinBundleGChi]
  ring

/-- **⟦ii-4⟧ — THE RAZOR, GRADED AND `χ`-LIFTED.**  The landed `USetThinTS.thin_sqrt_kill` is
character-free AND partition-free arithmetic and is reused VERBATIM, with the bundle carrying
the single character debit `q^{2α_Jb}` — the whole cost of the hybrid height
`(qT)^{2α_Jb} = q^{2α_Jb}·T^{2α_Jb}`.  MR Step 0's `T ≤ X` and the gate `α_Jb ≤ 1/4 − η` are
the landed ones; the `α` is now MR (21)'s own `α_Jb`, not a free parameter tied to a level by
a `hVα` gate.

  `|ℰ|·√T ≤ q^{2α_Jb}·bundle·X^{1−2η}`.

The `q = 1`/flat twin is `USetChiTS.UsetChi_thin_sqrt_kill` (:247). -/
theorem UsetGChi_thin_sqrt_kill (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J)
    (η X : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) :
    (ℰ.card : ℝ) * Real.sqrt T
      ≤ (q : ℝ) ^ (2 * αseq Jb)
          * thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
          * X ^ (1 - 2 * η) := by
  have hq0 : (0 : ℝ) < q := by
    have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hcnt := UsetGChi_thin_bundle q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T VJ
    hT1 hqT hP3 hPQ hQT hκ30 hLL5 hVJ ℰ hws hsub hU
  have hsplit : ((q : ℝ) * T) ^ (2 * αseq Jb)
      = (q : ℝ) ^ (2 * αseq Jb) * T ^ (2 * αseq Jb) := Real.mul_rpow hq0.le hT0
  have hbundle0 : (0 : ℝ) ≤ thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) :=
    thinBundleGChi_nonneg _ _ _ _ _
  have hdeb0 : (0 : ℝ) ≤ (q : ℝ) ^ (2 * αseq Jb) := Real.rpow_nonneg hq0.le _
  have hcnt' : (ℰ.card : ℝ)
      ≤ ((q : ℝ) ^ (2 * αseq Jb)
          * thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb))
        * T ^ (2 * αseq Jb) := by
    rw [hsplit] at hcnt
    calc (ℰ.card : ℝ)
        ≤ thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * ((q : ℝ) ^ (2 * αseq Jb) * T ^ (2 * αseq Jb)) := hcnt
      _ = ((q : ℝ) ^ (2 * αseq Jb)
            * thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb))
          * T ^ (2 * αseq Jb) := by ring
  exact thin_sqrt_kill T X
    ((q : ℝ) ^ (2 * αseq Jb)
      * thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb))
    (αseq Jb) η (ℰ.card : ℝ) hT1 hTX (mul_nonneg hdeb0 hbundle0) hα hη2 hcnt'

/-- **⟦ii-4⟧ — THE GRADED RAZOR WITH THE DEBIT ABSORBED.**  `|ℰ|·√T ≤ bundle·X^{1−2η+ε}`:
the character debit costs the exponent `ε`, and at `ε ≤ η` the razor still exits at `X^{1−η}`
— half the margin pays for the whole `φ(q)`-genre cost.  The debit page is
`USetChiTS.charDebit_le_rpow`, **reusable verbatim** (see `UsetGChi_thin_sqrt_kill_at_debit`).

The `q = 1`/flat twin is `USetChiTS.UsetChi_thin_sqrt_kill_absorbed` (:375); the exits match
byte-for-byte apart from the bundle's identity. -/
theorem UsetGChi_thin_sqrt_kill_absorbed (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J)
    (η X ε : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hdebit : (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε) :
    (ℰ.card : ℝ) * Real.sqrt T
      ≤ thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
          * X ^ (1 - 2 * η + ε) := by
  have hraw := UsetGChi_thin_sqrt_kill q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0
    T VJ hT1 hqT hP3 hPQ hQT hκ30 hLL5 hVJ ℰ hws hsub hU η X hα hη2 hTX
  have hbundle0 : (0 : ℝ) ≤ thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb) :=
    thinBundleGChi_nonneg _ _ _ _ _
  have hXpow0 : (0 : ℝ) < X ^ (1 - 2 * η) := Real.rpow_pos_of_pos hX0 _
  have hstep : (q : ℝ) ^ (2 * αseq Jb)
        * thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
        * X ^ (1 - 2 * η)
      ≤ thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
          * X ^ (1 - 2 * η + ε) := by
    have hsum : X ^ (1 - 2 * η + ε) = X ^ (1 - 2 * η) * X ^ ε := by
      rw [Real.rpow_add hX0]
    rw [hsum]
    have h1 : (q : ℝ) ^ (2 * αseq Jb)
          * thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
          * X ^ (1 - 2 * η)
        = (thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η)) * (q : ℝ) ^ (2 * αseq Jb) := by ring
    have h2 : thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
          * (X ^ (1 - 2 * η) * X ^ ε)
        = (thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η)) * X ^ ε := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hdebit (mul_nonneg hbundle0 hXpow0.le)
  exact le_trans hraw hstep

/-- **⟦ii-4⟧ — the graded razor at the PRICED debit** (the verbatim reuse of
`USetChiTS.charDebit_le_rpow`).  At the port's modulus gate `q ≤ (log X)^{12}` and
`2α_Jb ≤ 1/2` the whole character cost is `q^{2α_Jb} ≤ √q ≤ (log X)^6 ≤ X^ε`, with
`ε = 1/1000` HALF the landed `2η ≥ 1/500` and the floor `e^{40} ≤ log X` some ~378 orders of
magnitude below the `𝒰`-leg's own X₀ law.  The debit page is blind to which partition produced
the `α`, so it needs no graded twin: this rung is pure wiring. -/
theorem UsetGChi_thin_sqrt_kill_at_debit (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : 30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (ℰ : Finset (DirichletCharacter ℂ q × ℝ)) (hws : FibreWellSpaced ℰ)
    (hsub : ∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T)
    (hU : ∀ r ∈ ℰ, r ∈ UsetGChi q f Pseq Qseq Hseq αseq J)
    (η X ε : ℝ) (hα : αseq Jb ≤ 1 / 4 - η) (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X)
    (hqlog : (q : ℝ) ≤ (Real.log X) ^ 12) (h2α : 2 * αseq Jb ≤ 1 / 2)
    (hε : 1 / 1000 ≤ ε) (hXfloor : Real.exp 40 ≤ Real.log X) :
    (ℰ.card : ℝ) * Real.sqrt T
      ≤ thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
          * X ^ (1 - 2 * η + ε) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  exact UsetGChi_thin_sqrt_kill_absorbed q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0
    T VJ hT1 hqT hP3 hPQ hQT hκ30 hLL5 hVJ ℰ hws hsub hU η X ε hα hη2 hTX hX0
    (charDebit_le_rpow X ε hX0 q hq1 hqlog (αseq Jb) h2α hε hXfloor)

end Salt.MR
