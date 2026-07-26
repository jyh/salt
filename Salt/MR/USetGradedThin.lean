/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SeamGraded
import Salt.MR.USetThinTL
import Salt.MR.USetPrice

/-!
# USetGradedThin — `𝒰` is thin at the GRADED threshold (ROUTE G, stone G1a)

`docs/exploration/hsup-design.md` ⟦V6⟧'s Route-G ladder, node `G1a`, on top of `G0`
(`Salt.MR.SeamGraded`).  Everything here is **parallel and additive**: the flat original
(`USetThin.Uset_thin`) is untouched heritage; this file supplies its graded twin.

## Why the graded route is CLEANER than the flat one

`Uset_thin` reads the flat `¬ BlockSmallAt` as "*some* sub-block `[P,Q] ⊆ [P_J,Q_J]` is
large", which is a statement about an ARBITRARY sub-range.  Turning that into something
Lemma 8 can count costs two devices: the ratio-2 `ratioChain` refinement and a pigeonhole
over its `K₀ = ⌊log₂(Q_J+1)⌋+1` pieces (`exists_piece_large`), after which the union runs
over the `t`-free family `dyadicPairs` and the pigeonhole loses a factor `K₀` in the level.

At the graded threshold **both devices disappear**.  `¬ BlockSmallG` already names one of
the FINITELY many blocks of `ramI (H_J) (P_J) (Q_J)` — MR's own index set — and each block
is a ratio-`≤ 2` window by construction (`ramQblock_le_two_base`).  So:

* the union runs over `I_J = ramI (Hseq J) (Pseq J) (Qseq J)` itself (`|I_J|` is the honest
  block count, priced by `USetPrice.ramI_card_le_pin`);
* the level at block `v` is `V_v := exp(α_J·v/H_J)` — no `K₀` division;
* **`log V_v / log (ramQbase H_J P_J v) ≤ α_J`, with EQUALITY at the block's own scale**
  — the base is `≥ e^{v/H_J}` (`exp_le_ramQbase`) and equals it whenever the `max P` and the
  `⌈·⌉` do not bite, so Lemma 8's `T`-power leg collapses to exactly `T^{2α_J}`, with no
  pigeonhole factor and no `α`-inflation.  This is ⟦V6⟧'s "log V/log base = α_J exactly",
  and it is the reason the graded row can afford Lemma 8 at all.

The V4a α-inflation finding is respected: `α_J` is a free parameter carried in-statement,
never a numeral, and the only facts asked of it are `0 ≤ α_J` (and `α_J ≤ 1` at the pin).

## THE EMPTY-BLOCK VACUITY (the `G0` trap, discharged here)

`G0` banked the structural trap: `BlockSmallG` is a bounded `∀` over `ramI`, so an **empty**
`ramI` makes it vacuously TRUE and the graded partition degenerates (`UsetG` becomes empty
and every thinness claim is silently vacuous).  This file pins non-degeneracy on both sides:

* `ramI_nonempty` — the geometric pin: `0 ≤ H`, `1 ≤ P`, `P ≤ Q` ⟹ `I` is nonempty
  (`⌊H log P⌋ ≤ ⌊H log Q⌋`);
* `ramI_nonempty_of_not_blockSmallG` — the **free** pin: `¬ BlockSmallG` *by itself* forces
  `I` nonempty, so every `t ∈ 𝒰G` certifies non-degeneracy at `J`.  The counting stones
  below carry `2 ≤ Hseq Jb` (hence `0 < H_Jb`), `3 ≤ Pseq Jb` and `Pseq Jb ≤ Qseq Jb`
  in-statement, so no rung of this file can be read vacuously.

`G0`'s second note stands: at `v = 0` the graded threshold is `e^0 = 1` (the toothless
small-prime end).  That costs nothing here — `V_0 = 1` is a legal Lemma-8 level.

## The sign convention (CATCH #B), byte-checked

`USetThinTL.ramQ_large_count` negates the ordinate set **internally** (it builds
`𝒮.image (fun t => -t)` and hands *that* to `large_value_count`, whose `dpoly` is
`P(1−it)`); its own statement quantifies `‖ramQ H P Q v c t‖` over `t ∈ 𝒮` with
`𝒮 ⊆ [−T,T]` — the same `t`, no flip.  `BlockSmallG` (G0) is likewise stated in the `+it`
convention with no flip.  **Therefore this file performs NO negation anywhere**: every `t`
is the ordinate the seam row integrates over, and `𝒯 ⊆ [−T,T]` is stated once.  (This is
exactly how the flat `Uset_thin` composes with `largeblock_count`.)

## The stones

* **T-1** `not_blockSmallG_witness` / `not_blockSmallG_witness_of_mem_UsetG` — the `∃ v`
  extraction, plus `ramI_nonempty`, `ramI_nonempty_of_not_blockSmallG`, and the two block
  geometry pins `ramI_div_le_log`, `ramQbase_le_of_mem_ramI`.
* **T-2** `ramQ_graded_count` (the per-block count at the graded level, with the three
  uniformisations) and `usetG_thin` / `usetG_thin_Q` (the union over `I_J`).
* **T-3** `gradeV_sq_le_rpow` (`Q_J^{2α_J} ≤ X^ε` — the `X^{o(1)}` form) and
  `usetG_thin_pin`, the §8.3 pin corollary.

**Law #253.**  Every growing-quantity gate rides the statement and is never absorbed:
`1 < T`, `3 ≤ P_Jb`, `P_Jb ≤ Q_Jb`, `Q_Jb ≤ T`, `30 ≤ log T/log Q_Jb` (the X₀ law),
`5 ≤ loglog T`, `2 ≤ H_Jb`, `0 ≤ α_Jb`; at the pin additionally `1 < X`, `0 < ε`,
`e ≤ log X`, `2/ε ≤ loglog X`, `α_Jb ≤ 1`, `H_Jb = H₈₃`, `Q_Jb ≤ Q₈₃`.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), §8.3 p.29; MRT v3 App. A.
-/

namespace Salt.MR

/-! ## §1 — T-1: the witness and the NON-DEGENERACY pins -/

/-- **The geometric non-degeneracy pin.**  `ramI H P Q = Icc ⌊H log P⌋ ⌊H log Q⌋` is
nonempty as soon as `0 ≤ H`, `1 ≤ P` and `P ≤ Q`.  Without it `BlockSmallG` is a bounded
`∀` over `∅` and the whole graded partition degenerates (the `G0` empty-block trap). -/
lemma ramI_nonempty {H : ℝ} (hH : 0 ≤ H) {P Q : ℕ} (hP1 : 1 ≤ P) (hPQ : P ≤ Q) :
    (ramI H P Q).Nonempty := by
  refine ⟨⌊H * Real.log (P : ℝ)⌋₊, ?_⟩
  rw [ramI, Finset.mem_Icc]
  refine ⟨le_rfl, Nat.floor_le_floor ?_⟩
  have hP0 : 0 < P := hP1
  have hP0R : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hlog : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log hP0R (by exact_mod_cast hPQ)
  exact mul_le_mul_of_nonneg_left hlog hH

/-- **The block height is below `log Q`.**  For `v ∈ ramI H P Q` (so `v ≤ ⌊H log Q⌋`) the
block's own height `v/H` is at most `log Q`.  This is the single geometric fact behind both
`ramQbase_le_of_mem_ramI` and the `V_v ≤ Q^{α}` level bound. -/
lemma ramI_div_le_log {H : ℝ} (hH : 0 < H) {P Q v : ℕ} (hQ1 : 1 ≤ Q)
    (hv : v ∈ ramI H P Q) : (v : ℝ) / H ≤ Real.log (Q : ℝ) := by
  have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hlogQ0 : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1R
  have hvle : v ≤ ⌊H * Real.log (Q : ℝ)⌋₊ := by
    rw [ramI, Finset.mem_Icc] at hv
    exact hv.2
  have hvR : (v : ℝ) ≤ H * Real.log (Q : ℝ) := by
    refine le_trans ?_ (Nat.floor_le (mul_nonneg hH.le hlogQ0))
    exact_mod_cast hvle
  rw [div_le_iff₀ hH]
  linarith

/-- **The block's dyadic base stays inside the window.**  `ramQbase H P v = max P ⌈e^{v/H}⌉`
is at most `Q` for every block index `v ∈ ramI H P Q`.  Consequence: the window gates
`Q ≤ T` and `30 ≤ log T/log Q` transfer to the base, uniformly in `v`. -/
lemma ramQbase_le_of_mem_ramI {H : ℝ} (hH : 0 < H) {P Q v : ℕ} (hP1 : 1 ≤ P) (hPQ : P ≤ Q)
    (hv : v ∈ ramI H P Q) : ramQbase H P v ≤ Q := by
  have hQ1 : 1 ≤ Q := le_trans hP1 hPQ
  have hQ0 : 0 < Q := hQ1
  have hQ0R : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hdiv := ramI_div_le_log hH hQ1 hv
  have hexp : Real.exp ((v : ℝ) / H) ≤ (Q : ℝ) := by
    calc Real.exp ((v : ℝ) / H) ≤ Real.exp (Real.log (Q : ℝ)) := Real.exp_le_exp.mpr hdiv
      _ = (Q : ℝ) := Real.exp_log hQ0R
  rw [ramQbase]
  exact max_le hPQ (Nat.ceil_le.mpr hexp)

/-- **T-1 — the `∃ v` extraction.**  `¬ BlockSmallG f Pseq Qseq Hseq αseq j t` says exactly
that SOME block index `v ∈ I_j` violates MR (21) at `t`:

  `exp(−α_j·v/H_j) < ‖ramQ H_j P_j Q_j v f t‖`.

No sign flip: `t` is the same ordinate throughout (see the module header). -/
lemma not_blockSmallG_witness {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ} {j : ℕ}
    {t : ℝ} (h : ¬ BlockSmallG f Pseq Qseq Hseq αseq j t) :
    ∃ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
      Real.exp (-(αseq j) * (v : ℝ) / Hseq j)
        < ‖ramQ (Hseq j) (Pseq j) (Qseq j) v f t‖ := by
  rw [BlockSmallG] at h
  push Not at h
  exact h

/-- **The FREE non-degeneracy pin (the `G0` empty-block trap, discharged).**  `¬ BlockSmallG`
cannot hold over an empty block-index set, so every violating ordinate certifies
`ramI (Hseq j) (Pseq j) (Qseq j) ≠ ∅` by itself — no geometric hypothesis needed. -/
lemma ramI_nonempty_of_not_blockSmallG {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ}
    {j : ℕ} {t : ℝ} (h : ¬ BlockSmallG f Pseq Qseq Hseq αseq j t) :
    (ramI (Hseq j) (Pseq j) (Qseq j)).Nonempty := by
  obtain ⟨v, hv, -⟩ := not_blockSmallG_witness h
  exact ⟨v, hv⟩

/-- **T-1 at `𝒰G`.**  An ordinate of the graded `𝒰` violates (21) at EVERY level of
`[1,J]`; in particular at a chosen `Jb`, where it names a block index. -/
lemma not_blockSmallG_witness_of_mem_UsetG {f : ℕ → ℂ} {Pseq Qseq : ℕ → ℕ}
    {Hseq αseq : ℕ → ℝ} {J Jb : ℕ} {t : ℝ} (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (ht : t ∈ UsetG f Pseq Qseq Hseq αseq J) :
    ∃ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
        < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v f t‖ :=
  not_blockSmallG_witness (ht Jb hJb1 hJbJ)

/-! ## §2 — T-2: the per-block count at the graded level

`ramQ_large_count` (LANDED, `USetThinTL` :207) is fed at `V := exp(α·v/H)`, i.e. at the
block's own graded threshold, and its three `v`-dependent factors are made uniform:

* `T ^ (2 log V / log base) ≤ T ^ (2α)` — because `log V = α·(v/H) ≤ α·log base`, the
  base being at least `e^{v/H}`.  **This is the exact-`α` collapse; nothing is inflated.**
* `V ^ 2 ≤ VJ ^ 2` — at any uniform level bound `VJ` (supplied as `Q^{α}` below);
* `exp(2·(log T/log base)·loglog T) ≤ exp(2·(log T/log P)·loglog T)` — the base is at
  least `P`. -/

/-- **T-2a — Lemma 8 at the block's own graded threshold.**  A well-spaced `𝒮 ⊆ [−T,T]` on
which the block polynomial `Q_{v,H}(1+it)` EXCEEDS `exp(−α·v/H)` is counted with the
`T`-power exponent collapsed to `2α` and every `v`-dependence removed.  All Lemma-8 gates
are carried in-statement (law #253), transferred from the window `[P,Q]` to the block base
by `ramQbase_le_of_mem_ramI`. -/
theorem ramQ_graded_count {H α : ℝ} (hH : 2 ≤ H) (hα : 0 ≤ α) (P Q v : ℕ) (f : ℕ → ℂ)
    (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1) (T VJ : ℝ)
    (hP3 : 3 ≤ P) (hPQ : P ≤ Q) (hT : 1 < T) (hQT : (Q : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log (Q : ℝ)) (hLL5 : 5 ≤ Real.log (Real.log T))
    (hv : v ∈ ramI H P Q) (hVJ : Real.exp (α * (v : ℝ) / H) ≤ VJ)
    (𝒮 : Finset ℝ) (hws : WellSpaced 𝒮) (hsub : ∀ t ∈ 𝒮, t ∈ Set.Icc (-T) T)
    (hlb : ∀ t ∈ 𝒮, Real.exp (-α * (v : ℝ) / H) < ‖ramQ H P Q v f t‖) :
    (𝒮.card : ℝ)
      ≤ 840 * T ^ (2 * α) * VJ ^ 2
          * Real.exp (2 * (Real.log T / Real.log (P : ℝ)) * Real.log (Real.log T)) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hP1 : 1 ≤ P := by omega
  have hQ1 : 1 ≤ Q := le_trans hP1 hPQ
  -- the base and its window gates
  have hPB : P ≤ ramQbase H P v := by rw [ramQbase]; exact le_max_left _ _
  have hB3 : 3 ≤ ramQbase H P v := le_trans hP3 hPB
  have hBQ : ramQbase H P v ≤ Q := ramQbase_le_of_mem_ramI hH0 hP1 hPQ hv
  have hBT : ((ramQbase H P v : ℕ) : ℝ) ≤ T :=
    le_trans (by exact_mod_cast hBQ) hQT
  have hB3R : (3 : ℝ) ≤ ((ramQbase H P v : ℕ) : ℝ) := by exact_mod_cast hB3
  have hlogB : 0 < Real.log ((ramQbase H P v : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hP3R : (3 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP3
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hlogPB : Real.log (P : ℝ) ≤ Real.log ((ramQbase H P v : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hPB)
  have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hlogBQ : Real.log ((ramQbase H P v : ℕ) : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hBQ)
  have hlogT0 : (0 : ℝ) < Real.log T := Real.log_pos hT
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log T) := by linarith
  -- the graded level
  have hx0 : (0 : ℝ) ≤ α * (v : ℝ) / H :=
    div_nonneg (mul_nonneg hα (Nat.cast_nonneg v)) hH0.le
  have hV1 : (1 : ℝ) ≤ Real.exp (α * (v : ℝ) / H) := by
    have h := Real.exp_le_exp.mpr hx0
    rwa [Real.exp_zero] at h
  have hκ30B : 30 ≤ Real.log T / Real.log ((ramQbase H P v : ℕ) : ℝ) := by
    refine le_trans hκ30 ?_
    gcongr
  have hlb' : ∀ t ∈ 𝒮, (Real.exp (α * (v : ℝ) / H))⁻¹ ≤ ‖ramQ H P Q v f t‖ := by
    intro t ht
    have hneg : Real.exp (-α * (v : ℝ) / H) = (Real.exp (α * (v : ℝ) / H))⁻¹ := by
      rw [show -α * (v : ℝ) / H = -(α * (v : ℝ) / H) by ring, Real.exp_neg]
    rw [← hneg]
    exact (hlb t ht).le
  have hcount := ramQ_large_count hH P Q v f hf1 T (Real.exp (α * (v : ℝ) / H))
    hB3 hT hBT hV1 hκ30B hLL5 𝒮 hws hsub hlb'
  -- (i) the EXACT-α collapse of the `T`-power leg
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
  have h1 : T ^ (2 * Real.log (Real.exp (α * (v : ℝ) / H))
      / Real.log ((ramQbase H P v : ℕ) : ℝ)) ≤ T ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_le hT.le hexpo
  -- (ii) the uniform level
  have h2 : Real.exp (α * (v : ℝ) / H) ^ 2 ≤ VJ ^ 2 := by
    have h0 : (0 : ℝ) ≤ Real.exp (α * (v : ℝ) / H) := (Real.exp_pos _).le
    nlinarith [hVJ, h0, hV1]
  -- (iii) the base-`P` floor in the `exp` leg
  have h3 : Real.exp (2 * (Real.log T / Real.log ((ramQbase H P v : ℕ) : ℝ))
        * Real.log (Real.log T))
      ≤ Real.exp (2 * (Real.log T / Real.log (P : ℝ)) * Real.log (Real.log T)) := by
    refine Real.exp_le_exp.mpr ?_
    have hd : Real.log T / Real.log ((ramQbase H P v : ℕ) : ℝ)
        ≤ Real.log T / Real.log (P : ℝ) := by gcongr
    nlinarith [hd, hLL0]
  -- the product
  have hTpow0 : (0 : ℝ) ≤ T ^ (2 * α) :=
    (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < T) _).le
  refine le_trans hcount ?_
  have step1 : (840 : ℝ) * T ^ (2 * Real.log (Real.exp (α * (v : ℝ) / H))
      / Real.log ((ramQbase H P v : ℕ) : ℝ)) ≤ 840 * T ^ (2 * α) := by linarith
  have step2 : (840 : ℝ) * T ^ (2 * Real.log (Real.exp (α * (v : ℝ) / H))
        / Real.log ((ramQbase H P v : ℕ) : ℝ)) * Real.exp (α * (v : ℝ) / H) ^ 2
      ≤ 840 * T ^ (2 * α) * VJ ^ 2 :=
    mul_le_mul step1 h2 (sq_nonneg _) (mul_nonneg (by norm_num) hTpow0)
  exact mul_le_mul step2 h3 (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg (by norm_num) hTpow0) (sq_nonneg _))

/-- **T-2 — THE GRADED THINNESS (`usetG_thin`).**  A well-spaced `𝒯 ⊆ [−T,T]` contained in
the graded `𝒰` is thin: each of its ordinates violates MR (21) at some block index
`v ∈ I_Jb`, so `𝒯` is covered by the `|I_Jb|` per-block large-value sets, each counted by
`ramQ_graded_count` at the *same* uniform bound.  Hence

  `|𝒯| ≤ |I_Jb| · 840 · T^{2α_Jb} · VJ² · exp(2·(log T/log P_Jb)·loglog T)`.

`VJ` is any uniform bound on the graded levels `exp(α_Jb·v/H_Jb)`, `v ∈ I_Jb`; the concrete
`VJ = Q_Jb^{α_Jb}` is supplied by `usetG_thin_Q`.  Compare `USetThin.Uset_thin` :642 — same
exit shape, with `dyadicPairs` replaced by MR's own `ramI` and the `K₀` pigeonhole gone.

**Non-degeneracy** (the `G0` empty-block trap) is pinned by `2 ≤ Hseq Jb`, `3 ≤ Pseq Jb`,
`Pseq Jb ≤ Qseq Jb`; `ramI_nonempty` then gives `I_Jb ≠ ∅`, and `1 ≤ Jb ≤ J` keeps the
`UsetG` hypothesis engaged. -/
theorem usetG_thin (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T VJ : ℝ) (hT : 1 < T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (hVJ : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ)
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ UsetG f Pseq Qseq Hseq αseq J) :
    (𝒯.card : ℝ)
      ≤ ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ)
        * (840 * T ^ (2 * αseq Jb) * VJ ^ 2
            * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
                * Real.log (Real.log T))) := by
  classical
  set B : ℝ := 840 * T ^ (2 * αseq Jb) * VJ ^ 2
      * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
          * Real.log (Real.log T)) with hBdef
  -- (i) every candidate block's count set is Lemma-8 bounded, uniformly
  have hpiece : ∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
      (((𝒯.filter (fun t => Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
          < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v f t‖)).card : ℝ)) ≤ B := by
    intro v hv
    exact ramQ_graded_count hH2 hα0 (Pseq Jb) (Qseq Jb) v f hf1 T VJ hP3 hPQ hT hQT
      hκ30 hLL5 hv (hVJ v hv) _
      (wellSpaced_of_subset (Finset.filter_subset _ _) hws)
      (fun t ht => hsub t (Finset.mem_filter.mp ht).1)
      (fun t ht => (Finset.mem_filter.mp ht).2)
  -- (ii) the count sets cover `𝒯` (T-1: each `t` names its own violating block)
  have hcover : 𝒯 ⊆ (ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).biUnion
      (fun v => 𝒯.filter (fun t => Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
        < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v f t‖)) := by
    intro t ht
    obtain ⟨v, hv, hbig⟩ :=
      not_blockSmallG_witness_of_mem_UsetG hJb1 hJbJ (hU t ht)
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨ht, hbig⟩⟩
  -- (iii) the union bound over `I_Jb`
  calc (𝒯.card : ℝ)
      ≤ (((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).biUnion
          (fun v => 𝒯.filter (fun t => Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
            < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v f t‖))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          ((𝒯.filter (fun t => Real.exp (-(αseq Jb) * (v : ℝ) / Hseq Jb)
            < ‖ramQ (Hseq Jb) (Pseq Jb) (Qseq Jb) v f t‖)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb), B := Finset.sum_le_sum hpiece
    _ = ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **T-2′ — the graded thinness at the concrete level `VJ = Q_Jb^{α_Jb}`.**  The uniform
level bound is free: `v ∈ I_Jb` forces `v/H_Jb ≤ log Q_Jb`, hence
`exp(α_Jb·v/H_Jb) ≤ Q_Jb^{α_Jb}`.  This is the `V² ≤ Q_J^{2α_J}` of ⟦V6⟧'s G1a bullet. -/
theorem usetG_thin_Q (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (hH2 : 2 ≤ Hseq Jb) (hα0 : 0 ≤ αseq Jb)
    (T : ℝ) (hT : 1 < T)
    (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ UsetG f Pseq Qseq Hseq αseq J) :
    (𝒯.card : ℝ)
      ≤ ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ)
        * (840 * T ^ (2 * αseq Jb) * (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2
            * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
                * Real.log (Real.log T))) := by
  have hH0 : (0 : ℝ) < Hseq Jb := by linarith
  have hP1 : 1 ≤ Pseq Jb := by omega
  have hQ1 : 1 ≤ Qseq Jb := le_trans hP1 hPQ
  have hQ0R : (0 : ℝ) < ((Qseq Jb : ℕ) : ℝ) := by exact_mod_cast hQ1
  refine usetG_thin f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T _ hT hP3 hPQ hQT
    hκ30 hLL5 ?_ 𝒯 hws hsub hU
  intro v hv
  have hdiv := ramI_div_le_log hH0 hQ1 hv
  have hle : αseq Jb * (v : ℝ) / Hseq Jb ≤ Real.log ((Qseq Jb : ℕ) : ℝ) * αseq Jb := by
    rw [show αseq Jb * (v : ℝ) / Hseq Jb = αseq Jb * ((v : ℝ) / Hseq Jb) by ring]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hα0]
  calc Real.exp (αseq Jb * (v : ℝ) / Hseq Jb)
      ≤ Real.exp (Real.log ((Qseq Jb : ℕ) : ℝ) * αseq Jb) := Real.exp_le_exp.mpr hle
    _ = ((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb) := (Real.rpow_def_of_pos hQ0R _).symm

/-! ## §3 — T-3: the §8.3 pin corollary -/

/-- **T-3a — the level is `X^{o(1)}` at the pin.**  `V_J² = Q_J^{2α_J} ≤ X^ε` whenever
`Q_J ≤ Q₈₃ X = exp(log X/loglog X)`, `α_J ≤ 1` and `loglog X ≥ 2/ε`.  The gate
`2/ε ≤ loglog X` is the honest, growing-quantity form (law #253): `ε` is free, and the
threshold it imposes on `X` is the consumer's to inherit — nothing is absorbed. -/
lemma gradeV_sq_le_rpow {X ε α : ℝ} {Q : ℕ} (hX1 : 1 < X) (hQ0 : 0 < Q)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hQpin : ((Q : ℕ) : ℝ) ≤ Q83 X) (hLL : 2 / ε ≤ Real.log (Real.log X)) :
    (((Q : ℕ) : ℝ) ^ α) ^ 2 ≤ X ^ ε := by
  have hQ0R : (0 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast hQ0
  have hX0 : (0 : ℝ) < X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos hX1
  have hLL0 : 0 < Real.log (Real.log X) := lt_of_lt_of_le (div_pos (by norm_num) hε) hLL
  have hsq : (((Q : ℕ) : ℝ) ^ α) ^ 2 = ((Q : ℕ) : ℝ) ^ (2 * α) := by
    rw [show (2 : ℝ) * α = α + α by ring, Real.rpow_add hQ0R, sq]
  have hkey : 2 * α ≤ ε * Real.log (Real.log X) := by
    rw [div_le_iff₀ hε] at hLL
    linarith
  have hexp : Real.log X / Real.log (Real.log X) * (2 * α) ≤ Real.log X * ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hLL0]
    have h := mul_le_mul_of_nonneg_left hkey hLX.le
    nlinarith [h]
  have hstep : (Q83 X) ^ (2 * α)
      = Real.exp (Real.log X / Real.log (Real.log X) * (2 * α)) := by
    rw [Q83, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [hsq]
  calc ((Q : ℕ) : ℝ) ^ (2 * α)
      ≤ (Q83 X) ^ (2 * α) := Real.rpow_le_rpow hQ0R.le hQpin (by linarith)
    _ = Real.exp (Real.log X / Real.log (Real.log X) * (2 * α)) := hstep
    _ ≤ Real.exp (Real.log X * ε) := Real.exp_le_exp.mpr hexp
    _ = X ^ ε := (Real.rpow_def_of_pos hX0 ε).symm

/-- **T-3 — THE GRADED THINNESS AT THE §8.3 PINS (`usetG_thin_pin`).**  With
`H_Jb = H₈₃ X θ₂₉₃ = (log X)^{θ}` and `Q_Jb ≤ Q₈₃ X`, the block count is priced by
`USetPrice.ramI_card_le_pin` and the graded level is `X^{o(1)}` by `gradeV_sq_le_rpow`:

  `|𝒯| ≤ 2(log X)^{1+θ₂₉₃} · 840 · T^{2α_Jb} · X^ε · exp(2·(log T/log P_Jb)·loglog T)`.

Every gate rides the statement (law #253): the `X₀` law `30 ≤ log T/log Q_Jb`, `5 ≤ loglog T`,
`e ≤ log X`, `2/ε ≤ loglog X` (the `X^{o(1)}` threshold), `α_Jb ≤ 1` (the honest α gate — no
inflation, cf. ⟦V4a⟧), and the non-degeneracy pins `2 ≤ H_Jb`, `3 ≤ P_Jb ≤ Q_Jb`. -/
theorem usetG_thin_pin (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ)
    (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J)
    (X ε T : ℝ) (hX1 : 1 < X) (hε : 0 < ε)
    (hLe : Real.exp 1 ≤ Real.log X) (hLL : 2 / ε ≤ Real.log (Real.log X))
    (hHpin : Hseq Jb = H83 X theta293) (hH2 : 2 ≤ Hseq Jb)
    (hα0 : 0 ≤ αseq Jb) (hα1 : αseq Jb ≤ 1)
    (hT : 1 < T) (hP3 : 3 ≤ Pseq Jb) (hPQ : Pseq Jb ≤ Qseq Jb)
    (hQpin : ((Qseq Jb : ℕ) : ℝ) ≤ Q83 X) (hQT : ((Qseq Jb : ℕ) : ℝ) ≤ T)
    (hκ30 : 30 ≤ Real.log T / Real.log ((Qseq Jb : ℕ) : ℝ))
    (hLL5 : 5 ≤ Real.log (Real.log T))
    (𝒯 : Finset ℝ) (hws : WellSpaced 𝒯) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T)
    (hU : ∀ t ∈ 𝒯, t ∈ UsetG f Pseq Qseq Hseq αseq J) :
    (𝒯.card : ℝ)
      ≤ 2 * (Real.log X) ^ (1 + theta293)
        * (840 * T ^ (2 * αseq Jb) * X ^ ε
            * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
                * Real.log (Real.log T))) := by
  have hP1 : 1 ≤ Pseq Jb := by omega
  have hQ0 : 0 < Qseq Jb := lt_of_lt_of_le hP1 hPQ
  have hTpow0 : (0 : ℝ) ≤ T ^ (2 * αseq Jb) :=
    (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < T) _).le
  have hraw := usetG_thin_Q f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2 hα0 T hT hP3 hPQ
    hQT hκ30 hLL5 𝒯 hws hsub hU
  -- the block count at the pin
  have hcard : ((ramI (Hseq Jb) (Pseq Jb) (Qseq Jb)).card : ℝ)
      ≤ 2 * (Real.log X) ^ (1 + theta293) := by
    rw [hHpin]
    exact ramI_card_le_pin X (Pseq Jb) (Qseq Jb) hQ0 hQpin hLe
  -- the graded level at the pin
  have hlev : (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2 ≤ X ^ ε :=
    gradeV_sq_le_rpow hX1 hQ0 hα0 hα1 hε hQpin hLL
  refine le_trans hraw ?_
  have hinner : 840 * T ^ (2 * αseq Jb) * (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2
        * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ)) * Real.log (Real.log T))
      ≤ 840 * T ^ (2 * αseq Jb) * X ^ ε
        * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
            * Real.log (Real.log T)) := by
    have hnn : (0 : ℝ) ≤ 840 * T ^ (2 * αseq Jb) := mul_nonneg (by norm_num) hTpow0
    have h1 : 840 * T ^ (2 * αseq Jb) * (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2
        ≤ 840 * T ^ (2 * αseq Jb) * X ^ ε := mul_le_mul_of_nonneg_left hlev hnn
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hinner0 : (0 : ℝ) ≤ 840 * T ^ (2 * αseq Jb)
      * (((Qseq Jb : ℕ) : ℝ) ^ (αseq Jb)) ^ 2
      * Real.exp (2 * (Real.log T / Real.log ((Pseq Jb : ℕ) : ℝ))
          * Real.log (Real.log T)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hTpow0) (sq_nonneg _))
      (Real.exp_pos _).le
  have hLX0 : (0 : ℝ) < Real.log X := by
    have he1 : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    linarith
  have hcard0 : (0 : ℝ) ≤ 2 * (Real.log X) ^ (1 + theta293) := by
    have := Real.rpow_nonneg hLX0.le (1 + theta293)
    linarith
  exact mul_le_mul hcard hinner hinner0 hcard0

end Salt.MR
