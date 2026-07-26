/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.USetThinTS
import Salt.MR.SeamSplit

/-!
# RamRAdapter — the `ramR = spoly` adapter and the Abel bridge (U-7 stone A)

The `⟦V5⟧` ladder's **U7-A** lane (`docs/exploration/hsup-design.md`): wire the Ramaré
co-factor `R_{j,H}(1+it)` (`RamareWindows.ramR`) into the landed unconditional Abel
inequality `SeamSplit.spoly_abel_sup`, so that a *linear* bound on the twisted partial sums
of the co-factor's own coefficients becomes a **pointwise** bound `‖ramR‖ ≤ 3S` — the shape
`USetThinTL.tL_main_sumsq` consumes as its `Rbd` hypothesis.

## What is here (and what is NOT — the no-duplication law)

* **A-1 is discharged UPSTREAM.**  `USetThinTS.ramRcoeff` (`:80`) already IS the explicit
  coefficient `a_R m = 1_{ramRrange}(m) · b m · (ω(m;P,Q)+1)⁻¹`, and
  `USetThinTS.ramR_eq_spoly` (`:95`) already IS the adapter
  `ramR H N X P Q j b t = spoly M (ramRcoeff H N X P Q j b) t` for any `M` with
  `ramRrange H N X j ⊆ Finset.Icc 1 M`.  Both are imported and reused verbatim; nothing
  here restates them.  What §1 adds is the **sharp-`M`** subset (`⟦V4a⟧`'s law: `M ≍ 2X'`,
  not the dyadic `N`) — `ramRrange_subset_Icc_sharp` — which the `𝒯_S` twin
  (`ramRrange_subset_Icc`, `⊆ Icc 1 N`) does not give.

* **A-3, THE HALF-OPEN ENDPOINT PAGE**, is the real content (§3).  `spoly_abel_sup` wants a
  dyadic *window* `X₀ < support ≤ N ≤ 2X₀` with the support hypothesis stated as
  `n ≤ X₀ → aₙ = 0` — i.e. the window is **open at the bottom**.  `ramRrange` is **closed at
  both ends** (`X' ≤ m ≤ 2X'`, `RamareWindows.lean:64`).  The two conventions do not fit:
  any strict lowering of the cut to `X₀ < X'` (needed for the support hypothesis) forces
  `2X₀ < 2X'`, so the Abel length `M` can no longer reach the top of the co-factor range.
  The gap is **at most two integers** — `⌊2X'⌋₊ − 1` and `⌊2X'⌋₊` — and they are peeled off
  and priced by the trivial per-term bound `‖a_R m/m^{1+it}‖ ≤ 1/m ≤ 1/X'` instead
  (`ramR_split_top`, `ramRtop_card_le_two`, `norm_ramRtop_le`).  Total endpoint charge
  `2/X'`.  This is where the `3S` (rather than `2S`) comes from: `2S` from Abel, `+ S` from
  the two endpoint terms once the consumer supplies `2/X' ≤ S`.

* **A-4** (§2): `norm_ramRcoeff_le_one` / `norm_ramRcoeff_cterm_le`.  **The normalization
  answer:** `ramR` carries the `1/m` *internally* (it is a `σ = 1` polynomial —
  `b m / m^{1+it}`), so the *coefficient* `a_R` is `1`-bounded and the *term* is
  `1/m`-bounded.  No `1/n` is expected from the consumer.

* **A-2** (§4): `ramR_abel_sup`, the composed form, and `ramR_abel_window_floor`, the
  concrete discharge of §3's window gates at `M := ⌊2X'⌋₊ − 2`.

## THE `t`-CONVENTION (stated explicitly — catch #B)

Everything in this file lives in the **`spoly`/`spolyA` convention at the SAME `t`** that
`ramR` is evaluated at:

* `ramR H N X P Q j b t = Σ_m a_R(m) · m^{−1−it}` (`RamareWindows.lean:73`), and
* `spolyA a t m = Σ_{n≤m} a n / n^{it} = Σ_{n≤m} a n · n^{−it}` (`SeamSplit.lean:198`).

So the partial-sum binder `hA` is over the **`n^{−it}`** twist — the *unnegated* `t`.  The
`−𝒯` sign bridge (`spoly_eq_dpoly : spoly N a t = dpoly N (aₙ/n) (−t)`) is **NOT used and
NOT re-armed anywhere in this file**: no `dpoly`, no `Finset.image (−·)`, no ordinate-set
negation appears.  A consumer that wires this row to a `dpoly`-side supply (Lemma 9,
`USetThinTS.ramR_sq_sum_le`) must apply `spoly_eq_dpoly` itself and negate there — the two
bridges do NOT compose silently.

Source pins (D5): MR arXiv v4 (`1501.04585v4`) p.19 (the `Q_{j,H}·R_{j,H}` block split);
`docs/exploration/hsup-design.md` ⟦V4a⟧ (the sharp-`M` law) and ⟦V5⟧ (the U7 ladder, lane
U7-A).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the co-factor window bottom and the sharp `M` -/

/-- **The co-factor window bottom** `X_j := X·e^{−j/H}`.  `ramRrange H N X j` is the closed
window `[X_j, 2X_j]` intersected with `[1,N]` (`RamareWindows.lean:64`). -/
noncomputable def ramRbot (H : ℝ) (X j : ℕ) : ℝ := (X : ℝ) * Real.exp (-(j : ℝ) / H)

lemma ramRbot_def (H : ℝ) (X j : ℕ) :
    ramRbot H X j = (X : ℝ) * Real.exp (-(j : ℝ) / H) := rfl

lemma ramRbot_nonneg (H : ℝ) (X j : ℕ) : 0 ≤ ramRbot H X j := by
  rw [ramRbot]; positivity

/-- The window is closed at the bottom: `m ∈ ramRrange → X_j ≤ m`. -/
lemma ramRrange_bot_le {H : ℝ} {N X j m : ℕ} (hm : m ∈ ramRrange H N X j) :
    ramRbot H X j ≤ (m : ℝ) := by
  rw [ramRrange, Finset.mem_filter] at hm
  exact hm.2.1

/-- The window is closed at the top: `m ∈ ramRrange → m ≤ 2X_j`. -/
lemma ramRrange_le_top {H : ℝ} {N X j m : ℕ} (hm : m ∈ ramRrange H N X j) :
    (m : ℝ) ≤ 2 * ramRbot H X j := by
  rw [ramRrange, Finset.mem_filter] at hm
  have h := hm.2.2
  rw [ramRbot]
  linarith

lemma ramRrange_one_le {H : ℝ} {N X j m : ℕ} (hm : m ∈ ramRrange H N X j) : 1 ≤ m := by
  rw [ramRrange, Finset.mem_filter, Finset.mem_Icc] at hm
  exact hm.1.1

/-- Anything strictly below the window bottom is out of range — the support half of the
half-open endpoint page. -/
lemma notMem_ramRrange_of_lt {H : ℝ} {N X j m : ℕ} (h : (m : ℝ) < ramRbot H X j) :
    m ∉ ramRrange H N X j :=
  fun hm => absurd (ramRrange_bot_le hm) (not_le.mpr h)

/-- **The sharp-`M` subset (`⟦V4a⟧`).**  Any `M ≥ 2X_j` contains the co-factor range.  This
is the `M ≍ 2X e^{−j/H}` of the sharp-`M` law — the `𝒯_S` twin `ramRrange_subset_Icc` only
gives the dyadic `N ≍ 2X`, which throws away the `e^{j/H}`. -/
lemma ramRrange_subset_Icc_sharp (H : ℝ) (N X j M : ℕ) (hM : 2 * ramRbot H X j ≤ (M : ℝ)) :
    ramRrange H N X j ⊆ Finset.Icc 1 M := by
  intro m hm
  refine Finset.mem_Icc.mpr ⟨ramRrange_one_le hm, ?_⟩
  exact_mod_cast le_trans (ramRrange_le_top hm) hM

/-! ## §2 — A-4: the coefficient and term bounds -/

/-- The Ramaré co-factor weight `(ω(m;P,Q)+1)⁻¹` has norm `≤ 1`. -/
lemma norm_blockOmega_inv_le_one (P Q m : ℕ) :
    ‖((blockOmega P Q m : ℂ) + 1)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have heq : ‖(blockOmega P Q m : ℂ) + 1‖ = (blockOmega P Q m : ℝ) + 1 := by
    rw [show ((blockOmega P Q m : ℂ) + 1) = ((blockOmega P Q m + 1 : ℕ) : ℂ) by
      push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [heq]
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (by positivity))

/-- **A-4, the coefficient bound.**  `‖a_R m‖ ≤ 1` for a `1`-bounded datum: the window
indicator is `0/1`, the datum is `1`-bounded, and the Ramaré weight `(ω+1)⁻¹` has norm
`≤ 1`.  There is no `1/m` here — `ramR` carries it internally (see `norm_ramRcoeff_cterm_le`). -/
lemma norm_ramRcoeff_le_one (H : ℝ) (N X P Q j : ℕ) {b : ℕ → ℂ} (hb : ∀ m, ‖b m‖ ≤ 1)
    (m : ℕ) : ‖ramRcoeff H N X P Q j b m‖ ≤ 1 := by
  classical
  rw [ramRcoeff]
  split_ifs with hmem
  · rw [norm_mul]
    have hw := norm_blockOmega_inv_le_one P Q m
    have hbm := hb m
    nlinarith [norm_nonneg (b m), norm_nonneg (((blockOmega P Q m : ℂ) + 1)⁻¹)]
  · rw [norm_zero]; norm_num

/-- **A-4, the term bound.**  `‖a_R m / m^{1+it}‖ ≤ 1/m` (`m ≥ 1`): the `σ = 1` normalization
puts the `1/m` inside `ramR`, so the consumer supplies no extra weight. -/
lemma norm_ramRcoeff_cterm_le (H : ℝ) (N X P Q j : ℕ) {b : ℕ → ℂ} (hb : ∀ m, ‖b m‖ ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ‖ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 / (m : ℝ) := by
  rw [norm_cterm_eq m hm _ t]
  exact div_le_div_of_nonneg_right (norm_ramRcoeff_le_one H N X P Q j hb m)
    (by exact_mod_cast Nat.zero_le m)

/-! ## §3 — A-3: THE HALF-OPEN ENDPOINT PAGE

`spoly_abel_sup` needs the coefficient support to sit *strictly above* its cut `X₀`
(`hsupp : n ≤ X₀ → aₙ = 0`) while the length obeys `X₀ ≤ M ≤ 2X₀`.  `ramRrange` is closed
at `X_j`, so the cut must go strictly below `X_j`, and then `2X₀ < 2X_j` no longer reaches
the top of the range.  At most **two** integers are lost; they are peeled and priced here. -/

/-- **The peel.**  `ramR = spoly M a_R + (the terms of the range above `M`)` — an identity,
for ANY `M`.  (`spoly M a_R` sees exactly `ramRrange ∩ [1,M]` because `a_R` vanishes off the
range.) -/
lemma ramR_split_top (H : ℝ) (N X P Q j M : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    ramR H N X P Q j b t
      = spoly M (ramRcoeff H N X P Q j b) t
        + ∑ m ∈ (ramRrange H N X j).filter (fun m => M < m),
            ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
  classical
  have hR : ramR H N X P Q j b t
      = ∑ m ∈ ramRrange H N X j,
          ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [ramR]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [ramRcoeff, if_pos hm, div_mul_eq_mul_div]
  have hspl := Finset.sum_filter_add_sum_filter_not (ramRrange H N X j) (fun m => M < m)
    (fun m => ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I))
  have hlo : spoly M (ramRcoeff H N X P Q j b) t
      = ∑ m ∈ (ramRrange H N X j).filter (fun m => ¬ M < m),
          ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [spoly]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro m hm
      rw [Finset.mem_filter] at hm
      have hm1 : 1 ≤ m := ramRrange_one_le hm.1
      have hm2 : m ≤ M := by omega
      exact Finset.mem_Icc.mpr ⟨hm1, hm2⟩
    · intro m hm hnot
      have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
      have hmr : m ∉ ramRrange H N X j := by
        intro hcon
        exact hnot (Finset.mem_filter.mpr ⟨hcon, by omega⟩)
      rw [ramRcoeff_of_notMem H N X P Q j b hmr, zero_div]
  rw [hR, hlo, ← hspl]
  ring

/-- **THE `+2` TERMS.**  If `M + 3` clears the top of the window (`2X_j < M + 3`) then the
peeled set is contained in `{M+1, M+2}` — at most two integers.  This is the exact size of
the `⌈⌉/⌊⌋` seam between the closed range `[X_j, 2X_j]` and Abel's open-at-the-bottom
dyadic window. -/
lemma ramRtop_card_le_two (H : ℝ) (N X j M : ℕ)
    (hMtop : 2 * ramRbot H X j < (M : ℝ) + 3) :
    ((ramRrange H N X j).filter (fun m => M < m)).card ≤ 2 := by
  classical
  have hsub : (ramRrange H N X j).filter (fun m => M < m) ⊆ Finset.Icc (M + 1) (M + 2) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have hup : (m : ℝ) < (M : ℝ) + 3 := lt_of_le_of_lt (ramRrange_le_top hm.1) hMtop
    have hm3 : m < M + 3 := by
      have : (m : ℝ) < ((M + 3 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  calc ((ramRrange H N X j).filter (fun m => M < m)).card
      ≤ (Finset.Icc (M + 1) (M + 2)).card := Finset.card_le_card hsub
    _ = 2 := by rw [Nat.card_Icc]; omega

/-- **The endpoint charge.**  The peeled terms cost at most `2/X_j`, by the trivial per-term
bound `‖a_R m / m^{1+it}‖ ≤ 1/m ≤ 1/X_j` (§2) times the `≤ 2` count. -/
lemma norm_ramRtop_le (H : ℝ) (N X P Q j M : ℕ) {b : ℕ → ℂ} (hb : ∀ m, ‖b m‖ ≤ 1)
    (hbot : 0 < ramRbot H X j) (hMtop : 2 * ramRbot H X j < (M : ℝ) + 3) (t : ℝ) :
    ‖∑ m ∈ (ramRrange H N X j).filter (fun m => M < m),
        ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 / ramRbot H X j := by
  classical
  set E := (ramRrange H N X j).filter (fun m => M < m) with hE
  have hcardR : (E.card : ℝ) ≤ 2 := by
    have := ramRtop_card_le_two H N X j M hMtop
    rw [hE]
    exact_mod_cast this
  have hterm : ∀ m ∈ E,
      ‖ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 1 / ramRbot H X j := by
    intro m hm
    have hmem : m ∈ ramRrange H N X j := (Finset.mem_filter.mp hm).1
    refine (norm_ramRcoeff_cterm_le H N X P Q j hb (ramRrange_one_le hmem) t).trans ?_
    exact one_div_le_one_div_of_le hbot (ramRrange_bot_le hmem)
  have hinv : (0 : ℝ) ≤ 1 / ramRbot H X j := by positivity
  calc ‖∑ m ∈ E, ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∑ m ∈ E, ‖ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
    _ ≤ E.card • (1 / ramRbot H X j) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (E.card : ℝ) * (1 / ramRbot H X j) := nsmul_eq_mul _ _
    _ ≤ 2 * (1 / ramRbot H X j) := mul_le_mul_of_nonneg_right hcardR hinv
    _ = 2 / ramRbot H X j := by ring

/-! ## §4 — A-2: the composed Abel consumption -/

/-- **A-2 — THE COMPOSED FORM the `U7-F` assembly consumes.**

From a *linear* bound on the co-factor's twisted partial sums,
`‖A_t(m)‖ = ‖Σ_{n≤m} a_R(n)·n^{−it}‖ ≤ S·m` for `m ≤ M`, conclude the pointwise
`‖R_{j,H}(1+it)‖ ≤ 3S`.

**The honest constant is `3`, and it splits as `2 + 1`:**
* `2S` is `spoly_abel_sup`'s absolute constant on the truncated length `M`
  (head `‖A_t(M)‖/M ≤ S`, tail `≤ S`);
* the extra `S` pays for the **half-open endpoint** (§3): the `≤ 2` integers of the closed
  window `[X_j, 2X_j]` that the open-at-the-bottom Abel window `(X_j−1, 2(X_j−1)]` cannot
  reach, priced trivially at `2/X_j` and absorbed by the gate `hend : 2/X_j ≤ S`.  That gate
  is free in the intended regime (`X_j ≍ X e^{−j/H}` is a power of `X`, `S ≍ (log X)^{−ρ}`).

The window gates `hlow`/`hhigh`/`hMtop` are dischargeable — see `ramR_abel_window_floor`,
which verifies them at `M := ⌊2X_j⌋₊ − 2` from `4 ≤ X_j` alone.

`t`-convention: the SAME `t` as `ramR`'s argument, twist `n^{−it}`; no `dpoly`, no
sign flip.  See the module docstring. -/
theorem ramR_abel_sup {H : ℝ} {N X P Q j M : ℕ} {b : ℕ → ℂ} {t S : ℝ}
    (hb : ∀ m, ‖b m‖ ≤ 1)
    (hbot : 1 < ramRbot H X j)
    (hlow : ramRbot H X j - 1 ≤ (M : ℝ))
    (hhigh : (M : ℝ) ≤ 2 * (ramRbot H X j - 1))
    (hMtop : 2 * ramRbot H X j < (M : ℝ) + 3)
    (hend : 2 / ramRbot H X j ≤ S)
    (hA : ∀ m : ℕ, m ≤ M → ‖spolyA (ramRcoeff H N X P Q j b) t m‖ ≤ S * m) :
    ‖ramR H N X P Q j b t‖ ≤ 3 * S := by
  classical
  have hX0 : (0 : ℝ) < ramRbot H X j - 1 := by linarith
  have hsupp : ∀ n : ℕ, (n : ℝ) ≤ ramRbot H X j - 1 → ramRcoeff H N X P Q j b n = 0 := by
    intro n hn
    exact ramRcoeff_of_notMem H N X P Q j b (notMem_ramRrange_of_lt (by linarith))
  have habel : ‖spoly M (ramRcoeff H N X P Q j b) t‖ ≤ 2 * S :=
    spoly_abel_sup hX0 hlow hhigh hsupp hA
  have htop := norm_ramRtop_le H N X P Q j M hb (by linarith) hMtop t
  calc ‖ramR H N X P Q j b t‖
      = ‖spoly M (ramRcoeff H N X P Q j b) t
          + ∑ m ∈ (ramRrange H N X j).filter (fun m => M < m),
              ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [ramR_split_top]
    _ ≤ ‖spoly M (ramRcoeff H N X P Q j b) t‖
          + ‖∑ m ∈ (ramRrange H N X j).filter (fun m => M < m),
              ramRcoeff H N X P Q j b m / (m : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ :=
        norm_add_le _ _
    _ ≤ 2 * S + 2 / ramRbot H X j := add_le_add habel htop
    _ ≤ 3 * S := by linarith

/-- **The window gates are dischargeable.**  At the concrete truncated length
`M := ⌊2X_j⌋₊ − 2`, the three §4 gates hold from `4 ≤ X_j` alone:

* `hlow  : X_j − 1 ≤ M`  (since `⌊2X_j⌋₊ > 2X_j − 1 ≥ X_j + 3`);
* `hhigh : M ≤ 2(X_j − 1)` (since `⌊2X_j⌋₊ ≤ 2X_j`);
* `hMtop : 2X_j < M + 3`  (since `⌊2X_j⌋₊ > 2X_j − 1`).

So the half-open corner costs exactly the two peeled terms, never more. -/
lemma ramR_abel_window_floor {W : ℝ} (hW : 4 ≤ W) :
    W - 1 ≤ ((⌊2 * W⌋₊ - 2 : ℕ) : ℝ)
      ∧ ((⌊2 * W⌋₊ - 2 : ℕ) : ℝ) ≤ 2 * (W - 1)
      ∧ 2 * W < ((⌊2 * W⌋₊ - 2 : ℕ) : ℝ) + 3 := by
  have hW0 : (0 : ℝ) ≤ 2 * W := by linarith
  have hfl : ((⌊2 * W⌋₊ : ℕ) : ℝ) ≤ 2 * W := Nat.floor_le hW0
  have hfu : 2 * W < ((⌊2 * W⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have h8 : (8 : ℕ) ≤ ⌊2 * W⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hcast : ((⌊2 * W⌋₊ - 2 : ℕ) : ℝ) = ((⌊2 * W⌋₊ : ℕ) : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast]
  refine ⟨by linarith, by linarith, by linarith⟩

end Salt.MR
