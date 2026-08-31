/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTPropA3

/-!
# MRT Theorem A.2 — the statement, filling the empty slot in `A.3 ⇒ A.2 ⇒ A.1`

**Statement text VERBATIM from the Captain-ratified draft 2** (`seat 3abef515`; drafts 1+2
ratified as drafted, all five questions).  **The statement act is the Captain's.**  Nothing in
this file adjusts the ratified text — iron rule 1.

⛔ **WHY A NEW FILE, AND WHY NOT ANY `ThmA2*.lean`.**  `Salt/MR/ThmA2.lean`,
`ThmA2Spine.lean` and `ThmA2Open.lean` are the **S8 `thm_A2′` ladder** — an unrelated object.
This campaign has already lost a day to two different "Prop 2.4", and `ThmA2*` was the seventh
name collision of the 08/26 night.  `MRTThmA2Stmt.lean` avoids the eighth.

📌 **The slot was EMPTY, not merely unproved.**  `MRTPropA3.lean`'s own 08/25 erratum records
that the object once called `MRTThmA2` was renamed `MRTThmA1GJ` because it is A.1's bound for the
`g_𝒥`-restricted datum, not A.2 — *"the `A.2` slot in the spine `A.3 ⇒ A.2 ⇒ A.1` is still
empty"*.  This file fills it.  **Nothing here is proved: `MRTThmA2` is a `Prop`, nothing produces
it and nothing assumes it.**
-/

namespace Salt.MR

open MeasureTheory

/-- **MRT Theorem A.2 at an explicit constant `C` and threshold `Xthr`** (`arXiv:1503.05121v3`
p. 21). The `≪` is one absolute `C` (house pattern of `MRTPropA3`); the source's
"for all `X > X(η)`" is carried as an explicit threshold function `Xthr : ℝ → ℝ` applied
at `η` — see ratification Q3 for the alternative. Band family, count, and sifted set
follow `MRTPropA3` verbatim (`MRTBands`, `MRTBandCount`, the `S`-characterization), so
the A.3 ⇒ A.2 bridge meets no vocabulary seam. The sifted short mean reuses
`mrtShortMean` (closed window, MRT's own `x ≤ n ≤ x + h`); the landed Parseval join's
half-open `shortSum` differs by at most one term, priced at `1/h`
(`closed_open_window_card_le_one`). -/
def MRTThmA2 (C : ℝ) (Xthr : ℝ → ℝ) : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
  ∀ (X X₀ h η : ℝ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (S : Finset ℕ),
    0 < η → η < 1 / 6 →
    3 ≤ h → (Qseq 1 : ℝ) ≤ h →
    Xthr η < X → h ≤ X →
    Real.sqrt X ≤ X₀ → X₀ ≤ X →
    MRTBands X₀ η Pseq Qseq → MRTBandCount X₀ Qseq J →
    (∀ n : ℕ, n ∈ S ↔ (X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 4 * X ∧ MemS Pseq Qseq J n)) →
    1 / X * (∫ x in X..(2 * X),
        ‖mrtShortMean (fun n => f n * (if n ∈ S then 1 else 0)) h x‖ ^ 2)
      ≤ C * (Real.exp (-(mrtM f X)) * mrtM f X
            + (Real.log h) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
            + 1 / (Real.log X) ^ ((1 : ℝ) / 50))

/-- **The producer as a Prop**: some absolute `C > 0` and some threshold work. -/
def MRTThmA2Statement : Prop := ∃ C : ℝ, 0 < C ∧ ∃ Xthr : ℝ → ℝ, MRTThmA2 C Xthr

/-- **A.2 at the θ=3/4 lane's tail rate (E34 V3)** — byte-identical to `MRTThmA2` except
the tail term `1/(log X)^{1/50} ↦ 1/(log X)^{1/70}`.  Statement act under the helm's word
in the E34 ladder-repair commission's fold (2026-08-31, in the private record); the old
name stays byte-untouched and citable. -/
def MRTThmA2_34 (C : ℝ) (Xthr : ℝ → ℝ) : Prop :=
  ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) → f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
  ∀ (X X₀ h η : ℝ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) (S : Finset ℕ),
    0 < η → η < 1 / 6 →
    3 ≤ h → (Qseq 1 : ℝ) ≤ h →
    Xthr η < X → h ≤ X →
    Real.sqrt X ≤ X₀ → X₀ ≤ X →
    MRTBands X₀ η Pseq Qseq → MRTBandCount X₀ Qseq J →
    (∀ n : ℕ, n ∈ S ↔ (X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 4 * X ∧ MemS Pseq Qseq J n)) →
    1 / X * (∫ x in X..(2 * X),
        ‖mrtShortMean (fun n => f n * (if n ∈ S then 1 else 0)) h x‖ ^ 2)
      ≤ C * (Real.exp (-(mrtM f X)) * mrtM f X
            + (Real.log h) ^ ((1 : ℝ) / 3) / (Pseq 1 : ℝ) ^ ((1 : ℝ) / 6 - η)
            + 1 / (Real.log X) ^ ((1 : ℝ) / 70))

end Salt.MR
