/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.MR.Sec9Glue
import Salt.MR.ChiEuler
import Salt.ExpSum.Basic

/-!
# MRT wave 1a — the typical-factorization set `S` and the statement of Proposition 2.4

Source, and the ONLY version this file is anchored to:
**Matomäki–Radziwiłł–Tao, "An averaged form of Chowla's conjecture",
`arXiv:1503.05121v3`** (`docs/sources/1503.05121v3.pdf`).  Definition 2.1 and
Lemma 2.2 are on p. 8; Theorem 2.3 on p. 9; **Proposition 2.4 on p. 10**.  The
`≪` of that paper is fixed on p. 7 (§1.3 Notation): `X ≪ Y` means `|X| ≤ C·Y`
for an **absolute** constant `C` — which is why the transcription below is a
`C`-parameterised `Prop` plus an `∃ C` wrapper, and not a bare inequality.

## What this file adds (E-1, E-2), and what it deliberately does NOT duplicate

* **E-1.** MRT Definition 2.1's band family `P_j, Q_j`, the cut-off index `J`,
  and the named set `S_{P₁,Q₁,X₀,X}`; plus Proposition 2.4's own instantiation
  `P₁ := W^200`, `Q₁ := H/W³`.
* **E-2.** The *statement* of Proposition 2.4 (`MRTProp24`), and MRT's quality
  quantities `M(g;X)` / `M(g;X,Q)` (p. 4, (1.6)) that its hypothesis (2.3) needs.
  **No proof is attempted and none is owed here** — `MRTProp24` is a `Prop`, not
  a theorem.

⭐ **THE J-FOLD INTERSECTION IS NOT NEW HERE.**  `Salt.MR.MemS`
(`Salt/MR/Sec9Glue.lean:118`) *already* carries it: `MemS Pseq Qseq J n` says
`n` has at least one prime factor in `[Pseq j, Qseq j]` for every `1 ≤ j ≤ J`,
written through `Decomp.blockOmega`.  MRT's Definition 2.1 and MR's §2 `S` are
the **same** membership condition; they differ only in *which* band sequence is
plugged in.  So `mrtS` below is `MemS` at MRT's Definition-2.1 sequence, and the
whole `gJ` / `lemma5` inclusion–exclusion apparatus (`Sec9Glue`, `Eq26Bridge`,
`M4Puncture`, `M4ParsevalStone`) applies to it verbatim.

⛔ **NAME TRAP, recorded so it is not walked into twice.**  `Salt/MR/SPartCore.lean`'s
`sPart F := F ⍟ ellLinInv F` is a smooth-part Dirichlet-convolution factorisation
from the S8 rescope freeze.  It is **not** MRT's `S` and has nothing to do with
this file.

## Band arithmetic: reals in, naturals out

MRT's `P_j, Q_j` are real quantities (`exp` of a real).  `MemS` takes `ℕ`-valued
endpoints, because `blockOmega` filters `n.primeFactors` by `P ≤ p ∧ p ≤ Q` with
`p : ℕ`.  The bridge is **exact, not a weakening**: for a natural `p`,
`P_j ≤ p ≤ Q_j` iff `⌈P_j⌉₊ ≤ p ≤ ⌊Q_j⌋₊` (`mem_mrtBand_nat`), since `Q_j > 0`.

## The `j = 1` check (why one formula, not a two-case definition)

MRT give `P₁, Q₁` as data and define `P_j, Q_j` by the displayed formula *for
`j > 1`*.  The formula is nevertheless **already correct at `j = 1`**:
`P₁' = exp(1^4·(log Q₁)^0·log P₁) = exp(log P₁) = P₁` and
`Q₁' = exp(1^6·(log Q₁)^1) = exp(log Q₁) = Q₁`.  That is *checked*, not assumed —
`mrtBandP_one` / `mrtBandQ_one` — so the uniform one-line definition is faithful.
-/

namespace Salt.MR

open Finset MeasureTheory

/-! ## §1 — E-1: MRT Definition 2.1 (p. 8) -/

/-- **MRT Definition 2.1's lower band endpoints** (`arXiv:1503.05121v3`, p. 8):
`P_j := exp(j^{4j} (log Q₁)^{j−1} log P₁)`.  Stated uniformly in `j`; the `j = 1`
instance recovers the given `P₁` (`mrtBandP_one`). -/
noncomputable def mrtBandP (P₁ Q₁ : ℝ) (j : ℕ) : ℝ :=
  Real.exp (((j ^ (4 * j) : ℕ) : ℝ) * Real.log Q₁ ^ (j - 1) * Real.log P₁)

/-- **MRT Definition 2.1's upper band endpoints** (p. 8):
`Q_j := exp(j^{4j+2} (log Q₁)^j)`.  The `j = 1` instance recovers the given `Q₁`
(`mrtBandQ_one`).  Unlike `mrtBandP`, this depends on `Q₁` alone — MRT's upper
formula carries no `P₁`, and the signature records that rather than hiding it
behind an unused argument. -/
noncomputable def mrtBandQ (Q₁ : ℝ) (j : ℕ) : ℝ :=
  Real.exp (((j ^ (4 * j + 2) : ℕ) : ℝ) * Real.log Q₁ ^ j)

@[simp] theorem mrtBandP_pos (P₁ Q₁ : ℝ) (j : ℕ) : 0 < mrtBandP P₁ Q₁ j :=
  Real.exp_pos _

@[simp] theorem mrtBandQ_pos (Q₁ : ℝ) (j : ℕ) : 0 < mrtBandQ Q₁ j :=
  Real.exp_pos _

/-- **Faithfulness at `j = 1` (lower endpoint).**  The uniform formula reproduces
MRT's *given* `P₁`, so no separate `j = 1` case is needed. -/
theorem mrtBandP_one {P₁ : ℝ} (Q₁ : ℝ) (hP : 0 < P₁) : mrtBandP P₁ Q₁ 1 = P₁ := by
  unfold mrtBandP
  norm_num
  exact Real.exp_log hP

/-- **Faithfulness at `j = 1` (upper endpoint).**  The uniform formula reproduces
MRT's *given* `Q₁`. -/
theorem mrtBandQ_one {Q₁ : ℝ} (hQ : 0 < Q₁) : mrtBandQ Q₁ 1 = Q₁ := by
  unfold mrtBandQ
  norm_num
  exact Real.exp_log hQ

/-- The `ℕ`-valued lower endpoint fed to `blockOmega`: `⌈P_j⌉₊`. -/
noncomputable def mrtBandPNat (P₁ Q₁ : ℝ) (j : ℕ) : ℕ := ⌈mrtBandP P₁ Q₁ j⌉₊

/-- The `ℕ`-valued upper endpoint fed to `blockOmega`: `⌊Q_j⌋₊`. -/
noncomputable def mrtBandQNat (Q₁ : ℝ) (j : ℕ) : ℕ := ⌊mrtBandQ Q₁ j⌋₊

/-- **The reals-to-naturals bridge is EXACT.**  For a natural `p`, the `ℕ`-band
condition `⌈P_j⌉₊ ≤ p ∧ p ≤ ⌊Q_j⌋₊` is *equivalent* to MRT's real condition
`P_j ≤ p ∧ p ≤ Q_j`.  Nothing is lost in passing to `MemS`. -/
theorem mem_mrtBand_nat (P₁ Q₁ : ℝ) (j p : ℕ) :
    (mrtBandPNat P₁ Q₁ j ≤ p ∧ p ≤ mrtBandQNat Q₁ j)
      ↔ (mrtBandP P₁ Q₁ j ≤ (p : ℝ) ∧ (p : ℝ) ≤ mrtBandQ Q₁ j) := by
  unfold mrtBandPNat mrtBandQNat
  rw [Nat.ceil_le, Nat.le_floor_iff (mrtBandQ_pos Q₁ j).le]

/-- **MRT Definition 2.1's cut-off index `J`** (p. 8): the largest index `j` with
`Q_j ≤ exp(√(log X₀))`.  Written as a supremum over `ℕ`, which under Definition
2.1's standing hypotheses (`Q₁ ≤ exp(√(log X₀))`, and `Q_j` increasing to
infinity) is attained and is exactly MRT's `J`.  The `sSup` carries no proof
obligation at the definition site — outside that regime it is `ℕ`'s junk value. -/
noncomputable def mrtJ (Q₁ X₀ : ℝ) : ℕ :=
  sSup {j : ℕ | mrtBandQ Q₁ j ≤ Real.exp (Real.sqrt (Real.log X₀))}

/-- **MRT's set `S_{P₁,Q₁,X₀,X}`** (Definition 2.1, p. 8): the integers
`1 ≤ n ≤ X` having at least one prime factor in `[P_j, Q_j]` for each
`1 ≤ j ≤ J`.  The `J`-fold intersection is `Salt.MR.MemS`, the corpus's own
membership predicate (`Sec9Glue.lean:118`), instantiated at Definition 2.1's
band sequence; `1 ≤ n ≤ X` is `Finset.Icc 1 ⌊X⌋₊`. -/
noncomputable def mrtS (P₁ Q₁ X₀ X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter
    (fun n => MemS (mrtBandPNat P₁ Q₁) (mrtBandQNat Q₁) (mrtJ Q₁ X₀) n)

/-- Membership in `S`, unfolded to MRT's own words: `1 ≤ n ≤ X`, and for each
`1 ≤ j ≤ J` at least one prime factor of `n` lies in the block `[P_j, Q_j]`. -/
theorem mem_mrtS {P₁ Q₁ X₀ X : ℝ} {n : ℕ} :
    n ∈ mrtS P₁ Q₁ X₀ X ↔
      (1 ≤ n ∧ n ≤ ⌊X⌋₊) ∧
        ∀ j ∈ Finset.Icc 1 (mrtJ Q₁ X₀),
          1 ≤ blockOmega (mrtBandPNat P₁ Q₁ j) (mrtBandQNat Q₁ j) n := by
  unfold mrtS MemS
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- `S ⊆ [1, ⌊X⌋₊]`. -/
theorem mrtS_subset_Icc (P₁ Q₁ X₀ X : ℝ) :
    mrtS P₁ Q₁ X₀ X ⊆ Finset.Icc 1 ⌊X⌋₊ :=
  Finset.filter_subset _ _

/-- `0 ∉ S` — the set lives on `1 ≤ n`, so the `n = 0` term of any window sum
below carries indicator `0`. -/
theorem zero_not_mem_mrtS (P₁ Q₁ X₀ X : ℝ) : 0 ∉ mrtS P₁ Q₁ X₀ X := by
  intro h
  exact absurd (mem_mrtS.mp h).1.1 (by omega)

/-! ## §2 — Proposition 2.4's instantiation of the two free band parameters -/

/-- **`P₁ := W^200`** (MRT Theorem 2.3 p. 9 and Proposition 2.4 p. 10). -/
noncomputable def mrtP1 (W : ℝ) : ℝ := W ^ (200 : ℕ)

/-- **`Q₁ := H/W³`** (MRT Theorem 2.3 p. 9 and Proposition 2.4 p. 10). -/
noncomputable def mrtQ1 (H W : ℝ) : ℝ := H / W ^ (3 : ℕ)

/-- **Proposition 2.4's set** (p. 10): `S := S_{P₁,Q₁,√X,X/d}`.  Note the fourth
subscript is `X/d`, not `X` — Theorem 2.3's is `S_{P₁,Q₁,√X,X}`.  MRT's own
remark on p. 8 explains why the pair `(X₀, X)` is carried separately: `X` may be
shrunk to `X/d` *without altering `J`*, which depends only on `X₀ = √X`. -/
noncomputable def mrtSProp24 (X H W : ℝ) (d : ℕ) : Finset ℕ :=
  mrtS (mrtP1 W) (mrtQ1 H W) (Real.sqrt X) (X / (d : ℝ))

/-! ## §3 — MRT's quality quantities `M(g;X)` and `M(g;X,Q)` (p. 4, (1.6)) -/

/-- **`M(g; X) := inf_{|t| ≤ X} 𝔻(g, n ↦ n^{it}; X)²`** (MRT p. 4, (1.6)).
`𝔻²` is the corpus's `Salt.MR.pretDistSq` (`Dist.lean:59`) and `n ↦ n^{it}` is
`Salt.MR.costwist` (`NonPret.lean:52`). -/
noncomputable def mrtM (g : ℕ → ℂ) (X : ℝ) : ℝ :=
  sInf {m : ℝ | ∃ t : ℝ, |t| ≤ X ∧ m = pretDistSq g (costwist t) X}

/-- **`M(g; X, Q) := inf_{|t| ≤ X; q ≤ Q; χ (q)} 𝔻(g, n ↦ χ(n)n^{it}; X)²`**
(MRT p. 4, the second display).  The twisted target `n ↦ χ(n)·n^{it}` is the
corpus's `Salt.MR.chiTwist` (`ChiEuler.lean:74`) — **unbarred `χ`, matching MRT**;
the corpus's barred `chiBarTwist` would give the same infimum (`χ ↦ χ̄` permutes
the characters mod `q`) but is not what MRT write, so it is not what is written
here.

This is Proposition 2.4's hypothesis (2.3) at `Q := W`, which is where MRT write
the modulus range out explicitly. -/
noncomputable def mrtQuality (g : ℕ → ℂ) (X Q : ℝ) : ℝ :=
  sInf {m : ℝ | ∃ (t : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q),
    |t| ≤ X ∧ 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ m = pretDistSq g (chiTwist χ t) X}

/-- **MRT's "1-bounded completely multiplicative"** (p. 4 for 1-boundedness,
Proposition 2.4 p. 10 for the complete multiplicativity).  Shaped exactly like
the corpus's `Salt.MR.Lemma4Datum` (`Eq26Bridge.lean:311`), which is its
`ℝ`-valued, `[−1,1]`-bounded sibling: `map_mul` carries **no** coprimality
hypothesis, which is what "completely" means. -/
structure MrtCompMultDatum (g : ℕ → ℂ) : Prop where
  /-- `g(1) = 1`. -/
  map_one : g 1 = 1
  /-- Complete multiplicativity: no coprimality hypothesis. -/
  map_mul : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → g (m * n) = g m * g n
  /-- `g` is 1-bounded. -/
  norm_le_one : ∀ n : ℕ, ‖g n‖ ≤ 1

/-! ## §4 — E-2: the statement of MRT Proposition 2.4 (p. 10) -/

/-- **Proposition 2.4's inner exponential sum**:
`∑_{x/d ≤ n ≤ x/d + H/d} 1_S(n) g(n) e(αn)`, with `e(·)` the corpus's normalised
additive character `Salt.ExpSum.eR` (`ExpSum/Basic.lean:43`).

The window `x/d ≤ n ≤ x/d + H/d` is realised over `ℕ` as
`Finset.Icc ⌈x/d⌉₊ ⌊x/d + H/d⌋₊`.  For `n ≥ 1` this is exactly MRT's range
(`Nat.ceil_le` is unconditional; `Nat.le_floor_iff` needs only the right endpoint
nonneg).  The only discrepancy is at `n = 0`, where the indicator `1_S` vanishes
(`zero_not_mem_mrtS`) — so the summand agrees with MRT's everywhere.  This is
also what makes the `x`-integral below finite: the integrand vanishes once the
window leaves `[1, ⌊X/d⌋]`. -/
noncomputable def mrtWindowExpSum (S : Finset ℕ) (g : ℕ → ℂ) (α : ℝ) (d : ℕ)
    (H x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈x / (d : ℝ)⌉₊ ⌊x / (d : ℝ) + H / (d : ℝ)⌋₊,
    (if n ∈ S then (1 : ℂ) else 0) * g n * Salt.ExpSum.eR (α * (n : ℝ))

/-- **The window bridge is EXACT** — the `ℕ`-window used by `mrtWindowExpSum` is
MRT's real window `x/d ≤ n ≤ x/d + H/d`, with both endpoints inclusive.  The
hypothesis `0 ≤ x/d + H/d` is only the right-endpoint nonnegativity `Nat.le_floor_iff`
needs; below it the window is empty of the `n ≥ 1` that carry `1_S`.  Companion to
`mem_mrtBand_nat`: together they are the whole reals-to-naturals cost of this
transcription, and it is zero. -/
theorem mem_mrtWindow {d : ℕ} {H x : ℝ} (hz : 0 ≤ x / (d : ℝ) + H / (d : ℝ))
    (n : ℕ) :
    n ∈ Finset.Icc ⌈x / (d : ℝ)⌉₊ ⌊x / (d : ℝ) + H / (d : ℝ)⌋₊
      ↔ (x / (d : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ x / (d : ℝ) + H / (d : ℝ)) := by
  rw [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hz]

/-- **MRT PROPOSITION 2.4 (Completely multiplicative exponential sum estimate),
`arXiv:1503.05121v3` p. 10 — THE STATEMENT, at an explicit constant `C`.**

> Let `X, H, W ≥ 10` be such that `(log H)^5 ≤ W ≤ min{H^{1/250}, (log X)^{1/125}}`,
> and let `g` be a 1-bounded completely multiplicative function such that
> `W ≤ exp(M(g;X,W)/3)`.  (2.3)
> Let `d` be a natural number with `d < W`.  Set `S := S_{P₁,Q₁,√X,X/d}` where
> `P₁ := W^200`, `Q₁ := H/W³`.  Then for any `α ∈ 𝕋` one has
> `∫_ℝ |∑_{x/d ≤ n ≤ x/d+H/d} 1_S(n) g(n) e(αn)| dx`
>   `≪ (1/d^{3/4})·((log H)^{1/4} loglog H / W^{1/4})·H·X`.  (2.4)

Transcription notes, each a deliberate choice:

* `α ∈ 𝕋` is quantified as `∀ α : ℝ`.  `e(αn)` is `1`-periodic in `α`, so this is
  equivalent, and it matches `Salt.Entropy.Chowla.MRTUniformity`, whose `∀ α`
  likewise sits **outside** the integral.  ⛔ The `sup`-inside form is Tao's (4.1)
  and is OPEN; the quantifier position here is MRT's and must not be moved.
* `d` is a *natural number* in MRT's sense, i.e. `1 ≤ d` (their `ℕ` starts at `1`;
  cf. Definition 2.1's "numbers `1 ≤ n ≤ X`").  Stated explicitly rather than left
  to the ambient `ℕ`.
* `(log H)^5` and `W^200`, `W³` are `ℕ`-powers; `H^{1/250}`, `(log X)^{1/125}`,
  `d^{3/4}`, `(log H)^{1/4}`, `W^{1/4}` are real powers (`rpow`).
* `≪` is MRT's absolute-constant `≪` (p. 7): hence the `C` parameter, and
  `MRTProp24Statement` for the `∃ C`.

⚠ **NON-VACUITY IS AN OWED SIDE-CHECK, NOT DISCHARGED HERE.**  Lean's Bochner
integral returns `0` for a non-integrable integrand, so a *proof* of `MRTProp24`
that never establishes integrability of `x ↦ ‖mrtWindowExpSum …‖` would be
vacuous.  The integrand is in fact a compactly supported step function — it
vanishes for `x < −H` and for `x > X`, because `S ⊆ [1, ⌊X/d⌋]`
(`mrtS_subset_Icc`) and `0 ∉ S` (`zero_not_mem_mrtS`) — but that is an
*argument*, not a landed lemma.  **Whoever discharges (2.4) must land the
integrability first, or the door is bought with `0 ≤ RHS`.** -/
def MRTProp24 (C : ℝ) : Prop :=
  ∀ (X H W : ℝ) (g : ℕ → ℂ) (d : ℕ) (α : ℝ),
    10 ≤ X → 10 ≤ H → 10 ≤ W →
    Real.log H ^ (5 : ℕ) ≤ W →
    W ≤ min (H ^ ((1 : ℝ) / 250)) (Real.log X ^ ((1 : ℝ) / 125)) →
    MrtCompMultDatum g →
    W ≤ Real.exp (mrtQuality g X W / 3) →
    1 ≤ d → (d : ℝ) < W →
    (∫ x : ℝ, ‖mrtWindowExpSum (mrtSProp24 X H W d) g α d H x‖)
      ≤ C * (1 / (d : ℝ) ^ ((3 : ℝ) / 4))
          * (Real.log H ^ ((1 : ℝ) / 4) * Real.log (Real.log H)
              / W ^ ((1 : ℝ) / 4))
          * H * X

/-- **MRT Proposition 2.4 as MRT state it**, i.e. with the `≪` spelled out as an
absolute constant (p. 7, §1.3).  Statement only: nothing in this file proves it,
and nothing in this file assumes it. -/
def MRTProp24Statement : Prop := ∃ C : ℝ, 0 < C ∧ MRTProp24 C

/-! ## E-5c — the `1_S`-dilation identity (MRT §4 p. 14)

Statements **VERBATIM** from the Captain-ratified draft (`seat 3abef515`, drafts 1+2 ratified
as drafted, all five questions).  **The statement act is the Captain's; the proofs are this
seat's.**  Nothing below adjusts the ratified text — iron rule 1.

Inside the major-arc reduction, residues mod `q`: for `n ≡ b (mod q)`, `d₀ := (b,q)`, `n = d₀m`,
`g` completely multiplicative and `d₀ ≤ q ≤ W ≤ P₁`.  Dividing out `d₀` — whose prime factors all
lie strictly below every band in play — moves the window parameter `Y ↦ Y/d₀` and touches nothing
else: `J` is pinned by `X₀`, which does NOT dilate. -/

/-- **Helper (mine, not ratified text): a factor with no band prime does not move the block
divisors.**  If every prime factor of `d₀` is strictly below the band's lower endpoint, then
`BlockPrimeDivs P Q (d₀·m) = BlockPrimeDivs P Q m` — the dilation is invisible to the band. -/
private theorem blockPrimeDivs_mul_of_lt_band {P Q d₀ m : ℕ} (hd₀ : 0 < d₀)
    (hlt : ∀ p ∈ d₀.primeFactors, p < P) :
    BlockPrimeDivs P Q (d₀ * m) = BlockPrimeDivs P Q m := by
  ext p
  rw [mem_blockPrimeDivs, mem_blockPrimeDivs]
  constructor
  · rintro ⟨hp, hdvd, hne, hPle, hQ⟩
    have hm0 : m ≠ 0 := by rintro rfl; simp at hne
    refine ⟨hp, ?_, hm0, hPle, hQ⟩
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact absurd hPle (not_le.mpr
        (hlt p (Nat.mem_primeFactors.mpr ⟨hp, h, hd₀.ne'⟩)))
    · exact h
  · rintro ⟨hp, hdvd, hne, hPle, hQ⟩
    exact ⟨hp, hdvd.mul_left d₀, by positivity, hPle, hQ⟩

/-- **E-5c — the `1_S`-dilation identity, membership half** (MRT `arXiv:1503.05121v3`
§4 p. 14, the residue split inside the major-arc reduction; the unstated child of v1's
deleted `E-5` — the parent was the Dirichlet split, this never was).
Dividing out `d₀` whose prime factors all lie strictly below every band in play moves
the window parameter `Y ↦ Y/d₀` and touches nothing else: `J` is pinned by `X₀`, which
does not dilate. Stated as an iff with no lower bound on `m`: at `m = 0` both sides are
false (`0 ∉ mrtS`), so the iff holds outright. -/
theorem mrtS_dilate {P₁ Q₁ X₀ Y : ℝ} {d₀ m : ℕ} (hd₀ : 1 ≤ d₀)
    (hP : ∀ j ∈ Finset.Icc 1 (mrtJ Q₁ X₀), ∀ p ∈ d₀.primeFactors,
        (p : ℝ) < mrtBandP P₁ Q₁ j) :
    d₀ * m ∈ mrtS P₁ Q₁ X₀ Y ↔ m ∈ mrtS P₁ Q₁ X₀ (Y / (d₀ : ℝ)) := by
  classical
  have hd₀pos : 0 < d₀ := hd₀
  have hd₀R : (0 : ℝ) < (d₀ : ℝ) := by exact_mod_cast hd₀pos
  rw [mem_mrtS, mem_mrtS]
  constructor
  · rintro ⟨⟨h1, h2⟩, hband⟩
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at h1
      · exact hm
    refine ⟨⟨hm1, ?_⟩, ?_⟩
    · -- range: `d₀·m ≤ ⌊Y⌋₊` gives `m ≤ ⌊Y/d₀⌋₊`
      have hYnn : (0 : ℝ) ≤ Y := by
        by_contra hneg
        rw [Nat.floor_of_nonpos (le_of_lt (not_le.mp hneg))] at h2
        omega
      have hle : ((d₀ * m : ℕ) : ℝ) ≤ Y := by
        have := Nat.floor_le hYnn
        calc ((d₀ * m : ℕ) : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
          _ ≤ Y := this
      refine Nat.le_floor ?_
      rw [le_div_iff₀ hd₀R]
      push_cast at hle ⊢
      linarith [hle]
    · -- bands: `d₀` contributes no block prime, so the block divisors coincide
      intro j hj
      have hdvd : BlockPrimeDivs (mrtBandPNat P₁ Q₁ j) (mrtBandQNat Q₁ j) (d₀ * m)
          = BlockPrimeDivs (mrtBandPNat P₁ Q₁ j) (mrtBandQNat Q₁ j) m :=
        blockPrimeDivs_mul_of_lt_band hd₀pos
          (fun q hq => Nat.lt_ceil.mpr (hP j hj q hq))
      have := hband j hj
      unfold blockOmega at this ⊢
      rwa [hdvd] at this
  · rintro ⟨⟨h1, h2⟩, hband⟩
    have hmul1 : 1 ≤ d₀ * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    refine ⟨⟨hmul1, ?_⟩, ?_⟩
    · have hYnn : (0 : ℝ) ≤ Y / (d₀ : ℝ) := by
        by_contra hneg
        rw [Nat.floor_of_nonpos (le_of_lt (not_le.mp hneg))] at h2
        omega
      have hle : ((m : ℕ) : ℝ) ≤ Y / (d₀ : ℝ) :=
        le_trans (by exact_mod_cast h2) (Nat.floor_le hYnn)
      rw [le_div_iff₀ hd₀R] at hle
      refine Nat.le_floor ?_
      push_cast at hle ⊢
      linarith [hle]
    · intro j hj
      have hdvd : BlockPrimeDivs (mrtBandPNat P₁ Q₁ j) (mrtBandQNat Q₁ j) (d₀ * m)
          = BlockPrimeDivs (mrtBandPNat P₁ Q₁ j) (mrtBandQNat Q₁ j) m :=
        blockPrimeDivs_mul_of_lt_band hd₀pos
          (fun q hq => Nat.lt_ceil.mpr (hP j hj q hq))
      have := hband j hj
      unfold blockOmega at this ⊢
      rwa [hdvd]

/-- **E-5c — the summand identity, the form the arc consumer takes** (same source line):
for completely multiplicative `g`, the sifted summand factors through the dilation. The
multiplicativity is taken hypothesis-level (`g (a·b) = g a · g b`, all `a b`), matching
MRT's "g completely multiplicative" without binding to a structure. -/
theorem mrtS_indicator_mul_dilate (g : ℕ → ℂ)
    (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {P₁ Q₁ X₀ Y : ℝ} {d₀ m : ℕ} (hd₀ : 1 ≤ d₀)
    (hP : ∀ j ∈ Finset.Icc 1 (mrtJ Q₁ X₀), ∀ p ∈ d₀.primeFactors,
        (p : ℝ) < mrtBandP P₁ Q₁ j) :
    (if d₀ * m ∈ mrtS P₁ Q₁ X₀ Y then (1 : ℂ) else 0) * g (d₀ * m)
      = g d₀ * ((if m ∈ mrtS P₁ Q₁ X₀ (Y / (d₀ : ℝ)) then (1 : ℂ) else 0) * g m) := by
  classical
  rw [hg d₀ m]
  by_cases hmem : m ∈ mrtS P₁ Q₁ X₀ (Y / (d₀ : ℝ))
  · rw [if_pos ((mrtS_dilate hd₀ hP).mpr hmem), if_pos hmem]
    ring
  · rw [if_neg (fun hc => hmem ((mrtS_dilate hd₀ hP).mp hc)), if_neg hmem]
    ring

end Salt.MR
