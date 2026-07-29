/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4WaveClosed
import Salt.MR.FrameWitness

/-!
# `M4Band` — ⟦THE BAND RE-CUT⟧'s pair law: the door datum on the Ramaré BAND `[P, Q]`

⟦THE POINT-vs-BAND WALL⟧ (flags, `1bab8e3`).  The capstone's Ramaré block was a POINT
(`ramI (H83 X θ) P P`) — TLGATES-SCOPE's *"easiest witness; a genuine band also works"* — and
the door datum called it: at a point the block-free mass is `≍ 1/X_d`, so the coprime tail's
charge is `O(1)` and no ε-window absorbs it.  `FrameWitness` §2′/§3′ and `M4MeanSq` §4 re-cut
the witness chain at the BAND `[P, Q]`, `Q` pinned at `⌊Q₈₃ X⌋₊`.  This file supplies the one
DATUM-side stone the band needs: the relativized pair law `SeamRowWindowed.SeamCoefW` at the
door's own sieved, χ-twisted, UN-PHASED coefficient.

## THE UPWARD MIRROR (§1)

`M4Residue` §2/§3 is the DOWNWARD dilation: a `d` all of whose prime factors lie BELOW every
block bottom is invisible to `MemS`.  The band needs the mirror: a `d` all of whose prime
factors lie ABOVE every block TOP is invisible too, for exactly the same reason —
`BlockPrimeDivs P Q` is a filter on `[P, Q]`, and either escape empties it.  The proofs are
`M4Residue`'s with `<` flipped.

At the door this is not an approximation but a fact about the calibration: the K-ladder's
tops obey `𝒬K_j < P₈₃ X θ₂₉₃ ≤ P` (`SeamCalibrationK.ladder_below_stationK` against the
capstone's own `hPlow`), so EVERY prime of the Ramaré band `[P, Q]` is above EVERY door block.

## THE PAIR LAW (§2)

`doorChiCoeff χ M = 1_𝒮·λχ̄` on the door's K-family.  Factorised at a band prime `p`:

  `1_𝒮(p·m)·λχ̄(p·m) = λχ̄(p) · 1_𝒮(m)·λχ̄(m)`,

i.e. `a(p·m) = b(m)·cf(p)` at

  `a = 1_{[X_d,2X_d]}·doorChiCoeff`,  `b = doorChiCoeff`,  `cf = λχ̄`.

**`b` IS THE DATUM** — the co-factor slot is the SAME sequence, which is what the freed
`b`-slot (⟦W1⟧, `M4MeanSq`'s carried co-factor datum) makes admissible.  There is no
coprimality condition (`λχ̄` is completely multiplicative, `liouChi_mul`), no window
restriction inside the law, and **no `m = 1` exception**: at `m = 1` both sides are `0`,
because a single band prime meets no door block.  That is the exact defect
`M4Seam.m4_row_cf_block_eq_zero` exhibits on the POINT chain, and it is what the band
dissolves.

## ⚠ THE UN-PHASED PIN (the forced order ⟦U2⟧)

`M4ErrRewire`'s `doorDatum`/`doorCofactor` are the PHASED pair, and they are genuinely
point-only: `e(αpm)` does not factor at a VARYING `p`, so the phase must come off before the
band is entered.  ⟦U2⟧'s forced composition order does exactly that (drift, split and
expansion all remove the phase), and the band sibling therefore lives at the un-phased
`doorChiCoeff`.  Do NOT generalize `doorDatum`/`doorCofactor` to a band.

## ⚠ THE `lam` COLLISION

`liouChi χ = liouvilleC·χ̄` (summed over integers), never `lamChi` — `M4Residue`'s trap.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — THE UPWARD MIRROR: a large `d` is invisible to `BlockPrimeDivs` -/

/-- **The honest largeness chain, at a prime.**  A prime `p` above the block top has its only
prime factor — itself — above the block top. -/
theorem primeFactors_gt_of_prime {p Q : ℕ} (hp : p.Prime) (hQ : Q < p) :
    ∀ r ∈ p.primeFactors, Q < r := by
  intro r hr
  rw [hp.primeFactors, Finset.mem_singleton] at hr
  omega

/-- A number all of whose prime factors are above the block top has **no** block primes:
`BlockPrimeDivs P Q d = ∅`.  The mirror of `M4Residue.blockPrimeDivs_eq_empty_of_small`. -/
theorem blockPrimeDivs_eq_empty_of_large {P Q d : ℕ} (hlg : ∀ p ∈ d.primeFactors, Q < p) :
    BlockPrimeDivs P Q d = ∅ := by
  rw [BlockPrimeDivs, Finset.filter_eq_empty_iff]
  intro p hp
  exact fun hc => absurd hc.2 (Nat.not_le.mpr (hlg p hp))

/-- **THE SHIFT IDENTITY, at the `Finset` level.**  If every prime factor of `d` lies above
the block top `Q`, the block primes of `d·m` are exactly those of `m`. -/
theorem blockPrimeDivs_shift_up {P Q d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hlg : ∀ p ∈ d.primeFactors, Q < p) :
    BlockPrimeDivs P Q (d * m) = BlockPrimeDivs P Q m := by
  rw [BlockPrimeDivs, BlockPrimeDivs, Nat.primeFactors_mul hd hm, Finset.filter_union,
    show (d.primeFactors.filter (fun p => P ≤ p ∧ p ≤ Q)) = ∅ from
      blockPrimeDivs_eq_empty_of_large (P := P) hlg, Finset.empty_union]

/-- `ω(d·m; P, Q) = ω(m; P, Q)` under the prime-level largeness gate. -/
theorem blockOmega_shift_up {P Q d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hlg : ∀ p ∈ d.primeFactors, Q < p) :
    blockOmega P Q (d * m) = blockOmega P Q m := by
  rw [blockOmega, blockOmega, blockPrimeDivs_shift_up hd hm hlg]

/-- **THE SHIFTED BLOCK CONDITION IS THE UNSHIFTED ONE.**  If every prime factor of `d` lies
above every block TOP `Qseq j`, `j ∈ [1, J]`, then `d·m ∈ 𝒮 ⟺ m ∈ 𝒮` — the mirror of
`M4Residue.memS_dilate`. -/
theorem memS_shift_up {Pseq Qseq : ℕ → ℕ} {J d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hlg : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ d.primeFactors, Qseq j < p) :
    MemS Pseq Qseq J (d * m) ↔ MemS Pseq Qseq J m := by
  constructor <;> intro h j hj
  · rw [← blockOmega_shift_up (P := Pseq j) hd hm (hlg j hj)]
    exact h j hj
  · rw [blockOmega_shift_up (P := Pseq j) hd hm (hlg j hj)]
    exact h j hj

/-- The `𝒮`-transfer at a BAND PRIME above every block top — the form the pair law reads. -/
theorem memS_shift_up_prime {Pseq Qseq : ℕ → ℕ} {J p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hgt : ∀ j ∈ Finset.Icc 1 J, Qseq j < p) :
    MemS Pseq Qseq J (p * m) ↔ MemS Pseq Qseq J m :=
  memS_shift_up hp.pos.ne' hm (fun j hj => primeFactors_gt_of_prime hp (hgt j hj))

/-- **THE POINTWISE PAIR LAW, UPWARD**: `1_𝒮(p·m)·g(p·m) = g(p)·1_𝒮(m)·g(m)` at a band prime
`p` above every block top, for any completely multiplicative `g`.  The mirror of
`M4Residue.indicator_mul_dilate`. -/
theorem indicator_mul_shift_up {g : ℕ → ℂ} (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {Pseq Qseq : ℕ → ℕ} {J p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hgt : ∀ j ∈ Finset.Icc 1 J, Qseq j < p) :
    (if MemS Pseq Qseq J (p * m) then g (p * m) else 0)
      = (if MemS Pseq Qseq J m then g m else 0) * g p := by
  by_cases hS : MemS Pseq Qseq J m
  · rw [if_pos ((memS_shift_up_prime hp hm hgt).mpr hS), if_pos hS, hg]; ring
  · rw [if_neg (fun hc => hS ((memS_shift_up_prime hp hm hgt).mp hc)), if_neg hS, zero_mul]

/-! ## §2 — THE BAND PAIR LAW AT THE SIEVED χ-TWISTED DATUM -/

/-- **THE BAND PAIR LAW** (`memSCoeff_seamCoefW_band`).  The window-cut sieved datum,
its own un-cut self as co-factor, and `λχ̄` as the prime coefficient satisfy
`SeamRowWindowed.SeamCoefW` on the WHOLE band `[P, Q]`, as soon as every door block top is
strictly below the band bottom `P`.

No coprimality, no `m = 1` exception, no relation between `X_d` and the band. -/
theorem memSCoeff_seamCoefW_band {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J Xd P Q : ℕ) (hgate : ∀ j ∈ Finset.Icc 1 J, Qseq j < P) :
    SeamCoefW Xd P Q (winCut Xd (memSCoeff Pseq Qseq J (liouChi χ)))
      (memSCoeff Pseq Qseq J (liouChi χ)) (liouChi χ) := by
  intro p m hp hPp _ _ hlo hhi
  have hgt : ∀ j ∈ Finset.Icc 1 J, Qseq j < p := fun j hj => lt_of_lt_of_le (hgate j hj) hPp
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · -- ⟦`m = 0`⟧ both sides vanish: `λχ̄(0) = 0`, so the sieved datum does too
    have hl0 : memSCoeff Pseq Qseq J (liouChi χ) 0 = 0 := by
      unfold memSCoeff
      split_ifs
      · unfold liouChi; simp
      · rfl
    have hw0 : winCut Xd (memSCoeff Pseq Qseq J (liouChi χ)) 0 = 0 := by
      unfold winCut
      split_ifs
      · exact hl0
      · rfl
    rw [mul_zero, hw0, hl0, zero_mul]
  · -- ⟦the generic cofactor⟧ the window puts `winCut` on its live branch
    have hloN : Xd ≤ p * m := by
      have : ((Xd : ℕ) : ℝ) ≤ ((p * m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hhiN : p * m ≤ 2 * Xd := by
      have : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    rw [winCut, if_pos ⟨hloN, hhiN⟩]
    exact indicator_mul_shift_up (liouChi_mul χ) hp (by omega) hgt

/-- **THE DOOR'S BAND PAIR LAW** (`doorChiCoeff_seamCoefW_band`) — `memSCoeff_seamCoefW_band`
at the door's own K-family, where `doorChiCoeff χ M` is the sieved datum by definition. -/
theorem doorChiCoeff_seamCoefW_band {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd P Q : ℕ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (3072 * M) M j < P) :
    SeamCoefW Xd P Q (winCut Xd (doorChiCoeff χ M)) (doorChiCoeff χ M) (liouChi χ) :=
  memSCoeff_seamCoefW_band χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2
    Xd P Q hgate

/-! ## §3 — THE BAND GATE IS THE CALIBRATION'S OWN

`SeamCalibrationK.ladder_below_stationK` says the K-ladder never enters the §8.3 window:
`𝒬K_j < P₈₃ X θ₂₉₃` at every level.  The capstone already carries `P₈₃ X θ₂₉₃ ≤ P`
(`hPlow`) and the `hJdef` cutoff (`hQXd`), so the band gate costs NOTHING new. -/

/-- **THE BAND GATE, FROM THE CALIBRATION** (`door_band_gate`).  Every door block top is
strictly below the Ramaré band bottom. -/
theorem door_band_gate {A G M Jb P : ℕ} {X : ℝ} (hG : 1 ≤ G) (hX : 1 < Real.log X)
    (hJdef : ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)))
    (hPlow : P83 X theta293 ≤ (P : ℝ)) :
    ∀ j ∈ Finset.Icc 1 Jb, calQK A G M j < P := by
  intro j hj
  have hjJ : j ≤ Jb := (Finset.mem_Icc.mp hj).2
  have h := ladder_below_stationK hG hX hJdef j hjJ
  have hR : ((calQK A G M j : ℕ) : ℝ) < (P : ℝ) := lt_of_lt_of_le h hPlow
  exact_mod_cast hR

/-- **THE BAND GATE FROM THE CAPSTONE'S OWN `hQXd`** (`door_band_gate_of_log`).  The cutoff
in the shape `M4MeanSq.m4_meansq_per_chi_gen` carries it: `log 𝒬K_Jb ≤ √(log X)`. -/
theorem door_band_gate_of_log {A G M Jb P : ℕ} {X : ℝ} (hG : 1 ≤ G) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ)) :
    ∀ j ∈ Finset.Icc 1 Jb, calQK A G M j < P := by
  refine door_band_gate hG hX ?_ hPlow
  have hQ1 : (1 : ℝ) ≤ ((calQK A G M Jb : ℕ) : ℝ) := by
    exact_mod_cast one_le_calQK A G M Jb
  have hQ0 : (0 : ℝ) < ((calQK A G M Jb : ℕ) : ℝ) := by linarith
  have hsq : Real.sqrt (Real.log X) = (Real.log X) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  calc ((calQK A G M Jb : ℕ) : ℝ)
      = Real.exp (Real.log ((calQK A G M Jb : ℕ) : ℝ)) := (Real.exp_log hQ0).symm
    _ ≤ Real.exp (Real.sqrt (Real.log X)) := Real.exp_le_exp.mpr hQlog
    _ = Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)) := by rw [hsq]

end Salt.MR
