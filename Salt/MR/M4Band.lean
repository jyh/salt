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

/-! ## §4 — ⟦THE ENDPOINT STRADDLE⟧: the pair law at a HALF-OPEN cut

`M4DoorRow` §1's finding.  The capstone's two support pins MEET at the block bottom —
`hsupp0` demands `a n = 0` for `(n : ℝ) ≤ X = X_d`, while `hasupp` allows support on
`[X_d, 2X_d]` — so the door datum must be cut HALF-OPEN (`M4DoorRow.winCutH`).  §2's pair law
is stated at the CLOSED `SeamRowWindowed.winCut`, whose `SeamCoefW` antecedent `X_d ≤ p·m`
INCLUDES the endpoint (`M4DoorRow.winCut_endpoint` witnesses the clash).

**The endpoint case is neither free nor vacuous.**  At `p·m = X_d` the half-open cut gives
`a (p·m) = 0`, while the right-hand side is `1_𝒮(m)·λχ̄(m)·λχ̄(p) = 1_𝒮(X_d)·λχ̄(X_d)` (§1's
shift-up identity), which does NOT vanish in general.  So the honest sibling carries exactly
one extra binder — **the datum vanishes at the block bottom** — and
`memSCoeff_endpoint_zero_of_seamCoefW` shows the binder is FORCED, not a convenience: any cut
with `a X_d = 0` satisfying `SeamCoefW` at a band factorization of `X_d` makes the datum
vanish there.

The cut is left ABSTRACT (an `a` with its agreement law) because `winCutH` is defined
DOWNSTREAM, in `M4DoorRow`; the half-open instance is that file's one-liner

  `memSCoeff_seamCoefW_band_H … (fun n h₁ h₂ => winCutH_of_mem _ h₁ h₂) (winCutH_supp0 _ le_rfl)`.
-/

/-- **THE BAND PAIR LAW AT AN ABSTRACT CUT** (`memSCoeff_seamCoefW_band_gen`).  §2's law needs
nothing about the cut beyond agreement with the sieved datum on the CLOSED dyadic window —
`winCut` is one such cut (§2), and a half-open cut is another as soon as the datum vanishes at
the endpoint. -/
theorem memSCoeff_seamCoefW_band_gen {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J Xd P Q : ℕ) (a : ℕ → ℂ) (hgate : ∀ j ∈ Finset.Icc 1 J, Qseq j < P)
    (ha : ∀ n : ℕ, Xd ≤ n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J (liouChi χ) n) :
    SeamCoefW Xd P Q a (memSCoeff Pseq Qseq J (liouChi χ)) (liouChi χ) := by
  intro p m hp hPp _ _ hlo hhi
  have hgt : ∀ j ∈ Finset.Icc 1 J, Qseq j < p := fun j hj => lt_of_lt_of_le (hgate j hj) hPp
  have hloN : Xd ≤ p * m := by
    have : ((Xd : ℕ) : ℝ) ≤ ((p * m : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hhiN : p * m ≤ 2 * Xd := by
    have : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  rw [ha _ hloN hhiN]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · -- ⟦`m = 0`⟧ both sides vanish: `λχ̄(0) = 0`, so the sieved datum does too
    have hl0 : memSCoeff Pseq Qseq J (liouChi χ) 0 = 0 := by
      unfold memSCoeff
      split_ifs
      · unfold liouChi; simp
      · rfl
    rw [mul_zero, hl0, zero_mul]
  · exact indicator_mul_shift_up (liouChi_mul χ) hp (by omega) hgt

/-- **THE HALF-OPEN BAND PAIR LAW** (`memSCoeff_seamCoefW_band_H`) — §2's law at a cut that
agrees with the sieved datum only STRICTLY above the block bottom and vanishes AT it, which is
the shape `M4DoorRow`'s `hsupp0`/`hasupp` straddle forces.  The one new binder `hend` is the
endpoint discharge, and it is forced (`memSCoeff_endpoint_zero_of_seamCoefW`). -/
theorem memSCoeff_seamCoefW_band_H {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J Xd P Q : ℕ) (a : ℕ → ℂ) (hgate : ∀ j ∈ Finset.Icc 1 J, Qseq j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J (liouChi χ) n)
    (ha0 : a Xd = 0) (hend : memSCoeff Pseq Qseq J (liouChi χ) Xd = 0) :
    SeamCoefW Xd P Q a (memSCoeff Pseq Qseq J (liouChi χ)) (liouChi χ) :=
  memSCoeff_seamCoefW_band_gen χ Pseq Qseq J Xd P Q a hgate (fun n hlo hhi => by
    rcases eq_or_lt_of_le hlo with rfl | hlt
    · rw [ha0, hend]
    · exact haH n hlt hhi)

/-! ### ⟦THE ENDPOINT WALL DISSOLVED⟧ — the STRICT siblings

`SeamRowWindowed.SeamCoefWS` asks for the factorization only STRICTLY above the block bottom,
which is exactly where a half-open cut agrees with the datum.  So the strict siblings take
`haH` **alone**: `ha0` and `hend` both DROP (`ha0` fed only the `n = X_d` branch of the
agreement law, and `hend` was that branch's obligation), and the `m = 0` case discharges by
absurdity — `X_d < p·0 = 0` contradicts `0 ≤ X_d`.  The endpoint mass this leaves unpriced is
paid on the ROW, by the fused `p²` filter `p ∣ m ∨ p·m = X`. -/

/-- **THE STRICT BAND PAIR LAW AT AN ABSTRACT CUT** (`memSCoeff_seamCoefWS_band_gen`).  §4's
law at `SeamCoefWS`: the cut need only agree with the sieved datum STRICTLY above the block
bottom, and nothing whatever is asked at `X_d`. -/
theorem memSCoeff_seamCoefWS_band_gen {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J Xd P Q : ℕ) (a : ℕ → ℂ) (hgate : ∀ j ∈ Finset.Icc 1 J, Qseq j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J (liouChi χ) n) :
    SeamCoefWS Xd P Q a (memSCoeff Pseq Qseq J (liouChi χ)) (liouChi χ) := by
  intro p m hp hPp _ _ hlo hhi
  have hgt : ∀ j ∈ Finset.Icc 1 J, Qseq j < p := fun j hj => lt_of_lt_of_le (hgate j hj) hPp
  -- ⟦AMENDMENT 5⟧ the `m` split comes BEFORE the agreement law: `m = 0` is absurd
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exfalso
    have h0 : (0 : ℝ) ≤ (Xd : ℝ) := Nat.cast_nonneg Xd
    rw [Nat.cast_zero, mul_zero] at hlo
    linarith
  · have hloN : Xd < p * m := by
      have h : ((Xd : ℕ) : ℝ) < ((p * m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    have hhiN : p * m ≤ 2 * Xd := by
      have h : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    rw [haH _ hloN hhiN]
    exact indicator_mul_shift_up (liouChi_mul χ) hp (by omega) hgt

/-- **THE STRICT HALF-OPEN BAND PAIR LAW** (`memSCoeff_seamCoefWS_band_H`) — the name
`memSCoeff_seamCoefW_band_H`'s consumers read, with `ha0`/`hend` gone. -/
theorem memSCoeff_seamCoefWS_band_H {q : ℕ} (χ : DirichletCharacter ℂ q) (Pseq Qseq : ℕ → ℕ)
    (J Xd P Q : ℕ) (a : ℕ → ℂ) (hgate : ∀ j ∈ Finset.Icc 1 J, Qseq j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J (liouChi χ) n) :
    SeamCoefWS Xd P Q a (memSCoeff Pseq Qseq J (liouChi χ)) (liouChi χ) :=
  memSCoeff_seamCoefWS_band_gen χ Pseq Qseq J Xd P Q a hgate haH

/-- **THE DOOR'S STRICT HALF-OPEN BAND PAIR LAW** (`doorChiCoeff_seamCoefWS_band_H`). -/
theorem doorChiCoeff_seamCoefWS_band_H {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd P Q : ℕ)
    (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (3072 * M) M j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff χ M n) :
    SeamCoefWS Xd P Q a (doorChiCoeff χ M) (liouChi χ) :=
  memSCoeff_seamCoefWS_band_H χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2
    Xd P Q a hgate haH

/-- **`hcoefPin` AT THE DOOR, STRICT** (`doorChiCoeff_seamCoefWS_at_door_H`) — the strict
sibling of `doorChiCoeff_seamCoefW_at_door_H`: the band gate discharged from the capstone's
own `hQXd`/`hPlow`, and NO endpoint obligation at all. -/
theorem doorChiCoeff_seamCoefWS_at_door_H {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd P Q : ℕ}
    {X : ℝ} {a : ℕ → ℂ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff χ M n) :
    SeamCoefWS Xd P Q a (doorChiCoeff χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefWS_band_H χ M Xd P Q a
    (door_band_gate_of_log (by omega : 1 ≤ 3072 * M) hX hQlog hPlow) haH

/-- **THE DOOR'S HALF-OPEN BAND PAIR LAW** (`doorChiCoeff_seamCoefW_band_H`) —
`memSCoeff_seamCoefW_band_H` at the door's own K-family. -/
theorem doorChiCoeff_seamCoefW_band_H {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd P Q : ℕ)
    (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (3072 * M) M j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff χ M Xd = 0) :
    SeamCoefW Xd P Q a (doorChiCoeff χ M) (liouChi χ) :=
  memSCoeff_seamCoefW_band_H χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2
    Xd P Q a hgate haH ha0 hend

/-- **`hcoefPin` AT THE DOOR, HALF-OPEN** (`doorChiCoeff_seamCoefW_at_door_H`) — the half-open
sibling of `M4DoorRow.doorChiCoeff_seamCoefW_at_door`: the band gate discharged from the
capstone's own `hQXd`/`hPlow`, the endpoint discharged by `hend`. -/
theorem doorChiCoeff_seamCoefW_at_door_H {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd P Q : ℕ}
    {X : ℝ} {a : ℕ → ℂ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff χ M Xd = 0) :
    SeamCoefW Xd P Q a (doorChiCoeff χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefW_band_H χ M Xd P Q a
    (door_band_gate_of_log (by omega : 1 ≤ 3072 * M) hX hQlog hPlow) haH ha0 hend

/-- The arithmetic entry to `hend`: outside `𝒮` the sieved datum is `0` by construction. -/
theorem memSCoeff_eq_zero_of_not_memS {Pseq Qseq : ℕ → ℕ} {J n : ℕ} (a : ℕ → ℂ)
    (h : ¬ MemS Pseq Qseq J n) : memSCoeff Pseq Qseq J a n = 0 := by
  simp only [memSCoeff, if_neg h]

/-- **THE ENDPOINT OBLIGATION, EXACTLY** (`seamCoefW_endpoint_forced`).  A cut vanishing at the
block bottom can satisfy `SeamCoefW`'s CLOSED antecedent only if the pair's right-hand side
vanishes at every band factorization of `X_d`.  Nothing about the door enters. -/
theorem seamCoefW_endpoint_forced {a b cf : ℕ → ℂ} {Xd P Q p m : ℕ}
    (hcoefW : SeamCoefW Xd P Q a b cf) (ha0 : a Xd = 0)
    (hp : p.Prime) (hP : P ≤ p) (hQ : p ≤ Q) (hpm : ¬ p ∣ m) (hXd : p * m = Xd) :
    b m * cf p = 0 := by
  have hR : (p : ℝ) * (m : ℝ) = (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) ≤ (Xd : ℝ) := Nat.cast_nonneg _
  have h := hcoefW p m hp hP hQ hpm (le_of_eq hR.symm) (by linarith)
  rw [hXd, ha0] at h
  exact h.symm

/-- **THE STRADDLE IS REAL** (`memSCoeff_endpoint_zero_of_seamCoefW`).  The converse of
`memSCoeff_seamCoefW_band_H`'s `hend`: if the block bottom admits ANY band factorization
`X_d = p·m` (`p` a band prime above every block, `m ≠ 0`), then a half-open cut satisfies the
band pair law ONLY IF the sieved datum vanishes at `X_d`.  So the extra binder is not a proof
convenience — it is what the endpoint costs. -/
theorem memSCoeff_endpoint_zero_of_seamCoefW {q : ℕ} (χ : DirichletCharacter ℂ q)
    {Pseq Qseq : ℕ → ℕ} {J Xd P Q p m : ℕ} {a : ℕ → ℂ}
    (hcoefW : SeamCoefW Xd P Q a (memSCoeff Pseq Qseq J (liouChi χ)) (liouChi χ))
    (ha0 : a Xd = 0) (hgate : ∀ j ∈ Finset.Icc 1 J, Qseq j < P)
    (hp : p.Prime) (hP : P ≤ p) (hQ : p ≤ Q) (hpm : ¬ p ∣ m) (hm0 : m ≠ 0)
    (hXd : p * m = Xd) :
    memSCoeff Pseq Qseq J (liouChi χ) Xd = 0 := by
  have hgt : ∀ j ∈ Finset.Icc 1 J, Qseq j < p := fun j hj => lt_of_lt_of_le (hgate j hj) hP
  have hzero := seamCoefW_endpoint_forced hcoefW ha0 hp hP hQ hpm hXd
  have hEq : memSCoeff Pseq Qseq J (liouChi χ) (p * m)
      = memSCoeff Pseq Qseq J (liouChi χ) m * liouChi χ p :=
    indicator_mul_shift_up (liouChi_mul χ) hp hm0 hgt
  rw [← hXd, hEq]
  exact hzero

/-! ## §GK — the G-lever twin

The five door-side band pair laws re-instantiated at `G := s13GK K M`.  Every one of them is
a pure re-instantiation of the `Pseq`/`Qseq`-generic law above (`memSCoeff_seamCoefW_band`,
`memSCoeff_seamCoefW_band_H`, `memSCoeff_seamCoefWS_band_H`), so the lever costs nothing at
all here: the datum is `doorChiCoeff_gk K χ M` (`M4WaveClosed`), which unfolds to the same
`memSCoeff` at the levered K-family.  The only non-mechanical step is the `1 ≤ G` side
condition of `door_band_gate_of_log`, which is `GLever.one_le_s13GK` instead of `by omega`. -/

/-- **THE DOOR'S BAND PAIR LAW, AT THE G-LEVER** (`doorChiCoeff_seamCoefW_band_gk`). -/
theorem doorChiCoeff_seamCoefW_band_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Xd P Q : ℕ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (s13GK K M) M j < P) :
    SeamCoefW Xd P Q (winCut Xd (doorChiCoeff_gk K χ M)) (doorChiCoeff_gk K χ M)
      (liouChi χ) :=
  memSCoeff_seamCoefW_band χ (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2
    Xd P Q hgate

/-- **THE DOOR'S STRICT HALF-OPEN BAND PAIR LAW, AT THE G-LEVER**
(`doorChiCoeff_seamCoefWS_band_H_gk`). -/
theorem doorChiCoeff_seamCoefWS_band_H_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Xd P Q : ℕ) (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (s13GK K M) M j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_gk K χ M n) :
    SeamCoefWS Xd P Q a (doorChiCoeff_gk K χ M) (liouChi χ) :=
  memSCoeff_seamCoefWS_band_H χ (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M)
    2 Xd P Q a hgate haH

/-- **`hcoefPin` AT THE DOOR, STRICT, AT THE G-LEVER**
(`doorChiCoeff_seamCoefWS_at_door_H_gk`).  The band gate is the calibration's own at the
levered base; `1 ≤ s13GK K M` is `GLever.one_le_s13GK`. -/
theorem doorChiCoeff_seamCoefWS_at_door_H_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd P Q : ℕ} {X : ℝ} {a : ℕ → ℂ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_gk K χ M n) :
    SeamCoefWS Xd P Q a (doorChiCoeff_gk K χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefWS_band_H_gk K χ M Xd P Q a
    (door_band_gate_of_log (one_le_s13GK K hM) hX hQlog hPlow) haH

/-- **THE DOOR'S HALF-OPEN BAND PAIR LAW, AT THE G-LEVER**
(`doorChiCoeff_seamCoefW_band_H_gk`). -/
theorem doorChiCoeff_seamCoefW_band_H_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Xd P Q : ℕ) (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 2, calQK (Adoor M) (s13GK K M) M j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_gk K χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_gk K χ M Xd = 0) :
    SeamCoefW Xd P Q a (doorChiCoeff_gk K χ M) (liouChi χ) :=
  memSCoeff_seamCoefW_band_H χ (calP (Adoor M) (s13GK K M)) (calQK (Adoor M) (s13GK K M) M) 2
    Xd P Q a hgate haH ha0 hend

/-- **`hcoefPin` AT THE DOOR, HALF-OPEN, AT THE G-LEVER**
(`doorChiCoeff_seamCoefW_at_door_H_gk`). -/
theorem doorChiCoeff_seamCoefW_at_door_H_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {M Xd P Q : ℕ} {X : ℝ} {a : ℕ → ℂ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ))
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = doorChiCoeff_gk K χ M n)
    (ha0 : a Xd = 0) (hend : doorChiCoeff_gk K χ M Xd = 0) :
    SeamCoefW Xd P Q a (doorChiCoeff_gk K χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefW_band_H_gk K χ M Xd P Q a
    (door_band_gate_of_log (one_le_s13GK K hM) hX hQlog hPlow) haH ha0 hend

-- #audit (temporary)

end Salt.MR
