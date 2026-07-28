/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Dyadic
import Salt.MR.SieveGlue
import Salt.MR.SeamNumber
import Salt.MR.CapFreeAssembly

/-!
# M4-1 — THE `1_𝒮` INSERT (`M4Sieve`)

Source: Matomäki–Radziwiłł–Tao `1503.05121v3`, **§4 step (a)** (p. 14); the campaign freeze
`docs/exploration/s9-freeze-0726.md` ⟦AMENDMENT B⟧ row `M4-1` (:276); the `M4-JOIN` delta in
`docs/blueprints/flags.md`.

MRT insert the block indicator `1_𝒮` by hand against the door's raw λ-window and pay the
complement by a **count**, not by analysis.  Post-`SieveGlue` the sieve leg is a
**citation**: `hsieve_of_engine` (`SieveGlue.lean:438`) already prices
`(1/X)·#{n ∈ N_lg : n ∉ 𝒮}` by `C·∑_j log 𝒫_j/log 𝒬_j` at the K-family, unconditionally,
with `C` the single shared constant of `card_blockfree_le`.  This file is the four moves
that turn that count into the door's own object.

## The ladder

* **§1 — the insert identity.**  `∑_{m ∈ W} a(m) = ∑_{m ∈ W} 1_𝒮(m)a(m) + ∑_{m ∈ W, m ∉ 𝒮}
  a(m)` at a general `a` (`sum_memS_split`), with the 1-bounded triangle bound on the
  complement leg (`norm_sum_notMemS_le`).  Instantiated at the door's carrier
  `absWindowSum` (`norm_absWindowSum_memS_insert`) and at MRT's own `shortSum`
  (`norm_shortSum_memS_insert`); the λ- and λχ̄-data ride
  `M4Residue.liouvilleC_norm_le_one` and `CapFreeAssembly.norm_liouChi_le_one`.
* **§2 — the complement count on the door's measure.**  `hsieve_of_engine` counts on
  `Ioc X (2X)`; the door needs the count integrated against `logMeasure x ω` over the
  SHORT windows `Ioc n (n+H)`, `n ∈ Ioc (x/ω) x`.  The exchange is a double count
  (`sum_window_double_count`): every `m` is covered by at most `H` of the short windows,
  so the `n`-sum of the short counts is `≤ H` times ONE count on `Ioc a (b+H)`.  The
  harmonic weight is spent by `1/n ≤ 1/X` on a **block** `(a, b]` above the sieve scale
  `X` — see ⟦THE VACUITY FINDING⟧ below for why the whole door window is not one block.
* **§3 — the half-open endpoint, and the citation.**  `card_notMemS_of_subset_Icc` pays the
  single lattice point `m = X` that `Ioc X (2X)` drops (`SieveGlue.lean:75–79`, the HS-6
  residual): its contribution to the normalised count is `≤ 1/X`, one term, bounded
  trivially.  `notMemS_window_count_le` then composes with `hsieve_of_engine`.
* **§4 — the M-gate.**  `SeamNumber.sum_ratioK_le_basel` collects the `j`-sum at the sharp
  `π²/6`; `sieve_mass_le_quarter` reads the freeze's gate `8C/δ ≤ M`.
* **§5 — the exits.**  `m4_sieve_block_mass` (the priced block: `(δ/4)·H + H/X`, all gates
  carried, nothing evaluated) and `m4_sieve_insert` (the door-shaped `logMeasure`-`L¹`
  statement M4-7 / M4-8 consume, with the total complement mass carried as `B`).

## ⟦THE VACUITY FINDING⟧ (this row's sharpest result — feeds M4-8's brief)

The M4-1 row as literally composed — the FULL door window against ONE sieve block — is
**vacuous**, not merely lossy.  `MemS`'s engine counts on `Ioc X (2X)`; containing
`Ioc (x/ω) (x+H)` in `Icc X (2X)` needs `X ≤ x/ω` and `x + H ≤ 2X`, hence
`ω(x+H) ≤ 2x`, hence `ω < 2` — while `ChowlaRegime.hω` pins `2 ≤ ω`.  Independently, the
crude whole-window weight `1/n ≤ ω/x` loses a factor `ω/log ω` against the normalisation
`Z = ∑_{n ∈ (x/ω,x]} 1/n ≍ log ω`.  **The dyadic split is load-bearing already at M4-1**,
not only at M4-8, and this file is therefore cut at the block: §2–§4 price ONE block
(`m4_sieve_block_mass`), and the door exit carries the assembled mass `B`, which M4-8
supplies by summing blocks over M4-4's cover (`M4Dyadic.sum_dyadCover`).

## ⟦WHAT IS CITED, NEVER RE-DERIVED⟧

`hsieve_of_engine` (the whole sieve leg), `card_blockfree_le`'s constant, `sum_ratioK_le_basel`,
`ShiftCorr.integral_logMeasure_eq` (the Dirac reduction — hence no integrability side
condition anywhere in this file), `M4Window.absWindowSum` and its conventions,
`M4Dyadic.integral_logMeasure_le_of_le`.

`Eq26Bridge.shortSum_eq26_window` (:380) and `Eq26Bridge.window_defect_bound` (:346) are the
landed **window-convention** bridges — half-open `(x, x+h]` against MR's closed
`[⌈x⌉₊, ⌊x+h⌋₊]`, for the eq-(26)/Theorem-3 carrier `shortSum`.  They are NOT needed here and
are not re-derived: the M4 carrier `absWindowSum` is half-open on `Ioc n (n+H)` already, and
`logMeasure`'s own carrier is the half-open `Ioc (x/ω) x`, so the two conventions agree on
the nose.  The ONLY convention crossing left in the M4-1 row is the bottom endpoint of the
sieve engine's dyadic window (`Icc X (2X)` against `Ioc X (2X)`), and §3 pays it explicitly.

## ⟦V9c LAW⟧

`calP`/`calQK` are `2^{65536}`-scale numerals; nothing here presents a closed one to `simp`
or `norm_num`.  Every statement keeps `A`, `G`, `M`, `j` variable and moves only through
`log_calP_div_log_calQK` (inside `sum_ratioK_le_basel`) and `ratioSumK`.

## ⟦THE `J`-RANGE⟧

One convention throughout, matching `MemS` (`Sec9Glue.lean:118`) and `hsieve_of_engine`:
the blocks are indexed by `j ∈ Finset.Icc 1 J`.  There is no `[1, J]`-versus-`Icc 1 Jb`
mismatch to reconcile — `Jb` is the door inhabitant's *value* for `J` (`Jb = 2`), not a
different range.

## ⟦THE THREE LOG SCALES⟧

This file speaks **X-scale** in §2–§4 (`√log X ≥ 100`, the block gates, the sieve scale `X`)
and **door scale** (`x`, `ω`, `H`) in §5.  No `log H` numeral appears; `W` never appears.
The bridge between the two is the pair of carried block hypotheses `X ≤ a` and
`Ioc a (b+H) ⊆ Icc X (2X)` — M4-4's dyadic cover, consumed as a gate.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — the three objects -/

/-- **The sieved coefficient sequence** `1_𝒮 · a`: MRT's inserted indicator, as a datum.
`𝒮` is `Sec9Glue.MemS Pseq Qseq J` — "a prime factor in every block `[P_j, Q_j]`,
`j ∈ [1, J]`". -/
def memSCoeff (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun m => if MemS Pseq Qseq J m then a m else 0

/-- The insert is transparent to a weight: `1_𝒮·(a·w) = (1_𝒮·a)·w`.  This is what lets the
general insert be stated at a bare coefficient sequence and consumed at the door's
`a(m)e(αm)`. -/
theorem memSCoeff_mul (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a w : ℕ → ℂ) (m : ℕ) :
    memSCoeff Pseq Qseq J (fun k => a k * w k) m = memSCoeff Pseq Qseq J a m * w m := by
  simp only [memSCoeff]
  split_ifs
  · rfl
  · rw [zero_mul]

/-- `1_𝒮·a` is 1-bounded whenever `a` is (the indicator only ever deletes terms). -/
theorem norm_memSCoeff_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (Pseq Qseq : ℕ → ℕ)
    (J : ℕ) (m : ℕ) : ‖memSCoeff Pseq Qseq J a m‖ ≤ 1 := by
  simp only [memSCoeff]
  split_ifs
  · exact ha m
  · rw [norm_zero]; norm_num

/-- **The complement count on ONE short window** `(n, n+H]` — the object the insert's
complement leg is bounded by, and the object §2 integrates. -/
def notMemSCount (Pseq Qseq : ℕ → ℕ) (J H n : ℕ) : ℕ :=
  ((Finset.Ioc n (n + H)).filter (fun m => ¬ MemS Pseq Qseq J m)).card

/-- **The K-family sieve mass**, `∑_{j ∈ [1,J]} log 𝒫_j / log 𝒬_j` — the right-hand side of
`hsieve_of_engine`, named so that no statement below has to display a closed `calP`. -/
def ratioSumK (A G M J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J,
    Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)

/-- The sieve mass is nonnegative: each ratio is `1/(j²M)` (`log_calP_div_log_calQK`). -/
theorem ratioSumK_nonneg {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (J : ℕ) :
    0 ≤ ratioSumK A G M J := by
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [log_calP_div_log_calQK hA hG hM (Finset.mem_Icc.mp hj).1]
  exact div_nonneg zero_le_one (by positivity)

/-- The count as a sum of indicators — the shape §2's double count consumes. -/
theorem card_notMemS_eq_sum (W : Finset ℕ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) :
    ((W.filter (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ)
      = ∑ m ∈ W, (if ¬ MemS Pseq Qseq J m then (1 : ℝ) else 0) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## §1 — THE INSERT IDENTITY

MRT p. 14 step (a).  Stated at a general coefficient sequence, over a general finite window;
the door's carrier and MRT's own `shortSum` are two instantiations. -/

/-- **THE INSERT IDENTITY.**  `∑_{m ∈ W} a(m) = ∑_{m ∈ W} 1_𝒮(m)a(m) + ∑_{m ∈ W, m ∉ 𝒮} a(m)`
— the `Finset` split at the block condition, exact. -/
theorem sum_memS_split {W : Finset ℕ} (a : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (J : ℕ) :
    ∑ m ∈ W, a m
      = (∑ m ∈ W, memSCoeff Pseq Qseq J a m)
        + ∑ m ∈ W.filter (fun m => ¬ MemS Pseq Qseq J m), a m := by
  have h := Finset.sum_filter_add_sum_filter_not W (fun m => MemS Pseq Qseq J m) a
  rw [← h]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [memSCoeff]

/-- **The 1-bounded triangle bound on the complement leg**: it is at most the complement
COUNT.  (This is where MRT's "and the second sum is `≪ #{n ∉ 𝒮}`" lives; no cancellation is
claimed or needed.) -/
theorem norm_sum_notMemS_le {W : Finset ℕ} {a : ℕ → ℂ} (ha : ∀ m ∈ W, ‖a m‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (J : ℕ) :
    ‖∑ m ∈ W.filter (fun m => ¬ MemS Pseq Qseq J m), a m‖
      ≤ ((W.filter (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun m hm => ha m (Finset.mem_filter.mp hm).1)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **THE M4-1 INSERT, at a general window.**  `‖∑_W a‖ ≤ ‖∑_W 1_𝒮 a‖ + #{m ∈ W : m ∉ 𝒮}`. -/
theorem norm_sum_memS_insert {W : Finset ℕ} {a : ℕ → ℂ} (ha : ∀ m ∈ W, ‖a m‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (J : ℕ) :
    ‖∑ m ∈ W, a m‖
      ≤ ‖∑ m ∈ W, memSCoeff Pseq Qseq J a m‖
        + ((W.filter (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ) := by
  rw [sum_memS_split a Pseq Qseq J]
  have h1 := norm_add_le (∑ m ∈ W, memSCoeff Pseq Qseq J a m)
    (∑ m ∈ W.filter (fun m => ¬ MemS Pseq Qseq J m), a m)
  have h2 := norm_sum_notMemS_le ha Pseq Qseq J
  linarith

/-- **The insert at the DOOR's carrier** (`M4Window.absWindowSum`, half-open on
`Ioc n (n+H)`).  The phase `e(αm)` has modulus one and rides through the insert untouched —
`memSCoeff_mul` is the only place it is moved. -/
theorem norm_absWindowSum_memS_insert {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (J H n : ℕ) (α : ℝ) :
    ‖absWindowSum a H n α‖
      ≤ ‖absWindowSum (memSCoeff Pseq Qseq J a) H n α‖
        + ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) := by
  have hphase : ∀ k : ℕ,
      ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((k : ℕ) : ℂ))‖ = 1 := by
    intro k
    rw [Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((k : ℕ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  have haw : ∀ m ∈ Finset.Ioc n (n + H),
      ‖a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ))‖ ≤ 1 := by
    intro m _
    rw [norm_mul, hphase m, mul_one]
    exact ha m
  have hins := norm_sum_memS_insert (W := Finset.Ioc n (n + H)) haw Pseq Qseq J
  have hrw : ∑ m ∈ Finset.Ioc n (n + H),
      memSCoeff Pseq Qseq J
        (fun k => a k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((k : ℕ) : ℂ))) m
      = absWindowSum (memSCoeff Pseq Qseq J a) H n α := by
    unfold absWindowSum
    exact Finset.sum_congr rfl (fun m _ => memSCoeff_mul Pseq Qseq J a _ m)
  rw [hrw] at hins
  have hgoal : ‖absWindowSum a H n α‖
      = ‖∑ m ∈ Finset.Ioc n (n + H),
          a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ))‖ := rfl
  have hcnt : ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ)
      = (((Finset.Ioc n (n + H)).filter (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ) := rfl
  rw [hgoal, hcnt]
  exact hins

/-- **The insert at MRT's own `shortSum` carrier** (`Lemma14.shortSum`, the `thm_A2′`
carrier).  Same statement, different window — the general lemma is the one that is proved. -/
theorem norm_shortSum_memS_insert {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (Pseq Qseq : ℕ → ℕ)
    (J : ℕ) (s0 : Finset ℕ) (x h : ℝ) :
    ‖shortSum a s0 x h‖
      ≤ ‖shortSum (memSCoeff Pseq Qseq J a) s0 x h‖
        + (((s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h)).filter
            (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ) := by
  simpa [shortSum] using
    norm_sum_memS_insert (W := s0.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h))
      (fun m _ => ha m) Pseq Qseq J

/-- The insert at the λ-datum (`M4Residue.liouvilleC`). -/
theorem norm_absWindowSum_memS_insert_liouville (Pseq Qseq : ℕ → ℕ) (J H n : ℕ) (α : ℝ) :
    ‖absWindowSum liouvilleC H n α‖
      ≤ ‖absWindowSum (memSCoeff Pseq Qseq J liouvilleC) H n α‖
        + ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) :=
  norm_absWindowSum_memS_insert liouvilleC_norm_le_one Pseq Qseq J H n α

/-- The insert at the row's own datum `λχ̄` (`CapFreeAssembly.liouChi`) — the `f` M4-5 plugs
into `thm_A2′`. -/
theorem norm_absWindowSum_memS_insert_liouChi {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Pseq Qseq : ℕ → ℕ) (J H n : ℕ) (α : ℝ) :
    ‖absWindowSum (liouChi χ) H n α‖
      ≤ ‖absWindowSum (memSCoeff Pseq Qseq J (liouChi χ)) H n α‖
        + ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) :=
  norm_absWindowSum_memS_insert (norm_liouChi_le_one χ) Pseq Qseq J H n α

/-! ## §2 — THE COMPLEMENT COUNT ON THE DOOR'S MEASURE

The freeze's HS-6 note: `hsieve_of_engine` counts on `Ioc X (2X)`, the door integrates short
windows against `logMeasure x ω`.  The exchange is a **double count**, and it is the only
new analysis in this row. -/

/-- **THE DOUBLE COUNT.**  Summing a nonnegative `f` over the short windows `(n, n+H]`,
`n ∈ (a, b]`, is at most `H` times the sum over the single window `(a, b+H]`: every `m` is
covered by at most `H` values of `n` (namely `m-H ≤ n < m`).

This is the Fubini exchange the door needs, and it is stated once. -/
theorem sum_window_double_count {f : ℕ → ℝ} (hf : ∀ m, 0 ≤ f m) (a b H : ℕ) :
    ∑ n ∈ Finset.Ioc a b, ∑ m ∈ Finset.Ioc n (n + H), f m
      ≤ (H : ℝ) * ∑ m ∈ Finset.Ioc a (b + H), f m := by
  have hinner : ∀ n ∈ Finset.Ioc a b,
      ∑ m ∈ Finset.Ioc n (n + H), f m
        = ∑ m ∈ Finset.Ioc a (b + H), (if n < m ∧ m ≤ n + H then f m else 0) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, by omega⟩, h1, h2⟩
    · rintro ⟨_, h⟩
      exact h
  calc ∑ n ∈ Finset.Ioc a b, ∑ m ∈ Finset.Ioc n (n + H), f m
      = ∑ n ∈ Finset.Ioc a b, ∑ m ∈ Finset.Ioc a (b + H),
          (if n < m ∧ m ≤ n + H then f m else 0) := Finset.sum_congr rfl hinner
    _ = ∑ m ∈ Finset.Ioc a (b + H), ∑ n ∈ Finset.Ioc a b,
          (if n < m ∧ m ≤ n + H then f m else 0) := Finset.sum_comm
    _ ≤ (H : ℝ) * ∑ m ∈ Finset.Ioc a (b + H), f m := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun m _ => ?_)
        have hsum : ∑ n ∈ Finset.Ioc a b, (if n < m ∧ m ≤ n + H then f m else 0)
            = (((Finset.Ioc a b).filter (fun n => n < m ∧ m ≤ n + H)).card : ℝ) * f m := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [hsum]
        have hcard : ((Finset.Ioc a b).filter (fun n => n < m ∧ m ≤ n + H)).card ≤ H := by
          have hsub : (Finset.Ioc a b).filter (fun n => n < m ∧ m ≤ n + H)
              ⊆ Finset.Ico (m - H) m := by
            intro n hn
            rw [Finset.mem_filter, Finset.mem_Ioc] at hn
            rw [Finset.mem_Ico]
            omega
          have hle := Finset.card_le_card hsub
          rw [Nat.card_Ico] at hle
          omega
        have hcardR : (((Finset.Ioc a b).filter (fun n => n < m ∧ m ≤ n + H)).card : ℝ)
            ≤ (H : ℝ) := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hcardR (hf m)

/-- **The double count at the complement indicator.**  The `n`-sum of the short-window
complement counts is at most `H` times ONE complement count, on `(x/ω, x+H]`. -/
theorem sum_notMemSCount_le (Pseq Qseq : ℕ → ℕ) (J H a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ)
      ≤ (H : ℝ) * (((Finset.Ioc a (b + H)).filter
          (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ) := by
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ (if ¬ MemS Pseq Qseq J m then (1 : ℝ) else 0) := by
    intro m; split_ifs <;> norm_num
  have hdc := sum_window_double_count hnn a b H
  rw [card_notMemS_eq_sum (Finset.Ioc a (b + H)) Pseq Qseq J]
  refine le_trans (le_of_eq ?_) hdc
  refine Finset.sum_congr rfl (fun n _ => ?_)
  exact card_notMemS_eq_sum (Finset.Ioc n (n + H)) Pseq Qseq J

/-- **The harmonic weight, spent on a BLOCK.**  On a sub-window `(a, b]` sitting at or above
the dyadic scale `X` (`X ≤ a`) every harmonic weight is `≤ 1/X`; combined with the double
count this prices the whole weighted `n`-sum of the block.

⟦WHY A BLOCK, AND NOT THE WHOLE DOOR WINDOW⟧ — the sharpest finding of this row.  The door
window `(x/ω, x]` spans a factor `ω ≥ 2` (`ChowlaRegime.hω`), and a single sieve block
`[X, 2X]` can contain `(x/ω, x+H]` only if `ω < 2`: `X ≤ x/ω` and `x + H ≤ 2X` force
`ω(x+H) ≤ 2x`.  So the M4-1 row composed against ONE `Ioc X (2X)` over the FULL door window
is not merely lossy, it is **vacuous**; and the crude whole-window weight `1/n ≤ ω/x` loses
`ω/log ω` against the normalisation `Z ≍ log ω`.  The dyadic split is therefore
load-bearing already here — it is not only M4-8's convenience.  This row supplies the
block; M4-8 supplies the cover. -/
theorem sum_notMemSCount_weighted_le {X a b : ℕ} (hX : 0 < (X : ℝ)) (hXa : X ≤ a)
    (Pseq Qseq : ℕ → ℕ) (J H : ℕ) :
    ∑ n ∈ Finset.Ioc a b, ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) * (n : ℝ)⁻¹
      ≤ (1 / (X : ℝ))
          * ((H : ℝ) * (((Finset.Ioc a (b + H)).filter
              (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ)) := by
  have hw : ∀ n ∈ Finset.Ioc a b, (n : ℝ)⁻¹ ≤ 1 / (X : ℝ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hXn : (X : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hXa hn.1.le
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hX hXn
  calc ∑ n ∈ Finset.Ioc a b, ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) * (n : ℝ)⁻¹
      ≤ ∑ n ∈ Finset.Ioc a b,
          ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) * (1 / (X : ℝ)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        exact mul_le_mul_of_nonneg_left (hw n hn) (Nat.cast_nonneg _)
    _ = (∑ n ∈ Finset.Ioc a b, ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ))
          * (1 / (X : ℝ)) := by rw [← Finset.sum_mul]
    _ ≤ ((H : ℝ) * (((Finset.Ioc a (b + H)).filter
            (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ)) * (1 / (X : ℝ)) := by
        refine mul_le_mul_of_nonneg_right (sum_notMemSCount_le Pseq Qseq J H _ _) ?_
        positivity
    _ = (1 / (X : ℝ))
          * ((H : ℝ) * (((Finset.Ioc a (b + H)).filter
              (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ)) := by ring

/-- **A pointwise-additive bound passes under `∫ · ∂logMeasure`.**  Proved through
`ShiftCorr.integral_logMeasure_eq`, so no integrability side condition is incurred (the
same route `M4Dyadic.integral_logMeasure_le_of_le` takes). -/
theorem integral_logMeasure_le_add {x ω : ℕ} {f g h : ℕ → ℝ}
    (hpt : ∀ n, f n ≤ g n + h n) :
    (∫ n, f n ∂(logMeasure x ω))
      ≤ (∫ n, g n ∂(logMeasure x ω)) + ∫ n, h n ∂(logMeasure x ω) := by
  rw [integral_logMeasure_eq, integral_logMeasure_eq, integral_logMeasure_eq,
    ← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => ?_)) ?_
  · have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have := hpt n
    nlinarith
  · exact inv_nonneg.mpr (Finset.sum_nonneg (fun n _ => by positivity))

/-- **THE VACUITY, KERNEL-CHECKED.**  For any door regime (`2 ≤ ω`, `2 ≤ x`) and any window
length `H ≥ 3`, the full door window `(x/ω, x+H]` does NOT fit in a single sieve block
`[X, 2X]` — for ANY `X`.  Hence a version of this row stated over the whole door window
against one `Ioc X (2X)` would have unsatisfiable hypotheses: it would be kernel-true and
consumable by nobody, the failure mode `TLGATES-SCOPE` found at `thm_a2'`.

The proof is three lines of endpoint arithmetic: the top `x+H` forces `x + H ≤ 2X`, the
bottom `x/ω + 1` forces `X ≤ x/ω + 1`, and `2·(x/ω) ≤ x` (from `ω ≥ 2`) then gives
`H ≤ 2`. -/
theorem door_window_not_one_block {x ω H X : ℕ} (hω : 2 ≤ ω) (_hx : 2 ≤ x) (hH : 3 ≤ H)
    (hcov : Finset.Ioc (x / ω) (x + H) ⊆ Finset.Icc X (2 * X)) : False := by
  have hdiv : 2 * (x / ω) ≤ x :=
    calc 2 * (x / ω) ≤ ω * (x / ω) := Nat.mul_le_mul hω (le_refl _)
      _ = (x / ω) * ω := Nat.mul_comm _ _
      _ ≤ x := Nat.div_mul_le_self x ω
  have hdle : x / ω ≤ x := Nat.div_le_self x ω
  obtain ⟨d, hd⟩ : ∃ d, x / ω = d := ⟨x / ω, rfl⟩
  rw [hd] at hcov hdiv hdle
  have hmemT : x + H ∈ Finset.Ioc d (x + H) := Finset.mem_Ioc.mpr ⟨by omega, le_refl _⟩
  have hmemB : d + 1 ∈ Finset.Ioc d (x + H) := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have h1 := Finset.mem_Icc.mp (hcov hmemT)
  have h2 := Finset.mem_Icc.mp (hcov hmemB)
  omega

/-- **THE DOOR NORMALISATION, SPENT.**  Under the gate `Z ≥ 1`
(`Z = ∑_{n ∈ (x/ω,x]} 1/n`, M4-8's `log ω` object — carried, never evaluated), any bound on
the harmonic `n`-sum is a bound on the `logMeasure`-`L¹` norm: the normalisation `Z⁻¹ ≤ 1`
can only help.  Proved through `ShiftCorr.integral_logMeasure_eq`, so no integrability side
condition is incurred. -/
theorem integral_logMeasure_le_of_weighted {x ω : ℕ} {f : ℕ → ℝ} {B : ℝ}
    (hZ : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) (hB0 : 0 ≤ B)
    (hB : ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ ≤ B) :
    (∫ n, f n ∂(logMeasure x ω)) ≤ B := by
  rw [integral_logMeasure_eq]
  set Z := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZdef
  have hZ0 : (0 : ℝ) < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZinv : Z⁻¹ ≤ 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hZ
    simpa using h
  calc Z⁻¹ * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹
      ≤ Z⁻¹ * B := mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hZinv hB0
    _ = B := one_mul B

/-! ## §3 — THE HALF-OPEN ENDPOINT, AND THE `hsieve` CITATION

`SieveGlue.lean:75–79` (the HS-6 residual): `typical_density_le` — hence
`hsieve_of_engine` — counts on the half-open `Ioc X (2X)`, while MR index the long sum by
the CLOSED `[X, 2X]`.  The single uncovered lattice point `m = X` is paid here, honestly:
one term, `≤ 1` in the count, `≤ 1/X` after normalisation. -/

/-- **THE ENDPOINT, PAID.**  Any window inside the closed `[X, 2X]` has complement count at
most the half-open count plus `1`. -/
theorem card_notMemS_of_subset_Icc {Wm : Finset ℕ} {X : ℕ} (Pseq Qseq : ℕ → ℕ) (J : ℕ)
    (hsub : Wm ⊆ Finset.Icc X (2 * X)) :
    ((Wm.filter (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ)
      ≤ (((Finset.Ioc X (2 * X)).filter (fun m => ¬ MemS Pseq Qseq J m)).card : ℝ) + 1 := by
  have hmono : (Wm.filter (fun m => ¬ MemS Pseq Qseq J m)).card
      ≤ ((Finset.Icc X (2 * X)).filter (fun m => ¬ MemS Pseq Qseq J m)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  have hstep : ((Finset.Icc X (2 * X)).filter (fun m => ¬ MemS Pseq Qseq J m)).card
      ≤ ((Finset.Ioc X (2 * X)).filter (fun m => ¬ MemS Pseq Qseq J m)).card + 1 := by
    have hsub2 : (Finset.Icc X (2 * X)).filter (fun m => ¬ MemS Pseq Qseq J m)
        ⊆ insert X ((Finset.Ioc X (2 * X)).filter (fun m => ¬ MemS Pseq Qseq J m)) := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      rcases eq_or_lt_of_le hm.1.1 with heq | hlt
      · exact heq ▸ Finset.mem_insert_self X _
      · exact Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlt, hm.1.2⟩, hm.2⟩)
    exact le_trans (Finset.card_le_card hsub2) (Finset.card_insert_le _ _)
  have : (Wm.filter (fun m => ¬ MemS Pseq Qseq J m)).card
      ≤ ((Finset.Ioc X (2 * X)).filter (fun m => ¬ MemS Pseq Qseq J m)).card + 1 :=
    le_trans hmono hstep
  exact_mod_cast this

/-- **THE COMPOSED COUNT — `hsieve_of_engine`, CONSUMED.**  For ANY window inside the closed
dyadic block `[X, 2X]`, the complement count is at most `C·X·(the sieve mass) + 1`, with `C`
the single shared constant of `card_blockfree_le`.  The `+1` is §3's endpoint, and nothing
else in the chain is lossy.

The three gates are `hsieve_of_engine`'s own (HS-3): the large-`X` guard `√log X ≥ 100`
(`hbig_of_floor`), MR's regularity `log 𝒬_j ≤ √log X` (`hreg_of_small_h`), and the
error-domination inequality (`herr_of_floor`).  They are carried, never discharged here. -/
theorem notMemS_window_count_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J X : ℕ) (Wm : Finset ℕ),
      1 ≤ A → 1 ≤ G → 1 ≤ M →
      Wm ⊆ Finset.Icc X (2 * X) → 0 < (X : ℝ) →
      (100 : ℝ) ≤ Real.sqrt (Real.log X) →
      (∀ j ∈ Finset.Icc 1 J,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X)) →
      (∀ j ∈ Finset.Icc 1 J,
        ((Nat.sqrt X : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      ((Wm.filter (fun m => ¬ MemS (calP A G) (calQK A G M) J m)).card : ℝ)
        ≤ C * (X : ℝ) * ratioSumK A G M J + 1 := by
  obtain ⟨C, hC, heng⟩ := hsieve_of_engine
  refine ⟨C, hC, ?_⟩
  intro A G M J X Wm hA hG hM hsub hX hbig hreg herr
  have hIoc := heng A G M J X (Finset.Ioc X (2 * X)) hA hG hM (subset_refl _) hX hbig hreg herr
  have hIoc' : (((Finset.Ioc X (2 * X)).filter
      (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
      ≤ C * (X : ℝ) * ratioSumK A G M J := by
    have hmul := mul_le_mul_of_nonneg_left hIoc hX.le
    rw [← mul_assoc, mul_one_div, div_self (ne_of_gt hX), one_mul] at hmul
    calc (((Finset.Ioc X (2 * X)).filter
          (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
        ≤ (X : ℝ) * (C * ratioSumK A G M J) := hmul
      _ = C * (X : ℝ) * ratioSumK A G M J := by ring
  exact le_trans (card_notMemS_of_subset_Icc _ _ J hsub) (by linarith)

/-! ## §4 — THE M-GATE

`SeamNumber.sum_ratioK_le_basel` collects the `j`-sum at the sharp `π²/6`; the freeze's
gate is `8C/δ ≤ M`. -/

/-- **The assembled sieve mass**: `C·∑_j log 𝒫_j/log 𝒬_j ≤ C·π²/(6M)`, uniformly in `J`
(`sum_ratioK_le_basel`, the Basel constant — `SeamCalibrationK.sum_ratioK_le`'s `2/M` is the
cruder sibling). -/
theorem sieve_mass_le_basel {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (J : ℕ)
    {C : ℝ} (hC : 0 ≤ C) :
    C * ratioSumK A G M J ≤ C * (Real.pi ^ 2 / (6 * (M : ℝ))) :=
  mul_le_mul_of_nonneg_left (sum_ratioK_le_basel hA hG hM J) hC

/-- `π² ≤ 10` — the only numeral this section evaluates. -/
private lemma pi_sq_le_ten : Real.pi ^ 2 ≤ 10 := by
  nlinarith [Real.pi_lt_d2, Real.pi_gt_three]

/-- **THE M-GATE AT THE FREEZE'S OWN SCALE.**  `8C/δ ≤ M ⟹ C·∑_j ≤ δ/4`.

⟦THE HONEST CONSTANT⟧  At the Basel collector the gate `M ≥ 8C/δ` delivers
`C·π²/(6M) ≤ π²δ/48 ≈ 0.206·δ`, i.e. `δ/4` with room, NOT `δ/8`.  `δ/8` needs
`M ≥ (4π²/3)(C/δ) ≈ 13.16·C/δ`; `sieve_mass_le_eighth` states it at the round `16C/δ`.
Both are shipped so that the consumer picks the gate it can afford — the freeze's
`8C/δ` is `SieveGlue.eq28_clears_of_M_const`'s gate, where the coefficient is `2C`, not
`C`, and the target is `δ/2`. -/
theorem sieve_mass_le_quarter {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (J : ℕ)
    {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ) (hMδ : 8 * C / δ ≤ (M : ℝ)) :
    C * ratioSumK A G M J ≤ δ / 4 := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hC0 : (0 : ℝ) < C := by linarith
  have hbasel := sieve_mass_le_basel hA hG hM J hC0.le
  have hMδ' : 8 * C ≤ (M : ℝ) * δ := by
    rw [div_le_iff₀ hδ] at hMδ; linarith
  have hrw : C * (Real.pi ^ 2 / (6 * (M : ℝ))) = C * Real.pi ^ 2 / (6 * (M : ℝ)) :=
    (mul_div_assoc C (Real.pi ^ 2) (6 * (M : ℝ))).symm
  have hkey : C * (Real.pi ^ 2 / (6 * (M : ℝ))) ≤ δ / 4 := by
    rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    nlinarith [mul_le_mul_of_nonneg_left pi_sq_le_ten hC0.le, hMδ']
  linarith

/-- **THE DOUBLED GATE.**  `16C/δ ≤ M ⟹ C·∑_j ≤ δ/8` — the `δ/8`-grade the M4-7 budget
asks for, at the honest gate.  (`13.16·C/δ` suffices; `16` is the round number.) -/
theorem sieve_mass_le_eighth {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (J : ℕ)
    {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 < δ) (hMδ : 16 * C / δ ≤ (M : ℝ)) :
    C * ratioSumK A G M J ≤ δ / 8 := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hC0 : (0 : ℝ) < C := by linarith
  have hbasel := sieve_mass_le_basel hA hG hM J hC0.le
  have hMδ' : 16 * C ≤ (M : ℝ) * δ := by
    rw [div_le_iff₀ hδ] at hMδ; linarith
  have hrw : C * (Real.pi ^ 2 / (6 * (M : ℝ))) = C * Real.pi ^ 2 / (6 * (M : ℝ)) :=
    (mul_div_assoc C (Real.pi ^ 2) (6 * (M : ℝ))).symm
  have hkey : C * (Real.pi ^ 2 / (6 * (M : ℝ))) ≤ δ / 8 := by
    rw [hrw, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
    nlinarith [mul_le_mul_of_nonneg_left pi_sq_le_ten hC0.le, hMδ']
  linarith

/-! ## §5 — THE EXIT

Two statements, and the seam between them is exactly the HS-6 residual.

* `m4_sieve_block_mass` — the **priced block**: on one sieve block, the harmonic mass of the
  complement count is `≤ (δ/4)·H + H/X`, under the M-gate and HS-3's three gates.  This is
  the whole sieve leg of M4-1, `hsieve_of_engine` consumed.
* `m4_sieve_insert` — the **door exit**: the `logMeasure`-`L¹` insert, with the total
  complement mass carried as `B`.  M4-8 supplies `B` by summing `m4_sieve_block_mass` over
  M4-4's dyadic cover (`M4Dyadic.sum_dyadCover`); it cannot be supplied by a single block,
  see `sum_notMemSCount_weighted_le`'s ⟦WHY A BLOCK⟧.

Everything is carried and nothing is evaluated: the door normalisation `Z ≥ 1`, the block
containment `Ioc a (b+H) ⊆ Icc X (2X)`, the block-scale gate `X ≤ a`, the M-gate `8C/δ ≤ M`,
and HS-3's `√log X ≥ 100` / regularity / error-domination. -/

/-- **`m4_sieve_block_mass` — THE PRICED BLOCK.**  On a sub-window `(a, b]` of the door
window lying in the sieve block `[X, 2X]`,

`∑_{n ∈ (a,b]} #{m ∈ (n, n+H] : m ∉ 𝒮}/n ≤ (δ/4)·H + H/X`,

with `𝒮` the K-family `MemS (calP A G) (calQK A G M) J` — the SAME family the sieve mass
names (`SieveGlue`'s HS-5 pin, taken by instantiation).

⟦THE TWO ERROR TERMS, NAMED⟧
* `(δ/4)·H` — the sieve mass `C·∑_j log 𝒫_j/log 𝒬_j`, under the M-gate `8C/δ ≤ M` (§4;
  `sieve_mass_le_eighth` gives `δ/8` at `16C/δ`).
* `H/X` — the half-open endpoint `m = X` of §3: `1/X`-grade, ONE lattice point, bounded
  trivially, spread over the `≤ H` windows that see it.

⟦ONE CONSTANT⟧  The `∃ C` is `card_blockfree_le`'s, opened once and threaded into the
M-gate — the discipline `SieveGlue.sec9_eq28_exit_calFamily` states. -/
theorem m4_sieve_block_mass :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J X H a b : ℕ) (δ : ℝ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 8 * C / δ ≤ (M : ℝ) →
      0 < (X : ℝ) → X ≤ a → Finset.Ioc a (b + H) ⊆ Finset.Icc X (2 * X) →
      (100 : ℝ) ≤ Real.sqrt (Real.log X) →
      (∀ j ∈ Finset.Icc 1 J,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X)) →
      (∀ j ∈ Finset.Icc 1 J,
        ((Nat.sqrt X : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      ∑ n ∈ Finset.Ioc a b,
          ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) * (n : ℝ)⁻¹
        ≤ δ / 4 * (H : ℝ) + (H : ℝ) / (X : ℝ) := by
  obtain ⟨C, hC, hcnt⟩ := notMemS_window_count_le
  refine ⟨C, hC, ?_⟩
  intro A G M J X H a b δ hA hG hM hδ hMδ hX hXa hcov hbig hreg herr
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hC0 : (0 : ℝ) < C := by linarith
  have hS0 : 0 ≤ ratioSumK A G M J := ratioSumK_nonneg hA hG hM J
  -- ⟦STEP 1: the double count and the block weight⟧
  have hwt := sum_notMemSCount_weighted_le (b := b) hX hXa (calP A G) (calQK A G M) J H
  -- ⟦STEP 2: the count, by `hsieve_of_engine` + the endpoint⟧
  have hNc := hcnt A G M J X (Finset.Ioc a (b + H)) hA hG hM hcov hX hbig hreg herr
  -- ⟦STEP 3: the M-gate⟧
  have hmass := sieve_mass_le_quarter hA hG hM J hC hδ hMδ
  -- ⟦STEP 4: the arithmetic⟧
  set Nc := (((Finset.Ioc a (b + H)).filter
    (fun m => ¬ MemS (calP A G) (calQK A G M) J m)).card : ℝ) with hNcdef
  have hNc0 : (0 : ℝ) ≤ Nc := Nat.cast_nonneg _
  have hXinv : (0 : ℝ) ≤ 1 / (X : ℝ) := by positivity
  have h1 : (1 / (X : ℝ)) * ((H : ℝ) * Nc)
      ≤ (1 / (X : ℝ)) * ((H : ℝ) * (C * (X : ℝ) * ratioSumK A G M J + 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNc hH0) hXinv
  have h2 : (1 / (X : ℝ)) * ((H : ℝ) * (C * (X : ℝ) * ratioSumK A G M J + 1))
      = (H : ℝ) * (C * ratioSumK A G M J) + (H : ℝ) / (X : ℝ) := by
    field_simp
  have h3 : (H : ℝ) * (C * ratioSumK A G M J) ≤ (H : ℝ) * (δ / 4) :=
    mul_le_mul_of_nonneg_left hmass hH0
  rw [hNcdef] at hwt
  linarith

/-- **`m4_sieve_insert` — THE M4-1 DOOR EXIT.**  At a general 1-bounded coefficient sequence
`a`, the door's `logMeasure`-`L¹` window norm is bounded by the SIEVED one plus the carried
complement mass `B`:

`∫‖∑_{n<m≤n+H} a(m)e(αm)‖ dμ ≤ ∫‖∑ 1_𝒮(m)a(m)e(αm)‖ dμ + B`.

The insert identity is exact and the triangle bound is the only inequality on the
coefficient side; `B` is the harmonic mass of the complement count, which
`m4_sieve_block_mass` prices one block at a time.  `𝒮` is left as a general
`MemS Pseq Qseq J` here — the K-family pin enters with `B`, not with the insert. -/
theorem m4_sieve_insert {x ω : ℕ} {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1)
    (hZ : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
    (Pseq Qseq : ℕ → ℕ) (J H : ℕ) (α : ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∑ n ∈ Finset.Ioc (x / ω) x,
        ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) * (n : ℝ)⁻¹ ≤ B) :
    (∫ n, ‖absWindowSum a H n α‖ ∂(logMeasure x ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff Pseq Qseq J a) H n α‖ ∂(logMeasure x ω)) + B := by
  have hadd : (∫ n, ‖absWindowSum a H n α‖ ∂(logMeasure x ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff Pseq Qseq J a) H n α‖ ∂(logMeasure x ω))
        + ∫ n, ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) ∂(logMeasure x ω) :=
    integral_logMeasure_le_add
      (fun n => norm_absWindowSum_memS_insert ha Pseq Qseq J H n α)
  have hcomp : (∫ n, ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) ∂(logMeasure x ω)) ≤ B :=
    integral_logMeasure_le_of_weighted hZ hB0 hB
  linarith

/-- The door exit at the λ-datum (`M4Residue.liouvilleC`) — the raw door window. -/
theorem m4_sieve_insert_liouville {x ω : ℕ}
    (hZ : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
    (Pseq Qseq : ℕ → ℕ) (J H : ℕ) (α : ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∑ n ∈ Finset.Ioc (x / ω) x,
        ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) * (n : ℝ)⁻¹ ≤ B) :
    (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure x ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff Pseq Qseq J liouvilleC) H n α‖
            ∂(logMeasure x ω)) + B :=
  m4_sieve_insert liouvilleC_norm_le_one hZ Pseq Qseq J H α hB0 hB

/-- The door exit at the row's own datum `λχ̄` (`CapFreeAssembly.liouChi`) — the `f` M4-5
plugs into `thm_A2′`, with the `1_𝒮` already inserted. -/
theorem m4_sieve_insert_liouChi {x ω q : ℕ} (χ : DirichletCharacter ℂ q)
    (hZ : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
    (Pseq Qseq : ℕ → ℕ) (J H : ℕ) (α : ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∑ n ∈ Finset.Ioc (x / ω) x,
        ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) * (n : ℝ)⁻¹ ≤ B) :
    (∫ n, ‖absWindowSum (liouChi χ) H n α‖ ∂(logMeasure x ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff Pseq Qseq J (liouChi χ)) H n α‖
            ∂(logMeasure x ω)) + B :=
  m4_sieve_insert (norm_liouChi_le_one χ) hZ Pseq Qseq J H α hB0 hB

end Salt.MR

end
