/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Close

/-!
# ⟦OPEN BRIDGE 1⟧ — THE RESIDUE-CLASS SPLIT OF THE WINDOW SUM (`M4BridgeResidue`)

Source: `M4Close`'s module header, ⟦THE FIVE OPEN BRIDGES⟧ item 1 —

> the residue-class split of the window sum at a tight-major `α` — `α = a/q + θ`,
> `e(αm) = e(am/q)e(θm)`, `e(am/q)` constant on classes mod `q`; the triangle inequality
> over the `q` classes.  §6 below lands the *character* half of this bridge at the honest
> sum-side datum (`sum_liou_modEq_residue_eq`, `inv_totient_sum_le`); what is still missing
> is the **window partition** and the **constancy of the rational phase**.

This file lands exactly what that sentence names as missing, and then bolts it onto the
landed character half.  Four jobs, and only these four:

1. **The window partition mod `q`** (§1).  `Finset.Ioc n (n+H)` is the disjoint union of its
   `q` residue classes `windowClass H n q r`, `r < q`.  Route:
   `Finset.sum_fiberwise_of_maps_to` at the fibre map `m ↦ m % q`, then one
   `Finset.filter_congr` to re-spell the fibre test `m % q = r` as `Nat.ModEq q m r` — the
   `ℕ`-form the corpus speaks (`M4Chars` §8, `M4Residue` §4).  The partition is stated at a
   general `AddCommMonoid`, so the cardinality identity `∑_{r<q} #class = H` is the same
   lemma at `M = ℕ` (`sum_card_windowClass`) — the half-open window paying off again.

2. **The rational-phase constancy** (§2).  `e(αm) = e((a₀/q)m)·e(θm)` (`exp_phase_split`,
   pure `Complex.exp_add`), and `e((a₀/q)m) = e(a₀r/q)` whenever `m ≡ r (mod q)`
   (`exp_eq_ratPhase_of_modEq`).  The second is the only arithmetic step in the file:
   `Nat.modEq_iff_dvd` gives `(q:ℤ) ∣ r − m`, the `q` cancels against the denominator, and
   what is left is `exp (integer · 2πi) = 1` (`Complex.exp_int_mul_two_pi_mul_I`).

3. **THE SPLIT** (§3).  `absWindowSum a H n (a₀/q + θ) = ∑_{r<q} ratPhase a₀ q r ·
   classPhaseSum a H n q r θ` (`absWindowSum_residue_split`), at a *general* coefficient
   sequence `a : ℕ → ℂ` — no `λ`, no 1-boundedness, no arc hypothesis.  The norm corollary
   `norm_absWindowSum_residue_split_le` drops the unimodular coefficients, and
   `norm_absWindowSum_le_class_sum_of_nearRatTight` is the arc-facing form: it *produces*
   the witnesses `(a₀, q)` and the drift datum `|θ| ≤ Q/(qH)` that ⟦BRIDGE 2⟧'s Abel step
   needs, alongside the bound.

4. **The composition hook to `M4Close` §6** (§4).  `windowClass` is *definitionally*
   `sum_liou_modEq_residue_eq`'s `S.filter (· ≡ b [MOD q])` at `S := Finset.Ioc n (n+H)`, so
   the character decomposition fires on each class by `rfl`-transport
   (`sum_windowClass_liou_eq`), and `inv_totient_sum_le` converts a `χ`-uniform bound into a
   per-class bound with the `1/φ(q)` cancelled exactly
   (`norm_sum_windowClass_liou_le_of_uniform`).  The partial-sum family
   `residueClassOn q r (Finset.Ioc n K)` — what Abel summation differences — is served by
   the same adapter at general `S`, and `windowClass_partial` identifies it with the
   `m ≤ K` truncation of the class.

## Conventions pinned in this file

* **The phase convention is `M4Window`'s, byte-verbatim**: every phase is spelled
  `Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((m : ℕ) : ℂ))` with `β : ℝ`.
  This is what `absWindowSum` (`M4Window.lean:97`) natively carries, so the split is stated
  in it and no `eR` (`Salt/ExpSum/Basic.lean:43`) appears anywhere below.  ⟦SEAM⟧ The
  `Complex.exp ↔ eR` transcription is ⟦BRIDGE 2⟧'s job (`M4Abel` speaks `eR`); this file
  hands it `classPhaseSum` in the `Complex.exp` spelling and nothing else.
* **Half-open**: the window is `Finset.Ioc n (n+H) = {n+1,…,n+H}`, `M4Window`'s convention,
  and the classes inherit it verbatim (`windowClass` is a `filter` of it, never a
  re-indexing).  `sum_card_windowClass` is the audit: the `q` class cardinalities sum to `H`
  on the nose.
* **`0 < q` is the geometry hypothesis, `[NeZero q]` the algebra one.**  §§1–3 carry
  `0 < q` because that is what `NearRatTight` (`BigXiArc.lean:566`) produces; §4 carries
  `[NeZero q]` because that is what `M4Chars`/`M4Close` §6 demand.  The bridge is
  `NeZero.of_pos` and it is taken exactly once, in
  `norm_absWindowSum_le_liou_class_bound_of_nearRatTight`.
* **`Nat.ModEq`, not `ZMod`.**  The class test is `m ≡ r [MOD q]` throughout, matching
  `M4Chars` §8 (`sum_lam_modEq_residue_eq`) and `M4Residue` §4 (`modEq_dilate_iff`).  The
  single `ZMod` occurrence is the character argument `((r : ℕ) : ZMod q)`, which is
  `M4Close` §6's own spelling.
* **No log scale.**  This file is pure algebra: it contains no `Real.log`, no `arcDen`, no
  `W`, and hence cannot commit the four-log-scales error (M4 trap sheet #8).  The only
  quantitative object it ever sees is `NearRatTight`'s `Q`, carried opaquely.

## What this file does NOT prove — the two seams, named

* ⟦SEAM A — the non-coprime classes⟧.  The character decomposition of §4 needs
  `Nat.Coprime q r`.  The `q − φ(q)` classes with `d₀ := (r,q) > 1` are NOT handled here:
  they route through `M4Residue.residue_split_dilate_door` (⟦BRIDGE 3⟧), which divides them
  by `d₀` and lands them back as coprime classes to a smaller modulus.  The split is
  *stated* so that this is visible: `norm_absWindowSum_split_coprime_add` cuts the `r`-sum
  into its coprime and non-coprime halves at exactly the place `M4Residue` plugs in.
* ⟦SEAM B — the `θ`-phase removal⟧.  `classPhaseSum` still carries `e(θm)`.  Stripping it is
  Abel summation against the partial sums of the class (⟦BRIDGE 2⟧); §4 supplies those
  partial sums (`windowClass_partial`, `norm_sum_residueClassOn_Ioc_liou_le_of_uniform`) in
  the `K`-uniform shape that step consumes, and stops there.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

/-! ## §1 — the window partition mod `q`

The classes are `filter`s of the window, never re-indexings: nothing about the half-open
convention is touched, and `windowClass` inherits `Finset.Ioc`'s endpoints verbatim. -/

/-- **A residue class inside a finite index set.**  `residueClassOn q r S = {m ∈ S : m ≡ r
(mod q)}`, with the test written in `ℕ` (`Nat.ModEq`) — the spelling `M4Chars` §8 and
`M4Residue` §4 both speak.  Stated at a general `S` because ⟦BRIDGE 2⟧'s Abel step needs the
same class on the truncated windows `Finset.Ioc n K`, not only on the full one. -/
def residueClassOn (q r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun m => m ≡ r [MOD q])

/-- **The `r`-th residue class of the door window**, `{n < m ≤ n+H : m ≡ r (mod q)}`. -/
def windowClass (H n q r : ℕ) : Finset ℕ :=
  residueClassOn q r (Finset.Ioc n (n + H))

theorem mem_residueClassOn {q r : ℕ} {S : Finset ℕ} {m : ℕ} :
    m ∈ residueClassOn q r S ↔ m ∈ S ∧ m ≡ r [MOD q] := by
  simp [residueClassOn]

theorem mem_windowClass {H n q r m : ℕ} :
    m ∈ windowClass H n q r ↔ (n < m ∧ m ≤ n + H) ∧ m ≡ r [MOD q] := by
  simp [windowClass, residueClassOn, Finset.mem_Ioc, and_assoc]

theorem windowClass_subset (H n q r : ℕ) : windowClass H n q r ⊆ Finset.Ioc n (n + H) :=
  Finset.filter_subset _ _

/-- **THE WINDOW PARTITION.**  Summing over the half-open window `Ioc n (n+H)` is summing
over its `q` residue classes.  Route: `Finset.sum_fiberwise_of_maps_to` at the fibre map
`m ↦ m % q` (which lands in `Finset.range q` precisely because `0 < q`), then one
`Finset.filter_congr` re-spelling `m % q = r` as `m ≡ r [MOD q]` — legitimate for `r < q`,
where `r % q = r`.

Stated at a general `AddCommMonoid` so that the cardinality audit (`sum_card_windowClass`)
is this same lemma at `M := ℕ`. -/
theorem sum_window_residue_partition {M : Type*} [AddCommMonoid M] {q : ℕ} (hq : 0 < q)
    (H n : ℕ) (f : ℕ → M) :
    ∑ m ∈ Finset.Ioc n (n + H), f m
      = ∑ r ∈ Finset.range q, ∑ m ∈ windowClass H n q r, f m := by
  have hmaps : ∀ m ∈ Finset.Ioc n (n + H), m % q ∈ Finset.range q := fun m _ =>
    Finset.mem_range.mpr (Nat.mod_lt _ hq)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrq : r % q = r := Nat.mod_eq_of_lt (Finset.mem_range.mp hr)
  have hfil : (Finset.Ioc n (n + H)).filter (fun m => m % q = r) = windowClass H n q r := by
    simp only [windowClass, residueClassOn]
    exact Finset.filter_congr fun m _ => by simp only [Nat.ModEq, hrq]
  rw [hfil]

/-- **The cardinality audit.**  The `q` class cardinalities sum to `H` on the nose — the
half-open window's card being `H` exactly (`Nat.card_Ioc`), so the partition neither creates
nor loses a term. -/
theorem sum_card_windowClass {q : ℕ} (hq : 0 < q) (H n : ℕ) :
    ∑ r ∈ Finset.range q, (windowClass H n q r).card = H := by
  have h := sum_window_residue_partition (M := ℕ) hq H n (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ioc] at h
  omega

/-! ## §2 — the phase algebra: the split, and the constancy of the rational part -/

/-- **THE RATIONAL PHASE** `e(a₀ r / q)`, in `M4Window`'s spelling.  This is the constant the
window sum's phase collapses to on the class `m ≡ r (mod q)`. -/
def ratPhase (a₀ : ℤ) (q r : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((a₀ : ℝ) / (q : ℝ) : ℝ) : ℂ) * ((r : ℕ) : ℂ))

/-- **THE `θ`-PHASED CLASS SUM** `∑_{m ∈ class} a(m) e(θm)`.  The summand is byte-identical
to `absWindowSum`'s (`M4Window.lean:97`); only the index set changes.  ⟦SEAM B⟧ the `e(θm)`
is still present: removing it is ⟦BRIDGE 2⟧'s Abel step. -/
def classPhaseSum (a : ℕ → ℂ) (H n q r : ℕ) (θ : ℝ) : ℂ :=
  ∑ m ∈ windowClass H n q r, a m *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ) * ((m : ℕ) : ℂ))

/-- The additive phase has modulus 1.  (`M4Window`'s `norm_exp_phase` is `private`; this is
the same one-line fact, re-proved rather than cross-imported.) -/
private lemma norm_exp_phase' (β : ℝ) (k : ℕ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((k : ℕ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * ((k : ℕ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The rational phase is unimodular — the only property of it the norm corollary uses. -/
theorem norm_ratPhase (a₀ : ℤ) (q r : ℕ) : ‖ratPhase a₀ q r‖ = 1 :=
  norm_exp_phase' _ r

/-- **THE PHASE SPLIT** `e(αm) = e((a₀/q)m)·e(θm)` at `α = a₀/q + θ`.  Pure `Complex.exp_add`
plus the `ℝ → ℂ` transport of the sum; no hypothesis on `q` (at `q = 0` both sides read
`a₀/0 = 0`, and the identity is still true). -/
theorem exp_phase_split (a₀ : ℤ) (q : ℕ) (θ : ℝ) (m : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (((a₀ : ℝ) / (q : ℝ) + θ : ℝ) : ℂ) * ((m : ℕ) : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I
            * (((a₀ : ℝ) / (q : ℝ) : ℝ) : ℂ) * ((m : ℕ) : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ) * ((m : ℕ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **THE RATIONAL-PHASE CONSTANCY** — the arithmetic heart of the bridge.  For `m ≡ r
(mod q)` and `0 < q`,

`e((a₀/q)·m) = e(a₀ r/q) = ratPhase a₀ q r`,

i.e. the rational part of the phase is CONSTANT on each residue class.  Route:
`Nat.modEq_iff_dvd` writes `(r:ℤ) − (m:ℤ) = q·k`; the `q` cancels against the denominator
(this is the only place `q ≠ 0` is used); what is left is `exp (a₀k · 2πi) = 1`
(`Complex.exp_int_mul_two_pi_mul_I`). -/
theorem exp_eq_ratPhase_of_modEq {q : ℕ} (hq : 0 < q) (a₀ : ℤ) {r m : ℕ}
    (h : m ≡ r [MOD q]) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * (((a₀ : ℝ) / (q : ℝ) : ℝ) : ℂ) * ((m : ℕ) : ℂ))
      = ratPhase a₀ q r := by
  have hq0 : ((q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp h
  have hrm : ((r : ℕ) : ℂ) = ((m : ℕ) : ℂ) + ((q : ℕ) : ℂ) * (k : ℂ) := by
    have hkC := congrArg (fun z : ℤ => (z : ℂ)) hk
    push_cast at hkC
    linear_combination hkC
  have hstep : (2 * (Real.pi : ℂ) * Complex.I
        * (((a₀ : ℝ) / (q : ℝ) : ℝ) : ℂ) * ((r : ℕ) : ℂ))
      = (2 * (Real.pi : ℂ) * Complex.I
            * (((a₀ : ℝ) / (q : ℝ) : ℝ) : ℂ) * ((m : ℕ) : ℂ))
        + ((a₀ * k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hqa : (a₀ : ℂ) / ((q : ℕ) : ℂ) * ((q : ℕ) : ℂ) = (a₀ : ℂ) :=
      div_mul_cancel₀ _ hq0
    rw [hrm]
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * hqa
  rw [ratPhase, hstep, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## §3 — THE SPLIT, and the norm corollary -/

/-- **THE RESIDUE-CLASS SPLIT OF THE WINDOW SUM** (⟦OPEN BRIDGE 1⟧, the window half).  At
`α = a₀/q + θ` with `0 < q`, and at a *general* coefficient sequence `a : ℕ → ℂ`,

`∑_{n<m≤n+H} a(m) e(αm) = ∑_{r<q} e(a₀r/q) · ∑_{n<m≤n+H, m≡r (q)} a(m) e(θm)`.

The rational phase has been pulled out of each class sum as a constant (§2), and the classes
tile the window exactly (§1).  No 1-boundedness, no arc hypothesis, no datum: those enter
only in the corollaries. -/
theorem absWindowSum_residue_split (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q) (a₀ : ℤ)
    (θ : ℝ) :
    absWindowSum a H n ((a₀ : ℝ) / (q : ℝ) + θ)
      = ∑ r ∈ Finset.range q, ratPhase a₀ q r * classPhaseSum a H n q r θ := by
  unfold absWindowSum
  rw [sum_window_residue_partition hq H n]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [classPhaseSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmod : m ≡ r [MOD q] := (mem_windowClass.mp hm).2
  rw [exp_phase_split a₀ q θ m, exp_eq_ratPhase_of_modEq hq a₀ hmod]
  ring

/-- **THE NORM COROLLARY.**  The `q` coefficients `e(a₀r/q)` are unimodular, so the triangle
inequality over the classes costs nothing:

`‖∑_{n<m≤n+H} a(m) e(αm)‖ ≤ ∑_{r<q} ‖∑_{m≡r (q)} a(m) e(θm)‖`. -/
theorem norm_absWindowSum_residue_split_le (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q)
    (a₀ : ℤ) (θ : ℝ) :
    ‖absWindowSum a H n ((a₀ : ℝ) / (q : ℝ) + θ)‖
      ≤ ∑ r ∈ Finset.range q, ‖classPhaseSum a H n q r θ‖ := by
  rw [absWindowSum_residue_split a H n hq a₀ θ]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun r _ => by rw [norm_mul, norm_ratPhase, one_mul]

/-- The norm corollary with `α` supplied as a hypothesis rather than as a literal sum — the
form the arc adapter applies, `θ` being `α − a₀/q` and hence not syntactically separable. -/
theorem norm_absWindowSum_residue_split_le_of_eq (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q)
    (a₀ : ℤ) {α θ : ℝ} (hα : α = (a₀ : ℝ) / (q : ℝ) + θ) :
    ‖absWindowSum a H n α‖ ≤ ∑ r ∈ Finset.range q, ‖classPhaseSum a H n q r θ‖ := by
  subst hα
  exact norm_absWindowSum_residue_split_le a H n hq a₀ θ

/-- **THE ARC-FACING FORM.**  At a tight-major `α` the split fires with the witnesses that
`NearRatTight` itself provides, and the drift datum `|θ| ≤ Q/(qH)` is handed out alongside
the bound: that inequality is precisely ⟦BRIDGE 2⟧'s input
(`M4Abel.norm_phase_sum_arcDen_drift`, which prices `∑‖e(θ(m+1)) − e(θm)‖` by `|θ|·length`).

The existential is over `(a₀, q)` because `NearRatTight` (`BigXiArc.lean:566`) is itself an
existential: the split's modulus is the arc's own witness denominator, never a choice made
here. -/
theorem norm_absWindowSum_le_class_sum_of_nearRatTight {Q : ℝ} {H : ℕ} {α : ℝ}
    (harc : NearRatTight Q H α) (a : ℕ → ℂ) (n : ℕ) :
    ∃ (a₀ : ℤ) (q : ℕ), 0 < q ∧ (q : ℝ) ≤ Q ∧
      |α - (a₀ : ℝ) / (q : ℝ)| ≤ Q / ((q : ℝ) * (H : ℝ)) ∧
      ‖absWindowSum a H n α‖
        ≤ ∑ r ∈ Finset.range q, ‖classPhaseSum a H n q r (α - (a₀ : ℝ) / (q : ℝ))‖ := by
  obtain ⟨a₀, q, hq, hqQ, hd⟩ := harc
  have hα : α = (a₀ : ℝ) / (q : ℝ) + (α - (a₀ : ℝ) / (q : ℝ)) := by ring
  exact ⟨a₀, q, hq, hqQ, hd,
    norm_absWindowSum_residue_split_le_of_eq a H n hq a₀ hα⟩

/-- ⟦SEAM A, named⟧ — the `r`-sum cut into its coprime and non-coprime halves.  §4's
character decomposition serves the first half; the second is `M4Residue`'s `d₀`-dilation
(⟦BRIDGE 3⟧), which plugs in exactly here. -/
theorem norm_absWindowSum_split_coprime_add (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q)
    (a₀ : ℤ) (θ : ℝ) :
    ‖absWindowSum a H n ((a₀ : ℝ) / (q : ℝ) + θ)‖
      ≤ (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
            ‖classPhaseSum a H n q r θ‖)
        + ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
            ‖classPhaseSum a H n q r θ‖ := by
  rw [Finset.sum_filter_add_sum_filter_not]
  exact norm_absWindowSum_residue_split_le a H n hq a₀ θ

/-! ### The trivial ceiling — the split is lossless

At the trivial level the split gives back exactly the trivial bound `H` of
`M4Window.norm_absWindowSum_le`: nothing is spent by passing to classes.  This is the
anti-vacuity check for §3. -/

/-- A class sum is at most the class cardinality, at a 1-bounded datum. -/
theorem norm_classPhaseSum_le_card {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (H n q r : ℕ)
    (θ : ℝ) :
    ‖classPhaseSum a H n q r θ‖ ≤ ((windowClass H n q r).card : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ windowClass H n q r,
      ‖a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ) * ((m : ℕ) : ℂ))‖ ≤ 1 := by
    intro m _
    rw [norm_mul, norm_exp_phase', mul_one]
    exact ha m
  refine (Finset.sum_le_sum hterm).trans ?_
  simp

/-- **The split is lossless at the trivial level**: the `q` class bounds sum back to `H`. -/
theorem sum_norm_classPhaseSum_le {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {q : ℕ} (hq : 0 < q)
    (H n : ℕ) (θ : ℝ) :
    ∑ r ∈ Finset.range q, ‖classPhaseSum a H n q r θ‖ ≤ (H : ℝ) := by
  refine (Finset.sum_le_sum
    (fun r _ => norm_classPhaseSum_le_card ha H n q r θ)).trans (le_of_eq ?_)
  rw [← Nat.cast_sum, sum_card_windowClass hq H n]

/-! ## §4 — the composition hook: the character decomposition fires on each class

`M4Close` §6 (`sum_liou_modEq_residue_eq`) is stated at a general `S : Finset ℕ` with the
class test written as `Nat.ModEq` — which is `residueClassOn`'s definition on the nose.  So
the adapters below are transport, not proof: the bridge's second half was already landed,
and this section only shows the two halves meet.

⚠ THE DATUM: `liouvilleC` and `liouChi`, never `lam`/`lamChi` (the ⟦lam collision⟧,
`M4Close` §6 preamble — `lam = fun _ => −1` is the pretentious datum, correct only at
primes, and this file sums over INTEGERS). -/

/-- **The character decomposition on a residue class**, at the sum-side datum, at a general
index set.  `M4Close.sum_liou_modEq_residue_eq` verbatim, re-expressed through
`residueClassOn`. -/
theorem sum_residueClassOn_liou_eq {q : ℕ} [NeZero q] {r : ℕ} (hcop : Nat.Coprime q r)
    (S : Finset ℕ) :
    ∑ m ∈ residueClassOn q r S, liouvilleC m
      = (q.totient : ℂ)⁻¹
          * ∑ χ : DirichletCharacter ℂ q,
              χ ((r : ℕ) : ZMod q) * ∑ m ∈ S, liouChi χ m :=
  sum_liou_modEq_residue_eq hcop S

/-- **THE HOOK.**  The character decomposition of `M4Close` §6, fired on the `r`-th class of
the door window: for `r` coprime to `q`,

`∑_{n<m≤n+H, m≡r (q)} λ(m) = (1/φ(q))·∑_χ χ(r)·∑_{n<m≤n+H} liouChi χ m`. -/
theorem sum_windowClass_liou_eq {q : ℕ} [NeZero q] {r : ℕ} (hcop : Nat.Coprime q r)
    (H n : ℕ) :
    ∑ m ∈ windowClass H n q r, liouvilleC m
      = (q.totient : ℂ)⁻¹
          * ∑ χ : DirichletCharacter ℂ q,
              χ ((r : ℕ) : ZMod q) * ∑ m ∈ Finset.Ioc n (n + H), liouChi χ m :=
  sum_residueClassOn_liou_eq hcop _

/-- The trivial bound on the class decomposition (the unimodular `χ(r)` discharged). -/
theorem norm_sum_residueClassOn_liou_le {q : ℕ} [NeZero q] {r : ℕ} (hcop : Nat.Coprime q r)
    (S : Finset ℕ) :
    ‖∑ m ∈ residueClassOn q r S, liouvilleC m‖
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖∑ m ∈ S, liouChi χ m‖ :=
  norm_sum_liou_modEq_residue_le hcop S

/-- **THE UNIFORMITY HOOK.**  A bound holding UNIFORMLY over `χ` passes to the class sum
unchanged — the `1/φ(q)` cancels against the character count exactly
(`M4Close.inv_totient_sum_le`).  This is the shape `M4Quality.m4_quality_of_joint` delivers
and the shape ⟦BRIDGE 2⟧ consumes. -/
theorem norm_sum_residueClassOn_liou_le_of_uniform {q : ℕ} [NeZero q] {r : ℕ}
    (hcop : Nat.Coprime q r) (S : Finset ℕ) {B : ℝ}
    (hB : ∀ χ : DirichletCharacter ℂ q, ‖∑ m ∈ S, liouChi χ m‖ ≤ B) :
    ‖∑ m ∈ residueClassOn q r S, liouvilleC m‖ ≤ B :=
  (norm_sum_residueClassOn_liou_le hcop S).trans (inv_totient_sum_le hB)

/-- The uniformity hook at the door window. -/
theorem norm_sum_windowClass_liou_le_of_uniform {q : ℕ} [NeZero q] {r : ℕ}
    (hcop : Nat.Coprime q r) (H n : ℕ) {B : ℝ}
    (hB : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ Finset.Ioc n (n + H), liouChi χ m‖ ≤ B) :
    ‖∑ m ∈ windowClass H n q r, liouvilleC m‖ ≤ B :=
  norm_sum_residueClassOn_liou_le_of_uniform hcop _ hB

/-- ⟦SEAM B, served⟧ — **the partial-sum family**.  Abel summation differences the partial
sums `A(K) = ∑_{n<m≤K, m≡r (q)} λ(m)`; those are `residueClassOn` on the truncated window,
and they are exactly the `m ≤ K` truncations of the class.  Both spellings are provided so
⟦BRIDGE 2⟧ can pick either. -/
theorem windowClass_partial {H n q r K : ℕ} (hK : K ≤ n + H) :
    residueClassOn q r (Finset.Ioc n K)
      = (windowClass H n q r).filter (fun m => m ≤ K) := by
  ext m
  simp only [mem_residueClassOn, Finset.mem_filter, mem_windowClass, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, h2.trans hK⟩, h3⟩, h2⟩
  · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩
    exact ⟨⟨h1, h4⟩, h3⟩

/-- The `K`-UNIFORM class bound: the shape ⟦BRIDGE 2⟧'s Abel step needs, since integration
by parts sees every partial sum of the window, not only the full one. -/
theorem norm_sum_residueClassOn_Ioc_liou_le_of_uniform {q : ℕ} [NeZero q] {r : ℕ}
    (hcop : Nat.Coprime q r) (n : ℕ) {B : ℝ}
    (hB : ∀ K : ℕ, ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ Finset.Ioc n K, liouChi χ m‖ ≤ B) (K : ℕ) :
    ‖∑ m ∈ residueClassOn q r (Finset.Ioc n K), liouvilleC m‖ ≤ B :=
  norm_sum_residueClassOn_liou_le_of_uniform hcop _ (hB K)

/-- **THE BRIDGE, assembled at the arc.**  The one statement that carries ⟦BRIDGE 1⟧'s whole
content into the M4 chain: at a tight-major `α`, with a `χ`-uniform bound `B` available on
every class of the arc's own modulus `q` and with the non-coprime classes priced separately
by `Bbad`, the window sum obeys

`‖∑_{n<m≤n+H} λ(m)e(αm)‖ ≤ φ(q)·B + (q − φ(q))·Bbad`  — here in its unevaluated,
class-by-class form, the counting being ⟦BRIDGE 3⟧'s to perform.

`NeZero q` is derived here, once, from `NearRatTight`'s `0 < q` — the only place the two
modulus conventions meet. -/
theorem norm_absWindowSum_le_liou_class_bound_of_nearRatTight {Q : ℝ} {H : ℕ} {α : ℝ}
    (harc : NearRatTight Q H α) (n : ℕ) :
    ∃ (a₀ : ℤ) (q : ℕ), 0 < q ∧ (q : ℝ) ≤ Q ∧
      |α - (a₀ : ℝ) / (q : ℝ)| ≤ Q / ((q : ℝ) * (H : ℝ)) ∧
      ‖absWindowSum liouvilleC H n α‖
        ≤ (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
              ‖classPhaseSum liouvilleC H n q r (α - (a₀ : ℝ) / (q : ℝ))‖)
          + ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
              ‖classPhaseSum liouvilleC H n q r (α - (a₀ : ℝ) / (q : ℝ))‖ := by
  obtain ⟨a₀, q, hq, hqQ, hd⟩ := harc
  refine ⟨a₀, q, hq, hqQ, hd, ?_⟩
  have hα : α = (a₀ : ℝ) / (q : ℝ) + (α - (a₀ : ℝ) / (q : ℝ)) := by ring
  rw [Finset.sum_filter_add_sum_filter_not]
  exact norm_absWindowSum_residue_split_le_of_eq liouvilleC H n hq a₀ hα

end Salt.MR

end
