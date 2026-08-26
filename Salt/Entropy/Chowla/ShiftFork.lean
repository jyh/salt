/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦L3-FORK FOUNDATION⟧ — the shift-`h` de-specialization, wave W-F1

The landed log-Chowla spine is Tao arXiv:1509.05422v2 at the model point
`(a, b, h) = (1, 0, 1)`.  This module opens the `h`-family **beside** the landed
objects: `logChowlaFails`, `bigXiH`, `MRTUniformityXiH` are new names with new
arities, and every landed declaration keeps its bytes and its arity.  Nothing
here edits a landed statement; the compat lemmas pin the landed objects as the
`h = 1` members of the new families.

* `logChowlaFails h` — the failure Prop at shift `h` (`logChowla2Fails` is
  `logChowlaFails 1`, definitionally).
* `bigXiH h` — Tao's `Ξ_H` with the `−hξ/H` twist made VISIBLE
  (`chowla.txt:1296-1300`); at `h = 1` it is the landed `bigXi` up to a
  `one_mul` rewrite.
* `MRTUniformityXiH h` — the `Ξ`-restricted MRT door over `bigXiH h`, with the
  door's frequency `α` **UNTWISTED**: the seam consumes the surviving DFT factor
  at `−ξ.val/H` (`Theorem23Shell.lean:188-193`), so the twist lives ONLY in the
  membership predicate of `bigXiH`.  Twisting the door's `α` would be a silent
  statement error that survives elaboration and kills the terminal at assembly.
* `bigXiH_card_le_gcd_mul` / `bigXiH_bounded` — the fiber bound
  `|Ξ_H(h)| ≤ gcd(h,H)·|Ξ_H|` and the explicit transfer of `bigXi_bounded`.
* `contradiction_of_mrtDoorXiH` — the `h`-general seam, the clone of
  `contradiction_of_mrtDoorXi` (`MRTDoor.lean:127-157`).  It is the wave's
  TRIPWIRE: under the untwisted door its termwise step matches the goal's
  integrand and the `calc` closes; under a twisted door the hypothesis would
  speak at `−(h·ξ.val)/H` while the goal's summand sits at `−ξ.val/H`, and no
  lemma closes that at general `h`.

**`h = 0` is degenerate.**  `logChowlaFails 0` is a statement about
`λ(n)² = 1`; `bigXiH 0 eps H` is `ξ`-independent, hence carries no `H`-uniform
cardinality bound; and `gcd 0 H = H`.  Every statement here that manufactures an
`H`-uniform constant therefore carries `0 < h` EXPLICITLY.

Scope: definitional/foundational only.  No claim about Chowla, about the door,
or about twins is made or moved by this file.
-/
import Salt.Entropy.Chowla.CircleMethod
import Salt.Entropy.Chowla.MRTDoor
import Salt.Entropy.Chowla.ChowlaFailure
import Salt.Entropy.Chowla.GoldbachEnergyFinal
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ## D1 — the failure Prop at shift `h` -/

/-- **The failure Prop at shift `h`** — `logChowla2Fails` (`ChowlaFailure.lean:59`)
with the carried scalar's second factor at `n + h` rather than `n + 1`:
"log-Chowla fails at shift `h`, scale `(x, ω)`, margin `ε`".  Tao (2.4) at the
Liouville model `a = 1, b = 0, g₁ = g₂ = λ`, general `h`.  UNnormalized
(RHS `ε·log ω`), verbatim the landed shape otherwise.

At `h = 0` the correlation degenerates to `∑ λ(n)² / n`, so this Prop is not a
Chowla statement there; see the module header. -/
def logChowlaFails (h : ℕ) (eps : ℚ) (x ω : ℕ) : Prop :=
  (eps : ℝ) * Real.log (ω : ℝ) <
    |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + h) : ℝ) / (n : ℝ)|

/-- **C1 — the `h = 1` compat, `rfl`-grade.**  The landed `logChowla2Fails` IS
`logChowlaFails 1`: substituting the literal `1` for `h` yields the landed
`n + 1` syntactically, so the two definitions are definitionally equal and every
landed `logChowla2Fails` consumer survives untouched (restatement-renames law). -/
theorem logChowla2Fails_eq_logChowlaFails_one :
    logChowla2Fails = logChowlaFails 1 := rfl

/-! ## D2 — the large-spectrum set with the `−hξ/H` twist -/

/-- **The major-arc frequency set `Ξ_H` at shift `h`** (Tao Lemma 3.4 at `a = 1`,
`chowla.txt:1296-1300`): the `ξ ∈ ℤ/Hℤ` with `|S_H(−(hξ)/H)| ≥ ε²/log H`.

THE TWIST LIVES HERE AND ONLY HERE.  At shift `h` only WHICH frequencies are
large-spectrum moves; the DFT factor that survives the circle-method estimate
stays at the untwisted `ξ` (`Theorem23Shell.lean:188-193`).  The twist is spelled
in `ZMod H` — `(h : ZMod H) * ξ` — so that `mem_bigXiH_iff` is a definitional
unfolding rather than a periodicity argument.

At `h = 1` the twist is INVISIBLE (`bigXi_eq_bigXiH_one`), which is exactly why
no `h = 1` compat lemma can police the door's spelling; the `h`-general seam
`contradiction_of_mrtDoorXiH` is the tripwire that can.

At `h = 0` the predicate does not mention `ξ` at all, so `bigXiH 0 eps H` is
either `∅` or `univ` and carries no `H`-uniform cardinality bound — the reason
`bigXiH_card_le_mul` and `bigXiH_bounded` both demand `0 < h`. -/
noncomputable def bigXiH (h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] : Finset (ZMod H) := by
  classical
  exact Finset.univ.filter (fun ξ : ZMod H =>
    (eps : ℝ) ^ 2 / Real.log (H : ℝ)
      ≤ ‖expSum eps H (-((((h : ZMod H) * ξ).val : ℕ) : ℝ) / (H : ℝ))‖)

/-- **C2a — the `h = 1` compat.**  NOT `rfl`-grade: `((1 : ℕ) : ZMod H) * ξ`
reduces to `ξ` only propositionally (`Nat.cast_one` then `one_mul`; `Nat.mul`
recurses on its second argument and `ZMod`'s multiplication goes through
`Nat.mod`, so neither step is definitional).  `simp only [one_mul]` alone fires
NOTHING here — the cast `((1 : ℕ) : ZMod H)` is not the `OfNat` literal
`(1 : ZMod H)`, so `Nat.cast_one` must come first. -/
theorem bigXi_eq_bigXiH_one (eps : ℚ) (H : ℕ) [NeZero H] :
    bigXi eps H = bigXiH 1 eps H := by
  classical
  unfold bigXi bigXiH
  exact Finset.filter_congr (fun ξ _ => by simp only [Nat.cast_one, one_mul])

/-- **C2b — the membership unfolding.**  `bigXiH h` is exactly the `μ_h`-preimage
of `bigXi`, `μ_h : ξ ↦ (h : ZMod H) * ξ`.  This is the object that transfers
`bigXi_bounded` without re-deriving Lemma 3.5's restriction theorem.

The unfolding is re-derived locally rather than imported: `CircleMethod`'s own
`mem_bigXi` is `private`, and the public copy lives in `Salt/MR/BigXiArc.lean`,
whose import would invert this file's lane layering. -/
theorem mem_bigXiH_iff {h : ℕ} {eps : ℚ} {H : ℕ} [NeZero H] {ξ : ZMod H} :
    ξ ∈ bigXiH h eps H ↔ (h : ZMod H) * ξ ∈ bigXi eps H := by
  classical
  unfold bigXiH bigXi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## T1 — frequency invariance of `expSum` under integer translation -/

/-- **T1 — `expSum` is `1`-periodic in its frequency, hence invariant under
adding ANY integer.**  The primes of the window are natural numbers, so every
character value `e(k·p)` at an integer `k` is `1`.

The period-1 form alone would be too weak for the `h`-family: the two spellings
of the twisted frequency — `−(h·ξ.val)/H` (the ℝ-side twist) and
`−((h·ξ).val)/H` (the `ZMod`-side twist used by `bigXiH`) — differ by an
arbitrary natural number, not by `1`. -/
theorem expSum_add_intCast (eps : ℚ) (H : ℕ) (α : ℝ) (k : ℤ) :
    expSum eps H (α + (k : ℝ)) = expSum eps H α := by
  unfold expSum
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  have hsplit : (2 * (Real.pi : ℂ) * Complex.I * ((α + (k : ℝ) : ℝ) : ℂ) * ((p : ℕ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((p : ℕ) : ℂ)
        + ((k * (p : ℕ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## T2 — the fiber bound `|Ξ_H(h)| ≤ gcd(h,H)·|Ξ_H|` -/

/-- Cancel a common positive factor and a coprimality: if `d·b' ∣ d·a'·v` and
`b'` is coprime to `a'`, then `b' ∣ v`.  (Stated with the quotients as free
variables so no rewrite has to reach inside a `Nat.gcd`.) -/
private lemma dvd_of_coprime_factor {d a' b' v : ℕ} (hd : 0 < d)
    (hcop : Nat.Coprime b' a') (hdvd : d * b' ∣ d * a' * v) : b' ∣ v := by
  rw [mul_assoc] at hdvd
  exact hcop.dvd_of_dvd_mul_left ((mul_dvd_mul_iff_left hd.ne').mp hdvd)

/-- The kernel of `μ_h : ZMod H → ZMod H`, `x ↦ (h : ZMod H) * x`, consists of the
multiples of `H / gcd(h,H)`: if `h·z = 0` in `ZMod H` then `H/gcd(h,H) ∣ z.val`. -/
private lemma val_dvd_of_mul_eq_zero {H : ℕ} [NeZero H] (h : ℕ) {z : ZMod H}
    (hz : (h : ZMod H) * z = 0) : H / Nat.gcd h H ∣ z.val := by
  have hHne : H ≠ 0 := NeZero.ne H
  have hdpos : 0 < Nat.gcd h H :=
    Nat.pos_of_ne_zero fun hzero => hHne (Nat.eq_zero_of_gcd_eq_zero_right hzero)
  have hcast : ((h * z.val : ℕ) : ZMod H) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id]
    exact hz
  have hdvd : H ∣ h * z.val := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hH : Nat.gcd h H * (H / Nat.gcd h H) = H :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right h H)
  have hh : Nat.gcd h H * (h / Nat.gcd h H) = h :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left h H)
  refine dvd_of_coprime_factor (d := Nat.gcd h H) hdpos
    ((Nat.coprime_div_gcd_div_gcd hdpos).symm) ?_
  rw [hH, hh]
  exact hdvd

/-- Every fiber of `μ_h : ξ ↦ (h : ZMod H) * ξ` has at most `gcd(h,H)` elements:
a nonempty fiber is a coset of the kernel, and the kernel injects into
`range (gcd h H)` by `z ↦ z.val / (H / gcd(h,H))`. -/
private lemma card_fiber_le {H : ℕ} [NeZero H] (h : ℕ) (a : ZMod H) :
    (Finset.univ.filter (fun x : ZMod H => (h : ZMod H) * x = a)).card
      ≤ Nat.gcd h H := by
  classical
  rcases Finset.eq_empty_or_nonempty
      (Finset.univ.filter (fun x : ZMod H => (h : ZMod H) * x = a)) with hE | hne
  · rw [hE, Finset.card_empty]
    exact Nat.zero_le _
  · obtain ⟨x₀, hx₀⟩ := hne
    have hx₀' : (h : ZMod H) * x₀ = a := (Finset.mem_filter.mp hx₀).2
    have hHdq : H / Nat.gcd h H * Nat.gcd h H = H :=
      Nat.div_mul_cancel (Nat.gcd_dvd_right h H)
    have hker : ∀ x ∈ Finset.univ.filter (fun x : ZMod H => (h : ZMod H) * x = a),
        (H / Nat.gcd h H) ∣ (x - x₀).val := by
      intro x hx
      refine val_dvd_of_mul_eq_zero h ?_
      have hx' : (h : ZMod H) * x = a := (Finset.mem_filter.mp hx).2
      rw [mul_sub, hx', hx₀', sub_self]
    have hle : (Finset.univ.filter (fun x : ZMod H => (h : ZMod H) * x = a)).card
        ≤ (Finset.range (Nat.gcd h H)).card := by
      refine Finset.card_le_card_of_injOn
        (fun x => (x - x₀).val / (H / Nat.gcd h H)) ?_ ?_
      · intro x _
        have hlt : (x - x₀).val / (H / Nat.gcd h H) < Nat.gcd h H := by
          refine Nat.div_lt_of_lt_mul ?_
          rw [hHdq]
          exact ZMod.val_lt _
        simpa using hlt
      · intro x hx y hy hxy
        replace hxy : (x - x₀).val / (H / Nat.gcd h H)
            = (y - x₀).val / (H / Nat.gcd h H) := hxy
        have hdx := hker x (Finset.mem_coe.mp hx)
        have hdy := hker y (Finset.mem_coe.mp hy)
        have hval : (x - x₀).val = (y - x₀).val := by
          rw [← Nat.div_mul_cancel hdx, ← Nat.div_mul_cancel hdy, hxy]
        have hz : x - x₀ = y - x₀ := ZMod.val_injective H hval
        have := congrArg (fun t : ZMod H => t + x₀) hz
        simpa using this
    simpa using hle

/-- **T2 — THE FIBER BOUND, hypothesis-free.**  `bigXiH h eps H` is the
`μ_h`-preimage of `bigXi eps H` (`mem_bigXiH_iff`), and each fiber of `μ_h` is a
coset of a kernel of size `gcd(h,H)` — so the twisted large-spectrum set is at
most `gcd(h,H)` times the landed one.  No hypothesis on `h`, `eps` or `H` beyond
`[NeZero H]`. -/
theorem bigXiH_card_le_gcd_mul (h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] :
    (bigXiH h eps H).card ≤ Nat.gcd h H * (bigXi eps H).card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun ξ : ZMod H => (h : ZMod H) * ξ) (t := bigXi eps H)
    (fun ξ hξ => mem_bigXiH_iff.mp hξ) (Nat.gcd h H) ?_
  intro b _
  refine le_trans (Finset.card_le_card ?_) (card_fiber_le h b)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨Finset.mem_univ x, hx.2⟩

/-- **T2, corollary** — the `h`-form of the fiber bound.  `gcd(h,H) ≤ h` needs
`0 < h`: at `h = 0` the gcd is `H` and the bound is vacuous, which is the `h = 0`
degeneracy of the module header. -/
theorem bigXiH_card_le_mul (h : ℕ) (hh : 0 < h) (eps : ℚ) (H : ℕ) [NeZero H] :
    (bigXiH h eps H).card ≤ h * (bigXi eps H).card :=
  le_trans (bigXiH_card_le_gcd_mul h eps H)
    (Nat.mul_le_mul_right _ (Nat.gcd_le_left H hh))

/-! ## T3 — the explicit transfer of `bigXi_bounded` -/

/-- **T3 — the twisted large-spectrum count is bounded.**  `bigXi_bounded`
(`GoldbachEnergyFinal.lean:502`, Tao Lemma 3.5, unconditional) transfers to the
`h`-family through T2 with the constant multiplied by `h` and NO re-derivation of
the restriction theorem.

`0 < h` is required: the constant `h·C` is `H`-uniform, and at `h = 0` the fiber
bound degenerates (module header). -/
theorem bigXiH_bounded (h : ℕ) (hh : 0 < h) (eps : ℚ) (heps : 0 < eps)
    (heps2 : (eps : ℝ) ^ 2 < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ (H : ℕ) [NeZero H], H₀ ≤ H →
      ((bigXiH h eps H).card : ℝ) ≤ (h : ℝ) * C := by
  obtain ⟨C, hC, H₀, hH₀, hb⟩ := bigXi_bounded eps heps heps2
  refine ⟨C, hC, H₀, hH₀, ?_⟩
  intro H _ hle
  have h1 : ((bigXiH h eps H).card : ℝ) ≤ (h : ℝ) * ((bigXi eps H).card : ℝ) := by
    exact_mod_cast bigXiH_card_le_mul h hh eps H
  refine le_trans h1 ?_
  exact mul_le_mul_of_nonneg_left (hb H hle) (Nat.cast_nonneg h)

/-! ## D3 — the `Ξ`-restricted MRT door at shift `h` -/

/-- **The `Ξ`-restricted MRT uniformity door at shift `h`** — `MRTUniformityXi`
(`MRTDoor.lean:109-111`) with the binder ranging over `bigXiH h R.eps H`.

THE `∀ ξ ∈ Ξ_H(h)` STAYS OUTSIDE THE INTEGRAL, and **the frequency `α` is
UNTWISTED**.  Both are load-bearing and neither is policed by the kernel:

* the quantifier position — the sup-inside form is Tao arXiv:1509.05422v2 (4.1), which is
  OPEN; moving the quantifier silently downgrades a theorem-door (Prop 2.4,
  PROVEN in Matomäki–Radziwiłł–Tao, arXiv:1503.05121) into an open conjecture;
* the frequency — the circle-method estimate's surviving factor is the DFT at the
  UNTWISTED `ξ` (`Theorem23Shell.lean:188-193`; the `−hξ/H` of Tao's `Ξ_H` lives
  in the membership predicate of `bigXiH`, `chowla.txt:1296-1300`).  A door
  stated at `−(h·ξ.val)/H` elaborates fine and then fails to compose at the seam.

**STRENGTH, WITH ITS DIRECTION NAMED.**  For `h ≥ 2` this is a STRICTLY STRONGER
hypothesis than the landed `MRTUniformityXi`: `bigXiH h` is the larger set (it
contains every `ξ` whose `h`-multiple is large-spectrum, and `μ_h` is not
injective when `gcd(h,H) > 1`), so the `h`-door constrains strictly more
frequencies.  It is still implied by the full `∀ α` door `MRTUniformity` by the
same one-liner as `mrtUniformity_implies_xi` (`MRTDoor.lean:116-119`) — the
frequency restriction only discards instances.

**THE PRODUCER STORY, HONESTLY.**  `MRTUniformity` is NEVER PRODUCED anywhere in
this corpus: every occurrence of it is a hypothesis binder, and the `∀ α`-shaped
terminal is DERIVED FROM the `Ξ`-restricted door (`SpineFinal.lean:976`), not the
reverse.  So `MRTUniformityXiH h` is the `h`-family's OPEN HYPOTHESIS, exactly as
`MRTUniformityXi` is for `h = 1`; a future `mrtUniformity_implies_xiH` would
supply it only from the `∀ α` Prop, which nothing in the corpus produces.  This
file adds no producer and claims none. -/
noncomputable def MRTUniformityXiH (h : ℕ) (R : ChowlaRegime) (δ : ℝ) : Prop :=
  ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ ξ ∈ bigXiH h R.eps H,
    (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)

/-- **C3 — the `h = 1` compat for the door, stated APPLIED.**  `Prop`-equality at
each `(R, δ)`, so a consumer can rewrite with it under the spine's binders.

It records that the FORK IS CONSERVATIVE at `h = 1` — and nothing more.  It
cannot certify the door's frequency spelling: at `h = 1` the twist is invisible
(`bigXi_eq_bigXiH_one`), so this lemma is provable under a twisted door too.  The
spelling's tripwire is `contradiction_of_mrtDoorXiH` below. -/
theorem mrtUniformityXi_eq_xiH_one (R : ChowlaRegime) (δ : ℝ) :
    MRTUniformityXi R δ = MRTUniformityXiH 1 R δ := by
  apply propext
  constructor
  · intro hd H _ hlo hhi ξ hξ
    exact hd H hlo hhi ξ (by rw [bigXi_eq_bigXiH_one]; exact hξ)
  · intro hd H _ hlo hhi ξ hξ
    exact hd H hlo hhi ξ (by rw [← bigXi_eq_bigXiH_one]; exact hξ)

/-! ## S1 — the `h`-general seam (THE TRIPWIRE) -/

/-- **The `Ξ`-restricted MRT seam at shift `h`** — the clone of
`contradiction_of_mrtDoorXi` (`MRTDoor.lean:127-157`) with the `Finset` swapped
for `bigXiH h R.eps H`.  Same collision, unchanged:
`c₀ε ≤ Σ_{ξ∈Ξ_H(h)}(1/H)∫‖…‖ ≤ Σ(1/H)(δH) = card·δ ≤ K·δ < c₀ε`.  Nonnegativity
of `δ` is the explicit hypothesis `hδ`, exactly as in the landed seam (the
`Ξ`-restricted door does not speak at `α = 0`).

**THIS IS THE WAVE'S TRIPWIRE.**  The termwise step fires the door at `ξ` and
must land on the goal's summand.  With the door at the untwisted `−ξ.val/H`
(above) the two are the same term and the `calc` closes at general `h`.  Had the
door been stated at the twisted `−(h·ξ.val)/H`, the hypothesis would bound a
different integrand from the one the sum carries, and no lemma closes that gap
for general `h` — the kernel refuses here, inside this wave, rather than silently
at a future assembly.

It is also the seam a door-conditional `h`-family terminal needs, so it costs the
campaign nothing it would not pay later.

`0 < h` is NOT required: `K` is supplied by the caller as a hypothesis rather
than manufactured here, so no `H`-uniform constant lives in this statement. -/
theorem contradiction_of_mrtDoorXiH (h : ℕ) (R : ChowlaRegime) {δ c₀ ε K : ℝ} {H : ℕ}
    [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi) (hH : 0 < H) (hδ : 0 ≤ δ)
    (hdoor : MRTUniformityXiH h R δ)
    (hXi : ((bigXiH h R.eps H).card : ℝ) ≤ K)
    (hsmall : K * δ < c₀ * ε)
    (hlower : c₀ * ε ≤ ∑ ξ ∈ bigXiH h R.eps H,
        (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
          ∂(logMeasure R.x R.ω)) :
    False := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  -- Termwise: (1/H)∫‖…‖ ≤ (1/H)(δH) = δ, firing the door at each ξ ∈ Ξ_H(h).
  have hsum : (∑ ξ ∈ bigXiH h R.eps H,
      (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
        ∂(logMeasure R.x R.ω)) ≤ ∑ _ξ ∈ bigXiH h R.eps H, δ := by
    apply Finset.sum_le_sum
    intro ξ hξ
    have hb := hdoor H hlo hhi ξ hξ
    calc (1 / (H : ℝ)) * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖
            ∂(logMeasure R.x R.ω)
        ≤ (1 / (H : ℝ)) * (δ * (H : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = δ * ((H : ℝ) / (H : ℝ)) := by ring
      _ = δ := by rw [div_self hHR.ne', mul_one]
  -- Σ_{ξ∈Ξ_H(h)} δ = card·δ ≤ K·δ (δ ≥ 0).
  have hconst : (∑ _ξ ∈ bigXiH h R.eps H, δ) = ((bigXiH h R.eps H).card : ℝ) * δ := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((bigXiH h R.eps H).card : ℝ) * δ ≤ K * δ :=
    mul_le_mul_of_nonneg_right hXi hδ
  have h1 : c₀ * ε ≤ ((bigXiH h R.eps H).card : ℝ) * δ :=
    le_trans hlower (le_trans hsum (le_of_eq hconst))
  linarith [h1, hcard, hsmall]

/-! ## E1 — the `h`-family circle-method estimate (wave W-F2) -/

/-- **The fork's large-spectrum set is the engine room's twisted filter.**
`bigXiTwistFilter h` (`CircleMethod.lean`) is `bigXiH h` spelled on the side of the file
that owns the circle method: `ShiftFork` IMPORTS `CircleMethod`, so the `h`-family
estimate cannot be stated over `bigXiH` there without an import cycle.  The two sets have
the SAME membership predicate — this lemma is a filter congruence at `Iff.rfl`, with the
decidability misalignment (both instances are classical) absorbed by
`Finset.filter_congr`. -/
theorem bigXiH_eq_twistFilter (h : ℕ) (eps : ℚ) (H : ℕ) [NeZero H] :
    bigXiH h eps H = bigXiTwistFilter h eps H := by
  classical
  unfold bigXiH bigXiTwistFilter
  exact Finset.filter_congr (fun ξ _ => Iff.rfl)

/-- **The circle-method estimate at shift `h`, over the fork's own set** — the
`bigXiH`-facing restatement of `circle_method_estimate_h_core` (`CircleMethod.lean`), the
`h`-family twin of `circle_method_estimate` (`CircleMethod.lean:574-585`).

Every byte of the conclusion matches the landed estimate's except two: the correlation's
offset is `p·h` rather than `p`, and the Fourier mass is summed over `bigXiH h eps H`
rather than `bigXi eps H`.  The DFT factor itself stays at the UNTWISTED `ξ` — that is the
seam's spelling (`Theorem23Shell.lean:188-193`), and it is why the twist can live in the
membership predicate alone.

The constant is `h·(1 + 2·C₀)` and `0 < h` is consumed for it (and, at `H = 1`, for the
vanishing of the window correlation); see `circle_method_estimate_h_core`. -/
theorem circle_method_estimate_h (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 x2 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) → (∀ i, |x2 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x2 (j + (p : ℕ) * h) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiH h eps H, (1 / (H : ℝ)) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖) := by
  obtain ⟨C, hC, hest⟩ := circle_method_estimate_h_core h hh C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro eps H _ x1 x2 hx1 hx2 hcard
  rw [bigXiH_eq_twistFilter]
  exact hest eps H x1 x2 hx1 hx2 hcard

/-- **The SQUARED circle-method estimate at shift `h`, over the fork's own set** — the
`bigXiH`-facing restatement of `circle_method_estimate_sq_h_core` (`CircleMethod.lean`), and
the object `QUEUE.md` P2 item 7 names.  It is to `circle_method_estimate_sq` exactly what
`circle_method_estimate_h` is to `circle_method_estimate`.

DIAGONAL, like its untwisted parent and unlike `circle_method_estimate_h`: ONE window `x1`,
because the `_sq` lane's consumers instantiate at `x₁ = x₂` and the square in the conclusion
IS that diagonality.  The Fourier mass is `(1/H²)‖𝓕Φ ξ‖²` over `bigXiH h eps H`; the DFT
factor stays at the UNTWISTED `ξ`, which is the seam's spelling and why the twist lives in
the membership predicate alone.

The set swap is the only step (`bigXiH_eq_twistFilter`, a filter congruence — the `ZMod`-side
spelling was chosen so this is a rewrite and not a periodicity argument).  Constant
`h·(1 + 2·C₀)` and the `0 < h` fence are the core's; see there.

⛔ **STILL NO CONSUMER:** `log_chowla_two_shell_xi_sq_h` does not exist, so this completes the
socket rather than connecting it. -/
theorem circle_method_estimate_sq_h (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiH h eps H, (1 / (H : ℝ) ^ 2) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) := by
  obtain ⟨C, hC, hest⟩ := circle_method_estimate_sq_h_core h hh C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro eps H _ x1 hx1 hcard
  rw [bigXiH_eq_twistFilter]
  exact hest eps H x1 hx1 hcard

/-! ## S2 — the `h`-collapse identity -/

/-- `λ(p)² = 1` for `p ≠ 0`.  Re-derived locally: `DilationStability`'s own `liouville_sq`
is `private`, and importing that module for four lines would widen this file's import
surface for nothing. -/
private lemma liouville_sq_shift {p : ℕ} (hp : p ≠ 0) :
    (ArithmeticFunction.liouville p : ℝ) ^ 2 = 1 := by
  rw [ArithmeticFunction.liouville_apply hp]; push_cast
  rw [← pow_mul]
  exact Even.neg_one_pow ⟨ArithmeticFunction.cardFactors p, by ring⟩

/-- **The collapse identity at shift `h`** — the `h`-family replay of `collapse_identity`
(`DilationStability.lean:53-63`): for `p ≠ 0`,
`λ(p·N)·λ(p·N + p·h) = λ(N)·λ(N + h)`.  Both arguments carry the factor `p`
(`p·N + p·h = p·(N + h)`), and `λ(p)² = 1` erases it.

`0 < h` is NOT required and is deliberately absent: at `h = 0` the identity degenerates to
`λ(p·N)² = λ(N)²`, which is still true.  The `p ≠ 0` fence is the only one the square
needs. -/
theorem liouville_collapse_h (p h : ℕ) (hp : p ≠ 0) (N : ℕ) :
    (ArithmeticFunction.liouville (p * N) : ℝ)
        * (ArithmeticFunction.liouville (p * N + p * h) : ℝ)
      = (ArithmeticFunction.liouville N : ℝ)
          * (ArithmeticFunction.liouville (N + h) : ℝ) := by
  have hpN : p * N + p * h = p * (N + h) := by ring
  rw [hpN, ArithmeticFunction.liouville_apply_mul, ArithmeticFunction.liouville_apply_mul]
  have hsq := liouville_sq_shift hp
  push_cast
  linear_combination (ArithmeticFunction.liouville N : ℝ)
    * (ArithmeticFunction.liouville (N + h) : ℝ) * hsq

/-! ## D4 — the `∀ α` door implies the `h`-door -/

/-- **The door weakening at shift `h`.**  This is the lemma named as "future" in
`MRTUniformityXiH`'s docstring above (`ShiftFork.lean:292-295`); it consumes the
never-produced `∀ α` door, so the producer story is UNCHANGED — no new supply of the
`h`-door exists.

The proof is `mrtUniformity_implies_xi`'s one-liner (`MRTDoor.lean:116-119`) with the
binder ranging over `bigXiH h R.eps H`: the door is instantiated at the UNTWISTED
`α := −ξ.val/H` for each `ξ` in the twisted set, and the frequency restriction only
discards instances.  Which `ξ` the binder ranges over is therefore immaterial here — the
lemma would hold over ANY `Finset (ZMod H)`, which is exactly why it certifies nothing
about the door's spelling (that is `contradiction_of_mrtDoorXiH`'s job). -/
theorem mrtUniformity_implies_xiH (h : ℕ) (R : ChowlaRegime) (δ : ℝ) :
    MRTUniformity R δ → MRTUniformityXiH h R δ := by
  intro hd H _ hlo hhi ξ _
  exact hd H hlo hhi (-(ξ.val : ℝ) / (H : ℝ))

/-! ## D5 — THE FORK OF THE `L²` DOOR -/

/-- **The Ξ-summed `L²` MRT uniformity door at shift `h`** — `MRTUniformityXiL2`
(`MRTDoor.lean:187-190`) with the summation set swapped for `bigXiH h R.eps H` and the
frequency `α` left UNTWISTED, exactly as in the `L¹` fork `MRTUniformityXiH`.

For `h ≥ 2` this binds a DIFFERENT set — the `μ_h`-preimage of `Ξ_H`, incomparable to
`Ξ_H` in general, of cardinality `≤ gcd(h,H)·|Ξ_H|` (`bigXiH_card_le_gcd_mul`); an
independent open hypothesis, implied by the full `∀ α` door (`mrtUniformity_implies_xiH`)
and neither implying nor implied by `MRTUniformityXiL2`.  Nothing in the corpus produces
it; the `h`-mint (`m4_doorL2_supply_500`'s `h`-analogue, `M4DoorL2.lean:206`/`:730`) and
the `h`-`L²` estimate (`circle_method_estimate_sq_h`) are W-F3+ scope — this fork makes
them REACHABLE, not done.
⛔ **STALE, CORRECTED 2026-08-26 (commission 7b, correction 3): `circle_method_estimate_sq_h`
IS LANDED — 90 lines below this citation, at `:432`, audited.** The `h`-mint is still open.
*Prose beside code is a second implementation nobody tests.*  At shift `h` the `L²` grade `ρ` must absorb the `gcd(h,H)`
fiber inflation — the `K`-shed line of the `L²` restructure
(`l3-design-block-0815.md` §1).

THE QUANTIFIERS STAY OUTSIDE THE INTEGRAL, per the REF-L2 mandate R4 restated at
`MRTUniformityXiL2` (`MRTDoor.lean:174-182`): the frequency quantifier is a `∑` over the
set sitting outside `∫`, and there is no `sup` anywhere inside the integral.  The
sup-inside form is Tao arXiv:1509.05422v2 (4.1), which is OPEN.  The normalisation `1/H²` is the
landed door's, unchanged. -/
noncomputable def MRTUniformityXiL2H (h : ℕ) (R : ChowlaRegime) (ρ : ℝ) : Prop :=
  ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi →
    ∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2)
        * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure R.x R.ω) ≤ ρ

/-- **C4 — the `h = 1` compat for the `L²` door, stated APPLIED.**  `Prop`-equality at
each `(R, ρ)`, so a consumer can rewrite with it under the spine's binders.  It records
that the `L²` fork is CONSERVATIVE at `h = 1`, and — like `mrtUniformityXi_eq_xiH_one` —
nothing more: at `h = 1` the twist is invisible (`bigXi_eq_bigXiH_one`), so no `h = 1`
compat can police a frequency spelling. -/
theorem mrtUniformityXiL2_eq_xiL2H_one (R : ChowlaRegime) (ρ : ℝ) :
    MRTUniformityXiL2 R ρ = MRTUniformityXiL2H 1 R ρ := by
  apply propext
  constructor
  · intro hd H _ hlo hhi
    rw [← bigXi_eq_bigXiH_one]
    exact hd H hlo hhi
  · intro hd H _ hlo hhi
    rw [bigXi_eq_bigXiH_one]
    exact hd H hlo hhi

/-- **The Ξ-summed `L²` MRT seam at shift `h`** — the clone of
`contradiction_of_mrtDoorXiL2` (`MRTDoor.lean:200-208`) with the summation set swapped for
`bigXiH h R.eps H`.  The chain is unchanged: `c₀ε ≤ (the summed L² door object) ≤ ρ < c₀ε`.

Absent here exactly as in the landed `L²` seam: no `K`, no `|Ξ| ≤ K` hypothesis, no
`δ`-nonnegativity side condition — the door's grade `ρ` is already the total over the set,
so the frequency count never multiplies it.  `0 < h` is not required: no `H`-uniform
constant is manufactured in this statement.

The lower bound `hlower` is TRANSCRIBED from the landed seam at the UNTWISTED
`−ξ.val/H`, with only the `Finset` swapped — never re-derived from the definition above —
so that `linarith`'s atom identity certifies the door's frequency spelling rather than
assuming it. -/
theorem contradiction_of_mrtDoorXiL2H (h : ℕ) (R : ChowlaRegime) {ρ c₀ ε : ℝ} {H : ℕ}
    [NeZero H] (hlo : R.Hlo ≤ H) (hhi : H ≤ R.Hhi)
    (hdoor : MRTUniformityXiL2H h R ρ)
    (hsmall : ρ < c₀ * ε)
    (hlower : c₀ * ε ≤ ∑ ξ ∈ bigXiH h R.eps H, (1 / (H : ℝ) ^ 2)
        * ∫ n, ‖windowExpSum H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure R.x R.ω)) :
    False := by
  have hd := hdoor H hlo hhi
  linarith

end Salt.Entropy.Chowla
