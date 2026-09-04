/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦STRIDE BRIDGE⟧ — Tao (3.16) / Prop 2.6 at the affine forms: the F-function with the class
filter, λ-BV wave 2-S step F2 (2026-09-03, statement-only at the freeze; v2 after the helm's
refuter verdict 18:1x — REPAIR-THEN-FIRE 6/6; LANDED 2026-09-04 on the council's word: 23
obligations, 23 first attempt, one Opus executor, every declaration `[3 axioms]` or fewer)

**The merge fence of the statement-only freeze is DISCHARGED**: no `sorry` remains in this
module (the fence read "the branch `math/lbv-w2s-f2` never reaches `main` until every obligation
here lands sorry-free"; they have, and `#audit_axioms` in `Salt/Entropy/All.lean` lists them).

`StrideFork` (F1) opened the OBJECTS of Tao arXiv:1509.05422 Theorem 2.3 at a general stride
`a` and offset `b`: the pushforward measure `logMeasureAff a x ω`, the frequency set
`bigXiAff`, the affine regime and the two doors with their seams.  This module opens the
(2.4) ⇒ (2.11) PRODUCER CHAIN at the affine forms — the twins, in the three files
`ChowlaFailure` / `Prop26` / `FBridge`, of what the `h`-fork twinned there — so that the entropy
half (F4) has a `(c₁, h211)` pair to consume at `(a, b, h)`, exactly as `outer_combine_h` consumes
`h211_of_logChowla2Fails_h`.

⟦THE DESIGN, IN THREE LINES — freeze `2026-09-03-math-FREEZE-lambda-bv-wave2S-F2.md` §1⟧
* Tao (3.16) (textdump:1278-1284) restricts the window index to the class `j ≡ p·b (mod a)`:
  `E Σ_p (c_p/p) Σ_{j : j, j+ph ∈ [1,H]} 1_{j ≡ pb (a)} g₁(an+j) g₂(an+j+ph) ≫ ε·H/log H`.  In the
  corpus's 0-indexed window (`windowVal H v j = λ(m+j+1)`) that filter is `j + 1 ≡ p·b (mod a)`,
  spelled `((j + 1 : ℕ) : ZMod a) = ((p·b : ℕ) : ZMod a)` — `p·b` and not `b`, because the
  multiplicativity step MULTIPLIES the argument by `p` (`n ↦ pn`, textdump:758).  ⭐ **THE FILTER IS
  A CONJUNCT ON THE SUMMATION INDEX `(j, p)` AND NEVER TOUCHES THE RESIDUE DATUM.**  Tao's gate
  `an + j ≡ pb (mod ap)` (the display at :741, the statement from :732) splits by CRT
  (`gcd(a, p) = 1`: `a ≤ ε²H₋/2 < p` by the regime's `hcoprime`; the kernel receipt is
  `coprime_PH_of_le`, `PrimeWindow.lean:143-160`) into `p ∣ an + j`
  — the landed gate on `y = m mod P_H` at `m = a·n` — and `j ≡ pb (mod a)`, which reads no `y`.
  So the carrier `ZMod (PH eps H)` is UNCHANGED and F1's STOP ("the filter cannot be carried through
  `fBridgeF`'s carrier without a new carrier") is cleared by inspection, not by a construction.
* ⛔ The filter sits on the FIRST factor's index only (`x_{1,j}`), never on `x_{2,j+ph}` — it
  cannot be pushed into the window pattern `v` (masking `v` would filter both factors and demand
  `ph ≡ 0 (mod a)`).  Hence a NEW definition `fBridgeG_aff`, not `fBridgeG_h` at a masked window.
* The main term is `SP·(H/a)·|X_aff|`: only `H/a` of the `j` survive the class, so `c ↦ cM/(2a)`
  and `c₁ ↦ c₁/a` (refuter §D: forced, entering at Lemma 2.5's normaliser).  The box bound
  `H/p + 1`, the residue-sum collapse and the whole concentration cone are `a`-FREE (the filter
  only REMOVES terms), so the Hoeffding substrate is reused verbatim, as the `h`-fork reused it.

⛔ **Degenerate values.**  `a = 0`: `ZMod 0 = ℤ` and the filter reads `j + 1 = p·b` in `ℤ`; every
identity and bound below is still true, `(H : ℝ) / 0 = 0` makes `hreduce_aff` trivial and
`cM / (2·0) = 0` makes the explicit conclusion `0 ≤ |…|`; `0 < a` is carried where a POSITIVE
constant is exported.  `h = 0` inherits the `h`-lane's degeneracy.  `b` is unconstrained in every
statement below EXCEPT `affCollapse_base_point`, which carries `b < a`: the collapsed base point is
the seed's `a·m' + b` ONLY for the reduced residue (at `a = 2, b = 3` the collapse lands on
`2m' + 1`, not `2m' + 3`), and the regime's `hb : b ≤ Hlo` is the WRONG ceiling for that — F4's
producer of `hreduce_aff` carries `hblt : b < a` (or the affine regime gains the field; F4's design
block decides).  At the prize instance `(210, 209, 2)` it holds.  `H = 0, 1`: `Finset.range H` and
`Fin H` degenerate as in `FBridge`.  `a = 1, b = 0`: the filter is `True` (`ZMod 1` is a
subsingleton) and every object is the landed `_h` member — the `_one_zero` compats say so.

⛔ **WHICH STATEMENTS POLICE THE FILTER'S SPELLING.**  None of the 19 producer-chain obligations
does: every identity carries the filter expression on BOTH sides (B7/B8/B12/P1), the `(1, 0)`
compats live at `ZMod 1` where every spelling is `True`, the bounds only lose terms, and C1–C4
never unfold `fBridgeF_aff` — the whole chain lands green under a WRONG filter (the F1 verdict's
§B3 shape, one wave later).  The kernel tripwires are the F2-T block: `affFilter_spec_three` (the
predicate at `a = 3`, where `p·b ≢ b`), `affFilter_spec_two` (the `j` vs `j + 1` axis) and
`fBridgeG_aff_two_one` (the OBJECT at `(2, 1)`, its surviving index set spelled `j % 2 = 0`).  A
wrong `H/a` is first caught at F4's `hreduce_aff` discharge.

Scope: definitions and the producer-chain statements only; `hreduce_aff` is a HYPOTHESIS here
exactly as `hreduce` is in `Prop26` (its discharge is F4's, at the stride measure).  Nothing here
produces `LogChowlaAffSupply`, moves a door, or bears on twin primes.  Import direction:
`Salt.Entropy`-internal; nothing from `Salt/MR` or `Salt/TwinBar`.
-/
import Salt.Entropy.Chowla.StrideFork
import Salt.Entropy.Chowla.Prop26
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

variable (eps : ℚ) (H : ℕ)

/-! ## F2-B — the F-function with the class filter (Tao (3.14)/(3.16) at `(a, b, h)`) -/

/-- **F2-B1 (def).**  The per-prime component at stride `a`, offset `b`, shift `h`:
`G_{p}^{(a,b,h)}(v)(r) = ∑_{j < H} 1_{(j+1 : ZMod p) = -r} · 1_{j+1 ≡ p·b (a)} · v_j · v_{j+p·h}`.
The gate is the landed `h`-free one on the base index; the class filter is the second conjunct,
on `(j, p)` alone.  `fBridgeG_h` is the `(1, 0)` member (`fBridgeG_aff_one_zero`). -/
noncomputable def fBridgeG_aff (a b h : ℕ) (v : Fin H → ℤ) (p : primeWindow eps H) :
    ZMod (p : ℕ) → ℝ :=
  fun r => ∑ j ∈ Finset.range H,
    if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
        ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0

/-- **F2-B2 (def).**  The assembly at `(a, b, h)`: `∑_{p ∈ 𝒫_H} G_p^{(a,b,h)}(v) ∘ residueProj p`,
the `∑_i G_i (proj_i ·)` shape `hoeffding_residueProj` centers on — the carrier is the landed
`ZMod (PH eps H)`. -/
noncomputable def fBridgeF_aff (a b h : ℕ) (v : Fin H → ℤ) : ZMod (PH eps H) → ℝ :=
  fun y => ∑ p : primeWindow eps H, fBridgeG_aff eps H a b h v p (residueProj eps H p y)

/-- **F2-B3 (class B) — the `(1, 0)` compat for `G`.**  At `a = 1` the filter compares two
elements of `ZMod 1`, a subsingleton (`Fin 1`), so the second conjunct is `True`: `funext r; unfold
fBridgeG_aff fBridgeG_h; refine Finset.sum_congr rfl (fun j _ => ?_); simp only
[eq_iff_true_of_subsingleton, and_true]` (recipe VERIFIED in a scratch probe at the freeze's v2,
09/03 18:1x; a local `hsub : ∀ u w : ZMod 1, u = w` is NOT a rewrite rule — its LHS is a bound
variable — and would leave `x = x`, which `and_true` cannot see).  Like `fBridgeG_h_one`, this
compat CANNOT police the filter's spelling — at `a = 1` every spelling is `True`; the filter's
tripwires are the F2-T block. -/
theorem fBridgeG_aff_one_zero (h : ℕ) (v : Fin H → ℤ) (p : primeWindow eps H) :
    fBridgeG_aff eps H 1 0 h v p = fBridgeG_h eps H h v p := by
  funext r
  unfold fBridgeG_aff fBridgeG_h
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [eq_iff_true_of_subsingleton, and_true]

/-- **F2-B4 (class A) — the `(1, 0)` compat for `F`.**  Termwise from `fBridgeG_aff_one_zero`
(`funext y; unfold fBridgeF_aff fBridgeF_h; exact Finset.sum_congr rfl (fun p _ => by rw
[fBridgeG_aff_one_zero])`). -/
theorem fBridgeF_aff_one_zero (h : ℕ) (v : Fin H → ℤ) :
    fBridgeF_aff eps H 1 0 h v = fBridgeF_h eps H h v := by
  funext y
  unfold fBridgeF_aff fBridgeF_h
  exact Finset.sum_congr rfl (fun p _ => by rw [fBridgeG_aff_one_zero])

/-- **F2-B5 (class B) — the deterministic box bound at `(a, b, h)`**:
`|G_p^{(a,b,h)}(v)(r)| ≤ H/p + 1`
for a `‖·‖ ≤ 1` pattern, uniformly in `a, b, h`.  The `h`-script (`fBridgeG_h_abs_le`,
`FBridge.lean:572`) with ONE extra step: each summand `|if gate ∧ filter then t else 0|` is
`≤ if gate then 1 else 0` (`split_ifs` on the conjunction; the filtered-out terms are `0 ≤ 1`, the
kept ones are `windowVal_prod_abs_le`), after which the residue-class count
`card_filter_natCast_eq_le H (-r - 1)` is the landed line.  The filter only REMOVES terms, so no
`a` appears in the bound. -/
lemma fBridgeG_aff_abs_le (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (p : primeWindow eps H) (r : ZMod (p : ℕ)) :
    |fBridgeG_aff eps H a b h v p r| ≤ (H : ℝ) / (p : ℝ) + 1 := by
  classical
  unfold fBridgeG_aff
  calc |∑ j ∈ Finset.range H, if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
            ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0|
      ≤ ∑ j ∈ Finset.range H, |if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
            ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range H, if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hA : ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
        · rw [if_pos hA]
          by_cases hB : ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)
          · rw [if_pos (And.intro hA hB)]
            exact windowVal_prod_abs_le hv j (j + (p : ℕ) * h)
          · have hn : ¬ (((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
                ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)) := fun hc => hB hc.2
            rw [if_neg hn]
            simp
        · have hn : ¬ (((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
              ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)) := fun hc => hA hc.1
          rw [if_neg hA, if_neg hn]
          simp
    _ = (((Finset.range H).filter
          (fun j : ℕ => ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ ≤ (H : ℝ) / (p : ℝ) + 1 := by
        have hset : (Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r)
            = (Finset.range H).filter (fun j : ℕ => (j : ZMod (p : ℕ)) = -r - 1) := by
          apply Finset.filter_congr
          intro j _
          rw [Nat.cast_add, Nat.cast_one, eq_sub_iff_add_eq]
        rw [hset]
        have hcard := card_filter_natCast_eq_le H (-r - 1)
        have hcast : (((Finset.range H).filter
            (fun j : ℕ => (j : ZMod (p : ℕ)) = -r - 1)).card : ℝ)
            ≤ ((H / (p : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
        have hdiv : ((H / (p : ℕ) : ℕ) : ℝ) ≤ (H : ℝ) / (p : ℝ) := Nat.cast_div_le
        push_cast at hcast
        linarith

/-- **F2-B6 (class A).**  The `[lo, hi]` box form: `Set.mem_Icc.mpr (abs_le.mp (fBridgeG_aff_abs_le
…))`. -/
lemma fBridgeG_aff_mem_Icc (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (p : primeWindow eps H) (r : ZMod (p : ℕ)) :
    fBridgeG_aff eps H a b h v p r
      ∈ Set.Icc (-((H : ℝ) / (p : ℝ) + 1)) ((H : ℝ) / (p : ℝ) + 1) := by
  exact Set.mem_Icc.mpr (abs_le.mp (fBridgeG_aff_abs_le eps H a b h hv p r))

/-- **F2-B7 (class B) — the residue-sum identity at `(a, b, h)`** (the mean's numerator):
`∑_{r ∈ ZMod p} G_p^{(a,b,h)}(v)(r) = ∑_{j < H} 1_{j+1 ≡ pb (a)} · v_j·v_{j+ph}`.  The `h`-script
(`fBridgeG_h_sum_over_residues`, `FBridge.lean:648`): `Finset.sum_comm`, then per `j` the
`r`-sum of `if gate r ∧ filter then t else 0` is `if filter then (∑_r if gate r then t else 0)
else 0` (`by_cases hf : filter` and `simp only [hf, and_true, and_false, if_false,
Finset.sum_const_zero]`), and the inner sum collapses at `r = -(j+1)` exactly as at `h`
(`Finset.sum_ite_eq'` after the `hcond` flip).  ⛔ B7 polices the GATE's residue collapse, NOT the
filter: the class filter appears identically on both sides, so this identity proves under ANY
spelling of it (the refuter's kill A1).  The arithmetic "at `a = 2, b = 1` the EVEN `j` survive"
is true, and it is `fBridgeG_aff_two_one` (F2-T3) that asserts it in the kernel. -/
lemma fBridgeG_aff_sum_over_residues (a b h : ℕ) {v : Fin H → ℤ} (p : primeWindow eps H) :
    ∑ r : ZMod (p : ℕ), fBridgeG_aff eps H a b h v p r
      = ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0 := by
  classical
  unfold fBridgeG_aff
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hf : ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)
  · rw [if_pos hf]
    have hcond : ∀ r : ZMod (p : ℕ),
        (((j + 1 : ℕ) : ZMod (p : ℕ)) = -r ∧ ((j + 1 : ℕ) : ZMod a)
            = (((p : ℕ) * b : ℕ) : ZMod a)) ↔ (r = -((j + 1 : ℕ) : ZMod (p : ℕ))) := by
      intro r
      constructor
      · rintro ⟨h1, -⟩; rw [h1, neg_neg]
      · intro h1; exact ⟨by rw [h1, neg_neg], hf⟩
    calc ∑ r : ZMod (p : ℕ), (if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
            ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0)
        = ∑ r : ZMod (p : ℕ), (if r = -((j + 1 : ℕ) : ZMod (p : ℕ)) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun r _ => ?_); rw [if_congr (hcond r) rfl rfl]
      _ = (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) := by
          rw [Finset.sum_ite_eq' Finset.univ (-((j + 1 : ℕ) : ZMod (p : ℕ)))]; simp
  · rw [if_neg hf]
    refine Finset.sum_eq_zero (fun r _ => ?_)
    have hn : ¬ (((j + 1 : ℕ) : ZMod (p : ℕ)) = -r ∧ ((j + 1 : ℕ) : ZMod a)
        = (((p : ℕ) * b : ℕ) : ZMod a)) := fun hc => hf hc.2
    rw [if_neg hn]

/-- **F2-B8 (class B) — the mean identity at `(a, b, h)`**:
`E_y[G_p^{(a,b,h)}(v)(y mod p)] = (1/p)·∑_{j} 1_{j+1 ≡ pb (a)} v_j v_{j+ph}`.  The `h`-script
(`fBridgeG_h_mean`, `FBridge.lean:671`) VERBATIM — `residueProj_fiber_card` never sees `v`, the
fibre equidistribution is filter-blind — with `fBridgeG_aff_sum_over_residues` in place of
`fBridgeG_h_sum_over_residues` at the one `rw`.  This is the decoupled `y`-mean that the affine
circle-method estimate (F3/F4's `hcirc_aff`) bounds. -/
lemma fBridgeG_aff_mean (a b h : ℕ) {v : Fin H → ℤ} (p : primeWindow eps H) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
        fBridgeG_aff eps H a b h v p (residueProj eps H p ω)]
      = (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0 := by
  classical
  set μ := uniformOn (Set.univ : Set (ZMod (PH eps H))) with hμ
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty
  have hmass : ∀ ω : ZMod (PH eps H), μ.real {ω} = ((PH eps H : ℝ))⁻¹ := by
    intro ω
    have hs : μ {ω} = ((PH eps H : ℝ≥0∞))⁻¹ := by
      rw [hμ, uniformOn_univ, Measure.count_singleton, ZMod.card]; simp
    rw [measureReal_def, hs, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [integral_fintype Integrable.of_finite]
  simp only [hmass, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hfib : ∑ ω : ZMod (PH eps H), fBridgeG_aff eps H a b h v p (residueProj eps H p ω)
      = ∑ r : ZMod (p : ℕ), (PH eps H / (p : ℕ)) • fBridgeG_aff eps H a b h v p r := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (ZMod (p : ℕ))))
        (fun ω _ => Finset.mem_univ (residueProj eps H p ω))
        (fun ω => fBridgeG_aff eps H a b h v p (residueProj eps H p ω))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_congr rfl (fun ω hω =>
      show fBridgeG_aff eps H a b h v p (residueProj eps H p ω)
          = fBridgeG_aff eps H a b h v p r by
        rw [(Finset.mem_filter.mp hω).2]), Finset.sum_const, residueProj_fiber_card]
  rw [hfib]
  simp only [nsmul_eq_mul]
  rw [← Finset.mul_sum, fBridgeG_aff_sum_over_residues]
  have hpp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos.ne'
  have harith : (PH eps H : ℝ)⁻¹ * ((PH eps H / (p : ℕ) : ℕ) : ℝ) = 1 / (p : ℝ) := by
    rw [Nat.cast_div (dvd_PH eps H p) hpp0]
    have hp0 : (PH eps H : ℝ) ≠ 0 := by exact_mod_cast (PH_pos eps H).ne'
    field_simp
  rw [← mul_assoc, harith]

/-- **F2-B9 (class A) — the raw concentration bound at `(a, b, h)`**: `hoeffding_residueProj eps H
(fBridgeG_aff eps H a b h v) (fun i x => fBridgeG_aff_mem_Icc eps H a b h hv i x) hδ` — the SAME
box, so the `h`-proof term transfers with the name changed (`fBridge_h_concentration_raw`,
`FBridge.lean:711`). -/
theorem fBridge_aff_concentration_raw (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_aff eps H a b h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_aff eps H a b h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 / (2 * ((∑ p : primeWindow eps H,
          (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  exact hoeffding_residueProj eps H (fBridgeG_aff eps H a b h v)
    (fun i x => fBridgeG_aff_mem_Icc eps H a b h hv i x) hδ

/-- **F2-B10 (class A) — the usable concentration bound at `(a, b, h)`**, exponent
`2·exp(−δ²/(2(ε²H+1)(2/ε²+1)²))` UNCHANGED (`fBridge_var_le` is `v`-, `h`- and `a`-free).  The
`h`-script (`fBridge_h_concentration`, `FBridge.lean:726`) with the raw bound's name moved. -/
theorem fBridge_aff_concentration (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_aff eps H a b h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_aff eps H a b h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 /
          (2 * (((eps : ℝ) ^ 2 * (H : ℝ) + 1) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2))) := by
  refine le_trans (fBridge_aff_concentration_raw eps H a b h hv hδ) ?_
  have hSpos : 0 < ((∑ p : primeWindow eps H,
      (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_sum]
    haveI : Nonempty (primeWindow eps H) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    refine Finset.sum_pos (fun p _ => ?_) Finset.univ_nonempty
    rw [fBridge_varTerm eps H p]; positivity
  have hSle := fBridge_var_le eps H heps
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [neg_div, neg_div, neg_le_neg_iff,
      div_le_div_iff₀ (by positivity) (mul_pos (by norm_num) hSpos)]
  nlinarith [sq_nonneg δ, hSle, hSpos]

/-- **F2-B11 (class A) — the sharp (one-log) concentration bound at `(a, b, h)`**: the
`h`-script (`fBridge_h_concentration_sharp`, `FBridge.lean:752`) verbatim; `fBridge_var_le_sharp`
is reused and the exponent is IDENTICAL — the stride and the offset cost nothing in the
concentration grade. -/
theorem fBridge_aff_concentration_sharp (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ)) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_aff eps H a b h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_aff eps H a b h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) /
          (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)) := by
  refine le_trans (fBridge_aff_concentration_raw eps H a b h hv hδ) ?_
  set D := 2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 with hDdef
  set S := ((∑ p : primeWindow eps H,
      (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) with hSdef
  have hepsne : (eps : ℝ) ≠ 0 := by exact_mod_cast heps.ne'
  have hlogpos : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
  have hlogne : Real.log (H : ℝ) ≠ 0 := hlogpos.ne'
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    rcases Nat.eq_zero_or_pos H with hh | hh
    · exfalso; rw [hh, Nat.cast_zero, Real.log_zero] at hlog; linarith
    · exact_mod_cast hh
  have hSpos : 0 < S := by
    rw [hSdef, NNReal.coe_sum]
    haveI : Nonempty (primeWindow eps H) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    refine Finset.sum_pos (fun p _ => ?_) Finset.univ_nonempty
    rw [fBridge_varTerm eps H p]; positivity
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hSle : S ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
      * (2 / (eps : ℝ) ^ 2 + 1) ^ 2 := by
    rw [hSdef]; exact fBridge_var_le_sharp eps H heps hcard
  have hkey : 2 * S * Real.log (H : ℝ) ≤ D := by
    have hmul : 2 * S * Real.log (H : ℝ)
        ≤ 2 * (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
            * (2 / (eps : ℝ) ^ 2 + 1) ^ 2) * Real.log (H : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hlogpos.le
      exact mul_le_mul_of_nonneg_left hSle (by norm_num)
    refine hmul.trans_eq ?_
    rw [hDdef]; field_simp
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hSpos) hDpos]
  nlinarith [sq_nonneg δ, hkey]

/-- **F2-B12 (class A) — the sharp decoupled-mean corollary at `(a, b, h)`** — the deviation set
written with the FILTERED decoupled mean `∑_p (1/p) ∑_j 1_{j+1 ≡ pb (a)} v_j v_{j+ph}`
(`fBridgeG_aff_mean` substituted into `fBridge_aff_concentration_sharp`, as
`fBridge_h_concentration_decoupled_sharp`, `FBridge.lean:801`).  ⚠ SITE 2 of the synchronised
offset spellings: `badSet_aff` (F4) must spell this set byte-identically. -/
theorem fBridge_aff_concentration_decoupled_sharp (a b h : ℕ)
    {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ)) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_aff eps H a b h v ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
            ∑ j ∈ Finset.range H,
              if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
                (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0|}
      ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) /
          (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)) := by
  have hmean : (∑ p : primeWindow eps H,
        (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
          fBridgeG_aff eps H a b h v p (residueProj eps H p ω)])
      = ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0 :=
    Finset.sum_congr rfl (fun p _ => fBridgeG_aff_mean eps H a b h p)
  have hq := fBridge_aff_concentration_sharp eps H a b h hv heps hne hδ hC₀ hcard hlog
  rw [hmean] at hq
  exact hq

/-! ## F2-T — the filter's KERNEL TRIPWIRES (the refuter's kill A1: no producer-chain statement is
filter-sensitive, so the spelling `j + 1 ≡ p·b (mod a)` is pinned here, decidably) -/

/-- **F2-T1 (class A) — the separating tripwire, at `a = 3`.**  `a = 3, b = 1, p = 2` ⇒ `p·b = 2`
⇒ `j + 1 ≡ 2 (mod 3)` ⇒ `j ∈ {1, 4}` in `range 6`.  The three rival spellings give three DIFFERENT
sets — `b` in place of `p·b` gives `{0, 3}`, `j` in place of `j + 1` gives `{2, 5}` — so this one
`decide` separates all of them (at `a = 2` every odd `p` has `p·b ≡ b`, which is why the freeze's
own `a = 2` instance could not).  Recipe: `decide` (VERIFIED in a scratch probe 09/03 18:1x, with
the `{0, 3}` mutant refused by the same tactic). -/
lemma affFilter_spec_three :
    (Finset.range 6).filter
      (fun j => ((j + 1 : ℕ) : ZMod 3) = ((2 * 1 : ℕ) : ZMod 3)) = {1, 4} := by
  decide

/-- **F2-T2 (class A) — the index-shift axis, at `a = 2`.**  `a = 2, b = 1, p = 3` ⇒ `j + 1` odd ⇒
the EVEN `j`: `{0, 2, 4}` in `range 6` (a filter on `j` would give the odd ones).  Recipe: `decide`
(VERIFIED in the same probe). -/
lemma affFilter_spec_two :
    (Finset.range 6).filter
      (fun j => ((j + 1 : ℕ) : ZMod 2) = ((3 * 1 : ℕ) : ZMod 2)) = {0, 2, 4} := by
  decide

/-- **F2-T3 (class B) — the OBJECT's tripwire: `fBridgeG_aff` at `(a, b) = (2, 1)` with the
surviving index set spelled ARITHMETICALLY.**  For an odd window prime `p·1 ≡ 1 (mod 2)`, so the
filter keeps exactly the even `j`, and the per-prime component is the gate-only sum over
`(range H).filter (· % 2 = 0)`.  FALSE under `j ≡ p·b`, under `b` in place of `p·b`, and under no
filter — the kernel tripwire the docstrings of v1 promised and did not have.  Recipe: `unfold
fBridgeG_aff`; `Finset.sum_filter` on the right, then `Finset.sum_congr rfl` and per `j` the
filter conjunct is `((j+1 : ℕ) : ZMod 2) = ((p*1 : ℕ) : ZMod 2) ↔ j % 2 = 0` by
`ZMod.natCast_eq_natCast_iff'` + `Nat.odd_iff.mp hp` + `omega`; `split_ifs` closes. -/
lemma fBridgeG_aff_two_one (h : ℕ) (v : Fin H → ℤ) (p : primeWindow eps H)
    (hp : Odd (p : ℕ)) (r : ZMod (p : ℕ)) :
    fBridgeG_aff eps H 2 1 h v p r
      = ∑ j ∈ (Finset.range H).filter (fun j => j % 2 = 0),
          if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0 := by
  classical
  unfold fBridgeG_aff
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hiff : ((j + 1 : ℕ) : ZMod 2) = (((p : ℕ) * 1 : ℕ) : ZMod 2) ↔ j % 2 = 0 := by
    rw [ZMod.natCast_eq_natCast_iff']
    have hpo : (p : ℕ) % 2 = 1 := Nat.odd_iff.mp hp
    omega
  by_cases hj : j % 2 = 0
  · rw [if_pos hj]
    by_cases hg : ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
    · rw [if_pos (And.intro hg (hiff.mpr hj)), if_pos hg]
    · have hn : ¬ (((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
          ∧ ((j + 1 : ℕ) : ZMod 2) = (((p : ℕ) * 1 : ℕ) : ZMod 2)) := fun hc => hg hc.1
      rw [if_neg hn, if_neg hg]
  · have hn : ¬ (((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
        ∧ ((j + 1 : ℕ) : ZMod 2) = (((p : ℕ) * 1 : ℕ) : ZMod 2)) := fun hc => hj (hiff.mp hc.2)
    rw [if_neg hn, if_neg hj]

/-! ## F2-P — Prop 2.6 at the affine forms: the pointwise unfold and the `(p, r)`-collapse -/

/-- **F2-P1 (class B) — the pointwise F-bridge unfold at `(a, b, h)`, at ANY base point `m`.**
The twin of `fBridgeF_h_liouville_apply` (`Prop26.lean:212`) with `n ↦ m` and the filter riding
the gate: for each window prime `p` and `j < H` the gate `p ∣ m+j+1` AND the class `j+1 ≡ pb (a)`
select `λ(m+j+1)·(windowVal … (j + p·h))`.  Under the stride measure the base point is `m = a·n`
(`integral_logMeasureAff`), which is Tao's `an + j` (3.16).  The `h`-script transfers: `hgate`
is the landed `push_cast; ring` congruence, and the `if` splits on the conjunction (`by_cases hc :
gate; by_cases hf : filter; simp only [hc, hf, hgate, …]`, the kept branch closing by
`windowVal_liouvilleWindow H m j hjH`). -/
lemma fBridgeF_aff_liouville_apply (a b h : ℕ) (m : ℕ) :
    fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          if ((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
              ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (m + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ)
          else 0 := by
  unfold fBridgeF_aff
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [residueProj_residueWindow]
  unfold fBridgeG_aff
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjH : j < H := Finset.mem_range.mp hj
  have hgate : ((j + 1 : ℕ) : ZMod (p : ℕ)) = -((m : ℕ) : ZMod (p : ℕ))
      ↔ ((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 := by
    rw [show ((m + j + 1 : ℕ) : ZMod (p : ℕ))
          = ((j + 1 : ℕ) : ZMod (p : ℕ)) + ((m : ℕ) : ZMod (p : ℕ)) from by push_cast; ring,
        add_eq_zero_iff_eq_neg]
  by_cases hc : ((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
  · by_cases hf : ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)
    · rw [if_pos (And.intro (hgate.mpr hc) hf), if_pos (And.intro hc hf),
        windowVal_liouvilleWindow H m j hjH]
    · have hn1 : ¬ (((j + 1 : ℕ) : ZMod (p : ℕ)) = -((m : ℕ) : ZMod (p : ℕ))
          ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)) := fun hq => hf hq.2
      have hn2 : ¬ (((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
          ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)) := fun hq => hf hq.2
      rw [if_neg hn1, if_neg hn2]
  · have hn1 : ¬ (((j + 1 : ℕ) : ZMod (p : ℕ)) = -((m : ℕ) : ZMod (p : ℕ))
        ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)) := fun hq => hc (hgate.mp hq.1)
    have hn2 : ¬ (((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
        ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a)) := fun hq => hc hq.1
    rw [if_neg hn1, if_neg hn2]

/-- **F2-P2 (class A) — the `(1, 0)` recovery of the pointwise unfold**, stated at the LANDED
conclusion of `fBridgeF_h_liouville_apply` and discharged through `fBridgeF_aff_one_zero`
(`rw [fBridgeF_aff_one_zero, fBridgeF_h_liouville_apply]`).  A conservativity check; it cannot
see the filter. -/
theorem fBridgeF_aff_liouville_apply_one_zero (h : ℕ) (m : ℕ) :
    fBridgeF_aff eps H 1 0 h (liouvilleWindow H m) (residueWindow eps H m)
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          if ((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (m + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ)
          else 0 := by
  rw [fBridgeF_aff_one_zero, fBridgeF_h_liouville_apply]

/-- **F2-P3 (class A) — THE INDEX ARITHMETIC OF THE `(p, r)`-COLLAPSE AT STRIDE `a`.**  On the
residue class `n ≡ rⱼ (mod p)` realising the gate `p ∣ a·n + j + 1`, write `p·k = a·rⱼ + j + 1`
(the gate at the class representative); then at `n = p·m + rⱼ` the window index is a multiple
of `p`: `a·(p·m + rⱼ) + j + 1 = p·(a·m + k)`.  Recipe (VERIFIED in a scratch probe 09/03 18:1x):
`have hx : a * (p * m + rj) + j + 1 = p * (a * m) + (a * rj + j + 1) := by ring` then
`rw [hx, ← hk]; ring`.  ⛔ NOT `omega` (it atomises `a * (p*m+rj)`, `p * (a*m+k)` and `p * k` as
unrelated atoms) and NOT a bare `rw [← hk]` (the goal has no subterm `a * rj + j + 1` until `hx`
exposes it).  This is the line the freeze names "`a·r + j + 1` in place of `r + j + 1`". -/
lemma affGate_index_eq (a p j rj k m : ℕ) (hk : p * k = a * rj + j + 1) :
    a * (p * m + rj) + j + 1 = p * (a * m + k) := by
  have hx : a * (p * m + rj) + j + 1 = p * (a * m) + (a * rj + j + 1) := by ring
  rw [hx, ← hk]; ring

/-- **F2-P4 (class A) — the multiplicativity collapse at stride `a`.**  With the gate
`p·k = a·rⱼ + j + 1` and `p ≠ 0`, the dilated pair collapses to the seed's shape at the base point
`a·m + k`: `λ(a(pm+rⱼ)+j+1)·λ(a(pm+rⱼ)+j+ph+1) = λ(am+k)·λ(am+k+h)`.  `affGate_index_eq` rewrites
both arguments (`a(pm+rⱼ)+j+ph+1 = p(am+k) + p·h` by `omega` from the first), then
`liouville_collapse_h p h hp (a*m+k)` (`ShiftFork.lean:472`) closes (the `omega` here IS sound: with
`affGate_index_eq` in context the atoms are shared and the goal is linear in them).  Downstream
(F4) `k ≡ b (mod a)` because `p·k ≡ j+1 ≡ p·b (mod a)` with `gcd(p, a) = 1` — the class filter is
what makes the collapsed base point `a·m' + b`, the seed's form; that congruence is F4's, and the
step from it to the seed's form is `affCollapse_base_point` below, which needs `b < a`. -/
lemma liouville_collapse_aff (a p j rj k m h : ℕ) (hp : p ≠ 0)
    (hk : p * k = a * rj + j + 1) :
    (ArithmeticFunction.liouville (a * (p * m + rj) + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (a * (p * m + rj) + j + p * h + 1) : ℝ)
      = (ArithmeticFunction.liouville (a * m + k) : ℝ)
          * (ArithmeticFunction.liouville (a * m + k + h) : ℝ) := by
  have h1 := affGate_index_eq a p j rj k m hk
  have h2 : a * (p * m + rj) + j + p * h + 1 = p * (a * m + k) + p * h := by
    rw [← h1]; ring
  rw [h1, h2]
  exact liouville_collapse_h p h hp (a * m + k)

/-- **F2-P5 (class A) — the per-pair dilation reduction at stride `a`.**  `dilation_error_div`
(`Dilation.lean:161`, generic in `f`) at `q ↦ p`, `r ↦ rⱼ`, `M ↦ 1` and
`f := fun n => λ(a·n + j + 1)·λ(a·n + j + p·h + 1)` — the twin of `perPair_dilation_h`
(`Prop26.lean:257`) with the window read at `a·n`.  The dilated summand is `f (p·m + rⱼ)`
beta-reduced: `a·(p·m + rⱼ) + j + 1` (the freeze's `a·r + j + 1`).  The `|f| ≤ 1` side condition
is the same two-factor bound (`abs_liouville_le_one`). -/
lemma perPair_collapse_aff {x ω : ℕ} (a h p j rj : ℕ) (hp : 1 ≤ p) (hrj : rj ≤ x / ω)
    {Z : ℝ} (hZ : 0 < Z) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = rj),
        ((ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
          * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ)) / (n : ℝ)) / Z
        - 1 / (p : ℝ) *
          ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = rj)).image (fun n => n / p),
              ((ArithmeticFunction.liouville (a * (p * m + rj) + j + 1) : ℝ)
                * (ArithmeticFunction.liouville (a * (p * m + rj) + j + p * h + 1) : ℝ))
                / (m : ℝ)) / Z)|
      ≤ 2 * 1 * (rj : ℝ) / (p : ℝ) ^ 2 / Z := by
  exact dilation_error_div hp hrj
    (f := fun n => (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ)) (M := 1)
    (fun n => by
      rw [abs_mul]
      exact mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _))
    hZ

/-- **F2-P6 (class A) — THE COLLAPSED BASE POINT IS THE SEED'S `a·m' + b` ONLY UNDER `b < a`** (the
refuter's kill A2).  From the class congruence `k ≡ b (mod a)` (F4 derives it from
`p·k ≡ j + 1 ≡ p·b (mod a)` and `gcd(p, a) = 1`) and the REDUCED residue `b < a`, `k = a·(k/a) + b`
— so the collapsed pair `λ(am+k)·λ(am+k+h)` is `λ(a·m' + b)·λ(a·m' + b + h)` at `m' = m + k/a`.
Without `b < a` the conclusion is FALSE (`a = 2, b = 3, k = 1`): the regime's `hb : b ≤ Hlo` does
not supply it, so F4's `hreduce_aff` producer carries `hblt : b < a`.  Recipe (VERIFIED in a
scratch probe 09/03 18:1x): `have h1 := (ZMod.natCast_eq_natCast_iff' k b a).mp hk; rw
[Nat.mod_eq_of_lt hblt] at h1; have h2 := Nat.div_add_mod k a; omega`. -/
lemma affCollapse_base_point (a b k : ℕ) (hblt : b < a)
    (hk : (k : ZMod a) = (b : ZMod a)) : k = a * (k / a) + b := by
  have h1 := (ZMod.natCast_eq_natCast_iff' k b a).mp hk
  rw [Nat.mod_eq_of_lt hblt] at h1
  have h2 := Nat.div_add_mod k a
  omega

/-! ## F2-C — the `(c₁, h211)` glue at the affine forms (the `ChowlaFailure` twins) -/

/-- **F2-C1 (class B) — Tao Prop 2.6 at the affine forms, EXPLICIT constant.**  From the seed
`hseed : δ ≤ |X_aff|` (`X_aff = ∫ λ(m+b)λ(m+b+h) ∂(logMeasureAff a x ω)`, produced by
`singleCorr_of_failsAff'`), the Mertens lower bound `hmert` (`a`-free) and the affine reduction
`hreduce_aff` — the F-bridge integral under the STRIDE measure dominates half the main term
`SP·(H/a)·|X_aff|`, the `H/a` being the class's share of the window (Tao (3.16)) — the affine
F-bridge expectation obeys `cM/(2a) · (δ·H/log H) ≤ |∫ F_aff|`.  The `h`-script
(`fBridge_of_singleCorr_h`, `Prop26.lean:286`) with `(H : ℝ)` read as `(H : ℝ) / a` in `hkey`'s
consumer and the constant `cM/2` read as `cM/(2a)`.  No `0 < a` binder here, so the executor
case-splits `rcases Nat.eq_zero_or_pos a`: at `a = 0` the LEFT side is `cM/0 · … = 0` and the goal
is `abs_nonneg` (the right side is NOT `0`); at `0 < a` the `h`-script with `field_simp`.  The
constant is EXPLICIT so that F5's grade line reads `cM/(2a)` from the kernel,
not from prose. -/
theorem fBridge_of_singleCorr_aff (a b h : ℕ) {x ω : ℕ}
    (hlog : 1 ≤ Real.log (H : ℝ)) {cM : ℝ} (hcM : 0 < cM)
    (hmert : cM / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (hreduce : (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
          * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)|)
    {δ : ℝ} (hδ : 0 < δ)
    (hseed : δ ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|) :
    cM / (2 * (a : ℝ)) * (δ * (H : ℝ) / Real.log (H : ℝ))
      ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
          ∂(logMeasureAff a x ω)| := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.cast_zero, mul_zero, div_zero, zero_mul]
    exact abs_nonneg _
  · set SP : ℝ := ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) with hSP
    set X : ℝ := |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
        * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| with hX
    have hlogpos : (0 : ℝ) < Real.log (H : ℝ) := by linarith
    have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hane : (a : ℝ) ≠ 0 := hapos.ne'
    have hlogne : Real.log (H : ℝ) ≠ 0 := hlogpos.ne'
    have hSPnn : (0 : ℝ) ≤ SP := by
      rw [hSP]; exact Finset.sum_nonneg (fun p hp => by positivity)
    have hXnn : (0 : ℝ) ≤ X := abs_nonneg _
    have hcM_le : cM ≤ SP * Real.log (H : ℝ) := (div_le_iff₀ hlogpos).mp hmert
    have hkey : cM * δ ≤ SP * X * Real.log (H : ℝ) := by
      calc cM * δ ≤ (SP * Real.log (H : ℝ)) * X :=
            mul_le_mul hcM_le hseed hδ.le (mul_nonneg hSPnn hlogpos.le)
        _ = SP * X * Real.log (H : ℝ) := by ring
    have hstep : cM * δ * (H : ℝ) ≤ SP * X * Real.log (H : ℝ) * (H : ℝ) :=
      mul_le_mul_of_nonneg_right hkey hHnn
    have hle1 : cM / (2 * (a : ℝ)) * (δ * (H : ℝ) / Real.log (H : ℝ))
        ≤ (1 / 2) * SP * ((H : ℝ) / (a : ℝ)) * X := by
      have hlhs : cM / (2 * (a : ℝ)) * (δ * (H : ℝ) / Real.log (H : ℝ))
          = (cM * δ * (H : ℝ)) / (2 * (a : ℝ) * Real.log (H : ℝ)) := by
        field_simp
      have hrhs : (1 / 2) * SP * ((H : ℝ) / (a : ℝ)) * X
          = (SP * X * (H : ℝ)) / (2 * (a : ℝ)) := by
        field_simp
      rw [hlhs, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hstep
        (by positivity : (0 : ℝ) ≤ 2 * (a : ℝ))]
    exact hle1.trans hreduce

/-- **F2-C2 (class A) — the same, in the consumer's `∃ c` shape** (the `hprop26` binder of
`h211_aff` below and of `h211_of_logChowla2Fails_h`).
`⟨cM / (2 * a), by positivity, fBridge_of_singleCorr_aff …⟩`; `0 < a` for the positivity. -/
theorem fBridge_of_singleCorr_aff' (a b h : ℕ) (ha : 0 < a) {x ω : ℕ}
    (hlog : 1 ≤ Real.log (H : ℝ)) {cM : ℝ} (hcM : 0 < cM)
    (hmert : cM / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (hreduce : (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
          * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)|)
    {δ : ℝ} (hδ : 0 < δ)
    (hseed : δ ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|) :
    ∃ c : ℝ, 0 < c ∧
      c * (δ * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)| := by
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  refine ⟨cM / (2 * (a : ℝ)), div_pos hcM (by linarith), ?_⟩
  exact fBridge_of_singleCorr_aff eps H a b h hlog hcM hmert hreduce hδ hseed

/-- **F2-C3 (class A) — Stmt 3 at the affine forms (compose to `h211`).**  The twin of
`h211_of_logChowla2Fails_h` (`ChowlaFailure.lean:254`): feed the affine seed
`singleCorr_of_failsAff'` (F1-N2, `δ := ε/2`, under the stride measure) into the affine
Prop-2.6 conclusion `hprop26` and take `c₁ := c/2`.  The glue arithmetic is the `h`-script
verbatim (`hEq` by `ring`).  The `a`-dependence is inside `c` (`cM/(2a)` when `hprop26` is
`fBridge_of_singleCorr_aff'`), so the exported `c₁` is `cM/(4a)` on that route — F4's budget
lines read `c₁ ↦ c₁/a` here and nowhere else. -/
theorem h211_aff (a b h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ)) (heps : 0 < eps)
    (hprop26 : ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
                ∂(logMeasureAff a x ω)|)
    (hfail : logChowlaFailsAff a b h eps x ω) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)| := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hseed := singleCorr_of_failsAff' a b h eps hx hω hωx hlog2 hfail
  have hδpos : (0 : ℝ) < (eps : ℝ) / 2 := by linarith
  obtain ⟨c, hc, hbound⟩ := hprop26 hδpos hseed
  refine ⟨c / 2, by linarith, ?_⟩
  have hEq : c / 2 * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      = c * ((eps : ℝ) / 2 * (H : ℝ) / Real.log (H : ℝ)) := by ring
  rw [hEq]
  exact hbound

/-- **F2-C4 (class B) — the `(1, 0)` recovery of `h211`**, stated at the LANDED conclusion of
`h211_of_logChowla2Fails_h` (the `logMeasure` integral of `fBridgeF_h`) from the LANDED
`logChowlaFails h` hypothesis and the `h`-twin's own `hprop26` spelling, and discharged from
`h211_aff 1 0 h`: `logChowlaFailsAff_one_zero` (`AffineFork.lean:78`) converts `hfail`;
`logMeasureAff_one` and `fBridgeF_aff_one_zero` convert the integrals in both the binder and the
conclusion (`simp only [logMeasureAff_one, fBridgeF_aff_one_zero, add_zero] at *` — the seed's
summand is `λ(m + 0)·λ(m + 0 + h)`, hence `add_zero`, NOT `zero_add`, which matches nothing and is
a silent simp no-op; `AffineFork.lean:76` records the same trap).  The kill-check that the affine
family SUBSUMES the `h`-family at its model point. -/
theorem h211_aff_one_zero (h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ)) (heps : 0 < eps)
    (hprop26 : ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
                ∂(logMeasure x ω)|)
    (hfail : logChowlaFails h eps x ω) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  have hfail' : logChowlaFailsAff 1 0 h eps x ω :=
    (logChowlaFailsAff_one_zero h eps x ω).mpr hfail
  have hprop26' : ∀ {δ : ℝ}, 0 < δ →
      δ ≤ |∫ m, (ArithmeticFunction.liouville (m + 0) : ℝ)
            * (ArithmeticFunction.liouville (m + 0 + h) : ℝ) ∂(logMeasureAff 1 x ω)| →
      ∃ c : ℝ, 0 < c ∧
        c * (δ * (H : ℝ) / Real.log (H : ℝ))
          ≤ |∫ m, fBridgeF_aff eps H 1 0 h (liouvilleWindow H m) (residueWindow eps H m)
              ∂(logMeasureAff 1 x ω)| := by
    intro δ hδ hs
    simp only [logMeasureAff_one, fBridgeF_aff_one_zero, add_zero] at hs ⊢
    exact hprop26 hδ hs
  have hmain := h211_aff eps H 1 0 h hx hω hωx hlog2 heps hprop26' hfail'
  simpa only [logMeasureAff_one, fBridgeF_aff_one_zero, add_zero] using hmain

end Salt.Entropy.Chowla
