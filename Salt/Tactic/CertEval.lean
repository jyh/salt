/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.Certificate
import Salt.Twelve.BudgetPoly
import Salt.Tactic.AuditAxioms

/-!
# T1 `CertEval` — a verified reflective evaluator for the rational certificate

Tactic-ledger node T1 (`docs/blueprints/tactics.md`): turn certificate checks
(currently 10M-heartbeat `norm_num` grinds, `Salt/Twelve/Certificate.lean`) into
fast, axiom-clean **kernel** computations. This is the PROBE deliverable: the
evaluator + soundness bridge land sorry-free, and the `J⁽0⁾(F★)` certificate value
is re-verified by pure kernel reduction (`decide +kernel` — NOT `native_decide`;
the produced proof depends only on `propext, Classical.choice, Quot.sound`).

## The idea

`Jcal m F` (C1) is a 56×56 double sum whose per-pair kernel `JD` lives over
`Fin 5 → ℕ` exponent *functions* and `Finset.univ` products/sums — shapes that the
kernel reduces slowly. We repack a monomial's exponents as a plain 5-tuple
(`Exp5`), recompute the SAME per-pair value with flat `Nat` arithmetic (`cJD`), and
sum with the same `List.map`/`List.sum` skeleton (`evalJcal`). One soundness
theorem `evalJcal_eq` proves this equals `Jcal` on the lifted polynomial; the
instance is then a single kernel reduction.

## Representation choice (the experiment)

`Exp5 := ℕ × ℕ × ℕ × ℕ × ℕ` — a packed exponent tuple, NOT a `Fin 5 → ℕ`. This is
the load-bearing decision: it removes `Matrix.cons`/`Fin.cons` value access and
`Finset.univ` folds from the hot path, leaving only binary-`Nat`-backed `ℚ`
arithmetic, which the kernel reduces with its GMP-accelerated `Nat` ops. `cJD`
computes `JD_eq`'s closed form directly: the five `(aᵢ+bᵢ)!`, one budget factorial
`(6+Σ)!`, and a single `ℚ` division per pair. (Factorials are recomputed per term;
for the degree regime here (args ≤ 12) that is negligible, but a tabulation is the
first lever if higher-degree certificates make the factorial args large.)

## MEASUREMENTS (Lean v4.32.0-rc1, mathlib pinned; this machine)

Re-verifying `J_Fstar_0 : Jcal 0 Fstar = 191881/119750400`:

| path                                            | heartbeats  | kernel wall-clock |
|-------------------------------------------------|-------------|-------------------|
| landed `simp only … ; norm_num` (C1)            | 1,090,188   | ≈ 28 s (norm_num 22.2s + simp 0.75s + kernel 5.3s) |
| reflective RAW `evalJcal 0 FstarC = lit`        |     25,824  | ≈ 5.0 s           |
| reflective FULL `Jcal 0 Fstar = lit` (+ bridge) |        477  | ≈ 15.5 s          |

Heartbeat reduction: FULL **≈ 2285×**, RAW **≈ 42×** (target was ≥100×). The
`norm_num` cost is elaborator heartbeats; the reflective cost moves to the kernel
(wall-clock, un-metered), so the honest wall-clock win is ≈ 1.8× (full) / ≈ 5×
(raw). The FULL path's extra ~10 s over RAW is the `toPoly FstarC = Fstar` defeq
check — the ONE place `Fin`/`Matrix` reduction re-enters (bridging the packed rep
to the landed `Fin`-based `Fstar`); it is one-time, not per-term.

Scaling of the RAW evaluator (`decide +kernel`, degree ≤ 3, random toy certs):

| monomials n | pairwise terms n² | heartbeats | kernel wall-clock |
|-------------|-------------------|------------|-------------------|
|  56 (F★)    |  3,136            |  25,824    | ≈ 5.0 s           |
| 100         | 10,000            |  46,892    | ≈ 5.0 s           |
| 200         | 40,000            | 162,177    | ≈ 19.2 s          |

Cost is ~linear in the pairwise-term count, asymptotically ≈ 4 heartbeats and
≈ 0.5 ms of kernel time per pair.

## VERDICT (k=105 certificate)

PLAUSIBLE via this route. The ledger sizes the k=105 certificate at ~10⁴–10⁵
pairwise terms (≈ 100–316 monomials). Linear extrapolation: ≈ 5–50 s kernel and
≈ 0.4–0.4M elaborator heartbeats PER `J⁽ᵐ⁾` value — i.e. the full I + five J
certificate is minutes of kernel time, not the infeasible generic-`norm_num`
path. Remaining production engineering: (i) a factorial tabulation in `cJD` if the
k=105 optimizer runs to higher degree (larger factorial args); (ii) generate the
packed `CPoly` + its bridge instance from the off-line optimizer output; (iii)
optionally avoid the `toPoly = Fstar` defeq tax by stating the certificate over the
packed rep natively. The evaluator + bridge below are the durable core; they are
`F`-generic, so any certificate polynomial reuses them unchanged.
-/

open Nat
open Salt.Twelve

namespace Salt.CertEval


/-- A packed exponent vector: five `ℕ`s, replacing C1's `Fin 5 → ℕ` exponent
function to keep `Matrix.cons`/`Finset.univ` folds off the kernel's hot path. -/
abbrev Exp5 : Type := ℕ × ℕ × ℕ × ℕ × ℕ

/-- A packed certificate monomial: a `t^α` exponent tuple with its `ℚ` coefficient. -/
abbrev CMono : Type := Exp5 × ℚ

/-- A packed certificate polynomial (the computation-friendly mirror of C1's `Poly`). -/
abbrev CPoly : Type := List CMono

/-- Unpack an `Exp5` back to the C1 exponent function `Fin 5 → ℕ`. -/
def toE (a : Exp5) : Fin 5 → ℕ := ![a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2]

/-- Lift a packed polynomial to C1's `Poly` (the semantic bridge target). -/
def toPoly (F : CPoly) : Poly := F.map (fun p => (toE p.1, p.2))

/-- The packed per-pair `J⁽ᵐ⁾` kernel: exactly `JD_eq`'s closed-form value computed
with flat `Nat` arithmetic — five `(aᵢ+bᵢ)!`, one budget factorial `(6+Σ)!`, and a
single `ℚ` division. Reduces to a normalized `Rat` in the kernel per pair. -/
def cJD (a b : Exp5) (m : Fin 5) : ℚ :=
  let s0 := a.1 + b.1
  let s1 := a.2.1 + b.2.1
  let s2 := a.2.2.1 + b.2.2.1
  let s3 := a.2.2.2.1 + b.2.2.2.1
  let s4 := a.2.2.2.2 + b.2.2.2.2
  let P : ℕ := Nat.factorial s0 * Nat.factorial s1 * Nat.factorial s2 *
    Nat.factorial s3 * Nat.factorial s4
  let D : ℕ := Nat.factorial (6 + (s0 + s1 + s2 + s3 + s4))
  match m with
  | 0 => ((P * ((s0 + 1) * (s0 + 2)) : ℕ) : ℚ) / (((a.1 + 1) * (b.1 + 1) * D : ℕ) : ℚ)
  | 1 => ((P * ((s1 + 1) * (s1 + 2)) : ℕ) : ℚ) / (((a.2.1 + 1) * (b.2.1 + 1) * D : ℕ) : ℚ)
  | 2 => ((P * ((s2 + 1) * (s2 + 2)) : ℕ) : ℚ) / (((a.2.2.1 + 1) * (b.2.2.1 + 1) * D : ℕ) : ℚ)
  | 3 => ((P * ((s3 + 1) * (s3 + 2)) : ℕ) : ℚ) / (((a.2.2.2.1 + 1) * (b.2.2.2.1 + 1) * D : ℕ) : ℚ)
  | 4 => ((P * ((s4 + 1) * (s4 + 2)) : ℕ) : ℚ) / (((a.2.2.2.2 + 1) * (b.2.2.2.2 + 1) * D : ℕ) : ℚ)

/-- The reflective evaluator for `J⁽ᵐ⁾`, mirroring `Jcal`'s `List.map`/`List.sum`
double-sum skeleton over the packed representation. -/
def evalJcal (m : Fin 5) (F : CPoly) : ℚ :=
  (F.map (fun p => (F.map (fun q => p.2 * q.2 * cJD p.1 q.1 m)).sum)).sum

/-- **Bridge, per-pair.** The packed kernel `cJD` equals C1's `JD` on the unpacked
exponents. Proved once by the same factorial/cast algebra as `contract_term`. -/
theorem cJD_eq (a b : Exp5) (m : Fin 5) : cJD a b m = JD (toE a) (toE b) m := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := a
  obtain ⟨b0, b1, b2, b3, b4⟩ := b
  fin_cases m <;>
  · rw [JD_eq]
    simp only [cJD, toE, Fin.prod_univ_five, Fin.sum_univ_five,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons]
    push_cast
    field_simp

/-- **The soundness bridge** (proved once, `F`-generically): the reflective
evaluator agrees with C1's `Jcal` on the lifted polynomial. This is the
verified-evaluator pattern — slow-but-once here, fast-forever at each instance. -/
theorem evalJcal_eq (m : Fin 5) (F : CPoly) : evalJcal m F = Jcal m (toPoly F) := by
  unfold evalJcal Jcal toPoly
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  simp only [Function.comp_def, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  rw [cJD_eq]


/-! ## The certified optimum, packed, and the reflective re-verification -/

/-- `F★` (C1's `Fstar`) in the packed representation. `toPoly FstarC = Fstar`
holds by `rfl` (each `Exp5` tuple lifts back to the matching `![…]` literal). -/
def FstarC : CPoly := [
  ((0,0,0,0,0), 7),
  ((0,0,0,0,1), -19),
  ((0,0,0,1,0), -19),
  ((0,0,1,0,0), -19),
  ((0,1,0,0,0), -19),
  ((1,0,0,0,0), -19),
  ((0,0,0,0,2), 28),
  ((0,0,0,2,0), 28),
  ((0,0,2,0,0), 28),
  ((0,2,0,0,0), 28),
  ((2,0,0,0,0), 28),
  ((0,0,0,1,1), 30),
  ((0,0,1,0,1), 30),
  ((0,0,1,1,0), 30),
  ((0,1,0,0,1), 30),
  ((0,1,0,1,0), 30),
  ((0,1,1,0,0), 30),
  ((1,0,0,0,1), 30),
  ((1,0,0,1,0), 30),
  ((1,0,1,0,0), 30),
  ((1,1,0,0,0), 30),
  ((0,0,0,0,3), -15),
  ((0,0,0,3,0), -15),
  ((0,0,3,0,0), -15),
  ((0,3,0,0,0), -15),
  ((3,0,0,0,0), -15),
  ((0,0,0,1,2), -21),
  ((0,0,0,2,1), -21),
  ((0,0,1,0,2), -21),
  ((0,0,1,2,0), -21),
  ((0,0,2,0,1), -21),
  ((0,0,2,1,0), -21),
  ((0,1,0,0,2), -21),
  ((0,1,0,2,0), -21),
  ((0,1,2,0,0), -21),
  ((0,2,0,0,1), -21),
  ((0,2,0,1,0), -21),
  ((0,2,1,0,0), -21),
  ((1,0,0,0,2), -21),
  ((1,0,0,2,0), -21),
  ((1,0,2,0,0), -21),
  ((1,2,0,0,0), -21),
  ((2,0,0,0,1), -21),
  ((2,0,0,1,0), -21),
  ((2,0,1,0,0), -21),
  ((2,1,0,0,0), -21),
  ((0,0,1,1,1), -19),
  ((0,1,0,1,1), -19),
  ((0,1,1,0,1), -19),
  ((0,1,1,1,0), -19),
  ((1,0,0,1,1), -19),
  ((1,0,1,0,1), -19),
  ((1,0,1,1,0), -19),
  ((1,1,0,0,1), -19),
  ((1,1,0,1,0), -19),
  ((1,1,1,0,0), -19)
]

/-- Sanity: the packed optimum lifts back to the landed `Fstar`. -/
theorem toPoly_FstarC : toPoly FstarC = Fstar := rfl

set_option maxRecDepth 8000 in
/-- **RAW reflective check** (evaluator vs. literal): the packed evaluator hits the
certified value by pure kernel reduction. ≈ 25.8k heartbeats / ≈ 5 s kernel,
vs. the landed 1.09M-heartbeat `norm_num` grind. -/
theorem evalJcal_FstarC_0 : evalJcal 0 FstarC = 191881 / 119750400 := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- **FULL reflective re-verification of `J_Fstar_0`** — the exact landed C1
statement `Jcal 0 Fstar = 191881/119750400`, discharged by the bridge plus one
kernel reduction (no `simp`, no `norm_num`). ≈ 477 heartbeats. -/
theorem J_Fstar_0_reflective : Jcal 0 Fstar = 191881 / 119750400 := by
  rw [← toPoly_FstarC, ← evalJcal_eq]
  decide +kernel

end Salt.CertEval

/-! ## Axiom audit (T5): the reflective route is kernel-pure. -/
open Salt.Tactic in
#audit_axioms
  Salt.CertEval.cJD_eq Salt.CertEval.evalJcal_eq
  Salt.CertEval.evalJcal_FstarC_0 Salt.CertEval.J_Fstar_0_reflective
