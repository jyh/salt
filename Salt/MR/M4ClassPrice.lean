/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Join

/-!
# ⟦PART C⟧ — THE CLASS PRICING (`M4ClassPrice`)

The M4 wave closed at a six-item register whose last open item is `M4Join.M4RowMeanSq`
(`M4Join`, ⟦THE RESIDUE⟧).  Two design questions stood behind it; this file lands the second,
⟦THE CLASS PRICING⟧, in the shape the residue design v2 froze — **at depth 1, with no
induction**.

## ⟦U2 — THE FORCED ORDER⟧ (the pin this file exists to fix)

The route from the door to the capstone is not a free choice of order.  It is

```
   the door's window sum at a tight-major α
     --(B-2, the Abel drift kill)-->        the sub-window sup at the RATIONAL b/q
     --(B-1, the residue split)-->          q class sums at the rational
     --(the rational phase is CONSTANT on a class)-->   q UN-PHASED class sums
     --(B-3, ONE dilation at d₀ = (r,q))--> a coprime class at (q₀, r₀)
     --(M4Close §6, the character expansion)-->  the χ-twisted sum over the SIEVED window
```

Every one of the three middle steps **removes** the phase — the drift kills `e(θm)`, the
split makes `e((b/q)m)` constant on each class, and the dilation is taken at the residual
frequency `d₀·0 = 0`.  So the capstone is instantiated at the **un-phased** `1_𝒮λχ̄` datum,
and `M4RowMeanSq` — which carries `doorCoeffPhase (doorSievedCoeff M) α` — is the wrong
interface to hand the capstone directly.  §7 states the re-cut (`M4RowMeanSqUnphased`) and
pins it to `M4Join`'s phased original by the one identity that relates them
(`doorCoeffPhase c 0 = c`), so THE FINAL COMPOSE has its interface fixed in advance.

## ⟦WHAT IS LANDED⟧

* **§1 — the phase removal.**  At the rational frequency `b/q` the window sum's phase is
  constant on each residue class (`M4BridgeResidue.exp_eq_ratPhase_of_modEq`), so the class
  carriers are the BARE class sums `∑_{m ∈ windowClass} a m`.  Both directions are named
  (`norm_absWindowSum_rat_le_class_sums`, `absWindowSum_classCoeff_rat`).
* **§2 — the sieved class sum meets the character expansion.**  `memSCoeff`'s indicator is a
  `filter`, so a class of the sieved window IS `residueClassOn` of the sieved index set — and
  `M4BridgeResidue.norm_sum_residueClassOn_liou_le_of_uniform` fires on it verbatim, with the
  `1/φ(q)` cancelled exactly against the character count.
* **§3 — `m4_class_price`, THE TWO-CASE CLASS LEMMA.**  `d₀ = (r,q) = 1` → §2 at `(q, r)`;
  `d₀ > 1` → `M4BridgeDilate.m4_class_dilate_exit` (an EQUALITY — zero loss) at the residual
  frequency `0`, then `m4_class_dilate_coprime` and §2 at `(q₀, r₀)`.  **No induction and no
  second split**: the dilated frequency `d₀·(b/q) = b/q₀` is again constant on classes mod
  `q₀`, and the dilated class is already coprime.
* **§4 — the assembly.**  `q` classes × the per-class grade, squared: `q²·B²`.  The `q²`
  lands in the `q`-graded slot of `M4BridgePhase.M4SievedDoorSqSup` — **the same `q` as the
  drift witness**, by construction (`M4BridgePhase` §3: the split's modulus is the arc's own
  witness denominator).  `M4BlockMeanSqSupQ` + `m4_cover_assembly_supQ` are the `q`-graded
  twins of `M4Join`'s pair, and they are what makes the socket's `q`-grading consumable.
* **§5 — the endpoint drop (K3(iii)).**  The dilated block `(⌊A/d⌋, ⌊B/d⌋]` fails the TIGHT
  `doorLadder_fit` by at most `3` units (`dilBlock_fit_slack`; the honest slack is `2`).
  Dropping the top `≤ 3` indices restores the fit and costs `3·H'²/A'` on the harmonic sum —
  negligible, and stated symbolically.
* **§6 — the two grade repairs.**  `m4_gradeGate_direct` (U3): `M4Close.M4GradeGate` from
  `√(Braw H) ≤ mrtDeliveredGrade (C/2) H` DIRECTLY, without routing through
  `Braw ≤ m4Saving` — `m4_gradeGate_of_pricing` throws away the whole `15 − 11/4` exponent
  gap and there is no reason to pay it.  `m4_decay_summand_eq` (U1): the first raw summand
  priced from `T0BandCapFree.cfbM0` DIRECTLY, as an **equality**, retaining the honest
  `(log X)^{1/15 − 7/(30e)}` decay.
* **§7 — the order pin (U2).**  As above.

## ⟦WHY NOT `m4_quality_summand_le`⟧ (U1, stated once)

`M4Close.m4_quality_summand_le` prices `8448·C₁'²·e^{−M₀/e}` by `8448·C₁'²·W^{−5/2}`, and
`M4Close.m4_rawMS_le`'s gate `g1` then asks `8448·C₁'² · W^{−5/2} ≤ m4Saving H/5 =
W^{−5/2}/5`, i.e. `8448·C₁'² ≤ 1/5` — **unsatisfiable** at `C₁' = cfbC₁ X C₁ ≥ 1`.  The
route that works keeps the decay in the `X`-variable instead of cashing it against `W`:
`cfbM0`'s leading `(7/30)·loglog X` turns `e^{−M₀/e}` into `(log X)^{−7/(30e)}`, which beats
`cfbC₁`'s own `(log X)^{1/15}` because `7/(30e) > 1/15` (`m4_decay_exponent_neg`, strict).
Nothing here is asymptotic hand-waving: §6 states the identity, not an estimate.

## ⟦THE TRAPS RESPECTED⟧

* **the four log scales** — this file writes `log H` (through `arcDen 12 H`, never evaluated)
  and `log X` (through `cfbM0`/`cfbC₁`/`seamT0`, §6 only).  The two never meet: §6's
  statements carry no `H`, §§1–5 carry no `X`.
* **the enlarged cap (B-3's rule)** — §3's dilation is taken at the RESIDUAL frequency `0`,
  which is `NearRatTight`-trivial; no arc datum is transported, so the enlarged cap
  `arcDen·(H+d₀)/H` is never incurred.  The general `nearRatTight_dilate` (never the
  door-pinned `nearRatTight_dilate_door`) is the citation if a consumer does need it.
* **`liouvilleC`/`liouChi` only** — never `lam`/`lamChi` (the ⟦lam collision⟧: `lam` is the
  pretentious datum, correct only at primes, and every sum here runs over integers).
* **the two `q`'s identity** — §4's `q` is `NearRatTight`'s witness denominator, the same one
  the drift factor `1 + 2π·arcDen 12 H/q` carries.  It is never re-chosen.
* **strict gates** — `0 < q`, `0 < H`, `R.Hlo ≤ H ≤ R.Hhi`, the door's `d₀ ≤ q ≤ (log H)^{12}
  < P₁` are carried, never weakened.
* **half-open** — every window is `Finset.Ioc n (n+H)`, every block `Finset.Ioc A B`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE PHASE REMOVAL

At the rational frequency `b/q` the window sum's phase is constant on each residue class, so
the class carriers ⟦BRIDGE 1⟧ produces are the BARE class sums `∑_{m ∈ windowClass} a m` —
no `e(·)` survives.  This is the step that makes ⟦U2⟧'s order forced. -/

/-- The window sum at the zero frequency is the plain sum over the window. -/
theorem absWindowSum_zero (a : ℕ → ℂ) (H n : ℕ) :
    absWindowSum a H n 0 = ∑ m ∈ Finset.Ioc n (n + H), a m := by
  unfold absWindowSum
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

/-- ⟦BRIDGE 1⟧'s class carrier at the ZERO residual frequency is the bare class sum. -/
theorem classPhaseSum_zero (a : ℕ → ℂ) (H n q r : ℕ) :
    classPhaseSum a H n q r 0 = ∑ m ∈ windowClass H n q r, a m := by
  unfold classPhaseSum
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

/-- The class-restricted datum's window sum at the zero frequency is the bare class sum. -/
theorem absWindowSum_classCoeff_zero (a : ℕ → ℂ) (H n q r : ℕ) :
    absWindowSum (classCoeff a q r) H n 0 = ∑ m ∈ windowClass H n q r, a m := by
  rw [absWindowSum_zero, windowClass, residueClassOn, Finset.sum_filter]
  rfl

/-- **THE SPLIT AT THE RATIONAL, in bare form.**  `‖∑_{n<m≤n+H} a(m)e((b/q)m)‖ ≤
∑_{r<q} ‖∑_{m ≡ r (q)} a(m)‖`: the `q` rational phases are unimodular constants on their
classes, so the triangle inequality over the classes costs nothing AND leaves no phase.

`M4BridgeResidue.norm_absWindowSum_residue_split_le` at `θ = 0`, with §1's identification. -/
theorem norm_absWindowSum_rat_le_class_sums (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q)
    (b : ℤ) :
    ‖absWindowSum a H n ((b : ℝ) / (q : ℝ))‖
      ≤ ∑ r ∈ Finset.range q, ‖∑ m ∈ windowClass H n q r, a m‖ := by
  have h := norm_absWindowSum_residue_split_le a H n hq b 0
  rw [add_zero] at h
  simpa only [classPhaseSum_zero] using h

/-- **THE CLASS-RESTRICTED WINDOW SUM AT A RATIONAL IS A CONSTANT TIMES THE BARE CLASS SUM.**
The phase `e((b/q)m)` is `ratPhase b q r` for every `m` in the class
(`M4BridgeResidue.exp_eq_ratPhase_of_modEq`), so it factors out of the whole sum. -/
theorem absWindowSum_classCoeff_rat (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q) (b : ℤ)
    (r : ℕ) :
    absWindowSum (classCoeff a q r) H n ((b : ℝ) / (q : ℝ))
      = ratPhase b q r * ∑ m ∈ windowClass H n q r, a m := by
  have h1 : ∑ m ∈ windowClass H n q r, a m
      = ∑ m ∈ Finset.Ioc n (n + H), classCoeff a q r m := by
    rw [windowClass, residueClassOn, Finset.sum_filter]
    rfl
  rw [h1, Finset.mul_sum]
  unfold absWindowSum
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hmod : m ≡ r [MOD q]
  · rw [exp_eq_ratPhase_of_modEq hq b hmod]
    ring
  · simp [classCoeff, hmod]

/-- The norm form: the rational phase is unimodular, so it is invisible. -/
theorem norm_absWindowSum_classCoeff_rat (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q) (b : ℤ)
    (r : ℕ) :
    ‖absWindowSum (classCoeff a q r) H n ((b : ℝ) / (q : ℝ))‖
      = ‖∑ m ∈ windowClass H n q r, a m‖ := by
  rw [absWindowSum_classCoeff_rat a H n hq b r, norm_mul, norm_ratPhase, one_mul]

/-! ## §2 — THE SIEVED CLASS SUM MEETS THE CHARACTER EXPANSION

`M4Sieve.memSCoeff` is an indicator, so a residue class of the SIEVED window is literally
`M4BridgeResidue.residueClassOn` taken on the sieved index set.  The character half of
⟦BRIDGE 1⟧ is stated at a general `S : Finset ℕ`, so it fires there without a single new
estimate — the `1/φ(q)` cancels against the character count exactly
(`M4Close.inv_totient_sum_le`). -/

/-- **THE SIEVED WINDOW** as an index set: `{n < m ≤ n+H : p m}`.  At `p := MemS Pseq Qseq J`
this is the door's own `1_𝒮`-restricted window. -/
def sievedWindow (p : ℕ → Prop) [DecidablePred p] (H n : ℕ) : Finset ℕ :=
  (Finset.Ioc n (n + H)).filter p

theorem mem_sievedWindow {p : ℕ → Prop} [DecidablePred p] {H n m : ℕ} :
    m ∈ sievedWindow p H n ↔ (n < m ∧ m ≤ n + H) ∧ p m := by
  simp [sievedWindow, Finset.mem_Ioc, and_assoc]

/-- **THE TWO FILTERS COMMUTE.**  Summing an indicator-restricted datum over a residue class
of the window is summing the bare datum over the residue class of the SIEVED window.  Pure
`Finset.filter` bookkeeping — no arithmetic. -/
theorem sum_windowClass_indicator (p : ℕ → Prop) [DecidablePred p] (a : ℕ → ℂ)
    (H n q r : ℕ) :
    ∑ m ∈ windowClass H n q r, (if p m then a m else 0)
      = ∑ m ∈ residueClassOn q r (sievedWindow p H n), a m := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [Finset.mem_filter, mem_windowClass, mem_residueClassOn, mem_sievedWindow]
  tauto

/-- The same at the door's own datum (`memSCoeff` is the indicator, by definition). -/
theorem sum_windowClass_memSCoeff (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a : ℕ → ℂ) (H n q r : ℕ) :
    ∑ m ∈ windowClass H n q r, memSCoeff Pseq Qseq J a m
      = ∑ m ∈ residueClassOn q r (sievedWindow (MemS Pseq Qseq J) H n), a m := by
  simpa only [memSCoeff] using
    sum_windowClass_indicator (MemS Pseq Qseq J) a H n q r

/-- **THE COPRIME BRANCH.**  A `χ`-uniform bound on the sieved window's twisted sums prices
each COPRIME class of the sieved window, with no loss at all: the `1/φ(q)` of the character
decomposition cancels against the `φ(q)` characters exactly. -/
theorem norm_sum_windowClass_memS_le_of_uniform {q : ℕ} [NeZero q] {r : ℕ}
    (hcop : Nat.Coprime q r) (Pseq Qseq : ℕ → ℕ) (J H n : ℕ) {B : ℝ}
    (hB : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ sievedWindow (MemS Pseq Qseq J) H n, liouChi χ m‖ ≤ B) :
    ‖∑ m ∈ windowClass H n q r, memSCoeff Pseq Qseq J liouvilleC m‖ ≤ B := by
  rw [sum_windowClass_memSCoeff]
  exact norm_sum_residueClassOn_liou_le_of_uniform hcop _ hB

/-! ## §3 — `m4_class_price`: THE TWO-CASE CLASS LEMMA (depth 1, NO induction)

The v1 design asked for a strong induction on `q` in `VdCSocket.socket_head`'s idiom.  The
refutation collapsed it: **one** dilation already lands a coprime class, because
`M4Residue.coprime_reduced_of_gcd` reduces `(r, q)` to `(r₀, q₀)` with `(r₀, q₀) = 1` in a
single step, and the dilated frequency `d₀·0 = 0` needs no second split.  So the recursion
has depth `1` and is a plain `by_cases`. -/

/-- **THE NON-COPRIME BRANCH — ONE DILATION, AN EQUALITY.**  At the residual frequency `0`,
`M4BridgeDilate.m4_class_dilate_exit` reads as a pure re-indexing of the bare class sum: the
class mod `q` of the window `(n, n+H]` is the class `r₀` mod `q₀` of the DILATED window
`(n/d₀, n/d₀ + dilLen]`, at the same sieved datum, and `‖λ(d₀)‖ = 1` makes the transport
loss-free.  Nothing is estimated here. -/
theorem norm_sum_windowClass_memS_dilate {M J q r H n : ℕ} {Hr : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (h1 : 1 ≤ Real.log Hr) (h2 : Real.log Hr ≤ (2 : ℝ) ^ (21845 : ℕ))
    (hqW : (q : ℝ) ≤ Real.log Hr ^ (12 : ℕ)) :
    ‖∑ m ∈ windowClass H n q r, memSCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) J liouvilleC m‖
      = ‖∑ m ∈ windowClass (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q)
            (q / Nat.gcd r q) (r / Nat.gcd r q),
          memSCoeff (calP (Adoor M) (3072 * M))
            (calQK (Adoor M) (3072 * M) M) J liouvilleC m‖ := by
  set c := memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) J liouvilleC
    with hc
  calc ‖∑ m ∈ windowClass H n q r, c m‖
      = ‖classWindowSum c H n q r 0‖ := by
        rw [classWindowSum_eq_classPhaseSum, classPhaseSum_zero]
    _ = ‖absWindowSum (classCoeff c (q / Nat.gcd r q) (r / Nat.gcd r q))
          (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) 0‖ := by
        have h := (m4_class_dilate_exit (J := J) (q := q) (r := r) (H := H) (n := n)
          (Hr := Hr) hM hq h1 h2 hqW 0).1
        rwa [mul_zero] at h
    _ = ‖∑ m ∈ windowClass (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q)
          (q / Nat.gcd r q) (r / Nat.gcd r q), c m‖ := by
        rw [absWindowSum_classCoeff_zero]

/-- **`m4_class_price` — THE PER-CLASS PRICE, both cases.**

For a class `r` mod `q` of the door's sieved `λ`-window sum at a tight-major rational `b/q`:

* `d₀ = (r,q) = 1` — the character expansion fires at `(q, r)` on the sieved window, and the
  `1/φ(q)` cancels (`hcop`);
* `d₀ > 1` — ONE dilation (an equality, zero loss) lands the class at the provably coprime
  `(q₀, r₀) = (q/d₀, r/d₀)` on the dilated window, where the same expansion fires (`hdil`).

The two hypotheses are the SAME row datum read at the two windows the two branches use; a
supplier uniform over the modulus range and the window range discharges both at once. -/
theorem m4_class_price {M J q r H n : ℕ} {Hr : ℝ} {B : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (h1 : 1 ≤ Real.log Hr) (h2 : Real.log Hr ≤ (2 : ℝ) ^ (21845 : ℕ))
    (hqW : (q : ℝ) ≤ Real.log Hr ^ (12 : ℕ))
    (hcop : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ sievedWindow (MemS (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) J) H n, liouChi χ m‖ ≤ B)
    (hdil : ∀ χ : DirichletCharacter ℂ (q / Nat.gcd r q),
      ‖∑ m ∈ sievedWindow (MemS (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) J)
          (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q), liouChi χ m‖ ≤ B) :
    ‖∑ m ∈ windowClass H n q r, memSCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) J liouvilleC m‖ ≤ B := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  by_cases hcase : Nat.gcd r q = 1
  · -- ⟦d₀ = 1⟧ the class is already coprime: the expansion at `(q, r)`
    haveI : NeZero q := ⟨hq.ne'⟩
    have hcopqr : Nat.Coprime q r := by
      rw [Nat.Coprime, Nat.gcd_comm]
      exact hcase
    exact norm_sum_windowClass_memS_le_of_uniform hcopqr _ _ J H n hcop
  · -- ⟦d₀ > 1⟧ ONE dilation, then the expansion at the reduced (coprime) pair
    rw [norm_sum_windowClass_memS_dilate (J := J) hM hq h1 h2 hqW]
    have hq₀ : 0 < q / Nat.gcd r q :=
      Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)) hd
    haveI : NeZero (q / Nat.gcd r q) := ⟨hq₀.ne'⟩
    have hcop₀ : Nat.Coprime (q / Nat.gcd r q) (r / Nat.gcd r q) :=
      (m4_class_dilate_coprime hq r).symm
    exact norm_sum_windowClass_memS_le_of_uniform hcop₀ _ _ J _ _ hdil

/-! ## §4 — THE ASSEMBLY: `q` CLASSES, AND WHERE THE `q²` LANDS

The split's whole loss is the class count `q`.  Squared, that is the `q²` of
`M4BridgePhase.M4SievedDoorSqSup`'s re-cut right-hand side — and it is THE SAME `q` as the
drift witness's, because `M4BridgePhase.norm_absWindowSum_le_drift_tight` hands out
`NearRatTight`'s own approximant and §1's split is taken at that modulus.  (`M4BridgePhase`
§3's docstring pins this identity; nothing here re-chooses a denominator.) -/

/-- **THE PER-`q` STATEMENT.**  `q` classes at a common per-class grade `B`. -/
theorem norm_absWindowSum_rat_le_class_count (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q)
    (b : ℤ) {B : ℝ} (hB : ∀ r, r < q → ‖∑ m ∈ windowClass H n q r, a m‖ ≤ B) :
    ‖absWindowSum a H n ((b : ℝ) / (q : ℝ))‖ ≤ (q : ℝ) * B := by
  refine le_trans (norm_absWindowSum_rat_le_class_sums a H n hq b) ?_
  calc ∑ r ∈ Finset.range q, ‖∑ m ∈ windowClass H n q r, a m‖
      ≤ ∑ _r ∈ Finset.range q, B :=
        Finset.sum_le_sum fun r hr => hB r (Finset.mem_range.mp hr)
    _ = (q : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The same at the SUB-WINDOW SUP — the carrier `M4BridgePhase`'s socket actually reads.
The per-class grade must be uniform over the sub-window lengths `K ≤ H`, which is exactly the
`K`-uniformity `M4BridgeResidue.norm_sum_residueClassOn_Ioc_liou_le_of_uniform` supplies. -/
theorem subWindowSup_le_class_count (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q) (b : ℤ)
    {B : ℝ} (hB : ∀ K, K ≤ H → ∀ r, r < q → ‖∑ m ∈ windowClass K n q r, a m‖ ≤ B) :
    subWindowSup a H n ((b : ℝ) / (q : ℝ)) ≤ (q : ℝ) * B :=
  subWindowSup_le fun K hK => norm_absWindowSum_rat_le_class_count a K n hq b (hB K hK)

/-- **THE `q²` LANDING.**  Squaring the class count: this is the exact shape of the `q²` slot
in `M4BridgePhase.M4SievedDoorSqSup`'s re-cut conclusion.  No positivity hypothesis on the
per-class grade is needed — `0 ≤ subWindowSup ≤ q·B` supplies it. -/
theorem subWindowSup_sq_le_class_count (a : ℕ → ℂ) (H n : ℕ) {q : ℕ} (hq : 0 < q) (b : ℤ)
    {B : ℝ}
    (hB : ∀ K, K ≤ H → ∀ r, r < q → ‖∑ m ∈ windowClass K n q r, a m‖ ≤ B) :
    (subWindowSup a H n ((b : ℝ) / (q : ℝ))) ^ 2 ≤ (q : ℝ) ^ 2 * B ^ 2 := by
  have hle := subWindowSup_le_class_count a H n hq b hB
  have h0 := subWindowSup_nonneg a H n ((b : ℝ) / (q : ℝ))
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith

/-- **THE `q`-GRADED PER-BLOCK MEAN SQUARE** — `M4Join.M4BlockMeanSqSup` with the class
modulus carried in the grade, matching `M4BridgePhase.M4SievedDoorSqSup`'s re-cut.  This is
the predicate the class price naturally produces: its supplier's loss is `q` classes, and
demoting that before the socket's `1/q` meets it wastes a factor `q²`. -/
def M4BlockMeanSqSupQ (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE `q`-GRADED COVERING SIDE.**  `M4Join.m4_cover_assembly_sup` at the `q`-graded block
predicate: the same `integral_door_cover_le_clean`, the same door-gate bundle, the same
absolute factor `3` — the covering argument never reads what the nonnegative integrand is, so
carrying `q²` through it is free. -/
theorem m4_cover_assembly_supQ {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqSupQ R M k Bblk) :
    M4SievedDoorSqSup R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2)
    (P := Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ)
  simp only [doorSievedCoeff] at hmain
  have heq : 3 * (Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2)
      = 3 * Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  exact hmain

/-- **THE CLASS PRICE, ASSEMBLED INTO THE `q`-GRADED BLOCK PREDICATE.**  With a per-class
grade `B H` valid at every sub-window length, every rational modulus in range and every door
index of the block, the block sum is at most `card × q²·(B H)²`, and the ladder's fit bounds
the block's cardinality by its own bottom `X_{i+1}` (`M4Door.doorLadder_fit`).

The resulting block grade is `(B H)²/H²` — i.e. the per-class grade measured against the
window length, which is exactly the currency `M4Join`'s §4 pricing reads. -/
theorem m4_blockMeanSqSupQ_of_classPrice {R : ChowlaRegime} {M k : ℕ} {B : ℕ → ℝ}
    (hclass : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        ∀ K, K ≤ H → ∀ r, r < q →
          ‖∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖ ≤ B H) :
    M4BlockMeanSqSupQ R M k (fun H => B H ^ 2 / (H : ℝ) ^ 2) := by
  intro H hlo hhi b q hq hqQ i hik
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  -- ⟦pointwise on the block: the class price squared⟧
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (q : ℝ) ^ 2 * B H ^ 2 := fun n hn =>
    subWindowSup_sq_le_class_count (doorSievedCoeff M) H n hq b
      (fun K hK r hr => hclass H hlo hhi q hq hqQ i hik n hn K hK r hr)
  have hcard : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * ((q : ℝ) ^ 2 * B H ^ 2) := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            ((q : ℝ) ^ 2 * B H ^ 2) := Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * ((q : ℝ) ^ 2 * B H ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  have hrhs : B H ^ 2 / (H : ℝ) ^ 2 * (q : ℝ) ^ 2 * (H : ℝ) ^ 2
        * (doorLadder R.x H (i + 1) : ℝ)
      = (doorLadder R.x H (i + 1) : ℝ) * ((q : ℝ) ^ 2 * B H ^ 2) := by
    field_simp
  rw [hrhs]
  refine le_trans hcard ?_
  have hQB : (0 : ℝ) ≤ (q : ℝ) ^ 2 * B H ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right hc hQB

/-! ## §5 — THE ENDPOINT DROP (K3(iii))

The dilated image `(⌊A/d⌋, ⌊B/d⌋]` of a `doorLadder` block `(A, B]` is not a block of any
ladder — the ⟦THE CLASS PRICING⟧ obstruction `M4Join`'s header named.  What it IS, is a free
`(A', B']` block for `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` (whose `A`, `B` and
scale `X` are already free) once its TIGHT fit `B' + H' ≤ 2A'` holds.  The dilated block
misses that fit by at most `3` units, and dropping the top `≤ 3` indices restores it. -/

private lemma slack_arith {a₁ b₁ c₁ : ℕ} (hca : a₁ ≤ c₁) (hkey : b₁ + c₁ ≤ 3 * a₁ + 2) :
    b₁ + (c₁ - a₁) ≤ 2 * a₁ + 3 := by omega

private lemma three_mul_lt {e d : ℕ} (h : e < d) : 3 * e < 3 * d := by omega

private lemma add_le_of_lt_three {u v : ℕ} (h : v < 3) : u + v ≤ u + 2 := by omega

private lemma drop_arith {u v w : ℕ} (h : u + v ≤ 2 * w + 3) (h3 : 3 ≤ u) :
    (u - 3) + v ≤ 2 * w ∧ u ≤ (u - 3) + 3 := by omega

/-- Tripling costs at most `2` to the floor: `⌊3A/d⌋ ≤ 3⌊A/d⌋ + 2`. -/
theorem three_mul_div_le (A : ℕ) {d : ℕ} (hd : 0 < d) : 3 * A / d ≤ 3 * (A / d) + 2 := by
  have hAd : A = d * (A / d) + A % d := (Nat.div_add_mod A d).symm
  have hdec : 3 * A = d * (3 * (A / d)) + 3 * (A % d) :=
    calc 3 * A = 3 * (d * (A / d) + A % d) := by rw [← hAd]
      _ = d * (3 * (A / d)) + 3 * (A % d) := by ring
  have hmod : A % d < d := Nat.mod_lt _ hd
  have hlt : 3 * (A % d) / d < 3 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    exact three_mul_lt hmod
  rw [hdec, Nat.mul_add_div hd]
  exact add_le_of_lt_three hlt

/-- **THE DILATED BLOCK'S FIT SLACK.**  Against the TIGHT `doorLadder_fit` `B + H ≤ 2A`, the
dilated block `(⌊A/d⌋, ⌊B/d⌋]` at the dilated length `dilLen H A d` misses the fit by at most
`3` units:

```
   ⌊B/d⌋ + dilLen H A d  ≤  2⌊A/d⌋ + 3
```

(the honest slack is `2`; `3` is stated because that is what the drop lemma below spends).
Every step is a floor identity: `⌊u/d⌋ + ⌊v/d⌋ ≤ ⌊(u+v)/d⌋` twice, then `three_mul_div_le`. -/
theorem dilBlock_fit_slack {A B H d : ℕ} (hd : 0 < d) (hfit : B + H ≤ 2 * A) :
    B / d + dilLen H A d ≤ 2 * (A / d) + 3 := by
  have hca : A / d ≤ (A + H) / d := Nat.div_le_div_right (Nat.le_add_right A H)
  have hbc : B / d + (A + H) / d ≤ (B + (A + H)) / d := div_add_div_le_add_div B (A + H) hd
  have hle : (B + (A + H)) / d ≤ 3 * A / d := Nat.div_le_div_right (by omega)
  have h3 : 3 * A / d ≤ 3 * (A / d) + 2 := three_mul_div_le A hd
  have hkey : B / d + (A + H) / d ≤ 3 * (A / d) + 2 := le_trans (le_trans hbc hle) h3
  exact slack_arith hca hkey

/-- **THE DILATED BLOCK IS FITTED AFTER THE DROP.**  Discarding the top `3` indices of the
dilated block restores the tight fit exactly, and the discarded range is `≤ 3` wide. -/
theorem dilBlock_fitted {A B H d : ℕ} (hd : 0 < d) (hfit : B + H ≤ 2 * A)
    (h3 : 3 ≤ B / d) :
    (B / d - 3) + dilLen H A d ≤ 2 * (A / d) ∧ B / d ≤ (B / d - 3) + 3 :=
  drop_arith (dilBlock_fit_slack hd hfit) h3

/-- **THE DROP LEMMA.**  Peeling the top `≤ 3` indices off a block costs `3` times the
per-index trivial bound, and nothing else.  Stated at a general summand so that the harmonic
weight, the mean square and the datum are all invisible to it. -/
theorem sum_Ioc_drop_top {v : ℕ → ℝ} {A B B' : ℕ} {Ctriv : ℝ}
    (hAB' : A ≤ B') (hB'B : B' ≤ B) (hdrop : B ≤ B' + 3) (hC0 : 0 ≤ Ctriv)
    (htriv : ∀ n ∈ Finset.Ioc B' B, v n ≤ Ctriv) :
    ∑ n ∈ Finset.Ioc A B, v n ≤ (∑ n ∈ Finset.Ioc A B', v n) + 3 * Ctriv := by
  have hsplit : (∑ n ∈ Finset.Ioc A B', v n) + ∑ n ∈ Finset.Ioc B' B, v n
      = ∑ n ∈ Finset.Ioc A B, v n := Finset.sum_Ioc_consecutive v hAB' hB'B
  have htail : ∑ n ∈ Finset.Ioc B' B, v n ≤ 3 * Ctriv := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ Ctriv htriv) ?_
    rw [Nat.card_Ioc, nsmul_eq_mul]
    have hc : ((B - B' : ℕ) : ℝ) ≤ 3 := by
      have : B - B' ≤ 3 := by omega
      exact_mod_cast this
    nlinarith
  linarith

/-- **THE FITTED-BLOCK COROLLARY.**  `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` at the
free `(A, B')` core, plus the drop's `3` dropped indices priced at `H²/X` each (`‖window
sum‖ ≤ H` and `n > A ≥ X` on the dropped range).

The dropped price `3·H²/X` is negligible at door scales: `X` is the block bottom, which the
ladder keeps `≥ x/(ω·W)`-grade while `H ≤ Hhi ≤ x/ω`, so `H²/X` is a `W`-power below the
block's own `H²·MS` content.  That comparison is a REGIME fact and is carried symbolically
here, exactly as the design specified. -/
theorem sum_Ioc_absWindowSum_sq_div_le_dropped {c : ℕ → ℂ} (hc : ∀ m, ‖c m‖ ≤ 1)
    (s0 : Finset ℕ) (α : ℝ) {H A B B' : ℕ} {X MS : ℝ} (hH : 0 < H)
    (hAB' : A ≤ B') (hB'B : B' ≤ B) (hdrop : B ≤ B' + 3)
    (hX : 0 < X) (hXA : X ≤ (A : ℝ)) (hfit : (B' : ℝ) + (H : ℝ) ≤ 2 * X)
    (hcov : ∀ n ∈ Finset.Ioc A B', ∀ m ∈ Finset.Ioc n (n + H), m ∉ s0 → c m = 0)
    (hMS : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum (doorCoeffPhase c α) s0 x (H : ℝ)‖ ^ 2) ≤ MS) :
    ∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ)
      ≤ (H : ℝ) ^ 2 * MS + 3 * ((H : ℝ) ^ 2 / X) := by
  have hcore := sum_Ioc_absWindowSum_sq_div_le c s0 α hH hAB' hX hXA hfit hcov hMS
  have hC0 : (0 : ℝ) ≤ (H : ℝ) ^ 2 / X := by positivity
  have htriv : ∀ n ∈ Finset.Ioc B' B,
      ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / X := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hAn : (A : ℝ) < (n : ℝ) := by
      have : A < n := by omega
      exact_mod_cast this
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hX (le_trans hXA hAn.le)
    have hw := norm_absWindowSum_le hc H n α
    have hw0 := norm_nonneg (absWindowSum c H n α)
    have hsq : ‖absWindowSum c H n α‖ ^ 2 ≤ (H : ℝ) ^ 2 := by nlinarith
    have hXn : X ≤ (n : ℝ) := le_trans hXA hAn.le
    have hstep1 : ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / (n : ℝ) := by
      gcongr
    have hstep2 : (H : ℝ) ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / X := by
      gcongr
    linarith
  have hdroplem := sum_Ioc_drop_top (v := fun n => ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ))
    hAB' hB'B hdrop hC0 htriv
  linarith

/-! ### §5b — THE SLACK-`4` SIBLING (⟦R2⟧'s UNIFORM ENDPOINTS)

§5 above prices the dilated block at the `n`-DEPENDENT length `dilLen H A d`, and its fit
misses by `3`.  ⟦R2⟧ (`M4NonCoprime`) re-indexes the block by the same map `n ↦ ⌊n/d₀⌋` and
therefore must read the window at the UNIFORM dilated length `⌊H/d₀⌋ + 1`, over the block
`(⌊A/d₀⌋ − 1, ⌊B/d₀⌋]` — the image of a half-open block is CLOSED, so the bottom index is hit
and the bottom endpoint drops by one.  Those two uniform endpoints cost one unit each, so
`M4NonCoprime.dilBlock_reindex_fit` states the fit at slack `4` and the drop must peel `4`
indices rather than `3`.

Nothing else moves: the same general summand, the same per-index `H²/X` price (still a REGIME
fact, still carried symbolically), and the same free-`A,B` block lemma
`M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` underneath.  Only the endpoint constant is
`4` in place of `3`. -/

private lemma drop_arith_four {u v w : ℕ} (h : u + v ≤ 2 * w + 4) (h4 : 4 ≤ u) :
    (u - 4) + v ≤ 2 * w ∧ u ≤ (u - 4) + 4 := by omega

/-- **A SLACK-`4` BLOCK IS FITTED AFTER THE DROP** — the slack-`4` sibling of
`dilBlock_fitted`, stated at the slack itself rather than at §5's `dilLen`, because ⟦R2⟧'s
block and window are BOTH uniform.  `M4NonCoprime.dilBlock_reindex_fit` is exactly this
lemma's `hslack`, at `B := ⌊B/d₀⌋`, `L := ⌊H/d₀⌋ + 1`, `A := ⌊A/d₀⌋ − 1`: discarding the top
`4` indices restores the TIGHT fit `B' + L ≤ 2A`, and the discarded range is `≤ 4` wide. -/
theorem slack4_fitted {B L A : ℕ} (hslack : B + L ≤ 2 * A + 4) (h4 : 4 ≤ B) :
    (B - 4) + L ≤ 2 * A ∧ B ≤ (B - 4) + 4 :=
  drop_arith_four hslack h4

/-- **THE DROP LEMMA AT SLACK `4`** — `sum_Ioc_drop_top` with one more index peeled.  Peeling
the top `≤ 4` indices off a block costs `4` times the per-index trivial bound and nothing
else; the summand is still general, so the harmonic weight, the mean square and the datum are
all invisible to it. -/
theorem sum_Ioc_drop_top_four {v : ℕ → ℝ} {A B B' : ℕ} {Ctriv : ℝ}
    (hAB' : A ≤ B') (hB'B : B' ≤ B) (hdrop : B ≤ B' + 4) (hC0 : 0 ≤ Ctriv)
    (htriv : ∀ n ∈ Finset.Ioc B' B, v n ≤ Ctriv) :
    ∑ n ∈ Finset.Ioc A B, v n ≤ (∑ n ∈ Finset.Ioc A B', v n) + 4 * Ctriv := by
  have hsplit : (∑ n ∈ Finset.Ioc A B', v n) + ∑ n ∈ Finset.Ioc B' B, v n
      = ∑ n ∈ Finset.Ioc A B, v n := Finset.sum_Ioc_consecutive v hAB' hB'B
  have htail : ∑ n ∈ Finset.Ioc B' B, v n ≤ 4 * Ctriv := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ Ctriv htriv) ?_
    rw [Nat.card_Ioc, nsmul_eq_mul]
    have hc : ((B - B' : ℕ) : ℝ) ≤ 4 := by
      have : B - B' ≤ 4 := by omega
      exact_mod_cast this
    nlinarith
  linarith

/-- **THE FITTED-BLOCK COROLLARY AT SLACK `4`** — `sum_Ioc_absWindowSum_sq_div_le_dropped`
with `4` dropped indices.  The core is the SAME free-`(A, B')` block lemma
`M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le`; the `4` dropped indices are priced at
`H²/X` each (`‖window sum‖ ≤ H` and `n > A ≥ X` on the dropped range).

The dropped price `4·H²/X` is negligible at door scales for exactly the reason §5 records —
`X` is the block bottom, kept `≥ x/(ω·W)`-grade while `H ≤ Hhi ≤ x/ω`, so `H²/X` is a
`W`-power below the block's own `H²·MS` content.  That comparison is a REGIME fact and is
carried symbolically here, as the design specified. -/
theorem sum_Ioc_absWindowSum_sq_div_le_dropped_four {c : ℕ → ℂ} (hc : ∀ m, ‖c m‖ ≤ 1)
    (s0 : Finset ℕ) (α : ℝ) {H A B B' : ℕ} {X MS : ℝ} (hH : 0 < H)
    (hAB' : A ≤ B') (hB'B : B' ≤ B) (hdrop : B ≤ B' + 4)
    (hX : 0 < X) (hXA : X ≤ (A : ℝ)) (hfit : (B' : ℝ) + (H : ℝ) ≤ 2 * X)
    (hcov : ∀ n ∈ Finset.Ioc A B', ∀ m ∈ Finset.Ioc n (n + H), m ∉ s0 → c m = 0)
    (hMS : 1 / X * (∫ x in X..(2 * X),
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum (doorCoeffPhase c α) s0 x (H : ℝ)‖ ^ 2) ≤ MS) :
    ∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ)
      ≤ (H : ℝ) ^ 2 * MS + 4 * ((H : ℝ) ^ 2 / X) := by
  have hcore := sum_Ioc_absWindowSum_sq_div_le c s0 α hH hAB' hX hXA hfit hcov hMS
  have hC0 : (0 : ℝ) ≤ (H : ℝ) ^ 2 / X := by positivity
  have htriv : ∀ n ∈ Finset.Ioc B' B,
      ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / X := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hAn : (A : ℝ) < (n : ℝ) := by
      have : A < n := by omega
      exact_mod_cast this
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hX (le_trans hXA hAn.le)
    have hw := norm_absWindowSum_le hc H n α
    have hw0 := norm_nonneg (absWindowSum c H n α)
    have hsq : ‖absWindowSum c H n α‖ ^ 2 ≤ (H : ℝ) ^ 2 := by nlinarith
    have hXn : X ≤ (n : ℝ) := le_trans hXA hAn.le
    have hstep1 : ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / (n : ℝ) := by
      gcongr
    have hstep2 : (H : ℝ) ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / X := by
      gcongr
    linarith
  have hdroplem := sum_Ioc_drop_top_four (v := fun n => ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ))
    hAB' hB'B hdrop hC0 htriv
  linarith

/-- **THE ⟦R2⟧ JOIN.**  The slack-`4` block bound stated in the shape ⟦R2⟧'s interface
`M4NonCoprime.M4CoprimeBlockMeanSq` hands out: a FREE half-open block `(A, B]` with `0 < A`,
the window length free, the fit at `B + H ≤ 2A + 4` — and NOTHING else.  The scale is pinned
at the block bottom (`X := A`), which is where the interface's own right-hand side
`B_cl H · L² · A` reads it, so the mean square is the block's own.

Both endpoint regimes are discharged here, so the caller supplies no drop hypotheses at all:

* `A + 4 ≤ B` — the block is long enough to drop into: `B' := B − 4` restores the TIGHT fit
  (`slack4_fitted` on the interface's slack), and `sum_Ioc_absWindowSum_sq_div_le_dropped_four`
  applies verbatim (the coverage restricts along `Finset.Ioc A B' ⊆ Finset.Ioc A B`);
* `B < A + 4` — the block has `≤ 4` indices, so the drop's own price `4·(H²/A)` already
  covers the WHOLE sum and the mean-square term is spent on nothing.

This is the drop-in the ⟦R2⟧ register item asked for: `M4NonCoprime.dilBlock_reindex_fit`
delivers the hypothesis `hfit` at the re-indexed block, at the uniform dilated length. -/
theorem sum_Ioc_absWindowSum_sq_div_le_slack4 {c : ℕ → ℂ} (hc : ∀ m, ‖c m‖ ≤ 1)
    (s0 : Finset ℕ) (α : ℝ) {H A B : ℕ} {MS : ℝ} (hH : 0 < H) (hA : 0 < A)
    (hfit : B + H ≤ 2 * A + 4)
    (hcov : ∀ n ∈ Finset.Ioc A B, ∀ m ∈ Finset.Ioc n (n + H), m ∉ s0 → c m = 0)
    (hMS : 1 / (A : ℝ) * (∫ x in (A : ℝ)..(2 * (A : ℝ)),
        ‖((1 / (H : ℝ) : ℝ) : ℂ) * shortSum (doorCoeffPhase c α) s0 x (H : ℝ)‖ ^ 2) ≤ MS) :
    ∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ)
      ≤ (H : ℝ) ^ 2 * MS + 4 * ((H : ℝ) ^ 2 / (A : ℝ)) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hMS0 : (0 : ℝ) ≤ MS :=
    le_trans (meanSq_nonneg (doorCoeffPhase c α) s0 (H : ℝ) hA0) hMS
  by_cases hlong : A + 4 ≤ B
  · -- ⟦the long block⟧ drop the top `4` and the interface's slack becomes the TIGHT fit
    obtain ⟨hfitN, hdrop⟩ := slack4_fitted (B := B) (L := H) (A := A) hfit (by omega)
    have hAB' : A ≤ B - 4 := by omega
    have hB'B : B - 4 ≤ B := by omega
    have hfitR : ((B - 4 : ℕ) : ℝ) + (H : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hfitN
    exact sum_Ioc_absWindowSum_sq_div_le_dropped_four hc s0 α hH hAB' hB'B hdrop hA0 le_rfl
      hfitR (fun n hn => hcov n (Finset.Ioc_subset_Ioc_right hB'B hn)) hMS
  · -- ⟦the short block⟧ `≤ 4` indices, each already priced at `H²/A`
    have hcard : ((Finset.Ioc A B).card : ℝ) ≤ 4 := by
      rw [Nat.card_Ioc]
      have hn : B - A ≤ 4 := by omega
      exact_mod_cast hn
    have htriv : ∀ n ∈ Finset.Ioc A B,
        ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / (A : ℝ) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hAn : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.le
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hA0 hAn
      have hw := norm_absWindowSum_le hc H n α
      have hw0 := norm_nonneg (absWindowSum c H n α)
      have hsq : ‖absWindowSum c H n α‖ ^ 2 ≤ (H : ℝ) ^ 2 := by nlinarith
      have hstep1 : ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / (n : ℝ) := by
        gcongr
      have hstep2 : (H : ℝ) ^ 2 / (n : ℝ) ≤ (H : ℝ) ^ 2 / (A : ℝ) := by
        gcongr
      linarith
    have hsum : ∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ)
        ≤ ((Finset.Ioc A B).card : ℝ) * ((H : ℝ) ^ 2 / (A : ℝ)) := by
      calc ∑ n ∈ Finset.Ioc A B, ‖absWindowSum c H n α‖ ^ 2 / (n : ℝ)
          ≤ ∑ _n ∈ Finset.Ioc A B, (H : ℝ) ^ 2 / (A : ℝ) := Finset.sum_le_sum htriv
        _ = ((Finset.Ioc A B).card : ℝ) * ((H : ℝ) ^ 2 / (A : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hHA : (0 : ℝ) ≤ (H : ℝ) ^ 2 / (A : ℝ) := by positivity
    have hMSterm : (0 : ℝ) ≤ (H : ℝ) ^ 2 * MS := by positivity
    nlinarith

/-! ## §6 — THE TWO GRADE REPAIRS (U3 and U1)

Both are about NOT spending a budget one does not have to spend. -/

/-- **⟦U3⟧ `m4_gradeGate_direct` — the grade gate, discharged DIRECTLY.**

`M4Close.m4_gradeGate_of_pricing` routes through `Braw H ≤ m4Saving H` and then spends
`M4Close.sqrt_m4Saving_le_delivered`, i.e. the ENTIRE `15 − 11/4` exponent gap, to get back
to `mrtDeliveredGrade (C/2) H`.  A supplier that already knows `√(Braw H)` is under the
delivered grade should not pay that: this sibling asks for exactly the half-budget statement
`M4GradeGate`'s own conclusion needs.

`M4Close.M4GradeGate` is untouched — this is a new discharge route for the SAME Prop socket,
so no statement anywhere is edited.  Note that `2 ≤ C` is not needed either: the halving is
`mrtDeliveredGrade`'s linearity in `C` and nothing else. -/
theorem m4_gradeGate_direct {R : ChowlaRegime} {C δ : ℝ} {Braw : ℕ → ℝ} {k : ℕ}
    (hdel : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H)
    (hrest : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) :
    M4GradeGate R C δ Braw k := by
  intro H hlo hhi
  have hhalf : mrtDeliveredGrade (C / 2) H + mrtDeliveredGrade (C / 2) H
      = mrtDeliveredGrade C H := by
    unfold mrtDeliveredGrade
    ring
  have h1 := hdel H hlo hhi
  have h2 := hrest H hlo hhi
  linarith

/-- The same from the SQUARED form, which is how a mean-square supplier states it: the door's
delivered grade is nonnegative past the regime floor (`e ≤ log H` gives `loglog H ≥ 1`), so
`√` is monotone onto it. -/
theorem m4_gradeGate_direct_of_sq {R : ChowlaRegime} {C δ : ℝ} {Braw : ℕ → ℝ} {k : ℕ}
    (hC : 0 ≤ C)
    (hdel : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Braw H ≤ mrtDeliveredGrade (C / 2) H ^ 2)
    (hrest : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) :
    M4GradeGate R C δ Braw k := by
  refine m4_gradeGate_direct (fun H hlo hhi => ?_) hrest
  have hLexp : Real.exp 1 ≤ Real.log (H : ℝ) := exp_one_le_log_of_regime_le R hlo
  have he : (1 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hL1 : (1 : ℝ) ≤ Real.log (H : ℝ) := le_trans he.le hLexp
  have hll : (1 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLexp
    rwa [Real.log_exp] at h
  have hrp : (0 : ℝ) < Real.log (H : ℝ) ^ (-(11 / 4 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hG0 : (0 : ℝ) ≤ mrtDeliveredGrade (C / 2) H := by
    unfold mrtDeliveredGrade
    have : (0 : ℝ) ≤ C / 2 := by linarith
    positivity
  calc Real.sqrt (Braw H) ≤ Real.sqrt (mrtDeliveredGrade (C / 2) H ^ 2) :=
        Real.sqrt_le_sqrt (hdel H hlo hhi)
    _ = mrtDeliveredGrade (C / 2) H := Real.sqrt_sq hG0

/-- **⟦U1⟧ THE STRICT NEGATIVITY** `1/15 − 7/(30e) < 0`.  Equivalent to `2e < 7`, and
`e < 2.7182818286` (`Real.exp_one_lt_d9`) settles it with room.  This is the ONE arithmetic
fact that makes the decay-retaining pricing route work at all: `cfbM0`'s leading
`(7/30)·loglog X` outruns `cfbC₁`'s own `(log X)^{1/15}`. -/
theorem m4_decay_exponent_neg : (1 : ℝ) / 15 - 7 / (30 * Real.exp 1) < 0 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h30 : (0 : ℝ) < 30 * Real.exp 1 := by linarith
  have hlt : (1 : ℝ) / 15 < 7 / (30 * Real.exp 1) := by
    rw [lt_div_iff₀ h30]
    linarith
  linarith

/-- **⟦U1⟧ THE DECAY-RETAINING GRADE.**  The first raw summand of
`M4MeanSq.m4_meansq_per_chi_gen` (`M4Close.m4RawMS`'s first term), read at `C₁' := cfbC₁ X C₁`
and `M₀ := cfbM0 K q X`, is EXACTLY

```
  8448·(C₁+1)²·exp((1/e)·D) · (log X)^{1/15 − 7/(30e)},
  D := (23/16)·logloglog X + (3/4)·log q + (1/4)·q + K
```

— the `X`-decay retained in the exponent, the debits of `cfbM0` displayed in one factor, and
nothing estimated. -/
def m4DecayGrade (K : ℝ) (q : ℕ) (X C₁ : ℝ) : ℝ :=
  8448 * (C₁ + 1) ^ 2
    * Real.exp ((1 / Real.exp 1)
        * (23 / 16 * Real.log (Real.log (Real.log X)) + 3 / 4 * Real.log (q : ℝ)
            + 1 / 4 * (q : ℝ) + K))
    * Real.log X ^ ((1 : ℝ) / 15 - 7 / (30 * Real.exp 1))

/-- **⟦U1⟧ THE PRICING, AS AN EQUALITY.**  `8448·(cfbC₁ X C₁)²·e^{−cfbM0 K q X/e}` IS
`m4DecayGrade K q X C₁`.  Route: `cfbC₁_sq` (`cfbC₁² = (C₁+1)²·seamT0 X`), `seamT0 X =
(log X)^{1/15}`, and `Real.rpow_def_of_pos` turning both `rpow`s into `exp`s — after which the
whole content is the linear identity `L/15 − cfbM0/e = D/e + L(1/15 − 7/(30e))` at
`L := loglog X`, which is `cfbM0`'s definition read backwards.

⚠ NEVER route this summand through `M4Close.m4_quality_summand_le`: its gate `g1` demands
`8448·C₁'² ≤ 1/5`, which is unsatisfiable at `C₁' = cfbC₁ X C₁ ≥ 1` (module header). -/
theorem m4_decay_summand_eq {X C₁ K : ℝ} {q : ℕ} (hX : 0 < Real.log X) :
    8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * cfbM0 K q X)
      = m4DecayGrade K q X C₁ := by
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hsq := cfbC₁_sq (X := X) (C₁ := C₁) hX.le
  have hT : seamT0 X = Real.exp (Real.log (Real.log X) * (1 / 15)) := by
    rw [seamT0, Real.rpow_def_of_pos hX]
  have hG : Real.log X ^ ((1 : ℝ) / 15 - 7 / (30 * Real.exp 1))
      = Real.exp (Real.log (Real.log X) * ((1 : ℝ) / 15 - 7 / (30 * Real.exp 1))) :=
    Real.rpow_def_of_pos hX _
  have hlhs : 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * cfbM0 K q X)
      = 8448 * (C₁ + 1) ^ 2
        * Real.exp (Real.log (Real.log X) * (1 / 15)
            + -(1 / Real.exp 1) * cfbM0 K q X) := by
    rw [Real.exp_add, hsq, hT]
    ring
  have hrhs : m4DecayGrade K q X C₁
      = 8448 * (C₁ + 1) ^ 2
        * Real.exp ((1 / Real.exp 1)
              * (23 / 16 * Real.log (Real.log (Real.log X)) + 3 / 4 * Real.log (q : ℝ)
                  + 1 / 4 * (q : ℝ) + K)
            + Real.log (Real.log X) * ((1 : ℝ) / 15 - 7 / (30 * Real.exp 1))) := by
    rw [m4DecayGrade, Real.exp_add, hG]
    ring
  have harg : Real.log (Real.log X) * (1 / 15) + -(1 / Real.exp 1) * cfbM0 K q X
      = (1 / Real.exp 1)
            * (23 / 16 * Real.log (Real.log (Real.log X)) + 3 / 4 * Real.log (q : ℝ)
                + 1 / 4 * (q : ℝ) + K)
          + Real.log (Real.log X) * ((1 : ℝ) / 15 - 7 / (30 * Real.exp 1)) := by
    unfold cfbM0
    field_simp
    ring
  rw [hlhs, hrhs, harg]

/-- The grade's `X`-factor genuinely decays: the exponent is strictly negative, so past
`log X ≥ 1` the factor is `≤ 1` and falls.  (Stated in the weakest useful form; the strict
monotonicity is `Real.rpow_natCast`-free and never needed downstream.) -/
theorem m4DecayGrade_factor_le_one {X : ℝ} (hX : 1 ≤ Real.log X) :
    Real.log X ^ ((1 : ℝ) / 15 - 7 / (30 * Real.exp 1)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hX (le_of_lt m4_decay_exponent_neg)

/-! ## §7 — ⟦U2⟧ THE ORDER PIN: the re-cut `M4RowMeanSq`

Part C is a RE-CUT of `M4Join.M4RowMeanSq` between the door and the capstone.  The drift, the
split and the character expansion REMOVE the phase (§1), so the capstone is instantiated at
the **un-phased** sieved datum.  This section states the re-cut's target shape and pins it to
`M4Join`'s phased original, so THE FINAL COMPOSE has no interface left to choose. -/

/-- **THE RE-CUT ROW INPUT** (`M4RowMeanSqUnphased`) — `M4Join.M4RowMeanSq` with the phase
gone: the same block, the same `thm_a2'` currency, the same seam index set, the same window
length, and the door's sieved datum carried BARE.

The `α`-quantifier and its `NearRatTight` premise are gone with the phase: after §1 there is
no frequency left in the integrand to quantify over. -/
def M4RowMeanSqUnphased (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ i < k,
    1 / (doorLadder R.x H (i + 1) : ℝ)
        * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
            ‖((1 / (H : ℝ) : ℝ) : ℂ)
                * shortSum (doorSievedCoeff M)
                    (seamS0 (2 * doorLadder R.x H (i + 1))
                      (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H

/-- **THE PHASE IS THE ONLY DIFFERENCE.**  `doorCoeffPhase c 0 = c` — the door's phased
coefficient at the removed frequency IS the bare datum. -/
theorem doorCoeffPhase_zero (c : ℕ → ℂ) : doorCoeffPhase c 0 = c := by
  funext m
  simp [doorCoeffPhase]

/-- **THE ORDER PIN, stated.**  `M4RowMeanSqUnphased` is byte-exactly `M4Join.M4RowMeanSq`'s
body at the REMOVED phase `α = 0` (and with the `α`-quantifier dropped).  So the final compose
has exactly one obligation at the interface — supply the un-phased row — and no re-cut of the
integrand to negotiate. -/
theorem m4_rowMeanSqUnphased_eq_phased_zero (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) :
    M4RowMeanSqUnphased R M k MS
      = ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ i < k,
          1 / (doorLadder R.x H (i + 1) : ℝ)
              * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
                  ‖((1 / (H : ℝ) : ℝ) : ℂ)
                      * shortSum (doorCoeffPhase (doorSievedCoeff M) 0)
                          (seamS0 (2 * doorLadder R.x H (i + 1))
                            (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
            ≤ MS H := by
  rw [doorCoeffPhase_zero]
  rfl

/-- **THE COMPOSE'S SHAPE, pinned once.**  The final compose is:

1. the un-phased row (`M4RowMeanSqUnphased`) supplies the χ-uniform sieved-window bounds;
2. `m4_class_price` (§3) prices every class at both branch windows;
3. `m4_blockMeanSqSupQ_of_classPrice` (§4) assembles them into `M4BlockMeanSqSupQ`;
4. `m4_cover_assembly_supQ` (§4) covers, at the absolute factor `3`;
5. `M4BridgePhase.m4_sievedDoorSq_of_sup` (the `q`-graded socket) discharges
   `M4Close.M4SievedDoorSq`, with the split's `q²` meeting the drift's `1/q²` exactly;
6. `m4_gradeGate_direct` (§6) supplies the budget line without spending the exponent gap.

Steps 3–5 are landed here as one statement, so only step 1's supply and step 2's two-window
instantiation remain for the compose. -/
theorem m4_sievedDoorSq_of_classPrice {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {B : ℕ → ℝ} {Braw : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ)
    (hgrade : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
          * ((q : ℝ) ^ 2 * (3 * (B H ^ 2 / (H : ℝ) ^ 2))) ≤ Braw H)
    (hclass : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        ∀ K, K ≤ H → ∀ r, r < q →
          ‖∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖ ≤ B H) :
    M4SievedDoorSq R M Braw :=
  m4_sievedDoorSq_of_sup hgrade
    (m4_cover_assembly_supQ hgates (fun H => by positivity)
      (m4_blockMeanSqSupQ_of_classPrice hclass))

end Salt.MR

end
