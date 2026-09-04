/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F4a — THE `hreduce_aff` DISCHARGE (the R-block)

The main-term extraction (Tao arXiv:1509.05422 Prop 2.6's reduction, spine node HREDUCE) at the
affine forms: the twins of `HBudget.hbudget_holds_h` (`HBudget.lean:1182`) and
`HMainAssembly.hreduce_holds_h` (`HMainAssembly.lean:165`) at the affine F-function
`fBridgeF_aff eps H a b h` (`StrideBridge.lean:96`) under the stride measure `logMeasureAff a x
ω`, discharging the hypothesis `hreduce` of `fBridge_of_singleCorr_aff` (F2-C1,
`StrideBridge.lean:588-601`):

    (1/2)·SP·(H/a)·|X_aff| ≤ |∫ F_aff dμ_aff|,   X_aff = ∫ λ(m+b)λ(m+b+h) dμ_aff.

THE DESIGN (price brief `2026-09-04-math-PRICE-lbv-w2S-F4-entropy-half.md` §3, R-block; F2
freeze §4.7).  The `h`-lane's budget `|∫F_h − Σ_p (H/p)·X_h| ≤ (1/4)·SP·H·ε` is three slices
`1/8 + 1/16 + 1/16` (dilation+swap paid by `hωbig`, shift paid by `hxbig`, boundary paid by the
gate `ε·h ≤ c/(32·log 4)`), assembled from `IF_unfold_h` + `per_term_h` + `boundary_card_le`.
At the affine forms: (i) THE GATE `((a·n + j + 1 : ℕ) : ZMod p) = 0` has a class representative
`rⱼ < p` because `gcd(a, p) = 1` (`gate_residue_aff`; the landed `gate_residue`,
`HBudget.lean:188`, is at `a = 1`); (ii) the collapse `λ(a(pm+rⱼ)+j+1)·λ(…+ph+1) =
λ(am+k)·λ(am+k+h)` with `p·k = a·rⱼ + j + 1` is F2's `liouville_collapse_aff`
(`StrideBridge.lean:522`), and the class filter `j + 1 ≡ p·b (a)` makes `k ≡ b (mod a)`, so the
collapsed base point is the SEED's `a·m' + b` by `affCollapse_base_point` (`StrideBridge.lean:567`,
needs `b < a` — F2's kill A2); (iii) the shift from the base point `b` to `k = a·(k/a) + b` is a
shift by `k/a` in `n`: `integral_shift_le` (`ShiftCorr.lean:235`, generic `f`, generic `s`) at
`s := k/a` replaces the stride-1-hard-wired `corr_shift_le` — no induction; (iv) the swap defect
`dilated_window_stability` (`DilationStability.lean:178`, generic `g`) and the dilation defect
`perPair_collapse_aff` (`StrideBridge.lean:540`) are reused verbatim; (v) THE MAIN TERM is pinned
to the literal `(H : ℝ)/(a : ℝ)` by the consumer (`StrideBridge.lean:591`), while the class
`J(p) = {j < H : j + 1 ≡ p·b (a)}` has `H/a ≤ #J(p) ≤ H/a + 1` (`card_class_range_ge`, NEW;
`card_class_range_le` from `card_filter_natCast_eq_le`, `FBridge.lean:125`) — the `±1` per prime
costs `Σ_p (1/p)·|X_aff| ≤ SP` and is a FOURTH slice; (vi) the boundary count is the COARSE
`boundary_card_le H (p·h) ≤ p·h` (`HBudget.lean:428`, through `Finset.card_le_card`), paying
`(1/32)·SP·(H/a)·ε` from THE GATE AT `ε·a·h ≤ c/(64·log 4)` (F1-B6 as forecast; under the pin
`ε = 1/(500·a·h)` it reads `1/500 ≤ 0.25/88.7`, the `h`-head's own margin).  THE FIVE SLICES:
`1/8 + 1/16 + 1/32 + 1/64 + 1/64 = 1/4` — dilation+swap · shift · boundary · the `±1` count
(`64·a ≤ ε·H`, a stated binder the head pays from `hcoprime : a ≤ ε²·Hlo/2` at `ε ≤ 1/32`) · the
`+1` leftovers of the first two slices (`12·a ≤ H`, implied by the same binder).  The
`hreduce_holds_h` arithmetic is index-blind (`HMainAssembly.lean:151-154`) and twins by
`H ↦ H/a`.  `HBudget`'s `private` substrate (`window_Z_pos :94`, `window_sum_inv_sq :162`,
`boundary_card_le :428`) is re-proved here (`HBudget.lean:876-883`'s own precedent).

⛔ Degenerate values.  `a = 0`: `1 ≤ a` is carried wherever `H/a` or `k/a` is read; `b < a`
forces `1 ≤ a` in every statement carrying `hblt`.  `a = 1, b = 0`: the filter is `True`, the
measure is `logMeasure`, `H/1 = H`, and every statement is the `h`-lane's (the compat
`hreduce_holds_aff_one_zero`).  `h = 0`: `0 < h` is carried by the boundary slice as at `h`.
`H < a`: `H/a = 0`, `card_class_range_ge` is `0 ≤ _`, vacuous.

HONEST LABEL.  Nothing here produces a door or bears on twin primes.  Every declaration below is
statement-only at the freeze (sorry-bodied, recipe in the docstring), built as a module through
`../saltbuild.sh`; NO executor fires before the helm's refuter verdict.  ⛔ MERGE FENCE (iron
rule 2): `math/lbv-w2s-f4a` never reaches `main` until every obligation in the four F4a files
lands sorry-free.
-/
import Salt.Entropy.Chowla.StrideDecrement
import Salt.Entropy.Chowla.StrideBridge
import Salt.Entropy.Chowla.HMainAssembly
import Salt.Entropy.Chowla.HBudget
import Salt.Entropy.Chowla.HeadPinLeaves
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## F4-R0 — `HBudget`'s private substrate, re-proved -/

/-- **F4-R0a (class A).**  `HBudget.window_Z_pos` (`:94`, private): `Finset.sum_pos` over the
nonempty window (`window_nonempty`), each `1/n > 0`. -/
theorem strideWindow_Z_pos {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
  sorry

/-- **F4-R0b (class A).**  `HBudget.window_sum_inv_sq` (`:162`, private): `Σ 1/p² ≤ (2/(ε²H))·SP`
from `window_lb` (`ε²H/2 < p`). -/
theorem strideWindow_sum_inv_sq (eps : ℚ) (H : ℕ) :
    ∑ p ∈ primeWindow eps H, (1 / (p : ℝ) ^ 2)
      ≤ (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
  sorry

/-- **F4-R0c (class A).**  `HBudget.boundary_card_le` (`:428`, private): `⊆ Finset.Ico (H − q) H`,
`Nat.card_Ico`, `omega`. -/
theorem strideBoundary_card_le (H q : ℕ) :
    ((Finset.range H).filter (fun j => H ≤ j + q)).card ≤ q := by
  sorry

/-! ## F4-R1 — the gate's class representative at stride `a`, and the class counts -/

/-- **F4-R1a (class C — new arithmetic) — THE GATE HAS A CLASS REPRESENTATIVE.**  For a prime
`p ≥ 2` coprime to `a`, the gate `((a·n + j + 1 : ℕ) : ZMod p) = 0` selects exactly one residue
class `n % p = r`, with `p ∣ a·r + j + 1`.  Recipe: `haveI : NeZero p`; let `u := (a : ZMod p)`,
a unit (`ZMod.isUnit_iff_coprime`, `hcop`); set `c := -(u⁻¹ * ((j + 1 : ℕ) : ZMod p))` and
`r := c.val`; `p ∣ a·r + j + 1` by `ZMod.natCast_eq_zero_iff` after `push_cast` and
`u * u⁻¹ = 1`; the iff by `ZMod.natCast_eq_natCast_iff'`-shape on `n % p` and the unit's
cancellation (`mul_left_cancel₀`).  The landed `gate_residue` (`HBudget.lean:188`) is the
`a = 1` case (`u = 1`); executor note (v1.1, verdict A8(iv)): at `a = 1` the term `1 * r` is
STUCK, not `rfl` — `one_mul` + `Nat.coprime_one_left`. -/
theorem gate_residue_aff (a p j : ℕ) (hp : 2 ≤ p) (hcop : Nat.Coprime a p) :
    ∃ r : ℕ, r < p ∧ p ∣ (a * r + j + 1) ∧
      ∀ n : ℕ, ((a * n + j + 1 : ℕ) : ZMod p) = 0 ↔ n % p = r := by
  sorry

/-- **F4-R1b (class A) — the class count, above.**  `#{j < H : ((j + 1 : ℕ) : ZMod a) = c} ≤ H/a + 1`:
`card_filter_natCast_eq_le` (`FBridge.lean:125`, modulus-generic) after the `j + 1 ↦ j` reindex of
the predicate (`StrideBridge.lean:163-170`'s `hset` trick at `c − 1`), or directly by the injection
`j ↦ (j + 1) / a` into `Finset.range (H / a + 2)`… — stated at `H/a + 1`, which the injection
`j ↦ j / a` into `range (H/a + 1)` gives after `Nat.div_le_div_right`. -/
theorem card_class_range_le (H a : ℕ) (c : ZMod a) :
    ((Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = c)).card ≤ H / a + 1 := by
  sorry

/-- **F4-R1c (class C — new counting) — the class count, below.**  `H/a ≤ #{j < H : ((j + 1 : ℕ)
: ZMod a) = c}` for `1 ≤ a`: the `H/a` naturals `i < H/a` give the distinct indices
`j_i := a·i + ((c.val + a - 1) % a)` (so `j_i + 1 ≡ c.val ≡ c (mod a)`, `j_i < a·(H/a) ≤ H`),
an injection `Finset.range (H / a) → filter` (`Finset.card_le_card_of_injOn`; `Nat.div_mul_le_self`,
`ZMod.natCast_self_eq_zero`, `Nat.add_mul_mod_self_left`).  At `H < a` it is `0 ≤ _`. -/
theorem card_class_range_ge (H a : ℕ) (ha : 1 ≤ a) (c : ZMod a) :
    H / a ≤ ((Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = c)).card := by
  sorry

/-- **F4-R1d (class B) — the boundary count in the class, COARSE.**  The class's boundary indices
are among all boundary indices: `Finset.card_le_card (Finset.filter_subset_filter …)`-shape, then
`strideBoundary_card_le H q`.  Stated at a general `q` (used at `q := p * h`). -/
theorem card_class_boundary_le (H a q : ℕ) (c : ZMod a) :
    ((Finset.range H).filter
        (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = c ∧ H ≤ j + q)).card ≤ q := by
  sorry

/-! ## F4-R2 — the shifted correlation at the stride measure -/

/-- **F4-R2a (def).**  The gap-`h` correlation at base point `k` under the stride measure:
`S^aff_h(k) = ∫ λ(m+k)·λ(m+k+h) dμ_aff`.  At `k = b` it is `X_aff` DEFINITIONALLY (the seed's
integrand, `StrideFork.lean:176`); by `integral_logMeasureAff` it is `∫ λ(a·n+k)·λ(a·n+k+h) dμ`.
Public (not `private` as `HBudget.shiftCorrH` is) so that the executor's scratch probes and the
later waves can name it. -/
noncomputable def shiftCorrAff (a x ω k h : ℕ) : ℝ :=
  ∫ m, (ArithmeticFunction.liouville (m + k) : ℝ)
      * (ArithmeticFunction.liouville (m + k + h) : ℝ) ∂(logMeasureAff a x ω)

/-- **F4-R2b (class A, `rfl`).**  At the base point `b` the shifted correlation IS the seed's
integrand: `rfl` (the two are syntactically the same integral). -/
theorem shiftCorrAff_base (a b x ω h : ℕ) :
    shiftCorrAff a x ω b h
      = ∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
          * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω) := by
  sorry

/-- **F4-R2c (class C, cheap) — the shift telescoping at stride `a`, NO induction.**  For
`k ≡ b (mod a)` with `b < a` (so `k = a·(k/a) + b`, `affCollapse_base_point`), the base points
`k` and `b` differ by the shift `k/a` in `n`: `integral_logMeasureAff` on both sides, then
`λ(a·n + k) = λ(a·(n + k/a) + b)` (`Nat.mul_add`, the collapse), so the difference is
`integral_shift_le x ω (k / a) hx hω hωx f hf` (`ShiftCorr.lean:235`) at
`f := fun n => λ(a·n + b)·λ(a·n + b + h)`, `|f| ≤ 1` by `abs_liouville_le_one` twice.  Executor
note (v1.1, verdict A8(iv)): the RHS here is `ring`-equal to `integral_shift_le`'s
(`ShiftCorr.lean:237-239`), not `exact` — close with `le_of_eq_of_le`/`ring_nf`, or `convert`. -/
theorem shiftCorrAff_le (a b x ω : ℕ) (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hblt : b < a) (k h : ℕ) (hk : (k : ZMod a) = (b : ZMod a)) :
    |shiftCorrAff a x ω k h - shiftCorrAff a x ω b h|
      ≤ ((k / a : ℕ) : ℝ)
          * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)) := by
  sorry

/-- **F4-R2d (class A).**  `|X_aff| ≤ 1`: `integral_logMeasureAff`, then the `h`-script of
`absXh_le_one` (`HBudget.lean:844`) verbatim — `integral_logMeasure_eq`, the termwise
`abs_liouville_le_one` bound, `strideWindow_Z_pos`. -/
theorem absXaff_le_one (a b h : ℕ) {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
        * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| ≤ 1 := by
  sorry

/-! ## F4-R3 — the per-pair reduction at stride `a` -/

/-- **F4-R3a (class A) — the collapsed image sum.**  `perPair_collapse_aff` (`StrideBridge.lean:540`)
states the image sum with the UNCOLLAPSED arguments; `liouville_collapse_aff` (`:522`) rewrites each
summand to `λ(a·m + k)·λ(a·m + k + h)` under `Finset.sum_congr` (the gate `p·k = a·rⱼ + j + 1` as
`hk`).  The twin of `perPair_collapse_h` (`HBudget.lean:912`) with `p * k = a * r + j + 1` in
place of `p ∣ r + j + 1`. -/
theorem perPair_collapse_aff_collapsed {x ω : ℕ} (a h p j r k : ℕ) (hp : 1 ≤ p)
    (hr : r ≤ x / ω) (hk : p * k = a * r + j + 1) {Z : ℝ} (hZ : 0 < Z) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
         (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
           * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ) / (n : ℝ)) / Z
       - 1 / (p : ℝ) *
         ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
            (ArithmeticFunction.liouville (a * m + k) : ℝ)
              * (ArithmeticFunction.liouville (a * m + k + h) : ℝ) / (m : ℝ)) / Z)|
      ≤ 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z := by
  sorry

/-- **F4-R3b (class C) — THE PER-PAIR BOUND AT STRIDE `a`.**  The twin of `perPair_bound_h`
(`HBudget.lean:945`) with the SAME right side.  Chain: `perPair_collapse_aff_collapsed` (dilation
defect `2r/p²/Z ≤ 2/(pZ)` since `r < p`); `dilated_window_stability` (`DilationStability.lean:178`)
at `g m := λ(a·m + k)·λ(a·m + k + h)` (swap defect `(2·log p + 6)/Z`, divided by `p`); the base
window sum `÷ Z` is `∫ g dμ = shiftCorrAff a x ω k h` (`integral_logMeasure_eq`,
`integral_logMeasureAff`); `k ≡ b (mod a)` from `p·k = a·r + j + 1 ≡ j + 1 ≡ p·b (mod a)` and
`gcd(p, a) = 1` (`hfilt`, `hcop`; cancel the unit `p`); then `shiftCorrAff_le` with the shift
`k/a ≤ 1 + H/p` (from `hkH : a·r + j + 1 ≤ a·p + H` and `1 ≤ a`: `k ≤ a + H/p`), so the shift
slice is `≤ (1/p)·(1 + H/p)·S ≤ (1/p + H/p²)·S` — the `h`-lane's own shape, weaker than the true
`H/(a·p²)`.  `hsplit : (2·log p + 8)/(pZ) = 2/(pZ) + (2·log p + 6)/(pZ)` as at `h`. -/
theorem perPair_bound_aff {x ω : ℕ} (a b h H : ℕ) (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (ha : 1 ≤ a) (hblt : b < a) (p j r : ℕ) (hp : 2 ≤ p) (hcop : Nat.Coprime a p)
    (hrp : r < p) (hdvd : p ∣ (a * r + j + 1))
    (hfilt : ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a))
    (hrx : r ≤ x / ω) (hB : 1 ≤ x / ω) (hkH : a * r + j + 1 ≤ a * p + H) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
         (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
           * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ) / (n : ℝ))
         / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
       - (1 / (p : ℝ)) * shiftCorrAff a x ω b h|
      ≤ (2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
            * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)) := by
  sorry

/-! ## F4-R4 — the F-bridge integral unfolded, and the per-term bound -/

/-- **F4-R4a (class C) — `IF_unfold_h` (`HBudget.lean:1040`) at the affine forms.**  The pointwise
half is landed (`fBridgeF_aff_liouville_apply`, `StrideBridge.lean:453`: the gate AND the class
filter in one `if`); then `IF_unfold_h`'s own script (`HBudget.lean:1040-1075`) at `m = a·n`:
`integral_logMeasureAff` (unconditional) + `integral_logMeasure_eq` (unconditional) +
`Finset.sum_comm` twice.  ⛔ NOT `integral_finsetSum` via `integrable_of_finiteSupport _`: that
route also demands `[IsFiniteMeasure (logMeasureAff a x ω)]`, which the `FiniteSupport` instance
does not give and which this statement carries no `hx`/`hω` to derive (v1.1, verdict A3).  Add
NO binders to this statement. -/
theorem IF_unfold_aff (a b h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ} :
    (∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
        ∂(logMeasureAff a x ω))
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ m, (if ((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
                  ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (m + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ)
            else 0) ∂(logMeasureAff a x ω) := by
  sorry

/-- **F4-R4b (class C) — THE PER-TERM BOUND AT THE AFFINE FORMS.**  The twin of `per_term_h`
(`HBudget.lean:1077`) with THREE branches: the class filter fails (both sides `0`: `if_neg` on the
gate-conjunction via `hfilt` zeroes the INTEGRAND pointwise, then `MeasureTheory.integral_zero`
closes `∫ 0` — as `per_term_h`, `HBudget.lean:1113-1116`; the RHS `if`s collapse by `if_neg
hfilt`; v1.1, verdict A5); the boundary `H ≤ j + p·h` (the window product is junk-zero, the whole
`(1/p)·X_aff` is lost); the interior (`integral_logMeasureAff`, `gate_residue_aff` for the class
`rⱼ`, `integral_logMeasure_eq`, the class sum, `perPair_bound_aff`, `hkH` from `r < p ≤ H`).
`hxωH : H ≤ x/ω` gives `r ≤ x/ω`; `hcop : Nat.Coprime a p`. -/
theorem per_term_aff (a b h : ℕ) (hh : 0 < h) (ha : 1 ≤ a) (hblt : b < a) (eps : ℚ) (H : ℕ)
    {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hxωH : H ≤ x / ω)
    (p : ℕ) (hp : p ∈ primeWindow eps H) (hcop : Nat.Coprime a p) (j : ℕ) (hj : j < H) :
    |(∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
              ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
        (ArithmeticFunction.liouville (m + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ) else 0) ∂(logMeasureAff a x ω))
      - (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
          (1 / (p : ℝ)) * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
            * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)) else 0)|
      ≤ if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
          ((2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
            + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)))
          + (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ m,
              (ArithmeticFunction.liouville (m + b) : ℝ)
                * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| else 0)
        else 0 := by
  sorry

/-! ## F4-R5 — THE BUDGET at the affine forms (the capstone) -/

/-- **F4-R5 (class C, THE CAPSTONE) — `hbudget_holds_h` (`HBudget.lean:1182`) at the affine
forms.**  The error budget with the main term pinned at the literal `(H/a)/p` per prime (R5's OWN
form: the consumer `StrideBridge.lean:591` carries `H/a` OUTSIDE the sum, and R6a's `hSPH` bridges
the two spellings — v1.1, verdict A8(iii)).  THE FIVE SLICES (module
header): dilation+swap `(H/a + 1)·Σ_p (2·log p + 8)/(pZ) ≤ (1/8)·SP·(H/a)·ε + (1/8)·SP·ε` from
`hωbig` (the `h`-lane's `hT1`, `:1246`, per surviving index; `card_class_range_le`); shift
`(H/a + 1)·Σ_p (1/p + H/p²)·S ≤ (1/16)·SP·(H/a)·ε + (1/16)·SP·ε` from `hxbig` and
`strideWindow_sum_inv_sq` (`hT2`, `:1322`); boundary `Σ_p (p·h)·(1/p)·|X_aff| ≤ |𝒫_H|·h ≤
(1/32)·SP·(H/a)·ε` from THE GATE `ε·a·h ≤ c/(64·log 4)` and `primeWindow_card_le_of_regime`
(`hT3`, `:1341`, with `64` for `32`); the `±1` class count `Σ_p |#J(p) − H/a|·(1/p)·|X_aff| ≤
SP ≤ (1/64)·SP·(H/a)·ε` from `64·a ≤ ε·H` (`card_class_range_ge`/`_le`, `absXaff_le_one`);
the two `+1` leftovers `(3/16)·SP·ε ≤ (1/64)·SP·(H/a)·ε` from `12·a ≤ H` (implied by
`64·a ≤ ε·H`, `ε² ≤ 1`).  Assembly: `IF_unfold_aff`, the main term as
`Σ_p Σ_{j<H} [filter]·(1/p)·X_aff` (`Finset.sum_const`, `Finset.card_filter`), the difference
distributed, `Finset.abs_sum_le_sum_abs` twice, `per_term_aff` termwise, the boundary sum by
`card_class_boundary_le H a (p*h)`, `linarith` on the five slices.  `c`, `1/4 ≤ c` and `H₀` are
`primeWindow_sum_inv_ge_bounded`'s (`HeadPinLeaves.lean:61`, imported for this):
`obtain ⟨c, hc, hcge, H₀, hD3⟩ := primeWindow_sum_inv_ge_bounded; refine ⟨c, hc, hcge, H₀, ?_⟩`
(`HeadPinLeavesH.lean:70-71`) — NEVER the unbounded `primeWindow_sum_inv_ge`
(`WindowMertensLower.lean:56`), whose `1/4` is a witness inside a proof, invisible after `obtain`
(v1.1, verdict A1; §3 S-7: the `cE` carry the head's gate reads). -/
theorem hbudget_holds_aff :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (a b h : ℕ) (eps : ℚ) (H x ω : ℕ),
      0 < h → 1 ≤ a → b < a → Nat.Coprime a (PH eps H) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) * (a : ℝ) * (h : ℝ) ≤ c / (64 * Real.log 4) →
      (64 : ℝ) * (a : ℝ) ≤ (eps : ℝ) * (H : ℝ) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      |(∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω))
          - (∑ p ∈ primeWindow eps H, ((H : ℝ) / (a : ℝ)) / (p : ℝ)
              * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ)) * (eps : ℝ) := by
  sorry

/-! ## F4-R6 — the reduction closes -/

/-- **F4-R6a (class B) — `hreduce_holds_h` (`HMainAssembly.lean:165`) at the affine forms.**
Index-blind arithmetic: `set SP`, `set Xs := X_aff`, `set IF`, `set MAIN := Σ_p ((H/a)/p)·Xs`;
`hSPH : Σ_p ((H/a)/p) = SP·(H/a)` (`Finset.sum_mul`, `one_div_mul_eq_div`); `|MAIN| = SP·(H/a)·|Xs|`;
the reverse triangle `abs_sub_abs_le_abs_sub`; `nlinarith [hmain, hbudget, hprod]` with
`hprod : 0 ≤ (2|Xs| − ε)·(SP·(H/a))` (`0 ≤ (H : ℝ)/(a : ℝ)` by `positivity`, true at `a = 0`). -/
theorem hreduce_holds_aff (a b h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|)
    (hbudget : |(∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
              ∂(logMeasureAff a x ω))
          - (∑ p ∈ primeWindow eps H, ((H : ℝ) / (a : ℝ)) / (p : ℝ)
              * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
            * (eps : ℝ)) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
        * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
            * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
      ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
          ∂(logMeasureAff a x ω)| := by
  sorry

/-- **F4-R6b (class B) — `hreduce_close_h` (`HReduce.lean:167`) at the affine forms** (the
`ETOT` form; `h`-free arithmetic on named reals with `H ↦ H/a`). -/
theorem hreduce_close_aff (a b h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|)
    {ETOT : ℝ}
    (hbudget : ETOT ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        * ((H : ℝ) / (a : ℝ)) * (eps : ℝ))
    (hmain : (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
          * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| - ETOT
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)|) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
        * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
            * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
      ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
          ∂(logMeasureAff a x ω)| := by
  sorry

/-- **F4-R6c (class A) — the consumability probe** (`HReduce.lean:140`'s shape): the frozen
`hreduce` is consumable into `h211_aff`'s `hprop26` slot without re-freeze — one line over
`fBridge_of_singleCorr_aff'` (`StrideBridge.lean:639`), `ha : 0 < a` for its positivity. -/
theorem consumability_probe_aff (a b h : ℕ) (ha : 0 < a) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hlog : 1 ≤ Real.log (H : ℝ)) {cM : ℝ} (hcM : 0 < cM)
    (hmert : cM / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (HRED : (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
          * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)|) :
    ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
                ∂(logMeasureAff a x ω)| := by
  sorry

/-- **F4-R6d (class A) — THE CAPSTONE COMPOSED: `hreduce_holds_final_h` (`HBudget.lean:1514`) at the
affine forms.**  `obtain ⟨c, hc, hcge, H₀, hbud⟩ := hbudget_holds_aff; refine ⟨c, hc, hcge, H₀, ?_⟩` (the
`1/4 ≤ c` carry FORWARDED, as `HeadPinLeavesH.lean:360-361`), then `hreduce_holds_aff` at the
budget.  This is the `hred` the affine head consumes (its `cE`, WITH `1/4 ≤ cE` — v1.1, verdict
A1, §3 S-7). -/
theorem hreduce_holds_final_aff :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (a b h : ℕ) (eps : ℚ) (H x ω : ℕ),
      0 < h → 1 ≤ a → b < a → Nat.Coprime a (PH eps H) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) * (a : ℝ) * (h : ℝ) ≤ c / (64 * Real.log 4) →
      (64 : ℝ) * (a : ℝ) ≤ (eps : ℝ) * (H : ℝ) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
          * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
          * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)| := by
  sorry

/-- **F4-R6e (class B) — the `(1, 0)` compat of the reduction, RESTATED v1.1 (verdict A2(b)) so
that it can fail.**  The hypotheses are `hreduce_holds_aff`'s at `(a, b) = (1, 0)` VERBATIM (the
affine vocabulary: `logMeasureAff 1 x ω`, `liouville (m + 0)`, `fBridgeF_aff eps H 1 0 h`,
`(H : ℝ) / ((1 : ℕ) : ℝ)`); the conclusion is `hreduce_holds_h`'s (`HMainAssembly.lean:165`)
VERBATIM (`logMeasure x ω`, `fBridgeF_h eps H h`, `(H : ℝ)`).  Discharge: `have := hreduce_holds_aff
1 0 h eps H hseed hbudget`, then the bridges ON THE CONCLUSION — `logMeasureAff_one`,
`fBridgeF_aff_one_zero` under the integral binders (`simp only`, not `rw`), `add_zero`,
`Nat.cast_one`, `div_one`.  The v1 form restated `hreduce_holds_h` byte for byte on both sides and
could not fail; here the bridge lemmas are LOAD-BEARING.  (The BUDGET's own `(1, 0)` compat is not
stated: `hbudget_holds_aff` carries two binders the `h`-lane's does not — the gate at `64` and the
count slack — so it does not recover `hbudget_holds_h`'s statement; the reduction's conclusion is
the receipt.) -/
theorem hreduce_holds_aff_one_zero (h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hseed : (eps : ℝ) / 2 ≤ |∫ m, (ArithmeticFunction.liouville (m + 0) : ℝ)
              * (ArithmeticFunction.liouville (m + 0 + h) : ℝ) ∂(logMeasureAff 1 x ω)|)
    (hbudget : |(∫ m, fBridgeF_aff eps H 1 0 h (liouvilleWindow H m) (residueWindow eps H m)
              ∂(logMeasureAff 1 x ω))
          - (∑ p ∈ primeWindow eps H, ((H : ℝ) / ((1 : ℕ) : ℝ)) / (p : ℝ)
              * (∫ m, (ArithmeticFunction.liouville (m + 0) : ℝ)
                  * (ArithmeticFunction.liouville (m + 0 + h) : ℝ) ∂(logMeasureAff 1 x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / ((1 : ℕ) : ℝ))
            * (eps : ℝ)) :
    (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
        * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)|
      ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
          ∂(logMeasure x ω)| := by
  sorry

end Salt.Entropy.Chowla
