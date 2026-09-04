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
  apply Finset.sum_pos
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
      exact_mod_cast hn0
    exact inv_pos.mpr hnR
  · refine ⟨x, ?_⟩
    rw [Finset.mem_Ioc]
    exact ⟨Nat.div_lt_self (by omega) (by omega), le_refl x⟩

/-- **F4-R0b (class A).**  `HBudget.window_sum_inv_sq` (`:162`, private): `Σ 1/p² ≤ (2/(ε²H))·SP`
from `window_lb` (`ε²H/2 < p`). -/
theorem strideWindow_sum_inv_sq (eps : ℚ) (H : ℕ) :
    ∑ p ∈ primeWindow eps H, (1 / (p : ℝ) ^ 2)
      ≤ (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp1 : 1 ≤ p := (prime_of_mem_primeWindow hp).one_lt.le
  have hlb : (eps : ℝ) ^ 2 * (H : ℝ) / 2 < (p : ℝ) := window_lb eps H ⟨p, hp⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hple : (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast (mem_primeWindow.mp hp).1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hEH : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := lt_of_lt_of_le hpR hple
  have hinv : 1 / (p : ℝ) ≤ 2 / ((eps : ℝ) ^ 2 * (H : ℝ)) := by
    rw [div_le_div_iff₀ hpR hEH]; nlinarith [hlb]
  have key : (1 / (p : ℝ)) * (1 / (p : ℝ))
      ≤ (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * (1 / (p : ℝ)) :=
    mul_le_mul_of_nonneg_right hinv (by positivity)
  calc (1 : ℝ) / (p : ℝ) ^ 2 = (1 / (p : ℝ)) ^ 2 := by rw [div_pow, one_pow]
    _ = (1 / (p : ℝ)) * (1 / (p : ℝ)) := pow_two (1 / (p : ℝ))
    _ ≤ (2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * (1 / (p : ℝ)) := key

/-- **F4-R0c (class A).**  `HBudget.boundary_card_le` (`:428`, private): `⊆ Finset.Ico (H − q) H`,
`Nat.card_Ico`, `omega`. -/
theorem strideBoundary_card_le (H q : ℕ) :
    ((Finset.range H).filter (fun j => H ≤ j + q)).card ≤ q := by
  have hsub : (Finset.range H).filter (fun j => H ≤ j + q) ⊆ Finset.Ico (H - q) H := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_Ico]
    omega
  calc ((Finset.range H).filter (fun j => H ≤ j + q)).card
      ≤ (Finset.Ico (H - q) H).card := Finset.card_le_card hsub
    _ = H - (H - q) := Nat.card_Ico _ _
    _ ≤ q := by omega

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
  haveI : NeZero p := ⟨by omega⟩
  have hu : ((a : ℕ) : ZMod p) * ((a : ℕ) : ZMod p)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one a hcop
  set c : ZMod p := -(((a : ℕ) : ZMod p)⁻¹ * ((j + 1 : ℕ) : ZMod p)) with hc
  have hrc : ((c.val : ℕ) : ZMod p) = c := ZMod.natCast_rightInverse c
  have hlt : c.val < p := ZMod.val_lt c
  have hkey : ∀ n : ℕ, ((a * n + j + 1 : ℕ) : ZMod p) = 0 ↔ ((n : ℕ) : ZMod p) = c := by
    intro n
    have hcast : ((a * n + j + 1 : ℕ) : ZMod p)
        = ((a : ℕ) : ZMod p) * ((n : ℕ) : ZMod p) + ((j + 1 : ℕ) : ZMod p) := by
      push_cast; ring
    rw [hcast, hc]
    constructor
    · intro hn
      have h2 : ((a : ℕ) : ZMod p) * ((n : ℕ) : ZMod p) = -((j + 1 : ℕ) : ZMod p) := by
        linear_combination hn
      have h3 : ((a : ℕ) : ZMod p)⁻¹ * (((a : ℕ) : ZMod p) * ((n : ℕ) : ZMod p))
          = ((a : ℕ) : ZMod p)⁻¹ * (-((j + 1 : ℕ) : ZMod p)) := by rw [h2]
      rw [← mul_assoc, mul_comm (((a : ℕ) : ZMod p)⁻¹) (((a : ℕ) : ZMod p)), hu, one_mul] at h3
      rw [h3]; ring
    · intro hn
      rw [hn]
      have hx : ((a : ℕ) : ZMod p) * (((a : ℕ) : ZMod p)⁻¹ * ((j + 1 : ℕ) : ZMod p))
          = ((j + 1 : ℕ) : ZMod p) := by rw [← mul_assoc, hu, one_mul]
      rw [mul_neg, hx]; ring
  refine ⟨c.val, hlt, ?_, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff]
    exact (hkey c.val).mpr hrc
  · intro n
    rw [hkey n]
    constructor
    · intro hn
      have hn' : (n : ZMod p) = ((c.val : ℕ) : ZMod p) := by rw [hrc]; exact hn
      have h2 := (ZMod.natCast_eq_natCast_iff n c.val p).mp hn'
      have h3 : n % p = c.val % p := h2
      rw [h3, Nat.mod_eq_of_lt hlt]
    · intro hn
      have h2 : n ≡ c.val [MOD p] := by
        unfold Nat.ModEq
        rw [hn, Nat.mod_eq_of_lt hlt]
      have h4 := (ZMod.natCast_eq_natCast_iff n c.val p).mpr h2
      rw [h4, hrc]

/-- **F4-R1b (class A) — the class count, above.**
`#{j < H : ((j + 1 : ℕ) : ZMod a) = c} ≤ H/a + 1`:
`card_filter_natCast_eq_le` (`FBridge.lean:125`, modulus-generic) after the `j + 1 ↦ j` reindex of
the predicate (`StrideBridge.lean:163-170`'s `hset` trick at `c − 1`), or directly by the injection
`j ↦ (j + 1) / a` into `Finset.range (H / a + 2)`… — stated at `H/a + 1`, which the injection
`j ↦ j / a` into `range (H/a + 1)` gives after `Nat.div_le_div_right`. -/
theorem card_class_range_le (H a : ℕ) (c : ZMod a) :
    ((Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = c)).card ≤ H / a + 1 := by
  classical
  calc ((Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = c)).card
      ≤ (Finset.range (H / a + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun j : ℕ => j / a) ?_ ?_
        · intro j hj
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hj
          simp only [Finset.mem_coe, Finset.mem_range]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hj.1.le)
        · intro j hj j' hj' hjj
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hj hj'
          have heq : ((j + 1 : ℕ) : ZMod a) = ((j' + 1 : ℕ) : ZMod a) := by rw [hj.2, hj'.2]
          have hmod : (j + 1) % a = (j' + 1) % a := (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
          have hmod' : j % a = j' % a := Nat.ModEq.add_right_cancel' 1 hmod
          have hdd : j / a = j' / a := hjj
          have e1 := Nat.div_add_mod j a
          have e2 := Nat.div_add_mod j' a
          rw [hdd, hmod'] at e1
          exact e1.symm.trans e2
    _ = H / a + 1 := Finset.card_range _

/-- **F4-R1c (class C — new counting) — the class count, below.**  `H/a ≤ #{j < H : ((j + 1 : ℕ)
: ZMod a) = c}` for `1 ≤ a`: the `H/a` naturals `i < H/a` give the distinct indices
`j_i := a·i + ((c.val + a - 1) % a)` (so `j_i + 1 ≡ c.val ≡ c (mod a)`, `j_i < a·(H/a) ≤ H`),
an injection `Finset.range (H / a) → filter` (`Finset.card_le_card_of_injOn`; `Nat.div_mul_le_self`,
`ZMod.natCast_self_eq_zero`, `Nat.add_mul_mod_self_left`).  At `H < a` it is `0 ≤ _`. -/
theorem card_class_range_ge (H a : ℕ) (ha : 1 ≤ a) (c : ZMod a) :
    H / a ≤ ((Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = c)).card := by
  classical
  haveI : NeZero a := ⟨by omega⟩
  obtain ⟨t, hta, hcls⟩ : ∃ t : ℕ, t < a ∧ ∀ i : ℕ, ((a * i + t + 1 : ℕ) : ZMod a) = c := by
    refine ⟨(c.val + a - 1) % a, Nat.mod_lt _ (by omega), ?_⟩
    have hrc : ((c.val : ℕ) : ZMod a) = c := ZMod.natCast_rightInverse c
    have hmodeq : ((c.val + a - 1) % a + 1) ≡ c.val [MOD a] := by
      have h1 : (c.val + a - 1) % a ≡ (c.val + a - 1) [MOD a] := Nat.mod_modEq _ _
      have h2 : (c.val + a - 1) % a + 1 ≡ (c.val + a - 1) + 1 [MOD a] := h1.add_right 1
      have h3 : (c.val + a - 1) + 1 = c.val + a := by omega
      rw [h3] at h2
      exact h2.trans (Nat.add_mod_right c.val a)
    intro i
    have hcast : ((a * i + (c.val + a - 1) % a + 1 : ℕ) : ZMod a)
        = (((c.val + a - 1) % a + 1 : ℕ) : ZMod a) := by
      push_cast [ZMod.natCast_self]
      ring
    rw [hcast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq, hrc]
  calc H / a = (Finset.range (H / a)).card := (Finset.card_range _).symm
    _ ≤ ((Finset.range H).filter (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = c)).card := by
        refine Finset.card_le_card_of_injOn (fun i : ℕ => a * i + t) ?_ ?_
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_range] at hi
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
          refine ⟨?_, hcls i⟩
          have hi' : i + 1 ≤ H / a := hi
          have h1 : a * (i + 1) ≤ a * (H / a) := Nat.mul_le_mul (le_refl a) hi'
          have h2 : a * (H / a) ≤ H := by
            rw [Nat.mul_comm]; exact Nat.div_mul_le_self H a
          have h3 : a * i + t < a * (i + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
          exact lt_of_lt_of_le h3 (le_trans h1 h2)
        · intro i _ i' _ hii
          have h4 : a * i + t = a * i' + t := hii
          have h5 : a * i = a * i' := by omega
          exact Nat.eq_of_mul_eq_mul_left (by omega) h5

/-- **F4-R1d (class B) — the boundary count in the class, COARSE.**  The class's boundary indices
are among all boundary indices: `Finset.card_le_card (Finset.filter_subset_filter …)`-shape, then
`strideBoundary_card_le H q`.  Stated at a general `q` (used at `q := p * h`). -/
theorem card_class_boundary_le (H a q : ℕ) (c : ZMod a) :
    ((Finset.range H).filter
        (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = c ∧ H ≤ j + q)).card ≤ q := by
  classical
  refine le_trans (Finset.card_le_card ?_) (strideBoundary_card_le H q)
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, hj.2.2⟩

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
  rfl

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
  have hk' : k = a * (k / a) + b := affCollapse_base_point a b k hblt hk
  have hfb : ∀ n : ℕ, |(ArithmeticFunction.liouville (a * n + b) : ℝ)
      * (ArithmeticFunction.liouville (a * n + b + h) : ℝ)| ≤ 1 := by
    intro n
    rw [abs_mul]
    exact mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _)
  have e1 : shiftCorrAff a x ω k h
      = ∫ n, (ArithmeticFunction.liouville (a * (n + k / a) + b) : ℝ)
          * (ArithmeticFunction.liouville (a * (n + k / a) + b + h) : ℝ) ∂(logMeasure x ω) := by
    unfold shiftCorrAff
    rw [integral_logMeasureAff]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun n => ?_))
    have hidx : a * n + k = a * (n + k / a) + b := by
      conv_lhs => rw [hk']
      ring
    change (ArithmeticFunction.liouville (a * n + k) : ℝ)
        * (ArithmeticFunction.liouville (a * n + k + h) : ℝ)
      = (ArithmeticFunction.liouville (a * (n + k / a) + b) : ℝ)
          * (ArithmeticFunction.liouville (a * (n + k / a) + b + h) : ℝ)
    rw [hidx]
  have e2 : shiftCorrAff a x ω b h
      = ∫ n, (ArithmeticFunction.liouville (a * n + b) : ℝ)
          * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) ∂(logMeasure x ω) := by
    unfold shiftCorrAff
    exact integral_logMeasureAff a x ω _
  rw [e1, e2]
  refine le_trans (integral_shift_le x ω (k / a) hx hω hωx
    (fun t : ℕ => (ArithmeticFunction.liouville (a * t + b) : ℝ)
      * (ArithmeticFunction.liouville (a * t + b + h) : ℝ)) hfb) (le_of_eq ?_)
  ring

/-- **F4-R2d (class A).**  `|X_aff| ≤ 1`: `integral_logMeasureAff`, then the `h`-script of
`absXh_le_one` (`HBudget.lean:844`) verbatim — `integral_logMeasure_eq`, the termwise
`abs_liouville_le_one` bound, `strideWindow_Z_pos`. -/
theorem absXaff_le_one (a b h : ℕ) {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω) :
    |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
        * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| ≤ 1 := by
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  have hZpos : 0 < Z := strideWindow_Z_pos hx hω
  rw [integral_logMeasureAff, integral_logMeasure_eq]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Z⁻¹)]
  have hbound : |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) * (n : ℝ)⁻¹| ≤ Z := by
    calc |∑ n ∈ Finset.Ioc (x / ω) x,
            (ArithmeticFunction.liouville (a * n + b) : ℝ)
              * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) * (n : ℝ)⁻¹|
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x,
            |(ArithmeticFunction.liouville (a * n + b) : ℝ)
              * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) * (n : ℝ)⁻¹| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Ioc] at hn
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹), abs_mul]
          have h1 : |(ArithmeticFunction.liouville (a * n + b) : ℝ)|
              * |(ArithmeticFunction.liouville (a * n + b + h) : ℝ)| ≤ 1 :=
            mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _)
          nlinarith [inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hfin : Z⁻¹ * |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) * (n : ℝ)⁻¹| ≤ Z⁻¹ * Z :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  rwa [inv_mul_cancel₀ hZpos.ne'] at hfin

/-! ## F4-R3 — the per-pair reduction at stride `a` -/

/-- **F4-R3a (class A) — the collapsed image sum.**  `perPair_collapse_aff`
(`StrideBridge.lean:540`)
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
  have hkey : |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
        ((ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
          * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ)) / (n : ℝ)) / Z
        - 1 / (p : ℝ) *
          ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
              ((ArithmeticFunction.liouville (a * (p * m + r) + j + 1) : ℝ)
                * (ArithmeticFunction.liouville (a * (p * m + r) + j + p * h + 1) : ℝ))
                / (m : ℝ)) / Z)|
      ≤ 2 * 1 * (r : ℝ) / (p : ℝ) ^ 2 / Z := perPair_collapse_aff a h p j r hp hr hZ
  have hcongr : ∀ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
      (ArithmeticFunction.liouville (a * m + k) : ℝ)
        * (ArithmeticFunction.liouville (a * m + k + h) : ℝ) / (m : ℝ)
      = ((ArithmeticFunction.liouville (a * (p * m + r) + j + 1) : ℝ)
          * (ArithmeticFunction.liouville (a * (p * m + r) + j + p * h + 1) : ℝ)) / (m : ℝ) := by
    intro m _
    rw [liouville_collapse_aff a p j r k m h (by omega) hk]
  rw [Finset.sum_congr rfl hcongr]
  calc |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
         (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
           * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ) / (n : ℝ)) / Z
       - 1 / (p : ℝ) *
         ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
            ((ArithmeticFunction.liouville (a * (p * m + r) + j + 1) : ℝ)
              * (ArithmeticFunction.liouville (a * (p * m + r) + j + p * h + 1) : ℝ))
              / (m : ℝ)) / Z)|
      ≤ 2 * 1 * (r : ℝ) / (p : ℝ) ^ 2 / Z := hkey
    _ = 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z := by ring

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
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hZpos0 : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := strideWindow_Z_pos hx hω
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZdef
  set S : ℝ := 3 * (ω : ℝ) / (x : ℝ) / Z with hSdef
  have hZpos : 0 < Z := hZpos0
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have hSnn : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  set k : ℕ := (a * r + j + 1) / p with hkdef
  have hk : p * k = a * r + j + 1 := Nat.mul_div_cancel' hdvd
  have hg : ∀ n : ℕ, |(ArithmeticFunction.liouville (a * n + k) : ℝ)
      * (ArithmeticFunction.liouville (a * n + k + h) : ℝ)| ≤ 1 := by
    intro n
    rw [abs_mul]
    exact mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _)
  have hcol : |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
         (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
           * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ) / (n : ℝ)) / Z
       - 1 / (p : ℝ) *
         ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image (fun n => n / p),
            (ArithmeticFunction.liouville (a * m + k) : ℝ)
              * (ArithmeticFunction.liouville (a * m + k + h) : ℝ) / (m : ℝ)) / Z)|
      ≤ 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z :=
    perPair_collapse_aff_collapsed a h p j r k (by omega) hrx hk hZpos
  have hswap0 : |(∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image
          (fun n => n / p),
         (ArithmeticFunction.liouville (a * m + k) : ℝ)
           * (ArithmeticFunction.liouville (a * m + k + h) : ℝ) / (m : ℝ)) / Z
       - (∑ n ∈ Finset.Ioc (x / ω) x,
         (ArithmeticFunction.liouville (a * n + k) : ℝ)
           * (ArithmeticFunction.liouville (a * n + k + h) : ℝ) / (n : ℝ)) / Z|
      ≤ (2 * Real.log p + 6) / Z :=
    dilated_window_stability hp hrp hB hg hZpos
  have hshift_eq : (∑ n ∈ Finset.Ioc (x / ω) x,
        (ArithmeticFunction.liouville (a * n + k) : ℝ)
          * (ArithmeticFunction.liouville (a * n + k + h) : ℝ) / (n : ℝ)) / Z
      = shiftCorrAff a x ω k h := by
    unfold shiftCorrAff
    rw [integral_logMeasureAff, integral_logMeasure_eq,
        Finset.sum_congr rfl (fun n (_ : n ∈ Finset.Ioc (x / ω) x) =>
          div_eq_mul_inv ((ArithmeticFunction.liouville (a * n + k) : ℝ)
            * (ArithmeticFunction.liouville (a * n + k + h) : ℝ)) ((n : ℕ) : ℝ)),
        div_eq_mul_inv]
    exact mul_comm _ _
  have hkb : ((k : ℕ) : ZMod a) = ((b : ℕ) : ZMod a) := by
    have hcast : ((p * k : ℕ) : ZMod a) = ((a * r + j + 1 : ℕ) : ZMod a) := by rw [hk]
    have h1 : ((p : ℕ) : ZMod a) * ((k : ℕ) : ZMod a) = ((j + 1 : ℕ) : ZMod a) := by
      push_cast at hcast ⊢
      rw [ZMod.natCast_self] at hcast
      linear_combination hcast
    rw [hfilt] at h1
    have h2 : ((p : ℕ) : ZMod a) * ((k : ℕ) : ZMod a)
        = ((p : ℕ) : ZMod a) * ((b : ℕ) : ZMod a) := by
      rw [h1]; push_cast; ring
    have hpu : ((p : ℕ) : ZMod a) * ((p : ℕ) : ZMod a)⁻¹ = 1 :=
      ZMod.coe_mul_inv_eq_one p (Nat.Coprime.symm hcop)
    calc ((k : ℕ) : ZMod a)
        = (((p : ℕ) : ZMod a)⁻¹ * ((p : ℕ) : ZMod a)) * ((k : ℕ) : ZMod a) := by
          rw [mul_comm (((p : ℕ) : ZMod a)⁻¹), hpu, one_mul]
      _ = ((p : ℕ) : ZMod a)⁻¹ * (((p : ℕ) : ZMod a) * ((k : ℕ) : ZMod a)) := by ring
      _ = ((p : ℕ) : ZMod a)⁻¹ * (((p : ℕ) : ZMod a) * ((b : ℕ) : ZMod a)) := by rw [h2]
      _ = (((p : ℕ) : ZMod a)⁻¹ * ((p : ℕ) : ZMod a)) * ((b : ℕ) : ZMod a) := by ring
      _ = ((b : ℕ) : ZMod a) := by rw [mul_comm (((p : ℕ) : ZMod a)⁻¹), hpu, one_mul]
  have hshiftle := shiftCorrAff_le a b x ω hx hω hωx hblt k h hkb
  have hkp : (((k / a : ℕ)) : ℝ) * (p : ℝ) ≤ (p : ℝ) + (H : ℝ) := by
    have hdiv : a * (k / a) ≤ k := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self k a
    have hnat : a * ((k / a) * p) ≤ a * p + H := by
      calc a * ((k / a) * p) = (a * (k / a)) * p := by ring
        _ ≤ k * p := Nat.mul_le_mul hdiv (le_refl p)
        _ = p * k := Nat.mul_comm _ _
        _ = a * r + j + 1 := hk
        _ ≤ a * p + H := hkH
    have hR : (a : ℝ) * ((((k / a : ℕ)) : ℝ) * (p : ℝ)) ≤ (a : ℝ) * (p : ℝ) + (H : ℝ) := by
      exact_mod_cast hnat
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have h9 : (a : ℝ) * ((((k / a : ℕ)) : ℝ) * (p : ℝ)) ≤ (a : ℝ) * ((p : ℝ) + (H : ℝ)) := by
      nlinarith [hR, mul_nonneg (sub_nonneg.mpr haR) hHnn]
    exact le_of_mul_le_mul_left h9 (by linarith)
  set A : ℝ := (∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
      (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ) / (n : ℝ)) / Z with hAdef
  set IMG : ℝ := (∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = r)).image
      (fun n => n / p), (ArithmeticFunction.liouville (a * m + k) : ℝ)
        * (ArithmeticFunction.liouville (a * m + k + h) : ℝ) / (m : ℝ)) / Z with hIMGdef
  have hBC : |(1 / (p : ℝ)) * IMG - (1 / (p : ℝ)) * shiftCorrAff a x ω k h|
      ≤ (1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z) := by
    rw [← hshift_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hswap0 (by positivity)
  have hCD : |(1 / (p : ℝ)) * shiftCorrAff a x ω k h
        - (1 / (p : ℝ)) * shiftCorrAff a x ω b h|
      ≤ (1 / (p : ℝ)) * (((k / a : ℕ) : ℝ) * S) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hshiftle (by positivity)
  have hrle : (r : ℝ) ≤ (p : ℝ) := by exact_mod_cast hrp.le
  have hb1a : 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z ≤ 2 / ((p : ℝ) * Z) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hrle) hpR.le) hZpos.le]
  have hb1b : (1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z)
      = (2 * Real.log p + 6) / ((p : ℝ) * Z) := by field_simp
  have hsplit : (2 * Real.log p + 8) / ((p : ℝ) * Z)
      = 2 / ((p : ℝ) * Z) + (2 * Real.log p + 6) / ((p : ℝ) * Z) := by
    rw [← add_div]; congr 1; ring
  have hbound2 : (1 / (p : ℝ)) * (((k / a : ℕ) : ℝ) * S)
      ≤ ((1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2) * S := by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hSnn
    have hRHS : (1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2 = ((p : ℝ) + H) / (p : ℝ) ^ 2 := by
      field_simp
    rw [mul_comm, mul_one_div, hRHS, div_le_div_iff₀ hpR (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hkp hpR.le]
  calc |A - (1 / (p : ℝ)) * shiftCorrAff a x ω b h|
      ≤ |A - (1 / (p : ℝ)) * IMG|
          + (|(1 / (p : ℝ)) * IMG - (1 / (p : ℝ)) * shiftCorrAff a x ω k h|
            + |(1 / (p : ℝ)) * shiftCorrAff a x ω k h
                - (1 / (p : ℝ)) * shiftCorrAff a x ω b h|) := by
        have h1 := abs_sub_le A ((1 / (p : ℝ)) * IMG)
          ((1 / (p : ℝ)) * shiftCorrAff a x ω b h)
        have h2 := abs_sub_le ((1 / (p : ℝ)) * IMG)
          ((1 / (p : ℝ)) * shiftCorrAff a x ω k h)
          ((1 / (p : ℝ)) * shiftCorrAff a x ω b h)
        linarith
    _ ≤ 2 * (r : ℝ) / (p : ℝ) ^ 2 / Z
          + ((1 / (p : ℝ)) * ((2 * Real.log p + 6) / Z)
            + (1 / (p : ℝ)) * (((k / a : ℕ) : ℝ) * S)) := by
        linarith [hcol, hBC, hCD]
    _ ≤ (2 * Real.log p + 8) / ((p : ℝ) * Z)
          + ((1 / (p : ℝ)) + (H : ℝ) / (p : ℝ) ^ 2) * S := by
        rw [hsplit, hb1b]
        linarith [hb1a, hbound2]

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
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  simp_rw [integral_logMeasureAff]
  rw [integral_logMeasure_eq]
  simp_rw [fBridgeF_aff_liouville_apply eps H a b h, integral_logMeasure_eq]
  have hR : ∑ n ∈ Finset.Ioc (x / ω) x,
        (∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((a * n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
              ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H (a * n)) (j + (p : ℕ) * h) : ℝ)
            else 0)) * (n : ℝ)⁻¹
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H, ∑ n ∈ Finset.Ioc (x / ω) x,
          (if ((a * n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
              ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H (a * n)) (j + (p : ℕ) * h) : ℝ)
            else 0) * (n : ℝ)⁻¹ := by
    have step1 : ∀ n : ℕ,
        (∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((a * n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
              ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H (a * n)) (j + (p : ℕ) * h) : ℝ)
            else 0)) * (n : ℝ)⁻¹
        = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((a * n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
              ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H (a * n)) (j + (p : ℕ) * h) : ℝ)
            else 0) * (n : ℝ)⁻¹ := by
      intro n
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun p _ => Finset.sum_mul _ _ _)
    rw [Finset.sum_congr rfl (fun n _ => step1 n), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]

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
  by_cases hfilt : ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a)
  · rw [if_pos hfilt, if_pos hfilt]
    have hp2 : 2 ≤ p := (prime_of_mem_primeWindow hp).two_le
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    have hZpos : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := strideWindow_Z_pos hx hω
    have hBp_nonneg : (0 : ℝ)
        ≤ (2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
          + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
              * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)) := by
      apply add_nonneg
      · exact div_nonneg (by linarith) (by positivity)
      · exact mul_nonneg (by positivity) (by positivity)
    by_cases hbd : H ≤ j + p * h
    · rw [if_pos hbd]
      have hwv0 : ∀ m : ℕ, (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ) = 0 := fun m => by
        simp only [windowVal, dif_neg (Nat.not_lt.mpr hbd), Int.cast_zero]
      have hT0 : (∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
          ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
          (ArithmeticFunction.liouville (m + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ) else 0)
          ∂(logMeasureAff a x ω)) = 0 := by
        rw [show (fun m => if ((m + j + 1 : ℕ) : ZMod p) = 0
            ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (m + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ) else 0)
            = (fun _ => (0 : ℝ)) from funext (fun m => by rw [hwv0 m, mul_zero, ite_self]),
          integral_zero]
      rw [hT0, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
      linarith [hBp_nonneg]
    · rw [if_neg hbd, add_zero]
      rw [not_le] at hbd
      obtain ⟨r, hrp, hdvd, hgate⟩ := gate_residue_aff a p j hp2 hcop
      have hpmul : p ≤ p * h := by
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hlt : p * h < H := Nat.lt_of_le_of_lt (Nat.le_add_left _ j) hbd
      have hpH : p ≤ H := le_of_lt (Nat.lt_of_le_of_lt hpmul hlt)
      have hT_eq : (∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
          ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
          (ArithmeticFunction.liouville (m + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ) else 0)
          ∂(logMeasureAff a x ω))
          = (∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = r),
              (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
                * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ) / (n : ℝ))
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
        rw [integral_logMeasureAff]
        rw [show (fun n => if ((a * n + j + 1 : ℕ) : ZMod p) = 0
            ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H (a * n)) (j + p * h) : ℝ) else 0)
            = (fun n => if n % p = r then
              (ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
                * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ) else 0)
            from funext (fun n => by
              rw [windowVal_liouvilleWindow H (a * n) (j + p * h) hbd,
                  show a * n + (j + p * h) + 1 = a * n + j + p * h + 1 from by ring]
              simp only [hgate n, hfilt, and_true])]
        rw [integral_logMeasure_eq, div_eq_mul_inv, mul_comm]
        congr 1
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun n _ => by rw [ite_mul, zero_mul, div_eq_mul_inv])
      rw [hT_eq]
      exact perPair_bound_aff a b h H hx hω hωx ha hblt p j r hp2 hcop hrp hdvd hfilt
        (le_trans hrp.le (le_trans hpH hxωH)) (by omega)
        (by
          have h1 : a * r ≤ a * p := Nat.mul_le_mul (le_refl a) hrp.le
          omega)
  · rw [if_neg hfilt, if_neg hfilt]
    have hT0 : (∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
        ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
        (ArithmeticFunction.liouville (m + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ) else 0)
        ∂(logMeasureAff a x ω)) = 0 := by
      rw [show (fun m => if ((m + j + 1 : ℕ) : ZMod p) = 0
          ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
          (ArithmeticFunction.liouville (m + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ) else 0)
          = (fun _ => (0 : ℝ)) from funext (fun m => if_neg (fun hc => hfilt hc.2)),
        integral_zero]
    rw [hT0, sub_zero, abs_zero]

/-! ## F4-R5 — THE BUDGET at the affine forms (the capstone) -/

set_option maxHeartbeats 1600000 in
-- The budget aggregation is a single large elaboration, as at the landed
-- `HBudget.lean:1182` (`hbudget_holds_h`); the ceiling here is that
-- declaration's, unchanged.
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
  obtain ⟨c, hc, hcge, H₀, hD3⟩ := primeWindow_sum_inv_ge_bounded
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro a b h eps H x ω hh ha hblt hcopPH hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0
    hgate hcount hωbig hxbig
  have hcop : ∀ p ∈ primeWindow eps H, Nat.Coprime a p := by
    rw [PH, Nat.coprime_prod_right_iff] at hcopPH
    exact hcopPH
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have haPos : (0 : ℝ) < (a : ℝ) := by linarith
  have haNe : (a : ℝ) ≠ 0 := haPos.ne'
  have hZpos : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := strideWindow_Z_pos hx hω
  have hZlb : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    (harmonic_window_bounds hx hω hωx).1
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hε2H0 : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := by linarith
  have hSP_lb : c / Real.log H ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    hD3 eps H hH0 hsqrt hepssq
  have hSPpos : (0 : ℝ) < ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    lt_of_lt_of_le (by positivity) hSP_lb
  have habsX : |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
      * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| ≤ 1 :=
    absXaff_le_one a b h hx hω
  have hcard : ((primeWindow eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime eps H hsqrt hH3
  have hxωH : H ≤ x / ω := by
    have hpos : (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) := by positivity
    have h2 : ω * H ≤ x := by
      have h3 : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by linarith
      exact_mod_cast h3
    rw [Nat.le_div_iff_mul_le (by omega : 0 < ω), Nat.mul_comm]; exact h2
  have hωR : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast (by omega : 0 < ω)
  have hε_le1 : (eps : ℝ) ≤ 1 := by nlinarith [hepssq, hepsR]
  have hlogε2H : (0 : ℝ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hple : ∀ p ∈ primeWindow eps H, (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    intro p hp
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast (mem_primeWindow.mp hp).1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hZbig' : 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64
      ≤ (eps : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    have h2 : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ)
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hepsR.le
    have hlhs : (eps : ℝ)
        * ((16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ))
        = 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 := by field_simp
    rw [hlhs] at h3; exact h3
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    nlinarith [hZbig', hlogε2H, hε_le1, hZpos, mul_le_mul_of_nonneg_right hε_le1 hZpos.le]
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hle : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by
      nlinarith [hxbig, (show (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        by positivity)]
    nlinarith [hle, mul_pos hωR hHR]
  -- === slice 1 (dilation + swap) ===
  have hZεbound : (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
      / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) ≤ (eps : ℝ) / 8 := by
    rw [div_le_div_iff₀ hZpos (by norm_num)]
    nlinarith [hZbig']
  have hsum1 : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
        * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ) := by
    have hle : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
          * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8) / (((p : ℕ) : ℝ)
          * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by
        exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < (p : ℕ))
      have hlogle : Real.log (p : ℕ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) :=
        Real.log_le_log hpR (hple p hp)
      gcongr
    have heq : ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
          / (((p : ℕ) : ℝ) * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        = (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [div_mul_eq_mul_div, mul_one_div, div_div]
    have hfin : (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
          / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))
        ≤ ((eps : ℝ) / 8) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right hZεbound hSPpos.le
    have hgoal : ((eps : ℝ) / 8) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))
        = (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ) := by ring
    linarith [hle, heq.le, heq.ge, hfin, hgoal.le, hgoal.ge]
  -- === slice 2 (shift) ===
  have key2 : ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      = ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => (mul_one_div _ _).symm)
  have hHsq : (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2)
      ≤ (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left (strideWindow_sum_inv_sq eps H) hHR.le
    have h2 : (H : ℝ) * ((2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        = (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by field_simp
    linarith [h1, h2.le, h2.ge]
  have hSpos2 : (0 : ℝ) ≤ 3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    positivity
  have hxbound : 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ (eps : ℝ) / (16 * (1 + 2 / (eps : ℝ) ^ 2)) := by
    have hxZ : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
      have hx1 : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := by
        nlinarith [hxbig, (show (0 : ℝ) ≤ (ω : ℝ) * (H : ℝ) by positivity)]
      calc 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := hx1
        _ = (x : ℝ) * 1 := (mul_one _).symm
        _ ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hZ1 hxpos.le
    rw [div_le_iff₀ hepsR] at hxZ
    rw [div_div, div_le_div_iff₀ (mul_pos hxpos hZpos) (by positivity)]
    nlinarith [hxZ]
  have hsum2 : ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ) := by
    rw [key2]
    have hfac : ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ ((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hHsq]) hSpos2
    have hmul : ((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ) := by
      have hCbound := hxbound
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (1 + 2 / (eps : ℝ) ^ 2))] at hCbound
      nlinarith [mul_le_mul_of_nonneg_left hCbound
        (by positivity : (0 : ℝ) ≤ (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) / 16)]
    linarith [hfac, hmul]
  -- === slice 3 (boundary), the gate at 64 ===
  have hT3 : ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ m,
        (ArithmeticFunction.liouville (m + b) : ℝ)
          * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|)
      ≤ (1 / 32) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ)) * (eps : ℝ) := by
    have hhR : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    have h64 : (eps : ℝ) * (a : ℝ) * (h : ℝ) * (64 * Real.log 4) ≤ c :=
      (le_div_iff₀ (by positivity)).mp hgate
    have hexp : (eps : ℝ) * (a : ℝ) * (h : ℝ) * (64 * Real.log 4)
          * (((H : ℝ) / (a : ℝ)) * (eps : ℝ) / 32)
        = 2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) * (h : ℝ) := by
      field_simp
      ring
    have hmul := mul_le_mul_of_nonneg_right h64
      (by positivity : (0 : ℝ) ≤ ((H : ℝ) / (a : ℝ)) * (eps : ℝ) / 32)
    rw [hexp] at hmul
    have hkey3' : 2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) * (h : ℝ)
        ≤ (1 / 32) * c * ((H : ℝ) / (a : ℝ)) * (eps : ℝ) := by linarith [hmul]
    calc ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ m,
            (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|)
        ≤ ((primeWindow eps H).card : ℝ) * ((h : ℝ) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habsX hhR) (Nat.cast_nonneg _)
      _ = ((primeWindow eps H).card : ℝ) * (h : ℝ) := by rw [mul_one]
      _ ≤ ((2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))) * (h : ℝ) :=
          mul_le_mul_of_nonneg_right hcard hhR
      _ = (2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ)) * (h : ℝ)) / Real.log H := by ring
      _ ≤ ((1 / 32) * c * ((H : ℝ) / (a : ℝ)) * (eps : ℝ)) / Real.log H := by gcongr
      _ = (1 / 32) * (c / Real.log H) * ((H : ℝ) / (a : ℝ)) * (eps : ℝ) := by ring
      _ ≤ (1 / 32) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
            * (eps : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSP_lb (by norm_num)) (by positivity)) hepsR.le
  -- === slices 4 and 5 (the ±1 count and the two `+1` leftovers) ===
  have hHA_ge : (64 : ℝ) ≤ ((H : ℝ) / (a : ℝ)) * (eps : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ haPos]
    linarith [hcount]
  have hHA_12 : (12 : ℝ) ≤ (H : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ haPos]
    nlinarith [hcount, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (eps : ℝ)) hHR.le]
  have hslice4 : (∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
      ≤ (1 / 64) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ)) * (eps : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hHA_ge hSPpos.le]
  have hslice5 : (3 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ)
      ≤ (1 / 64) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ)) * (eps : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hHA_12
      (by positivity : (0 : ℝ) ≤ (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ) / 64)]
  -- === the div/floor comparisons for the class count ===
  have hdivR : ((H / a : ℕ) : ℝ) ≤ (H : ℝ) / (a : ℝ) := Nat.cast_div_le
  have hdivR2 : (H : ℝ) / (a : ℝ) < ((H / a : ℕ) : ℝ) + 1 := by
    have h1 : H < a * (H / a) + a := by
      have h2 : a * (H / a) + H % a = H := Nat.div_add_mod H a
      have h3 : H % a < a := Nat.mod_lt _ (by omega)
      omega
    have h4 : (H : ℝ) < (a : ℝ) * ((H / a : ℕ) : ℝ) + (a : ℝ) := by exact_mod_cast h1
    rw [div_lt_iff₀ haPos]
    linarith
  -- === the unfold and the assembly ===
  have hIF : (∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
        ∂(logMeasureAff a x ω))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
                  ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (m + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ)
            else 0) ∂(logMeasureAff a x ω) := by
    rw [IF_unfold_aff a b h eps H]
    exact Finset.sum_coe_sort (primeWindow eps H)
      (fun p => ∑ j ∈ Finset.range H, ∫ m, (if ((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
        ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
        (ArithmeticFunction.liouville (m + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ) else 0)
        ∂(logMeasureAff a x ω))
  have hMAINsplit : (∑ p ∈ primeWindow eps H, ((H : ℝ) / (a : ℝ)) / (p : ℝ)
        * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
            * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)))
      = (∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
            (1 / (p : ℝ)) * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)) else 0))
        + (∑ p ∈ primeWindow eps H,
            (((H : ℝ) / (a : ℝ))
              - (((Finset.range H).filter
                    (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a))).card : ℝ))
              * ((1 / (p : ℝ)) * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ)
                    ∂(logMeasureAff a x ω)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  have habs3 : ∀ u v w : ℝ, |u - (v + w)| ≤ |u - v| + |w| := by
    intro u v w
    have h1 := abs_sub_le u v (v + w)
    have h2 : |v - (v + w)| = |w| := by
      rw [show v - (v + w) = -w from by ring, abs_neg]
    linarith [h1, h2.le, h2.ge]
  have hterm : ∀ p ∈ primeWindow eps H, ∀ j ∈ Finset.range H,
      |(∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
                ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
          (ArithmeticFunction.liouville (m + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ) else 0)
          ∂(logMeasureAff a x ω))
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
        else 0 :=
    fun p hp j hj => per_term_aff a b h hh ha hblt eps H hx hω hωx hxωH p hp (hcop p hp) j
      (Finset.mem_range.mp hj)
  rw [hIF, hMAINsplit]
  refine le_trans (habs3 _ _ _) ?_
  have hE : |∑ p ∈ primeWindow eps H,
        (((H : ℝ) / (a : ℝ))
          - (((Finset.range H).filter
                (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a))).card : ℝ))
          * ((1 / (p : ℝ)) * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)))|
      ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : 2 ≤ p := (prime_of_mem_primeWindow hp).two_le
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hge : ((H / a : ℕ) : ℝ)
        ≤ ((((Finset.range H).filter
              (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a))).card : ℕ) : ℝ) := by
      exact_mod_cast card_class_range_ge H a ha (((p * b : ℕ) : ZMod a))
    have hle : ((((Finset.range H).filter
              (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a))).card : ℕ) : ℝ)
        ≤ ((H / a : ℕ) : ℝ) + 1 := by
      exact_mod_cast card_class_range_le H a (((p * b : ℕ) : ZMod a))
    have hd1 : |((H : ℝ) / (a : ℝ))
        - ((((Finset.range H).filter
              (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a))).card : ℕ) : ℝ)|
        ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hdivR, hdivR2, hge, hle]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
    have hinvnn : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hinner : (1 / (p : ℝ)) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
          * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
        ≤ (1 / (p : ℝ)) * 1 := mul_le_mul_of_nonneg_left habsX hinvnn
    have hfin := mul_le_mul hd1 hinner (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    calc |(H : ℝ) / (a : ℝ)
            - ((((Finset.range H).filter
                  (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a))).card : ℕ) : ℝ)|
          * ((1 / (p : ℝ)) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|)
        ≤ 1 * ((1 / (p : ℝ)) * 1) := hfin
      _ = 1 / (p : ℝ) := by ring
  have hD : |(∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
        ∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
                ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
          (ArithmeticFunction.liouville (m + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ)
          else 0) ∂(logMeasureAff a x ω))
      - (∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
            (1 / (p : ℝ)) * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω))
            else 0))|
      ≤ ((H : ℝ) / (a : ℝ) + 1)
          * ((1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ)
            + (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ))
        + ((primeWindow eps H).card : ℝ) * ((h : ℝ) * |∫ m,
            (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|) := by
    rw [← Finset.sum_sub_distrib]
    have hcombine : ∀ p ∈ primeWindow eps H,
        (∑ j ∈ Finset.range H, ∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
              ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (m + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ)
            else 0) ∂(logMeasureAff a x ω))
          - (∑ j ∈ Finset.range H,
              (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
                (1 / (p : ℝ)) * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω))
                else 0))
        = ∑ j ∈ Finset.range H,
            ((∫ m, (if ((m + j + 1 : ℕ) : ZMod p) = 0
                  ∧ ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
                (ArithmeticFunction.liouville (m + j + 1) : ℝ)
                  * (windowVal H (liouvilleWindow H m) (j + p * h) : ℝ)
                else 0) ∂(logMeasureAff a x ω))
              - (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
                  (1 / (p : ℝ)) * (∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                    * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω))
                  else 0)) :=
      fun p _ => by rw [Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl hcombine]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun p hp => Finset.abs_sum_le_sum_abs _ _)).trans ?_
    refine (Finset.sum_le_sum (fun p hp => Finset.sum_le_sum
      (fun j hj => hterm p hp j hj))).trans ?_
    have hper : ∀ p ∈ primeWindow eps H,
        (∑ j ∈ Finset.range H,
          (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
            ((2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
              + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                  * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)))
            + (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ m,
                (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
              else 0)
          else 0))
        ≤ ((H : ℝ) / (a : ℝ) + 1)
            * ((2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
              + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                  * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)))
          + (h : ℝ) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| := by
      intro p hp
      have hp2 : 2 ≤ p := (prime_of_mem_primeWindow hp).two_le
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
      have hBnn : (0 : ℝ)
          ≤ (2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
            + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)) := by
        apply add_nonneg
        · exact div_nonneg (by linarith) (by positivity)
        · exact mul_nonneg (by positivity) (by positivity)
      have hsp : ∀ j : ℕ,
          (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
            ((2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
              + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                  * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)))
            + (if H ≤ j + p * h then (1 / (p : ℝ)) * |∫ m,
                (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
              else 0)
          else 0)
          = (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
              ((2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
                + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                    * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)))
            else 0)
            + (if (((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) ∧ H ≤ j + p * h) then
                (1 / (p : ℝ)) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
              else 0) := by
        intro j
        by_cases hF : ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a)
        · by_cases hQ : H ≤ j + p * h
          · rw [if_pos hF, if_pos hQ, if_pos hF, if_pos (And.intro hF hQ)]
          · rw [if_pos hF, if_neg hQ, if_pos hF, if_neg (fun hc => hQ hc.2)]
        · rw [if_neg hF, if_neg hF, if_neg (fun hc => hF hc.1), add_zero]
      rw [Finset.sum_congr rfl (fun j _ => hsp j), Finset.sum_add_distrib]
      have hA1 : (∑ j ∈ Finset.range H,
            (if ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) then
              ((2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
                + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                    * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)))
            else 0))
          ≤ ((H : ℝ) / (a : ℝ) + 1)
              * ((2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
                + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                    * (3 * (ω : ℝ) / (x : ℝ)
                        / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ hBnn
        have hcle : ((((Finset.range H).filter
              (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a))).card : ℕ) : ℝ)
            ≤ ((H / a : ℕ) : ℝ) + 1 := by
          exact_mod_cast card_class_range_le H a (((p * b : ℕ) : ZMod a))
        linarith [hdivR, hcle]
      have hA2 : (∑ j ∈ Finset.range H,
            (if (((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a) ∧ H ≤ j + p * h) then
              (1 / (p : ℝ)) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
            else 0))
          ≤ (h : ℝ) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hcb : ((((Finset.range H).filter
              (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a)
                ∧ H ≤ j + p * h)).card : ℕ) : ℝ) ≤ (p : ℝ) * (h : ℝ) := by
          have hnat := card_class_boundary_le H a (p * h) (((p * b : ℕ) : ZMod a))
          calc ((((Finset.range H).filter
                (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a)
                  ∧ H ≤ j + p * h)).card : ℕ) : ℝ)
              ≤ ((p * h : ℕ) : ℝ) := by exact_mod_cast hnat
            _ = (p : ℝ) * (h : ℝ) := by push_cast; ring
        calc ((((Finset.range H).filter
                (fun j : ℕ => ((j + 1 : ℕ) : ZMod a) = ((p * b : ℕ) : ZMod a)
                  ∧ H ≤ j + p * h)).card : ℕ) : ℝ)
              * ((1 / (p : ℝ)) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|)
            ≤ ((p : ℝ) * (h : ℝ))
              * ((1 / (p : ℝ)) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                  * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|) :=
              mul_le_mul_of_nonneg_right hcb (by positivity)
          _ = (h : ℝ) * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
                * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| := by
              field_simp
      linarith [hA1, hA2]
    refine (Finset.sum_le_sum hper).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hBsum : (∑ p ∈ primeWindow eps H,
          ((2 * Real.log p + 8) / ((p : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
            + (1 / (p : ℝ) + (H : ℝ) / (p : ℝ) ^ 2)
                * (3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))))
        ≤ (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ)
          + (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (eps : ℝ) := by
      rw [Finset.sum_add_distrib]
      linarith [hsum1, hsum2]
    have hHA1 : (0 : ℝ) ≤ (H : ℝ) / (a : ℝ) + 1 := by positivity
    linarith [mul_le_mul_of_nonneg_left hBsum hHA1]
  linarith [hD, hE, hT3, hslice4, hslice5]

/-! ## F4-R6 — the reduction closes -/

/-- **F4-R6a (class B) — `hreduce_holds_h` (`HMainAssembly.lean:165`) at the affine forms.**
Index-blind arithmetic: `set SP`, `set Xs := X_aff`, `set IF`, `set MAIN := Σ_p ((H/a)/p)·Xs`;
`hSPH : Σ_p ((H/a)/p) = SP·(H/a)` (`Finset.sum_mul`, `one_div_mul_eq_div`);
`|MAIN| = SP·(H/a)·|Xs|`;
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
  set SP : ℝ := ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) with hSP
  set Xs : ℝ := ∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
      * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω) with hXs
  set IFa : ℝ := ∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
      ∂(logMeasureAff a x ω) with hIFa
  set MAIN : ℝ := ∑ p ∈ primeWindow eps H, ((H : ℝ) / (a : ℝ)) / (p : ℝ) * Xs with hMAIN
  have hSPnn : (0 : ℝ) ≤ SP := Finset.sum_nonneg (fun p _ => by positivity)
  have hHnn : (0 : ℝ) ≤ (H : ℝ) / (a : ℝ) := div_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg a)
  have hfac : MAIN = (∑ p ∈ primeWindow eps H, ((H : ℝ) / (a : ℝ)) / (p : ℝ)) * Xs := by
    rw [hMAIN, Finset.sum_mul]
  have hsumnn : (0 : ℝ) ≤ ∑ p ∈ primeWindow eps H, ((H : ℝ) / (a : ℝ)) / (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => div_nonneg hHnn (Nat.cast_nonneg _))
  have hSPH : (∑ p ∈ primeWindow eps H, ((H : ℝ) / (a : ℝ)) / (p : ℝ))
      = SP * ((H : ℝ) / (a : ℝ)) := by
    rw [hSP, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun p _ => by rw [one_div_mul_eq_div])
  have hMAIN_abs : |MAIN| = SP * ((H : ℝ) / (a : ℝ)) * |Xs| := by
    rw [hfac, abs_mul, abs_of_nonneg hsumnn, hSPH]
  have hmain : SP * ((H : ℝ) / (a : ℝ)) * |Xs| - |IFa - MAIN| ≤ |IFa| := by
    have h1 : |MAIN| - |IFa| ≤ |IFa - MAIN| := by
      rw [abs_sub_comm IFa MAIN]
      exact abs_sub_abs_le_abs_sub MAIN IFa
    linarith [hMAIN_abs]
  have hprod : (0 : ℝ) ≤ (2 * |Xs| - (eps : ℝ)) * (SP * ((H : ℝ) / (a : ℝ))) :=
    mul_nonneg (by linarith [hseed]) (mul_nonneg hSPnn hHnn)
  nlinarith [hmain, hbudget, hprod]

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
  set SP : ℝ := ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) with hSP
  set Xv : ℝ := |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
      * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| with hXv
  have hSPnn : (0 : ℝ) ≤ SP := Finset.sum_nonneg (fun p _ => by positivity)
  have hHnn : (0 : ℝ) ≤ (H : ℝ) / (a : ℝ) := div_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg a)
  have hprod : (0 : ℝ) ≤ (2 * Xv - (eps : ℝ)) * (SP * ((H : ℝ) / (a : ℝ))) :=
    mul_nonneg (by linarith) (mul_nonneg hSPnn hHnn)
  nlinarith [hmain, hbudget, hprod]

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
  intro δ hδ hseed
  exact fBridge_of_singleCorr_aff' eps H a b h ha hlog hcM hmert HRED hδ hseed

/-- **F4-R6d (class A) — THE CAPSTONE COMPOSED: `hreduce_holds_final_h` (`HBudget.lean:1514`) at the
affine forms.**  `obtain ⟨c, hc, hcge, H₀, hbud⟩ := hbudget_holds_aff;
refine ⟨c, hc, hcge, H₀, ?_⟩` (the
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
  obtain ⟨c, hc, hcge, H₀, hbud⟩ := hbudget_holds_aff
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro a b h eps H x ω hh ha hblt hcop hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0
    hgate hcount hωbig hxbig hseed
  exact hreduce_holds_aff a b h eps H hseed
    (hbud a b h eps H x ω hh ha hblt hcop hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0
      hgate hcount hωbig hxbig)

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
  have hmain := hreduce_holds_aff 1 0 h eps H hseed hbudget
  simp only [logMeasureAff_one, fBridgeF_aff_one_zero, Nat.cast_one, div_one, add_zero] at hmain
  exact hmain

end Salt.Entropy.Chowla
