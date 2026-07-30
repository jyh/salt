/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Door
import Salt.MR.M4Window
import Salt.Entropy.Chowla.CircleMethod

/-!
# ⟦THE L² RESTRUCTURE⟧ stone 5 — THE PARSEVAL STONE and the door budget line

Source: `docs/exploration/l2-restructure-freeze-0730.md` (freeze v1, 2026-07-30 12:45 PDT),
stone 5 — "the Parseval-difference stone + the glue mass re-export"; and the refuter return
⟦REF-L2-STONE⟧ (`docs/blueprints/flags.md`, 2026-07-30 12:58 PDT), mandate **R1**, whose
kernel-checked probe this file ports verbatim.

## The finding this file carries

The door's sieve-insert error `a − 1_𝒮·a` is **frequency-INDEPENDENT**: the block indicator
`1_𝒮` does not see `α`.  So its total Fourier mass over ALL `H` frequencies is paid ONCE —
`∑_{ξ ∈ ZMod H} ‖(raw − sieved)^(−ξ.val/H)‖² = H·(time-side mass) ≤ H·notMemSCount` — instead
of once per major arc.  That is the whole `K`-shed of the restructure: the glue grade `δ` the
spine's `hMδ` reads becomes `|Ξ|`-FREE.

## The route (four steps, each a named lemma)

1. `errC_normSq_le` — the pointwise support/value bound `‖errC m‖² ≤ 1_{m ∉ 𝒮}` (the
   indicator is bare: on `𝒮` the error VANISHES, off it the datum is 1-bounded).
2. `offWindowSum_eq_dft` — ⟦THE CARRIER IDENTITY⟧: the door's window sum at `α = −ξ.val/H`
   IS a `ZMod.dft` of the window datum, up to a unimodular phase.  The half-open window
   `(n, n+H]` ↔ `ZMod H` bijection is `sum_zmod_window`; the phase IS `ZMod.stdAddChar`.
3. `parseval_insert_error` — `dft_parseval` (`CircleMethod.lean:126`, unnormalised dft with
   `H` on the TIME side) applied to the error datum.
4. `parseval_stone_budget` / `parseval_insert_budget_door` — the budget line over any
   frequency set `Ξ ⊆ ZMod H` (in particular `bigXi`), fed by the landed door mass.

## The door mass, carried named

`m4_door_insert_mass_integral` re-exports the `∫ notMemSCount dμ` bound that lives INSIDE
`m4_door_glue`'s proof (`M4Door.lean:738–762`) as a statement of its own — same constant `C`
(from `m4_door_sieve_mass`), same gate list verbatim (the M-gate `24C/δ ≤ M`, HS-3's per-block
bundle, the count bound, the `log ω ≥ 4` floor, the ladder's three gates).  Nothing is
re-proved: the derivation is the landed one, transcribed.  Composed with the stone it gives

  `(1/H²)·∑_{ξ∈Ξ} ∫‖raw − sieved‖² dμ ≤ δ/4 + 4·2^k/x`

— the freeze's budget line verbatim, and the `Ξ`-summed `L²` grade
`Salt.Entropy.Chowla.MRTUniformityXiL2` is stated to consume exactly this shape.

⟦ADDITIVE⟧ No landed declaration is touched; `norm_dft_neg_of_real` (the reality check the
`L²` major arm needs) is NOT duplicated here — stone 1 landed it in `CircleMethod.lean:700`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the insert error as a datum -/

/-- The insert error `a − 1_𝒮·a` (`memSCoeff` is M4-1's `1_𝒮`-multiplied datum). -/
def errC (Pseq Qseq : ℕ → ℕ) (J : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun m => a m - memSCoeff Pseq Qseq J a m

/-- **SUPPORT + VALUE BOUND**: `‖errC m‖² ≤ 1_{m ∉ 𝒮}` pointwise.  On `𝒮` the error is
exactly `0` (the insert is the identity there); off `𝒮` it is the raw datum, of modulus `≤ 1`.
The indicator is BARE — no constant leaks into the Parseval budget. -/
theorem errC_normSq_le (Pseq Qseq : ℕ → ℕ) (J : ℕ) {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (m : ℕ) :
    ‖errC Pseq Qseq J a m‖ ^ 2 ≤ (if ¬ MemS Pseq Qseq J m then (1 : ℝ) else 0) := by
  by_cases h : MemS Pseq Qseq J m
  · have h0 : errC Pseq Qseq J a m = 0 := by
      simp only [errC, memSCoeff, if_pos h]; ring
    rw [h0, if_neg (by simpa using h)]
    simp
  · have h0 : errC Pseq Qseq J a m = a m := by
      simp only [errC, memSCoeff, if_neg h]; ring
    rw [h0, if_pos (by simpa using h)]
    have := ha m
    nlinarith [norm_nonneg (a m)]

/-- The window sums are additive in the datum (`absWindowSum`, the absolute-indexed form). -/
theorem absWindowSum_sub (a b : ℕ → ℂ) (H n : ℕ) (α : ℝ) :
    absWindowSum (fun m => a m - b m) H n α
      = absWindowSum a H n α - absWindowSum b H n α := by
  simp only [absWindowSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The window sums are additive in the datum (`offWindowSum`, the re-based form). -/
theorem offWindowSum_sub (a b : ℕ → ℂ) (H n : ℕ) (α : ℝ) :
    offWindowSum (fun m => a m - b m) H n α
      = offWindowSum a H n α - offWindowSum b H n α := by
  simp only [offWindowSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## §2 — the carrier bridge: the window sum at `α = −ξ.val/H` IS a `ZMod.dft` -/

/-- The window datum on `ZMod H`: `j ↦ a(n + j.val + 1)` (the half-open window `(n, n+H]`,
transported to the cyclic group the dft lives on). -/
def winDatum (a : ℕ → ℂ) (H n : ℕ) : ZMod H → ℂ := fun j => a (n + ZMod.val j + 1)

/-- The `exp ↔ stdAddChar` conversion at `α = −ξ.val/H` (the `hd` step of
`CircleMethod.expSum_eq_char_sum`, at this file's carrier). -/
private lemma char_eq_phase {H : ℕ} [NeZero H] (ξ : ZMod H) (k : ℕ) {α : ℝ}
    (hα : α = -(ξ.val : ℝ) / (H : ℝ)) :
    ZMod.stdAddChar (-(((k : ℕ) : ZMod H) * ξ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((k : ℕ) : ℂ)) := by
  subst hα
  have hrw : -((((k : ℕ)) : ZMod H) * ξ) = ((-(((k : ℕ)) * ξ.val : ℕ) : ℤ) : ZMod H) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  rw [hrw, ZMod.stdAddChar_coe]; push_cast; ring_nf

/-- **THE CARRIER IDENTITY.**  `offWindowSum a H n (−ξ.val/H) = e(−ξ/H)·dft (winDatum a H n) ξ`.

The door's exponential-sum carrier and the circle method's Fourier carrier are the SAME
`H`-term sum; the only difference is a unimodular rebasing phase, invisible to every modulus
the door takes.  (Cf. `Theorem23Shell.windowExpSum_norm_eq_dft`, Bridge A, at the λ-datum;
this is its general-datum twin, stated at `offWindowSum` so the difference of two data can
pass through it.) -/
theorem offWindowSum_eq_dft {H : ℕ} [NeZero H] (a : ℕ → ℂ) (n : ℕ) (ξ : ZMod H) :
    offWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
      = ZMod.stdAddChar (-(((1 : ℕ) : ZMod H) * ξ)) * ZMod.dft (winDatum a H n) ξ := by
  classical
  let e : Fin H ≃ ZMod H :=
    { toFun := fun i => ((i : ℕ) : ZMod H)
      invFun := fun j => ⟨ZMod.val j, ZMod.val_lt j⟩
      left_inv := fun i => by apply Fin.ext; exact ZMod.val_natCast_of_lt i.isLt
      right_inv := fun j => by simp }
  have he : ∀ i : Fin H, e i = ((i : ℕ) : ZMod H) := fun _ => rfl
  have hev : ∀ i : Fin H, ZMod.val (e i) = (i : ℕ) := fun i => ZMod.val_natCast_of_lt i.isLt
  rw [ZMod.dft_apply, Finset.mul_sum, ← Equiv.sum_comp e]
  unfold offWindowSum
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hval : winDatum a H n (e i) = a (n + (i : ℕ) + 1) := by
    simp only [winDatum]
    rw [hev i]
  have hchar : ZMod.stdAddChar (-(((1 : ℕ) : ZMod H) * ξ)) * ZMod.stdAddChar (-((e i) * ξ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((-(ξ.val : ℝ) / (H : ℝ) : ℝ) : ℂ) * (((i : ℕ) : ℂ) + 1)) := by
    rw [← ZMod.stdAddChar.map_add_eq_mul]
    have hsum : -(((1 : ℕ) : ZMod H) * ξ) + -((e i) * ξ)
        = -(((((i : ℕ) + 1 : ℕ)) : ZMod H) * ξ) := by
      rw [he i]; push_cast; ring
    rw [hsum, char_eq_phase ξ ((i : ℕ) + 1) rfl]
    congr 2
    push_cast
    ring
  rw [smul_eq_mul, hval, ← mul_assoc, hchar]
  ring

/-- The norm form: the door's window sum at `−ξ.val/H` has the SAME modulus as the dft. -/
theorem norm_absWindowSum_eq_dft {H : ℕ} [NeZero H] (a : ℕ → ℂ) (n : ℕ) (ξ : ZMod H) :
    ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))‖ = ‖ZMod.dft (winDatum a H n) ξ‖ := by
  rw [← norm_offWindowSum, offWindowSum_eq_dft, norm_mul, ZMod.stdAddChar_apply,
    Circle.norm_coe, one_mul]

/-! ## §3 — the time-side sum IS the window sum -/

/-- The `ZMod H` ↔ `(n, n+H]` transport of a time-side sum (the half-open convention paying
off: the bijection is `j ↦ n + j.val + 1` on the nose). -/
theorem sum_zmod_window {H : ℕ} [NeZero H] (n : ℕ) (g : ℕ → ℝ) :
    ∑ j : ZMod H, g (n + ZMod.val j + 1) = ∑ m ∈ Finset.Ioc n (n + H), g m := by
  refine Finset.sum_nbij' (fun j : ZMod H => n + ZMod.val j + 1)
    (fun m : ℕ => ((m - n - 1 : ℕ) : ZMod H))
    (fun j _ => Finset.mem_Ioc.mpr ⟨by omega, by have := ZMod.val_lt j; omega⟩)
    (fun m _ => Finset.mem_univ _)
    (fun j _ => by
      rw [show n + ZMod.val j + 1 - n - 1 = ZMod.val j by omega, ZMod.natCast_zmod_val])
    (fun m hm => by
      rw [Finset.mem_Ioc] at hm
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega)
    (fun j _ => rfl)

/-! ## §4 — ⟦THE PARSEVAL STONE⟧ -/

/-- **R1, THE STONE.**  For a 1-bounded datum `a`, at every window position `n`:

`∑_{ξ ∈ ZMod H} ‖(raw − sieved)(−ξ.val/H)‖² ≤ H · notMemSCount`.

`dft_parseval` (`∑_ξ ‖𝓕Φ ξ‖² = H·∑_j ‖Φ j‖²` — unnormalised dft, `H` on the TIME side) plus
the pointwise support/value bound `errC_normSq_le`.  The inequality (not equality) is the
favorable direction: the time-side mass is bounded by the complement COUNT. -/
theorem parseval_insert_error {H : ℕ} [NeZero H] {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (J n : ℕ) :
    ∑ ξ : ZMod H, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff Pseq Qseq J a) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
      ≤ (H : ℝ) * ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) := by
  classical
  have hdiff : ∀ ξ : ZMod H,
      absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff Pseq Qseq J a) H n (-(ξ.val : ℝ) / (H : ℝ))
      = absWindowSum (errC Pseq Qseq J a) H n (-(ξ.val : ℝ) / (H : ℝ)) := by
    intro ξ
    rw [← absWindowSum_sub]
    rfl
  have hstep : ∑ ξ : ZMod H, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff Pseq Qseq J a) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
      = ∑ ξ : ZMod H, ‖ZMod.dft (winDatum (errC Pseq Qseq J a) H n) ξ‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [hdiff ξ, norm_absWindowSum_eq_dft]
  rw [hstep, dft_parseval]
  have htime : ∑ j : ZMod H, ‖winDatum (errC Pseq Qseq J a) H n j‖ ^ 2
      ≤ ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) := by
    have h1 : ∑ j : ZMod H, ‖winDatum (errC Pseq Qseq J a) H n j‖ ^ 2
        ≤ ∑ j : ZMod H,
            (if ¬ MemS Pseq Qseq J (n + ZMod.val j + 1) then (1 : ℝ) else 0) :=
      Finset.sum_le_sum (fun j _ => errC_normSq_le Pseq Qseq J ha _)
    have h2 : ∑ j : ZMod H,
        (if ¬ MemS Pseq Qseq J (n + ZMod.val j + 1) then (1 : ℝ) else 0)
        = ∑ m ∈ Finset.Ioc n (n + H), (if ¬ MemS Pseq Qseq J m then (1 : ℝ) else 0) :=
      sum_zmod_window n (fun m => if ¬ MemS Pseq Qseq J m then (1 : ℝ) else 0)
    have h3 : ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ)
        = ∑ m ∈ Finset.Ioc n (n + H), (if ¬ MemS Pseq Qseq J m then (1 : ℝ) else 0) :=
      card_notMemS_eq_sum (Finset.Ioc n (n + H)) Pseq Qseq J
    rw [h3, ← h2]
    exact h1
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  exact mul_le_mul_of_nonneg_left htime hH0

/-- **R1, THE BUDGET LINE, pointwise in `n`.**  Over ANY frequency set `Ξ ⊆ ZMod H` (in
particular `bigXi`):

`(1/H²)·∑_{ξ∈Ξ} ‖raw − sieved‖² ≤ (1/H)·notMemSCount`.

Restricting the sum to `Ξ` only discards nonnegative terms — the shed does not depend on
which frequencies the major arc keeps. -/
theorem parseval_stone_budget {H : ℕ} [NeZero H] {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (J n : ℕ) (Xi : Finset (ZMod H)) :
    (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ Xi, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff Pseq Qseq J a) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
      ≤ (1 / (H : ℝ)) * ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast NeZero.pos H
  have hsub : ∑ ξ ∈ Xi, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff Pseq Qseq J a) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
      ≤ ∑ ξ : ZMod H, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff Pseq Qseq J a) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
  have hpar := parseval_insert_error (H := H) ha Pseq Qseq J n
  have hkey : ∑ ξ ∈ Xi, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff Pseq Qseq J a) H n (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
      ≤ (H : ℝ) * ((notMemSCount Pseq Qseq J H n : ℕ) : ℝ) := le_trans hsub hpar
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul, div_le_div_iff₀ (by positivity)
    hHpos]
  nlinarith [Nat.cast_nonneg (α := ℝ) (notMemSCount Pseq Qseq J H n), hHpos]

/-! ## §5 — the glue mass, re-exported; and the composed door budget -/

/-- **A finite `ξ`-sum of `logMeasure` integrals, bounded pointwise.**  `∑_i ∫ f i ≤ ∫ g`
whenever `∑_i f i ≤ g` at every point.  Proved through `ShiftCorr.integral_logMeasure_eq`
(each integral is a finite weighted sum), so no integrability side condition is incurred —
the same route `M4Sieve.integral_logMeasure_le_add` takes. -/
theorem sum_integral_logMeasure_le {x ω : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (g : ℕ → ℝ) (hpt : ∀ n, ∑ i ∈ s, f i n ≤ g n) :
    ∑ i ∈ s, (∫ n, f i n ∂(logMeasure x ω)) ≤ ∫ n, g n ∂(logMeasure x ω) := by
  simp only [integral_logMeasure_eq]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_
    (inv_nonneg.mpr (Finset.sum_nonneg (fun n _ => by positivity)))
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hpt n) (by positivity)

/-- **THE GLUE MASS, RE-EXPORTED.**  The `∫ notMemSCount dμ` bound that lives inside
`m4_door_glue`'s proof (`M4Door.lean:738–762`), stated on its own:

`∫ notMemSCount dμ ≤ (δ/4)·H + 4·2^k·H/x`.

Same constant `C` (opened once from `m4_door_sieve_mass`), same gate list verbatim — the
M-gate `24C/δ ≤ M` (the freeze's `8C/δ` at the per-block grade `δ/3`, i.e. the `log ω`
absorption already applied), HS-3's per-block bundle, the count bound `k ≤ log ω/log 2 + 2`,
the door regime `2 ≤ x`, `2 ≤ ω`, `ω ≤ x`, `4 ≤ log ω`, and the ladder's three gates.  The
derivation is the landed one, transcribed: the sharp normalisation
(`integral_logMeasure_le_div`), the `k ≤ 3Z` cancellation, the `δ/3 → δ/4` rescale, and the
`Z ≥ 1` endpoint. -/
theorem m4_door_insert_mass_integral :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J x ω H k : ℕ) (δ : ℝ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 24 * C / δ ≤ (M : ℝ) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 4 ≤ Real.log ω →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (k : ℝ) ≤ Real.log ω / Real.log 2 + 2 →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      (∫ n, ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) ∂(logMeasure x ω))
        ≤ δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := m4_door_sieve_mass
  refine ⟨C, hC, ?_⟩
  intro A G M J x ω H k δ hA hG hM hδ hMδ hx hω hωx hL hxH hreach hpow hk hgate
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hpowR : (2 : ℝ) ^ (k + 1) ≤ (x : ℝ) := by exact_mod_cast hpow
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hpowR
  -- ⟦the normaliser⟧
  have hZlo : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    door_norm_ge hx hω hωx
  have hZ0 : (0 : ℝ) < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
  -- ⟦the mass, at the per-block grade δ/3 — the M-gate 24C/δ IS 8C/(δ/3)⟧
  have hδ3 : (0 : ℝ) < δ / 3 := by linarith
  have hMδ3 : 8 * C / (δ / 3) ≤ (M : ℝ) := by
    have he : 8 * C / (δ / 3) = 24 * C / δ := by field_simp; ring
    rw [he]; exact hMδ
  have hB := hmass A G M J x ω H k (δ / 3) hA hG hM hδ3 hMδ3 hxH hreach hpow hgate
  -- ⟦the sharp normalisation⟧
  have hint : (∫ n, ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ)
        ∂(logMeasure x ω))
      ≤ ((k : ℝ) * (δ / 3 / 4 * (H : ℝ)) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ))
          / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    integral_logMeasure_le_div hZ0 hB
  -- ⟦the absorption⟧
  have hk3 : (k : ℝ) ≤ 3 * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    door_count_le_three_mul_norm hL hk hZlo
  have habs := door_mass_normalised_le (k := k)
    (Z := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) (δ := δ) (Hr := (H : ℝ))
    (Gm := 4 * 2 ^ k * (H : ℝ) / (x : ℝ)) hZ0 hk3 hδ.le hH0
  -- ⟦the endpoint term: `Z ≥ 1` can only help⟧
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
  have hnn : (0 : ℝ) ≤ 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by positivity
  have hend : (4 * 2 ^ k * (H : ℝ) / (x : ℝ)) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹
      ≤ 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
    rw [div_le_iff₀ hZ0]
    nlinarith
  linarith

/-- **⟦THE FREEZE'S BUDGET LINE⟧** (stone 5's exit).  For a 1-bounded datum `a` and ANY
frequency set `Ξ ⊆ ZMod H`:

`(1/H²)·∑_{ξ∈Ξ} ∫‖raw − sieved‖² dμ ≤ δ/4 + 4·2^k/x`.

The sieve-insert error is α-INDEPENDENT, so its total Fourier mass is paid ONCE
(`parseval_stone_budget`) and the door's own mass estimate
(`m4_door_insert_mass_integral`) discharges it — the `|Ξ|` factor NEVER appears.  This is
the summand the spine's `hMδ` reads, and it is `K`-free; the `K` that survives the
restructure multiplies only the SQUARED-scale socket grade.

Gates: exactly `m4_door_glue`'s, carried named and unchanged, plus `NeZero H` (the dft's
carrier).  The constant `C` is `card_blockfree_le`'s, opened once through
`m4_door_sieve_mass`. -/
theorem parseval_insert_budget_door :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A G M J x ω H k : ℕ) [NeZero H] (a : ℕ → ℂ) (δ : ℝ)
      (Xi : Finset (ZMod H)),
      (∀ m, ‖a m‖ ≤ 1) →
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 24 * C / δ ≤ (M : ℝ) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 4 ≤ Real.log ω →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (k : ℝ) ≤ Real.log ω / Real.log 2 + 2 →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ Xi,
          ∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
              - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
                  (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure x ω)
        ≤ δ / 4 + 4 * 2 ^ k / (x : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := m4_door_insert_mass_integral
  refine ⟨C, hC, ?_⟩
  intro A G M J x ω H k _ a δ Xi ha hA hG hM hδ hMδ hx hω hωx hL hxH hreach hpow hk hgate
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast NeZero.pos H
  -- the pointwise stone, at every window position `n`
  have hpt : ∀ n : ℕ, ∑ ξ ∈ Xi, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
            (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
      ≤ (H : ℝ) * ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) := by
    intro n
    have hb := parseval_stone_budget (H := H) ha (calP A G) (calQK A G M) J n Xi
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul,
      div_le_div_iff₀ (by positivity) hHpos] at hb
    nlinarith [Nat.cast_nonneg (α := ℝ) (notMemSCount (calP A G) (calQK A G M) J H n), hHpos]
  -- the ξ-sum of integrals, bounded by the door's mass integral
  have hsum : ∑ ξ ∈ Xi, (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
          - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
              (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure x ω))
      ≤ ∫ n, (H : ℝ) * ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ)
          ∂(logMeasure x ω) :=
    sum_integral_logMeasure_le Xi _ _ hpt
  rw [integral_const_mul] at hsum
  have hmassI := hmass A G M J x ω H k δ hA hG hM hδ hMδ hx hω hωx hL hxH hreach hpow hk hgate
  have hchain : ∑ ξ ∈ Xi, (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
          - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
              (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure x ω))
      ≤ (H : ℝ) * (δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hmassI hHpos.le)
  have hfinal : (1 / (H : ℝ) ^ 2) * ((H : ℝ) * (δ / 4 * (H : ℝ)
      + 4 * 2 ^ k * (H : ℝ) / (x : ℝ))) = δ / 4 + 4 * 2 ^ k / (x : ℝ) := by
    field_simp
  calc (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ Xi,
        (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
                (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure x ω))
      ≤ (1 / (H : ℝ) ^ 2) * ((H : ℝ) * (δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = δ / 4 + 4 * 2 ^ k / (x : ℝ) := hfinal

end Salt.MR

end
