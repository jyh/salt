/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PerEEngine2

/-!
# PE3 — the α-side per-`e` bound (the last analytic lemma of the Chen arc)

Design: `docs/blueprints/flags.md`, "2026-07-13 THE PE3 GATE — CATCH #44" (the frozen v2
design) and "CATCH #43"; `docs/blueprints/chen.md`, "THE PE ARC".

After PE1/PE2 (`Salt.Chen.PerEEngine2`) the keystone-2 endgame is exactly one bound:
```
EfoldTermAlpha α (blockPrimeInd N) X M D0 Dset e
    ≤ Kerr · (XM/(log XM)^{A+1}) · (1/e)               -- `efold_alpha_le`
```
under the `general_BV_final'` side-condition set plus the new threshold hypotheses.
`hPerE_reduces_to_alpha` + `efold_alpha_le` then fill the per-`e` slot of
`general_BV_final'`, yielding `general_BV_alpha_discharged`.

## The route (gate-verified, catch #44 v2)

* **Step 0 (identities, `D < N`).** Every large modulus `d ≤ D < N` is coprime to every
  block-prime `> N`, so `coprimeRestrict (blockPrimeInd N) d = blockPrimeInd N`
  (`coprimeRestrict_blockPrimeInd`); via `bilinTwist_coprimeRestrict_primitive` the
  imprimitive β-twist `B_d(χ)` **is already primitive** — `bilinTwist (blockPrimeInd N) M d χ
  = bilinTwist (blockPrimeInd N) M χ.conductor χ.primitiveCharacter`
  (`bilinTwist_blockPrimeInd_imprim_eq`).  Hence `EfoldTermAlpha` is a **primitive×primitive**
  energy sum (`EfoldTermAlpha_eq_prim`).  No `ω(d)` imprimitivity correction exists.

* **Step 1–4 (conductor regroup + density + two-regime energy).**  Per `d`, `regroup_bilin`
  bounds the χ-energy by the conductor block energy; the `e ∣ d` moduli are summed via the
  `(e,f)`-regrouped density.  The **small-conductor** half (`f ≤ D0`) closes for **all** `e`
  via `smallConductor_energy_le` at the dilated scale `(⌊X/e⌋, M)` — the `X/e` scale supplies
  the `1/e`.  The **large-conductor** half needs the `x^{−ε'}` level deficit and the density's
  `1/φ(e)`; see the FLAG below.

## What this file lands (all sorry-free, axiom-clean)

* `coprimeRestrict_blockPrimeInd`, `bilinTwist_blockPrimeInd_imprim_eq`,
  `EfoldTermAlpha_eq_prim` — Step 0 (the primitive×primitive collapse).
* `efold_alpha_reduce` — the crude conductor reduction (drops the `e∣d` decay).
* `efold_alpha_reduce_dense` — the **honest** `(e,f)`-density reduction (keeps `1/φ(lcm(e,f))`).
* `efold_small_le` — Step 2, the small-conductor block energy at the dilated scale.
* `efold_large_fourterm` — **PE3a**, the hDscale-free raw four-term at the dilated scale.
* `efold_alpha_le` — the two-regime assembly (small + large named, à la `bilinear_hLargeDisc`).
* `efold_small_discharge` — the small core `hsmall` **discharged for all `e`**
  (`Ksmall = 2^{A+5}·Kβ`; scale condition `log(XM) ≤ 2·log(⌊X/e⌋·M)`).
* `general_BV_alpha_discharged` — `general_BV_final'` with the per-`e` slot filled, reduced to
  the two dyadic-glue cores `hsmall` (discharged) and `hlarge` (flagged).

`Kerr = Ksmall + Klarge`, matching `general_BV_final'`'s consumer shape at exponent `A`.

## FLAG (Iron Rule 4 / STOP-AND-FLAG) — the large-conductor core `hlarge`

`efold_alpha_le` / `general_BV_alpha_discharged` take `hlarge` — the `f > D0` conductor
contribution — as a **named** hypothesis (exactly as the landed `bilinear_hLargeDisc` names
`hMainEnergy`/`hErrSum` and `general_BV_final` named `hPerE`).  It is **not** dischargeable
from the landed corpus, and the obstruction is a genuine Lean-level (and arguably
math-level) finding, gate-verified below:

**The numeric sanity pass (exponent bookkeeping).**  Operating point `XM ≍ x`,
`√(XM) ≍ x^{1/2}`, `D = x^{1/2−ε'}` (`ε' = 1e−4`), `2 ≤ e ≤ D`, `⌊X/e⌋·M ≍ x/e`.  PE3a's raw
four-term (`efold_large_fourterm`) has diagonal `~ D·√((X/e)M) = D·√(XM)/√e`.  Feeding it
through the density prefactor `4(1+log D)` and the target
`Kerr·XM/((log XM)^{A+1}·e)` needs the **level deficit** `D ≤ √(XM)/(log XM)^{2A+4}`:
* WITHOUT the density's `1/φ(e)` (i.e. bounding `4/φ(lcm(e,f)) ≤ 4/φ(f)`): main-LC decays only
  as `e^{−1/2}` (from the `√(X/e)` scale).  Ratio to target `~ √e/(log)^{A+1}`, which is
  `≥ x^{1/4−ε'}/(log)^{2A+5}` at `e ≍ D` — **diverges** (catch #44's middle band
  `e ∈ (x^{2ε'}, x^{1/4})`).
* WITH the density's `1/φ(e)`: main-LC `~ x^{1−ε'}/e^{3/2}`, ratio `~ x^{−ε'}(log)^{A+1}/√e → 0`
  at a threshold `x₀(ε',A)` — **closes** (the gate's route).

**Why the landed conductor-dyadic machinery cannot supply `e^{−3/2}`.**  The linear-`D`
diagonal (not `D²`) requires the `(1/φf)`-weighted dyadic-in-conductor sum
(`dyadic_large_reduction`: the `(1/φf) ≤ (1/2^k)(f/φf)` lift produces the `1/2^k` that
telescopes `2^K ≍ D`, not `4^K ≍ D²`).  The density is
`∑_{d ≤ D, lcm(e,f)∣d} 1/φd ≤ 4/φ(lcm(e,f)) = 4·φ(gcd(e,f))/(φe·φf)` (using the identity
`φ(lcm)·φ(gcd) = φe·φf`).  Extracting BOTH the `1/φ(e)` (for `e^{−3/2}`) AND the `1/φf` (for
linear `D`) needs `4/φ(lcm(e,f)) ≤ (C/φe)(1/φf)`, i.e. `φ(gcd(e,f)) ≤ C/4` uniformly — **false**
for `e ∣ f` (then `φ(lcm) = φf`, forcing `φe ≤ C/4`).  Any single bound loses one factor:
`≤ 4/φf` kills the e-decay (the `e^{−1/2}` failure above); `≤ (4/φe)(f/φf)` gives the shell's
`(f/φf)` weight, which has **no `1/2^k`** and yields the `4^K ≍ D²` diagonal disaster
(`~ √(XM)/(log)^{3A+5}·(1/√e) → ∞`).  The honest form
`(4(1+log D)/φe)·∑_f (φ(gcd(e,f))/φf)·E(f)` needs a **`δ`-restricted / gcd-weighted large-sieve
mean value** (`∑_{f ≤ Q, δ∣f} (f/φf)·bilinPrimEnergy ≤ [shell with the `Q²/δ` diagonal]`),
which is **not in the landed corpus** — it is the one genuinely missing analytic input.  This
is a re-instantiation gap the design's Step 4 did not anticipate; recorded as a finding, not a
failure (the envelope remains plausibly true; the gate verified the arithmetic, the Lean-level
tool is absent).

`efold_alpha_reduce_dense` lands the honest reduction *up to* this `∑_f φ(gcd(e,f))/φf·E(f)`
form, so `hlarge` is exactly one estimate away from closure.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset Salt.BV
open scoped BigOperators

/-! ## Step 0 — the primitive×primitive identities (`D < N`) -/

/-- **The coprime restriction of the block-prime indicator is itself (`d < N`).**  For a
modulus `d < N`, every block-prime `p > N` satisfies `p > d ≥ gcd(p,d)`, so (as `p` is prime)
`gcd(p, d) = 1`, i.e. `p` is a unit mod `d`; thus the coprime restriction drops nothing:
`coprimeRestrict (blockPrimeInd N) d = blockPrimeInd N`. -/
lemma coprimeRestrict_blockPrimeInd {N d : ℕ} [NeZero d] (hd : d < N) :
    coprimeRestrict (blockPrimeInd N) d = blockPrimeInd N := by
  funext m
  unfold coprimeRestrict
  by_cases hu : IsUnit ((m : ℕ) : ZMod d)
  · rw [if_pos hu]
  · rw [if_neg hu]
    symm
    unfold blockPrimeInd
    rw [if_neg]
    rintro ⟨hNm, hp⟩
    apply hu
    rw [ZMod.isUnit_iff_coprime]
    refine (hp.coprime_iff_not_dvd).mpr (fun hdvd => ?_)
    have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have : m ≤ d := Nat.le_of_dvd hdpos hdvd
    omega

/-- **The imprimitive β-twist is primitive (`d < N`).**  Combining the fold
`bilinTwist_coprimeRestrict_primitive` with `coprimeRestrict_blockPrimeInd`: the
imprimitive twist of `blockPrimeInd N` mod `d` equals its primitive twist at the
conductor. -/
lemma bilinTwist_blockPrimeInd_imprim_eq {N M d : ℕ} [NeZero d] (hd : d < N)
    (χ : DirichletCharacter ℂ d) :
    bilinTwist (blockPrimeInd N) M d χ
      = bilinTwist (blockPrimeInd N) M χ.conductor χ.primitiveCharacter := by
  rw [bilinTwist_coprimeRestrict_primitive (blockPrimeInd N) M χ,
    coprimeRestrict_blockPrimeInd hd]

open Classical in
/-- **Step 0 (FULL) — `EfoldTermAlpha` is a primitive×primitive energy.**  Under
`1 ≤ d ≤ D < N` on `Dset`, the imprimitive β-twist `B_d(χ)` collapses to the primitive
twist `B⋆(χ⋆)` (`bilinTwist_blockPrimeInd_imprim_eq`), so `EfoldTermAlpha` is exactly the
`(1/φd)`-weighted primitive-pair energy of the dilated `α^{(e)}` against `blockPrimeInd N`
over the `e ∣ d` moduli. -/
theorem EfoldTermAlpha_eq_prim (α : ℕ → ℂ) (N X M D0 D e : ℕ) (Dset : Finset ℕ)
    (hDsetD : ∀ d ∈ Dset, d ≤ D) (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDN : D < N) :
    EfoldTermAlpha α (blockPrimeInd N) X M D0 Dset e
      = ∑ d ∈ (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d),
          (1 / (d.totient : ℝ)) *
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
              (‖bilinTwist (fun m' => α (e * m')) (X / e) χ.conductor χ.primitiveCharacter‖
                * ‖bilinTwist (blockPrimeInd N) M χ.conductor χ.primitiveCharacter‖) := by
  unfold EfoldTermAlpha
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_filter, Finset.mem_filter] at hd
  have hd1 : 1 ≤ d := hDset1 d hd.1.1
  have hdD : d ≤ D := hDsetD d hd.1.1
  have hdN : d < N := by omega
  haveI : NeZero d := ⟨by omega⟩
  refine congrArg _ (Finset.sum_congr rfl (fun χ _ => ?_))
  rw [bilinTwist_blockPrimeInd_imprim_eq hdN χ]

/-! ## Step 1 — the crude conductor reduction (regroup + φ-swap, all `e`) -/

open Classical in
/-- **The crude conductor reduction (all `e`).**  After the primitive×primitive collapse
(`EfoldTermAlpha_eq_prim`), per `d` the χ-energy regroups by conductor (`regroup_bilin`)
onto the block energy `∑_{f ∣ d} bilinPrimEnergy`; extending the `e ∣ d` moduli to all
`d ≤ D` and φ-swapping (`swapPhi_generic`) folds the `d`-density into the `4(1+log D)`
prefactor:
```
EfoldTermAlpha α (blockPrimeInd N) X M D0 Dset e
    ≤ 4(1+log D) · ∑_{2≤f≤D} (1/φf) · bilinPrimEnergy α^{(e)} (blockPrimeInd N) (⌊X/e⌋) M f.
```
**Discards the `e ∣ d` restriction** (the extra `1/φ(e)` density decay) — sufficient for
the small-conductor half (the `1/e` there is carried by the dilated scale `⌊X/e⌋`), but not
for the large-conductor diagonal (see the FLAG). -/
theorem efold_alpha_reduce (α : ℕ → ℂ) (N X M D0 D e : ℕ) (Dset : Finset ℕ)
    (hD1 : 1 ≤ D) (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D) (hDN : D < N) :
    EfoldTermAlpha α (blockPrimeInd N) X M D0 Dset e
      ≤ 4 * (1 + Real.log D) *
          ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) *
            bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f := by
  classical
  rw [EfoldTermAlpha_eq_prim α N X M D0 D e Dset hDsetD hDset1 hDN]
  set a : ℕ → ℂ := fun m' => α (e * m') with ha
  set β : ℕ → ℂ := blockPrimeInd N with hβ
  set XX : ℕ := X / e with hXX
  set S := (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d) with hS
  have hsubset : S ⊆ Finset.Icc 1 D := by
    intro d hd
    rw [hS, Finset.mem_filter, Finset.mem_filter] at hd
    rw [Finset.mem_Icc]
    exact ⟨hDset1 d hd.1.1, hDsetD d hd.1.1⟩
  calc ∑ d ∈ S, (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (‖bilinTwist a XX χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β M χ.conductor χ.primitiveCharacter‖)
      ≤ ∑ d ∈ S, (1 / (d.totient : ℝ)) *
          ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), bilinPrimEnergy a β XX M f := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [hS, Finset.mem_filter, Finset.mem_filter] at hd
        have hdD : d ≤ D := hDsetD d hd.1.1
        haveI : NeZero d := ⟨by have := hDset1 d hd.1.1; omega⟩
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Eq.trans_le ?_ (regroup_bilin hdD a β XX M)
        exact Finset.sum_congr
          (congrArg (fun i => @Finset.erase (DirichletCharacter ℂ d) i Finset.univ 1)
            (Subsingleton.elim _ _)) (fun _ _ => rfl)
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (1 / (d.totient : ℝ)) *
          ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), bilinPrimEnergy a β XX M f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => ?_)
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg (fun f _ => bilinPrimEnergy_nonneg _ _ _ _ _))
    _ ≤ 4 * (1 + Real.log D) *
          ∑ f ∈ Finset.Icc 2 D, (1 / (f.totient : ℝ)) * bilinPrimEnergy a β XX M f :=
        swapPhi_generic hD1 (bilinPrimEnergy a β XX M) (bilinPrimEnergy_nonneg a β XX M)

open Classical in
/-- **The honest `(e,f)`-density reduction (keeps the `e ∣ d` restriction).**  Same
regroup+swap as `efold_alpha_reduce`, but the `e ∣ d` moduli are *kept*: the per-`f` density
`∑_{d ≤ D, e∣d, f∣d} 1/φd = ∑_{d ≤ D, lcm(e,f)∣d} 1/φd ≤ (4/φ(lcm(e,f)))·(1+log D)`
(`sum_inv_totient_dvd_le'` at modulus `lcm(e,f)`) carries the **extra `1/φ(e)` e-decay**:
```
EfoldTermAlpha α (blockPrimeInd N) X M D0 Dset e
    ≤ ∑_{2≤f≤D} (4/φ(lcm(e,f)))·(1+log D) · bilinPrimEnergy α^{(e)} (blockPrimeInd N) (⌊X/e⌋) M f.
```
This is the honest form the large-conductor assembly must consume (see the FLAG). -/
theorem efold_alpha_reduce_dense (α : ℕ → ℂ) (N X M D0 D e : ℕ) (Dset : Finset ℕ)
    (hD1 : 1 ≤ D) (he1 : 1 ≤ e) (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hDN : D < N) :
    EfoldTermAlpha α (blockPrimeInd N) X M D0 Dset e
      ≤ ∑ f ∈ Finset.Icc 2 D,
          ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
            * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f := by
  classical
  rw [EfoldTermAlpha_eq_prim α N X M D0 D e Dset hDsetD hDset1 hDN]
  set a : ℕ → ℂ := fun m' => α (e * m') with ha
  set β : ℕ → ℂ := blockPrimeInd N with hβ
  set XX : ℕ := X / e with hXX
  set S := (Dset.filter (fun d => ¬ d ≤ D0)).filter (fun d => e ∣ d) with hS
  set G := (Finset.Icc 1 D).filter (fun d => e ∣ d) with hG
  have hsubset : S ⊆ G := by
    intro d hd
    rw [hS, Finset.mem_filter, Finset.mem_filter] at hd
    rw [hG, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hDset1 d hd.1.1, hDsetD d hd.1.1⟩, hd.2⟩
  calc ∑ d ∈ S, (1 / (d.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (‖bilinTwist a XX χ.conductor χ.primitiveCharacter‖
              * ‖bilinTwist β M χ.conductor χ.primitiveCharacter‖)
      ≤ ∑ d ∈ S, (1 / (d.totient : ℝ)) *
          ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), bilinPrimEnergy a β XX M f := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [hS, Finset.mem_filter, Finset.mem_filter] at hd
        have hdD : d ≤ D := hDsetD d hd.1.1
        haveI : NeZero d := ⟨by have := hDset1 d hd.1.1; omega⟩
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Eq.trans_le ?_ (regroup_bilin hdD a β XX M)
        exact Finset.sum_congr
          (congrArg (fun i => @Finset.erase (DirichletCharacter ℂ d) i Finset.univ 1)
            (Subsingleton.elim _ _)) (fun _ _ => rfl)
    _ ≤ ∑ d ∈ G, (1 / (d.totient : ℝ)) *
          ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d), bilinPrimEnergy a β XX M f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => ?_)
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg (fun f _ => bilinPrimEnergy_nonneg _ _ _ _ _))
    _ = ∑ d ∈ G, ∑ f ∈ (Finset.Icc 2 D).filter (· ∣ d),
          (1 / (d.totient : ℝ)) * bilinPrimEnergy a β XX M f := by
        refine Finset.sum_congr rfl (fun d _ => ?_); rw [Finset.mul_sum]
    _ = ∑ f ∈ Finset.Icc 2 D, ∑ d ∈ G.filter (fun d => f ∣ d),
          (1 / (d.totient : ℝ)) * bilinPrimEnergy a β XX M f := by
        refine Finset.sum_comm' ?_
        intro d f
        simp only [hG, Finset.mem_filter, Finset.mem_Icc]; tauto
    _ = ∑ f ∈ Finset.Icc 2 D,
          (∑ d ∈ G.filter (fun d => f ∣ d), (1 / (d.totient : ℝ)))
            * bilinPrimEnergy a β XX M f := by
        refine Finset.sum_congr rfl (fun f _ => ?_); rw [Finset.sum_mul]
    _ ≤ ∑ f ∈ Finset.Icc 2 D,
          ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * bilinPrimEnergy a β XX M f := by
        refine Finset.sum_le_sum (fun f hf => ?_)
        rw [Finset.mem_Icc] at hf
        refine mul_le_mul_of_nonneg_right ?_ (bilinPrimEnergy_nonneg _ _ _ _ _)
        have hlcm1 : 1 ≤ Nat.lcm e f := by
          have : Nat.lcm e f ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
          omega
        have hfilter : G.filter (fun d => f ∣ d)
            = (Finset.Icc 1 D).filter (fun d => Nat.lcm e f ∣ d) := by
          rw [hG, Finset.filter_filter]
          refine Finset.filter_congr (fun d _ => ?_)
          rw [Nat.lcm_dvd_iff]
        rw [hfilter]
        exact Salt.LS.sum_inv_totient_dvd_le' hlcm1 hD1

/-! ## Step 2 — the small-conductor half (all `e`, no level hypothesis) -/

/-- The dilated coefficient `α^{(e)}(m') = α(e·m')` inherits the `‖·‖ ≤ 1` bound. -/
lemma norm_dilate_le {α : ℕ → ℂ} (hα : ∀ m, ‖α m‖ ≤ 1) (e : ℕ) :
    ∀ m', ‖(fun m' => α (e * m')) m'‖ ≤ 1 := fun m' => hα (e * m')

open Classical in
/-- **Step 2 (FULL) — the small-conductor block energy at the dilated scale.**  A direct
instance of `smallConductor_energy_le` for `α^{(e)}` against `blockPrimeInd N` at the
**dilated scale** `(⌊X/e⌋, M)`.  The β-twist `bilinTwist (blockPrimeInd N) M f ψ` is
*unchanged* by the dilation (it lives on the second factor `M`), so its SW-regularity is
exactly the landed `hβSW` shape; only the α-side moves to scale `⌊X/e⌋`.  The output carries
the `⌊X/e⌋·M` scale — which is where the `1/e` of the per-`e` bound comes from — and holds
for **every** `e` (no level cut needed in the small regime). -/
theorem efold_small_le (α : ℕ → ℂ) (N X M D0 e : ℕ) {A C0 Kβ : ℝ}
    (hα : ∀ m, ‖α m‖ ≤ 1) (hKβ : 0 ≤ Kβ)
    (hLpos : 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)))
    (hD0 : (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0)
    (hβSW : ∀ f : ℕ, 2 ≤ f → f ≤ D0 → ∀ ψ : DirichletCharacter ℂ f, ψ ≠ 1 →
        ‖bilinTwist (blockPrimeInd N) M f ψ‖
          ≤ Kβ * (M : ℝ) / (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ (A + C0)) :
    ∑ f ∈ Finset.Icc 2 D0,
        (1 / (f.totient : ℝ)) *
          bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
      ≤ Kβ * (((X / e : ℕ) : ℝ) * (M : ℝ))
          / (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ A :=
  smallConductor_energy_le (fun m' => α (e * m')) (blockPrimeInd N)
    (norm_dilate_le hα e) hKβ hLpos hD0 hβSW

/-! ## Step 3 (PE3a) — the raw four-term at the dilated scale (no level absorption) -/

open Classical in
/-- **PE3a (FULL) — the hDscale-free four-term at the dilated scale `(⌊X/e⌋, M)`.**  The
large-conductor block energy `∑_{D0 < f ≤ D} (1/φf)·bilinPrimEnergy` is bounded by the
explicit dyadic **four-term** expression (`dyadic_large_reduction` + `geom_shell_sum_le` at
scale `(⌊X/e⌋, M)`), with the diagonal `4·2^{K+1}` term **kept explicit and rational** — no
level cut `D ≤ √((X/e)M)/(log)^B` is absorbed (catch #44: that cut fails for the middle band
of `e`).  This is the raw mean value the assembly consumes; the level deficit is applied to
its diagonal *afterwards*, per `e`. -/
theorem efold_large_fourterm (α : ℕ → ℂ) (N X M D0 D k0 K e : ℕ)
    (hD0 : D0 = 2 ^ k0) (hK : K = Nat.log 2 D) (hM : 0 < M) (hα : ∀ m, ‖α m‖ ≤ 1) :
    ∑ f ∈ Finset.Icc (D0 + 1) D,
        (1 / (f.totient : ℝ)) *
          bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
      ≤ (2 * (1 + Real.log M) * Real.sqrt ((X / e : ℕ)) * Real.sqrt M)
          * (4 * (2 : ℝ) ^ (K + 1)
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * (((X / e : ℕ) : ℝ) + 1))
            + 2 * ((K + 1 : ℕ) : ℝ) * Real.sqrt (13 * ((M : ℝ) + 1))
            + Real.sqrt (13 * (((X / e : ℕ) : ℝ) + 1)) * Real.sqrt (13 * ((M : ℝ) + 1))
                * (2 / (2 : ℝ) ^ k0)) := by
  have hβ : ∀ n, ‖blockPrimeInd N n‖ ≤ 1 := by
    intro n; unfold blockPrimeInd
    by_cases h : N < n ∧ n.Prime
    · rw [if_pos h, norm_one]
    · rw [if_neg h, norm_zero]; norm_num
  exact le_trans
    (dyadic_large_reduction hD0 hK hM (fun m' => α (e * m')) (blockPrimeInd N)
      (norm_dilate_le hα e) hβ)
    (geom_shell_sum_le hM)

/-! ## Step 4 — the two-regime assembly (small discharged + large named) -/

open Classical in
/-- **PE3 (the α-side per-`e` bound) — the two-regime assembly.**  Composes the honest
`(e,f)`-density reduction (`efold_alpha_reduce_dense`) with the conductor split at `D0` into
the **small** (`f ≤ D0`) and **large** (`f > D0`) contributions, each supplied in the target
envelope shape `K·(XM/(log XM)^{A+1})·(1/e)`.  Mirrors `bilinear_hLargeDisc`'s named-core
pattern (`hMainEnergy`/`hErrSum`): the two dyadic-glue inputs are named, their sum is the
per-`e` slot of `general_BV_final'`.

* `hsmall` is **dischargeable for all `e`** (`efold_small_le` at the dilated scale `(⌊X/e⌋,M)`
  + the mild scale condition `log(XM) ≤ 2·log(⌊X/e⌋·M)`; the `1/e` is carried by `⌊X/e⌋`);
  see `efold_small_discharge`.
* `hlarge` is the genuine large-conductor core — the raw four-term (`efold_large_fourterm`)
  diagonal `D·√((X/e)M)` closes only with the density's `1/φ(e)` **and** the level deficit
  simultaneously; those two conflict in the landed conductor-dyadic machinery (see the FLAG).
-/
theorem efold_alpha_le (α : ℕ → ℂ) (N X M D0 D e : ℕ) (Dset : Finset ℕ) {A Ksmall Klarge : ℝ}
    (hD1 : 1 ≤ D) (he1 : 1 ≤ e) (hDset1 : ∀ d ∈ Dset, 1 ≤ d) (hDsetD : ∀ d ∈ Dset, d ≤ D)
    (hDN : D < N) (h2D0 : 2 ≤ D0) (hD0D : D0 ≤ D)
    (hsmall : ∑ f ∈ Finset.Icc 2 D0,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
      ≤ Ksmall * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)))
    (hlarge : ∑ f ∈ Finset.Icc (D0 + 1) D,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
      ≤ Klarge * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ))) :
    EfoldTermAlpha α (blockPrimeInd N) X M D0 Dset e
      ≤ (Ksmall + Klarge)
          * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) := by
  refine le_trans (efold_alpha_reduce_dense α N X M D0 D e Dset hD1 he1 hDset1 hDsetD hDN) ?_
  set g : ℕ → ℝ := fun f => ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
    * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f with hg
  have hsplit : ∑ f ∈ Finset.Icc 2 D, g f
      = ∑ f ∈ Finset.Icc 2 D0, g f + ∑ f ∈ Finset.Icc (D0 + 1) D, g f := by
    rw [show Finset.Icc 2 D = Finset.Ioc 1 D by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega,
        show Finset.Icc 2 D0 = Finset.Ioc 1 D0 by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega,
        show Finset.Icc (D0 + 1) D = Finset.Ioc D0 D by
          ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
    exact (Finset.sum_Ioc_consecutive g (by omega : 1 ≤ D0) hD0D).symm
  rw [hsplit]
  calc ∑ f ∈ Finset.Icc 2 D0, g f + ∑ f ∈ Finset.Icc (D0 + 1) D, g f
      ≤ Ksmall * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ))
        + Klarge * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) :=
        add_le_add hsmall hlarge
    _ = (Ksmall + Klarge)
          * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) := by
        ring

open Classical in
/-- **The small-conductor core, discharged (all `e`).**  Proves `efold_alpha_le`'s `hsmall`
hypothesis from `efold_small_le` (at the raised exponent `A+2`, dilated scale `(⌊X/e⌋,M)`) and
the mild scale condition `log(XM) ≤ 2·log(⌊X/e⌋·M)`.  Mechanism: `4/φ(lcm(e,f)) ≤ 4/φ(f)`
(as `f ∣ lcm(e,f)`) folds the density into the `4(1+log D)` prefactor; `efold_small_le`
contracts the block energy to `Kβ·(⌊X/e⌋·M)/log(⌊X/e⌋M)^{A+2}`; and `⌊X/e⌋·M ≤ XM/e`,
`1+log D ≤ 2·log(XM)`, `log(⌊X/e⌋M) ≥ (1/2)log(XM)` deliver the target envelope with
`Ksmall = 2^{A+5}·Kβ`.  **No level cut** — closes for every `e`.  This is the concrete
discharge behind `efold_alpha_le`'s `hsmall` slot (see the FLAG: the analogous `hlarge` slot
has no such landed discharge). -/
theorem efold_small_discharge (α : ℕ → ℂ) (N X M D0 D e : ℕ) {A C0 Kβ : ℝ}
    (hA : 0 ≤ A) (he1 : 1 ≤ e) (hα : ∀ m, ‖α m‖ ≤ 1) (hKβ : 0 ≤ Kβ) (hD1 : 1 ≤ D)
    (hLEpos : 0 < Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)))
    (hD0E : (D0 : ℝ) ≤ (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ C0)
    (hβSW : ∀ f : ℕ, 2 ≤ f → f ≤ D0 → ∀ ψ : DirichletCharacter ℂ f, ψ ≠ 1 →
        ‖bilinTwist (blockPrimeInd N) M f ψ‖
          ≤ Kβ * (M : ℝ) / (Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) ^ ((A + 2) + C0))
    (hL1 : 1 ≤ Real.log ((X : ℝ) * (M : ℝ)))
    (hDXM : (D : ℝ) ≤ (X : ℝ) * (M : ℝ))
    (hscale : Real.log ((X : ℝ) * (M : ℝ))
        ≤ 2 * Real.log (((X / e : ℕ) : ℝ) * (M : ℝ))) :
    ∑ f ∈ Finset.Icc 2 D0,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
          * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
      ≤ ((2 : ℝ) ^ (A + 5) * Kβ)
          * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1)) * (1 / (e : ℝ)) := by
  set L := Real.log ((X : ℝ) * (M : ℝ)) with hLdef
  set LE := Real.log (((X / e : ℕ) : ℝ) * (M : ℝ)) with hLEdef
  have hLpos : 0 < L := by linarith
  set xe : ℝ := ((X / e : ℕ) : ℝ) with hxe
  set E : ℕ → ℝ := fun f =>
    bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f with hEdef
  have h1logD : (0 : ℝ) ≤ 1 + Real.log D :=
    by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (D : ℝ) by exact_mod_cast hD1)]
  -- Step 1: fold `4/φ(lcm(e,f)) ≤ 4/φf` into the `4(1+log D)` prefactor.
  have hstep1 : ∑ f ∈ Finset.Icc 2 D0,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * E f
      ≤ 4 * (1 + Real.log D) * ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * E f := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun f hf => ?_)
    rw [Finset.mem_Icc] at hf
    have hφf : (0 : ℝ) < (f.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < f)
    have hlcmpos : 0 < Nat.lcm e f := by
      have : Nat.lcm e f ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
      omega
    have hφle : (f.totient : ℝ) ≤ ((Nat.lcm e f).totient : ℝ) := by
      have h : f.totient ∣ (Nat.lcm e f).totient :=
        Nat.totient_dvd_of_dvd (Nat.dvd_lcm_right e f)
      exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hlcmpos) h
    have hdiv : (4 : ℝ) / ((Nat.lcm e f).totient : ℝ) ≤ 4 / (f.totient : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hφf hφle
    have hEf : 0 ≤ E f := bilinPrimEnergy_nonneg _ _ _ _ _
    calc ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * E f
        ≤ ((4 / (f.totient : ℝ)) * (1 + Real.log D)) * E f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiv h1logD) hEf
      _ = 4 * (1 + Real.log D) * ((1 / (f.totient : ℝ)) * E f) := by ring
  -- Step 2: `efold_small_le` at exponent `A+2`.
  have hstep2 : ∑ f ∈ Finset.Icc 2 D0, (1 / (f.totient : ℝ)) * E f
      ≤ Kβ * (xe * (M : ℝ)) / LE ^ (A + 2) :=
    efold_small_le α N X M D0 e (A := A + 2) (C0 := C0) (Kβ := Kβ) hα hKβ hLEpos hD0E hβSW
  have h4logD : (0 : ℝ) ≤ 4 * (1 + Real.log D) := by positivity
  have hcombine : ∑ f ∈ Finset.Icc 2 D0,
        ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D)) * E f
      ≤ 4 * (1 + Real.log D) * (Kβ * (xe * (M : ℝ)) / LE ^ (A + 2)) :=
    le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 h4logD)
  refine le_trans hcombine ?_
  -- Step 4: scale conversion.
  have hLEpow : (0 : ℝ) < LE ^ (A + 2) := Real.rpow_pos_of_pos hLEpos (A + 2)
  have hLpow1 : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos (A + 1)
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hxeM : xe * (M : ℝ) ≤ (X : ℝ) * (M : ℝ) / (e : ℝ) := by
    have h1 : xe ≤ (X : ℝ) / (e : ℝ) := Nat.cast_div_le
    calc xe * (M : ℝ) ≤ ((X : ℝ) / (e : ℝ)) * (M : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hMnn
      _ = (X : ℝ) * (M : ℝ) / (e : ℝ) := by ring
  have hlogDL : Real.log D ≤ L :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < D)) hDXM
  have h1logD2L : 1 + Real.log D ≤ 2 * L := by linarith
  -- rpow bookkeeping
  have hrp1 : L * L ^ (A + 1) = L ^ (A + 2) := by
    have hh := Real.rpow_add hLpos 1 (A + 1)
    rw [Real.rpow_one] at hh
    rw [← hh]; congr 1; ring
  have hrp2 : (L / 2) ^ (A + 2) = L ^ (A + 2) / (2 : ℝ) ^ (A + 2) :=
    Real.div_rpow hLpos.le (by norm_num) (A + 2)
  have hrp3 : (2 : ℝ) ^ (A + 5) = (2 : ℝ) ^ (A + 2) * 8 := by
    rw [show (A : ℝ) + 5 = (A + 2) + 3 by ring, Real.rpow_add (by norm_num), show (3:ℝ) =
      ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ (A + 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hLElo : (L / 2) ^ (A + 2) ≤ LE ^ (A + 2) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hXMnn : (0 : ℝ) ≤ (X : ℝ) * (M : ℝ) := by positivity
  have hpowdiv : (2 : ℝ) ^ (A + 5) / (2 : ℝ) ^ (A + 2) = 8 := by
    rw [hrp3, mul_comm, mul_div_assoc, div_self h2pow.ne']; ring
  -- rewrite both sides into single fractions and cross-multiply
  have hLHSeq : 4 * (1 + Real.log D) * (Kβ * (xe * (M : ℝ)) / LE ^ (A + 2))
      = (4 * (1 + Real.log D) * Kβ * (xe * (M : ℝ))) / LE ^ (A + 2) := by ring
  have hRHSeq : ((2 : ℝ) ^ (A + 5) * Kβ) * ((X : ℝ) * (M : ℝ) / L ^ (A + 1)) * (1 / (e : ℝ))
      = ((2 : ℝ) ^ (A + 5) * Kβ * ((X : ℝ) * (M : ℝ))) / (L ^ (A + 1) * (e : ℝ)) := by ring
  rw [hLHSeq, hRHSeq, div_le_div_iff₀ hLEpow (by positivity : (0:ℝ) < L ^ (A + 1) * (e : ℝ))]
  -- goal: (4(1+logD)*Kβ*(xe*M))*(L^(A+1)*e) ≤ (2^(A+5)*Kβ*(XM))*LE^(A+2)
  have hxeMe : (xe * (M : ℝ)) * (e : ℝ) ≤ (X : ℝ) * (M : ℝ) := by
    have := mul_le_mul_of_nonneg_right hxeM heR.le
    rwa [div_mul_cancel₀ _ heR.ne'] at this
  have key : (4 * (1 + Real.log D) * Kβ * (xe * (M : ℝ))) * (L ^ (A + 1) * (e : ℝ))
      ≤ 8 * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 2) := by
    calc (4 * (1 + Real.log D) * Kβ * (xe * (M : ℝ))) * (L ^ (A + 1) * (e : ℝ))
        = (4 * (1 + Real.log D)) * (Kβ * ((xe * (M : ℝ)) * (e : ℝ))) * L ^ (A + 1) := by ring
      _ ≤ (8 * L) * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hLpow1.le
          refine mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hxeMe hKβ)
            (mul_nonneg hKβ (by positivity)) (by positivity)
      _ = 8 * (Kβ * ((X : ℝ) * (M : ℝ))) * (L * L ^ (A + 1)) := by ring
      _ = 8 * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 2) := by rw [hrp1]
  refine le_trans key ?_
  have hle : 8 * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 2)
      = ((2 : ℝ) ^ (A + 5) * Kβ * ((X : ℝ) * (M : ℝ))) * (L / 2) ^ (A + 2) := by
    rw [hrp2]
    rw [show ((2 : ℝ) ^ (A + 5) * Kβ * ((X : ℝ) * (M : ℝ))) * (L ^ (A + 2) / (2 : ℝ) ^ (A + 2))
          = ((2 : ℝ) ^ (A + 5) / (2 : ℝ) ^ (A + 2)) * (Kβ * ((X : ℝ) * (M : ℝ))) * L ^ (A + 2)
        by ring, hpowdiv]
  rw [hle]
  exact mul_le_mul_of_nonneg_left hLElo
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKβ) hXMnn)

/-! ## Step 5 — the per-`e` slot of `general_BV_final'`, filled -/

open Classical in
/-- **PE3 — `general_BV_final'` with the per-`e` slot discharged to the two α-side cores.**
`general_BV_final'` (PE1) has its per-`e` obligation reduced to the α-side alone by
`hPerE_reduces_to_alpha` (PE2: the β-side is `0` under `D < N`); `efold_alpha_le` (PE3)
supplies that α-side bound from the small/large conductor cores.  So the general bilinear-BV
`L¹`-over-`d` AP-discrepancy for the interval prime indicator is bounded with **no per-`e`
slot remaining** — only the two named dyadic-glue cores `hsmall` (dischargeable, all `e`) and
`hlarge` (the flagged large-conductor estimate). -/
theorem general_BV_alpha_discharged {A C0 : ℝ} (hA : 0 < A) (hC0 : 0 < C0) :
    ∃ (K : ℝ) (N₀ : ℕ), 0 < K ∧
      ∀ (α : ℕ → ℂ) (X N M R₀ D0 D : ℕ) (Dset : Finset ℕ) (Kβ Kmain Ksmall Klarge : ℝ),
        (∀ m, ‖α m‖ ≤ 1) → 0 ≤ Kβ → 3 ≤ N → N₀ ≤ N → N ≤ M → M ≤ 2 * N →
        (∀ d ∈ Dset, 1 ≤ d) → (∀ d ∈ Dset, Nat.Coprime R₀ d) →
        (0 < Real.log ((X : ℝ) * (M : ℝ))) →
        ((D0 : ℝ) ≤ (Real.log ((X : ℝ) * (M : ℝ))) ^ C0) →
        ((D0 : ℝ) ≤ (Real.log N) ^ C0) →
        (K * (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 2 * C0)
            ≤ Kβ * (Real.log N) ^ (A + 2 * C0)) →
        1 ≤ D → (∀ d ∈ Dset, d ≤ D) → D < N → 2 ≤ D0 → D0 ≤ D →
        0 ≤ Ksmall → 0 ≤ Klarge → (1 : ℝ) ≤ (X : ℝ) * (M : ℝ) →
        (4 * (1 + Real.log D) *
            ∑ f ∈ Finset.Icc 2 D,
              (1 / (f.totient : ℝ)) * bilinPrimEnergy α (blockPrimeInd N) X M f
          ≤ Kmain * ((X : ℝ) * (M : ℝ)) / (Real.log ((X : ℝ) * (M : ℝ))) ^ A) →
        (∀ e, 2 ≤ e → e ≤ D →
            ∑ f ∈ Finset.Icc 2 D0,
                ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
                  * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
              ≤ Ksmall * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1))
                  * (1 / (e : ℝ))) →
        (∀ e, 2 ≤ e → e ≤ D →
            ∑ f ∈ Finset.Icc (D0 + 1) D,
                ((4 / ((Nat.lcm e f).totient : ℝ)) * (1 + Real.log D))
                  * bilinPrimEnergy (fun m' => α (e * m')) (blockPrimeInd N) (X / e) M f
              ≤ Klarge * ((X : ℝ) * (M : ℝ) / (Real.log ((X : ℝ) * (M : ℝ))) ^ (A + 1))
                  * (1 / (e : ℝ))) →
        ∑ d ∈ Dset, ‖apDiscBilin α (blockPrimeInd N) X M R₀ d‖
          ≤ (Kβ + (Kmain + (Ksmall + Klarge))) * ((X : ℝ) * (M : ℝ))
              / (Real.log ((X : ℝ) * (M : ℝ))) ^ A := by
  obtain ⟨K, N₀, hK0, hbody⟩ := general_BV_final' (A := A) (C0 := C0) hA hC0
  refine ⟨K, N₀, hK0, fun α X N M R₀ D0 D Dset Kβ Kmain Ksmall Klarge hα hKβ hN3 hN hNM hM2N
    hDge1 hcop hLpos hD0 hD0N hscale hD1 hDsetD hDN h2D0 hD0D hKs hKl hXM1 hMainEnergy
    hsmall hlarge => ?_⟩
  refine hbody α X N M R₀ D0 D Dset Kβ Kmain (Ksmall + Klarge) hα hKβ hN3 hN hNM hM2N hDge1 hcop
    hLpos hD0 hD0N hscale hD1 hDsetD hDN (by linarith) hXM1 hMainEnergy ?_
  intro e he2 heD
  rw [hPerE_reduces_to_alpha α N X M D0 D e Dset he2 heD hDN]
  exact efold_alpha_le α N X M D0 D e Dset hD1 (by omega) hDge1 hDsetD hDN h2D0 hD0D
    (hsmall e he2 heD) (hlarge e he2 heD)

end Salt.Chen
