/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TLegPreamble

/-!
# TLegE1 — MR §8.1, the level-1 graded `𝒯`-leg (ROUTE G, stone G3)

`docs/exploration/hsup-design.md` ⟦V6⟧'s Route-G ladder, node `G3`: the FIRST of the two
`𝒯`-leg pages, on top of `G2` (`Salt.MR.TLegPreamble`).  Everything here is **parallel and
additive**: no landed statement is touched.

MR §8.1 (p.25) prices the level-1 piece of eq (24),

  `E₁ := ∫_{A₁} |F(1+it)|² dt`,  `A₁ := (Ann ∖ ball) ∩ 𝒯₁`,

by the mean-value theorem alone — no power-raising, no Lemma 13 (those are §8.2, node `G4`).
The whole content is a COMPOSITION of stones that `G2` already landed; this file performs it
and states the exit honestly.

## The route (four steps, each a landed stone)

1. **Lemma 12 on `A₁`** (`TLegPreamble.lemma12_on_TsetG`): the mean square splits as
   `2|I₁|·Σ_{v∈I₁} ∫_{A₁}‖Q_{v,H₁}·R_{v,H₁}‖² + E`, with `E` the three full-range error rows.
2. **The graded pointwise gain** (`TLegPreamble.ramQ_sq_le_of_blockSmallG`): on `𝒯₁` the
   block polynomial obeys MR (21), `‖Q_{v,H₁}(1+it)‖² ≤ e^{−2α₁v/H₁}`, for EVERY `v ∈ I₁` —
   so the `v`-dependent threshold pulls straight out of the integral
   (`norm_ramMain_sq_le_of_mem_TsetG`).
3. **The sharp-length co-factor MVT** (`TLegPreamble.cofactor_mvt_sharp_exit_visible`):
   `∫_{−T}^{T}‖R_{v,H₁}‖² ≤ 4T·e^{v/H₁}/X_d + 120`, the absolute `120` being exactly what
   ⟦V4a⟧'s sharp-`M` law buys.  The transfer `∫_{A₁} ≤ ∫_{−T}^{T}` is the nonnegative-
   integrand monotonicity through `A₁ ⊆ [−T,T]`.
4. **The two geometric `v`-sums** (`TLegPreamble.sum_exp_growth_top`,
   `sum_exp_neg_graded_rate`, `sum_exp_neg_graded_card`).  The product of steps 2 and 3
   splits into TWO legs of opposite sign:

   * the `T`-leg carries `e^{−2α₁v/H₁}·e^{v/H₁} = e^{(1−2α₁)v/H₁}` — **the GROWING leg**,
     summed by `sum_exp_growth_top` at `(H₁/(1−2α₁))·e^{(1−2α₁)/H₁}·Q₁^{1−2α₁}` under the
     in-statement gate `2α₁ < 1`;
   * the absolute `120` rides `e^{−2α₁v/H₁}` — **the DECAYING leg**, where the consumer takes
     the `min` of the rate form `(H₁/2α₁)·e^{−2α₁(v₀−1)/H₁}` and the crude
     `|I₁|·e^{−2α₁v₀/H₁}` (both are stated at `G2` precisely so the min is available).

## The stones

* **G3a — `E1_bound`** (with the generic-`A` workhorses
  `norm_ramMain_sq_le_of_mem_TsetG`, `integral_ramMain_sq_le_of_subset_TsetG`,
  `sum_integral_ramMain_sq_le_of_subset_TsetG`).  The assembled level-1 page, exit form

  `∫_{A₁}‖F‖² ≤ 2|I₁|·( (4T/X_d)·(H₁/(1−2α₁))·e^{(1−2α₁)/H₁}·Q₁^{1−2α₁}
                        + 120·min{(H₁/2α₁)·e^{−2α₁(v₀−1)/H₁}, |I₁|·e^{−2α₁v₀/H₁}} ) + E`,

  `v₀ = ⌊H₁ log P₁⌋`, `E` the verbatim three-row Lemma 12 error.  Nothing is absorbed into a
  numeral (law #253): `T`, `N`, `X_d`, `H₁`, `α₁`, `P₁`, `Q₁`, `|I₁|` all ride the statement.

* **G3b — `E1_pin`.**  The same page at the block bottom `v₀` and MR's normalization
  `T/(X_d/Q₁) = T·Q₁/X_d`:

  `∫_{A₁}‖F‖² ≤ 2(H₁ log Q₁ + 1)·(T·Q₁/X_d + 1)·P₁^{−2α₁}
                  ·( 4(H₁/(1−2α₁))e^{(1−2α₁)/H₁} + 60(H₁/α₁)e^{4α₁/H₁} ) + E`.

  Two conversions and nothing else: `Q₁^{1−2α₁} = Q₁·Q₁^{−2α₁} ≤ Q₁·P₁^{−2α₁}` (the base
  comparison `P₁ ≤ Q₁` at a NEGATIVE exponent — this is what turns the growing leg into MR's
  `(T/(X/Q₁))·P₁^{−2α₁}` shape), and `e^{−2α₁(v₀−1)/H₁} ≤ e^{4α₁/H₁}·P₁^{−2α₁}` from
  `H₁ log P₁ < v₀ + 1`.  `|I₁| ≤ H₁ log Q₁ + 1` is `USetPrice.ramI_card_le`.

## The honest exponent (G3b's verdict — recorded, NOT pinned)

`E1_pin`'s shape is `H₁²·log Q₁·P₁^{−2α₁}·(T/(X/Q₁)+1)`: the two `H₁` come from the block
count `|I₁| ≈ H₁ log Q₁` and from the geometric `v`-sums' own `H₁/(1−2α₁)`, `H₁/(2α₁)`.
At MR's own pins (p.24: `H_j = j²·P₁^{1/6−η}/(log Q₁)^{1/3}`, eq (20): `α_j = 1/4 − η(1+1/(2j))`,
so `2α₁ = 1/2 − 3η`) the arithmetic is

  `H₁²·log Q₁·P₁^{−2α₁} = P₁^{1/3−2η}(log Q₁)^{−2/3}·log Q₁·P₁^{−1/2+3η}
                        = P₁^{−1/6+η}(log Q₁)^{1/3} = (log Q₁)^{1/3}/P₁^{1/6−η}`,

which is **exactly** MR's stated §8.1 bound `E₁ ≪ (T/(X/Q₁)+1)(log Q₁)^{1/3}/P₁^{1/6−η}`
(`docs/sources/mr_extract.md` §2.7).  So the honest composed exponent MATCHES the source at
their `α₁`; the `−1/2+3η` of `P₁^{−2α₁}` is consumed by the `H₁²·log Q₁` block factor, not
lost.  The α-sequence numerals themselves belong to `G4f`/`G5` — `α₁` is carried here only
through its two gates (`0 < α₁` on the decaying leg, `2α₁ < 1` on the growing leg).

## Conventions and pins (law #253, byte-checked)

* **The coefficient seam (a composition finding).**  Lemma 12's block factor is `ramQ … c`
  with `c` the Ramaré prime coefficient, while `G0`'s graded set is `TsetG f …` with `f` its
  own datum.  The graded gain bites only when **`f = c`**, which is MR's own convention
  (`c p = f p` in the Ramaré factorization `a(pm) = b(m)c(p)`).  Every statement here
  therefore instantiates the set at `c` itself — the seam is closed in the statement, not
  left to the consumer.
* **No negation.**  `G0`/`G1a`/`G2`'s posture is kept: every `t` is the ordinate the seam row
  integrates over; no `dpoly`, no `Finset.image (−·)`, no `−𝒯` bridge appears.
* **`M` vs `Ms`.**  The co-factor length `Ms` (`exists_sharp_length`, `2X_v ≤ Ms ≤ 3X_v`) is
  produced INSIDE the per-`v` step and never identified with the row's `N` — `G2` banked that
  as a standing warning and it is honoured here (the two are different roundings).
* **The sharp-length window** is carried as the gate `1 ≤ ramRbot H₁ X_d v` for `v ∈ I₁`
  (`G2`'s `exists_sharp_length` records why the sub-`1` regime would be vacuous), and
  `ramRbot_one_le_of_mem_ramI` certifies it holds on the WHOLE block range as soon as
  `Q₁ ≤ X_d` — so the gate is satisfiable, not silent.
* **Non-degeneracy.**  `I₁ ≠ ∅` under `0 ≤ H₁`, `1 ≤ P₁`, `P₁ ≤ Q₁`
  (`USetGradedThin.ramI_nonempty`, quoted at `G2` by
  `exists_mem_ramI_ramQ_le_of_mem_TsetG`); it is not carried as a gate here because the
  inequalities do not consume it, and an unused gate is a false pin.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 eq (21), §6 (Lemma 12), §8.1 p.25,
p.24 (the `H_j` table) and eq (20) p.24 (the `α_j` sequence);
`docs/exploration/hsup-design.md` ⟦V4a⟧ (the sharp-`M` law) and ⟦V6⟧ (the Route-G ladder).
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — G3a-i: the graded pointwise gain on `𝒯ⱼ` -/

/-- **The graded pointwise gain.**  For `t ∈ 𝒯ⱼ` and `v ∈ I_j`, MR (21) prices the block
factor of `Q_{v,H_j}·R_{v,H_j}` at `e^{−2α_j v/H_j}`:

  `‖(Q·R)_{v,H_j}(1+it)‖² ≤ e^{−2α_j v/H_j}·‖R_{v,H_j}(1+it)‖²`.

The graded set is instantiated at the SAME coefficient `c` the Ramaré block factor carries
(the coefficient seam — see the module docstring); with any other datum the gain does not
bite. -/
lemma norm_ramMain_sq_le_of_mem_TsetG {Pseq Qseq : ℕ → ℕ} {Hseq αseq : ℕ → ℝ} {Jb j : ℕ}
    {c : ℕ → ℂ} {t : ℝ} (ht : t ∈ TsetG c Pseq Qseq Hseq αseq Jb j)
    {v : ℕ} (hv : v ∈ ramI (Hseq j) (Pseq j) (Qseq j)) (N Xd : ℕ) (b : ℕ → ℂ) :
    ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2
      ≤ Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
  rw [ramMain, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (ramQ_sq_le_of_blockSmallG ht hv) (sq_nonneg _)

/-! ## §2 — G3a-ii: the per-block integral on a subset of `𝒯ⱼ` -/

/-- **G3a-ii — the per-block integral.**  On any measurable `A ⊆ [−T,T]` contained in `𝒯ⱼ`,

  `∫_A ‖(Q·R)_{v,H_j}(1+it)‖² dt ≤ e^{−2α_j v/H_j}·(4T·e^{v/H_j}/X_d + 120)`.

Three landed stones compose: the graded gain (§1) pulls the `v`-threshold out of the
integral; `A ⊆ [−T,T]` and a nonnegative integrand transfer the co-factor integral to the
full range; `G2`'s SHARP-`M` exit (`cofactor_mvt_sharp_exit_visible`) prices it, the length
`Ms` being produced here by `exists_sharp_length` from the window gate `1 ≤ X_v` and never
identified with the row length `N`. -/
theorem integral_ramMain_sq_le_of_subset_TsetG (c b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ)
    (Hseq αseq : ℕ → ℝ) (Jb j N Xd : ℕ) (hXd : 0 < Xd) (hb : ∀ m, ‖b m‖ ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (hAT : A ⊆ TsetG c Pseq Qseq Hseq αseq Jb j)
    (v : ℕ) (hv : v ∈ ramI (Hseq j) (Pseq j) (Qseq j))
    (hbot : 1 ≤ ramRbot (Hseq j) Xd v) :
    (∫ t in A, ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
      ≤ Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
          * (4 * T * Real.exp ((v : ℝ) / Hseq j) / (Xd : ℝ) + 120) := by
  have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) := (Real.exp_pos _).le
  have hcontM : Continuous
      (fun t : ℝ => ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2) :=
    (continuous_ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v).norm.pow 2
  have hcontR : Continuous
      (fun t : ℝ => ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) :=
    (continuous_ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b).norm.pow 2
  have hIntM : IntegrableOn
      (fun t : ℝ => ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2) A :=
    (hcontM.integrableOn_Icc (a := -T) (b := T)).mono_set hAsub
  have hIntR : IntegrableOn
      (fun t : ℝ => ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) A :=
    (hcontR.integrableOn_Icc (a := -T) (b := T)).mono_set hAsub
  have hIntRc : IntegrableOn
      (fun t : ℝ => Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
        * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) A := hIntR.const_mul _
  have hpt : (∫ t in A, ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
      ≤ ∫ t in A, Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    setIntegral_mono_on hIntM hIntRc hAm
      (fun t ht => norm_ramMain_sq_le_of_mem_TsetG (hAT ht) hv N Xd b)
  have hconst : (∫ t in A, Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
        * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      = Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
        * ∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    MeasureTheory.integral_const_mul _ _
  have hbig : IntegrableOn
      (fun t : ℝ => ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) (Set.Icc (-T) T) :=
    hcontR.integrableOn_Icc
  have hmono : (∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      ≤ ∫ t in Set.Icc (-T) T, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    setIntegral_mono_set hbig (Filter.Eventually.of_forall (fun t => by positivity))
      hAsub.eventuallyLE
  have hfull : (∫ t in Set.Icc (-T) T, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      = ∫ t in (-T)..T, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
  obtain ⟨Ms, hMs, hMs'⟩ := exists_sharp_length (Hseq j) Xd v hbot
  have hmvt := cofactor_mvt_sharp_exit_visible (Hseq j) N Xd (Pseq j) (Qseq j) v Ms b hb T hT
    hXd (by linarith) hMs hMs'
  have hR : (∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      ≤ 4 * T * Real.exp ((v : ℝ) / Hseq j) / (Xd : ℝ) + 120 := by
    rw [hfull] at hmono
    linarith
  calc (∫ t in A, ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
      ≤ Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
          * ∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
        rw [← hconst]; exact hpt
    _ ≤ Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
          * (4 * T * Real.exp ((v : ℝ) / Hseq j) / (Xd : ℝ) + 120) :=
        mul_le_mul_of_nonneg_left hR hE0

/-- **The sharp-length gate is SATISFIABLE on the whole block range (no silent vacuity).**
`X_v = X_d·e^{−v/H} ≥ 1` holds for EVERY `v ∈ I_j` as soon as `Q_j ≤ X_d` — the live regime,
since `v ≤ ⌊H log Q_j⌋ ≤ H log Q_j` puts the smallest window bottom at `X_d/Q_j`.  Recorded
(rather than assumed) because `G2`'s `exists_sharp_length` is vacuous below `X_v = 1`, and
`E1_bound` carries the gate as a hypothesis. -/
lemma ramRbot_one_le_of_mem_ramI {H : ℝ} (hH : 0 < H) {P Q Xd v : ℕ} (hQ : 1 ≤ Q)
    (hQX : Q ≤ Xd) (hv : v ∈ ramI H P Q) : 1 ≤ ramRbot H Xd v := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hlogQ : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast hQ)
  have hXQ : (Q : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hQX
  have hvle : (v : ℝ) ≤ H * Real.log (Q : ℝ) := by
    rw [ramI, Finset.mem_Icc] at hv
    have h : (v : ℝ) ≤ (⌊H * Real.log (Q : ℝ)⌋₊ : ℝ) := by exact_mod_cast hv.2
    exact le_trans h (Nat.floor_le (by positivity))
  have hkey : -(Real.log (Q : ℝ)) ≤ -(v : ℝ) / H := by
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hH]
    linarith
  have hinv : Real.exp (-(Real.log (Q : ℝ))) = 1 / (Q : ℝ) := by
    rw [Real.exp_neg, Real.exp_log hQ0, one_div]
  have h1 : (1 : ℝ) / (Q : ℝ) ≤ Real.exp (-(v : ℝ) / H) := by
    rw [← hinv]; exact Real.exp_le_exp.mpr hkey
  rw [ramRbot]
  calc (1 : ℝ) = (Q : ℝ) * (1 / (Q : ℝ)) := by field_simp
    _ ≤ (Xd : ℝ) * Real.exp (-(v : ℝ) / H) :=
        mul_le_mul hXQ h1 (by positivity) (le_trans hQ0.le hXQ)

/-! ## §3 — G3a-iii: the `v`-sum, both legs -/

/-- **G3a-iii — the block sum on a subset of `𝒯ⱼ`.**  Summing §2 over `v ∈ I_j` splits the
product `e^{−2α_j v/H_j}·(4T·e^{v/H_j}/X_d + 120)` into the two legs of opposite sign:

  `Σ_{v∈I_j} ∫_A ‖(Q·R)_v‖² ≤ (4T/X_d)·(H_j/(1−2α_j))·e^{(1−2α_j)/H_j}·Q_j^{1−2α_j}
                              + 120·min{(H_j/2α_j)·e^{−2α_j(v₀−1)/H_j}, |I_j|·e^{−2α_j v₀/H_j}}`

with `v₀ = ⌊H_j log P_j⌋`.  The `T`-leg GROWS (`e^{−2αv/H}·e^{v/H} = e^{(1−2α)v/H}`) and is
gated by `2α_j < 1` in-statement; the absolute `120` rides the decaying leg, where BOTH `G2`
forms are available and the `min` is taken. -/
theorem sum_integral_ramMain_sq_le_of_subset_TsetG (c b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ)
    (Hseq αseq : ℕ → ℝ) (Jb j N Xd : ℕ) (hXd : 0 < Xd) (hb : ∀ m, ‖b m‖ ≤ 1)
    (hH : 0 < Hseq j) (hα : 0 < αseq j) (hα2 : 2 * αseq j < 1) (hQ : 1 ≤ Qseq j)
    (T : ℝ) (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (hAT : A ⊆ TsetG c Pseq Qseq Hseq αseq Jb j)
    (hbot : ∀ v ∈ ramI (Hseq j) (Pseq j) (Qseq j), 1 ≤ ramRbot (Hseq j) Xd v) :
    (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
        ∫ t in A, ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
      ≤ 4 * T / (Xd : ℝ)
          * (Hseq j / (1 - 2 * αseq j) * Real.exp ((1 - 2 * αseq j) / Hseq j)
              * (Qseq j : ℝ) ^ (1 - 2 * αseq j))
        + 120 * min (Hseq j / (2 * αseq j)
                * Real.exp (-(2 * αseq j)
                    * ((⌊Hseq j * Real.log (Pseq j : ℝ)⌋₊ : ℝ) - 1) / Hseq j))
              (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
                * Real.exp (-(2 * αseq j)
                    * (⌊Hseq j * Real.log (Pseq j : ℝ)⌋₊ : ℝ) / Hseq j)) := by
  have hXR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hcoef0 : (0 : ℝ) ≤ 4 * T / (Xd : ℝ) := by positivity
  have hstep : ∀ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
      (∫ t in A, ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        ≤ 4 * T / (Xd : ℝ) * Real.exp ((1 - 2 * αseq j) * (v : ℝ) / Hseq j)
          + 120 * Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) := by
    intro v hv
    refine le_trans (integral_ramMain_sq_le_of_subset_TsetG c b Pseq Qseq Hseq αseq Jb j N Xd
      hXd hb T hT A hAm hAsub hAT v hv (hbot v hv)) (le_of_eq ?_)
    have hmerge : Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) * Real.exp ((v : ℝ) / Hseq j)
        = Real.exp ((1 - 2 * αseq j) * (v : ℝ) / Hseq j) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
          * (4 * T * Real.exp ((v : ℝ) / Hseq j) / (Xd : ℝ) + 120)
        = 4 * T / (Xd : ℝ)
              * (Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) * Real.exp ((v : ℝ) / Hseq j))
            + 120 * Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) := by ring
      _ = 4 * T / (Xd : ℝ) * Real.exp ((1 - 2 * αseq j) * (v : ℝ) / Hseq j)
            + 120 * Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j) := by rw [hmerge]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hgrow := sum_exp_growth_top (Hseq j) (αseq j) hH hα2 (Pseq j) (Qseq j) hQ
  have hdec :=
    le_min (sum_exp_neg_graded_rate (Hseq j) (αseq j) hH hα (Pseq j) (Qseq j))
      (sum_exp_neg_graded_card (Hseq j) (αseq j) hH hα.le (Pseq j) (Qseq j))
  have h1 := mul_le_mul_of_nonneg_left hgrow hcoef0
  have h2 := mul_le_mul_of_nonneg_left hdec (by norm_num : (0 : ℝ) ≤ 120)
  linarith

/-! ## §4 — G3a: the assembled level-1 page -/

/-- **G3a — MR §8.1, the level-1 `𝒯`-leg.**  The mean square of the row polynomial over
`A₁ := (Ann ∖ ball) ∩ 𝒯₁`, priced by the mean-value theorem alone:

  `∫_{A₁}‖F(1+it)‖² dt`
    `≤ 2|I₁|·( (4T/X_d)·(H₁/(1−2α₁))·e^{(1−2α₁)/H₁}·Q₁^{1−2α₁}`
    `          + 120·min{(H₁/2α₁)·e^{−2α₁(v₀−1)/H₁}, |I₁|·e^{−2α₁v₀/H₁}} ) + E`,

`v₀ = ⌊H₁ log P₁⌋`, `E` Lemma 12's error rows.  Every gate is in-statement: `2 ≤ H₁` (which
supplies `0 < H₁` for both `v`-sums), `0 < α₁` for the DECAYING leg only, `2α₁ < 1` for the
GROWING leg, `1 ≤ X_d`, `1 ≤ Q₁`, the measure frame `0 ≤ T`, and the sharp-length window
`1 ≤ X_v` on `I₁` (satisfiable — `G2`'s `exists_sharp_length`).  The graded set is
instantiated at the Ramaré prime coefficient `c` itself (the coefficient seam).

⟦ROW-GENERIC⟧ (⟦WALL 1⟧'s wave).  Lemma 12's rows are HOISTED: this page reads them only as
the opaque additive term `row`, supplied by the caller together with the per-level Lemma-12
conclusion `hL12`.  So `hcoef`, `hwin` and `hc` leave the statement, and the caller chooses
the exit — the landed three-row `TLegPreamble.lemma12_on_TsetG` (see `E1_bound` just below,
whose statement is unchanged) or ⟦WALL 1⟧'s `hwin`-free four-row
`M4RowMR.lemma12_on_TsetG_mr_windowed`. -/
theorem E1_bound_gen (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jb : ℕ)
    (hH : 2 ≤ Hseq 1) (hα : 0 < αseq 1) (hα2 : 2 * αseq 1 < 1)
    (N Xd : ℕ) (hX : 1 ≤ Xd) (hQ : 1 ≤ Qseq 1)
    (a b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1)
    (X T t₁ : ℝ) (hT : 0 ≤ T)
    (hbot : ∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v)
    (row : ℝ)
    (hL12 : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq αseq Jb 1,
          ‖spoly N a t‖ ^ 2)
        ≤ 2 * ((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
            * (∑ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1),
                ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq αseq Jb 1,
                  ‖ramMain (Hseq 1) N Xd (Pseq 1) (Qseq 1) b c v t‖ ^ 2)
          + row) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq αseq Jb 1,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
          * (4 * T / (Xd : ℝ)
              * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
                  * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
            + 120 * min (Hseq 1 / (2 * αseq 1)
                  * Real.exp (-(2 * αseq 1)
                      * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
                (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
                  * Real.exp (-(2 * αseq 1)
                      * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1)))
        + row := by
  have hmain := sum_integral_ramMain_sq_le_of_subset_TsetG c b Pseq Qseq Hseq αseq Jb 1 N Xd
    hX hb (lt_of_lt_of_le (by norm_num) hH) hα hα2 hQ T hT _
    (measurableSet_annulus_TsetG c Pseq Qseq Hseq αseq Jb 1 X T t₁)
    (annulus_TsetG_subset_Icc c Pseq Qseq Hseq αseq Jb 1 X T t₁)
    Set.inter_subset_right hbot
  have hcard0 : (0 : ℝ) ≤ 2 * ((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmain hcard0
  refine le_trans hL12 ?_
  linarith

/-- **G3a — MR §8.1, the level-1 `𝒯`-leg** (`E1_bound`) — `E1_bound_gen` at the LANDED
three-row Lemma-12 exit `TLegPreamble.lemma12_on_TsetG`.  Statement unchanged. -/
theorem E1_bound (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jb : ℕ)
    (hH : 2 ≤ Hseq 1) (hα : 0 < αseq 1) (hα2 : 2 * αseq 1 < 1)
    (N Xd : ℕ) (hX : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hP : 1 ≤ Pseq 1) (hQ : 1 ≤ Qseq 1)
    (a b : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → Pseq 1 ≤ p → p ≤ Qseq 1 → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → Pseq 1 ≤ p → p ≤ Qseq 1 → c p * b m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (X T t₁ : ℝ) (hT : 0 ≤ T)
    (hbot : ∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq αseq Jb 1,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * ((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
          * (4 * T / (Xd : ℝ)
              * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
                  * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
            + 120 * min (Hseq 1 / (2 * αseq 1)
                  * Real.exp (-(2 * αseq 1)
                      * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
                (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
                  * Real.exp (-(2 * αseq 1)
                      * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1)))
        + 2 * (3 * ((2 * T + 20 * (N : ℝ))
                * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq 1 + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N,
                    ‖ramP2coeff N (Pseq 1) (Qseq 1) a b c n‖ ^ 2 / (n : ℝ) ^ 2
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega (Pseq 1) (Qseq 1) n = 0),
                    ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) :=
  E1_bound_gen c Pseq Qseq Hseq αseq Jb hH hα hα2 N Xd hX hQ a b hb X T t₁ hT hbot _
    (lemma12_on_TsetG c Pseq Qseq Hseq αseq Jb 1 hH N Xd hX hN hP a b c hcoef hb hc hwin
      X T t₁ hT)

/-! ## §5 — G3b: the page at the pins -/

/-- The DECAYING leg at the block bottom: `e^{−2α(v₀−1)/H} ≤ e^{4α/H}·P^{−2α}`, from
`H log P < v₀ + 1` (`Nat.lt_floor_add_one`).  Both `e^{2α/H}` factors are kept visible — one
from the rate form's `v₀ − 1`, one from the floor. -/
lemma exp_block_bottom_le_rpow {H α : ℝ} (hH : 0 < H) (hα : 0 < α) {P : ℕ} (hP : 1 ≤ P) :
    Real.exp (-(2 * α) * ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1) / H)
      ≤ Real.exp (4 * α / H) * (P : ℝ) ^ (-(2 * α)) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hfl : H * Real.log (P : ℝ) < (⌊H * Real.log (P : ℝ)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hkey : α * (H * Real.log (P : ℝ))
      ≤ α * ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hfl.le hα.le
  rw [Real.rpow_def_of_pos hP0, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  rw [div_add' _ _ _ (ne_of_gt hH), div_le_div_iff_of_pos_right hH]
  nlinarith [hkey]

/-- The GROWING leg's base conversion: `Q^{1−2α} = Q·Q^{−2α} ≤ Q·P^{−2α}` for `1 ≤ P ≤ Q`
and `0 < α`.  This is the step that turns `(4T/X_d)·Q^{1−2α}` into MR's normalized
`4·(T/(X_d/Q))·P^{−2α}` — the negative exponent reverses the base comparison. -/
lemma rpow_growth_le_rpow_bottom {α : ℝ} (hα : 0 < α) {P Q : ℕ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    (Q : ℝ) ^ (1 - 2 * α) ≤ (Q : ℝ) * (P : ℝ) ^ (-(2 * α)) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hQ0 : (0 : ℝ) < (Q : ℝ) := lt_of_lt_of_le hP0 (by exact_mod_cast hPQ)
  have hsplit : (Q : ℝ) ^ (1 - 2 * α) = (Q : ℝ) * (Q : ℝ) ^ (-(2 * α)) := by
    rw [show (1 : ℝ) - 2 * α = 1 + -(2 * α) by ring, Real.rpow_add hQ0, Real.rpow_one]
  have hbase : (Q : ℝ) ^ (-(2 * α)) ≤ (P : ℝ) ^ (-(2 * α)) := by
    rw [Real.rpow_def_of_pos hQ0, Real.rpow_def_of_pos hP0]
    refine Real.exp_le_exp.mpr ?_
    have hlog : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
      Real.log_le_log hP0 (by exact_mod_cast hPQ)
    nlinarith [hlog, hα]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hbase hQ0.le

/-- **G3b — MR §8.1 at the pins.**  `E1_bound` evaluated at the block bottom
`v₀ = ⌊H₁ log P₁⌋`, with the block count discharged by `USetPrice.ramI_card_le` and the
growing leg normalized to MR's `T/(X/Q₁)`:

  `∫_{A₁}‖F(1+it)‖² dt`
    `≤ 2(H₁ log Q₁ + 1)·(T·Q₁/X_d + 1)·P₁^{−2α₁}`
    `      ·( 4(H₁/(1−2α₁))·e^{(1−2α₁)/H₁} + 60(H₁/α₁)·e^{4α₁/H₁} ) + E`.

That is the `H₁²·log Q₁·P₁^{−2α₁}·(T/(X/Q₁)+1)` shape of MR p.25 — see the module docstring
for the arithmetic verdict at MR's own `H₁`, `α₁` (it reproduces `(log Q₁)^{1/3}/P₁^{1/6−η}`
exactly).  `α₁` is NOT pinned here beyond its two gates: the α-sequence numerals belong to
the collection stones. -/
theorem E1_pin_gen (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jb : ℕ)
    (hH : 2 ≤ Hseq 1) (hα : 0 < αseq 1) (hα2 : 2 * αseq 1 < 1)
    (N Xd : ℕ) (hX : 1 ≤ Xd) (hP : 1 ≤ Pseq 1) (hPQ : Pseq 1 ≤ Qseq 1)
    (a b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1)
    (X T t₁ : ℝ) (hT : 0 ≤ T)
    (hbot : ∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v)
    (row : ℝ)
    (hL12 : (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq αseq Jb 1,
          ‖spoly N a t‖ ^ 2)
        ≤ 2 * ((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
            * (∑ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1),
                ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq αseq Jb 1,
                  ‖ramMain (Hseq 1) N Xd (Pseq 1) (Qseq 1) b c v t‖ ^ 2)
          + row) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq αseq Jb 1,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
          * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
          * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
          * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
              + 60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1))
        + row := by
  have hQ : 1 ≤ Qseq 1 := le_trans hP hPQ
  have hH0 : (0 : ℝ) < Hseq 1 := by linarith
  have hXR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hX
  have hP0 : (0 : ℝ) < (Pseq 1 : ℝ) := by exact_mod_cast hP
  have hQ0 : (0 : ℝ) < (Qseq 1 : ℝ) := by exact_mod_cast hQ
  have hlogQ : (0 : ℝ) ≤ Real.log (Qseq 1 : ℝ) := Real.log_nonneg (by exact_mod_cast hQ)
  have hPrpow : (0 : ℝ) ≤ (Pseq 1 : ℝ) ^ (-(2 * αseq 1)) := Real.rpow_nonneg hP0.le _
  have hden : (0 : ℝ) < 1 - 2 * αseq 1 := by linarith
  -- the two legs, each converted at the block bottom
  have hgrow : 4 * T / (Xd : ℝ)
        * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
            * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
      ≤ T * (Qseq 1 : ℝ) / (Xd : ℝ) * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
          * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)) := by
    have hc0 : (0 : ℝ) ≤ 4 * T / (Xd : ℝ)
        * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)) := by positivity
    have hstep := mul_le_mul_of_nonneg_left (rpow_growth_le_rpow_bottom hα hP hPQ) hc0
    calc 4 * T / (Xd : ℝ)
          * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
              * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
        = 4 * T / (Xd : ℝ)
              * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1))
            * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1) := by ring
      _ ≤ 4 * T / (Xd : ℝ)
              * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1))
            * ((Qseq 1 : ℝ) * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))) := hstep
      _ = T * (Qseq 1 : ℝ) / (Xd : ℝ) * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
            * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)) := by
          ring
  have hdecay : 120 * min (Hseq 1 / (2 * αseq 1)
          * Real.exp (-(2 * αseq 1)
              * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
        (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
          * Real.exp (-(2 * αseq 1)
              * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1))
      ≤ (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
          * (60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1)) := by
    have hmin := min_le_left (Hseq 1 / (2 * αseq 1)
        * Real.exp (-(2 * αseq 1)
            * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
      (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
        * Real.exp (-(2 * αseq 1)
            * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1))
    have hrate : (0 : ℝ) ≤ Hseq 1 / (2 * αseq 1) := by positivity
    have hbottom := mul_le_mul_of_nonneg_left (exp_block_bottom_le_rpow hH0 hα hP) hrate
    have heq : Hseq 1 / (2 * αseq 1)
          * (Real.exp (4 * αseq 1 / Hseq 1) * (Pseq 1 : ℝ) ^ (-(2 * αseq 1)))
        = (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
            * ((Hseq 1 / (2 * αseq 1)) * Real.exp (4 * αseq 1 / Hseq 1)) := by ring
    have hfin : (120 : ℝ) * ((Pseq 1 : ℝ) ^ (-(2 * αseq 1))
            * ((Hseq 1 / (2 * αseq 1)) * Real.exp (4 * αseq 1 / Hseq 1)))
        = (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
            * (60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1)) := by
      field_simp
      ring
    nlinarith [hmin, hbottom, heq, hfin, hPrpow]
  -- the `(T·Q/X_d + 1)` normalization: `u·A + B ≤ (u+1)(A+B)` for `u, A, B ≥ 0`
  have hu0 : (0 : ℝ) ≤ T * (Qseq 1 : ℝ) / (Xd : ℝ) := by positivity
  have hA0 : (0 : ℝ) ≤ (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
      * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)) := by
    have : (0 : ℝ) ≤ 4 * (Hseq 1 / (1 - 2 * αseq 1))
        * Real.exp ((1 - 2 * αseq 1) / Hseq 1) := by positivity
    exact mul_nonneg hPrpow this
  have hB0 : (0 : ℝ) ≤ (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
      * (60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1)) := by
    have : (0 : ℝ) ≤ 60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1) := by positivity
    exact mul_nonneg hPrpow this
  have hbracket : 4 * T / (Xd : ℝ)
        * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
            * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
      + 120 * min (Hseq 1 / (2 * αseq 1)
            * Real.exp (-(2 * αseq 1)
                * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
          (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
            * Real.exp (-(2 * αseq 1)
                * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1))
      ≤ (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1) * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
          * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
              + 60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1)) := by
    nlinarith [hgrow, hdecay, hu0, hA0, hB0]
  have hbr0 : (0 : ℝ) ≤ 4 * T / (Xd : ℝ)
        * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
            * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
      + 120 * min (Hseq 1 / (2 * αseq 1)
            * Real.exp (-(2 * αseq 1)
                * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
          (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
            * Real.exp (-(2 * αseq 1)
                * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1)) := by
    have h1 : (0 : ℝ) ≤ 4 * T / (Xd : ℝ)
        * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
            * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1)) := by
      have hq : (0 : ℝ) ≤ (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1) := Real.rpow_nonneg hQ0.le _
      have hcf : (0 : ℝ) ≤ 4 * T / (Xd : ℝ)
          * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)) := by positivity
      nlinarith [hq, hcf]
    have h2 : (0 : ℝ) ≤ min (Hseq 1 / (2 * αseq 1)
          * Real.exp (-(2 * αseq 1)
              * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
        (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
          * Real.exp (-(2 * αseq 1)
              * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1)) :=
      le_min (by positivity) (by positivity)
    linarith
  have hcard : 2 * ((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
      ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1) := by
    have h := ramI_card_le (Hseq 1) (Pseq 1) (Qseq 1) (mul_nonneg hH0.le hlogQ)
    linarith
  have hpos : (0 : ℝ) ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1) := by
    have := mul_nonneg hH0.le hlogQ
    linarith
  have hfinal : 2 * ((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
        * (4 * T / (Xd : ℝ)
            * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
                * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
          + 120 * min (Hseq 1 / (2 * αseq 1)
                * Real.exp (-(2 * αseq 1)
                    * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
              (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
                * Real.exp (-(2 * αseq 1)
                    * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1)))
      ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
          * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
          * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
          * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
              + 60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1)) :=
  calc 2 * ((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
        * (4 * T / (Xd : ℝ)
            * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
                * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
          + 120 * min (Hseq 1 / (2 * αseq 1)
                * Real.exp (-(2 * αseq 1)
                    * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
              (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
                * Real.exp (-(2 * αseq 1)
                    * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1)))
      ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
          * (4 * T / (Xd : ℝ)
              * (Hseq 1 / (1 - 2 * αseq 1) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
                  * (Qseq 1 : ℝ) ^ (1 - 2 * αseq 1))
            + 120 * min (Hseq 1 / (2 * αseq 1)
                  * Real.exp (-(2 * αseq 1)
                      * ((⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) - 1) / Hseq 1))
                (((ramI (Hseq 1) (Pseq 1) (Qseq 1)).card : ℝ)
                  * Real.exp (-(2 * αseq 1)
                      * (⌊Hseq 1 * Real.log (Pseq 1 : ℝ)⌋₊ : ℝ) / Hseq 1))) :=
        mul_le_mul_of_nonneg_right hcard hbr0
    _ ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
          * ((T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1) * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
              * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
                  + 60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1))) :=
        mul_le_mul_of_nonneg_left hbracket hpos
    _ = 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
          * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
          * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
          * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
              + 60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1)) := by ring
  refine le_trans (E1_bound_gen c Pseq Qseq Hseq αseq Jb hH hα hα2 N Xd hX hQ a b hb
    X T t₁ hT hbot row hL12) ?_
  linarith

/-- **G3b — MR §8.1 at the pins** (`E1_pin`) — `E1_pin_gen` at the LANDED three-row Lemma-12
exit `TLegPreamble.lemma12_on_TsetG`.  Statement unchanged. -/
theorem E1_pin (c : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (Jb : ℕ)
    (hH : 2 ≤ Hseq 1) (hα : 0 < αseq 1) (hα2 : 2 * αseq 1 < 1)
    (N Xd : ℕ) (hX : 1 ≤ Xd) (hN : 2 * Xd ≤ N) (hP : 1 ≤ Pseq 1) (hPQ : Pseq 1 ≤ Qseq 1)
    (a b : ℕ → ℂ)
    (hcoef : ∀ p m, p.Prime → Pseq 1 ≤ p → p ≤ Qseq 1 → ¬ p ∣ m → a (p * m) = b m * c p)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hwin : ∀ p m : ℕ, p.Prime → Pseq 1 ≤ p → p ≤ Qseq 1 → c p * b m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (X T t₁ : ℝ) (hT : 0 ≤ T)
    (hbot : ∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) :
    (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq αseq Jb 1,
        ‖spoly N a t‖ ^ 2)
      ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
          * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
          * (Pseq 1 : ℝ) ^ (-(2 * αseq 1))
          * (4 * (Hseq 1 / (1 - 2 * αseq 1)) * Real.exp ((1 - 2 * αseq 1) / Hseq 1)
              + 60 * (Hseq 1 / αseq 1) * Real.exp (4 * αseq 1 / Hseq 1))
        + 2 * (3 * ((2 * T + 20 * (N : ℝ))
                * ((2 * Real.exp 1 * (Xd : ℝ) / Hseq 1 + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ Finset.Icc 1 N,
                    ‖ramP2coeff N (Pseq 1) (Qseq 1) a b c n‖ ^ 2 / (n : ℝ) ^ 2
            + (2 * T + 20 * (N : ℝ))
                * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega (Pseq 1) (Qseq 1) n = 0),
                    ‖a n‖ ^ 2 / (n : ℝ) ^ 2)) :=
  E1_pin_gen c Pseq Qseq Hseq αseq Jb hH hα hα2 N Xd hX hP hPQ a b hb X T t₁ hT hbot _
    (lemma12_on_TsetG c Pseq Qseq Hseq αseq Jb 1 hH N Xd hX hN hP a b c hcoef hb hc hwin
      X T t₁ hT)

end Salt.MR
