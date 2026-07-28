/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4MeanSq

/-!
# `M4Seam` — THE A2-5 SEAM, CLOSED AT THE ROW (`m4_hT0band_at_row`)

`M4MeanSq`'s capstone `m4_meansq_per_chi_gen` keeps the `T₀`-band as an explicit slot

  `hT0band : ∫_{−T₀}^{T₀} ‖dpolyA a (seamS0 N X) t‖² ≤ t0BandB X C₁′ M₀`

because the landed band supply `T0BandCapFree.cfb_t0band_supply` asks for the UNSIEVED seam
datum (`hDatum : a n = seamCoeff (ellLin g) 1 t₀ n` above `X`) while the row's own `a` is
SIEVED (`homega : a n ≠ 0 → 1 ≤ blockOmega P P n`).  `M4Close`'s `M4LiveAgree` named the
missing agreement; as stated it is jointly unsatisfiable with the sieve support, so it is a
dead-end name for a real obligation.  This file supplies the real obligation instead.

## THE TWO STONES

* **§1 — `cfb_t0band_supply_of_sup`**: the datum-free re-cut of the band supply.  In
  `cfb_t0band_supply` the datum hypothesis `hDatum` is used EXACTLY ONCE, at the single call
  to `cfb_sup_of_center`, whose own statement is at an abstract `f`; everything after it (the
  crude fold `band_integral_of_sup_crude` and the plug arithmetic) is `a`-generic.  Cutting
  there gives a supply whose only coefficient hypotheses are `hsupp` (vanishing below `X`)
  and the PER-FREQUENCY SUP at `a` itself.  No `hRHS`, no `hfloor`, no `hDatum`, no `X₀`
  existential — the scale floor collapses to the bare `3 ≤ X` that `bandTail_nonneg` wants.

* **§2–§4 — THE DILATION ROUTE.**  The row's `hcoefPin` already resolves the sieve:
  `a(P·m) = ellLin (liouChi χ) m · cf P` whenever `P ∤ m`.  So `a`'s polynomial FACTORIZES
  through the unsieved datum at the dilated scale `X/P`:

  `Σ_{n ∈ s} a n · n^{−it}
     = cf P · P^{−it} · Σ_{k ∈ s/P, P ∤ k} ℓ(k) · k^{−it}  +  Σ_{n ∈ s, P² ∣ n} a n · n^{−it}`

  (`ℓ := ellLin (liouChi χ)`).  The re-index is EXACT — no `±1`:

  | end | condition on `n = P·k` | condition on `k` | why exact |
  |---|---|---|---|
  | top (`Icc`) | `P·k ≤ m` | `k ≤ m / P` | `Nat.le_div_iff_mul_le`, `0 < P` |
  | top (`seamS0`) | `P·k ≤ N` | `k ≤ N / P` | same (NAT division, not `⌊·⌋`) |
  | bottom (`seamS0`) | `X < P·k` | `X/P < k` | `div_lt_iff₀`, `0 < (P:ℝ)` (REAL division) |
  | multiplicity | `P ∣ n`, `P² ∤ n` | `P ∤ k` | `mul_dvd_mul_iff_left`, `P ≠ 0` |

  The only inexactness anywhere is the `P²`-remainder, which is NOT an endpoint effect: it is
  the genuine part of `a` on which `hcoefPin` is silent (`a(P²j) = a(P·(P j))` and `P ∣ P j`),
  and it is paid by the trivial count `#{n ≤ m : P² ∣ n} = m/P² ≤ m/P²` (`card_filter_dvd_Icc`,
  exact on the nose).

  **The `t₀`-shift, tracked exactly.**  The row's `hcoefPin` factorizes `a` through the
  UNTWISTED `ℓ` — no `n^{−it₀}` rides in it.  Where a `t₀`-twisted datum IS used (the
  `m4BandDatum` route of `M4MeanSq` §2) the shift factors as
  `(P·m)^{−it₀} = P^{−it₀}·m^{−it₀}` and the `P^{−it₀}` joins the `cf P` coefficient,
  unimodular; here it is the frequency `t` itself that splits that way (`natCast_mul_cpow`),
  and `‖P^{−it}‖ = 1` is `norm_natCast_cpow_it`.  The `t₀`-slot of the exit is therefore FREE
  — `m4_hT0band_at_row` never picks a `t₀`, and none appears in its statement.

## THE FINDING (kernel-checked here, `m4_row_cf_block_eq_zero`)

`m4_meansq_per_chi_gen`'s window binder at the block prime,

  `∀ p m, p.Prime → P ≤ p → p ≤ P → cf p · ℓ(m) ≠ 0 → X_d ≤ p·m ∧ p·m ≤ 2X_d`,

quantifies over EVERY `m : ℕ`, and `ℓ(1) = 1` (the empty product over `(1 : ℕ).primeFactors`,
`Squarefree 1`).  Taking `m := 1` therefore forces `cf P ≠ 0 → X_d ≤ P`.  But the row also
carries `(P:ℝ) ≤ 2(X/h)`, `4 ≤ h` and `(X_d : ℝ) = X`, so `P ≤ X/2 < X = X_d`.  Hence

  **`cf P = 0` at every instance of the row.**

That is not vacuity (`a ≡ 0`, and any `a` supported on `P²`-multiples of the dyadic window,
inhabit the binder set) — but it does collapse the dilation route's MAIN term: with `cf P = 0`
the pin forces `a` to vanish off `P²ℕ`, and the whole polynomial is the `P²`-residue.  The
seam then closes on ONE numeric gate, `M₀ ≤ 4e·log P` (§4), which the row's own numerology
clears with astronomical margin: `P83 X θ₂₉₃ ≤ P` gives `log P ≥ (log X)^{1−θ₂₉₃}`, while
`cfb_t0band_supply_chi`'s own arithmetic gives `M₀ = cfbM0 K q X ≤ loglog X`.

Both routes are landed: `m4_hT0band_of_dilated_sup` (§4) is the general supplier — the one
that survives if the window binder is repaired to a bounded `m`-range — and
`m4_hT0band_at_row` (§4) is the row's own instance, which needs no dilated sup at all.

## WHAT IS NOT CLAIMED

Nothing here supplies `hRHS` at the dilated scale, and nothing here re-states a blueprint
node.  `m4_hT0band_of_dilated_sup`'s `hdil` is a named binder of exactly the shape
`cfb_sup_of_center` produces at scale `X/P`; the four log scales (`log X`, `log(X/P)`,
`loglog X`, `log P`) are never silently identified — the only comparison used is the single
inequality `M₀ ≤ 4e·log P`, carried as a binder.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory
open scoped BigOperators

/-! ## §1 — THE DATUM-FREE RE-CUT OF THE BAND SUPPLY

`cfb_t0band_supply` uses `hDatum` at exactly one place: the call
`cfb_sup_of_center hX0 hXN hS₀0 hsupp hDatum hcen`, which manufactures the per-frequency sup
`‖spolyA a t m‖ ≤ 2S₀·m`.  Take that sup as the hypothesis and the rest of the proof — the
crude fold plus the plug arithmetic — goes through verbatim at a completely abstract `a`. -/

/-- **THE DATUM-FREE BAND SUPPLY (`cfb_t0band_supply_of_sup`).**  With the per-frequency,
unweighted sup at `a` ITSELF as the hypothesis,

  `∫_{−T₀}^{T₀} ‖dpolyA a (seamS0 N X) t‖² dt ≤ t0BandB X (cfbC₁ X C₁) M₀`,
  `T₀ = seamT0 X = (log X)^{1/15}`,

which is `ThmA2Rows.thm_a2'_of_rows`'s (hence `m4_meansq_per_chi_gen`'s) `hT0band` slot at
`C₁′ := cfbC₁ X C₁` — an instantiation, not a re-statement.

Compared with `cfb_t0band_supply` this drops `hRHS`, `hfloor`, `hDatum`, the four `Y`-gates,
the `g`-slot and the `X₀` existential; it keeps `hsupp` (the crude fold reads it), `hErr`
(the `4P ≤ E` step of the plug) and the pins.  `hSle` names the sup's grade: `S` must be the
supply's own `2(C₁E + 4P)` or better, which is exactly what `cfb_sup_of_center` delivers. -/
theorem cfb_t0band_supply_of_sup {N : ℕ} {a : ℕ → ℂ} {X C₁ M₀ S : ℝ}
    (hX3 : (3 : ℝ) ≤ X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X) (hC₁ : 1 ≤ C₁)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hS0 : 0 ≤ S)
    (hSle : S ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)))
    (hsup : ∀ t : ℝ, |t| ≤ seamT0 X → ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * (m : ℝ))
    (hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)) :
    (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
  have hT0 : (0 : ℝ) ≤ seamT0 X := seamT0_nonneg hlogX0
  set E : ℝ := Real.exp (-(1 / (2 * Real.exp 1)) * M₀) with hEdef
  set P : ℝ := Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) with hPdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hP0 : (0 : ℝ) ≤ P := Real.rpow_nonneg hlogX0 _
  -- §2 of `T0BandCapFree`, verbatim: the crude fold
  have hint := band_integral_of_sup_crude (N := N) (a := a) (X := X) (R := seamT0 X)
    (S := S) hX0 hT0 hXN hN2 hsupp hsup
  refine le_trans hint ?_
  -- the plug: `8·T₀·S² ≤ 8·(2√2·C₁′·E)² ≤ t0BandB X C₁′ M₀`
  have hC1'0 : (0 : ℝ) ≤ cfbC₁ X C₁ := cfbC₁_nonneg hC₁
  have hsqrt2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htail : (0 : ℝ) ≤ bandTail X (seamT0 X) * (1 + seamT0 X) :=
    mul_nonneg (bandTail_nonneg hX3 hT0) (by linarith)
  have hinner : 2 * Real.sqrt 2 * (cfbC₁ X C₁ * E) ≤ t0BandS X (cfbC₁ X C₁) M₀ := by
    unfold t0BandS bandSupS
    nlinarith [hP0, hsqrt2, htail]
  have hinner0 : (0 : ℝ) ≤ 2 * Real.sqrt 2 * (cfbC₁ X C₁ * E) := by positivity
  have hexpand : (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2
      = 8 * ((C₁ + 1) ^ 2 * seamT0 X * E ^ 2) := by
    have h : (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2
        = 4 * Real.sqrt 2 ^ 2 * (cfbC₁ X C₁ ^ 2 * E ^ 2) := by ring
    rw [h, hsq2, cfbC₁_sq hlogX0]
    ring
  have hSle' : S ≤ 2 * ((C₁ + 1) * E) := by nlinarith [hSle, hErr]
  have hSsq : S ^ 2 ≤ (2 * ((C₁ + 1) * E)) ^ 2 := pow_le_pow_left₀ hS0 hSle' 2
  have hfinal : 8 * seamT0 X * S ^ 2 ≤ 8 * (t0BandS X (cfbC₁ X C₁) M₀) ^ 2 := by
    have h1 : 8 * seamT0 X * S ^ 2 ≤ 32 * seamT0 X * ((C₁ + 1) ^ 2 * E ^ 2) := by
      nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hSsq)]
    have h2 : 32 * seamT0 X * ((C₁ + 1) ^ 2 * E ^ 2)
        ≤ 8 * (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2 := by
      rw [hexpand]
      nlinarith [hT0, sq_nonneg E, sq_nonneg (C₁ + 1)]
    have h3 : (2 * Real.sqrt 2 * (cfbC₁ X C₁ * E)) ^ 2 ≤ (t0BandS X (cfbC₁ X C₁) M₀) ^ 2 :=
      pow_le_pow_left₀ hinner0 hinner 2
    linarith
  unfold t0BandB
  linarith

/-! ## §2 — THE DILATION RE-INDEX

Two Finset identities and their counting partners.  Everything here is exact: the top end is
NAT division, the bottom end (for `seamS0`) is REAL division, and the multiplicity condition
`P ∣ n ∧ P² ∤ n` corresponds to `P ∤ k` under `n = P·k`. -/

/-- `1 ≤ ω(n; P, P)` at the block prime is exactly `P ∣ n`. -/
theorem dvd_of_one_le_blockOmega_self {P n : ℕ} (h : 1 ≤ blockOmega P P n) : P ∣ n := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (BlockPrimeDivs P P n).card from h)
  obtain ⟨-, hpn, -, hPp, hpP⟩ := mem_blockPrimeDivs.mp hp
  have hpe : p = P := le_antisymm hpP hPp
  exact hpe ▸ hpn

/-- `‖n^{it}‖ = 1` at `n ≥ 1` — the unimodularity of the frequency twist. -/
theorem norm_natCast_cpow_it {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  have hre : ((t : ℂ) * I).re = 0 := by simp
  rw [hre, Real.rpow_zero]

-- The multiplicative split of the cpow along a NAT product — where `P^{−it}` (and, in the
-- twisted route, `P^{−it₀}`) detaches from the dilated variable — is `SupF.natCast_mul_cpow`,
-- already in the corpus; it is used verbatim below.

/-- A sum of `1`-bounded coefficients against the unimodular twist is bounded by the card. -/
theorem norm_sum_div_cpow_le_card {s : Finset ℕ} {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1)
    (hs : ∀ n ∈ s, 1 ≤ n) (t : ℝ) :
    ‖∑ n ∈ s, b n / (n : ℂ) ^ ((t : ℂ) * I)‖ ≤ (s.card : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ s, ‖b n / (n : ℂ) ^ ((t : ℂ) * I)‖ ≤ 1 := by
    intro n hn
    rw [norm_div, norm_natCast_cpow_it (hs n hn) t, div_one]
    exact hb n
  calc ∑ n ∈ s, ‖b n / (n : ℂ) ^ ((t : ℂ) * I)‖ ≤ ∑ _n ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (s.card : ℝ) := by simp

/-- `#{n ∈ [1,m] : d ∣ n} = m / d` (NAT division) — `Nat.Ioc_filter_dvd_card_eq_div` at the
`Icc 1 m = Ioc 0 m` convention. -/
theorem card_filter_dvd_Icc (d m : ℕ) :
    ((Finset.Icc 1 m).filter (fun n => d ∣ n)).card = m / d := by
  have hset : Finset.Icc 1 m = Finset.Ioc 0 m := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hset]
  exact Nat.Ioc_filter_dvd_card_eq_div m d

/-- **THE RE-INDEX ON `[1, m]`** — exact, both ends. -/
theorem Icc_filter_pexact_image {P m : ℕ} (hP : 0 < P) :
    ((Finset.Icc 1 (m / P)).filter (fun k => ¬ P ∣ k)).image (fun k => P * k)
      = (Finset.Icc 1 m).filter (fun n => P ∣ n ∧ ¬ P * P ∣ n) := by
  ext n
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨⟨hk1, hk2⟩, hkP⟩, rfl⟩
    have hkm : k * P ≤ m := (Nat.le_div_iff_mul_le hP).mp hk2
    refine ⟨⟨?_, ?_⟩, dvd_mul_right P k, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr fun hz => by
        rcases Nat.mul_eq_zero.mp hz with h | h <;> omega
    · rw [Nat.mul_comm]; exact hkm
    · exact fun hc => hkP ((mul_dvd_mul_iff_left hP.ne').mp hc)
  · rintro ⟨⟨hn1, hn2⟩, ⟨k, rfl⟩, hsq⟩
    refine ⟨k, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
    · exact Nat.pos_of_ne_zero fun hz => by subst hz; simp at hn1
    · exact (Nat.le_div_iff_mul_le hP).mpr (by rw [Nat.mul_comm]; exact hn2)
    · exact fun hc => hsq (mul_dvd_mul_left P hc)

/-- **THE RE-INDEX ON `seamS0`** — the dilated index set is `seamS0 (N/P) (X/P)` with the
`P`-multiples removed; NAT division at the top, REAL division at the bottom, both exact. -/
theorem seamS0_filter_pexact_image {P N : ℕ} {X : ℝ} (hP : 0 < P) :
    ((seamS0 (N / P) (X / (P : ℝ))).filter (fun k => ¬ P ∣ k)).image (fun k => P * k)
      = (seamS0 N X).filter (fun n => P ∣ n ∧ ¬ P * P ∣ n) := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  ext n
  simp only [seamS0, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨⟨⟨hk1, hk2⟩, hkX⟩, hkP⟩, rfl⟩
    have hkm : k * P ≤ N := (Nat.le_div_iff_mul_le hP).mp hk2
    have hkXR : X < (k : ℝ) * (P : ℝ) := (div_lt_iff₀ hPR).mp hkX
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right P k, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr fun hz => by
        rcases Nat.mul_eq_zero.mp hz with h | h <;> omega
    · rw [Nat.mul_comm]; exact hkm
    · push_cast; linarith
    · exact fun hc => hkP ((mul_dvd_mul_iff_left hP.ne').mp hc)
  · rintro ⟨⟨⟨hn1, hn2⟩, hnX⟩, ⟨k, rfl⟩, hsq⟩
    push_cast at hnX
    refine ⟨k, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · exact Nat.pos_of_ne_zero fun hz => by subst hz; simp at hn1
    · exact (Nat.le_div_iff_mul_le hP).mpr (by rw [Nat.mul_comm]; exact hn2)
    · exact (div_lt_iff₀ hPR).mpr (by linarith)
    · exact fun hc => hsq (mul_dvd_mul_left P hc)

/-- The `P`-dilation map is injective on any index set (`0 < P`). -/
theorem injOn_mul_left {P : ℕ} (hP : 0 < P) (s : Finset ℕ) :
    Set.InjOn (fun k => P * k) ↑s := fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hP h

/-! ## §3 — THE FACTORIZATION

Both the `spolyA` (unweighted, what the sup wants) and the `dpolyA` (weighted, the slot's own
integrand) forms.  `cf P · P^{−it}` is the detached coefficient; the residue is the honest
`P²`-part, on which `hcoefPin` is silent. -/

/-- **THE `spolyA` DILATION FACTORIZATION.**  Under the row's sieve support and coefficient
pin at the block prime `P`,

  `A_t(m) = cf P · (P^{it})⁻¹ · Σ_{k ≤ m/P, P ∤ k} ℓ(k)·k^{−it} + Σ_{n ≤ m, P² ∣ n} a n·n^{−it}`,

`ℓ := ellLin (liouChi χ)`.  Exact — the only non-`hcoefPin` part of `a` is the `P²`-part. -/
theorem spolyA_dilate_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {P m : ℕ} {a cf : ℕ → ℂ}
    (hP : 0 < P)
    (homega : ∀ n : ℕ, a n ≠ 0 → P ∣ n)
    (hpin : ∀ k : ℕ, ¬ P ∣ k → a (P * k) = ellLin (liouChi χ) k * cf P)
    (t : ℝ) :
    spolyA a t m
      = cf P * ((P : ℂ) ^ ((t : ℂ) * I))⁻¹
          * (∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => ¬ P ∣ k),
              ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I))
        + ∑ n ∈ (Finset.Icc 1 m).filter (fun n => P * P ∣ n),
            a n / (n : ℂ) ^ ((t : ℂ) * I) := by
  classical
  have hsplit : spolyA a t m
      = (∑ n ∈ (Finset.Icc 1 m).filter (fun n => P ∣ n ∧ ¬ P * P ∣ n),
          a n / (n : ℂ) ^ ((t : ℂ) * I))
        + ∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ (P ∣ n ∧ ¬ P * P ∣ n)),
            a n / (n : ℂ) ^ ((t : ℂ) * I) := by
    unfold spolyA
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hres : (∑ n ∈ (Finset.Icc 1 m).filter (fun n => ¬ (P ∣ n ∧ ¬ P * P ∣ n)),
        a n / (n : ℂ) ^ ((t : ℂ) * I))
      = ∑ n ∈ (Finset.Icc 1 m).filter (fun n => P * P ∣ n),
          a n / (n : ℂ) ^ ((t : ℂ) * I) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
        fun hc => hc.2 (Finset.mem_filter.mp hn).2⟩
    · intro n hn hn'
      have hmem : n ∈ Finset.Icc 1 m := (Finset.mem_filter.mp hn).1
      have hnot : ¬ (P ∣ n ∧ ¬ P * P ∣ n) := (Finset.mem_filter.mp hn).2
      have hnsq : ¬ P * P ∣ n := fun hsq => hn' (Finset.mem_filter.mpr ⟨hmem, hsq⟩)
      have hnd : ¬ P ∣ n := fun hd => hnot ⟨hd, hnsq⟩
      have haz : a n = 0 := by by_contra hc; exact hnd (homega n hc)
      rw [haz, zero_div]
  have hmain : (∑ n ∈ (Finset.Icc 1 m).filter (fun n => P ∣ n ∧ ¬ P * P ∣ n),
        a n / (n : ℂ) ^ ((t : ℂ) * I))
      = cf P * ((P : ℂ) ^ ((t : ℂ) * I))⁻¹
          * ∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => ¬ P ∣ k),
              ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I) := by
    rw [← Icc_filter_pexact_image hP, Finset.sum_image (injOn_mul_left hP _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkP : ¬ P ∣ k := (Finset.mem_filter.mp hk).2
    rw [hpin k hkP, natCast_mul_cpow]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hsplit, hres, hmain]

/-- **THE `dpolyA` FACTORIZATION** (the slot's own integrand).  Same re-index, with the
weighted exponent `1 + it`:

  `dpolyA a (seamS0 N X) t
     = cf P · (P^{1+it})⁻¹ · dpolyA ℓ ((seamS0 (N/P) (X/P)).filter (P ∤ ·)) t
       + Σ_{n ∈ seamS0 N X, P² ∣ n} a n / n^{1+it}`.

The dilated index set is `seamS0` AT THE DILATED SCALE — `N/P` (NAT) and `X/P` (REAL) — with
the `P`-multiples removed.  This is the "one new lemma" the dilation route needed: no
`dpolyA` re-index existed in the corpus. -/
theorem dpolyA_seamS0_dilate {q : ℕ} (χ : DirichletCharacter ℂ q) {P N : ℕ} {a cf : ℕ → ℂ}
    {X : ℝ} (hP : 0 < P)
    (homega : ∀ n : ℕ, a n ≠ 0 → P ∣ n)
    (hpin : ∀ k : ℕ, ¬ P ∣ k → a (P * k) = ellLin (liouChi χ) k * cf P)
    (t : ℝ) :
    dpolyA a (seamS0 N X) t
      = cf P * ((P : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))⁻¹
          * dpolyA (ellLin (liouChi χ))
              ((seamS0 (N / P) (X / (P : ℝ))).filter (fun k => ¬ P ∣ k)) t
        + ∑ n ∈ (seamS0 N X).filter (fun n => P * P ∣ n),
            a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I) := by
  classical
  have hsplit : dpolyA a (seamS0 N X) t
      = (∑ n ∈ (seamS0 N X).filter (fun n => P ∣ n ∧ ¬ P * P ∣ n),
          a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))
        + ∑ n ∈ (seamS0 N X).filter (fun n => ¬ (P ∣ n ∧ ¬ P * P ∣ n)),
            a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I) := by
    unfold dpolyA
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hres : (∑ n ∈ (seamS0 N X).filter (fun n => ¬ (P ∣ n ∧ ¬ P * P ∣ n)),
        a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))
      = ∑ n ∈ (seamS0 N X).filter (fun n => P * P ∣ n),
          a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
        fun hc => hc.2 (Finset.mem_filter.mp hn).2⟩
    · intro n hn hn'
      have hmem : n ∈ seamS0 N X := (Finset.mem_filter.mp hn).1
      have hnot : ¬ (P ∣ n ∧ ¬ P * P ∣ n) := (Finset.mem_filter.mp hn).2
      have hnsq : ¬ P * P ∣ n := fun hsq => hn' (Finset.mem_filter.mpr ⟨hmem, hsq⟩)
      have hnd : ¬ P ∣ n := fun hd => hnot ⟨hd, hnsq⟩
      have haz : a n = 0 := by by_contra hc; exact hnd (homega n hc)
      rw [haz, zero_div]
  have hmain : (∑ n ∈ (seamS0 N X).filter (fun n => P ∣ n ∧ ¬ P * P ∣ n),
        a n / (n : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))
      = cf P * ((P : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I))⁻¹
          * dpolyA (ellLin (liouChi χ))
              ((seamS0 (N / P) (X / (P : ℝ))).filter (fun k => ¬ P ∣ k)) t := by
    rw [← seamS0_filter_pexact_image hP, Finset.sum_image (injOn_mul_left hP _)]
    unfold dpolyA
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkP : ¬ P ∣ k := (Finset.mem_filter.mp hk).2
    rw [hpin k hkP, natCast_mul_cpow]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hsplit, hres, hmain]

/-! ## §4 — THE SUP TRANSFER AND THE COMPOSED EXITS -/

/-- **THE SUP TRANSFER.**  The dilation bound at the row's own `a`:

  `‖A_t(m)‖ ≤ ‖cf P‖·‖A^ℓ_t(⌊m/P⌋)‖ + (‖cf P‖ + 1)·m/P²`.

The two `m/P²` debits are (i) the `P ∣ k` terms removed from the dilated sum to make it a
FULL `spolyA` of `ℓ` (which is what the band machinery bounds) and (ii) the `P²`-residue of
`a`.  Both counts are EXACT: `#{k ≤ m/P : P ∣ k} = #{n ≤ m : P² ∣ n} = m/(P·P)`. -/
theorem norm_spolyA_dilate_le {q : ℕ} (χ : DirichletCharacter ℂ q) {P m : ℕ} {a cf : ℕ → ℂ}
    (hP : 0 < P) (ha1 : ∀ n, ‖a n‖ ≤ 1)
    (homega : ∀ n : ℕ, a n ≠ 0 → P ∣ n)
    (hpin : ∀ k : ℕ, ¬ P ∣ k → a (P * k) = ellLin (liouChi χ) k * cf P)
    (t : ℝ) :
    ‖spolyA a t m‖
      ≤ ‖cf P‖ * ‖spolyA (ellLin (liouChi χ)) t (m / P)‖
        + (‖cf P‖ + 1) * ((m : ℝ) / ((P : ℝ) * (P : ℝ))) := by
  classical
  have hl1 : ∀ n, ‖ellLin (liouChi χ) n‖ ≤ 1 :=
    fun n => ellLin_norm_le_one (liouChi χ) (fun p _ => norm_liouChi_le_one χ p) n
  have hcard1 : (((Finset.Icc 1 (m / P)).filter (fun k => P ∣ k)).card : ℝ)
      ≤ (m : ℝ) / ((P : ℝ) * (P : ℝ)) := by
    rw [card_filter_dvd_Icc, Nat.div_div_eq_div_mul]
    calc (((m / (P * P) : ℕ)) : ℝ) ≤ (m : ℝ) / ((P * P : ℕ) : ℝ) := Nat.cast_div_le
      _ = (m : ℝ) / ((P : ℝ) * (P : ℝ)) := by rw [Nat.cast_mul]
  have hcard2 : (((Finset.Icc 1 m).filter (fun n => P * P ∣ n)).card : ℝ)
      ≤ (m : ℝ) / ((P : ℝ) * (P : ℝ)) := by
    rw [card_filter_dvd_Icc]
    calc (((m / (P * P) : ℕ)) : ℝ) ≤ (m : ℝ) / ((P * P : ℕ) : ℝ) := Nat.cast_div_le
      _ = (m : ℝ) / ((P : ℝ) * (P : ℝ)) := by rw [Nat.cast_mul]
  have hsieve : ‖∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => ¬ P ∣ k),
        ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I)‖
      ≤ ‖spolyA (ellLin (liouChi χ)) t (m / P)‖ + (m : ℝ) / ((P : ℝ) * (P : ℝ)) := by
    have hfull : spolyA (ellLin (liouChi χ)) t (m / P)
        = (∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => P ∣ k),
            ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I))
          + ∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => ¬ P ∣ k),
              ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I) := by
      unfold spolyA
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have heq : (∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => ¬ P ∣ k),
          ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I))
        = spolyA (ellLin (liouChi χ)) t (m / P)
          - ∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => P ∣ k),
              ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I) := by
      rw [hfull]; ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    have hc := norm_sum_div_cpow_le_card (b := ellLin (liouChi χ)) hl1
      (s := (Finset.Icc 1 (m / P)).filter (fun k => P ∣ k))
      (fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1) t
    linarith
  have hresid : ‖∑ n ∈ (Finset.Icc 1 m).filter (fun n => P * P ∣ n),
        a n / (n : ℂ) ^ ((t : ℂ) * I)‖ ≤ (m : ℝ) / ((P : ℝ) * (P : ℝ)) := by
    have hc := norm_sum_div_cpow_le_card (b := a) ha1
      (s := (Finset.Icc 1 m).filter (fun n => P * P ∣ n))
      (fun n hn => (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1) t
    linarith
  rw [spolyA_dilate_eq χ hP homega hpin t]
  refine (norm_add_le _ _).trans ?_
  have hPunit : ‖((P : ℂ) ^ ((t : ℂ) * I))⁻¹‖ = 1 := by
    rw [norm_inv, norm_natCast_cpow_it hP t, inv_one]
  have hfac : ‖cf P * ((P : ℂ) ^ ((t : ℂ) * I))⁻¹
      * (∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => ¬ P ∣ k),
          ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I))‖
      = ‖cf P‖ * ‖∑ k ∈ (Finset.Icc 1 (m / P)).filter (fun k => ¬ P ∣ k),
          ellLin (liouChi χ) k / (k : ℂ) ^ ((t : ℂ) * I)‖ := by
    rw [norm_mul, norm_mul, hPunit, mul_one]
  rw [hfac]
  have hcf0 : (0 : ℝ) ≤ ‖cf P‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hsieve hcf0, hresid]

/-- **THE FINDING** (`m4_row_cf_block_eq_zero`).  The row's window binder at the block prime,
read at the cofactor `m = 1` (where `ℓ(1) = 1`), forces `X_d ≤ P` unless `cf P = 0`.  Since
the row also carries `P < X_d`, the block coefficient VANISHES at every instance. -/
theorem m4_row_cf_block_eq_zero {q : ℕ} (χ : DirichletCharacter ℂ q) {P : ℕ} {Xd : ℝ}
    {cf : ℕ → ℂ} (hP : P.Prime) (hPXd : (P : ℝ) < Xd)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → cf p * ellLin (liouChi χ) m ≠ 0 →
        Xd ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * Xd) :
    cf P = 0 := by
  by_contra hc
  have hl1 : ellLin (liouChi χ) 1 = 1 := by simp [ellLin]
  have hne : cf P * ellLin (liouChi χ) 1 ≠ 0 := by rw [hl1, mul_one]; exact hc
  have hle := (hwin P 1 hP le_rfl le_rfl hne).1
  simp only [Nat.cast_one, mul_one] at hle
  linarith

/-- With the block coefficient vanishing, the pin forces `a` to live on `P²ℕ`. -/
theorem m4_row_supp_sq {q P : ℕ} {χ : DirichletCharacter ℂ q} {a cf : ℕ → ℂ}
    (hcf0 : cf P = 0)
    (homega : ∀ n : ℕ, a n ≠ 0 → P ∣ n)
    (hpin : ∀ k : ℕ, ¬ P ∣ k → a (P * k) = ellLin (liouChi χ) k * cf P) :
    ∀ n : ℕ, a n ≠ 0 → P * P ∣ n := by
  intro n hn
  obtain ⟨k, rfl⟩ := homega n hn
  by_cases hk : P ∣ k
  · exact mul_dvd_mul_left P hk
  · exact absurd (by rw [hpin k hk, hcf0, mul_zero]) hn

/-- **THE GENERAL DILATION EXIT** (`m4_hT0band_of_dilated_sup`).  The `hT0band` slot at the
row's own `a`, from the UNSIEVED sup at the dilated scale.  This is the supplier the dilation
route was designed for: `hdil` is exactly the shape `cfb_sup_of_center` produces at scale
`X/P`, and `hgate` is the one grade comparison, `S₁/P + 2/P² ≤ 2(C₁E + 4P)`. -/
theorem m4_hT0band_of_dilated_sup {q : ℕ} (χ : DirichletCharacter ℂ q)
    {N P : ℕ} {a cf : ℕ → ℂ} {X C₁ M₀ S₁ : ℝ}
    (hX3 : (3 : ℝ) ≤ X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X) (hC₁ : 1 ≤ C₁)
    (hP : 0 < P) (hcf1 : ‖cf P‖ ≤ 1) (hS1 : 0 ≤ S₁) (ha1 : ∀ n, ‖a n‖ ≤ 1)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (homega : ∀ n : ℕ, a n ≠ 0 → P ∣ n)
    (hpin : ∀ k : ℕ, ¬ P ∣ k → a (P * k) = ellLin (liouChi χ) k * cf P)
    (hdil : ∀ t : ℝ, |t| ≤ seamT0 X → ∀ K : ℕ, K ≤ N / P →
        ‖spolyA (ellLin (liouChi χ)) t K‖ ≤ S₁ * (K : ℝ))
    (hgate : S₁ / (P : ℝ) + 2 / ((P : ℝ) * (P : ℝ))
        ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
            + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)))
    (hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)) :
    (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hS0 : (0 : ℝ) ≤ S₁ / (P : ℝ) + 2 / ((P : ℝ) * (P : ℝ)) := by positivity
  refine cfb_t0band_supply_of_sup hX3 hXN hN2 hC₁ hsupp hS0 hgate ?_ hErr
  intro t ht m hm
  have hbase := norm_spolyA_dilate_le χ hP ha1 homega hpin (m := m) t
  have hdil' : ‖spolyA (ellLin (liouChi χ)) t (m / P)‖ ≤ S₁ * ((m / P : ℕ) : ℝ) :=
    hdil t ht (m / P) (Nat.div_le_div_right hm)
  have hcast : (((m / P : ℕ)) : ℝ) ≤ (m : ℝ) / (P : ℝ) := Nat.cast_div_le
  have hcast' : S₁ * (((m / P : ℕ)) : ℝ) ≤ S₁ * ((m : ℝ) / (P : ℝ)) :=
    mul_le_mul_of_nonneg_left hcast hS1
  have hmid : ‖cf P‖ * ‖spolyA (ellLin (liouChi χ)) t (m / P)‖
      ≤ S₁ * ((m : ℝ) / (P : ℝ)) := by
    have hsp : (0 : ℝ) ≤ ‖spolyA (ellLin (liouChi χ)) t (m / P)‖ := norm_nonneg _
    nlinarith [hdil', hcast', hsp, norm_nonneg (cf P)]
  have hmp : (0 : ℝ) ≤ (m : ℝ) / ((P : ℝ) * (P : ℝ)) := by positivity
  have hlast : (‖cf P‖ + 1) * ((m : ℝ) / ((P : ℝ) * (P : ℝ)))
      ≤ 2 * ((m : ℝ) / ((P : ℝ) * (P : ℝ))) := by nlinarith [hcf1, hmp]
  calc ‖spolyA a t m‖
      ≤ S₁ * ((m : ℝ) / (P : ℝ)) + 2 * ((m : ℝ) / ((P : ℝ) * (P : ℝ))) := by linarith
    _ = (S₁ / (P : ℝ) + 2 / ((P : ℝ) * (P : ℝ))) * (m : ℝ) := by ring

/-- **THE COMPOSED EXIT (`m4_hT0band_at_row`)** — the `hT0band` slot of
`M4MeanSq.m4_meansq_per_chi_gen` DISCHARGED at the row's own coefficient sequence `a`, under
the row's own binders (`hsupp`, `homega`, `hcoefPin`, the window binder, `ha1`) plus the two
named gates.  The A2-5 seam is closed: no `M4LiveAgree`, no `hDatum`, no `t₀`.

The route is §2–§3's dilation with the main term identically zero (`m4_row_cf_block_eq_zero`):
`a` lives on `P²ℕ`, so the whole polynomial is the trivially-bounded residue, and the ONLY
analytic content left is the numeric gate `M₀ ≤ 4e·log P`, which the row's `P83 X θ₂₉₃ ≤ P`
and `cfbM0 K q X ≤ loglog X` clear with astronomical margin.  See the module docstring. -/
theorem m4_hT0band_at_row {q : ℕ} (χ : DirichletCharacter ℂ q)
    {N P Xd : ℕ} {a cf : ℕ → ℂ} {X h C₁ M₀ : ℝ}
    (hP : P.Prime)
    (hXee : Real.exp (Real.exp 1) ≤ X) (hXd : (Xd : ℝ) = X)
    (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X) (hC₁ : 1 ≤ C₁)
    (hh4 : 4 ≤ h) (hPX : (P : ℝ) ≤ 2 * (X / h))
    (ha1 : ∀ n, ‖a n‖ ≤ 1)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (homega : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P P n)
    (hcoefPin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → ¬ p ∣ m →
        a (p * m) = ellLin (liouChi χ) m * cf p)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → cf p * ellLin (liouChi χ) m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (hM0P : M₀ ≤ 4 * Real.exp 1 * Real.log (P : ℝ))
    (hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)) :
    (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  have hX3 : (3 : ℝ) ≤ X := le_trans exp_exp_one_gt_three.le hXee
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hPpos : 0 < P := hP.pos
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP.one_lt.le
  -- `P < X_d`: the row's own door gates
  have hXh : X / h ≤ X / 4 := by
    rw [div_le_div_iff₀ hh0 (by norm_num : (0 : ℝ) < 4)]
    nlinarith
  have hPXd : (P : ℝ) < (Xd : ℝ) := by rw [hXd]; linarith
  -- THE FINDING, and the `P²`-support it forces
  have hpin : ∀ k : ℕ, ¬ P ∣ k → a (P * k) = ellLin (liouChi χ) k * cf P :=
    fun k hk => hcoefPin P k hP le_rfl le_rfl hk
  have hcf0 : cf P = 0 := m4_row_cf_block_eq_zero χ hP hPXd hwin
  have homega' : ∀ n : ℕ, a n ≠ 0 → P ∣ n :=
    fun n hn => dvd_of_one_le_blockOmega_self (homega n hn)
  -- the sup at `S = 1/P²`
  have hsup : ∀ t : ℝ, |t| ≤ seamT0 X → ∀ m : ℕ, m ≤ N →
      ‖spolyA a t m‖ ≤ (1 / ((P : ℝ) * (P : ℝ))) * (m : ℝ) := by
    intro t _ m _
    have hb := norm_spolyA_dilate_le χ hPpos ha1 homega' hpin (m := m) t
    rw [hcf0, norm_zero] at hb
    calc ‖spolyA a t m‖
        ≤ 0 * ‖spolyA (ellLin (liouChi χ)) t (m / P)‖
          + (0 + 1) * ((m : ℝ) / ((P : ℝ) * (P : ℝ))) := hb
      _ = (1 / ((P : ℝ) * (P : ℝ))) * (m : ℝ) := by ring
  -- the gate: `1/P² ≤ e^{−M₀/(2e)}`
  have hlogP : (0 : ℝ) ≤ Real.log (P : ℝ) := Real.log_nonneg hP1
  have hPP : Real.exp (2 * Real.log (P : ℝ)) = (P : ℝ) * (P : ℝ) := by
    rw [show (2 : ℝ) * Real.log (P : ℝ) = Real.log ((P : ℝ) * (P : ℝ)) by
      rw [Real.log_mul hPR.ne' hPR.ne']; ring]
    exact Real.exp_log (by positivity)
  have hkey : 1 / ((P : ℝ) * (P : ℝ)) ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) := by
    have hrw : 1 / ((P : ℝ) * (P : ℝ)) = Real.exp (-(2 * Real.log (P : ℝ))) := by
      rw [Real.exp_neg, hPP, one_div]
    rw [hrw]
    refine Real.exp_le_exp.mpr ?_
    have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
    have hstep : (1 / (2 * Real.exp 1)) * M₀
        ≤ (1 / (2 * Real.exp 1)) * (4 * Real.exp 1 * Real.log (P : ℝ)) :=
      mul_le_mul_of_nonneg_left hM0P hc0.le
    have heq : (1 / (2 * Real.exp 1)) * (4 * Real.exp 1 * Real.log (P : ℝ))
        = 2 * Real.log (P : ℝ) := by
      have hne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
      field_simp
      ring
    linarith
  have hPw : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hE0 : (0 : ℝ) < Real.exp (-(1 / (2 * Real.exp 1)) * M₀) := Real.exp_pos _
  have hSle : 1 / ((P : ℝ) * (P : ℝ))
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    nlinarith [hkey, hPw, hE0, mul_nonneg (by linarith : (0 : ℝ) ≤ C₁ - 1) hE0.le]
  exact cfb_t0band_supply_of_sup hX3 hXN hN2 hC₁ hsupp (by positivity) hSle hsup hErr

/-- The same exit at the row's OWN two pins (`(X_d : ℝ) = X` and `N = 2·X_d`, `M4MeanSq`'s
`hXd`/`hNXd`) instead of at `thm_a2'_of_rows`' derived window bounds — so the plug into
`m4_meansq_per_chi_gen`'s `hT0band` slot consumes only binders the capstone already carries,
plus the two named gates `hM0P` and `hErr`. -/
theorem m4_hT0band_at_row_pins {q : ℕ} (χ : DirichletCharacter ℂ q)
    {N P Xd : ℕ} {a cf : ℕ → ℂ} {X h C₁ M₀ : ℝ}
    (hP : P.Prime)
    (hXee : Real.exp (Real.exp 1) ≤ X) (hXd : (Xd : ℝ) = X) (hNXd : N = 2 * Xd)
    (hC₁ : 1 ≤ C₁)
    (hh4 : 4 ≤ h) (hPX : (P : ℝ) ≤ 2 * (X / h))
    (ha1 : ∀ n, ‖a n‖ ≤ 1)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (homega : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P P n)
    (hcoefPin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → ¬ p ∣ m →
        a (p * m) = ellLin (liouChi χ) m * cf p)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → cf p * ellLin (liouChi χ) m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (hM0P : M₀ ≤ 4 * Real.exp 1 * Real.log (P : ℝ))
    (hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)) :
    (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  have hX3 : (3 : ℝ) ≤ X := le_trans exp_exp_one_gt_three.le hXee
  have hNR : (N : ℝ) = 2 * X := by rw [hNXd]; push_cast; rw [hXd]
  exact m4_hT0band_at_row χ hP hXee hXd (by rw [hNR]; linarith) (le_of_eq hNR) hC₁ hh4 hPX
    ha1 hsupp homega hcoefPin hwin hM0P hErr

end Salt.MR
