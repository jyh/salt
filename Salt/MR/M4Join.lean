/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4BridgeCover
import Salt.MR.M4BridgePhase
import Salt.MR.M4BridgeIntegral
import Salt.MR.M4BridgeDilate
import Salt.MR.M4Seam

/-!
# `M4Join` — THE M4 WAVE'S CLOSE (`m4_wave_exit`)

The bridge wave (B-1 … B-5) and the SEAM landed six files on 2026-07-28.  This file is the
wave's final flight: it fires the assembled per-block mean square into
`M4BridgeCover.m4_door_contradiction_of_blockMeanSq` and states the end-to-end exit with its
hypothesis register enumerated once, as ⟦THE REGISTER⟧ (§5).

## WHAT IS LANDED HERE

* **§1 ⟦THE WALL⟧** — the capstone binder defect, RE-MEASURED after the authorised repair.
  `M4MeanSq`'s `hcoefPin`/`hcoefBand` are now window-restricted (`M4MeanSq` §3′), and that
  repair is correct and complete on its own terms.  It does **not** dissolve the defect: the
  *window* binder `hwinPin` forces `cf P = 0` on its own, at `m = 1`, with no reference to
  `hcoefPin` at all — which is exactly what `M4Seam.m4_row_cf_block_eq_zero` already proves.
  §1 states that at the capstone's own gates and draws the consequence (`a` lives on `P²ℕ`
  even with the repaired coefficient binder).  This is the wave's remaining structural wall
  and it is named, not worked around.

* **§2 ⟦THE SUP-ROUTE COVER⟧** — B-5's documented residue, landed.  `M4BlockMeanSqSup` is
  `M4BridgeCover.M4BlockMeanSq` at B-2's carrier (`subWindowSup` at the rational `b/q`), and
  `m4_cover_assembly_sup` is the same `integral_door_cover_le_clean` composition at the same
  absolute factor `3`.  B-5's header asked for this repackage "in whichever of the two files
  settles last"; this is that file.

* **§3 ⟦THE BLOCK EXCHANGE⟧** — B-4's per-block exit (`sum_Ioc_absWindowSum_sq_div_le_ladder`,
  the harmonic-weighted block sum) converted into B-5's socket currency (the unweighted block
  sum against the block bottom).  The conversion is `block_weight_exchange_tight` read
  backwards and costs the ladder's factor `2` and nothing else — no `log`, no boundary term
  (⟦THE ENDPOINT LEDGER⟧: at the block's own scale both fits of
  `sum_Ioc_absWindowSum_sq_div_le` are `le_rfl` and `doorLadder_fit`).

* **§4 ⟦THE GRADE⟧** — the composed grade and its pricing into `M4Close.M4GradeGate`, through
  `M4BridgeCover.m4_gradeGate_of_block_pricing`.  Every constant is symbolic.

* **§5 ⟦THE CLOSE⟧** — `m4_wave_exit` and its collision form, plus the sup-route twin.

## ⟦THE GRADE LEDGER⟧ — where each factor is charged

| factor | source | charged in |
|---|---|---|
| `3` | cover count `k` against the normaliser `Z` | `m4_cover_assembly(_sup)` (B-5) |
| `2` | ladder fit `X_i ≤ 2X_{i+1}` (harmonic ↔ flat) | `m4_blockMeanSq_of_rowMeanSq` (§3) |
| `(1 + 2π·arcDen 12 H)²` | drift from `α` to `b/q` | `m4_sievedDoorSq_of_sup` (B-2) |
| `q ≤ arcDen 12 H` | class count in the residue split | NOT charged here — see ⟦THE RESIDUE⟧ |
| `(H + d₀)/H` | dilation's enlarged arc cap | NOT charged here — see ⟦THE RESIDUE⟧ |

The composed grade of the plain route is therefore `3·(2·MS) = 6·MS`, and the pricing gate
is `6·MS H ≤ m4Saving H` — an absolute constant against `W^{−5/2}`, which the margin lemma
(`M4Close`, exponent gap `15 − 11/4`) swallows without noticing.

## ⟦THE RESIDUE⟧ — named precisely, not deferred vaguely

`M4RowMeanSq` (§3) is the wave's remaining input: the mean square of the door's *phased*
sieved datum on one ladder block, in `ThmA2.thm_a2'_of_rows`' own currency
(`1/X·∫_X^{2X} ‖(1/H)·shortSum a (seamS0 N X) y H‖²`, at `X = X_{i+1}`, `N = 2X_{i+1}`,
`h = H`).  It is byte-shaped to `M4MeanSq.m4_meansq_per_chi_gen`'s conclusion, and it is
**not** discharged here.  Two obstructions, both named:

1. ⟦THE WALL⟧ (§1) — the capstone's window binder `hwinPin` forces `cf P = 0`, so its binder
   set hosts only `P²`-supported data.  The door's sieved λ is not `P²`-supported.  Fixing
   this is a statement repair at `hwinPin`'s own consumer chain
   (`FrameWitness.err_at_witness` → `SeamCalibrationK.ramP2mass_direct`), i.e. upstream of
   the M4 wave.  NOT attempted here (not authorised, and Fable/human tier).

2. ⟦THE CLASS PRICING⟧ — the route from a tight-major `α` to the *unsieved dilated* datum
   (B-1's residue split → B-3's dilation at the enlarged cap `arcDen·(H+d₀)/H` → B-2's sup)
   changes the block's index set: the dilation maps a `doorLadder` block `(X_{i+1}, X_i]` to
   `(X_{i+1}/d₀ − 1, X_i/d₀]`, which is NOT a `doorLadder` block of any ladder.  So the class
   pricing cannot be stated as `M4BlockMeanSq` at the dilated scale without a general
   per-interval input; and the non-coprime half is not discharged by the trivial threshold at
   small `d₀` (`trivThresh H d₀ W = H·d₀/W³` needs `d₀² ≳ W³`).  Both are design questions,
   not proof-engineering ones.  NOT attempted here.

## ⟦THE TRAPS RESPECTED⟧

* the four log scales — this file writes `log ω` only (through B-5's two M4-8 lemmas);
  `W = (log H)^{12}` appears only inside `arcDen`/`m4Saving`, never evaluated;
* the `lam` collision — every datum here is `liouvilleC` (through `doorSievedCoeff`), never
  `lam`; no character row is instantiated in this file at all;
* the `t₀`-absence — SEAM's finding stands: no `t₀` appears on the row path, and none is
  written here;
* the half-open convention — every block is `Finset.Ioc`, every window `Ioc n (n+H)`;
* strict gates — `0 < q`, `2 ≤ C`, `R.Hlo ≤ H ≤ R.Hhi` are carried, never weakened.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — ⟦THE WALL⟧: the capstone's window binder, after the repair

`M4MeanSq` §3′ narrowed `hcoefPin`/`hcoefBand` to the support window.  That repair is sound
(it is hypothesis-weakening, and the widening lemma re-derives the unrestricted law from the
support data) and it removes the `m = 1` forcing *through the coefficient binder*.

It does not remove the forcing, because the forcing never needed the coefficient binder.
`M4Seam.m4_row_cf_block_eq_zero` derives `cf P = 0` from the **window** binder alone:
`cf P · ℓ(1) ≠ 0` would put `P · 1` inside `[X_d, 2X_d]`, and the row carries `P < X_d`.  The
two statements below say that at the capstone's own gates, and draw the consequence. -/

/-- **THE WALL, at the capstone's own gates** (`m4_capstone_window_forces_cf_zero`).
`M4MeanSq.m4_meansq_per_chi_gen` carries `hh4 : 4 ≤ h`, `hPX : (P:ℝ) ≤ 2(X/h)` and the pin
`hXd : (X_d : ℝ) = X`.  Together they give `P ≤ X/2 < X = X_d`, and then the capstone's own
`hwinPin` — untouched by the §3′ repair — forces the block coefficient to vanish.

So the repaired binder set STILL cannot host a datum with `cf P ≠ 0`.  The `P`-exact
factorisation `a(P·m) = ℓ(m)·cf P` is available only in its degenerate reading. -/
theorem m4_capstone_window_forces_cf_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {P Xd : ℕ} {cf : ℕ → ℂ} {X h : ℝ}
    (hP : P.Prime) (hXd : (Xd : ℝ) = X) (hX0 : 0 < X) (hh4 : 4 ≤ h)
    (hPX : (P : ℝ) ≤ 2 * (X / h))
    (hwinPin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → cf p * ellLin (liouChi χ) m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) :
    cf P = 0 := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hXh : X / h ≤ X / 4 := by
    rw [div_le_div_iff₀ hh0 (by norm_num : (0 : ℝ) < 4)]
    nlinarith
  have hPXd : (P : ℝ) < (Xd : ℝ) := by rw [hXd]; linarith
  exact m4_row_cf_block_eq_zero χ hP hPXd hwinPin

/-- **THE CONSEQUENCE** (`m4_capstone_row_supp_sq`).  With `cf P = 0` forced, the capstone's
data are supported on `P²ℕ` — and this survives the §3′ repair, because the narrowed
coefficient binder is applied only at points of `a`'s own support, which `hasupp` places
inside the window where the narrowed binder lives.

(This is `M4Seam.m4_row_supp_sq` re-proved at the *window-restricted* coefficient binder: the
window hypothesis is discharged by `hasupp`, so nothing is lost by the narrowing.) -/
theorem m4_capstone_row_supp_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {P Xd : ℕ} {a cf : ℕ → ℂ} (hP : P.Prime) (hcf0 : cf P = 0)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (homega : ∀ n : ℕ, a n ≠ 0 → 1 ≤ blockOmega P P n)
    (hcoefPin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ P → ¬ p ∣ m →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
      a (p * m) = ellLin (liouChi χ) m * cf p) :
    ∀ n : ℕ, a n ≠ 0 → P * P ∣ n := by
  intro n hn
  obtain ⟨k, rfl⟩ := dvd_of_one_le_blockOmega_self (homega n hn)
  by_cases hk : P ∣ k
  · exact mul_dvd_mul_left P hk
  · exfalso
    obtain ⟨hlo, hhi⟩ := hasupp _ hn
    have hloR : (Xd : ℝ) ≤ (P : ℝ) * (k : ℝ) := by
      have : ((Xd : ℕ) : ℝ) ≤ ((P * k : ℕ) : ℝ) := by exact_mod_cast hlo
      push_cast at this
      linarith
    have hhiR : (P : ℝ) * (k : ℝ) ≤ 2 * (Xd : ℝ) := by
      have : ((P * k : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast hhi
      push_cast at this
      linarith
    exact hn (by rw [hcoefPin P k hP le_rfl le_rfl hk hloR hhiR, hcf0, mul_zero])

/-! ## §2 — ⟦THE SUP-ROUTE COVER⟧ (B-5's documented residue, landed)

`M4BridgeCover`'s ⟦THE SUP ROUTE⟧ header: "§3's `integral_door_cover_le` is stated at a
**general nonnegative `g : ℕ → ℝ`**, so it applies verbatim at
`g n := (subWindowSup (1_𝒮·λ) H n (b/q))²` — the covering side of the sup route needs no new
lemma, only the ~20-line repackaging of §4 (`M4BlockMeanSqSup` ⟹ `M4SievedDoorSqSup`, same
factor `3`)."  Here it is. -/

/-- **THE PER-BLOCK MEAN SQUARE, AT B-2's CARRIER** (`M4BlockMeanSqSup`).
`M4BridgeCover.M4BlockMeanSq` with the two changes that define the sup route
(`M4BridgePhase.M4SievedDoorSqSup`'s own two):

* the frequency is the RATIONAL `b/q` with `0 < q ≤ arcDen 12 H`, not the tight-major `α`;
* the integrand is the sup over sub-window lengths `K ≤ H`, not the full window sum.

The blocks, the count `k` and the right-hand side (`grade × H² × block bottom`) are
`M4BlockMeanSq`'s, unchanged. -/
def M4BlockMeanSqSup (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ Bblk H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **`m4_cover_assembly_sup` — THE SUP ROUTE'S COVERING SIDE.**  `M4BridgeCover`'s §4 at
B-2's carrier: the same `integral_door_cover_le_clean`, the same door-gate bundle, the same
absolute factor `3` (the cover count `k` against the door normaliser `Z`).

Nothing about the covering argument depends on what the nonnegative integrand *is*, which is
precisely why B-5 could state its §3 at a free `g` and defer this repackage. -/
theorem m4_cover_assembly_sup {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqSup R M k Bblk) :
    M4SievedDoorSqSup R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (H : ℝ) ^ 2 := mul_nonneg (hB0 H) (by positivity)
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2)
    (P := Bblk H * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ)
  simp only [doorSievedCoeff] at hmain
  have heq : 3 * (Bblk H * (H : ℝ) ^ 2) = 3 * Bblk H * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  exact hmain

/-- **THE SUP-ROUTE BLOCK HYPOTHESIS IS INHABITED** (the anti-vacuity duty, mirroring
`M4BridgeCover.m4_blockMeanSq_trivial` and `M4BridgePhase.m4_sievedDoorSqSup_trivial`).  At
the trivial grade `B_blk ≡ 1` every sub-window carries at most `H` terms of modulus `≤ 1`, so
the sup is `≤ H`, its square `≤ H²`, and the block's cardinality is `≤ X_{i+1}`. -/
theorem m4_blockMeanSqSup_trivial (R : ChowlaRegime) (M k : ℕ) :
    M4BlockMeanSqSup R M k (fun _ => 1) := by
  intro H _ hhi b q _ _ i _
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2 ≤ (H : ℝ) ^ 2 := by
    intro n _
    have h := subWindowSup_le_of_norm_le_one (a := doorSievedCoeff M)
      (norm_doorSievedCoeff_le_one M) H n ((b : ℝ) / (q : ℝ))
    have h0 := subWindowSup_nonneg (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))
    nlinarith
  have hcard : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * (H : ℝ) ^ 2 := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i), (H : ℝ) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * (H : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  nlinarith

/-! ## §3 — ⟦THE BLOCK EXCHANGE⟧: B-4's currency into B-5's socket

B-4 exits at the **harmonic-weighted** block sum `∑ ‖W(n)‖²/n ≤ H²·MS` (that is the shape the
`thm_a2'` mean square natively delivers, because `logMeasure`'s `1/n` and `thm_a2'`'s `1/X`
cancel at `X = X_{i+1}`).  B-5's socket wants the **flat** block sum against the block bottom.
`block_weight_exchange_tight` is the exchange, and by the ladder's fit it costs the factor
`2` — no `log`, and (⟦THE ENDPOINT LEDGER⟧) no boundary term at all. -/

/-- **THE EXCHANGE, backwards** (`sum_Ioc_le_two_mul_of_harmonic`).  A harmonic-weighted block
bound becomes a flat block bound against the block bottom, at the ladder's factor `2`. -/
theorem sum_Ioc_le_two_mul_of_harmonic {x H i : ℕ} {f : ℕ → ℝ} {V : ℝ} (hxH : H + 1 ≤ x)
    (hf : ∀ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), 0 ≤ f n)
    (hh : ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n / (n : ℝ) ≤ V) :
    ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n
      ≤ 2 * V * (doorLadder x H (i + 1) : ℝ) := by
  have hX1 : (0 : ℝ) < (doorLadder x H (i + 1) : ℝ) := doorLadder_pos hxH (i + 1)
  have hrw : ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n * (n : ℝ)⁻¹
      = ∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n / (n : ℝ) :=
    Finset.sum_congr rfl fun n _ => by rw [div_eq_mul_inv]
  have htight := block_weight_exchange_tight (x := x) (H := H) (i := i) (f := f) hxH hf
  rw [hrw] at htight
  have hstep : (∑ n ∈ Finset.Ioc (doorLadder x H (i + 1)) (doorLadder x H i), f n)
      / (2 * (doorLadder x H (i + 1) : ℝ)) ≤ V := le_trans htight hh
  rw [div_le_iff₀ (by positivity)] at hstep
  linarith

/-- **THE WAVE'S REMAINING INPUT** (`M4RowMeanSq`) — the mean square of the door's PHASED
sieved datum on one ladder block, in `ThmA2.thm_a2'_of_rows`' own currency.

The instantiation is forced, not chosen: at the block `(X_{i+1}, X_i]` the fits of
`M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` read `X := X_{i+1}` (`le_rfl`) and
`X_i + H ≤ 2X_{i+1}` (`doorLadder_fit`), and the index set is `seamS0 (2X_{i+1}) X_{i+1}` —
so `N = 2X_d`, `X_d = X`, which are exactly `M4MeanSq.m4_meansq_per_chi_gen`'s two pins.  The
window length `h` is the door's own `H`.

This predicate is the wave's ⟦RESIDUE⟧: see the module header for the two obstructions that
keep it from being discharged from `m4_meansq_per_chi_gen` today. -/
def M4RowMeanSq (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ, NearRatTight (arcDen 12 H) H α → ∀ i < k,
    1 / (doorLadder R.x H (i + 1) : ℝ)
        * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
            ‖((1 / (H : ℝ) : ℝ) : ℂ)
                * shortSum (doorCoeffPhase (doorSievedCoeff M) α)
                    (seamS0 (2 * doorLadder R.x H (i + 1))
                      (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H

/-- **§3's EXIT** (`m4_blockMeanSq_of_rowMeanSq`).  The row input, block by block, IS
`M4BridgeCover.M4BlockMeanSq` at the grade `2·MS` — B-4's ladder lemma (the coverage datum
discharged by `hcov_of_seamS0`, both fits by the ladder) followed by §3's exchange.

`0 < H` is free: `R.Hlo ≤ H` and `R.hHlo_floor` give `H ≥ 4·10⁶`. -/
theorem m4_blockMeanSq_of_rowMeanSq {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℝ}
    (hrow : M4RowMeanSq R M k MS) :
    M4BlockMeanSq R M k (fun H => 2 * MS H) := by
  intro H hlo hhi α harc i hik
  have hH0 : 0 < H := by
    have := R.hHlo_floor
    omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  -- ⟦the coverage datum is free at the block's own seam index set⟧
  have hcov : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ∀ m ∈ Finset.Ioc n (n + H), m ∉ seamS0 (2 * doorLadder R.x H (i + 1))
          (doorLadder R.x H (i + 1) : ℝ) → doorSievedCoeff M m = 0 :=
    hcov_of_seamS0 (doorSievedCoeff M) (A := doorLadder R.x H (i + 1))
      (B := doorLadder R.x H i) (N := 2 * doorLadder R.x H (i + 1)) (H := H) le_rfl
      (by omega)
  -- ⟦B-4: the harmonic-weighted block bound⟧
  have hladder := sum_Ioc_absWindowSum_sq_div_le_ladder (doorSievedCoeff M)
    (seamS0 (2 * doorLadder R.x H (i + 1)) (doorLadder R.x H (i + 1) : ℝ)) α
    (x := R.x) (H := H) (i := i) (MS := MS H) hH0 hxH hcov (hrow H hlo hhi α harc i hik)
  -- ⟦§3: the exchange⟧
  have hflat := sum_Ioc_le_two_mul_of_harmonic (x := R.x) (H := H) (i := i)
    (f := fun n => ‖absWindowSum (doorSievedCoeff M) H n α‖ ^ 2)
    (V := (H : ℝ) ^ 2 * MS H) hxH (fun n _ => by positivity) hladder
  have heq : 2 * ((H : ℝ) ^ 2 * MS H) * (doorLadder R.x H (i + 1) : ℝ)
      = 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring
  rw [heq] at hflat
  exact hflat

/-- The composed grade is a grade (`M4BlockMeanSq`'s and the join's `hB0` slot). -/
theorem m4_blockGrade_nonneg {MS : ℕ → ℝ} (hMS : ∀ H : ℕ, 0 ≤ MS H) (H : ℕ) :
    0 ≤ 2 * MS H := by have := hMS H; linarith

/-! ## §4 — ⟦THE GRADE⟧

The plain route's composed grade is `3·(2·MS) = 6·MS`: the cover's `3` (B-5) times the
exchange's `2` (§3).  `M4BridgeCover.m4_gradeGate_of_block_pricing` is the gate at the
assembly's output grade, so the pricing demand is `6·MS H ≤ m4Saving H`. -/

/-- **THE PRICING, at the wave's composed grade** (`m4_wave_gradeGate`).  `M4Close.M4GradeGate`
at `3·(2·MS)`, from the absolute pricing `6·MS H ≤ m4Saving H` and the door's own two terms
against the other half of the budget.  The halving needs `2 ≤ C` (the grade is linear in `C`).
-/
theorem m4_wave_gradeGate {R : ChowlaRegime} {C δ : ℝ} {MS : ℕ → ℝ} {k : ℕ}
    (hC : 2 ≤ C)
    (hprice : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 6 * MS H ≤ m4Saving H)
    (hrest : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) :
    M4GradeGate R C δ (fun H => 3 * (2 * MS H)) k :=
  m4_gradeGate_of_block_pricing (Bblk := fun H => 2 * MS H) hC
    (fun H hlo hhi => by have := hprice H hlo hhi; linarith) hrest

/-! ## §5 — ⟦THE CLOSE⟧

`M4BridgeCover.m4_door_contradiction_of_blockMeanSq` carries `M4BlockMeanSq` as a hypothesis;
§3 discharges it from `M4RowMeanSq`, §4 supplies the budget line.  Composing them is the M4
wave end to end. -/

/-- **`m4_wave_exit` — THE M4 WAVE'S CLOSE.**

For every `C_MRT ≥ 2` and every floor / outer-scale demand there is a regime `R` at which
**log-Chowla-2 does not fail**, conditional on exactly ⟦THE REGISTER⟧ below — and on nothing
else.  This list is what the S11 spine compose must clear.

⟦THE REGISTER⟧

1. **`M4DoorGates Cg R M k δ`** — M4-8's door-glue list at the regime: `1 ≤ M`, `0 < δ`, the
   `M`-gate `24·Cg/δ ≤ M`, the absorption floor `4 ≤ log ω`, the ladder's three gates
   (`2^{k+1} ≤ x`, the cover count `k ≤ log ω/log 2 + 2`, `hreach`), and HS-3's per-block
   sieve bundle.  Witness at `k := doorCount R.ω`: `M4Door.doorCount_gates`.
   *SCALE/REGIME data — owed by the door numerology, not by analysis.*
2. **`∀ H, 0 ≤ MS H`** — the row grade is a grade.  *DATA.*
3. **`2 ≤ C`** — the budget halving (`mrtDeliveredGrade` is linear in `C`). *SCALE.*
4. **`∀ H ∈ [Hlo, Hhi], 6·MS H ≤ m4Saving H`** — THE PRICING: the row grade, after the
   cover's `3` and the exchange's `2`, under the quality demand's `W^{−5/2}` saving.
   *REGIME — the analytic content of the whole wave, as one inequality.*
5. **`∀ H ∈ [Hlo, Hhi], δ/4 + 4·2^k/x ≤ mrtDeliveredGrade (C/2) H`** — the door's own two
   grades against the other half of the budget.  *SCALE/REGIME.*
6. **`M4RowMeanSq R M k MS`** — THE ROW INPUT: the per-block mean square of the phased sieved
   datum, in `thm_a2'`'s own currency.  *THE WAVE'S RESIDUE* (module header, ⟦THE RESIDUE⟧).

Nothing else: the arc, the budget head, the collision, the sieve insert, the harmonic cover,
the `log ω` absorption, the `L²→L¹` descent, the block exchange and the grade gate are all
landed and consumed. -/
theorem m4_wave_exit :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 2 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (MS : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ MS H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 6 * MS H ≤ m4Saving H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4RowMeanSq R M k MS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_blockMeanSq
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C (by linarith) U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ MS M k hgates hMS0 hprice hrest hrow => ?_⟩
  exact hR δ (fun H => 2 * MS H) M k hgates (m4_blockGrade_nonneg hMS0)
    (m4_wave_gradeGate hC hprice hrest) (m4_blockMeanSq_of_rowMeanSq hrow)

/-- **The close's collision form** (`m4_wave_False`).  Same register; with the failure branch
assumed at the exit's regime the chain closes to `False`. -/
theorem m4_wave_False :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 2 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (MS : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ MS H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 6 * MS H ≤ m4Saving H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4RowMeanSq R M k MS →
              logChowla2Fails R.eps R.x R.ω → False := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_False_of_blockMeanSq
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C (by linarith) U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ MS M k hgates hMS0 hprice hrest hrow => ?_⟩
  exact hR δ (fun H => 2 * MS H) M k hgates (m4_blockGrade_nonneg hMS0)
    (m4_wave_gradeGate hC hprice hrest) (m4_blockMeanSq_of_rowMeanSq hrow)

/-- **THE SUP-ROUTE CLOSE** (`m4_wave_exit_sup`).  The same wave exit entered at B-2's
carrier: `M4BlockMeanSqSup` → (§2) `M4SievedDoorSqSup` → (B-2's `m4_sievedDoorSq_of_sup`)
`M4SievedDoorSq` → `M4Close.m4_door_contradiction_of_live`.

⟦THE REGISTER, sup form⟧ items 1–3 and 5 of `m4_wave_exit` unchanged; items 4 and 6 become

4′. `M4GradeGate R C δ Braw k` with the DRIFT PRICE paid explicitly:
    `(1 + 2π·arcDen 12 H)²·(3·B_blk H) ≤ Braw H` on the window range (`hdrift`), and
6′. `M4BlockMeanSqSup R M k B_blk` — the per-block sup mean square at the rationals.

The drift price is B-2's and is charged here rather than folded into the grade, because the
sup route's whole point is that the frequency is rational when the mean square is taken. -/
theorem m4_wave_exit_sup :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bblk : ℕ → ℝ) (M k : ℕ),
            M4DoorGates Cg R M k δ → (∀ H : ℕ, 0 ≤ Bblk H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              (1 + 2 * Real.pi * arcDen 12 H) ^ 2 * (3 * Bblk H) ≤ Braw H) →
            M4GradeGate R C δ Braw k →
            M4BlockMeanSqSup R M k Bblk →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg,
    fun δ Braw Bblk M k hgates hB0 hBraw0 hdrift hgrade hblk => ?_⟩
  exact hR δ Braw M k hgates hBraw0 hgrade
    (m4_sievedDoorSq_of_sup hdrift (m4_cover_assembly_sup hgates hB0 hblk))

end Salt.MR

end
