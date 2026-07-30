/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ChiSummed

/-!
# ⟦D-3⟧ — THE STRATIFIED GAUSS CONSUMER (`M4Gauss`)

Wave ④ stage S-3 of the second-road freeze v2.  This file is where the second road's saving
actually happens: the exponential sum at a rational `b/q` is priced by the **Gauss sum's own
second moment** instead of by the class count.

## ⟦THE `q²` AND WHY IT DIES HERE⟧

`M4ClassPrice` §4 prices `‖∑_{m ∈ W} a(m)e(bm/q)‖` by splitting `W` into `q` residue
classes and Cauchy–Schwarzing the split: `q` classes squared is the `q²` of ⟦F2⟧'s wall.
The classical route does not split.  For the part of the window coprime to `q`:

```
   ∑_{(m,q)=1} a(m)e(bm/q)  =  (1/φ(q))·∑_χ τ_b(χ)·(∑_m a(m)χ̄(m)) ,
   τ_b(χ) := ∑_{(r,q)=1} χ(r)e(br/q)     (the Gauss sum),
```

and Cauchy–Schwarz over `χ` costs `(∑_χ ‖τ_b(χ)‖²)^{1/2} = φ(q)` — which cancels the
`1/φ(q)` EXACTLY:

```
   ‖∑_{(m,q)=1} a(m)e(bm/q)‖²  ≤  ∑_χ ‖∑_m a(m)χ̄(m)‖²      (§2, prefactor 1).
```

**⟦THE SECOND MOMENT IS EXACT AT EVERY `b`⟧** — `∑_χ ‖τ_b(χ)‖² = φ(q)²` for EVERY `b : ℤ`,
including `gcd(b,q) > 1` (§1).  The proof is the double sum with the unit-indicator
collapse, so no primitivity, no `‖τ‖ = √q`, and no coprimality hypothesis on `b` is ever
needed — which matters, because `NearRatTight` hands out whatever `b` it likes.

## ⟦THE STRATIFICATION⟧ — the non-coprime residues, one dilation each

The window is not coprime to `q`.  Cut it by `d = gcd(m,q)`: the stratum `d` is the classes
`r` with `gcd(r,q) = d`, and ONE dilation (`M4BridgeDilate.classWindowSum_dilate`, an
EQUALITY, plus `absWindowSum_dilCoeff_memS_door`'s `λ(d)` factorisation) carries it to the
COPRIME residues of the reduced modulus `q/d` on the dilated window
`(⌊n/d⌋, ⌊n/d⌋ + dilLen K n d]` — where §2 fires verbatim.  So:

```
   ‖(the stratum `d`)‖²  ≤  ∑_{χ mod q/d} (doorChiSup χ M (L/d+1) ⌊n/d⌋)²      (§4)
```

⟦THE PER-STRATUM SHAPE IS DELIBERATE⟧ §4 is stated as its own lemma, per stratum, priced
against the stratum's OWN dilated length `L/d + 1` — NOT as one summed inequality against a
single budget.  Wave ⑤'s `D₀`-truncation replaces the strata `d > D₀` by the landed trivial
bound (`M4BridgeDilate.norm_classWindowSum_le_thresh`, gate-free) and needs exactly this
granularity to do so without re-opening §5's sum.

The strata are recombined by the WEIGHTED Cauchy–Schwarz at `1/d` (§5): the weight is what
turns the per-stratum ledger's `1/d²` decay (`M4NonCoprime.d0_ledger_sharp`, banked unspent
by the first road) into the residual `(∑_{d ∣ q} 1/d)² = (σ(q)/q)²`, an `H`-only quantity
bounded by `(1 + log(arcDen 12 H))²` — never a power of `q`.

## Contents

* §1 THE GAUSS SUM AND ITS SECOND MOMENT — `chiGaussSum`, `sum_normSq_chiGaussSum`.
* §2 THE COPRIME EXPANSION, AT ANY MODULUS — `coprime_window_expansion`,
  `norm_sq_coprime_window_le` (prefactor `1`).
* §3 THE STRATUM RE-INDEX — the fibres of `r ↦ gcd(r,q)`, and the dilation of one class.
* §4 THE PER-STRATUM BOUND — `stratum_sq_le_chiSummed`.
* §5 THE WEIGHTED RECOMBINATION — `subWindowSup_sq_le_strata` and the block form.

## ⟦THE TRAPS RESPECTED⟧

* the dilation gate is the `M`-RELATIVE one (`d ≤ q ≤ W < calP (Adoor M) (3072M) 1`,
  `M4Residue.door_dilation_gate'`'s genre) — the numeral `log H ≤ 2^{21845}` (an H-UPPER,
  ⟦WALL C⟧'s genre) is NEVER demanded: every dilation below routes through
  `M4BridgeDilate.classWindowSum_dilate` / `absWindowSum_dilCoeff_memS_door`, whose
  hypothesis is `hW : W < P₁` with `W` a FREE ceiling;
* the frequency is the RATIONAL `b/q` on the outside and the reduced rational `b/(q/d)`
  inside the stratum — the residual frequency is `0` throughout, so no arc datum is
  transported and no enlarged cap is incurred;
* `liouChi`, never `lamChi`; the datum is `doorSievedCoeff M` outside and
  `doorChiCoeff χ M` (through `doorSievedWindow`) inside;
* half-open windows and blocks throughout; strict gates never weakened.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE GAUSS SUM AND ITS SECOND MOMENT -/

/-- **THE GAUSS SUM** `τ_b(χ) = ∑_{r < q, (r,q)=1} χ(r)·e(br/q)`, at the corpus's own
rational phase `M4BridgeResidue.ratPhase`.

The sum runs over the coprime residues explicitly (rather than over all of `range q` with
`χ` vanishing off the units), so no `MulChar.map_nonunit` is needed and the diagonal count
is `Nat.totient`'s own definition. -/
def chiGaussSum {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ) : ℂ :=
  ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
    χ ((r : ℕ) : ZMod q) * ratPhase b q r

/-- `‖z‖²` as a complex product — the one cast used in §1. -/
private theorem normSq_cast_eq_mul_conj (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **THE GAUSS SUM'S SECOND MOMENT, EXACT AND AT EVERY `b`** —
`∑_χ ‖τ_b(χ)‖² = φ(q)²`.

The double sum `∑_{r,r'} e(b(r−r')/q)·∑_χ χ(r)χ̄(r')` collapses on the diagonal by
`M4Chars.sum_chi_mul_conj_chi` (the coefficient side is a unit because `r` is coprime), and
the diagonal has `φ(q)` terms each of modulus `1`.

⟦NO HYPOTHESIS ON `b`⟧ — the phases are unimodular constants and cancel against their own
conjugates on the diagonal, so `gcd(b,q) > 1` is not excluded.  This is what lets the
consumer read whatever rational `NearRatTight` produces. -/
theorem sum_normSq_chiGaussSum {q : ℕ} [NeZero q] (b : ℤ) :
    ∑ χ : DirichletCharacter ℂ q, ‖chiGaussSum χ b‖ ^ 2 = ((q.totient : ℕ) : ℝ) ^ 2 := by
  classical
  set F := (Finset.range q).filter (fun r => Nat.Coprime q r) with hF
  have hcardF : F.card = q.totient := by
    rw [hF, Nat.totient]
  have hunit : ∀ r ∈ F, IsUnit ((r : ℕ) : ZMod q) := by
    intro r hr
    exact isUnit_natCast_of_coprime (Finset.mem_filter.mp hr).2
  have hinj : ∀ r ∈ F, ∀ r' ∈ F, ((r : ℕ) : ZMod q) = ((r' : ℕ) : ZMod q) → r = r' := by
    intro r hr r' hr' h
    have hrq : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hr'q : r' < q := Finset.mem_range.mp (Finset.mem_filter.mp hr').1
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt hrq, ZMod.val_natCast_of_lt hr'q] at hv
  -- ⟦the complex identity⟧
  have key : ∑ χ : DirichletCharacter ℂ q,
        chiGaussSum χ b * (starRingEnd ℂ) (chiGaussSum χ b)
      = (((q.totient : ℕ) : ℝ) ^ 2 : ℝ) := by
    have hexp : ∀ χ : DirichletCharacter ℂ q,
        chiGaussSum χ b * (starRingEnd ℂ) (chiGaussSum χ b)
          = ∑ r ∈ F, ∑ r' ∈ F,
              (ratPhase b q r * (starRingEnd ℂ) (ratPhase b q r'))
                * (χ ((r : ℕ) : ZMod q) * (starRingEnd ℂ) (χ ((r' : ℕ) : ZMod q))) := by
      intro χ
      rw [chiGaussSum, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
      rw [map_mul]
      ring
    calc ∑ χ : DirichletCharacter ℂ q,
          chiGaussSum χ b * (starRingEnd ℂ) (chiGaussSum χ b)
        = ∑ χ : DirichletCharacter ℂ q, ∑ r ∈ F, ∑ r' ∈ F,
            (ratPhase b q r * (starRingEnd ℂ) (ratPhase b q r'))
              * (χ ((r : ℕ) : ZMod q) * (starRingEnd ℂ) (χ ((r' : ℕ) : ZMod q))) :=
          Finset.sum_congr rfl fun χ _ => hexp χ
      _ = ∑ r ∈ F, ∑ r' ∈ F, ∑ χ : DirichletCharacter ℂ q,
            (ratPhase b q r * (starRingEnd ℂ) (ratPhase b q r'))
              * (χ ((r : ℕ) : ZMod q) * (starRingEnd ℂ) (χ ((r' : ℕ) : ZMod q))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ r ∈ F, ∑ r' ∈ F,
            (ratPhase b q r * (starRingEnd ℂ) (ratPhase b q r'))
              * (if ((r : ℕ) : ZMod q) = ((r' : ℕ) : ZMod q) then ((q.totient : ℕ) : ℂ)
                  else 0) := by
          refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun r' _ => ?_
          rw [← Finset.mul_sum, sum_chi_mul_conj_chi (hunit r hr)]
      _ = ∑ r ∈ F, ∑ r' ∈ F,
            (ratPhase b q r * (starRingEnd ℂ) (ratPhase b q r'))
              * (if r = r' then ((q.totient : ℕ) : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun r' hr' => ?_
          by_cases hrr : r = r'
          · rw [if_pos hrr, if_pos (by rw [hrr])]
          · rw [if_neg hrr, if_neg (fun h => hrr (hinj r hr r' hr' h))]
      _ = ∑ r ∈ F, (ratPhase b q r * (starRingEnd ℂ) (ratPhase b q r))
              * ((q.totient : ℕ) : ℂ) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.sum_eq_single r]
          · rw [if_pos rfl]
          · intro r' _ hne
            rw [if_neg (fun h => hne h.symm), mul_zero]
          · intro hmem
            exact absurd hr hmem
      _ = (((q.totient : ℕ) : ℝ) ^ 2 : ℝ) := by
          have hone : ∀ r ∈ F,
              (ratPhase b q r * (starRingEnd ℂ) (ratPhase b q r)) * ((q.totient : ℕ) : ℂ)
                = ((q.totient : ℕ) : ℂ) := by
            intro r _
            have h := normSq_cast_eq_mul_conj (ratPhase b q r)
            rw [norm_ratPhase] at h
            have hmod : ratPhase b q r * (starRingEnd ℂ) (ratPhase b q r) = 1 := by
              simpa using h.symm
            rw [hmod, one_mul]
          rw [Finset.sum_congr rfl hone, Finset.sum_const, hcardF, nsmul_eq_mul]
          push_cast
          ring
  -- ⟦the real form⟧
  have hreal : ((∑ χ : DirichletCharacter ℂ q, ‖chiGaussSum χ b‖ ^ 2 : ℝ) : ℂ)
      = (((q.totient : ℕ) : ℝ) ^ 2 : ℝ) := by
    rw [← key, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun χ _ => normSq_cast_eq_mul_conj (chiGaussSum χ b)
  exact_mod_cast hreal

/-! ## §2 — THE COPRIME EXPANSION, AT ANY MODULUS

The window's coprime part, expanded over characters and then Cauchy–Schwarzed against §1.
The `1/φ(q)` and the `φ(q)` of the second moment cancel: **prefactor `1`**. -/

/-- **THE COPRIME EXPANSION** — the coprime residues of the door's sieved window at the
rational `b/q`, folded into the Gauss sums and the χ-twisted window sums.

`M4ClassPrice.sum_windowClass_memSCoeff` (the two filters commute) then
`M4BridgeResidue.sum_residueClassOn_liou_eq` (the character decomposition), then the two
sums exchanged.  An EQUALITY — nothing is estimated. -/
theorem coprime_window_expansion {q : ℕ} [NeZero q] (M K n : ℕ) (b : ℤ) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m
      = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          chiGaussSum χ b * ∑ m ∈ doorSievedWindow M K n, liouChi χ m := by
  classical
  have hclass : ∀ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
      ∑ m ∈ windowClass K n q r, doorSievedCoeff M m
        = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow M K n, liouChi χ m := by
    intro r hr
    have hcop : Nat.Coprime q r := (Finset.mem_filter.mp hr).2
    have hfilt : ∑ m ∈ windowClass K n q r, doorSievedCoeff M m
        = ∑ m ∈ residueClassOn q r (doorSievedWindow M K n), liouvilleC m := by
      simpa only [doorSievedCoeff, doorSievedWindow] using
        sum_windowClass_memSCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 liouvilleC K n q r
    rw [hfilt]
    exact sum_residueClassOn_liou_eq hcop (doorSievedWindow M K n)
  have hstep : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
          ratPhase b q r * (((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow M K n, liouChi χ m) :=
    Finset.sum_congr rfl fun r hr => by rw [hclass r hr]
  rw [hstep]
  calc ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * (((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow M K n, liouChi χ m)
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
          ∑ χ : DirichletCharacter ℂ q, ((q.totient : ℕ) : ℂ)⁻¹
            * ((ratPhase b q r * χ ((r : ℕ) : ZMod q))
              * ∑ m ∈ doorSievedWindow M K n, liouChi χ m) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ _ => by ring
    _ = ∑ χ : DirichletCharacter ℂ q,
          ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
            ((q.totient : ℕ) : ℂ)⁻¹
              * ((ratPhase b q r * χ ((r : ℕ) : ZMod q))
                * ∑ m ∈ doorSievedWindow M K n, liouChi χ m) := Finset.sum_comm
    _ = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          chiGaussSum χ b * ∑ m ∈ doorSievedWindow M K n, liouChi χ m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [chiGaussSum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring

/-- **THE CAUCHY–SCHWARZ STEP, AT PREFACTOR `1`** — for ANY family `S : χ ↦ ℂ`,

`‖(1/φ(q))·∑_χ τ_b(χ)·S(χ)‖² ≤ ∑_χ ‖S(χ)‖²`.

The `φ(q)²` of the second moment (§1) cancels the `1/φ(q)²` of the expansion EXACTLY; no
`q` and no `√q` survives.  This single inequality is the whole difference between the second
road and ⟦F2⟧'s `q²`. -/
theorem norm_sq_inv_totient_gauss_le {q : ℕ} [NeZero q] (b : ℤ)
    (S : DirichletCharacter ℂ q → ℂ) :
    ‖((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, chiGaussSum χ b * S χ‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖S χ‖ ^ 2 := by
  classical
  have hφ : (0 : ℝ) < ((q.totient : ℕ) : ℝ) := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast this
  -- ⟦the triangle inequality, then the real Cauchy–Schwarz⟧
  have htri : ‖∑ χ : DirichletCharacter ℂ q, chiGaussSum χ b * S χ‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖chiGaussSum χ b‖ * ‖S χ‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun χ _ => norm_mul _ _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun χ => ‖chiGaussSum χ b‖) (fun χ => ‖S χ‖)
  rw [sum_normSq_chiGaussSum b] at hcs
  have h0 : (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ q, ‖chiGaussSum χ b‖ * ‖S χ‖ :=
    Finset.sum_nonneg fun χ _ => by positivity
  have hsq : ‖∑ χ : DirichletCharacter ℂ q, chiGaussSum χ b * S χ‖ ^ 2
      ≤ ((q.totient : ℕ) : ℝ) ^ 2 * ∑ χ : DirichletCharacter ℂ q, ‖S χ‖ ^ 2 := by
    have h1 : ‖∑ χ : DirichletCharacter ℂ q, chiGaussSum χ b * S χ‖ ^ 2
        ≤ (∑ χ : DirichletCharacter ℂ q, ‖chiGaussSum χ b‖ * ‖S χ‖) ^ 2 := by
      have hn0 : (0 : ℝ) ≤ ‖∑ χ : DirichletCharacter ℂ q, chiGaussSum χ b * S χ‖ :=
        norm_nonneg _
      nlinarith
    linarith
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow,
    inv_mul_le_iff₀ (by positivity)]
  exact hsq

/-- **THE COPRIME PART OF A WINDOW, SQUARED** (`norm_sq_coprime_window_le`) — §2's headline:
the coprime residues of the door's sieved window at `b/q`, squared, are under the χ-SUM of
the twisted sub-window sups at any cap `Lw ≥ K`.  **Prefactor `1`.** -/
theorem norm_sq_coprime_window_le {q : ℕ} [NeZero q] (M : ℕ) {K Lw : ℕ} (hK : K ≤ Lw)
    (n : ℕ) (b : ℤ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ q, (doorChiSup χ M Lw n) ^ 2 := by
  rw [coprime_window_expansion M K n b]
  refine le_trans (norm_sq_inv_totient_gauss_le b
    (fun χ => ∑ m ∈ doorSievedWindow M K n, liouChi χ m)) ?_
  refine Finset.sum_le_sum fun χ _ => ?_
  have h := le_doorChiSup χ M Lw n hK
  have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow M K n, liouChi χ m‖ := norm_nonneg _
  nlinarith

/-! ## §3 — THE STRATUM RE-INDEX

The residues of `q` cut by `d = gcd(r,q)`, and the fibre `{r : gcd(r,q) = d}` re-indexed onto
the COPRIME residues of `q/d` by `r = d·r₀`.  Pure `Nat` bookkeeping — no estimate. -/

/-- **THE FIBRE, RE-INDEXED.**  `{r < q : gcd(r,q) = d} ≃ {r₀ < q/d : (r₀, q/d) = 1}` via
`r = d·r₀`.  Both directions are `Nat.gcd_mul_left` / `Nat.coprime_div_gcd_div_gcd`. -/
theorem sum_fibre_eq_coprime {q d : ℕ} (hq : 0 < q) (hd0 : 0 < d) (hdq : d ∣ q)
    (f : ℕ → ℂ) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d), f r
      = ∑ r₀ ∈ (Finset.range (q / d)).filter (fun r₀ => Nat.Coprime (q / d) r₀), f (d * r₀) := by
  classical
  have hqd : d * (q / d) = q := Nat.mul_div_cancel' hdq
  have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
  refine Finset.sum_nbij' (i := fun r => r / d) (j := fun r₀ => d * r₀) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    have hmem := Finset.mem_filter.mp hr
    have hrq : r < q := Finset.mem_range.mp hmem.1
    have hgcd : Nat.gcd r q = d := hmem.2
    have hdr : d ∣ r := hgcd ▸ Nat.gcd_dvd_left r q
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have h1 : d * (r / d) < d * (q / d) := by
        rw [Nat.mul_div_cancel' hdr, hqd]; exact hrq
      exact lt_of_mul_lt_mul_left h1 (Nat.zero_le d)
    · have hcop := Nat.coprime_div_gcd_div_gcd (m := r) (n := q) (by rw [hgcd]; exact hd0)
      rw [hgcd] at hcop
      exact hcop.symm
  · intro r₀ hr₀
    have hmem := Finset.mem_filter.mp hr₀
    have hr₀q : r₀ < q / d := Finset.mem_range.mp hmem.1
    have hcop : Nat.Coprime (q / d) r₀ := hmem.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · calc d * r₀ < d * (q / d) := mul_lt_mul_of_pos_left hr₀q hd0
        _ = q := hqd
    · rw [← hqd, Nat.gcd_mul_left]
      have : Nat.gcd r₀ (q / d) = 1 := hcop.symm
      rw [this, Nat.mul_one]
  · intro r hr
    have hmem := Finset.mem_filter.mp hr
    have hgcd : Nat.gcd r q = d := hmem.2
    have hdr : d ∣ r := hgcd ▸ Nat.gcd_dvd_left r q
    exact Nat.mul_div_cancel' hdr
  · intro r₀ _
    exact Nat.mul_div_cancel_left r₀ hd0
  · intro r hr
    have hmem := Finset.mem_filter.mp hr
    have hgcd : Nat.gcd r q = d := hmem.2
    have hdr : d ∣ r := hgcd ▸ Nat.gcd_dvd_left r q
    rw [Nat.mul_div_cancel' hdr]

/-- **THE RATIONAL PHASE IS INVARIANT UNDER THE DILATION** — `e(br/q) = e(br₀/q₀)` at
`r = d·r₀`, `q = d·q₀`.  The dilated frequency `d·(b/q)` IS `b/q₀`, which is why the
stratum's expansion runs at the reduced modulus with the SAME `b`. -/
theorem ratPhase_dilate {q r d : ℕ} (hd0 : 0 < d) (hq : 0 < q) (hdq : d ∣ q) (hdr : d ∣ r)
    (b : ℤ) : ratPhase b q r = ratPhase b (q / d) (r / d) := by
  have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
  have hdC : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hq0C : (((q / d : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq0.ne'
  have hqC : ((q : ℕ) : ℂ) = ((d : ℕ) : ℂ) * (((q / d : ℕ)) : ℂ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (Nat.mul_div_cancel' hdq).symm
  have hrC : ((r : ℕ) : ℂ) = ((d : ℕ) : ℂ) * (((r / d : ℕ)) : ℂ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (Nat.mul_div_cancel' hdr).symm
  unfold ratPhase
  congr 1
  push_cast
  rw [hqC, hrC]
  field_simp

/-- **ONE CLASS, DILATED** (`class_rat_dilate`) — the bare class sum of the door's sieved
datum at `(q, r)` IS `λ(d)` times the bare class sum at the reduced pair `(q/d, r/d)` on the
dilated window, `d = gcd(r,q)`.

`M4BridgeDilate.classWindowSum_dilate` (an equality, the change of variables) then
`absWindowSum_dilCoeff_memS_door` (the `λ(d)` factorisation under the `M`-RELATIVE door gate
`gcd(r,q) ≤ W < calP (Adoor M) (3072M) 1`).  ⟦NO NUMERAL⟧ — the ceiling `W` is free; the
retired `log H ≤ 2^{21845}` (an H-upper) is never demanded.

⟦THE GATE SITS AT `d`, NOT AT `q`⟧ (wave ⑤, ⟦D0-TEST⟧'s structural fact) — the door side
(`door_gate_blocks`, `dilCoeff_memS_door`, `absWindowSum_dilCoeff_memS_door`) carries `q` and
`W` as PURE INTERMEDIATES: neither occurs in the conclusion, so the whole chain is
instantiable at `q := d` with `hdq := le_rfl` and ZERO new bytes.  The hypothesis here is
therefore the strictly weaker `(gcd r q : ℝ) ≤ W`; every landed caller supplies it from
`gcd r q ≤ q ≤ W`. -/
theorem class_rat_dilate {M K n q r : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hdW : ((Nat.gcd r q : ℕ) : ℝ) ≤ W)
    (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) :
    ∑ m ∈ windowClass K n q r, doorSievedCoeff M m
      = liouvilleC (Nat.gcd r q)
        * ∑ m ∈ windowClass (dilLen K n (Nat.gcd r q)) (n / Nat.gcd r q)
            (q / Nat.gcd r q) (r / Nat.gcd r q), doorSievedCoeff M m := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  simp only [doorSievedCoeff]
  calc ∑ m ∈ windowClass K n q r, memSCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) 2 liouvilleC m
      = classWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) K n q r 0 := by
        rw [classWindowSum_eq_classPhaseSum, classPhaseSum_zero]
    _ = absWindowSum (dilCoeff (memSCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) (Nat.gcd r q) (q / Nat.gcd r q)
            (r / Nat.gcd r q)) (dilLen K n (Nat.gcd r q)) (n / Nat.gcd r q) 0 := by
        have h := classWindowSum_dilate (memSCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 liouvilleC) hq r K n 0
        rwa [mul_zero] at h
    _ = liouvilleC (Nat.gcd r q) * absWindowSum (classCoeff (memSCoeff
          (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC)
            (q / Nat.gcd r q) (r / Nat.gcd r q)) (dilLen K n (Nat.gcd r q))
              (n / Nat.gcd r q) 0 :=
        absWindowSum_dilCoeff_memS_door (J := 2) (q := Nat.gcd r q) hM hd.ne' le_rfl hdW hW 0
    _ = liouvilleC (Nat.gcd r q) * ∑ m ∈ windowClass (dilLen K n (Nat.gcd r q))
          (n / Nat.gcd r q) (q / Nat.gcd r q) (r / Nat.gcd r q),
            memSCoeff (calP (Adoor M) (3072 * M))
              (calQK (Adoor M) (3072 * M) M) 2 liouvilleC m := by
        rw [absWindowSum_classCoeff_zero]

/-! ## §4 — THE PER-STRATUM BOUND

⟦THE TRUNCATION-READY SHAPE⟧ — one stratum, priced against its OWN dilated cap `Lw`, as a
standalone lemma.  Wave ⑤'s `D₀`-truncation replaces the strata `d > D₀` by the landed
trivial bound without touching §5's recombination, because the recombination consumes only
this statement, once per `d`. -/

/-- **THE STRATUM `d`, SQUARED** (`stratum_sq_le_chiSummed`) — the classes with
`gcd(r,q) = d`, phased and summed, are under the χ-SUM at the reduced modulus `q/d` on the
dilated window.  Prefactor `1` (§2), `λ(d)` invisible (`‖λ‖ = 1`).

The cap `Lw` is a parameter with the single hypothesis `dilLen K n d ≤ Lw`, so the consumer
chooses `L` at `d = 1` and `⌊L/d⌋ + 1` at `d ≥ 2` — the two caps that keep the length under
the ambient `H`.

⟦THE GATE SITS AT `d`⟧ (wave ⑤) — `hdW : (d : ℝ) ≤ W`, NOT `(q : ℝ) ≤ W`: the door gate is
demanded at the dilation factor alone (`class_rat_dilate`'s header).  A consumer that
truncates the strata at a ceiling `D₀` reads this at `W := D₀`, so the analytic strata never
demand a gate above `D₀`. -/
theorem stratum_sq_le_chiSummed {M K n q d Lw : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hd0 : 0 < d) (hdq : d ∣ q) (hdW : (d : ℝ) ≤ W)
    (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) (b : ℤ)
    (hlen : dilLen K n d ≤ Lw) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup χ M Lw (n / d)) ^ 2 := by
  classical
  have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
  haveI : NeZero (q / d) := ⟨hq0.ne'⟩
  -- ⟦each class of the fibre, dilated⟧
  have hterm : ∀ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
      ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m
        = liouvilleC d * (ratPhase b (q / d) (r / d)
          * ∑ m ∈ windowClass (dilLen K n d) (n / d) (q / d) (r / d),
              doorSievedCoeff M m) := by
    intro r hr
    have hgcd : Nat.gcd r q = d := (Finset.mem_filter.mp hr).2
    have hdr : d ∣ r := hgcd ▸ Nat.gcd_dvd_left r q
    have hdil := class_rat_dilate (M := M) (K := K) (n := n) (q := q) (r := r) hM hq
      (by rw [hgcd]; exact hdW) hW
    rw [hgcd] at hdil
    rw [hdil, ratPhase_dilate hd0 hq hdq hdr b]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_fibre_eq_coprime hq hd0 hdq
      (fun r => ratPhase b (q / d) (r / d)
        * ∑ m ∈ windowClass (dilLen K n d) (n / d) (q / d) (r / d), doorSievedCoeff M m)]
  -- ⟦the `λ(d)` is unimodular⟧
  have hround : ∀ r₀ ∈ (Finset.range (q / d)).filter (fun r₀ => Nat.Coprime (q / d) r₀),
      ratPhase b (q / d) ((d * r₀) / d)
          * ∑ m ∈ windowClass (dilLen K n d) (n / d) (q / d) ((d * r₀) / d),
              doorSievedCoeff M m
        = ratPhase b (q / d) r₀
          * ∑ m ∈ windowClass (dilLen K n d) (n / d) (q / d) r₀, doorSievedCoeff M m := by
    intro r₀ _
    rw [Nat.mul_div_cancel_left r₀ hd0]
  rw [Finset.sum_congr rfl hround, norm_mul, liouvilleC_norm hd0.ne', one_mul]
  exact norm_sq_coprime_window_le M hlen (n / d) b

/-! ## §5 — THE WEIGHTED RECOMBINATION

The strata are recombined by Cauchy–Schwarz at the weights `1/d`, which is what converts the
per-stratum ledger's `1/d²` decay into the `H`-only residual `(∑_{d ∣ q} 1/d)²`. -/

/-- **THE STRATUM CAP** — `L` at `d = 1` (no dilation happens) and `⌊L/d⌋ + 1` at `d ≥ 2`.
Both are `≤ L`, which is what keeps every instance of the χ-summed socket inside its own
window range. -/
def capL (L d : ℕ) : ℕ := if d = 1 then L else L / d + 1

theorem dilLen_le_capL {K n L d : ℕ} (hd0 : 0 < d) (hKL : K ≤ L) :
    dilLen K n d ≤ capL L d := by
  unfold capL
  by_cases hd1 : d = 1
  · rw [if_pos hd1, hd1]
    have hone : dilLen K n 1 = K := by simp [dilLen]
    omega
  · rw [if_neg hd1]
    exact le_trans (dilLen_le K n hd0) (Nat.add_le_add_right (Nat.div_le_div_right hKL) 1)

theorem capL_le {L d : ℕ} (hd0 : 0 < d) (hL : 2 ≤ L) : capL L d ≤ L := by
  unfold capL
  by_cases hd1 : d = 1
  · rw [if_pos hd1]
  · rw [if_neg hd1]
    have hd2 : 2 ≤ d := by omega
    have : L / d ≤ L / 2 := Nat.div_le_div_left hd2 (by omega)
    have h2 : L / 2 + 1 ≤ L := by omega
    omega

theorem capL_le_div {L d : ℕ} (hd0 : 0 < d) :
    ((capL L d : ℕ) : ℝ) ≤ ((L : ℝ) + (d : ℝ)) / (d : ℝ) := by
  have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  unfold capL
  by_cases hd1 : d = 1
  · rw [if_pos hd1, hd1]
    push_cast
    rw [div_one]
    linarith
  · rw [if_neg hd1]
    have h := Nat.cast_div_le (α := ℝ) (m := L) (n := d)
    have heq : ((L : ℝ) + (d : ℝ)) / (d : ℝ) = (L : ℝ) / (d : ℝ) + 1 := by field_simp
    rw [heq]
    push_cast
    linarith

/-- **THE STRATUM LEDGER, SHARP** (`capL_ledger`) — `M4NonCoprime.d0_ledger_sharp` at the
stratum cap: `d·(B·capL²·⌊A/d⌋⁻) ≤ B·(L+d)²·A/d²`.  The `1/d²` is the profit the first road
banked unspent (`M4NonCoprime`'s ⟦THE d₀-LEDGER⟧); the second road spends it against the
weighted Cauchy–Schwarz. -/
theorem capL_ledger {A L d : ℕ} (hd : 0 < d) {Bc : ℝ} (hBc : 0 ≤ Bc) :
    (d : ℝ) * (Bc * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ))
      ≤ Bc * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcap := capL_le_div (L := L) (d := d) hd
  have hA' : ((A / d - 1 : ℕ) : ℝ) ≤ (A : ℝ) / (d : ℝ) := by
    have h1 : ((A / d - 1 : ℕ) : ℝ) ≤ ((A / d : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le (A / d) 1
    exact h1.trans (Nat.cast_div_le (α := ℝ))
  have hcap0 : (0 : ℝ) ≤ ((capL L d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA'0 : (0 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLd0 : (0 : ℝ) ≤ ((L : ℝ) + (d : ℝ)) / (d : ℝ) := by positivity
  have hsq : ((capL L d : ℕ) : ℝ) ^ 2 ≤ (((L : ℝ) + (d : ℝ)) / (d : ℝ)) ^ 2 := by
    nlinarith
  have hstep : (d : ℝ) * (Bc * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ))
      ≤ (d : ℝ) * (Bc * (((L : ℝ) + (d : ℝ)) / (d : ℝ)) ^ 2 * ((A : ℝ) / (d : ℝ))) := by
    have h1 : Bc * ((capL L d : ℕ) : ℝ) ^ 2 ≤ Bc * (((L : ℝ) + (d : ℝ)) / (d : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hBc
    have h2 : (0 : ℝ) ≤ Bc * (((L : ℝ) + (d : ℝ)) / (d : ℝ)) ^ 2 := by positivity
    have := mul_le_mul h1 hA' hA'0 h2
    exact mul_le_mul_of_nonneg_left this hd0.le
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- **THE STRATUM'S BUDGET AT ONE BASE** — the χ-SUM at the reduced modulus `q/d`, read at
the stratum's own cap and dilated base.  Named so §5's recombination and wave ⑤'s
truncation speak the same object. -/
def strataTerm (M q L d n : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup χ M (capL L d) (n / d)) ^ 2

theorem strataTerm_nonneg (M q L d n : ℕ) : 0 ≤ strataTerm M q L d n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **THE STRATIFIED SUP BOUND AT ONE BASE** (`subWindowSup_sq_le_strata`) — the door's
sieved sub-window sup at the rational `b/q`, squared, against the weighted stratum budgets.

The weights are `1/d` (the Cauchy–Schwarz side) and `d` (the budget side); their product's
`(∑_{d ∣ q} 1/d)²` is the ONLY `q`-dependence that survives the whole road, and it is
bounded `H`-only by `(1 + log arcDen)²`. -/
theorem subWindowSup_sq_le_strata {M n q L : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) (b : ℤ) :
    (subWindowSup (doorSievedCoeff M) L n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q L d n := by
  classical
  set T := ∑ d ∈ q.divisors, Real.sqrt (strataTerm M q L d n) with hT
  -- ⟦every sub-window is under the sum of the strata's square roots⟧
  have hstrat : ∀ K, K ≤ L →
      ‖absWindowSum (doorSievedCoeff M) K n ((b : ℝ) / (q : ℝ))‖ ≤ T := by
    intro K hK
    have hsplit : absWindowSum (doorSievedCoeff M) K n ((b : ℝ) / (q : ℝ))
        = ∑ r ∈ Finset.range q,
            ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m := by
      have h := absWindowSum_residue_split (doorSievedCoeff M) K n hq b 0
      rw [add_zero] at h
      simpa only [classPhaseSum_zero] using h
    have hmaps : ∀ r ∈ Finset.range q, Nat.gcd r q ∈ q.divisors := fun r _ =>
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right r q, hq.ne'⟩
    rw [hsplit, ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun r => ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m)]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdW : (d : ℝ) ≤ W :=
      le_trans (by exact_mod_cast Nat.le_of_dvd hq hdq) hqW
    have hsq := stratum_sq_le_chiSummed (M := M) (K := K) (n := n) (q := q) (d := d)
      (Lw := capL L d) hM hq hd0 hdq hdW hW b (dilLen_le_capL hd0 hK)
    have h0 : (0 : ℝ) ≤ ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖ := norm_nonneg _
    calc ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
            ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖
        = Real.sqrt (‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
            ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff M m‖ ^ 2) :=
          (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (strataTerm M q L d n) := Real.sqrt_le_sqrt hsq
  have hsup : subWindowSup (doorSievedCoeff M) L n ((b : ℝ) / (q : ℝ)) ≤ T :=
    subWindowSup_le hstrat
  have hsup0 : (0 : ℝ) ≤ subWindowSup (doorSievedCoeff M) L n ((b : ℝ) / (q : ℝ)) :=
    subWindowSup_nonneg _ _ _ _
  -- ⟦the weighted Cauchy–Schwarz over the strata⟧
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq q.divisors
    (fun d => (Real.sqrt (d : ℝ))⁻¹)
    (fun d => Real.sqrt (d : ℝ) * Real.sqrt (strataTerm M q L d n))
  have hprod : ∀ d ∈ q.divisors,
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ) * Real.sqrt (strataTerm M q L d n))
        = Real.sqrt (strataTerm M q L d n) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hs : Real.sqrt (d : ℝ) ≠ 0 := by positivity
    field_simp
  have hf2 : ∀ d ∈ q.divisors,
      ((Real.sqrt (d : ℝ))⁻¹) ^ 2 = (1 : ℝ) / (d : ℝ) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [inv_pow, Real.sq_sqrt hd0R.le, one_div]
  have hg2 : ∀ d ∈ q.divisors,
      (Real.sqrt (d : ℝ) * Real.sqrt (strataTerm M q L d n)) ^ 2
        = (d : ℝ) * strataTerm M q L d n := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [mul_pow, Real.sq_sqrt hd0R.le, Real.sq_sqrt (strataTerm_nonneg M q L d n)]
  rw [Finset.sum_congr rfl hprod, Finset.sum_congr rfl hf2, Finset.sum_congr rfl hg2] at hcs
  calc (subWindowSup (doorSievedCoeff M) L n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ T ^ 2 := by nlinarith
    _ ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q L d n := hcs

/-- **THE DIVISOR RESIDUAL, `H`-ONLY** — `∑_{d ∣ q} 1/d ≤ 1 + log q`, the harmonic bound on
the divisors.  This is the ONE place the `q`-dependence of the second road is discharged, and
it is discharged into a `loglog`-scale quantity, never a power. -/
theorem sum_inv_divisors_le {q : ℕ} (hq : 0 < q) :
    ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (q : ℝ) := by
  have hsub : q.divisors ⊆ Finset.Icc 1 q := by
    intro d hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hq (Nat.mem_divisors.mp hd).1⟩
  have h1 : ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) ≤ ∑ d ∈ Finset.Icc 1 q, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
  have h2 : ∑ d ∈ Finset.Icc 1 q, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (q : ℝ) := by
    have h := harmonic_le_one_add_log q
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      using h
  linarith

/-- **THE STRATA RESIDUAL** `1 + log(arcDen 12 H)` — `H`-only, one-sided, and the composed
price's whole `q`-dependence.  At the door's magnitudes this is `≈ 12·loglog H`, i.e. the
`≈ 7.7`-nat residual of the freeze's D-3, never `arcDen` and never `q`. -/
def strataResidual (H : ℕ) : ℝ := 1 + Real.log (arcDen 12 H)

theorem strataResidual_nonneg {H : ℕ} (h : (1 : ℝ) ≤ arcDen 12 H) : 0 ≤ strataResidual H := by
  have := Real.log_nonneg h
  unfold strataResidual
  linarith

theorem capL_le_div_succ {L d : ℕ} (_hd0 : 0 < d) : capL L d ≤ L / d + 1 := by
  unfold capL
  by_cases hd1 : d = 1
  · rw [if_pos hd1, hd1]
    omega
  · rw [if_neg hd1]

/-- **⟦R-P5⟧ THE DILATED CAP FITS STRICTLY INSIDE THE DILATED BASE**
(`capL_le_dilated_base`).  `ℕ`-division bookkeeping only: `capL L d ≤ ⌊L/d⌋ + 1`
(`capL_le_div_succ`), `⌊L/d⌋ ≥ 32` from `32d ≤ L`, and `⌊A/d⌋ ≥ 2⌊L/d⌋` from `2L ≤ A` —
so `⌊A/d⌋ − 1 ≥ ⌊L/d⌋ + 31`.  The two units of slack the `−1` and the `+1` need are bought
by the `32`, never guessed.

This is what supplies `M4ChiSummedBlockMeanSqN`'s LENGTH antecedent (`L ≤ A`) at the
stratified consumer's re-indexed block. -/
theorem capL_le_dilated_base {L d A : ℕ} (hd0 : 0 < d) (h32 : 32 * d ≤ L)
    (h2LA : 2 * L ≤ A) : capL L d ≤ A / d - 1 := by
  have hc := capL_le_div_succ (L := L) (d := d) hd0
  have hLd32 : 32 ≤ L / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
  have h2Ld : 2 * (L / d) ≤ A / d := by
    refine le_trans ?_ (Nat.div_le_div_right h2LA)
    refine (Nat.le_div_iff_mul_le hd0).mpr ?_
    have h := Nat.div_mul_le_self L d
    calc 2 * (L / d) * d = 2 * (L / d * d) := by ring
      _ ≤ 2 * L := Nat.mul_le_mul_left 2 h
  -- the three ℕ atoms, abstracted so `omega` sees no variable division
  have hkey : ∀ c l a : ℕ, c ≤ l + 1 → 32 ≤ l → 2 * l ≤ a → c ≤ a - 1 := by
    intro c l a h1 h2 h3; omega
  exact hkey _ _ _ hc hLd32 h2Ld

/-- **⟦R-P5⟧ THE DILATED BASE'S TWO-SIDED `ℕ`-DIVISION BOUND** (`le_mul_div_add`).
`A ≤ d·⌊A/d⌋ + d` — the `+d` is the discarded remainder, spent explicitly. -/
theorem le_mul_div_add {A d : ℕ} (hd0 : 0 < d) : A ≤ d * (A / d) + d := by
  conv_lhs => rw [← Nat.div_add_mod A d]
  exact Nat.add_le_add_left (Nat.mod_lt _ hd0).le _

theorem le_mul_capL {L d : ℕ} (hd0 : 0 < d) : L ≤ d * capL L d := by
  unfold capL
  by_cases hd1 : d = 1
  · rw [if_pos hd1, hd1, one_mul]
  · rw [if_neg hd1]
    have h2 : L % d < d := Nat.mod_lt _ hd0
    calc L = d * (L / d) + L % d := (Nat.div_add_mod L d).symm
      _ ≤ d * (L / d) + d := Nat.add_le_add_left h2.le _
      _ = d * (L / d + 1) := by ring

set_option maxHeartbeats 1600000 in
-- the stratified assembly re-elaborates the divisor sum, the fibre count, the χ-datum and
-- the ledger at every stratum, and each step carries the full `strataTerm` expansion; the
-- arithmetic steps are all `linarith`/`nlinarith` with explicit hints (no unbounded search)
/-- **⟦S-3⟧ THE STRATIFIED CONSUMER, IN BLOCK FORM** (`m4_freeBlockSup_of_chiSummed`).

The door's sieved sub-window sup at ANY rational `b/q` of the arc range, mean-squared over a
free half-open block `(A, B]` with the TIGHT fit `B + L ≤ 2A`, priced by the χ-summed supply
at the composed constant

```
      4 · (1 + log arcDen 12 H)² · B_cl H .
```

⟦WHAT IS NOT IN THE PRICE⟧ no `q`, no `q²`, no `arcDen` power: the class count died at §2's
prefactor `1`, and the strata's `1/d²` ledger paid the fibre factor.  The only survivor is
the divisor residual `(∑_{d ∣ q} 1/d)² ≤ (1 + log arcDen)²` — `H`-only and `loglog`-scale.

⟦THE GATES⟧ two, both `H`-only, one-sided and regime-absorbable: the `M`-RELATIVE dilation
gate `arcDen 12 H < calP (Adoor M) (3072M) 1` (never the retired numeral), and the window
floor `32·arcDen 12 H² ≤ H`.  The latter is what makes every stratum's re-indexed block
non-degenerate (`2d ≤ A`) and every dilated cap admissible.

⟦R-P5, THE BASE ANTECEDENTS SWAPPED⟧ the crude base floor `32·arcDen 12 H ≤ A` is replaced
by the two x-scale-ladder facts `2H ≤ A` and `R.x ≤ 8·R.ω·A`, and the window floor is read
at its square (`16·arcDen 12 H ² ≤ H`).  All three are strictly what the socket's three base
antecedents cost at the ONE dilation this file performs: the re-indexed block
`(⌊A/d⌋ − 1, ⌊B/d⌋]` must satisfy `capL L d ≤ ⌊A/d⌋ − 1`, `√H ≤ ⌊A/d⌋ − 1` and
`R.x ≤ 16·R.ω·arcDen 12 H·(⌊A/d⌋ − 1)`, and each is derived below by the same pattern as
`hcapnar` (the narrowing at the dilated cap): one power of `arcDen 12 H` is spent because
`d ≤ arcDen 12 H`.  `32·arcDen 12 H ≤ A` still follows (`2H ≥ 2·32·arcDen`), so nothing
downstream of the old floor is weakened. -/
theorem m4_freeBlockSup_of_chiSummed {R : ChowlaRegime} {M : ℕ} {Bcl : ℕ → ℝ} (hM : 1 ≤ M)
    (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    (hchi : M4ChiSummedBlockMeanSqN R M Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (L : ℝ) → 32 * arcDen 12 H ≤ (L : ℝ) →
      16 * arcDen 12 H ^ 2 ≤ (H : ℝ) →
      ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
        ∀ A B : ℕ, 0 < A → 2 * (H : ℝ) ≤ (A : ℝ) →
          (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) → B + L ≤ 2 * A →
          ∑ n ∈ Finset.Ioc A B,
              (subWindowSup (doorSievedCoeff M) L n ((b : ℝ) / (q : ℝ))) ^ 2
            ≤ 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
  classical
  intro H hlo hhi L hLH hnar hLarc harcsq b q hq hqQ A B hA hAH hAx hfit
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hAarc : 32 * arcDen 12 H ≤ (A : ℝ) := by
    have hLHR : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH
    linarith
  have hres0 : (0 : ℝ) ≤ strataResidual H := strataResidual_nonneg harc1
  have hB0 := hBcl0 H
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  have hL0R : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hdiv0 : (0 : ℝ) ≤ ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => by positivity
  have hdivres : ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) ≤ strataResidual H := by
    refine le_trans (sum_inv_divisors_le hq) ?_
    unfold strataResidual
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have := Real.log_le_log (by linarith) hqQ
    linarith
  by_cases hAB : B < A
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  rw [Nat.not_lt] at hAB
  -- ⟦the block's own consequences: the tight fit and the two arc floors⟧
  have hLA : L ≤ A := by omega
  have hLAR : (L : ℝ) ≤ (A : ℝ) := by exact_mod_cast hLA
  have hL32 : (32 : ℝ) ≤ (L : ℝ) := by nlinarith
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast this
  -- ⟦R-P5, THE THREE ANTECEDENTS AT THE UNDILATED BASE⟧ the two arithmetic facts every
  -- dilated instance below re-reads: `4·arcDen 12 H ≤ √H` (the window floor at its square)
  -- and `2L ≤ A` (the length antecedent with the two units of `ℕ`-division slack)
  have hH0 : 0 < H := by omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have hLHR : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hsqsq : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt hH0R.le
  have harcsqrt : 4 * arcDen 12 H ≤ Real.sqrt (H : ℝ) := by
    have h1 : Real.sqrt ((4 * arcDen 12 H) ^ 2) ≤ Real.sqrt (H : ℝ) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hsqrtle : Real.sqrt (H : ℝ) ≤ (H : ℝ) := by nlinarith [harcsqrt, harc1]
  have h2LA : 2 * L ≤ A := by
    have h : (2 : ℝ) * (L : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast h
  -- ⟦the per-base stratified bound, summed⟧
  have hpt : ∀ n ∈ Finset.Ioc A B,
      (subWindowSup (doorSievedCoeff M) L n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q L d n := fun n _ =>
    subWindowSup_sq_le_strata hM hq hqQ (hgate H hlo hhi) b
  refine le_trans (Finset.sum_le_sum hpt) ?_
  have hswap : ∑ n ∈ Finset.Ioc A B,
        ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm M q L d n)
      = (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm M q L d n := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
  rw [hswap]
  -- ⟦THE PER-STRATUM BUDGET⟧ the fibre count, the χ-datum, the sharp ledger
  have hstr : ∀ d ∈ q.divisors,
      (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm M q L d n
        ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdarc : (d : ℝ) ≤ arcDen 12 H :=
      le_trans (by exact_mod_cast Nat.le_of_dvd hq hdq) hqQ
    have hdA2R : 2 * (d : ℝ) ≤ (A : ℝ) := by nlinarith
    have hdA2 : 2 * d ≤ A := by exact_mod_cast hdA2R
    have hdA : d ≤ A := by omega
    have hdL : (d : ℝ) ≤ (L : ℝ) := by nlinarith
    have h32dL : 32 * d ≤ L := by
      have h : (32 : ℝ) * (d : ℝ) ≤ (L : ℝ) := by linarith
      exact_mod_cast h
    have hdA3 : 3 * d ≤ A := by
      have h : (3 : ℝ) * (d : ℝ) ≤ (A : ℝ) := by linarith
      exact_mod_cast h
    -- ⟦the reduced modulus⟧
    have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
    have hq0Q : ((q / d : ℕ) : ℝ) ≤ arcDen 12 H :=
      le_trans (by exact_mod_cast Nat.div_le_self q d) hqQ
    -- ⟦the dilated cap is admissible⟧
    have hcapL : capL L d ≤ L := capL_le hd0 hL2
    have hcapH : capL L d ≤ H := le_trans hcapL hLH
    have hcapmul : (L : ℝ) ≤ (d : ℝ) * ((capL L d : ℕ) : ℝ) := by
      exact_mod_cast le_mul_capL (L := L) (d := d) hd0
    have hcap0 : (0 : ℝ) ≤ ((capL L d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcapnar : (H : ℝ) ≤ arcDen 12 H ^ 3 * ((capL L d : ℕ) : ℝ) := by
      have h1 : (L : ℝ) ≤ arcDen 12 H * ((capL L d : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hdarc hcap0
        linarith [hcapmul]
      have h2 : arcDen 12 H ^ 2 * (L : ℝ)
          ≤ arcDen 12 H ^ 2 * (arcDen 12 H * ((capL L d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have heq : arcDen 12 H ^ 2 * (arcDen 12 H * ((capL L d : ℕ) : ℝ))
          = arcDen 12 H ^ 3 * ((capL L d : ℕ) : ℝ) := by ring
      rw [heq] at h2
      linarith [hnar]
    -- ⟦the re-indexed block⟧
    have hA'2 : 2 ≤ A / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    have hA'pos : 0 < A / d - 1 := by omega
    have hA'3 : 3 ≤ A / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    -- ⟦R-P5, THE THREE ANTECEDENTS AT THE DILATED BASE⟧ each spends exactly one power of
    -- `arcDen 12 H` (because `d ≤ arcDen 12 H`) and the two `ℕ`-division units the `⌊·⌋` and
    -- the `−1` cost — the same pattern as `hcapnar` above
    have hA'cast : ((A / d - 1 : ℕ) : ℝ) = ((A / d : ℕ) : ℝ) - 1 := by
      have h1 : 1 ≤ A / d := by omega
      rw [Nat.cast_sub h1, Nat.cast_one]
    have hAdiv : (A : ℝ) ≤ (d : ℝ) * ((A / d : ℕ) : ℝ) + (d : ℝ) := by
      have h' := (Nat.cast_le (α := ℝ)).mpr (le_mul_div_add (A := A) (d := d) hd0)
      push_cast at h'
      linarith
    have hA'0 : (0 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hA'2R : (2 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
      have h : (2 : ℕ) ≤ A / d - 1 := by omega
      exact_mod_cast h
    -- (i) THE LENGTH ANTECEDENT `capL L d ≤ ⌊A/d⌋ − 1`
    have hcapA : capL L d ≤ A / d - 1 := capL_le_dilated_base hd0 h32dL h2LA
    -- (ii) THE `√H` ANTECEDENT
    have hsqA' : Real.sqrt (H : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
      rw [hA'cast]
      have hd4 : 4 * (d : ℝ) ≤ Real.sqrt (H : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hd4
        (by positivity : (0 : ℝ) ≤ Real.sqrt (H : ℝ) + 2)
      have hkey : (d : ℝ) * (Real.sqrt (H : ℝ) + 2) ≤ (A : ℝ) := by
        nlinarith [hmul, hsqsq, hsqrtle, hAH, hH0R, hA0R]
      have hstep : (d : ℝ) * Real.sqrt (H : ℝ)
          ≤ (d : ℝ) * (((A / d : ℕ) : ℝ) - 1) := by nlinarith [hAdiv, hkey]
      exact le_of_mul_le_mul_left hstep hd0R
    -- (iii) THE x-SCALE ANTECEDENT
    have hxA' : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) := by
      have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
      have hAd2 : (A : ℝ) ≤ (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ) := by
        rw [hA'cast]; linarith [hAdiv]
      have s1 : (R.x : ℝ)
          ≤ 8 * (R.ω : ℝ) * ((d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hAd2 (by positivity : (0 : ℝ) ≤ 8 * (R.ω : ℝ))
        linarith [hAx]
      have s2 : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ)
          ≤ 2 * (arcDen 12 H * ((A / d - 1 : ℕ) : ℝ)) := by
        have h1 : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ)
            ≤ arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hdarc hA'0
        have h2 : 2 * arcDen 12 H ≤ arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) := by
          nlinarith [hA'2R, harc0]
        linarith
      have s3 := mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℝ) ≤ 8 * (R.ω : ℝ))
      nlinarith [s1, s3]
    have hfit' : B / d + capL L d ≤ 2 * (A / d - 1) + 4 := by
      have h := dilBlock_reindex_fit (A := A) (B := B) (H := L) (d := d) hd0 hdA hfit
      have hc := capL_le_div_succ (L := L) (d := d) hd0
      omega
    -- ⟦the fibre count⟧
    have hf0 : ∀ n' : ℕ, (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ (q / d),
        (doorChiSup χ M (capL L d) n') ^ 2 := fun n' =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmaps : ∀ n ∈ Finset.Ioc A B, n / d ∈ Finset.Ioc (A / d - 1) (B / d) := fun n hn =>
      div_mem_reindexed hd0 hdA hn
    have hfib := sum_Ioc_comp_div_le (f := fun n' => ∑ χ : DirichletCharacter ℂ (q / d),
      (doorChiSup χ M (capL L d) n') ^ 2) hf0 hd0 hmaps
    -- ⟦the χ-summed datum at the reduced modulus⟧
    have hdatum := hchi H hlo hhi (capL L d) hcapH hcapnar (q / d) hq0 hq0Q
      (A / d - 1) (B / d) hA'pos hcapA hsqA' hxA' hfit'
    -- ⟦the sharp ledger⟧
    have hled := capL_ledger (A := A) (L := L) (d := d) hd0 hB0
    have hdatum' : ∑ n' ∈ Finset.Ioc (A / d - 1) (B / d),
          ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup χ M (capL L d) n') ^ 2
        ≤ Bcl H * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      exact hdatum
    have hchain : ∑ n ∈ Finset.Ioc A B, strataTerm M q L d n
        ≤ (d : ℝ) * (Bcl H * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ)) := by
      refine le_trans hfib ?_
      exact mul_le_mul_of_nonneg_left hdatum' hd0R.le
    have hfinal : ∑ n ∈ Finset.Ioc A B, strataTerm M q L d n
        ≤ Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2 := le_trans hchain hled
    have hLd : ((L : ℝ) + (d : ℝ)) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by nlinarith
    have hstep : (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm M q L d n
        ≤ (d : ℝ) * (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hfinal hd0R.le
    have hdne : ((d : ℝ)) ≠ 0 := ne_of_gt hd0R
    have hrw : (d : ℝ) * (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2)
        = (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
      field_simp
    refine le_trans hstep ?_
    rw [hrw]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith [mul_le_mul_of_nonneg_left hLd (mul_nonneg hB0 hA0R)]
  -- ⟦the recombination⟧
  have hsum : ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm M q L d n
      ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hstr
  have hbig0 : (0 : ℝ) ≤ 4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by positivity
  calc (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm M q L d n
      ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ((4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ))
            * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hdiv0
    _ ≤ strataResidual H * ((4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H) := by
        have h1 : (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ))
              * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ)
            ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H :=
          mul_le_mul_of_nonneg_left hdivres hbig0
        have h2 : (0 : ℝ) ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H := by
          positivity
        nlinarith [hdivres, hdiv0]
    _ = 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by ring

end Salt.MR

end
