/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦STRIDE BRIDGE⟧ — Tao (3.16) / Prop 2.6 at the affine forms: the F-function with the class
filter, λ-BV wave 2-S step F2 (2026-09-03, STATEMENT-ONLY at the freeze; executors after the
09/04 08:00 council)

`StrideFork` (F1) opened the OBJECTS of Tao arXiv:1509.05422 Theorem 2.3 at a general stride
`a` and offset `b`: the pushforward measure `logMeasureAff a x ω`, the frequency set
`bigXiAff`, the affine regime and the two doors with their seams.  This module opens the
(2.4) ⇒ (2.11) PRODUCER CHAIN at the affine forms — the twins, in the three files
`ChowlaFailure` / `Prop26` / `FBridge`, of what the `h`-fork twinned there — so that the entropy
half (F4) has a `(c₁, h211)` pair to consume at `(a, b, h)`, exactly as `outer_combine_h` consumes
`h211_of_logChowla2Fails_h`.

⟦THE DESIGN, IN THREE LINES — freeze `2026-09-03-math-FREEZE-lambda-bv-wave2S-F2.md` §1⟧
* Tao (3.16) (textdump:1288-1290) restricts the window index to the class `j ≡ p·b (mod a)`:
  `E Σ_p (c_p/p) Σ_{j : j, j+ph ∈ [1,H]} 1_{j ≡ pb (a)} g₁(an+j) g₂(an+j+ph) ≫ ε·H/log H`.  In the
  corpus's 0-indexed window (`windowVal H v j = λ(m+j+1)`) that filter is `j + 1 ≡ p·b (mod a)`,
  spelled `((j + 1 : ℕ) : ZMod a) = ((p·b : ℕ) : ZMod a)`.  ⭐ **THE FILTER IS A CONJUNCT ON THE
  SUMMATION INDEX `(j, p)` AND NEVER TOUCHES THE RESIDUE DATUM.**  Tao's gate `an + j ≡ pb (mod ap)`
  splits by CRT (`gcd(a, p) = 1`: `a ≤ ε²H₋/2 < p` by the regime's `hcoprime`) into `p ∣ an + j`
  — the landed gate on `y = m mod P_H` at `m = a·n` — and `j ≡ pb (mod a)`, which reads no `y`.
  So the carrier `ZMod (PH eps H)` is UNCHANGED and F1's STOP ("the filter cannot be carried through
  `fBridgeF`'s carrier without a new carrier") is cleared by inspection, not by a construction.
* ⛔ The filter sits on the FIRST factor's index only (`x_{1,j}`), never on `x_{2,j+ph}` — it
  cannot be pushed into the window pattern `v` (masking `v` would filter both factors and demand
  `ph ≡ 0 (mod a)`).  Hence a NEW definition `fBridgeG_aff`, not `fBridgeG_h` at a masked window.
* The main term is `SP·(H/a)·|X_aff|`: only `H/a` of the `j` survive the class, so `c ↦ cM/(2a)`
  and `c₁ ↦ c₁/a` (refuter §D: forced, entering at Lemma 2.5's normaliser).  The box bound
  `H/p + 1`, the residue-sum collapse and the whole concentration cone are `a`-FREE (the filter
  only REMOVES terms), so the Hoeffding substrate is reused verbatim, as the `h`-fork reused it.

⛔ **Degenerate values.**  `a = 0`: `ZMod 0 = ℤ` and the filter reads `j + 1 = p·b` in `ℤ`; every
identity and bound below is still true, `(H : ℝ) / 0 = 0` makes `hreduce_aff` trivial and
`cM / (2·0) = 0` makes the explicit conclusion `0 ≤ |…|`; `0 < a` is carried where a POSITIVE
constant is exported.  `h = 0` inherits the `h`-lane's degeneracy.  `b` is unconstrained here
(the regime's `hb` binds it downstream).  `H = 0, 1`: `Finset.range H` and `Fin H` degenerate as in
`FBridge`.  `a = 1, b = 0`: the filter is `True` (`ZMod 1` is a subsingleton) and every object is
the landed `_h` member — the `_one_zero` compats say so.

Scope: definitions and the producer-chain statements only; `hreduce_aff` is a HYPOTHESIS here
exactly as `hreduce` is in `Prop26` (its discharge is F4's, at the stride measure).  Nothing here
produces `LogChowlaAffSupply`, moves a door, or bears on twin primes.  Import direction:
`Salt.Entropy`-internal; nothing from `Salt/MR` or `Salt/TwinBar`.
-/
import Salt.Entropy.Chowla.StrideFork
import Salt.Entropy.Chowla.Prop26
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

variable (eps : ℚ) (H : ℕ)

/-! ## F2-B — the F-function with the class filter (Tao (3.14)/(3.16) at `(a, b, h)`) -/

/-- **F2-B1 (def).**  The per-prime component at stride `a`, offset `b`, shift `h`:
`G_{p}^{(a,b,h)}(v)(r) = ∑_{j < H} 1_{(j+1 : ZMod p) = -r} · 1_{j+1 ≡ p·b (a)} · v_j · v_{j+p·h}`.
The gate is the landed `h`-free one on the base index; the class filter is the second conjunct,
on `(j, p)` alone.  `fBridgeG_h` is the `(1, 0)` member (`fBridgeG_aff_one_zero`). -/
noncomputable def fBridgeG_aff (a b h : ℕ) (v : Fin H → ℤ) (p : primeWindow eps H) :
    ZMod (p : ℕ) → ℝ :=
  fun r => ∑ j ∈ Finset.range H,
    if ((j + 1 : ℕ) : ZMod (p : ℕ)) = -r
        ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0

/-- **F2-B2 (def).**  The assembly at `(a, b, h)`: `∑_{p ∈ 𝒫_H} G_p^{(a,b,h)}(v) ∘ residueProj p`,
the `∑_i G_i (proj_i ·)` shape `hoeffding_residueProj` centers on — the carrier is the landed
`ZMod (PH eps H)`. -/
noncomputable def fBridgeF_aff (a b h : ℕ) (v : Fin H → ℤ) : ZMod (PH eps H) → ℝ :=
  fun y => ∑ p : primeWindow eps H, fBridgeG_aff eps H a b h v p (residueProj eps H p y)

/-- **F2-B3 (class B) — the `(1, 0)` compat for `G`.**  At `a = 1` the filter compares two
elements of `ZMod 1`, a subsingleton (`Fin 1`), so the second conjunct is `True`:
`have hsub : ∀ u w : ZMod 1, u = w := fun u w => Subsingleton.elim u w`, then `funext r; unfold
fBridgeG_aff fBridgeG_h; refine Finset.sum_congr rfl (fun j _ => ?_); simp only [hsub, and_true]`.
Like `fBridgeG_h_one`, this compat CANNOT police the filter's spelling — at `a = 1` every
spelling is `True`; `fBridgeG_aff_sum_over_residues` at `a = 2` is where a wrong filter shows. -/
theorem fBridgeG_aff_one_zero (h : ℕ) (v : Fin H → ℤ) (p : primeWindow eps H) :
    fBridgeG_aff eps H 1 0 h v p = fBridgeG_h eps H h v p := by
  sorry

/-- **F2-B4 (class A) — the `(1, 0)` compat for `F`.**  Termwise from `fBridgeG_aff_one_zero`
(`funext y; unfold fBridgeF_aff fBridgeF_h; exact Finset.sum_congr rfl (fun p _ => by rw
[fBridgeG_aff_one_zero])`). -/
theorem fBridgeF_aff_one_zero (h : ℕ) (v : Fin H → ℤ) :
    fBridgeF_aff eps H 1 0 h v = fBridgeF_h eps H h v := by
  sorry

/-- **F2-B5 (class B) — the deterministic box bound at `(a, b, h)`**:
`|G_p^{(a,b,h)}(v)(r)| ≤ H/p + 1`
for a `‖·‖ ≤ 1` pattern, uniformly in `a, b, h`.  The `h`-script (`fBridgeG_h_abs_le`,
`FBridge.lean:572`) with ONE extra step: each summand `|if gate ∧ filter then t else 0|` is
`≤ if gate then 1 else 0` (`split_ifs` on the conjunction; the filtered-out terms are `0 ≤ 1`, the
kept ones are `windowVal_prod_abs_le`), after which the residue-class count
`card_filter_natCast_eq_le H (-r - 1)` is the landed line.  The filter only REMOVES terms, so no
`a` appears in the bound. -/
lemma fBridgeG_aff_abs_le (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (p : primeWindow eps H) (r : ZMod (p : ℕ)) :
    |fBridgeG_aff eps H a b h v p r| ≤ (H : ℝ) / (p : ℝ) + 1 := by
  sorry

/-- **F2-B6 (class A).**  The `[lo, hi]` box form: `Set.mem_Icc.mpr (abs_le.mp (fBridgeG_aff_abs_le
…))`. -/
lemma fBridgeG_aff_mem_Icc (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (p : primeWindow eps H) (r : ZMod (p : ℕ)) :
    fBridgeG_aff eps H a b h v p r
      ∈ Set.Icc (-((H : ℝ) / (p : ℝ) + 1)) ((H : ℝ) / (p : ℝ) + 1) := by
  sorry

/-- **F2-B7 (class B) — the residue-sum identity at `(a, b, h)`** (the mean's numerator):
`∑_{r ∈ ZMod p} G_p^{(a,b,h)}(v)(r) = ∑_{j < H} 1_{j+1 ≡ pb (a)} · v_j·v_{j+ph}`.  The `h`-script
(`fBridgeG_h_sum_over_residues`, `FBridge.lean:648`): `Finset.sum_comm`, then per `j` the
`r`-sum of `if gate r ∧ filter then t else 0` is `if filter then (∑_r if gate r then t else 0)
else 0` (`by_cases hf : filter` and `simp only [hf, and_true, and_false, if_false,
Finset.sum_const_zero]`), and the inner sum collapses at `r = -(j+1)` exactly as at `h`
(`Finset.sum_ite_eq'` after the `hcond` flip).  ⭐ THIS IS THE FILTER'S TRIPWIRE: at `a = 2, b = 1`
the right-hand side keeps only the `j` with `j + 1 ≡ p (mod 2)`, i.e. the EVEN `j` (every window
prime is odd) — a filter on `j` instead of `j + 1` keeps the odd ones. -/
lemma fBridgeG_aff_sum_over_residues (a b h : ℕ) {v : Fin H → ℤ} (p : primeWindow eps H) :
    ∑ r : ZMod (p : ℕ), fBridgeG_aff eps H a b h v p r
      = ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0 := by
  sorry

/-- **F2-B8 (class B) — the mean identity at `(a, b, h)`**:
`E_y[G_p^{(a,b,h)}(v)(y mod p)] = (1/p)·∑_{j} 1_{j+1 ≡ pb (a)} v_j v_{j+ph}`.  The `h`-script
(`fBridgeG_h_mean`, `FBridge.lean:671`) VERBATIM — `residueProj_fiber_card` never sees `v`, the
fibre equidistribution is filter-blind — with `fBridgeG_aff_sum_over_residues` in place of
`fBridgeG_h_sum_over_residues` at the one `rw`.  This is the decoupled `y`-mean that the affine
circle-method estimate (F3/F4's `hcirc_aff`) bounds. -/
lemma fBridgeG_aff_mean (a b h : ℕ) {v : Fin H → ℤ} (p : primeWindow eps H) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
        fBridgeG_aff eps H a b h v p (residueProj eps H p ω)]
      = (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0 := by
  sorry

/-- **F2-B9 (class A) — the raw concentration bound at `(a, b, h)`**: `hoeffding_residueProj eps H
(fBridgeG_aff eps H a b h v) (fun i x => fBridgeG_aff_mem_Icc eps H a b h hv i x) hδ` — the SAME
box, so the `h`-proof term transfers with the name changed (`fBridge_h_concentration_raw`,
`FBridge.lean:711`). -/
theorem fBridge_aff_concentration_raw (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_aff eps H a b h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_aff eps H a b h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 / (2 * ((∑ p : primeWindow eps H,
          (‖((H : ℝ) / (p : ℝ) + 1) - -((H : ℝ) / (p : ℝ) + 1)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  sorry

/-- **F2-B10 (class A) — the usable concentration bound at `(a, b, h)`**, exponent
`2·exp(−δ²/(2(ε²H+1)(2/ε²+1)²))` UNCHANGED (`fBridge_var_le` is `v`-, `h`- and `a`-free).  The
`h`-script (`fBridge_h_concentration`, `FBridge.lean:726`) with the raw bound's name moved. -/
theorem fBridge_aff_concentration (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_aff eps H a b h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_aff eps H a b h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 /
          (2 * (((eps : ℝ) ^ 2 * (H : ℝ) + 1) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2))) := by
  sorry

/-- **F2-B11 (class A) — the sharp (one-log) concentration bound at `(a, b, h)`**: the
`h`-script (`fBridge_h_concentration_sharp`, `FBridge.lean:752`) verbatim; `fBridge_var_le_sharp`
is reused and the exponent is IDENTICAL — the stride and the offset cost nothing in the
concentration grade. -/
theorem fBridge_aff_concentration_sharp (a b h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ)) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_aff eps H a b h v ω - ∑ p : primeWindow eps H,
            (uniformOn (Set.univ : Set (ZMod (PH eps H))))[fun ω =>
              fBridgeG_aff eps H a b h v p (residueProj eps H p ω)]|}
      ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) /
          (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)) := by
  sorry

/-- **F2-B12 (class A) — the sharp decoupled-mean corollary at `(a, b, h)`** — the deviation set
written with the FILTERED decoupled mean `∑_p (1/p) ∑_j 1_{j+1 ≡ pb (a)} v_j v_{j+ph}`
(`fBridgeG_aff_mean` substituted into `fBridge_aff_concentration_sharp`, as
`fBridge_h_concentration_decoupled_sharp`, `FBridge.lean:801`).  ⚠ SITE 2 of the synchronised
offset spellings: `badSet_aff` (F4) must spell this set byte-identically. -/
theorem fBridge_aff_concentration_decoupled_sharp (a b h : ℕ)
    {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) (heps : 0 < eps)
    (hne : (primeWindow eps H).Nonempty) {δ : ℝ} (hδ : 0 ≤ δ)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcard : ((primeWindow eps H).card : ℝ)
        ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)))
    (hlog : 1 ≤ Real.log (H : ℝ)) :
    (uniformOn (Set.univ : Set (ZMod (PH eps H)))).real
        {ω | δ ≤ |fBridgeF_aff eps H a b h v ω - ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
            ∑ j ∈ Finset.range H,
              if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
                (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ) else 0|}
      ≤ 2 * Real.exp (-δ ^ 2 * Real.log (H : ℝ) /
          (2 * C₀ * (eps : ℝ) ^ 2 * (H : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) ^ 2)) := by
  sorry

/-! ## F2-P — Prop 2.6 at the affine forms: the pointwise unfold and the `(p, r)`-collapse -/

/-- **F2-P1 (class B) — the pointwise F-bridge unfold at `(a, b, h)`, at ANY base point `m`.**
The twin of `fBridgeF_h_liouville_apply` (`Prop26.lean:212`) with `n ↦ m` and the filter riding
the gate: for each window prime `p` and `j < H` the gate `p ∣ m+j+1` AND the class `j+1 ≡ pb (a)`
select `λ(m+j+1)·(windowVal … (j + p·h))`.  Under the stride measure the base point is `m = a·n`
(`integral_logMeasureAff`), which is Tao's `an + j` (3.16).  The `h`-script transfers: `hgate`
is the landed `push_cast; ring` congruence, and the `if` splits on the conjunction (`by_cases hc :
gate; by_cases hf : filter; simp only [hc, hf, hgate, …]`, the kept branch closing by
`windowVal_liouvilleWindow H m j hjH`). -/
lemma fBridgeF_aff_liouville_apply (a b h : ℕ) (m : ℕ) :
    fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          if ((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0
              ∧ ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (ArithmeticFunction.liouville (m + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ)
          else 0 := by
  sorry

/-- **F2-P2 (class A) — the `(1, 0)` recovery of the pointwise unfold**, stated at the LANDED
conclusion of `fBridgeF_h_liouville_apply` and discharged through `fBridgeF_aff_one_zero`
(`rw [fBridgeF_aff_one_zero, fBridgeF_h_liouville_apply]`).  A conservativity check; it cannot
see the filter. -/
theorem fBridgeF_aff_liouville_apply_one_zero (h : ℕ) (m : ℕ) :
    fBridgeF_aff eps H 1 0 h (liouvilleWindow H m) (residueWindow eps H m)
      = ∑ p : primeWindow eps H, ∑ j ∈ Finset.range H,
          if ((m + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (m + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H m) (j + (p : ℕ) * h) : ℝ)
          else 0 := by
  sorry

/-- **F2-P3 (class A) — THE INDEX ARITHMETIC OF THE `(p, r)`-COLLAPSE AT STRIDE `a`.**  On the
residue class `n ≡ rⱼ (mod p)` realising the gate `p ∣ a·n + j + 1`, write `p·k = a·rⱼ + j + 1`
(the gate at the class representative); then at `n = p·m + rⱼ` the window index is a multiple
of `p`: `a·(p·m + rⱼ) + j + 1 = p·(a·m + k)`.  `subst`-free: `nlinarith`/`ring_nf` after `rw [←
hk]`, or `omega` (linear in `m` once `hk` is a hypothesis: `a·p·m + (a·rⱼ + j + 1) = p·a·m +
p·k`).  This is the line the freeze names "`a·r + j + 1` in place of `r + j + 1`". -/
lemma affGate_index_eq (a p j rj k m : ℕ) (hk : p * k = a * rj + j + 1) :
    a * (p * m + rj) + j + 1 = p * (a * m + k) := by
  sorry

/-- **F2-P4 (class A/B) — the multiplicativity collapse at stride `a`.**  With the gate
`p·k = a·rⱼ + j + 1` and `p ≠ 0`, the dilated pair collapses to the seed's shape at the base point
`a·m + k`: `λ(a(pm+rⱼ)+j+1)·λ(a(pm+rⱼ)+j+ph+1) = λ(am+k)·λ(am+k+h)`.  `affGate_index_eq` rewrites
both arguments (`a(pm+rⱼ)+j+ph+1 = p(am+k) + p·h` by `omega` from the first), then
`liouville_collapse_h p h hp (a*m+k)` (`ShiftFork.lean:472`) closes.  Downstream (F4) `k ≡ b
(mod a)` because `p·k ≡ j+1 ≡ p·b (mod a)` with `gcd(p, a) = 1` — the class filter is what makes
the collapsed base point `a·m' + b`, the seed's form; that congruence is NOT stated here. -/
lemma liouville_collapse_aff (a p j rj k m h : ℕ) (hp : p ≠ 0)
    (hk : p * k = a * rj + j + 1) :
    (ArithmeticFunction.liouville (a * (p * m + rj) + j + 1) : ℝ)
        * (ArithmeticFunction.liouville (a * (p * m + rj) + j + p * h + 1) : ℝ)
      = (ArithmeticFunction.liouville (a * m + k) : ℝ)
          * (ArithmeticFunction.liouville (a * m + k + h) : ℝ) := by
  sorry

/-- **F2-P5 (class A) — the per-pair dilation reduction at stride `a`.**  `dilation_error_div`
(`Dilation.lean:161`, generic in `f`) at `q ↦ p`, `r ↦ rⱼ`, `M ↦ 1` and
`f := fun n => λ(a·n + j + 1)·λ(a·n + j + p·h + 1)` — the twin of `perPair_dilation_h`
(`Prop26.lean:257`) with the window read at `a·n`.  The dilated summand is `f (p·m + rⱼ)`
beta-reduced: `a·(p·m + rⱼ) + j + 1` (the freeze's `a·r + j + 1`).  The `|f| ≤ 1` side condition
is the same two-factor bound (`abs_liouville_le_one`). -/
lemma perPair_collapse_aff {x ω : ℕ} (a h p j rj : ℕ) (hp : 1 ≤ p) (hrj : rj ≤ x / ω)
    {Z : ℝ} (hZ : 0 < Z) :
    |(∑ n ∈ (Finset.Ioc (x / ω) x).filter (fun n => n % p = rj),
        ((ArithmeticFunction.liouville (a * n + j + 1) : ℝ)
          * (ArithmeticFunction.liouville (a * n + j + p * h + 1) : ℝ)) / (n : ℝ)) / Z
        - 1 / (p : ℝ) *
          ((∑ m ∈ ((Finset.Ioc (x / ω) x).filter (fun n => n % p = rj)).image (fun n => n / p),
              ((ArithmeticFunction.liouville (a * (p * m + rj) + j + 1) : ℝ)
                * (ArithmeticFunction.liouville (a * (p * m + rj) + j + p * h + 1) : ℝ))
                / (m : ℝ)) / Z)|
      ≤ 2 * 1 * (rj : ℝ) / (p : ℝ) ^ 2 / Z := by
  sorry

/-! ## F2-C — the `(c₁, h211)` glue at the affine forms (the `ChowlaFailure` twins) -/

/-- **F2-C1 (class B) — Tao Prop 2.6 at the affine forms, EXPLICIT constant.**  From the seed
`hseed : δ ≤ |X_aff|` (`X_aff = ∫ λ(m+b)λ(m+b+h) ∂(logMeasureAff a x ω)`, produced by
`singleCorr_of_failsAff'`), the Mertens lower bound `hmert` (`a`-free) and the affine reduction
`hreduce_aff` — the F-bridge integral under the STRIDE measure dominates half the main term
`SP·(H/a)·|X_aff|`, the `H/a` being the class's share of the window (Tao (3.16)) — the affine
F-bridge expectation obeys `cM/(2a) · (δ·H/log H) ≤ |∫ F_aff|`.  The `h`-script
(`fBridge_of_singleCorr_h`, `Prop26.lean:286`) with `(H : ℝ)` read as `(H : ℝ) / a` in `hkey`'s
consumer and the constant `cM/2` read as `cM/(2a)` (`field_simp` at `0 < a`; at `a = 0` both
sides are `0`).  The constant is EXPLICIT so that F5's grade line reads `cM/(2a)` from the kernel,
not from prose. -/
theorem fBridge_of_singleCorr_aff (a b h : ℕ) {x ω : ℕ}
    (hlog : 1 ≤ Real.log (H : ℝ)) {cM : ℝ} (hcM : 0 < cM)
    (hmert : cM / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (hreduce : (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
          * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)|)
    {δ : ℝ} (hδ : 0 < δ)
    (hseed : δ ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|) :
    cM / (2 * (a : ℝ)) * (δ * (H : ℝ) / Real.log (H : ℝ))
      ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
          ∂(logMeasureAff a x ω)| := by
  sorry

/-- **F2-C2 (class A) — the same, in the consumer's `∃ c` shape** (the `hprop26` binder of
`h211_aff` below and of `h211_of_logChowla2Fails_h`).
`⟨cM / (2 * a), by positivity, fBridge_of_singleCorr_aff …⟩`; `0 < a` for the positivity. -/
theorem fBridge_of_singleCorr_aff' (a b h : ℕ) (ha : 0 < a) {x ω : ℕ}
    (hlog : 1 ≤ Real.log (H : ℝ)) {cM : ℝ} (hcM : 0 < cM)
    (hmert : cM / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
    (hreduce : (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * ((H : ℝ) / (a : ℝ))
          * |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)|)
    {δ : ℝ} (hδ : 0 < δ)
    (hseed : δ ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)|) :
    ∃ c : ℝ, 0 < c ∧
      c * (δ * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)| := by
  sorry

/-- **F2-C3 (class A) — Stmt 3 at the affine forms (compose to `h211`).**  The twin of
`h211_of_logChowla2Fails_h` (`ChowlaFailure.lean:254`): feed the affine seed
`singleCorr_of_failsAff'` (F1-N2, `δ := ε/2`, under the stride measure) into the affine
Prop-2.6 conclusion `hprop26` and take `c₁ := c/2`.  The glue arithmetic is the `h`-script
verbatim (`hEq` by `ring`).  The `a`-dependence is inside `c` (`cM/(2a)` when `hprop26` is
`fBridge_of_singleCorr_aff'`), so the exported `c₁` is `cM/(4a)` on that route — F4's budget
lines read `c₁ ↦ c₁/a` here and nowhere else. -/
theorem h211_aff (a b h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ)) (heps : 0 < eps)
    (hprop26 : ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ m, (ArithmeticFunction.liouville (m + b) : ℝ)
              * (ArithmeticFunction.liouville (m + b + h) : ℝ) ∂(logMeasureAff a x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
                ∂(logMeasureAff a x ω)|)
    (hfail : logChowlaFailsAff a b h eps x ω) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ m, fBridgeF_aff eps H a b h (liouvilleWindow H m) (residueWindow eps H m)
            ∂(logMeasureAff a x ω)| := by
  sorry

/-- **F2-C4 (class B) — the `(1, 0)` recovery of `h211`**, stated at the LANDED conclusion of
`h211_of_logChowla2Fails_h` (the `logMeasure` integral of `fBridgeF_h`) from the LANDED
`logChowlaFails h` hypothesis and the `h`-twin's own `hprop26` spelling, and discharged from
`h211_aff 1 0 h`: `logChowlaFailsAff_one_zero` (`AffineFork.lean:78`) converts `hfail`;
`logMeasureAff_one` and `fBridgeF_aff_one_zero` convert the integrals in both the binder and the
conclusion (`simp only [logMeasureAff_one, fBridgeF_aff_one_zero, zero_add] at *` — the seed's
summand is `λ(m + 0)·λ(m + 0 + h)`, hence the `zero_add`).  The kill-check that the affine family
SUBSUMES the `h`-family at its model point. -/
theorem h211_aff_one_zero (h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ)) (heps : 0 < eps)
    (hprop26 : ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
                ∂(logMeasure x ω)|)
    (hfail : logChowlaFails h eps x ω) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  sorry

end Salt.Entropy.Chowla
