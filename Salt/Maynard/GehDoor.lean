/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.Level
import Salt.BV.Defs

/-!
# The GEH door — `GEH_min` and its interface (design node D-N1)

Design freeze: `docs/exploration/s2-b3-design.md`, RE-CUT block (2026-07-17).
This file lands the *definitions* of the narrowed generalized-Elliott–Halberstam
door and its anti-vacuity trivia; the implication `GEH_min → HasLevel` (node
D-N2) and the composition to bounded gaps (D-N3) live downstream.

## What the door claims, honestly

`GEH_min θ` is a **weakening** of Polymath8b's generalized Elliott–Halberstam
conjecture GEH[θ] (arXiv:1407.4897, Claim 2.6): it is implied by GEH[θ], never
stronger — hence the name `_min`. Two deviations, both in the *weaker* (safe)
direction, and one faithful carry:

* **SW slot is a genuine hypothesis, family-indexed** (`SWAt`). The RE-CUT
  restores the `∃K` *before* `∀x` ordering of Siegel–Walfisz
  (`Salt/BV/Defs.lean`): demanding a single discrepancy constant uniform in `x`
  is the honest shape. (The earlier house freeze put `∃K` *after* `∀x`; the B3
  gate kernel-proved that form's SW slot vacuous — `swat_vacuous` — so `GEH_min`
  would have silently *dropped* the hypothesis and become *stronger* than GEH,
  the `_min` backwards. See `docs/exploration/pilot.md`, "THE B3 GATE: RE-CUT".)
  We keep P8b's `r`-coprimality restriction and its `τ(qr)^{O(1)}` divisor
  allowance (as `∃ j`), so `SWAt` is no stronger than GEH's SW input.
* **Coefficient class carries the τ-exponent `k` OUTSIDE the `∃B ∃C`**
  (`CoeffAt`): every fixed divisor-power exponent is covered, faithful to P8b's
  `≪ τ(n)^{O(1)} log^{O(1)}` coefficient bound.
* **Discrepancy cutoff is `4·N·M`** — the full convolution support of
  `dconv (α x) (β x)`, no truncation (R4).

## The consistency anchor (prose only)

`GEH_min θ` for `θ < 1/2` is a *theorem* (Motohashi; P8b Theorem 2.8), so the
Prop is not vacuously strong — there is a genuine unconditional regime below
`1/2`. This is stated, not formalized here (it is the reason the door is
believable, not a step in the door).

## What the door reaches, and what it does not

The door reaches the landed `H₁ ≤ 12` bounded-gaps conclusion **carrying
`WindowPNT`** — the π/ψ window PNT input is undischarged in-corpus, so the
honest chain is `GEH_min (3999/4000) → WindowPNT → H₁ ≤ 12`. There is **no
unconditional gap claim** anywhere in this arc. The `H₁ ≤ 6` sharpening (the
ε-enlarged Maynard functional `M₃^{[ε]} > 2` gap) is **explicitly out of
scope** here, per the TwinDoor D5 discipline (design node D-N5): stated, not
attempted.
-/

open Finset

/-- **Sequence discrepancy** at modulus `q`, weight `f`: the maximal (over
reduced residues `a mod q`) deviation of the residue-class weight sum from the
coprime *mean* `(∑_{coprime} f)/φ(q)`.  This is P8b's `Δ`-shaped main term (the
coprime mean, NOT a `π(x)/φ(q)`-style total).  Junk value `0` when `q = 0`;
consumers only ever sum over `q ≥ 1`. -/
noncomputable def seqDiscrepancy (f : ℕ → ℝ) (x q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
  ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup'
    (exists_coprime_lt hq) (fun a =>
      |(∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
        - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0)
          / (q.totient : ℝ)|)

/-- **Dirichlet convolution** of weights `α, β`: `(α ⋆ β)(n) = ∑_{d ∣ n} α(d)
β(n/d)`.  The bilinear form whose AP discrepancy `GEH_min` controls. -/
noncomputable def dconv (α β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, α d * β (n / d)

/-- **Coefficient class** (family-indexed): `α x` is supported on the dyadic
block `Ioc (N x) (2 N x)` and bounded by `τ(n)^k (log x)^k`.  The exponent `k`
is a *parameter* (carried outside the `∃B ∃C` of `GEH_min`), so every fixed
divisor-power is covered — faithful to P8b's `≪ τ^{O(1)} log^{O(1)}`. -/
def CoeffAt (α : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ x n, (α x n ≠ 0 → n ∈ Finset.Ioc (N x) (2 * N x)) ∧
    |α x n| ≤ (n.divisors.card : ℝ) ^ k * Real.log x ^ k

/-- **Siegel–Walfisz slot** (family-indexed, `∃K` BEFORE `∀x`).  For the family
`β`, there is a divisor-power exponent `j` such that for every log-power saving
`A` a single constant `K` (uniform in `x, r, q`) bounds the `r`-coprime-twisted
sequence discrepancy by `K τ(qr)^j (M x)/(log x)^A`.  This is the honest
Siegel–Walfisz shape (mirrors `Salt.BV.SiegelWalfisz`): the constant is chosen
BEFORE the point `x`, so it cannot silently absorb an `x`-growing discrepancy
(that failure is the gate's `swat_vacuous`, now excluded by construction). -/
def SWAt (β : ℕ → ℕ → ℝ) (M : ℕ → ℕ) : Prop :=
  ∃ j : ℕ, ∀ A : ℝ, 0 < A → ∃ K, 0 ≤ K ∧ ∀ x r q : ℕ,
    2 ≤ x → 0 < r → 0 < q →
    seqDiscrepancy (fun n => if Nat.Coprime n r then β x n else 0) x q
      ≤ K * ((q * r).divisors.card : ℝ) ^ j * (M x : ℝ) / Real.log x ^ A

/-- **The SW property at EXPLICIT data** `(j, KF)` — the `x`-uniform Siegel–Walfisz
slot with the divisor-power exponent `j` and the per-`A` constant function `KF`
named *outside* the `∀ x`.  This is the destructured form of `SWAt`: `SWAt` says
"there EXIST `j, KF`"; `SWAtData β M j KF` fixes them.  The constant `KF A` is
chosen BEFORE the point `x` (the honest ordering, mirroring
`Salt.BV.SiegelWalfisz`), so it cannot silently absorb an `x`-growing
discrepancy.  `GEH_min` quantifies over `(j, KF)` and picks its haircut `B`,
constant `C` uniformly in the family — matching P8b Claim 2.6's convention that
the implied `≪`-constant depends only on the fixed data (Def 1.6). -/
def SWAtData (β : ℕ → ℕ → ℝ) (M : ℕ → ℕ) (j : ℕ) (KF : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ x r q : ℕ, 2 ≤ x → 0 < r → 0 < q →
    seqDiscrepancy (fun n => if Nat.Coprime n r then β x n else 0) x q
      ≤ KF A * ((q * r).divisors.card : ℝ) ^ j * (M x : ℝ) / Real.log x ^ A

/-- **`SWAt` destructures to `SWAtData`.**  The family-level `SWAt β M` (an
`∃ j, ∀ A, ∃ K, …`) yields explicit data `(j, KF)` with `SWAtData β M j KF`:
take `j` from the outer `∃`, and let `KF A` be a valid constant `K` for each
`A > 0` (choice on the per-`A` existential; junk `0` off the positive ray).  The
bridge that lets a consumer holding `SWAt β M` feed the `(j, KF)`-indexed
`GEH_min`. -/
theorem sWAtData_of_sWAt {β : ℕ → ℕ → ℝ} {M : ℕ → ℕ} (h : SWAt β M) :
    ∃ j : ℕ, ∃ KF : ℝ → ℝ, SWAtData β M j KF := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  have hchoice : ∀ A : ℝ, ∃ K : ℝ, 0 < A →
      ∀ x r q : ℕ, 2 ≤ x → 0 < r → 0 < q →
        seqDiscrepancy (fun n => if Nat.Coprime n r then β x n else 0) x q
          ≤ K * ((q * r).divisors.card : ℝ) ^ j * (M x : ℝ) / Real.log x ^ A := by
    intro A
    by_cases hA : 0 < A
    · obtain ⟨K, _hK0, hK⟩ := hj A hA
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun hA' => absurd hA' hA⟩
  obtain ⟨KF, hKF⟩ := Classical.axiomOfChoice hchoice
  exact ⟨KF, fun A hA x r q hx hr hq => hKF A hA x r q hx hr hq⟩

/-- **The narrowed GEH door** `GEH_min θ` (house amendment, 2026-07-16: `x`- and
`y`-uniform).  For every `ε, A > 0`, every divisor-power `k`, and every SW data
`(j, KF)`, there is a single log-power haircut `B` and constant `C` — depending
only on `(ε, A, k, j, KF)`, *uniform over the whole coefficient/SW-admissible
family class* — such that for every balanced pair `(α, β)` on scales `(N, M)`
and every prefix cutoff `y ≤ 4 N M`, the summed AP discrepancy of `α x ⋆ β x`
over moduli `≤ x^θ/(log x)^B` is `≤ C x/(log x)^A`, in the window `N M ≤ x ≤ 4 N M`
with both scales in `[x^ε, x^{1-ε}]`.

Two faithfulness corrections over the earlier freeze, both toward P8b Claim 2.6
(Def 1.6: the implied constant depends only on the fixed data) and both keeping
`GEH_min ≤ P8b GEH[θ]` (the honest `_min` direction):

* **`∃ B C` moved OUTSIDE `∀ α β N M`** — `B, C` are uniform over the sequence
  class, not re-chosen per family.  The earlier `∃`-after-`∀` form was too weak:
  it let each family pick its own haircut, so the `O(log² x)` dyadic block-pair
  sum (each pair a distinct family) had no common `B` and the Type-II domination
  `hdom` was unsatisfiable.
* **Discrepancy cutoff is an arbitrary prefix `y ≤ 4 N M`**, not pinned at the
  top `4 N M` — P8b's `Δ` is controlled at every scale, which the Λ→π Abel
  bridge (`GehPiSeam`) consumes.

The SW slot is `SWAtData β M j KF` (the destructured, `x`-uniform `SWAt`); a
consumer holding `SWAt β M` feeds this via `sWAtData_of_sWAt`.  Discrepancy
cutoff `4 N M` = the full convolution support (R4).  Implied by P8b GEH[θ]; see
the module docstring for the honest-direction accounting. -/
def GEH_min (θ : ℝ) : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∀ k j : ℕ, ∀ KF : ℝ → ℝ, ∃ B C : ℝ, 0 ≤ B ∧
  ∀ α β : ℕ → ℕ → ℝ, ∀ N M : ℕ → ℕ,
    CoeffAt α N k → CoeffAt β M k → SWAtData β M j KF →
    ∀ x y : ℕ, 2 ≤ x → y ≤ 4 * N x * M x →
      (x : ℝ) ^ ε ≤ (N x : ℝ) → (N x : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      (x : ℝ) ^ ε ≤ (M x : ℝ) → (M x : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      N x * M x ≤ x → x ≤ 4 * N x * M x →
      (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
          seqDiscrepancy (dconv (α x) (β x)) y q)
        ≤ C * x / Real.log x ^ A

/-- `seqDiscrepancy` is nonnegative (a `sup'` of absolute values; junk `0` at
`q = 0`).  Mirrors `maxDiscrepancy_nonneg`. -/
theorem seqDiscrepancy_nonneg (f : ℕ → ℝ) (x q : ℕ) : 0 ≤ seqDiscrepancy f x q := by
  unfold seqDiscrepancy
  split
  · exact le_refl 0
  · rename_i hq
    obtain ⟨a0, ha0⟩ := exists_coprime_lt hq
    refine le_trans (abs_nonneg
      ((∑ n ∈ Finset.Icc 1 x, if n % q = a0 then f n else 0)
        - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0)
          / (q.totient : ℝ))) ?_
    exact Finset.le_sup'
      (fun a => |(∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
        - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0)
          / (q.totient : ℝ)|) ha0

/-- `GEH_min` is **antitone in `θ`** (a door at level `θ₂` gives one at any
smaller `θ₁ ≤ θ₂` — the same `B, C` witnesses work over the smaller modulus
range).  Mirrors `HasLevel_antitone`: the subset argument over the `Icc` of
moduli, closed by `seqDiscrepancy_nonneg`. -/
theorem GEH_min_antitone {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) (_hθ₁ : 0 ≤ θ₁)
    (hG : GEH_min θ₂) : GEH_min θ₁ := by
  intro ε A hε hA k j KF
  obtain ⟨B, C, hB0, hC⟩ := hG ε A hε hA k j KF
  refine ⟨B, C, hB0,
    fun α β N M hα hβ hSW x y hx hyle hNlo hNhi hMlo hMhi hNM hx4 => ?_⟩
  have hx1 : (1 : ℝ) < (x : ℝ) := by
    have : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hxr : (1 : ℝ) ≤ (x : ℝ) := le_of_lt hx1
  have hden : (0 : ℝ) < Real.log x ^ B := Real.rpow_pos_of_pos (Real.log_pos hx1) B
  have hsub : Finset.Icc 1 ⌊(x : ℝ) ^ θ₁ / Real.log x ^ B⌋₊
      ⊆ Finset.Icc 1 ⌊(x : ℝ) ^ θ₂ / Real.log x ^ B⌋₊ := by
    apply Finset.Icc_subset_Icc_right
    apply Nat.floor_le_floor
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hxr h)
      (le_of_lt (inv_pos.mpr hden))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q _ _ => seqDiscrepancy_nonneg _ _ _)).trans
    (hC α β N M hα hβ hSW x y hx hyle hNlo hNhi hMlo hMhi hNM hx4)

/-- **Soundness compat: the new `GEH_min` implies the OLD (pointwise, `∃`-after-`∀`,
top-cutoff) shape.**  Recovers exactly the pre-amendment statement — for each family
a haircut/constant `∃ B C` and the top-cutoff `4 N M` discrepancy bound — by
destructuring `SWAt β M` to `(j, KF)` (`sWAtData_of_sWAt`) and specialising the new
door at cutoff `y := 4 N M`.  Confirms the amendment only STRENGTHENED the door
(nothing the old form asserted was lost): downstream soundness is preserved. -/
theorem GEH_min_implies_pointwise {θ : ℝ} (hG : GEH_min θ) :
    ∀ ε A : ℝ, 0 < ε → 0 < A → ∀ k : ℕ, ∀ α β : ℕ → ℕ → ℝ, ∀ N M : ℕ → ℕ,
      CoeffAt α N k → CoeffAt β M k → SWAt β M →
      ∃ B C : ℝ, 0 ≤ B ∧ ∀ x : ℕ, 2 ≤ x →
        (x : ℝ) ^ ε ≤ (N x : ℝ) → (N x : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
        (x : ℝ) ^ ε ≤ (M x : ℝ) → (M x : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
        N x * M x ≤ x → x ≤ 4 * N x * M x →
        (∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ / Real.log x ^ B⌋₊,
            seqDiscrepancy (dconv (α x) (β x)) (4 * N x * M x) q)
          ≤ C * x / Real.log x ^ A := by
  intro ε A hε hA k α β N M hα hβ hSW
  obtain ⟨j, KF, hSWData⟩ := sWAtData_of_sWAt hSW
  obtain ⟨B, C, hB0, hbound⟩ := hG ε A hε hA k j KF
  refine ⟨B, C, hB0, fun x hx hNlo hNhi hMlo hMhi hNM hx4 => ?_⟩
  exact hbound α β N M hα hβ hSWData x (4 * N x * M x) hx (le_refl _)
    hNlo hNhi hMlo hMhi hNM hx4

/-- `seqDiscrepancy` of the identically-zero weight is `0` (every residue-class
sum and coprime mean vanish).  The base fact behind the honest SW inhabitation
`swat_zero_family`. -/
theorem seqDiscrepancy_const_zero (x q : ℕ) :
    seqDiscrepancy (fun _ => (0 : ℝ)) x q = 0 := by
  refine le_antisymm ?_ (seqDiscrepancy_nonneg _ _ _)
  unfold seqDiscrepancy
  split
  · exact le_refl 0
  · rename_i hq
    apply Finset.sup'_le
    intro a _
    simp

/-- **Honest SW inhabitation** (anti-vacuity, D-N1(i) minimal witness).  The
zero family satisfies `SWAt`: its twisted discrepancy is identically `0 ≤` any
nonnegative bound.  This is the *minimal* non-vacuous witness — it certifies
`SWAt` is not empty without asserting anything false.  (The constant-on-range
family, whose discrepancy is a genuine small quantity, is deferred to D-N2 —
see the friction note; it is not cheap here.) -/
theorem swat_zero_family (M : ℕ → ℕ) : SWAt (fun _ _ => 0) M := by
  refine ⟨0, fun A _hA => ⟨0, le_refl 0, fun x r _q _hx _hr _hq => ?_⟩⟩
  have hfun : (fun n => if Nat.Coprime n r then (fun _ _ => (0 : ℝ)) x n else 0)
      = (fun _ => (0 : ℝ)) := by
    funext n; simp
  rw [hfun, seqDiscrepancy_const_zero]
  simp

/-! ### The π-seam (design node D-N1(ii))

The consumable BV target `maxDiscrepancy` (`Salt/Maynard.lean`) is π-based with
main term `π(x)/φ(q)`; `seqDiscrepancy` of the prime indicator has main term the
coprime *mean* `(#coprime primes)/φ(q)`.  The two differ only in the mean, and
the mean gap is exactly the primes DIVIDING `q` — at most `ω(q) = |primeFactors
q|`, each counted once — so the seam costs `ω(q)/φ(q)`.  D-N2c consumes
`maxDiscrepancy_le_seqDiscrepancy_prime`. -/

/-- **Numerator identity.**  The prime-indicator weight summed over the residue
class `a mod q` on `[1,x]` is exactly `π(x;q,a) = primesCount x q a` (the `n = 0`
term of the `Nat.count` range is dropped since `0` is not prime). -/
theorem residueSum_prime_eq_primesCount (x q a : ℕ) :
    (∑ n ∈ Finset.Icc 1 x,
        if n % q = a then (if n.Prime then (1 : ℝ) else 0) else 0)
      = (primesCount x q a : ℝ) := by
  have hcongr : ∀ n ∈ Finset.Icc 1 x,
      (if n % q = a then (if n.Prime then (1 : ℝ) else 0) else 0)
        = if (n.Prime ∧ n % q = a) then (1 : ℝ) else 0 := by
    intro n _
    by_cases h : n % q = a <;> by_cases hp : n.Prime <;> simp [h, hp]
  have hfilt : (Finset.Icc 1 x).filter (fun n => n.Prime ∧ n % q = a)
      = (Finset.range (x + 1)).filter (fun n => n.Prime ∧ n % q = a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_, hnx⟩, hp, hr⟩; exact ⟨hnx, hp, hr⟩
    · rintro ⟨hnx, hp, hr⟩; exact ⟨⟨by have := hp.two_le; omega, hnx⟩, hp, hr⟩
  rw [Finset.sum_congr rfl hcongr, Finset.sum_boole]
  unfold primesCount
  rw [Nat.count_eq_card_filter_range, hfilt]

/-- **Coprime-mean gap.**  The total prime count `π(x) = primesCount x 1 0`
exceeds the coprime-restricted prime count by exactly the primes dividing `q`,
of which there are at most `ω(q) = |q.primeFactors|`.  This is the entire cost
of the π-seam. -/
theorem primeMean_gap_le (x q : ℕ) (hq : q ≠ 0) :
    |(primesCount x 1 0 : ℝ)
        - (∑ n ∈ Finset.Icc 1 x,
            if Nat.Coprime n q then (if n.Prime then (1 : ℝ) else 0) else 0)|
      ≤ (q.primeFactors.card : ℝ) := by
  have Pi_eq : (primesCount x 1 0 : ℝ)
      = (((Finset.Icc 1 x).filter (fun n => n.Prime)).card : ℝ) := by
    rw [← residueSum_prime_eq_primesCount x 1 0]
    have hc : ∀ n ∈ Finset.Icc 1 x,
        (if n % 1 = 0 then (if n.Prime then (1 : ℝ) else 0) else 0)
          = if n.Prime then (1 : ℝ) else 0 := by
      intro n _; simp [Nat.mod_one]
    rw [Finset.sum_congr rfl hc, Finset.sum_boole]
  have Scop_eq : (∑ n ∈ Finset.Icc 1 x,
        if Nat.Coprime n q then (if n.Prime then (1 : ℝ) else 0) else 0)
      = (((Finset.Icc 1 x).filter (fun n => n.Prime ∧ Nat.Coprime n q)).card : ℝ) := by
    have hc : ∀ n ∈ Finset.Icc 1 x,
        (if Nat.Coprime n q then (if n.Prime then (1 : ℝ) else 0) else 0)
          = if (n.Prime ∧ Nat.Coprime n q) then (1 : ℝ) else 0 := by
      intro n _; by_cases h : Nat.Coprime n q <;> by_cases hp : n.Prime <;> simp [h, hp]
    rw [Finset.sum_congr rfl hc, Finset.sum_boole]
  rw [Pi_eq, Scop_eq]
  set S1 := (Finset.Icc 1 x).filter (fun n => n.Prime) with hS1
  set S2 := (Finset.Icc 1 x).filter (fun n => n.Prime ∧ Nat.Coprime n q) with hS2
  have hsub : S2 ⊆ S1 := by
    rw [hS1, hS2]; intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have hkey : S1 \ S2 ⊆ q.primeFactors := by
    intro n hn
    rw [Finset.mem_sdiff, hS1, hS2, Finset.mem_filter, Finset.mem_filter] at hn
    obtain ⟨⟨hnI, hnp⟩, hnot⟩ := hn
    have hncop : ¬ Nat.Coprime n q := fun hcop => hnot ⟨hnI, hnp, hcop⟩
    have hdvd : n ∣ q := by
      by_contra hnd
      exact hncop ((Nat.Prime.coprime_iff_not_dvd hnp).mpr hnd)
    exact Nat.mem_primeFactors.mpr ⟨hnp, hdvd, hq⟩
  have hcard : (S1 \ S2).card ≤ q.primeFactors.card := Finset.card_le_card hkey
  have hsdiff : (S1 \ S2).card = S1.card - S2.card := Finset.card_sdiff_of_subset hsub
  have hle : S2.card ≤ S1.card := Finset.card_le_card hsub
  have hlecast : (S2.card : ℝ) ≤ (S1.card : ℝ) := by exact_mod_cast hle
  rw [abs_of_nonneg (by linarith)]
  have hcast : (S1.card : ℝ) - (S2.card : ℝ) = ((S1.card - S2.card : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]
  rw [hcast, ← hsdiff]
  exact_mod_cast hcard

/-- Each per-residue term of `seqDiscrepancy` is `≤` the whole `sup'` (for any
weight `f` and any reduced residue `a`).  The `le_sup'` projection, stated with
a general `f` so it applies without beta-reduction friction. -/
theorem seqDiscrepancy_apply_le (f : ℕ → ℝ) (x q a : ℕ) (hq : q ≠ 0)
    (ha : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q)) :
    |(∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
      - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0) / (q.totient : ℝ)|
      ≤ seqDiscrepancy f x q := by
  unfold seqDiscrepancy
  rw [dif_neg hq]
  exact Finset.le_sup'
    (fun a => |(∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
      - (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0) / (q.totient : ℝ)|) ha

/-- **The π-seam** (design node D-N1(ii); gate-verified sound).  The π-based BV
target `maxDiscrepancy` is bounded by the coprime-mean sequence discrepancy of
the prime indicator plus the seam cost `ω(q)/φ(q)`.  This lets D-N2c convert the
`GEH_min`-controlled `seqDiscrepancy` back to the landed `maxDiscrepancy` that
`HasLevel` sums; the extra `ω(q)/φ(q)`, summed over `q`, is polylog `≪ x/log^A`. -/
theorem maxDiscrepancy_le_seqDiscrepancy_prime (x q : ℕ) (hq : 0 < q) :
    maxDiscrepancy x q
      ≤ seqDiscrepancy (fun n => if n.Prime then (1 : ℝ) else 0) x q
        + (q.primeFactors.card : ℝ) / (q.totient : ℝ) := by
  have hq0 : q ≠ 0 := hq.ne'
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold maxDiscrepancy
  rw [dif_neg hq0]
  apply Finset.sup'_le
  intro a ha
  have hnum := residueSum_prime_eq_primesCount x q a
  have hgap := primeMean_gap_le x q hq0
  have hterm :
      |(∑ n ∈ Finset.Icc 1 x, if n % q = a then (if n.Prime then (1 : ℝ) else 0) else 0)
        - (∑ n ∈ Finset.Icc 1 x,
            if Nat.Coprime n q then (if n.Prime then (1 : ℝ) else 0) else 0)
          / (q.totient : ℝ)|
      ≤ seqDiscrepancy (fun n => if n.Prime then (1 : ℝ) else 0) x q :=
    seqDiscrepancy_apply_le _ x q a hq0 ha
  set φ : ℝ := (q.totient : ℝ) with hφ
  set NUMa : ℝ := ∑ n ∈ Finset.Icc 1 x, if n % q = a then (if n.Prime then (1 : ℝ) else 0) else 0
    with hNUMa
  set MEAN : ℝ := ∑ n ∈ Finset.Icc 1 x,
      if Nat.Coprime n q then (if n.Prime then (1 : ℝ) else 0) else 0 with hMEAN
  set S : ℝ := seqDiscrepancy (fun n => if n.Prime then (1 : ℝ) else 0) x q with hS
  rw [← hnum]
  calc |NUMa - (primesCount x 1 0 : ℝ) / φ|
      = |(NUMa - MEAN / φ) + (MEAN / φ - (primesCount x 1 0 : ℝ) / φ)| := by
        congr 1; ring
    _ ≤ |NUMa - MEAN / φ| + |MEAN / φ - (primesCount x 1 0 : ℝ) / φ| := abs_add_le _ _
    _ ≤ S + (q.primeFactors.card : ℝ) / φ := by
        apply add_le_add hterm
        rw [div_sub_div_same, abs_div, abs_of_pos hφpos, div_le_div_iff_of_pos_right hφpos,
          abs_sub_comm]
        exact hgap
