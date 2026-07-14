/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PieceDecomp

/-!
# BND — the ordering band via the symmetry split (catch #56's resolution)

Design: `docs/blueprints/flags.md`, the `2026-07-14 WBV6 … ★ CATCH #56 ★` entry (the FROZEN
symmetry-split design) and the `WBV3`/`WBV4`/`WBV5` entries (the cutoff-carrier machinery this
node feeds into).  The target is `PieceDecomp.hBlock_of_window_prices`'s **named low-piece band
slot** `Plo`, i.e. the `L¹`-over-`d` sum

  `∑_k ∑_{d<bound} |blockBoxHonestDisc x z y ε₀ j (pieceN k) (pieceM k)`
  `      (min (z·pieceN k + 1) (x+1)) (x+1) d|`

— each summand is the discrepancy of the **band sub-box** `[c k, x+1) × (N, M]` (`c k =
min (z·N+1, x+1)`), the residual the corner-free identification `WindowSW.blockBox_windowDisc_eq`
cannot reach (its `hord : b ≤ z·N+1` fails on the band, whose `m`-range STARTS at `z·N+1`).

## ★ Item 3 — NUMERIC PLAN (recorded FIRST): the diagonal is crude, the symmetric part is BV ★

Fix a band box `(j, k)`, `N = pieceN k = 2^k−1`, `M = pieceM k = 2^{k+1}−1`.  Its triples are
`(p₁, p₂, p₃)` with `p₁ ∈ block j`, `y < p₂ ≤ p₃`, `p₃ ∈ (N, M]`, `p₁p₂ ≥ z·N+1`, `window`,
`prod ≡ 2 (mod d)`.  Split the ORDERING `p₂ ≤ p₃`:

* **The diagonal `p₂ = p₃` (crude, this file).**  `prod = p₁·p²` with `p = p₂ = p₃ ∈ (N, M]`,
  `p₁ ∈ [z, y]`.  These triples inject into their `(p₁, p₃)` projection
  (`bandDiagCount_le_pairCard`), so per box `#diag ≤ #(Icc 1 y × Ioc N M) = y·(M−N)`.  The HONEST
  global arithmetic: `p₁p² ≤ x` ⟹ `p ≤ √(x/p₁)`, so summing the `π`-refined count over
  `p₁ ≤ y = x^{1/3}` gives `∑_{p₁≤y} π(√(x/p₁)) ≪ √x · ∑_{p₁≤y} p₁^{−1/2} ≪ √x·√y/log x =
  x^{2/3}/log x`.  Then `∑_{d<bound} (resCount_diag + ν·unitCount_diag) ≤ #diag·(1 + ∑_{d<bound}
  ν(d)) + ∑_{diag t} τ(prod−2) ≪ x^{2/3}·(C log x) + x^{2/3+o(1)} ≪ x/(log x)^{10}` ✓
  (`x^{2/3+o(1)}` beats every `(log x)^c`).  So the diagonal genuinely clears the budget.

* **The symmetric part `p₂ ≠ p₃` (BV, downstream).**  For a symmetric summand the ordered sum is
  `½·(the full block×block double sum + the diagonal)` — `sum_symm_ordered_split` (this file).
  The full double sum over `(p₂, p₃)` UNORDERED is a CLEAN `(m, n)`-rectangle at the cutoff carrier
  (window rides in `T`), priced verbatim by `WindowClose.general_BV_cutoff_final`.

## ★ CATCH #56b (STRUCTURAL SURPRISE — the symmetric-summand verification FAILS as designed) ★

The FROZEN design ("the ordered band = ½·(the UNORDERED **block×block** sum + the diagonal)")
assumes the band box's two large primes `p₂, p₃` BOTH range over the piece `(N, M]`.  **They do
not.**  The band box is `{p₃ ∈ (N,M], p₂ ≤ p₃, m = p₁p₂ ≥ z·N+1}` (its `m`-threshold is the FROZEN
`PieceDecomp` split point, unchangeable).  For pieces with `N > y` (which exist and carry the band
whenever `y < N < x/z`, a non-empty range since `z < y`), the constraint `m ≥ z·N+1` does NOT force
`p₂ > N`: with `p₁` near `y` and `p₂ ∈ (y, N]`, one has `m = p₁p₂ ≥ z·N+1` yet `p₂ ≤ N < p₃`.
Concretely `2^k ∈ (x^{1/3}, √(x/z))`, `p₂ ∈ (y, 2^k)`, `p₁ ∈ (z·2^k/p₂, y]`, `p₃ ∈ [2^k, 2^{k+1})`
is a valid band triple with `p₂` in a STRICTLY LOWER dyadic band than `p₃`.  So

  band box = {p₂, p₃ ∈ (max(y,N), M], p₂ ≤ p₃}   (SYMMETRIC — the design's ½-split applies)
           ⊔ {p₂ ∈ (y, N], p₃ ∈ (N, M]}          (Part 2 — p₂ in a lower band, N > y only).

Part 2 is a `Θ(x·loglog x/log x)`-chunk (NOT the diagonal, NOT `≤ x/(log x)^{10}`): it is its own
oriented semiprime × prime **rectangle** `α_low(m) = [m = p₁p₂, p₁ ∈ block j, y < p₂ ≤ N]` (an
`m`-intrinsic `0/1` indicator, ordering automatic since `p₂ ≤ N < p₃`), priced by
`general_BV_cutoff_final` at its own cutoff — but it is ABSENT from the frozen design.  Discharging
`Plo` therefore needs, per band box, TWO BV-priced rectangles (`α_sym` over `(max(y,N),M]` + the
½-split, and `α_low` over `(y,N]`) plus the crude diagonal — a design amendment (adding `α_low`,
and the `max(y,N)` threshold nuance) that is Fable/human-tier.  **Recorded in the closing flag,
`docs/blueprints/flags.md` "2026-07-14 BND".**

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* **FLOOR A(i) — `sum_symm_ordered_split`.**  The exact `½`-symmetry identity: for a symmetric
  weight `w`, `2·∑_{p ≤ q ∈ S} w p q = ∑_{S×S} w + ∑_{p∈S} w p p`.  General/reusable — the algebraic
  heart of the symmetric part (the eventual resolution consumes it with `S` = the piece prime set
  and `w` the residue/window weight).

* **FLOOR A(ii) — `bandDiagCount` + `bandDiagCount_le_pairCard`/`bandDiagCount_le`.**  The crude
  diagonal kernel: the `p₂ = p₃` band triples inject into `(p₁, p₃)`, so their count is
  `≤ y·(M−N)`.  The `x^{2/3}` global bound is the item-3 arithmetic above (`π`-refined, downstream).

The band-box → rectangle connection (FLOOR B) and the composed `Plo_discharge` (FULL) are BLOCKED
on the catch-#56b amendment above and are deliberately NOT attempted here.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the abstract symmetry-split identity (FLOOR A(i)) -/

/-- **`sum_symm_ordered_split` (FULL — the `½`-identity).**  For a symmetric weight `w` on a finite
set `S`, twice the ordered (`≤`) pair sum equals the full product sum plus the diagonal sum:
`2·∑_{(p,q)∈S×S, p≤q} w p q = ∑_{(p,q)∈S×S} w p q + ∑_{p∈S} w p p`.

The algebraic core of the band's symmetry split (catch #56).  Proof: `S×S` is covered by the
`≤`-filter `A` and the `≥`-filter `B` with intersection the diagonal
(`Finset.sum_union_inter`); `B`'s sum equals `A`'s via the swap `Prod.swap` and the symmetry of
`w`; the diagonal filter reindexes to `∑_{p∈S} w p p` via `p ↦ (p, p)`. -/
theorem sum_symm_ordered_split {ι : Type*} [LinearOrder ι]
    (S : Finset ι) (w : ι → ι → ℝ) (hsymm : ∀ a b, w a b = w b a) :
    2 * ∑ q ∈ (S ×ˢ S).filter (fun q => q.1 ≤ q.2), w q.1 q.2
      = (∑ q ∈ S ×ˢ S, w q.1 q.2) + ∑ p ∈ S, w p p := by
  classical
  set A := (S ×ˢ S).filter (fun q => q.1 ≤ q.2) with hA
  set B := (S ×ˢ S).filter (fun q => q.2 ≤ q.1) with hB
  -- `A ∪ B = S ×ˢ S` (totality of `≤`).
  have hunion : A ∪ B = S ×ˢ S := by
    rw [hA, hB, ← Finset.filter_or]
    exact Finset.filter_true_of_mem (fun q _ => le_total q.1 q.2)
  -- `A ∩ B` = the diagonal filter (antisymmetry).
  have hinter : A ∩ B = (S ×ˢ S).filter (fun q => q.1 = q.2) := by
    rw [hA, hB, ← Finset.filter_and]
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2
    · intro he; exact ⟨he.le, he.ge⟩
  -- `∑_B = ∑_A` via the swap + symmetry.
  have hBA : ∑ q ∈ B, w q.1 q.2 = ∑ q ∈ A, w q.1 q.2 := by
    apply Finset.sum_bij' (fun q _ => Prod.swap q) (fun q _ => Prod.swap q)
    · intro q hq
      rw [hB, Finset.mem_filter, Finset.mem_product] at hq
      rw [hA, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
    · intro q hq
      rw [hA, Finset.mem_filter, Finset.mem_product] at hq
      rw [hB, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
    · intro q _; simp
    · intro q _; simp
    · intro q _; exact hsymm q.1 q.2
  -- the diagonal filter reindexes to `∑_{p∈S}`.
  have hset : (S ×ˢ S).filter (fun q => q.1 = q.2) = S.image (fun p => (p, p)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, _⟩, he⟩; exact ⟨q.1, h1, (Prod.ext_iff.mpr ⟨rfl, he⟩)⟩
    · rintro ⟨p, hp, hpq⟩; rw [← hpq]; exact ⟨⟨hp, hp⟩, rfl⟩
  have hdiag : ∑ q ∈ (S ×ˢ S).filter (fun q => q.1 = q.2), w q.1 q.2 = ∑ p ∈ S, w p p := by
    rw [hset, Finset.sum_image (fun a _ b _ hab => (Prod.ext_iff.mp hab).1)]
  -- assemble via `sum_union_inter`.
  have hui := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun q => w q.1 q.2)
  rw [hunion, hinter, hdiag, hBA] at hui
  rw [two_mul]
  linarith [hui]

/-! ## Part B — the diagonal crude count kernel (FLOOR A(ii)) -/

/-- **`bandDiagCount`** — the `p₂ = p₃` band triples of the box `(j, (N, M])`: block-`j` triples
with the two large primes EQUAL and in the piece `(N, M]`.  The diagonal of the symmetry split;
its honest discrepancy is crude-bounded by this count (`|disc| ≤ resCount + ν·unitCount ≤ count`).
No residue filter (the crude count ignores it). -/
noncomputable def bandDiagCount (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) : ℝ :=
  (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ t.2.1 = t.2.2 ∧
     N < t.2.2 ∧ t.2.2 ≤ M)).card : ℝ)

/-- **`bandDiagCount_le_pairCard` (FULL — the diagonal injection).**  Each diagonal band triple
`(p₁, p, p)` is recovered from its projection `(p₁, p₃)` (the equal-primes constraint pins
`p₂ = p₃`), so the diagonal count is `≤ #(Icc 1 y × Ioc N M)`.  The crude kernel of item 3. -/
theorem bandDiagCount_le_pairCard (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) :
    bandDiagCount x z y ε₀ j N M ≤ ((Finset.Icc 1 y ×ˢ Finset.Ioc N M).card : ℝ) := by
  classical
  unfold bandDiagCount
  rw [Nat.cast_le]
  apply Finset.card_le_card_of_injOn (fun t => (t.1, t.2.2))
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨htri, _hblk, _hdiag, hN, hM⟩ := ht
    rw [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc] at htri
    obtain ⟨⟨⟨h1lo, _⟩, _, _⟩, _hz, hp1y, _⟩ := htri
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ioc]
    exact ⟨⟨h1lo, hp1y⟩, hN, hM⟩
  · intro t ht t' ht' heq
    rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨_, _, hdiag, _, _⟩ := ht
    obtain ⟨_, _, hdiag', _, _⟩ := ht'
    rw [Prod.mk.injEq] at heq
    obtain ⟨h1, h3⟩ := heq
    have h2 : t.2.1 = t'.2.1 := by rw [hdiag, h3, ← hdiag']
    exact Prod.ext h1 (Prod.ext h2 h3)

/-- **`bandDiagCount_le` (FULL — the explicit crude form).**  `#diag ≤ y·(M − N)` per box: the
projection pair set has `#(Icc 1 y × Ioc N M) = y·(M − N)` (natural subtraction, `0` when the
piece is empty).  The `x^{2/3}` global bound follows by the `π`-refinement of item 3
(`∑_{p₁≤y} π(√(x/p₁)) ≪ x^{2/3}/log x`, downstream). -/
theorem bandDiagCount_le (x z y : ℕ) (ε₀ : ℝ) (j N M : ℕ) :
    bandDiagCount x z y ε₀ j N M ≤ (y : ℝ) * ((M - N : ℕ) : ℝ) := by
  refine (bandDiagCount_le_pairCard x z y ε₀ j N M).trans ?_
  rw [Finset.card_product, Nat.card_Icc, Nat.card_Ioc, show y + 1 - 1 = y from by omega,
    Nat.cast_mul]

end Salt.Chen
