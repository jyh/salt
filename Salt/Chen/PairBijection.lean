/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.BlockPricing

/-!
# PBJ — the pair-bijection + window identification (the switch line's last bridge)

Design: `docs/blueprints/flags.md`, entries "2026-07-13 BVP Opus done (block pricing composed;
the pair bijection is the last bridge)" and "2026-07-13 SW3d Opus done … ★ CATCH #50 ★"
(findings SW3d-i/ii/iii).

This file discharges the honest core of the NAMED `hHD` slot of `BlockPricing`'s
`hBVblocks_of_generalBV` / `hHDblocks_of_perBlock`.  Quoting the exact target (BlockPricing.lean):

  `hHD : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),`
  `          ∑ d ∈ Nat.divisors Ps,`
  `            if (d : ℝ) < Q * Dlev then |blockHonestDisc x z y ε₀ j d| else 0) ≤ RHD`

The one step that BVP left NAMED is the per-`(j, p₃-piece)` **pair-bijection + window
identification**: turning a `blockHonestDisc` (a `tripleSet` residue/unit-count discrepancy) into
the `apDiscBilin` double sums the `general_BV_alpha_final` engine prices, via
`(p₁,p₂,p₃) ↦ (m, p) = (p₁·p₂, p₃)` (`semiprimeBlockInd`/`blockAlpha` multiplicity — SW3d-iii, the
bridge that was NOT in the corpus).

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* **FLOOR A — the pair bijection (`blockBox_pair_card`).**  For any class predicate `P`, the
  block-`j` triples whose `m = p₁p₂ ∈ [a, b)`, `p₃ ∈ (N, M]`, and `P(p₁p₂p₃)` correspond
  **bijectively** to the `(m, n)` pairs with `blockAlpha`-weight `1`, `n` a `(N, M]`-prime, and
  `P(m·n)` — the honest `(p₁,p₂,p₃) ↦ (p₁p₂, p₃)` bijection (`m` ↦ the ORIENTED `{p₁,p₂}` by unique
  factorization: `prime_pair_unique`).  Mirrors `SwitchBV.switchSieve_multSum_eq_apCount`'s
  fiberwise pattern, lifted to a genuine `Finset.card_bij` on the `(m,n)`-plane.

* **FLOOR B — the window identification on a DECIDED box (`blockBox_apDiscBilin_eq`,
  `norm_blockBox_apDiscBilin_eq`).**  On a `(j, [a,b)×(N,M])` box that is corner-decided-in-window
  (`SwitchStrip.productInWindow_of_corners`: `x/2+2 ≤ a(N+1)`, `(b-1)M ≤ x`) AND ordering-cleared
  (`b ≤ zN+1` ⟹ `p₂ ≤ N < p₃` automatically), the box's honest discrepancy is EXACTLY an
  `apDiscBilin` at the decided coefficient `restrictAlpha (blockAlpha j) a b`:
  `‖apDiscBilin (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d‖`
    `= |blockBoxResCount − nuChen d · blockBoxUnitCount|`.
  The main-term convention reconciles on the nose: `apDiscBilin`'s `(1/φd)·unit-count`
  IS `nuChen d · blockBoxUnitCount` (`nuChen_eq_inv_totient`).  The `α`-additivity backbone
  (`SwitchStrip.apDiscBilin_sum_alpha`) then sums the decided boxes coherently.

## ★ SHAPE MISMATCH FOUND — the FULL `blockHonestDisc_le_apDiscBilin_sum` is NOT provable as
   shaped (STOP-AND-FLAG, designer decision) ★

The FULL identification asks that `|blockHonestDisc_j d|` (the whole `tripleSet` discrepancy) be a
finite sum of `apDiscBilin (restrictAlpha (blockAlpha j) a b) (blockPrimeInd N) X M 2 d` terms over
the decided + band `α`-parts of `O(log x)` dyadic `p₃`-pieces.  Working the identification honestly
surfaces two genuine obstructions — exactly catch #50's findings SW3d-ii/iii, which the BVP flag's
"band-by-discrepancy dissolves the count-wall" was optimism, not a proof:

1. **The window BAND is a hyperbolic staircase, not a rectangle (SW3d-ii).**  `blockHonestDisc` is
   the WINDOWED (`x/2+2 ≤ p₁p₂p₃ ≤ x`) discrepancy.  A decided-in box has the window redundant
   (this file's `blockBox_apDiscBilin_eq`).  A *crossing* (band) `m`-interval does NOT: the window
   boundary `m·p = x` sweeps `m = x/p` across the piece, so the band's WINDOWED count differs from
   its full-rectangle `apDiscBilin` by the out-of-window part.  `apDiscBilin (restrictAlpha
   (blockAlpha j) a' b')` measures the FULL rectangle `[a',b')×(N,M]`, and a signed discrepancy over
   a sub-region is NOT bounded by the discrepancy over the whole region — so the band's contribution
   to `blockHonestDisc` is NOT `‖apDiscBilin(band α)‖`.  No finite axis-aligned sub-tiling makes the
   hyperbola redundant (a crossing cell always remains); the honest band price is the 2-D
   `m`-and-`p` sub-split + a residual singleton-`m` prime-AP mini-BV
   (`SwitchStrip.apDiscBilin_singleton_collapse`), NOT a `restrictAlpha (blockAlpha j) a' b'`
   rectangle term.  The `hHD` RHS as shaped carries NO such extra term.

2. **The ordering `p₂ ≤ p₃` is a joint `m`-`n` constraint absent from `blockAlpha` (SW3d-iii /
   the SW3c `boxCorr` diagonal).**  `tripleSet` carries `p₂ ≤ p₃`; `blockAlpha j m` records only
   the existence of `m = p₁p₂` with `z ≤ p₁ ≤ y < p₂` — NO reference to `p₃`.  So
   `apDiscBilin (blockAlpha j) (blockPrimeInd N)` counts UN-ordered pairs.  The ordering is
   `apDiscBilin`-decidable only on the `m`-upper-corner `b ≤ zN+1` (`blockBox_apDiscBilin_eq`'s
   `hord`, since `p₂ ≤ m/z < b/z ≤ N+1`); off that corner an ordering-crossing diagonal band
   remains, which — like the window band — is not a `restrictAlpha (blockAlpha j)` rectangle.

**Consequence.**  The decided part is honestly identified here (`blockBox_apDiscBilin_eq`).  The
band + ordering-diagonal remainder needs a slot with an explicit residual mini-BV term (the 2-D
strip), a Fable-tier revision of the `hHD` RHS shape.  Recorded in the closing flag
`docs/blueprints/flags.md`, "2026-07-13 PBJ".

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the box residue / unit counts and the pair predicate -/

open Classical in
/-- **`blockBoxResCount`** — block-`j` triples with `m = p₁p₂ ∈ [a, b)`, `p₃ ∈ (N, M]`, and
`prod ≡ 2 (mod d)`.  The `(j, [a,b)×(N,M])`-box restriction of `blockResCount`. -/
noncomputable def blockBoxResCount (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℝ)

open Classical in
/-- **`blockBoxUnitCount`** — the same box with `prod` a UNIT mod `d`; the box restriction of
`blockUnitCount` (the `apDiscBilin` coprime main-term support). -/
noncomputable def blockBoxUnitCount (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) : ℝ :=
  (((tripleSet x z y).filter
      (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod d) ∧
        N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card : ℝ)

/-- **`blockBoxHonestDisc`** — the box's honest residue-class discrepancy against the coprime main
term (`blockHonestDisc` restricted to the box); the `apDiscBilin` target after identification. -/
noncomputable def blockBoxHonestDisc (x z y : ℕ) (ε₀ : ℝ) (j N M a b d : ℕ) : ℝ :=
  blockBoxResCount x z y ε₀ j N M a b d - nuChen d * blockBoxUnitCount x z y ε₀ j N M a b d

/-- **The `(m, n)`-pair predicate** at class `P` — the image of the box triple predicate under
`(p₁,p₂,p₃) ↦ (p₁p₂, p₃)`: `m` carries `blockAlpha`-weight `1` (the oriented semiprime `∃`), `n`
is a `(N, M]`-prime, and `P(m·n)`.  The decided box makes the window + ordering redundant, so no
joint `m`-`n` constraint appears — the predicate is the honest product `blockAlpha·blockPrimeInd`
guarded by `P`. -/
def pairPred (z y : ℕ) (ε₀ : ℝ) (j N a b : ℕ) (P : ℕ → Prop) (q : ℕ × ℕ) : Prop :=
  P (q.1 * q.2) ∧ (a ≤ q.1 ∧ q.1 < b) ∧
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₁ * p₂ = q.1 ∧
      blockIdx z ε₀ p₁ = j) ∧ (N < q.2 ∧ q.2.Prime)

/-! ## Part B — unique factorization of the oriented semiprime -/

/-- **`prime_pair_unique` — the oriented `m ↦ {p₁, p₂}` bijection is honest.**  Two prime pairs
`(p₁, p₂)`, `(p₁', p₂')` split at `y` (`p_i ≤ y < p_i'`-shape) with equal products are equal.  This
is the injectivity kernel of the switch bijection: `m = p₁p₂` determines the ORIENTED factorization
uniquely (unique factorization + the `z ≤ p₁ ≤ y < p₂` orientation). -/
private lemma prime_pair_unique {y p₁ p₂ p₁' p₂' : ℕ}
    (h1 : p₁.Prime) (h1' : p₁'.Prime) (h2' : p₂'.Prime)
    (hp1 : p₁ ≤ y) (hp2' : y < p₂')
    (heq : p₁ * p₂ = p₁' * p₂') : p₁ = p₁' ∧ p₂ = p₂' := by
  have hdvd : p₁ ∣ p₁' * p₂' := heq ▸ dvd_mul_right p₁ p₂
  rcases (Nat.Prime.dvd_mul h1).mp hdvd with hd | hd
  · have heqp : p₁ = p₁' := (Nat.prime_dvd_prime_iff_eq h1 h1').mp hd
    refine ⟨heqp, ?_⟩
    rw [heqp] at heq
    exact Nat.eq_of_mul_eq_mul_left h1'.pos heq
  · have heqp : p₁ = p₂' := (Nat.prime_dvd_prime_iff_eq h1 h2').mp hd
    omega

/-! ## Part C — the pair bijection (FLOOR A) -/

open Classical in
/-- **`blockBox_pair_card` — the pair bijection (FLOOR A, FULL).**  Under the box's decided-window
corner tests (`hwin_lo`/`hwin_hi`) and the ordering-clearance corner (`hord`), the `(m, n)` pairs
selected by `pairPred` are in bijection with the block-`j` box triples, via
`(p₁,p₂,p₃) ↦ (p₁p₂, p₃)`.  Injectivity is `prime_pair_unique`; surjectivity reconstructs the
triple, deriving `p₂ ≤ p₃` from `hord` (`p₂·z ≤ p₁p₂ = m < b ≤ zN+1`) and the window from the
corners (`SwitchStrip.productInWindow_of_corners`). -/
theorem blockBox_pair_card {x z y : ℕ} {ε₀ : ℝ} {j N M a b X : ℕ}
    (P : ℕ → Prop) [DecidablePred P]
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1)
    (hwin_lo : x / 2 + 2 ≤ a * (N + 1)) (hwin_hi : (b - 1) * M ≤ x) :
    (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter (fun q => pairPred z y ε₀ j N a b P q)).card)
      = (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧ P (prod3 t) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card) := by
  classical
  symm
  apply Finset.card_bij (fun t _ => (t.1 * t.2.1, t.2.2))
  · -- membership: the image lands in the pair set
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htri, hblk, hP, hNlt, hMle, hab_lo, hab_hi⟩ := ht
    rw [tripleSet, Finset.mem_filter] at htri
    obtain ⟨_, hzp1, hp1y, hyp2, _hp2p3, hp1prime, hp2prime, hp3prime, _hwlo, _hwhi⟩ := htri
    have hm1 : 1 ≤ t.1 * t.2.1 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hp1prime.pos.ne' hp2prime.pos.ne')
    have hmX : t.1 * t.2.1 ≤ X := by omega
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hm1, hmX⟩, ⟨hp3prime.pos, hMle⟩⟩,
      hP, ⟨hab_lo, hab_hi⟩,
      ⟨t.1, t.2.1, hp1prime, hp2prime, hzp1, hp1y, hyp2, rfl, hblk⟩, ⟨hNlt, hp3prime⟩⟩
  · -- injectivity: `prime_pair_unique`
    intro t ht t' ht' heq
    rw [Finset.mem_filter] at ht ht'
    have htri := ht.1
    have htri' := ht'.1
    rw [tripleSet, Finset.mem_filter] at htri htri'
    obtain ⟨_, _, hp1y, _, _, hp1prime, _, _, _, _⟩ := htri
    obtain ⟨_, _, _, hyp2', _, hp1prime', hp2prime', _, _, _⟩ := htri'
    rw [Prod.mk.injEq] at heq
    obtain ⟨hmeq, hneq⟩ := heq
    obtain ⟨he1, he2⟩ := prime_pair_unique hp1prime hp1prime' hp2prime' hp1y hyp2' hmeq
    exact Prod.ext_iff.mpr ⟨he1, Prod.ext_iff.mpr ⟨he2, hneq⟩⟩
  · -- surjectivity: reconstruct the triple from a pair
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    obtain ⟨⟨⟨hq1lo, _hq1hi⟩, hq2lo, hq2hi⟩, hpp⟩ := hq
    obtain ⟨hP, ⟨ha_lo, ha_hi⟩, ⟨p₁, p₂, hp1prime, hp2prime, hzp1, hp1y, hyp2, hprod, hblk⟩,
      ⟨hNq2, hq2prime⟩⟩ := hpp
    -- ordering `p₂ ≤ q.2` from `hord`  (`p₂·z ≤ p₁p₂ = q.1 < b ≤ zN+1`)
    have hp2z : p₂ * z ≤ p₁ * p₂ := by
      have h : p₂ * z ≤ p₂ * p₁ := Nat.mul_le_mul_left p₂ hzp1
      rwa [mul_comm p₂ p₁] at h
    have hp2N : p₂ ≤ N := by
      have h1 : p₂ * z ≤ b - 1 := by rw [hprod] at hp2z; omega
      have h2 : z * p₂ ≤ z * N := by rw [mul_comm z p₂]; omega
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    have hord3 : p₂ ≤ q.2 := by omega
    -- the window from the corners (`SwitchStrip.productInWindow_of_corners`)
    have hwin : ProductInWindow x q.1 q.2 :=
      productInWindow_of_corners (a := a) (b := b - 1) (c := N + 1) (e := M)
        hwin_lo hwin_hi ha_lo (by omega) (by omega) hq2hi
    obtain ⟨hwlo, hwhi⟩ := hwin
    have hprod3 : prod3 (p₁, p₂, q.2) = q.1 * q.2 := by
      change p₁ * p₂ * q.2 = q.1 * q.2; rw [hprod]
    -- sizes for `Icc 1 x`
    have hq1x : q.1 ≤ x := le_trans (Nat.le_mul_of_pos_right q.1 (by omega)) hwhi
    have hq2x : q.2 ≤ x := le_trans (Nat.le_mul_of_pos_left q.2 (by omega)) hwhi
    have hp1le : p₁ ≤ q.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_right p₁ hp2prime.pos
    have hp2le : p₂ ≤ q.1 := by rw [← hprod]; exact Nat.le_mul_of_pos_left p₂ hp1prime.pos
    refine ⟨(p₁, p₂, q.2), ?_, Prod.ext_iff.mpr ⟨hprod, rfl⟩⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hblk, ?_, hNq2, hq2hi, ?_, ?_⟩
    · rw [tripleSet, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨⟨hp1prime.pos, le_trans hp1le hq1x⟩, ⟨hp2prime.pos, le_trans hp2le hq1x⟩,
          ⟨hq2prime.pos, hq2x⟩⟩,
        hzp1, hp1y, hyp2, hord3, hp1prime, hp2prime, hq2prime, ?_, ?_⟩
      · rw [hprod3]; exact hwlo
      · rw [hprod3]; exact hwhi
    · rw [hprod3]; exact hP
    · change a ≤ p₁ * p₂
      rw [hprod]; exact ha_lo
    · change p₁ * p₂ < b
      rw [hprod]; exact ha_hi

/-! ## Part D — the decided-box `apDiscBilin` identification (FLOOR B) -/

open Classical in
/-- **The pointwise indicator identity.**  The `apDiscBilin` summand
`[P(m·n)]·restrictAlpha(blockAlpha j) a b m·blockPrimeInd N n` is the `0/1` indicator of
`pairPred` — the product of `blockAlpha`'s and `blockPrimeInd`'s `0/1` weights guarded by `P`. -/
private lemma summand_eq (z y : ℕ) (ε₀ : ℝ) (j N a b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ × ℕ) :
    (if P (q.1 * q.2) then
        restrictAlpha (blockAlpha z y ε₀ j) a b q.1 * blockPrimeInd N q.2 else (0 : ℂ))
      = (if pairPred z y ε₀ j N a b P q then (1 : ℂ) else 0) := by
  classical
  unfold pairPred restrictAlpha blockAlpha blockPrimeInd
  by_cases hP : P (q.1 * q.2)
  · by_cases hbox : a ≤ q.1 ∧ q.1 < b
    · by_cases hf : (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧
          p₁ * p₂ = q.1 ∧ blockIdx z ε₀ p₁ = j)
      · by_cases hn : N < q.2 ∧ q.2.Prime
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_pos hn, if_pos ⟨hP, hbox, hf, hn⟩, mul_one]
        · rw [if_pos hP, if_pos hbox, if_pos hf, if_neg hn, mul_zero,
            if_neg (fun h => hn h.2.2.2)]
      · rw [if_pos hP, if_pos hbox, if_neg hf, zero_mul, if_neg (fun h => hf h.2.2.1)]
    · rw [if_pos hP, if_neg hbox, zero_mul, if_neg (fun h => hbox h.2.1)]
  · rw [if_neg hP, if_neg (fun h => hP h.1)]

open Classical in
/-- **The `apDiscBilin` term as a pair-set cardinality.**  Each of `apDiscBilin`'s two
`α·β`-weighted double sums (residue and unit) counts the `pairPred`-`(m,n)` pairs — the pair side
of the bijection.  `Finset.sum_product'` folds the double sum over the product, `summand_eq` turns
each summand into an indicator, `Finset.sum_boole` counts. -/
private lemma pairTerm_eq (z y : ℕ) (ε₀ : ℝ) (j N a b X M : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 M,
        if P (m * n) then
          restrictAlpha (blockAlpha z y ε₀ j) a b m * blockPrimeInd N n else (0 : ℂ))
      = (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
            (fun q => pairPred z y ε₀ j N a b P q)).card : ℂ) := by
  classical
  rw [← Finset.sum_product']
  rw [Finset.sum_congr rfl (fun q _ => summand_eq z y ε₀ j N a b P q)]
  rw [Finset.sum_boole]

open Classical in
/-- **`blockBox_apDiscBilin_eq` — the decided-box identification (FLOOR B, FULL).**  On a box that
is corner-decided-in-window (`hwin_lo`/`hwin_hi`, via `SwitchStrip.productInWindow_of_corners`) and
ordering-cleared (`hord`), the block's honest box discrepancy IS an `apDiscBilin` at the decided
coefficient `restrictAlpha (blockAlpha j) a b`.  The main-term convention reconciles on the nose:
`apDiscBilin`'s `(1/φd)·(unit pair count)` is exactly `nuChen d · blockBoxUnitCount`
(`nuChen_eq_inv_totient`: `nuChen d = 1/(d.totient : ℝ)`).  Assembles `pairTerm_eq` +
`blockBox_pair_card` for both the residue and the unit class. -/
theorem blockBox_apDiscBilin_eq {x z y : ℕ} {ε₀ : ℝ} {j N M a b X d : ℕ}
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1)
    (hwin_lo : x / 2 + 2 ≤ a * (N + 1)) (hwin_hi : (b - 1) * M ≤ x) :
    apDiscBilin (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d
      = ((blockBoxResCount x z y ε₀ j N M a b d : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) * ((blockBoxUnitCount x z y ε₀ j N M a b d : ℝ) : ℂ) := by
  classical
  -- the pair↔triple card bridges, stated with the REDUCED class predicate (matching
  -- `blockBoxResCount`/`blockBoxUnitCount`); proven by `blockBox_pair_card` up to beta-defeq
  have hR : (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
        (fun q => pairPred z y ε₀ j N a b (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
          q)).card)
      = (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
          ((prod3 t : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card) :=
    blockBox_pair_card (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d))
      hz hbX hord hwin_lo hwin_hi
  have hU : (((Finset.Icc 1 X ×ˢ Finset.Icc 1 M).filter
        (fun q => pairPred z y ε₀ j N a b (fun v => IsUnit ((v : ℕ) : ZMod d)) q)).card)
      = (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
          IsUnit ((prod3 t : ℕ) : ZMod d) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ a ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < b)).card) :=
    blockBox_pair_card (fun v => IsUnit ((v : ℕ) : ZMod d)) hz hbX hord hwin_lo hwin_hi
  unfold apDiscBilin
  rw [pairTerm_eq z y ε₀ j N a b X M (fun v => ((v : ℕ) : ZMod d) = ((2 : ℕ) : ZMod d)),
    pairTerm_eq z y ε₀ j N a b X M (fun v => IsUnit ((v : ℕ) : ZMod d)), hR, hU,
    blockBoxResCount, blockBoxUnitCount]
  push_cast
  ring

open Classical in
/-- **`norm_blockBox_apDiscBilin_eq` — the norm form (the `hHD`-shaped bound's per-box atom).**  The
`‖apDiscBilin‖` on a decided box EQUALS the box's honest discrepancy `|blockBoxHonestDisc|` — the
exact object the `hHD` sum accumulates.  Immediate from `blockBox_apDiscBilin_eq` (`apDiscBilin` is
a real number at these `0/1` coefficients) via `Complex.norm_ofReal`. -/
theorem norm_blockBox_apDiscBilin_eq {x z y : ℕ} {ε₀ : ℝ} {j N M a b X d : ℕ}
    (hz : 1 ≤ z) (hbX : b ≤ X + 1) (hord : b ≤ z * N + 1)
    (hwin_lo : x / 2 + 2 ≤ a * (N + 1)) (hwin_hi : (b - 1) * M ≤ x) :
    ‖apDiscBilin (restrictAlpha (blockAlpha z y ε₀ j) a b) (blockPrimeInd N) X M 2 d‖
      = |blockBoxHonestDisc x z y ε₀ j N M a b d| := by
  rw [blockBox_apDiscBilin_eq hz hbX hord hwin_lo hwin_hi, blockBoxHonestDisc, nuChen_apply]
  rw [show ((blockBoxResCount x z y ε₀ j N M a b d : ℝ) : ℂ)
        - (1 / (d.totient : ℂ)) * ((blockBoxUnitCount x z y ε₀ j N M a b d : ℝ) : ℂ)
      = ((blockBoxResCount x z y ε₀ j N M a b d
          - 1 / (d.totient : ℝ) * blockBoxUnitCount x z y ε₀ j N M a b d : ℝ) : ℂ) by
        push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

end Salt.Chen
