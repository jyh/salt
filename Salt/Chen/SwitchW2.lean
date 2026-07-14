/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchW

/-!
# A3W2 — the W box/band close: the `hBVblocksW` supplier (H-AMENDMENT 2, the A3W leftover)

Design: `docs/blueprints/chen.md`, "H-AMENDMENT 2" (D3) + "GATE RESULT" (C4);
`docs/blueprints/flags.md`, the WAVE-2 A3W bullet ("REMAINING CONSTRUCTION … = node A3W2").
A3W landed `mainA3_of_block_remainders_W` with the single slot `hBVblocksW` and the L¹ bridge
`hBVblocksW_of_generalBV` reducing it to priced sums of `blockHonestDiscW` — the honest per-`d`
discrepancy at the Q-SHIFTED modulus `Q·d` and CRT class `crtClassW Q d a`.  This file constructs
the W-mirrors of the landed box/band DECOMPOSITION and PRICING suppliers that feed that bridge —
the analogue of the landed chain `PieceDecomp` → `hBlock_of_window_prices` →
(box: `hNum_at_op_sqrtD`; band: `Plo_discharge` + the `BandIdent` identifications) at the shifted
class:

* **Part A — the W box objects**: `blockBoxResCountW`/`blockBoxUnitCountW` (free modulus `m`,
  free class `c` — the box restriction of `SwitchW.blockResCountM`/`blockUnitCountM`) and
  `blockBoxHonestDiscW` (at `m = Q·d`, `c = crtClassW Q d a`); the W-band disc family
  `bandSymRectDiscW`/`bandLowDiscW`/`bandDiagDiscW` (the landed `BandClose` count objects —
  which are CLASS-GENERIC — instantiated at the shifted class; the landed discs hard-code
  residue `2`, per the gate's ratified narrowing the literal lives only in disc DEFS, so the
  W-route defines its own).
* **Part B/C — the piece decomposition (WBV6's pattern)**: `blockHonestDiscW_eq_sum_pieces` —
  the per-`j` W-block honest disc is the sum over the `O(log x)` dyadic `p₃`-pieces of W-box
  discs (full `m`-range `(0, x+1)`) — plus the `m`-range splitters
  `blockBox*CountW_split_m`/`blockBoxHonestDiscW_split_m`.
* **Part D — the per-block assembly**: `hBlockW_of_window_prices`, the verbatim W-mirror of
  `PieceDecomp.hBlock_of_window_prices` (ordering-clear sub-box `[0, min(z·N+1, x+1))` priced
  by `Phi`, band sub-box `[min(z·N+1, x+1), x+1)` priced by `Plo`).
* **Part E — the box pricing**: `blockBoxW_windowDisc_eq` (the R₀-free core
  `WindowSW.blockBox_windowDisc_eq_res` at `d := Q·d'`, `R₀ := crtClassW Q d' a`, folded into
  the W count objects), `hHD_of_box_discW` (the T-difference feeder), and `hNum_at_opW` — the
  W-mirror of `SqrtDFold.hNum_at_op_sqrtD`: the three-way survivor split
  (`MediumFloor.box_disc_three_way`, r(d)-generalized per C4) at
  `Dset := ((divisors Ps).filter (·<bound)).image (Q * ·)` and
  `r := fun m => crtClassW Q (m/Q) a`, with the same `z·y` support floor
  (`medium_support_floor_high` — the W-shift touches only modulus/class, never the `m`-side).
* **Part F — the band close (the three-piece `Plo_discharge` pattern)**:
  `bandDiscW_eq_three`/`bandDiscW_le_three_pieces` (½·sym + ½·diag + low, on the class-generic
  `bandCard_split`/`symCard_two_mul`), `abs_diagDiscW_le_bandDiagCount` (the diagonal is a
  counting bound — the Q-restriction only SHRINKS the diagonal count, so the landed
  `bandDiagCount_le` applies verbatim), and `PloW_discharge`.
* **Part G — the band identifications + feeders**: `norm_symRectW_eq`/`norm_lowRectW_eq` (the
  R₀-generalized cores `BandIdent.symRect_eq_apDiscBilinCutoff`/`lowRect_eq_apDiscBilinCutoff`
  at the shifted pair, norm form) and `PloW_sym_of_box_disc`/`PloW_low_of_box_disc` (the
  T-difference feeders at the image family, mirroring `MediumFloor.Plo_sym_of_box_disc`/
  `Plo_low_of_box_disc`).
* **Part H — the composed supplier**: `hBVblocksW_discharge` — the `hBVblocksW` slot of
  `mainA3_of_block_remainders_W` discharged modulo NAMED numeric/threshold rows only, plus the
  structural `Dset` rows for the shifted family (`hrW_discharge` — the `hr` row, DISCHARGED;
  `hDge1W`, `hDlevW`) and the composition `example` landing character-for-character in the
  `hBVblocksW` slot (emitting the `hA3` shape at the W-carrier).

## GLU-2W named-row ledger (CONSOLIDATED: A3W's rows + this node's)

The A3W rows (recorded in `SwitchW.lean` Part D, restated for the single consolidated list):

1. **level** (`hDscale`-form): the shifted moduli run to `D = Q·(QR·Dlev)`; the terminal's
   `D ≤ √(XM)/L^B` row absorbs ONE extra factor `Q ≤ 4^{w₀} ≤ L` (C2's tower
   `x₀ ≥ exp(exp(2·w0N ε))`).  Structural shape supplied here: `hDlevW`.
2. **divisor** (`herr_div`-form): `τ(Q·d) ≤ τ(Q)·τ(d) ≤ Q·τ(d) ≤ L·τ(d)` — one extra `L`
   against the `x^{1/9}`+ room of `hdiv_direct`'s floor (`hfloor` at `F = z·y`).
3. **BV crumb** (`hNum`-form): the `x/L^10` budget vs the W main scale
   `X_W/φ(Q) ≥ 32e^{−70}·x/L³` (C7) — `L⁷/e^{70}` room.
4. **`hr`**: DISCHARGED — `hrW_discharge` (via `crtClassW_coprime` + `switch_dvd_coprime_two`;
   `hQa2` free at `a = Q−1` via `residue_witness`).  `1 ≤ d`: DISCHARGED (`hDge1W`).
5. **`hQPs`**: `gcd(Q, Ps) = 1` — free at instantiation (`Q`'s primes `< w₀ ≤` `Ps`'s).

This node's rows (the NAMED slots of `hBVblocksW_discharge`):

6. **`Price j k i`** (high boxes): per boundary survivor `i` of the `(j, k)` box, TWO
   `medium_survivor_price_sqrtD` applications (`T = x` and `T = x/2+1`, same price) at
   `X := 2^{i+1} − 1`, `Dset :=` the Q-shifted image family, `r := fun m => crtClassW Q (m/Q) a`
   (`hr`/`1 ≤ d` from rows 4; level from row 1 at the shifted `D`).  The terminal's threshold
   list re-runs at the shifted level: `hDsq : D < (N+1)²`, `habs : 4(1+log D)·D ≤ N·M/L^A`,
   and the D0-window family via `d0_window_nonempty` (A = 13, C0 = 18).  **Floor caveat**
   (flags finding 3, pending amendment): `d0_window_nonempty`'s floor hypothesis is
   `N ≥ x^{11/24}/8`; any W-box needing the LOWER floor `√(x/(24z))` takes that floor as a
   NAMED hypothesis at GLU-2W (do NOT edit `GlueFinal`) — the same construction covers it with
   room ≈ 83×.
7. **`PsymK`/`PlowK` `j k`** (band boxes): the per-`(j, k)` T-difference prices at the band
   carriers — `box_disc_three_way` (hsupp := `medium_support_floor_sym`/`_low`, the same `z·y`
   floor) + the same terminal at the shifted family.  The sym carrier's `hDsq` discharges from
   the single row `D < (y+1)²` via `hDsq_at_sym_carrier` exactly as landed.
8. **the diagonal row**: explicit — `(1/2)·τ(Ps)·Σ_k y·(pieceM k − pieceN k)`; a counting
   bound (`bandDiagCount_le`), Q-free.
9. **`hCE_W`**: the W conversion-error crumb (`blockConvErrW` double sum — finding 5's
   mechanism at kept points; the crude count only shrinks under the AP filter).
10. **`hSum`/`hNum`**: the `A ≥ 13`-family budget rows at the C7 crude main scale (row 3).

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

open Finset ArithmeticFunction

namespace Salt.Chen

/-! ## Part A — the W box count objects (free modulus `m`, free class `c`) -/

open Classical in
/-- **`blockBoxResCountW`** — the block-`j` box triples (`N < p₃ ≤ M`, `lo ≤ p₁p₂ < hi`) with
`prod3 ≡ c (mod m)`, at a FREE modulus `m` and class `c` — the box restriction of
`SwitchW.blockResCountM` (and the free-class generalization of `PairBijection.blockBoxResCount`,
which pins `m = d`, `c = 2`).  The W-route consumes it at `m = Q·d`, `c = crtClassW Q d a`. -/
noncomputable def blockBoxResCountW (x z y : ℕ) (ε₀ : ℝ) (j N M lo hi m c : ℕ) : ℝ :=
  (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
      ((prod3 t : ℕ) : ZMod m) = ((c : ℕ) : ZMod m) ∧
      N < t.2.2 ∧ t.2.2 ≤ M ∧ lo ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < hi)).card : ℝ)

open Classical in
/-- **`blockBoxUnitCountW`** — the block-`j` box triples with `prod3` a UNIT mod `m` (free
modulus); the box restriction of `SwitchW.blockUnitCountM`. -/
noncomputable def blockBoxUnitCountW (x z y : ℕ) (ε₀ : ℝ) (j N M lo hi m : ℕ) : ℝ :=
  (((tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
      IsUnit ((prod3 t : ℕ) : ZMod m) ∧
      N < t.2.2 ∧ t.2.2 ≤ M ∧ lo ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < hi)).card : ℝ)

/-- **The W honest BOX discrepancy at the Q-shifted pair** — `blockBoxHonestDisc`'s mirror at
modulus `Q·d`, class `crtClassW Q d a`; the object the C4-generalized windowed chain prices
per `(j, piece, sub-box)`.  Sums (over the pieces) to `SwitchW.blockHonestDiscW` (Part B). -/
noncomputable def blockBoxHonestDiscW (x z y : ℕ) (ε₀ : ℝ) (j Q a N M lo hi d : ℕ) : ℝ :=
  blockBoxResCountW x z y ε₀ j N M lo hi (Q * d) (crtClassW Q d a)
    - nuChen (Q * d) * blockBoxUnitCountW x z y ε₀ j N M lo hi (Q * d)

/-! ## Part B — the piece decomposition (WBV6's pattern at the shifted class)

`PieceDecomp.count_eq_sum_piece` is `private` there; re-proved here (the same fibering over
`k = ⌊log₂ p₃⌋`). -/

open Classical in
/-- Re-proof of `PieceDecomp.count_eq_sum_piece` (private there): any predicate-filtered count
of `tripleSet` partitions exactly over the `Nat.log 2 x + 1` dyadic `p₃`-pieces. -/
private lemma count_eq_sum_pieceW {x z y : ℕ} (P : ℕ × ℕ × ℕ → Prop) [DecidablePred P] :
    (((tripleSet x z y).filter P).card : ℝ)
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          (((tripleSet x z y).filter (fun t => Nat.log 2 t.2.2 = k ∧ P t)).card : ℝ) := by
  classical
  have hmaps : ∀ t ∈ (tripleSet x z y).filter P,
      Nat.log 2 t.2.2 ∈ Finset.range (Nat.log 2 x + 1) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have htri := ht.1
    rw [tripleSet, Finset.mem_filter] at htri
    obtain ⟨_, _, _, _, _, hp1, hp2, _hp3, _hlo, hhi⟩ := htri
    have hmpos : 0 < t.1 * t.2.1 := Nat.mul_pos hp1.pos hp2.pos
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    have hple : t.2.2 ≤ x := by
      calc t.2.2 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_left _ hmpos
        _ = prod3 t := hprod.symm
        _ ≤ x := hhi
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hple)
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hfilt : ((tripleSet x z y).filter P).filter (fun t => Nat.log 2 t.2.2 = k)
      = (tripleSet x z y).filter (fun t => Nat.log 2 t.2.2 = k ∧ P t) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro t _; exact and_comm
  rw [hfilt]

/-- **The free-class block residue count partitions over the `p₃`-pieces.**  The W-mirror of
`PieceDecomp.blockResCount_eq_sum_pieces` at a free modulus/class pair `(m, c)`. -/
theorem blockResCountM_eq_sum_pieces (x z y : ℕ) (ε₀ : ℝ) (j m c : ℕ) :
    blockResCountM x z y ε₀ j m c
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          blockBoxResCountW x z y ε₀ j (pieceN k) (pieceM k) 0 (x + 1) m c := by
  classical
  unfold blockResCountM
  rw [count_eq_sum_pieceW
        (fun t => blockIdx z ε₀ t.1 = j ∧ ((prod3 t : ℕ) : ZMod m) = ((c : ℕ) : ZMod m))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold blockBoxResCountW
  rw [Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _hp1, _hp2, hp3, _, hwhi⟩ := ht
  have hp3pos : 1 ≤ t.2.2 := hp3.pos
  have hmle : t.1 * t.2.1 ≤ x := by
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    calc t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hp3.pos
      _ = prod3 t := hprod.symm
      _ ≤ x := hwhi
  rw [log_eq_iff_piece hp3pos]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hblk, hres⟩
    exact ⟨hblk, hres, hlo, hhi, Nat.zero_le _, by omega⟩
  · rintro ⟨hblk, hres, hlo, hhi, _, _⟩
    exact ⟨⟨hlo, hhi⟩, hblk, hres⟩

/-- **The free-modulus block unit count partitions over the `p₃`-pieces.** -/
theorem blockUnitCountM_eq_sum_pieces (x z y : ℕ) (ε₀ : ℝ) (j m : ℕ) :
    blockUnitCountM x z y ε₀ j m
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          blockBoxUnitCountW x z y ε₀ j (pieceN k) (pieceM k) 0 (x + 1) m := by
  classical
  unfold blockUnitCountM
  rw [count_eq_sum_pieceW (fun t => blockIdx z ε₀ t.1 = j ∧ IsUnit ((prod3 t : ℕ) : ZMod m))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold blockBoxUnitCountW
  rw [Nat.cast_inj]
  refine congrArg Finset.card (Finset.filter_congr (fun t ht => ?_))
  rw [tripleSet, Finset.mem_filter] at ht
  obtain ⟨_, _, _, _, _, _hp1, _hp2, hp3, _, hwhi⟩ := ht
  have hp3pos : 1 ≤ t.2.2 := hp3.pos
  have hmle : t.1 * t.2.1 ≤ x := by
    have hprod : prod3 t = t.1 * t.2.1 * t.2.2 := rfl
    calc t.1 * t.2.1 ≤ t.1 * t.2.1 * t.2.2 := Nat.le_mul_of_pos_right _ hp3.pos
      _ = prod3 t := hprod.symm
      _ ≤ x := hwhi
  rw [log_eq_iff_piece hp3pos]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hblk, hres⟩
    exact ⟨hblk, hres, hlo, hhi, Nat.zero_le _, by omega⟩
  · rintro ⟨hblk, hres, hlo, hhi, _, _⟩
    exact ⟨⟨hlo, hhi⟩, hblk, hres⟩

/-- **`blockHonestDiscW_eq_sum_pieces` (the piece decomposition, EXACT).**  The per-`j` W-block
honest discrepancy is the sum over the `O(log x)` dyadic `p₃`-pieces of the W-box honest
discrepancies (full `m`-range `(0, x+1)`).  WBV6's `blockHonestDisc_eq_sum_pieces` at the
shifted pair `(Q·d, crtClassW Q d a)`. -/
theorem blockHonestDiscW_eq_sum_pieces (x z y : ℕ) (ε₀ : ℝ) (j Q a d : ℕ) :
    blockHonestDiscW x z y ε₀ j Q a d
      = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) 0 (x + 1) d := by
  unfold blockHonestDiscW blockBoxHonestDiscW
  rw [blockResCountM_eq_sum_pieces, blockUnitCountM_eq_sum_pieces, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

/-- **The triangle over the pieces.** -/
theorem abs_blockHonestDiscW_le_sum_pieces (x z y : ℕ) (ε₀ : ℝ) (j Q a d : ℕ) :
    |blockHonestDiscW x z y ε₀ j Q a d|
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) 0 (x + 1) d| := by
  rw [blockHonestDiscW_eq_sum_pieces]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## Part C — the `m`-range split of the W box counts -/

/-- **The `m`-range split of the W box residue count.**  For `lo ≤ mid ≤ hi`, the box `[lo, hi)`
partitions into `[lo, mid) ⊔ [mid, hi)` on the `m = p₁p₂` axis.  The free-class mirror of
`PieceDecomp.blockBoxResCount_split_m`. -/
theorem blockBoxResCountW_split_m (x z y : ℕ) (ε₀ : ℝ) (j N M lo mid hi m c : ℕ)
    (hac : lo ≤ mid) (hcb : mid ≤ hi) :
    blockBoxResCountW x z y ε₀ j N M lo hi m c
      = blockBoxResCountW x z y ε₀ j N M lo mid m c
        + blockBoxResCountW x z y ε₀ j N M mid hi m c := by
  classical
  unfold blockBoxResCountW
  rw [← Nat.cast_add, Nat.cast_inj,
    ← Finset.card_filter_add_card_filter_not
        (s := (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
          ((prod3 t : ℕ) : ZMod m) = ((c : ℕ) : ZMod m) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ lo ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < hi))
        (p := fun t => t.1 * t.2.1 < mid)]
  congr 1
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro t _
    constructor
    · rintro ⟨⟨hblk, hres, hN, hM, ham, _hmb⟩, hmc⟩
      exact ⟨hblk, hres, hN, hM, ham, hmc⟩
    · rintro ⟨hblk, hres, hN, hM, ham, hmc⟩
      exact ⟨⟨hblk, hres, hN, hM, ham, by omega⟩, hmc⟩
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro t _
    constructor
    · rintro ⟨⟨hblk, hres, hN, hM, _ham, hmb⟩, hmc⟩
      exact ⟨hblk, hres, hN, hM, by omega, hmb⟩
    · rintro ⟨hblk, hres, hN, hM, hcm, hmb⟩
      exact ⟨⟨hblk, hres, hN, hM, by omega, hmb⟩, by omega⟩

/-- **The `m`-range split of the W box unit count.** -/
theorem blockBoxUnitCountW_split_m (x z y : ℕ) (ε₀ : ℝ) (j N M lo mid hi m : ℕ)
    (hac : lo ≤ mid) (hcb : mid ≤ hi) :
    blockBoxUnitCountW x z y ε₀ j N M lo hi m
      = blockBoxUnitCountW x z y ε₀ j N M lo mid m
        + blockBoxUnitCountW x z y ε₀ j N M mid hi m := by
  classical
  unfold blockBoxUnitCountW
  rw [← Nat.cast_add, Nat.cast_inj,
    ← Finset.card_filter_add_card_filter_not
        (s := (tripleSet x z y).filter (fun t => blockIdx z ε₀ t.1 = j ∧
          IsUnit ((prod3 t : ℕ) : ZMod m) ∧
          N < t.2.2 ∧ t.2.2 ≤ M ∧ lo ≤ t.1 * t.2.1 ∧ t.1 * t.2.1 < hi))
        (p := fun t => t.1 * t.2.1 < mid)]
  congr 1
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro t _
    constructor
    · rintro ⟨⟨hblk, hu, hN, hM, ham, _hmb⟩, hmc⟩
      exact ⟨hblk, hu, hN, hM, ham, hmc⟩
    · rintro ⟨hblk, hu, hN, hM, ham, hmc⟩
      exact ⟨⟨hblk, hu, hN, hM, ham, by omega⟩, hmc⟩
  · rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro t _
    constructor
    · rintro ⟨⟨hblk, hu, hN, hM, _ham, hmb⟩, hmc⟩
      exact ⟨hblk, hu, hN, hM, by omega, hmb⟩
    · rintro ⟨hblk, hu, hN, hM, hcm, hmb⟩
      exact ⟨⟨hblk, hu, hN, hM, by omega, hmb⟩, by omega⟩

/-- **The `m`-range split of the W box honest discrepancy** — the splitter for Part D
(ordering-clear `[0, min(z·N+1, x+1))` + band `[min(z·N+1, x+1), x+1)`). -/
theorem blockBoxHonestDiscW_split_m (x z y : ℕ) (ε₀ : ℝ) (j Q a N M lo mid hi d : ℕ)
    (hac : lo ≤ mid) (hcb : mid ≤ hi) :
    blockBoxHonestDiscW x z y ε₀ j Q a N M lo hi d
      = blockBoxHonestDiscW x z y ε₀ j Q a N M lo mid d
        + blockBoxHonestDiscW x z y ε₀ j Q a N M mid hi d := by
  unfold blockBoxHonestDiscW
  rw [blockBoxResCountW_split_m x z y ε₀ j N M lo mid hi (Q * d) (crtClassW Q d a) hac hcb,
    blockBoxUnitCountW_split_m x z y ε₀ j N M lo mid hi (Q * d) hac hcb]
  ring

/-! ## Part D — the per-block assembly: `hBlockW_of_window_prices` -/

open Classical in
/-- **`hBlockW_of_window_prices`** — the W-mirror of `PieceDecomp.hBlock_of_window_prices`: the
per-block W honest-discrepancy `L¹`-over-`d` sum is bounded by the high-piece prices `Phi` plus
the named band budget `Plo`.  Each piece box `(0, x+1)` splits at
`c k = min (z·pieceN k + 1) (x+1)` into the ordering-clear sub-box (priced by `hNum_at_opW`,
Part E) and the band sub-box (priced by `PloW_discharge`, Part F).  The output is the exact
per-block shape `hBVblocksW_of_generalBV`'s `hHD` consumes blockwise. -/
theorem hBlockW_of_window_prices (x z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (bound : ℝ) (j : ℕ)
    (Phi : ℕ → ℝ) (Plo : ℝ)
    (hHigh : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) 0
                 (min (z * pieceN k + 1) (x + 1)) d| else 0) ≤ Phi k)
    (hLow : (∑ k ∈ Finset.range (Nat.log 2 x + 1),
              ∑ d ∈ Nat.divisors Ps,
                if (d : ℝ) < bound then
                  |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
                     (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0) ≤ Plo) :
    (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |blockHonestDiscW x z y ε₀ j Q a d| else 0)
      ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1), Phi k) + Plo := by
  classical
  set c : ℕ → ℕ := fun k => min (z * pieceN k + 1) (x + 1) with hc
  have hterm : ∀ d : ℕ,
      (if (d : ℝ) < bound then |blockHonestDiscW x z y ε₀ j Q a d| else 0)
        ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ((if (d : ℝ) < bound then
                |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) 0 (c k) d| else 0)
              + (if (d : ℝ) < bound then
                |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) (c k) (x + 1) d|
                  else 0)) := by
    intro d
    by_cases hd : (d : ℝ) < bound
    · rw [if_pos hd]
      refine le_trans (abs_blockHonestDiscW_le_sum_pieces x z y ε₀ j Q a d) ?_
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [if_pos hd, if_pos hd]
      have hsplit := blockBoxHonestDiscW_split_m x z y ε₀ j Q a (pieceN k) (pieceM k) 0 (c k)
        (x + 1) d (Nat.zero_le _) (min_le_right _ _)
      rw [hsplit]
      exact abs_add_le _ _
    · rw [if_neg hd]
      refine Finset.sum_nonneg (fun k _ => ?_)
      simp only [if_neg hd]; positivity
  calc (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < bound then |blockHonestDiscW x z y ε₀ j Q a d| else 0)
      ≤ ∑ d ∈ Nat.divisors Ps, ∑ k ∈ Finset.range (Nat.log 2 x + 1),
          ((if (d : ℝ) < bound then
              |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) 0 (c k) d| else 0)
            + (if (d : ℝ) < bound then
              |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) (c k) (x + 1) d|
                else 0)) :=
        Finset.sum_le_sum (fun d _ => hterm d)
    _ = ∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
          ((if (d : ℝ) < bound then
              |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) 0 (c k) d| else 0)
            + (if (d : ℝ) < bound then
              |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) (c k) (x + 1) d|
                else 0)) :=
        Finset.sum_comm
    _ = (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) 0 (c k) d| else 0)
          + (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) (c k) (x + 1) d|
                else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
    _ ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1), Phi k) + Plo :=
        add_le_add (Finset.sum_le_sum (fun k hk => hHigh k hk)) hLow

/-! ## Part E — the box identification + the three-way-split pricing (`hNum_at_opW`) -/

open Classical in
/-- **`blockBoxW_windowDisc_eq` — the W box identification.**  The R₀-free core
`WindowSW.blockBox_windowDisc_eq_res` at `d := Q·d`, `R₀ := crtClassW Q d a`, folded into the W
count objects: on an ordering-cleared box the difference of the two one-sided cutoff carriers
at the SHIFTED pair equals `blockBoxResCountW − (1/φ(Q·d))·blockBoxUnitCountW`. -/
theorem blockBoxW_windowDisc_eq {x z y : ℕ} {ε₀ : ℝ} {j N M lo hi X Q d a : ℕ}
    (hz : 1 ≤ z) (hbX : hi ≤ X + 1) (hord : hi ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x) :
    apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi) (blockPrimeInd N) X M
        (crtClassW Q d a) (Q * d) x
      - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi) (blockPrimeInd N) X M
          (crtClassW Q d a) (Q * d) (x / 2 + 1)
      = ((blockBoxResCountW x z y ε₀ j N M lo hi (Q * d) (crtClassW Q d a) : ℝ) : ℂ)
        - (1 / ((Q * d).totient : ℂ))
          * ((blockBoxUnitCountW x z y ε₀ j N M lo hi (Q * d) : ℝ) : ℂ) := by
  rw [blockBox_windowDisc_eq_res hz hbX hord hxlo, blockBoxResCountW, blockBoxUnitCountW]
  push_cast
  ring

/-- **`hHD_of_box_discW`** — the W box honest discrepancy priced at the T-DIFFERENCE (the
mirror of `MediumFloor.hHD_of_box_disc`).  Per `d`, `|blockBoxHonestDiscW| = ‖carrier(x) −
carrier(x/2+1)‖` at the shifted pair (the identification above); the difference sum is exactly
what `box_disc_three_way` emits at the shifted `Dset`. -/
theorem hHD_of_box_discW {x z y : ℕ} {ε₀ : ℝ} {j N M lo hi X Q a : ℕ} (Dset : Finset ℕ)
    {P : ℝ}
    (hz : 1 ≤ z) (hbX : hi ≤ X + 1) (hord : hi ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x)
    (hdiff : ∑ d ∈ Dset,
        ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
            (blockPrimeInd N) X M (crtClassW Q d a) (Q * d) x
          - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
            (blockPrimeInd N) X M (crtClassW Q d a) (Q * d) (x / 2 + 1)‖ ≤ P) :
    ∑ d ∈ Dset, |blockBoxHonestDiscW x z y ε₀ j Q a N M lo hi d| ≤ P := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun d _ => ?_))) hdiff
  have hid : ((blockBoxHonestDiscW x z y ε₀ j Q a N M lo hi d : ℝ) : ℂ)
      = apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
          (blockPrimeInd N) X M (crtClassW Q d a) (Q * d) x
        - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
          (blockPrimeInd N) X M (crtClassW Q d a) (Q * d) (x / 2 + 1) := by
    rw [blockBoxW_windowDisc_eq (X := X) hz hbX hord hxlo, blockBoxHonestDiscW,
      nuChen_apply]
    push_cast
    ring
  rw [← hid, Complex.norm_real, Real.norm_eq_abs]

open Classical in
/-- **`hNum_at_opW`** — the W-mirror of `SqrtDFold.hNum_at_op_sqrtD`: the completed three-way
survivor split at the `z·y` floor for an ordering-clear W box, at the Q-SHIFTED family.  The
box's `d`-guarded W honest-discrepancy sum — the EXACT `hHigh` summand of
`hBlockW_of_window_prices` (`Phi k := Σ_{i ∈ boundary} Price i`, a `≤ 3`-term sum by
`dyadicBoundary_card_le_three`) — is bounded by the boundary-survivor prices.  Composes
`hHD_of_box_discW` with the r(d)-generalized `box_disc_three_way` at
`Dset := ((divisors Ps).filter (·<bound)).image (Q * ·)`, `r := fun m => crtClassW Q (m/Q) a`
(the support floor is the landed `medium_support_floor_high` — the W-shift never touches the
`m`-side).  The `hprice` slot is exactly TWO `medium_survivor_price_sqrtD` applications per
boundary survivor (`T = x` and `T = x/2+1`, same price) at `X := 2^{i+1} − 1` — GLU-2W row 6. -/
theorem hNum_at_opW {x z y : ℕ} {ε₀ : ℝ} {j N M lo hi X : ℕ} (K Q a Ps : ℕ) (bound : ℝ)
    (Price : ℕ → ℝ)
    (hQ1 : 1 ≤ Q)
    (hz : 1 ≤ z) (hbX : hi ≤ X + 1) (hord : hi ≤ z * N + 1) (hxlo : x / 2 + 1 ≤ x)
    (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K, 2 ^ (i + 1) ≤ X + 1)
    (hprice : ∀ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K,
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
                (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd N) (2 ^ (i + 1) - 1) M
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
                  (2 ^ i) (2 ^ (i + 1))) (blockPrimeInd N) (2 ^ (i + 1) - 1) M
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price i) :
    (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |blockBoxHonestDiscW x z y ε₀ j Q a N M lo hi d| else 0)
      ≤ ∑ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K, Price i := by
  classical
  have hQ0 : 0 < Q := hQ1
  rw [← Finset.sum_filter]
  refine hHD_of_box_discW _ hz hbX hord hxlo ?_
  have h3 := box_disc_three_way (α := restrictAlpha (blockAlpha z y ε₀ j) lo hi) K hK hxlo
    (fun m hm => medium_support_floor_high hm)
    (((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d))
    (fun m => crtClassW Q (m / Q) a) Price hiX hprice
  rw [Finset.sum_image (fun d₁ _ d₂ _ h => Nat.eq_of_mul_eq_mul_left hQ0 h)] at h3
  calc (∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
        ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
            (blockPrimeInd N) X M (crtClassW Q d a) (Q * d) x
          - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
            (blockPrimeInd N) X M (crtClassW Q d a) (Q * d) (x / 2 + 1)‖)
      = ∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
        ‖apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
            (blockPrimeInd N) X M (crtClassW Q (Q * d / Q) a) (Q * d) x
          - apDiscBilinCutoff (restrictAlpha (blockAlpha z y ε₀ j) lo hi)
            (blockPrimeInd N) X M (crtClassW Q (Q * d / Q) a) (Q * d) (x / 2 + 1)‖ := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Nat.mul_div_cancel_left d hQ0]
    _ ≤ ∑ i ∈ dyadicBoundary N M (x / 2 + 1) x (z * y) K, Price i := h3

/-! ## Part F — the band close: the three-piece `Plo_discharge` pattern at the W objects -/

open Classical in
/-- **The W symmetric UNORDERED rectangle honest discrepancy** at the shifted pair —
`bandSymRectDisc`'s mirror (the landed def pins residue `2`; the class-generic
`symRectCount` carries the shifted class). -/
noncomputable def bandSymRectDiscW (x z y : ℕ) (ε₀ : ℝ) (j Q a N M d : ℕ) : ℝ :=
  symRectCount x z y ε₀ j N M
      (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
    - nuChen (Q * d)
      * symRectCount x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))

open Classical in
/-- **The W `α_low` rectangle honest discrepancy** (`p₂ ≤ N < p₃`) at the shifted pair. -/
noncomputable def bandLowDiscW (x z y : ℕ) (ε₀ : ℝ) (j Q a N M lo hi d : ℕ) : ℝ :=
  lowCard x z y ε₀ j N M lo hi
      (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
    - nuChen (Q * d)
      * lowCard x z y ε₀ j N M lo hi (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))

open Classical in
/-- **The W diagonal honest discrepancy** (`p₂ = p₃`) at the shifted pair — crude. -/
noncomputable def bandDiagDiscW (x z y : ℕ) (ε₀ : ℝ) (j Q a N M d : ℕ) : ℝ :=
  diagSum x z y ε₀ j N M
      (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
    - nuChen (Q * d) * diagSum x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))

/-- `blockBoxResCountW` is `bandCard` at the shifted residue class. -/
lemma bandCard_eq_blockBoxResCountW (x z y : ℕ) (ε₀ : ℝ) (j N M lo hi m c : ℕ) :
    blockBoxResCountW x z y ε₀ j N M lo hi m c
      = bandCard x z y ε₀ j N M lo hi
          (fun v => ((v : ℕ) : ZMod m) = ((c : ℕ) : ZMod m)) := by
  unfold blockBoxResCountW bandCard
  rw [Nat.cast_inj]
  apply congrArg Finset.card
  ext t
  simp only [Finset.mem_filter]

/-- `blockBoxUnitCountW` is `bandCard` at the unit class. -/
lemma bandCard_eq_blockBoxUnitCountW (x z y : ℕ) (ε₀ : ℝ) (j N M lo hi m : ℕ) :
    blockBoxUnitCountW x z y ε₀ j N M lo hi m
      = bandCard x z y ε₀ j N M lo hi (fun v => IsUnit ((v : ℕ) : ZMod m)) := by
  unfold blockBoxUnitCountW bandCard
  rw [Nat.cast_inj]
  apply congrArg Finset.card
  ext t
  simp only [Finset.mem_filter]

/-- **The W band honest disc decomposes into three pieces.**  The mirror of
`BandClose.bandDisc_eq_three` — the count-level partition `bandCard_split` and the ½-symmetry
`symCard_eq_half` are CLASS-GENERIC, so they apply verbatim at the shifted class. -/
theorem bandDiscW_eq_three (x z y : ℕ) (ε₀ : ℝ) (j Q a N M d : ℕ) (hz : 1 ≤ z) :
    blockBoxHonestDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d
      = (1 / 2) * bandSymRectDiscW x z y ε₀ j Q a N M d
        + (1 / 2) * bandDiagDiscW x z y ε₀ j Q a N M d
        + bandLowDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d := by
  have ha : min (z * N + 1) (x + 1) ≤ z * N + 1 := min_le_left _ _
  have hb : x + 1 ≤ x + 1 := le_refl _
  unfold blockBoxHonestDiscW
  rw [bandCard_eq_blockBoxResCountW, bandCard_eq_blockBoxUnitCountW,
    bandCard_split x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1)
      (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) hz ha hb,
    bandCard_split x z y ε₀ j N M (min (z * N + 1) (x + 1)) (x + 1)
      (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) hz ha hb,
    symCard_eq_half x z y ε₀ j N M
      (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d))),
    symCard_eq_half x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))]
  unfold bandSymRectDiscW bandDiagDiscW bandLowDiscW
  ring

/-- **The crude W diagonal disc bound.**  `|bandDiagDiscW| ≤ bandDiagCount`: the Q-restriction
only SHRINKS the class counts (`diagSum_le_bandDiagCount` is class-generic), so the landed
`d`-free counting bound applies verbatim — `BandSplit.bandDiagCount_le` then gives
`≤ y·(M−N)`. -/
theorem abs_diagDiscW_le_bandDiagCount (x z y : ℕ) (ε₀ : ℝ) (j Q a N M d : ℕ) :
    |bandDiagDiscW x z y ε₀ j Q a N M d| ≤ bandDiagCount x z y ε₀ j N M := by
  unfold bandDiagDiscW
  have hR0 := diagSum_nonneg x z y ε₀ j N M
    (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
  have hU0 := diagSum_nonneg x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
  have hRC := diagSum_le_bandDiagCount x z y ε₀ j N M
    (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
  have hUC := diagSum_le_bandDiagCount x z y ε₀ j N M
    (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
  have hc0 : 0 ≤ nuChen (Q * d) := by rw [nuChen_apply]; positivity
  have hc1 : nuChen (Q * d) ≤ 1 := nuChen_le_one (Q * d)
  have hcU : nuChen (Q * d) * diagSum x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod (Q * d)))
      ≤ diagSum x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) :=
    mul_le_of_le_one_left hU0 hc1
  have hcUnn : 0 ≤ nuChen (Q * d)
      * diagSum x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) :=
    mul_nonneg hc0 hU0
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **The per-`d` W triangle over the three pieces** — `BandClose.bandDisc_le_three_pieces`'s
mirror: `|W band disc| ≤ ½·|symRectW| + |lowW| + ½·bandDiagCount`. -/
theorem bandDiscW_le_three_pieces (x z y : ℕ) (ε₀ : ℝ) (j Q a N M d : ℕ) (hz : 1 ≤ z) :
    |blockBoxHonestDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d|
      ≤ (1 / 2) * |bandSymRectDiscW x z y ε₀ j Q a N M d|
        + |bandLowDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d|
        + (1 / 2) * bandDiagCount x z y ε₀ j N M := by
  rw [bandDiscW_eq_three x z y ε₀ j Q a N M d hz]
  have hdiag := abs_diagDiscW_le_bandDiagCount x z y ε₀ j Q a N M d
  have htri : |(1 / 2) * bandSymRectDiscW x z y ε₀ j Q a N M d
        + (1 / 2) * bandDiagDiscW x z y ε₀ j Q a N M d
        + bandLowDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d|
      ≤ |(1 / 2) * bandSymRectDiscW x z y ε₀ j Q a N M d|
        + |(1 / 2) * bandDiagDiscW x z y ε₀ j Q a N M d|
        + |bandLowDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d| := by
    have h1 := abs_add_le ((1 / 2) * bandSymRectDiscW x z y ε₀ j Q a N M d
      + (1 / 2) * bandDiagDiscW x z y ε₀ j Q a N M d)
      (bandLowDiscW x z y ε₀ j Q a N M (min (z * N + 1) (x + 1)) (x + 1) d)
    have h2 := abs_add_le ((1 / 2) * bandSymRectDiscW x z y ε₀ j Q a N M d)
      ((1 / 2) * bandDiagDiscW x z y ε₀ j Q a N M d)
    linarith
  rw [abs_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 by norm_num] at htri
  linarith

open Classical in
/-- **`PloW_discharge`** — the band slot of `hBlockW_of_window_prices` priced by the three
pieces: `½·(sym price) + (low price) + (explicit crude diagonal)`.  The verbatim W-mirror of
`BandClose.Plo_discharge`. -/
theorem PloW_discharge (x z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (bound : ℝ) (j : ℕ)
    (Psym Plow : ℝ) (hz : 1 ≤ z)
    (hSym : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0) ≤ Psym)
    (hLow : (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
          (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0) ≤ Plow) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ (1 / 2) * Psym + Plow
        + (1 / 2) * ((Nat.divisors Ps).card : ℝ)
            * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := by
  classical
  set R := Finset.range (Nat.log 2 x + 1) with hR
  have hterm : ∀ (k d : ℕ),
      (if (d : ℝ) < bound then
          |blockBoxHonestDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
             (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
        ≤ (1 / 2) * (if (d : ℝ) < bound then
              |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
          + (if (d : ℝ) < bound then |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
          + (1 / 2) * (if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k)
              else 0) := by
    intro k d
    by_cases hd : (d : ℝ) < bound
    · simp only [if_pos hd]
      exact bandDiscW_le_three_pieces x z y ε₀ j Q a (pieceN k) (pieceM k) d hz
    · simp only [if_neg hd]; norm_num
  refine le_trans (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun d _ => hterm k d))) ?_
  have hsplit : ∀ k, (∑ d ∈ Nat.divisors Ps,
        ((1 / 2) * (if (d : ℝ) < bound then
              |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
          + (if (d : ℝ) < bound then |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
          + (1 / 2) * (if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k)
              else 0)))
      = (1 / 2) * (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then
              |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
        + (∑ d ∈ Nat.divisors Ps, if (d : ℝ) < bound then
            |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
              (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
        + (1 / 2) * (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) else 0) := by
    intro k
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hdiagBound : ∑ k ∈ R, (∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) else 0)
      ≤ ((Nat.divisors Ps).card : ℝ)
          * ∑ k ∈ R, (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hnn : 0 ≤ bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) := by
      unfold bandDiagCount; positivity
    calc (∑ d ∈ Nat.divisors Ps,
            if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) else 0)
        ≤ ∑ _d ∈ Nat.divisors Ps, bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) := by
          refine Finset.sum_le_sum (fun d _ => ?_)
          split_ifs with h
          · exact le_refl _
          · exact hnn
      _ = ((Nat.divisors Ps).card : ℝ) * bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Nat.divisors Ps).card : ℝ) * ((y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact bandDiagCount_le x z y ε₀ j (pieceN k) (pieceM k)
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsymSum : (1 / 2) * (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
      ≤ (1 / 2) * Psym := mul_le_mul_of_nonneg_left hSym hhalf
  have hdiagSum : (1 / 2) * (∑ k ∈ R, ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then bandDiagCount x z y ε₀ j (pieceN k) (pieceM k) else 0)
      ≤ (1 / 2) * (((Nat.divisors Ps).card : ℝ)
          * ∑ k ∈ R, (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiagBound hhalf
  linarith [hLow]

/-! ## Part G — the band identifications at the shifted pair + the T-difference feeders -/

/-- **`norm_symRectW_eq`** — the symmetric identification at the shifted pair, norm form: the
R₀-generalized core `BandIdent.symRect_eq_apDiscBilinCutoff` at `d := Q·d`,
`R₀ := crtClassW Q d a` says the `‖T-difference‖` at the sym coefficient EQUALS
`|bandSymRectDiscW|`. -/
theorem norm_symRectW_eq {x z y : ℕ} {ε₀ : ℝ} {j N M X Q d a : ℕ}
    (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x) :
    ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j N M) (blockPrimeInd (max y N)) X M
        (crtClassW Q d a) (Q * d) x
      - apDiscBilinCutoff (blockAlphaSym z y ε₀ j N M) (blockPrimeInd (max y N)) X M
          (crtClassW Q d a) (Q * d) (x / 2 + 1)‖
      = |bandSymRectDiscW x z y ε₀ j Q a N M d| := by
  rw [symRect_eq_apDiscBilinCutoff hxX hxlo, bandSymRectDiscW, nuChen_apply]
  rw [show ((symRectCount x z y ε₀ j N M
          (fun v => ((v : ℕ) : ZMod (Q * d))
            = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) : ℝ) : ℂ)
        - (1 / ((Q * d).totient : ℂ)) *
          ((symRectCount x z y ε₀ j N M (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) : ℝ) : ℂ)
      = ((symRectCount x z y ε₀ j N M
            (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
          - 1 / (((Q * d).totient : ℕ) : ℝ) *
            symRectCount x z y ε₀ j N M
              (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) : ℝ) : ℂ) by
        push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- **`norm_lowRectW_eq`** — the low identification at the shifted pair, norm form
(`BandIdent.lowRect_eq_apDiscBilinCutoff` at `d := Q·d`, `R₀ := crtClassW Q d a`). -/
theorem norm_lowRectW_eq {x z y : ℕ} {ε₀ : ℝ} {j N M lo hi X Q d a : ℕ}
    (hbX : hi ≤ X + 1) (hxlo : x / 2 + 1 ≤ x) :
    ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j N) lo hi) (blockPrimeInd N) X M
        (crtClassW Q d a) (Q * d) x
      - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j N) lo hi) (blockPrimeInd N)
          X M (crtClassW Q d a) (Q * d) (x / 2 + 1)‖
      = |bandLowDiscW x z y ε₀ j Q a N M lo hi d| := by
  rw [lowRect_eq_apDiscBilinCutoff hbX hxlo, bandLowDiscW, nuChen_apply]
  rw [show ((lowCard x z y ε₀ j N M lo hi
          (fun v => ((v : ℕ) : ZMod (Q * d))
            = ((crtClassW Q d a : ℕ) : ZMod (Q * d))) : ℝ) : ℂ)
        - (1 / ((Q * d).totient : ℂ)) *
          ((lowCard x z y ε₀ j N M lo hi
            (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) : ℝ) : ℂ)
      = ((lowCard x z y ε₀ j N M lo hi
            (fun v => ((v : ℕ) : ZMod (Q * d)) = ((crtClassW Q d a : ℕ) : ZMod (Q * d)))
          - 1 / (((Q * d).totient : ℕ) : ℝ) *
            lowCard x z y ε₀ j N M lo hi
              (fun v => IsUnit ((v : ℕ) : ZMod (Q * d))) : ℝ) : ℂ) by
        push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

open Classical in
/-- **`PloW_sym_of_box_disc`** — the W sym-band rectangles priced at the T-difference over the
Q-shifted image family; the VERBATIM `hSym` input of `PloW_discharge`.  Mirrors
`MediumFloor.Plo_sym_of_box_disc` (the per-`k` slots are `box_disc_three_way` outputs at the
sym carrier — GLU-2W row 7). -/
theorem PloW_sym_of_box_disc {x z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ)
    (PsymK : ℕ → ℝ) (hQ1 : 1 ≤ Q) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hdiffK : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PsymK k) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK k := by
  classical
  have hQ0 : 0 < Q := hQ1
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [← Finset.sum_filter]
  have himg : (∑ m ∈ ((Nat.divisors Ps).filter
        (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
          - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
            (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
            (x / 2 + 1)‖)
      = ∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
          |bandSymRectDiscW x z y ε₀ j Q a (pieceN k) (pieceM k) d| := by
    rw [Finset.sum_image (fun d₁ _ d₂ _ h => Nat.eq_of_mul_eq_mul_left hQ0 h)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Nat.mul_div_cancel_left d hQ0]
    exact norm_symRectW_eq hxX hxlo
  exact le_trans (le_of_eq himg.symm) (hdiffK k hk)

open Classical in
/-- **`PloW_low_of_box_disc`** — the W low-band rectangles priced at the T-difference over the
Q-shifted image family; the VERBATIM `hLow` input of `PloW_discharge`.  Mirrors
`MediumFloor.Plo_low_of_box_disc` (GLU-2W row 7). -/
theorem PloW_low_of_box_disc {x z y : ℕ} {ε₀ : ℝ} {j X Q a : ℕ} (Ps : ℕ) (bound : ℝ)
    (PlowK : ℕ → ℝ) (hQ1 : 1 ≤ Q) (hxX : x ≤ X) (hxlo : x / 2 + 1 ≤ x)
    (hdiffK : ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PlowK k) :
    (∑ k ∈ Finset.range (Nat.log 2 x + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < bound then
          |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
            (min (z * pieceN k + 1) (x + 1)) (x + 1) d| else 0)
      ≤ ∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK k := by
  classical
  have hQ0 : 0 < Q := hQ1
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [← Finset.sum_filter]
  have himg : (∑ m ∈ ((Nat.divisors Ps).filter
        (fun d : ℕ => (d : ℝ) < bound)).image (fun d => Q * d),
        ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
              (min (z * pieceN k + 1) (x + 1)) (x + 1))
            (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
          - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
              (min (z * pieceN k + 1) (x + 1)) (x + 1))
            (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
      = ∑ d ∈ (Nat.divisors Ps).filter (fun d : ℕ => (d : ℝ) < bound),
          |bandLowDiscW x z y ε₀ j Q a (pieceN k) (pieceM k)
            (min (z * pieceN k + 1) (x + 1)) (x + 1) d| := by
    rw [Finset.sum_image (fun d₁ _ d₂ _ h => Nat.eq_of_mul_eq_mul_left hQ0 h)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Nat.mul_div_cancel_left d hQ0]
    exact norm_lowRectW_eq (by omega) hxlo
  exact le_trans (le_of_eq himg.symm) (hdiffK k hk)

/-! ## Part H — the structural `Dset` rows + the composed supplier -/

/-- **The `hr` row for the Q-shifted family — DISCHARGED (GLU-2W row 4).**  Every member
`m = Q·d` of the image family has `gcd(crtClassW Q (m/Q) a, m) = 1`, from `gcd(Q, Ps) = 1`,
`gcd(Q, a+2) = 1` (at `a = Q−1`: `residue_witness`), and `d` odd
(`switch_dvd_coprime_two`) — via `crtClassW_coprime`.  This is the `hcop2` input of the
r(d)-generalized terminals at `Dset :=` the image family, `r := fun m => crtClassW Q (m/Q) a`. -/
theorem hrW_discharge {Q a Ps : ℕ} (hQ1 : 1 ≤ Q) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps)
    (hQa2 : Nat.Coprime Q (a + 2)) {S : Finset ℕ} (hS : ∀ d ∈ S, d ∣ Ps) :
    ∀ m ∈ S.image (fun d => Q * d), Nat.Coprime (crtClassW Q (m / Q) a) m := by
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  have hdPs : d ∣ Ps := hS d hd
  have hQd : Nat.Coprime Q d := hQPs.coprime_dvd_right hdPs
  have h2d : Nat.Coprime 2 d := switch_dvd_coprime_two hPs hPodd hdPs
  rw [Nat.mul_div_cancel_left d hQ1]
  exact crtClassW_coprime hQd hQa2 h2d

/-- **The `1 ≤ d` row for the Q-shifted family — DISCHARGED.** -/
theorem hDge1W {Q Ps : ℕ} (hQ1 : 1 ≤ Q) (hPs0 : Ps ≠ 0) {S : Finset ℕ}
    (hS : ∀ d ∈ S, d ∣ Ps) :
    ∀ m ∈ S.image (fun d => Q * d), 1 ≤ m := by
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (hS d hd) (Nat.pos_of_ne_zero hPs0)
  exact Nat.mul_pos hQ1 hd0

/-- **The level shape for the Q-shifted family** — the image family sits under `Q·D` whenever
the base family sits under `D` (GLU-2W row 1's structural half; the numeric half is
`Q·D ≤ √(XM)/L^B` at the tower `Q ≤ L`). -/
theorem hDlevW {Q D : ℕ} {S : Finset ℕ} (hSD : ∀ d ∈ S, d ≤ D) :
    ∀ m ∈ S.image (fun d => Q * d), m ≤ Q * D := by
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  exact Nat.mul_le_mul le_rfl (hSD d hd)

open Classical in
/-- **`hBVblocksW_discharge` — THE COMPOSED SUPPLIER (the A3W2 endpoint).**  The
`hBVblocksW` slot of `mainA3_of_block_remainders_W` discharged modulo NAMED rows only:

* `Price j k i` — the high-box boundary-survivor prices (GLU-2W row 6: two
  `medium_survivor_price_sqrtD` applications each, at the shifted `Dset`/`r`);
* `PsymK`/`PlowK j k` — the band T-difference prices (row 7: `box_disc_three_way` at the band
  carriers + the same terminal);
* the diagonal — EXPLICIT (row 8, `bandDiagCount_le` inside `PloW_discharge`);
* `hCE` — the W conversion-error crumb (row 9);
* `hSum`/`hNum` — the budget rows (row 10).

Chains `hNum_at_opW` → `hBlockW_of_window_prices` ← (`PloW_sym_of_box_disc` +
`PloW_low_of_box_disc` → `PloW_discharge`), then `hBVblocksW_of_generalBV`.  The conclusion is
character-for-character the `hBVblocksW` hypothesis `mainA3_of_block_remainders_W` names. -/
theorem hBVblocksW_discharge (x z y : ℕ) (ε₀ : ℝ) (Q a Ps : ℕ) (hPs : Squarefree Ps)
    (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p) (hQPs : Nat.Coprime Q Ps) (hQ1 : 1 ≤ Q)
    (QR : ℝ) (Dlev : ℕ) (X K : ℕ)
    (hz : 1 ≤ z) (hxlo : x / 2 + 1 ≤ x) (hxX : x ≤ X) (hK : Nat.log 2 X ≤ K)
    (hiX : ∀ k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        2 ^ (i + 1) ≤ X + 1)
    (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price j k i)
    (PsymK PlowK : ℕ → ℕ → ℝ)
    (hpriceSym : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PsymK j k)
    (hpriceLow : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PlowK j k)
    (RHD RCE : ℝ)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * ((Nat.divisors Ps).card : ℝ)
                 * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                     (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)))) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then blockConvErrW x z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    -- the EXACT `hBVblocksW` hypothesis of `mainA3_of_block_remainders_W`:
    (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        rosserRemainder (blockSwitchSieveW x z y ε₀ j Q a Ps hPs hPodd) (QR * Dlev))
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  have hBlock : ∀ j ∈ Finset.range (maxBlock x z ε₀ + 1),
      (∑ d ∈ Nat.divisors Ps,
          if (d : ℝ) < QR * Dlev then |blockHonestDiscW x z y ε₀ j Q a d| else 0)
        ≤ (∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * ((Nat.divisors Ps).card : ℝ)
                 * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                     (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)) := by
    intro j _
    refine hBlockW_of_window_prices x z y ε₀ Q a Ps (QR * Dlev) j
      (fun k => ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) K,
        Price j k i) _ ?_ ?_
    · intro k _
      exact hNum_at_opW K Q a Ps (QR * Dlev) (Price j k) hQ1 hz
        (le_trans (min_le_right _ _) (Nat.add_le_add_right hxX 1)) (min_le_left _ _)
        hxlo hK (hiX k) (hprice j k)
    · exact PloW_discharge x z y ε₀ Q a Ps (QR * Dlev) j _ _ hz
        (PloW_sym_of_box_disc Ps (QR * Dlev) (PsymK j) hQ1 hxX hxlo (hpriceSym j))
        (PloW_low_of_box_disc Ps (QR * Dlev) (PlowK j) hQ1 hxX hxlo (hpriceLow j))
  refine hBVblocksW_of_generalBV x z y ε₀ Q a Ps hPs hPodd hQPs QR Dlev ?_ hCE hNum
  exact le_trans (Finset.sum_le_sum hBlock) hSum

/-! ## The composition into `mainA3_of_block_remainders_W` — the required `example`

The chain `hBVblocksW_discharge → mainA3_of_block_remainders_W` lands
character-for-character in the `hBVblocksW` slot and emits the `hA3` shape at the W-carrier
(the AP-scale main term `tripleSum/φ(Q)`).  The remaining hypotheses are exactly the GLU-2W
ledger rows of the module header. -/

section CompositionSanity

/-- **The A3W2 discharge composition.**  Everything below `mainA3_of_block_remainders_W`'s
`hBVblocksW` slot is discharged by `hBVblocksW_discharge`; the surviving hypotheses are the
NAMED numeric/threshold rows (the module-header ledger).  The conclusion is the EXACT
`hA3`-shape `chen_of_hypotheses_W` consumes. -/
example (x z y : ℕ) (ε₀ : ℝ) (P Q a w' Ps Dlev : ℕ) (ε K QR : ℝ) (X KX : ℕ)
    (hz : 1 ≤ z) (hε₀ : 0 < ε₀)
    (hPs : Squarefree Ps) (hPodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hPy : ∀ p ∈ Ps.primeFactors, p < y)
    (hPlow : ∀ p ∈ Ps.primeFactors, w0R ε ≤ (p : ℝ))
    (hx : 2 ≤ x) (hyx2 : y ≤ x / 2)
    (hQfull : ∀ q, q.Prime → q < w' → q ∣ Q)
    (hPfull' : ∀ q, q.Prime → w' ≤ q → q < z → q ∣ P)
    (hQa2 : Nat.Coprime Q (a + 2)) (hQPs : Nat.Coprime Q Ps) (hQ1 : 1 ≤ Q)
    (hD2 : 2 ≤ Dlev) (hQR : 1 ≤ QR)
    (hε : 0 < ε) (hw0 : 3 ≤ w0R ε) (hεsmall : ε ≤ 1 / 1000) (hKe : K ≤ 1 + ε)
    (h4 : ∀ (s' : BoundingSieve) (z' D' : ℕ), 1 ≤ D' →
        (∀ q ∈ s'.prodPrimes.primeFactors, q < z') →
        (∀ q ∈ s'.prodPrimes.primeFactors,
            3 ≤ (q : ℝ) ∧ 19 / Real.log q + 4 / ((q : ℝ) - 1) ≤ Real.log (1 + ε)) →
        (∀ q ∈ s'.prodPrimes.primeFactors, s'.nu q ≤ 1 / ((q : ℝ) - 1)) →
        1 ≤ logRatio z' D' → logRatio z' D' ≤ 3 →
        Vlow s' D' ≤ (3 * K / logRatio z' D') * Salt.BrunLower.W s')
    (hStop : 1 ≤ logRatio y Dlev)
    (hxX : x ≤ X) (hKX : Nat.log 2 X ≤ KX)
    (hiX : ∀ k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) KX,
        2 ^ (i + 1) ≤ X + 1)
    (Price : ℕ → ℕ → ℕ → ℝ)
    (hprice : ∀ j k, ∀ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) KX,
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                  (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                (crtClassW Q (m / Q) a) m x‖)
          + (∑ m ∈ ((Nat.divisors Ps).filter
                (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
              ‖apDiscBilinCutoff (restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0
                    (min (z * pieceN k + 1) (x + 1))) (2 ^ i) (2 ^ (i + 1)))
                  (blockPrimeInd (pieceN k)) (2 ^ (i + 1) - 1) (pieceM k)
                  (crtClassW Q (m / Q) a) m (x / 2 + 1)‖)
          ≤ Price j k i)
    (PsymK PlowK : ℕ → ℕ → ℝ)
    (hpriceSym : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (blockAlphaSym z y ε₀ j (pieceN k) (pieceM k))
                (blockPrimeInd (max y (pieceN k))) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PsymK j k)
    (hpriceLow : ∀ j, ∀ k ∈ Finset.range (Nat.log 2 x + 1),
        (∑ m ∈ ((Nat.divisors Ps).filter
              (fun d : ℕ => (d : ℝ) < QR * Dlev)).image (fun d => Q * d),
            ‖apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m x
              - apDiscBilinCutoff (restrictAlpha (blockAlphaLow z y ε₀ j (pieceN k))
                  (min (z * pieceN k + 1) (x + 1)) (x + 1))
                (blockPrimeInd (pieceN k)) X (pieceM k) (crtClassW Q (m / Q) a) m
                (x / 2 + 1)‖)
          ≤ PlowK j k)
    (RHD RCE : ℝ)
    (hSum : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1),
        ((∑ k ∈ Finset.range (Nat.log 2 x + 1),
            ∑ i ∈ dyadicBoundary (pieceN k) (pieceM k) (x / 2 + 1) x (z * y) KX,
              Price j k i)
          + ((1 / 2) * (∑ k ∈ Finset.range (Nat.log 2 x + 1), PsymK j k)
             + (∑ k ∈ Finset.range (Nat.log 2 x + 1), PlowK j k)
             + (1 / 2) * ((Nat.divisors Ps).card : ℝ)
                 * ∑ k ∈ Finset.range (Nat.log 2 x + 1),
                     (y : ℝ) * ((pieceM k - pieceN k : ℕ) : ℝ)))) ≤ RHD)
    (hCE : (∑ j ∈ Finset.range (maxBlock x z ε₀ + 1), ∑ d ∈ Nat.divisors Ps,
        if (d : ℝ) < QR * Dlev then blockConvErrW x z y ε₀ j Q d else 0) ≤ RCE)
    (hNum : RHD + RCE ≤ (x : ℝ) / (Real.log x) ^ 10) :
    -- the EXACT `hA3`-shape at the W-carrier (the AP-scale main term):
    triplePrimeSumW Q a x P y
      ≤ Real.log x *
          (tripleSum x z y / (Q.totient : ℝ)
              * Salt.BrunLower.W (switchSieve x z y Ps hPs hPodd)
              * (Fchain (maxDepth (switchSieve x z y Ps hPs hPodd)) (logRatio y Dlev)
                + ε * CsharpB ε * Real.exp 2 * hBJS (logRatio y Dlev))
            + (x : ℝ) / (Real.log x) ^ 10) := by
  have hxlo : x / 2 + 1 ≤ x := by omega
  refine mainA3_of_block_remainders_W x z y P Q a w' Ps Dlev ε₀ ε K QR hz hε₀ hPs hPodd hPy
    hPlow hx hyx2 hQfull hPfull' hQa2 hD2 hQR hε hw0 hεsmall hKe h4 hStop ?_
  exact hBVblocksW_discharge x z y ε₀ Q a Ps hPs hPodd hQPs hQ1 QR Dlev X KX hz hxlo hxX hKX
    hiX Price hprice PsymK PlowK hpriceSym hpriceLow RHD RCE hSum hCE hNum

-- the W box objects + the piece decomposition (items 1–2)
#check @Salt.Chen.blockBoxResCountW
#check @Salt.Chen.blockBoxUnitCountW
#check @Salt.Chen.blockBoxHonestDiscW
#check @Salt.Chen.blockHonestDiscW_eq_sum_pieces
#check @Salt.Chen.abs_blockHonestDiscW_le_sum_pieces
#check @Salt.Chen.blockBoxHonestDiscW_split_m
#check @Salt.Chen.hBlockW_of_window_prices
-- the box identification + pricing (item 3)
#check @Salt.Chen.blockBoxW_windowDisc_eq
#check @Salt.Chen.hHD_of_box_discW
#check @Salt.Chen.hNum_at_opW
-- the band close (item 4)
#check @Salt.Chen.bandSymRectDiscW
#check @Salt.Chen.bandLowDiscW
#check @Salt.Chen.bandDiagDiscW
#check @Salt.Chen.bandDiscW_eq_three
#check @Salt.Chen.bandDiscW_le_three_pieces
#check @Salt.Chen.PloW_discharge
#check @Salt.Chen.norm_symRectW_eq
#check @Salt.Chen.norm_lowRectW_eq
#check @Salt.Chen.PloW_sym_of_box_disc
#check @Salt.Chen.PloW_low_of_box_disc
-- the composed supplier (item 5) + the structural Dset rows
#check @Salt.Chen.hrW_discharge
#check @Salt.Chen.hDge1W
#check @Salt.Chen.hDlevW
#check @Salt.Chen.hBVblocksW_discharge
-- the landed consumers/suppliers this composes with (GLU-2W's slots)
#check @Salt.Chen.mainA3_of_block_remainders_W
#check @Salt.Chen.hBVblocksW_of_generalBV
#check @Salt.Chen.box_disc_three_way
#check @Salt.Chen.medium_survivor_price_sqrtD
#check @Salt.Chen.general_BV_cutoff_sqrtD
#check @Salt.Chen.d0_window_nonempty
#check @Salt.Chen.hDsq_at_sym_carrier
#check @Salt.Chen.medium_support_floor_high
#check @Salt.Chen.medium_support_floor_sym
#check @Salt.Chen.medium_support_floor_low

end CompositionSanity

end Salt.Chen
