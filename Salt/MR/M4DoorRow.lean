/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Maximal
import Salt.MR.M4Band
import Salt.MR.M4RowSupply
import Salt.MR.CaseAWide
import Salt.MR.M4Seam

/-!
# `M4DoorRow` — ⟦W2-DOOR⟧: the capstone at the dyadic row, and THE TWO WALLS it meets

The night sequence's step 2 asked for `M4Maximal.M4ChiDyadicRowMeanSq` to be discharged from
the band-re-cut capstone `M4MeanSq.m4_meansq_per_chi_gen`, instantiated per `(χ, block,
shift, dyadic length)`.  The instantiation does **not** close, and the two obstructions are
structural rather than proof-engineering.  This file lands every stone that IS available at
the door datum (§1–§5, all kernel-checked and reusable) and states the two obstructions as
theorems rather than prose (§6–§7), so the next design block reads them off the kernel.

## ⟦WHAT LANDS⟧ (§1–§5) — the door row's supply, as far as it goes

* **§1 the half-open window cut** `winCutH` and the datum bridge.  The capstone's two support
  pins straddle the block bottom: `hsupp0` demands `a n = 0` for `(n : ℝ) ≤ X = X_d` while
  `hasupp` allows support on `[X_d, 2X_d]`, so the door datum must be cut HALF-OPEN.
  `SeamRowWindowed.winCut` (the closed cut, which `M4Band`'s pair law is stated at) fails
  `hsupp0` at the single point `n = X_d` (`winCut_endpoint`).  Both cuts are invisible to the
  conclusion, because `seamS0 (2X_d) X_d` filters `X_d < m` strictly
  (`shortSum_winCutH_seamS0`, `shortSum_winCut_seamS0`).
* **§2 the S8 datum slots** at the door's cut datum: `ha1`, `hsupp0`, `hasupp` — all three
  discharged (`doorRow_ha1`, `doorRow_hsupp0`, `doorRow_hasupp`).
* **§3 the co-factor socket** at `Ps := 1`: `CofactorSupplier.doorCofactor0_at_one` turns
  `CaseAWide.m4_supplier_complete`'s conclusion into the capstone's `hsockR` slot at
  `b := doorChiCoeff χ M` verbatim (`cofactorSocket_doorChiCoeff`).
* **§4 the Ramaré-band pair law** at the door's own gate: `M4Band.doorChiCoeff_seamCoefW_band`
  composed with `door_band_gate_of_log`, i.e. `hcoefPin` discharged from binders the capstone
  already carries (`doorChiCoeff_seamCoefW_at_door`).
* **§5 the coprime-tail supply** at the door's cut datum: `M4RowSupply.m4_tail_supply_at_band`
  instantiated, delivering `hMtail`, `hMtail0` and the `12·EP₂` budget line inside the K6
  existential (`m4_door_tail_supply`).

## ⚠ ⟦WALL 1 — THE K-BLOCK WINDOW LAW⟧ (§6)

`m4_meansq_per_chi_gen` carries, at the door's own K-ladder blocks `[𝒫_j, 𝒬K_j]`, the PAIR

```
hcoefBand : ∀ j ∈ [1,2], ∀ p m, p prime → 𝒫_j ≤ p ≤ 𝒬K_j → ¬p∣m →
              X_d ≤ pm ≤ 2X_d → a (p·m) = bfam j m · cf p
hwinBand  : ∀ j ∈ [1,2], ∀ p m, p prime → 𝒫_j ≤ p ≤ 𝒬K_j →
              cf p · bfam j m ≠ 0 → X_d ≤ pm ≤ 2X_d
```

(inherited verbatim from `ThmA2Rows.a2Rows_of_capfree3`'s `hcoef`/`hwin`, where the pair is
consumed through `M4MeanSq.coef_widen_of_window`).  `band_window_ratio_lock` below is what
that pair says: **any two block primes at which the datum is live are within a factor `2` of
each other.**  The door's level-1 K-block spans `[2^{A}, 2^{M·A}]` with `A = Adoor M ≥ 2^18`
(`door_block_one_wide`: it contains a factor `4` already at `M ≥ 2`), and the door's sieved
datum `1_𝒮·λχ̄` is by construction supported on multiples of block primes — `𝒮` is exactly
"has a prime factor in every block".  So the datum is live at block primes spanning the whole
block, and the lock is violated.

This is `M4Join` §1's ⟦THE WALL⟧ (`m4_row_cf_block_eq_zero`) alive on the K-BLOCK chain: the
closing wave deleted `hwinPin` from the Ramaré-band pin chain, but `hwinBand` — the same law
at the door's own blocks — was left standing, and it is the binder the door datum cannot
inhabit.  The repair is a statement re-cut at `a2Rows_of_capfree3`'s `hwin` (ThmA2Rows:916),
upstream of the M4 wave and outside an executor's authorization.

## ⚠ ⟦WALL 2 — THE UNIFORM-IN-`j` GRADE⟧ (§7)

`M4ChiDyadicRowMeanSq R M k MS` asks ONE grade `MS H` at EVERY dyadic length `2^j`,
`j ≤ log₂ H`.  Two independent facts contradict that:

* the capstone cannot even be STATED at small `j`: its window gates are `4 ≤ h` and
  `𝒬K_1 ≤ h`, and at `h = 2^j` the second forces `M·Adoor M ≤ j` (`door_length_gate`),
  i.e. `j ≥ 2^18` — every smaller `j` is outside the capstone's reach
  (`door_length_gate_fails_of_small`);
* at `j = 0` the quantity IS the block density of the live sieved residues (the integral
  collapses to `(1/X_d)·∑_{X_d<m≤2X_d}‖a_m‖²`, one integer per unit `y`-interval), which is
  `≍ 1` — while `m4_wave_closed_of_dyadicRow`'s own drift/budget gates force
  `MS H ≲ (log H)^{-30}`.  So no `MS` serves both ends.

The dyadic assembly does not need uniformity: `M4Maximal` §4's count
`∑_j (⌊H/2^{j+1}⌋+1)(2^j)² ≤ 3H²` is where the length-dependence is thrown away
(`dyadic_count_weight_le`), and a LENGTH-GRADED input `MS : ℕ → ℕ → ℝ` costs nothing there
(the `j = 0` term contributes `≍ H`, against a budget of `H²·(log H)^{-30}`).  Re-grading
`M4ChiDyadicRowMeanSq` is a statement change in `M4Maximal`, again Fable/human tier.

## ⟦THE T₀-BAND, NAMED⟧

No landed supplier reaches the capstone's `hT0band` slot at the door datum:
`M4Seam.m4_hT0band_at_row` needs the (now deleted) `blockOmega P P`-support pin, and
`M4MeanSq.m4_t0band_of_live` needs agreement with the UNSIEVED seam coefficient (the A2-5
clash).  The only open route is `M4Seam.cfb_t0band_supply_of_sup` at a CARRIED per-frequency
polynomial sup `‖spolyA a t m‖ ≤ S·m` for `|t| ≤ seamT0 X`, `m ≤ N`, with
`S ≤ 2(C₁e^{−M₀/2e} + 4(log X)^{−1/2+1/1000})` — a genuine cancellation demand on the door's
sieved χ-twisted datum, and the item the S11 spine would have to price.  Recorded here, not
attempted.

## ⟦THE TRAPS RESPECTED⟧

* the four log scales — this file writes `log X` only at the block scale `X_d` and never
  collapses it to `log R.x`; `Nat.log 2` appears only in `Adoor`/the length gate;
* the un-phased datum — every carrier is `doorChiCoeff χ M` BARE (frequency `0`);
* `liouChi`, never `lamChi`;
* half-open — `winCutH` is the half-open cut, `seamS0` filters `X < m` strictly;
* strict gates — `2 ≤ P`, `P ≤ Q`, `0 < m` are carried, never weakened.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE HALF-OPEN WINDOW CUT, AND WHY IT IS FORCED

The capstone's two support pins are

* `hsupp0 : ∀ n, (n : ℝ) ≤ X → a n = 0`   (`X = X_d`, the block bottom), and
* `hasupp : ∀ n, a n ≠ 0 → X_d ≤ n ∧ n ≤ 2X_d`,

so the admissible support is the HALF-OPEN window `(X_d, 2X_d]`.  `SeamRowWindowed.winCut`
is the CLOSED cut and fails `hsupp0` at the single point `n = X_d` (`winCut_endpoint`).
Both cuts agree on `seamS0 (2X_d) X_d`, which is what the conclusion reads. -/

/-- **THE HALF-OPEN DYADIC CUT** `winCutH X_d F = 1_{(X_d, 2X_d]}·F` — `winCut`'s half-open
sibling, the shape the capstone's `hsupp0`/`hasupp` pair forces. -/
def winCutH (Xd : ℕ) (F : ℕ → ℂ) : ℕ → ℂ :=
  fun n => if Xd < n ∧ n ≤ 2 * Xd then F n else 0

theorem winCutH_of_mem {Xd n : ℕ} (F : ℕ → ℂ) (h1 : Xd < n) (h2 : n ≤ 2 * Xd) :
    winCutH Xd F n = F n := by
  simp only [winCutH]
  split_ifs with hc
  · rfl
  · exact absurd ⟨h1, h2⟩ hc

theorem winCutH_supp {Xd : ℕ} {F : ℕ → ℂ} {n : ℕ} (h : winCutH Xd F n ≠ 0) :
    Xd < n ∧ n ≤ 2 * Xd := by
  by_contra hc
  exact h (by simp only [winCutH, if_neg hc])

/-- `hasupp`'s shape: the cut datum lives in the closed dyadic window. -/
theorem winCutH_asupp {Xd : ℕ} {F : ℕ → ℂ} {n : ℕ} (h : winCutH Xd F n ≠ 0) :
    Xd ≤ n ∧ n ≤ 2 * Xd :=
  ⟨(winCutH_supp h).1.le, (winCutH_supp h).2⟩

/-- `hsupp0`'s shape: the cut datum vanishes at and below the block bottom. -/
theorem winCutH_supp0 {Xd : ℕ} (F : ℕ → ℂ) {n : ℕ} (h : (n : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    winCutH Xd F n = 0 := by
  have hc : ¬ (Xd < n ∧ n ≤ 2 * Xd) := by
    rintro ⟨h1, -⟩
    have : ((Xd : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast h1
    linarith
  simp only [winCutH, if_neg hc]

theorem norm_winCutH_le {Xd : ℕ} {F : ℕ → ℂ} (hF : ∀ n, ‖F n‖ ≤ 1) (n : ℕ) :
    ‖winCutH Xd F n‖ ≤ 1 := by
  simp only [winCutH]
  split_ifs
  · exact hF n
  · simp

/-- ⟦THE ENDPOINT STRADDLE⟧ the CLOSED cut does not vanish at the block bottom, so it cannot
meet the capstone's `hsupp0` unless the datum itself vanishes there.  This is why §1 mints the
half-open cut — and why `M4Band`'s pair law, stated at `winCut`, does not transfer to it
without an endpoint case (see §6's note). -/
theorem winCut_endpoint {Xd : ℕ} (F : ℕ → ℂ) (h : 1 ≤ Xd) :
    winCut Xd F Xd = F Xd :=
  winCut_of_mem F le_rfl (by omega)

/-- The half-open cut agrees with its datum on the row's own index set. -/
theorem winCutH_eq_on_seamS0 {Xd n : ℕ} (F : ℕ → ℂ)
    (hn : n ∈ seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) :
    winCutH Xd F n = F n := by
  obtain ⟨-, h2, h3⟩ := mem_seamS0 hn
  exact winCutH_of_mem F (by exact_mod_cast h3) h2

/-- The closed cut agrees with its datum on the row's own index set. -/
theorem winCut_eq_on_seamS0 {Xd n : ℕ} (F : ℕ → ℂ)
    (hn : n ∈ seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) :
    winCut Xd F n = F n := by
  obtain ⟨-, h2, h3⟩ := mem_seamS0 hn
  have : Xd < n := by exact_mod_cast h3
  exact winCut_of_mem F this.le h2

/-- **THE DATUM BRIDGE** — the cut is invisible to the row's short sum, at every `y` and every
window length.  This is what lets the capstone be instantiated at a CUT datum while
`M4Maximal.M4ChiDyadicRowMeanSq` speaks the BARE one. -/
theorem shortSum_winCutH_seamS0 {Xd : ℕ} (F : ℕ → ℂ) (y h : ℝ) :
    shortSum (winCutH Xd F) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y h
      = shortSum F (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y h := by
  simp only [shortSum]
  exact Finset.sum_congr rfl fun m hm =>
    winCutH_eq_on_seamS0 F (Finset.mem_filter.mp hm).1

/-- The closed cut's bridge (same proof; the closed cut is the shape `M4Band`'s pair law
delivers). -/
theorem shortSum_winCut_seamS0 {Xd : ℕ} (F : ℕ → ℂ) (y h : ℝ) :
    shortSum (winCut Xd F) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y h
      = shortSum F (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y h := by
  simp only [shortSum]
  exact Finset.sum_congr rfl fun m hm =>
    winCut_eq_on_seamS0 F (Finset.mem_filter.mp hm).1

/-! ## §2 — THE S8 DATUM SLOTS AT THE DOOR'S CUT DATUM

`ha1`, `hsupp0`, `hasupp` — three of the capstone's binders, discharged once and for all at
`a := winCutH X_d (doorChiCoeff χ M)`. -/

/-- The door's sieved, χ-twisted datum is `1`-bounded (`memSCoeff` only deletes terms). -/
theorem norm_doorChiCoeff_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (M n : ℕ) :
    ‖doorChiCoeff χ M n‖ ≤ 1 :=
  norm_memSCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 n

/-- `ha1` at the door row datum. -/
theorem doorRow_ha1 {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ) :
    ‖winCutH Xd (doorChiCoeff χ M) n‖ ≤ 1 :=
  norm_winCutH_le (norm_doorChiCoeff_le_one χ M) n

/-- `hsupp0` at the door row datum. -/
theorem doorRow_hsupp0 {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ)
    (h : (n : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    winCutH Xd (doorChiCoeff χ M) n = 0 :=
  winCutH_supp0 _ h

/-- `hasupp` at the door row datum. -/
theorem doorRow_hasupp {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd : ℕ) (n : ℕ)
    (h : winCutH Xd (doorChiCoeff χ M) n ≠ 0) :
    Xd ≤ n ∧ n ≤ 2 * Xd :=
  winCutH_asupp h

/-! ## §3 — THE CO-FACTOR SOCKET AT THE DOOR DATUM (`Ps := 1`)

⟦THE SHIFT DECOUPLING⟧ (the band wave's C-1) split `doorCofactor0`'s shift from the Ramaré
band bottom, so `CaseAWide.m4_supplier_complete` may be read at `Ps := 1`; there
`doorCofactor0_at_one` identifies its datum with the door's own `doorChiCoeff`.  The capstone's
`hsockR` slot is then filled verbatim — the socket is the ONLY fact the row reads about `b`,
and the pair law of §4 delivers `b = doorChiCoeff χ M`. -/

/-- The supplier's datum at the shift `1` IS the door's sieved χ-twisted datum. -/
theorem doorCofactor0_door_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) :
    doorCofactor0 χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 1
      = doorChiCoeff χ M :=
  doorCofactor0_at_one χ _ _ 2

/-- **THE SOCKET, AT THE CAPSTONE'S `b`-SLOT** — `m4_supplier_complete`'s conclusion at
`Ps := 1`, re-read at the door datum. -/
theorem cofactorSocket_doorChiCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) {M : ℕ}
    {H : ℝ} {N Xd P Q : ℕ} {Tann Rrad t₁ Rbar : ℝ}
    (h : CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar
      (doorCofactor0 χ (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 1)) :
    CofactorSocket H N Xd P Q Tann Rrad t₁ Rbar (doorChiCoeff χ M) := by
  rwa [doorCofactor0_door_eq] at h

/-! ## §4 — THE RAMARÉ-BAND PAIR LAW AT THE DOOR'S OWN GATE

`M4Band.doorChiCoeff_seamCoefW_band` needs the band gate `𝒬K_j < P`; `door_band_gate_of_log`
supplies it from binders the capstone already carries (`hQXd`, `hPlow`).  Composed, this is
the capstone's `hcoefPin` slot at `b = doorChiCoeff χ M`, `cf = liouChi χ` — the SAME `b` the
socket of §3 delivers. -/

/-- **`hcoefPin`, AT THE DOOR** — the band pair law with its gate discharged from the
capstone's own `hQXd`/`hPlow`. -/
theorem doorChiCoeff_seamCoefW_at_door {q : ℕ} (χ : DirichletCharacter ℂ q) {M Xd P Q : ℕ}
    {X : ℝ} (hM : 1 ≤ M) (hX : 1 < Real.log X)
    (hQlog : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log X))
    (hPlow : P83 X theta293 ≤ (P : ℝ)) :
    SeamCoefW Xd P Q (winCut Xd (doorChiCoeff χ M)) (doorChiCoeff χ M) (liouChi χ) :=
  doorChiCoeff_seamCoefW_band χ M Xd P Q
    (door_band_gate_of_log (by omega : 1 ≤ 3072 * M) hX hQlog hPlow)

/-! ## §5 — THE COPRIME-TAIL SUPPLY AT THE DOOR DATUM

`M4RowSupply.m4_tail_supply_at_band`'s triple (`hMtail`, `hMtail0`, the `12·EP₂` budget line)
instantiated at the door's cut datum — its two datum binders are §2's.  ⟦THE K6 PATTERN⟧: the
mass constant `C` is opaque, so the `2688`-threshold is stated where `C` is bound. -/

/-- **THE DOOR ROW'S TAIL TRIPLE** (`m4_door_tail_supply`) — the coprime-tail mass, its
nonnegativity, and the capstone's `hEP2` budget line, all at
`M_tail := C·(log P/log Q)/X_d + 1/X_d²` and the door's own cut datum. -/
theorem m4_door_tail_supply :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (M P Q Xd N : ℕ) (X ε : ℝ),
        (Xd : ℝ) = X → (N : ℝ) = 2 * X → 0 < X → 256 ≤ Real.log X →
        2 ≤ P → P ≤ Q → 1 ≤ Xd →
        100 * Real.log Q ≤ Real.log Xd →
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
        P83 X theta293 ≤ (P : ℝ) →
        10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ) →
        8640 ≤ (Real.log X) ^ ε →
        Real.log (P : ℝ) / Real.log (Q : ℝ)
          ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)) →
        2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε →
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖winCutH Xd (doorChiCoeff χ M) n‖ ^ 2 / (n : ℝ) ^ 2
            ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
          ∧ 0 ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2
          ∧ 12 * (witEP2 X N Xd P
              + 4 / 3 * ((2 * X + 20 * (N : ℝ))
                * (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)))
            ≤ (Real.log X) ^ (-theta293 + ε) := by
  obtain ⟨C, hC0, hband⟩ := m4_tail_supply_at_band
  refine ⟨C, hC0, ?_⟩
  intro q χ M P Q Xd N X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate hdom hP83 hthr habs hgrade hthr2
  exact hband P Q Xd N (winCutH Xd (doorChiCoeff χ M)) X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate
    hdom (doorRow_ha1 χ M Xd) (fun n hn => doorRow_hasupp χ M Xd n hn) hP83 hthr habs hgrade
    hthr2

/-! ## §6 — ⚠ ⟦WALL 1⟧: THE K-BLOCK WINDOW LAW LOCKS THE BLOCK TO A FACTOR `2`

The capstone's `hcoefBand`/`hwinBand` pair (`M4MeanSq`, inherited from
`ThmA2Rows.a2Rows_of_capfree3`'s `hcoef`/`hwin`) is the K-block analogue of the deleted
`hwinPin`.  `band_window_ratio_lock` states exactly what it costs: two block primes at which
the datum is live cannot differ by more than a factor `2`.  `door_block_one_wide` shows the
door's level-1 block already spans a factor `4` at `M ≥ 2` (in fact `2^{(M−1)·2^18}`), and the
sieve `𝒮` puts live points at block primes throughout the block.  Hence no `(bfam, cf)`
inhabits the pair at the door's datum. -/

/-- **THE RATIO LOCK** (`band_window_ratio_lock`).  Under the capstone's window pair at one
block `[P₁, Q₁]`: if the datum is nonzero at `p·m` and at `p'·m'` — both admissible
factorisations inside the dyadic window — then `p' ≤ 2p`.

The proof is three lines and uses nothing but the two binders: the first factorisation makes
the co-factor `bfam m` nonzero, the second makes `cf p'` nonzero, and then the window law
applied to the CROSS pair `(p', m)` puts `p'·m` in a window that already contains `p·m`. -/
theorem band_window_ratio_lock {a cf bf : ℕ → ℂ} {Xd P1 Q1 : ℕ}
    (hcoef : ∀ p m : ℕ, p.Prime → P1 ≤ p → p ≤ Q1 → ¬ p ∣ m →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
        a (p * m) = bf m * cf p)
    (hwin : ∀ p m : ℕ, p.Prime → P1 ≤ p → p ≤ Q1 → cf p * bf m ≠ 0 →
      (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    {p p' m m' : ℕ} (hm0 : 0 < m)
    (hp : p.Prime) (hpP : P1 ≤ p) (hpQ : p ≤ Q1) (hpm : ¬ p ∣ m)
    (hlo : (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ)) (hhi : (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ))
    (hp' : p'.Prime) (hp'P : P1 ≤ p') (hp'Q : p' ≤ Q1) (hp'm : ¬ p' ∣ m')
    (hlo' : (Xd : ℝ) ≤ (p' : ℝ) * (m' : ℝ)) (hhi' : (p' : ℝ) * (m' : ℝ) ≤ 2 * (Xd : ℝ))
    (hne : a (p * m) ≠ 0) (hne' : a (p' * m') ≠ 0) :
    (p' : ℝ) ≤ 2 * (p : ℝ) := by
  have h1 : bf m * cf p ≠ 0 := by
    rw [← hcoef p m hp hpP hpQ hpm hlo hhi]; exact hne
  have h2 : bf m' * cf p' ≠ 0 := by
    rw [← hcoef p' m' hp' hp'P hp'Q hp'm hlo' hhi']; exact hne'
  have hbf : bf m ≠ 0 := left_ne_zero_of_mul h1
  have hcf' : cf p' ≠ 0 := right_ne_zero_of_mul h2
  obtain ⟨-, hup⟩ := hwin p' m hp' hp'P hp'Q (mul_ne_zero hcf' hbf)
  have hm0R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hkey : (p' : ℝ) * (m : ℝ) ≤ (2 * (p : ℝ)) * (m : ℝ) := by linarith
  exact le_of_mul_le_mul_right hkey hm0R

/-- **THE DOOR'S LEVEL-1 K-BLOCK IS WIDE** (`door_block_one_wide`).  `𝒫_1 = 2^{Adoor M}` and
`𝒬K_1 = 2^{M·Adoor M}`, so already at `M ≥ 2` the block contains a factor `4` — and
`Adoor M ≥ 2^18`, so the true spread is `2^{(M−1)·2^18}`.  Against §6's ratio lock this is the
wall. -/
theorem door_block_one_wide {M : ℕ} (hM : 2 ≤ M) :
    4 * calP (Adoor M) (3072 * M) 1 ≤ calQK (Adoor M) (3072 * M) M 1 := by
  have hE : calE (Adoor M) (3072 * M) 1 = Adoor M := calE_one _ _
  have hA2 : 2 ≤ Adoor M := le_trans (by norm_num) (Adoor_ge M)
  have hstep : Adoor M + 2 ≤ 1 ^ 2 * M * Adoor M := by
    have h2 : 2 * Adoor M ≤ M * Adoor M := Nat.mul_le_mul_right _ hM
    simp only [one_pow, one_mul]
    omega
  have hL : 4 * calP (Adoor M) (3072 * M) 1 = 2 ^ (Adoor M + 2) := by
    simp only [calP, hE, pow_add]
    ring
  have hR : calQK (Adoor M) (3072 * M) M 1 = 2 ^ (1 ^ 2 * M * Adoor M) := by
    simp only [calQK, hE]
  rw [hL, hR]
  exact Nat.pow_le_pow_right (by norm_num) hstep

/-! ## §7 — ⚠ ⟦WALL 2⟧: THE UNIFORM-IN-`j` GRADE

`M4ChiDyadicRowMeanSq` asks one grade at every dyadic length `2^j`, `j ≤ log₂ H`.  The
capstone's own window gate `𝒬K_1 ≤ h` reads, at `h = 2^j`, as an ARITHMETIC lower bound on
`j` — `M·Adoor M ≤ j` — so the small-`j` instances are outside the capstone's statement
entirely, before any estimate is attempted. -/

/-- **THE LENGTH GATE, SOLVED** (`door_length_gate`).  The capstone's `hQ1h` at the dyadic
length `h = 2^j` is `M·Adoor M ≤ j`. -/
theorem door_length_gate {M j : ℕ}
    (h : ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)) :
    M * Adoor M ≤ j := by
  have hN : calQK (Adoor M) (3072 * M) M 1 ≤ 2 ^ j := by exact_mod_cast h
  rw [calQK, calE_one] at hN
  have hle : 1 ^ 2 * M * Adoor M ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hN
  simpa using hle

/-- **THE SMALL-`j` INSTANCES ARE UNREACHABLE** (`door_length_gate_fails_of_small`).  For
`1 ≤ M` the capstone's window gate is violated at every dyadic length `2^j` with
`j < 2^18 ≤ M·Adoor M` — in particular at `j = 0`, which
`M4Maximal.M4ChiDyadicRowMeanSq` demands at every `H`. -/
theorem door_length_gate_fails_of_small {M j : ℕ} (hM : 1 ≤ M) (hj : j < 2 ^ 18) :
    ¬ ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
  intro h
  have hle := door_length_gate h
  have hA : 2 ^ 18 ≤ Adoor M := Adoor_ge M
  have : Adoor M ≤ M * Adoor M := Nat.le_mul_of_pos_left _ hM
  omega

end Salt.MR

end
