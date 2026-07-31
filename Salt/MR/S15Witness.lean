/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S15Compose
import Salt.MR.ConstantsExposed
import Salt.Tactic.AuditAxioms

/-!
# ⟦S15-WITNESS⟧ — THE `M`-SELECTION REGISTER, WITNESSED AT NUMERALS

PURELY ADDITIVE: no landed declaration is touched.

`S15Compose` §9 closes with ⟦THE ONE LOUD STOP⟧ — `logChowla2_conditional_sharp` carries
`S15Sel'` and `S15CrossingBound`, and no witness for `S15Sel'` was attempted, because its
eleven lines must be met against the OPAQUE `Cg`, `δ₀`, `Ct`, `x₀`, `Mfl`, `K` that
`logChowla2_capstone_final_const'_graded` produces existentially.  This file closes that
stop in the only honest way available: the opaque constants' NUMERIC BOUNDS become explicit
hypotheses, and at those numerals every line of the register is discharged at an EXPLICIT
`M`.

## §A — the witness tuple

| slot | value | why |
|---|---|---|
| `λ₋ := loglog H₋` | `≈ 69.08` (`log H₋ ≥ 10^30`) | `half` needs `log H₋ ≥ 1.4·M·A(M)` |
| `λ₊ := loglog H₊` | `≤ 2·10^8` | `anchor`/`gRows`/`gP1`/`lvl` all read `λ₊` |
| `M` | `s15WitM = max (max Mfl x₀) (max 1 ⌈24Cg/δ₀⌉₊)` | the three `M`-lowers, by construction |

The two regime facts are exactly what the compose can deliver: `R.Hlo = U1floor` is the
CALLER's scale (so `log H₋ ≥ 10^30` is a choice), and `λ₊ ≤ λ₋^{9/2}` is the compose's own
tower conjunct, which at `λ₋ ≤ 69.315` gives `λ₊ ≤ 1.922·10^8 ≤ 2·10^8`.

## §B — the constant window, and why it is the whole story

The register is met when the opaque constants satisfy

```
1 ≤ Cg ≤ 2^41        1/2^10 ≤ δ₀        0 < K ≤ 2^20
0 < Ct ≤ 2^20        x₀ ≤ 2^56          Mfl ≤ 2^56        1/2^9 ≤ ε
```

Every one of these is generous EXCEPT the `δ₀` floor.  The binding chain is

* `bfloor`  : `24·Cg/δ₀ ≤ M`   — the spine's `hMδ`;
* `half`    : `0.7·M·A(M) ≤ log H₋/2` — the window gate, so `M ≲ log H₋ / (1.4·2^36)`;
* `anchor`  : `14·λ₊ + log(1/ρ) + 33 ≤ 3.9·10^9`, i.e. `λ₊ ≤ 2.7857·10^8`.  The compose's
  ONLY exported `λ₊`-handle is its `9/2` tower conjunct `λ₊ ≤ λ₋^{9/2}`, so `anchor` is
  PROVABLE only where `λ₋^{9/2} ≤ 2.7857·10^8`, i.e. `λ₋ ≤ 75.28`, hence
  `log H₋ ≤ e^{75.28} ≈ 4.92·10^32 ≤ 2^110` and `M ≤ 2^74` (crude, at `A(M) ≥ 2^36`;
  `2^{66.05}` reading `A(M) = 2^36·(⌊log₂M⌋+1)` exactly).

So the register is witnessable through the exported interface exactly when
`24·Cg/δ₀ ≤ 2^74`.  `ConstantsExposed.b_floor_cert` certifies the road's own value at
`24·Cg/δ₀ ≤ 2^603` (true value `1.68·10^181 = 2^602.02`).  **THE GAP IS 529 BITS** at the
crude read, ~538 at the refined one — the same wall `ConstantsExposed`'s preamble names
("the spine's `hMδ` is short by ~350 bits" against the DRIFT cap), here read at the register.
§5 lands that arithmetic as a theorem: `s15_sel'_bfloor_window` turns any inhabitant of the
register into an upper bound on `24·Cg/δ₀`, unconditionally.

## §C — why the bounds are HYPOTHESES and not `∃`-prefix conjuncts

The conjunct-carry genre (`HloExportMR`) would put the numerals INTO the capstone's `∃`, one
twin per link.  The chains were traced (2026-07-31) and priced:

* `Cg`: EIGHT `∃ C`-links, `typical_density_le` (`TypicalDensity.lean:873`) →
  `card_blockfree_le` (`SieveGlue.lean:183`) → `hsieve_of_engine` (`SieveGlue.lean:438`) →
  `notMemS_window_count_le` (`M4Sieve.lean:468`) → `m4_sieve_block_mass` (`M4Sieve.lean:588`)
  → `m4_door_sieve_mass` (`M4Door.lean:616`) → `m4_door_insert_mass_integral`
  (`M4ParsevalStone.lean:281`) → `parseval_insert_budget_door` (`M4ParsevalStone.lean:341`).
  Links 2–8 are verbatim re-emits; link 1→2 raises to `max C₀ 1` (harmless above `1`).
  `ConstantsExposed.typical_density_le_bounded` is the wired root, so this chain is TWINNABLE.
* `δ₀`, `K`, `ε`: TWENTY distinct `∃`-producers under
  `Salt.Entropy.Chowla.log_chowla_two_budget_head_g` (`SpineFinal.lean:873`), and — the
  blocker — `log_chowla_two_budget_head_g_sq_count_hloCap` (`HloExport.lean:389`), the head
  the road actually consumes, does NOT `obtain` from it: the four heads are INDEPENDENT
  verbatim replays of the same leaf set, so their `ε`/`δ₀`/`K` are four different
  `Classical.choose` terms.  A carry there is not a twin chain but a re-replay of the head
  with twenty bounded leaves.  No wired root exists for any of them
  (`ConstantsExposed`'s reachability caveat is exactly this).

So the numerals ride as hypotheses here, and §7 measures — in the kernel, at the closed
forms — what the carry would find if it were done.

⟦WHAT IS AND IS NOT CLAIMED⟧ `s15_sel'_witness` is a witness at STATED numerals; it does not
claim the road's constants meet them, and `s15_sel'_bfloor_window` says exactly how far they
are from meeting them.  The register is NOT proved empty: `bfloor` only bounds `24·Cg/δ₀`
from above, and no landed statement bounds `δ₀` from above, so the emptiness question stays
open at the interface — what is closed is the WITNESS question, and the answer is a number.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

set_option maxRecDepth 40000
set_option exponentiation.threshold 4000

/-! ## §1 — THE `ρ` FLOOR

`ρ = doorRhoOfDelta (s12DeltaSock δ₀ K) = min 1 (δ₀/(16·K·110525))`.  At `δ₀ ≥ 2^{-10}` and
`K ≤ 2^20` this is `≥ 2^{-51}`, so `log(1/ρ) ≤ 36` — the number every `ρ`-carrying line of
the register spends. -/

/-- **⟦THE `ρ` FLOOR⟧** — `2^{-51} ≤ ρ` at the constant window. -/
theorem s15w_rho_ge {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / 2 ^ 10 ≤ δ₀) (hKb : K ≤ 2 ^ 20) :
    (1 : ℝ) / 2 ^ 51 ≤ doorRhoOfDelta (s12DeltaSock δ₀ K) := by
  rw [doorRhoOfDelta, le_min_iff]
  refine ⟨by norm_num, ?_⟩
  rw [s12DeltaSock_sq hδ hK, div_div, le_div_iff₀ (by positivity)]
  nlinarith [hKb, hδb, hK]

/-- **⟦THE CLEARING CHARGE, NUMERIC⟧** — `log(1/ρ) ≤ 36`. -/
theorem s15w_neglog_rho_le {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / 2 ^ 10 ≤ δ₀) (hKb : K ≤ 2 ^ 20) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 36 := by
  have hge := s15w_rho_ge hδ hK hδb hKb
  have h1 : Real.log ((1 : ℝ) / 2 ^ 51)
      ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) :=
    Real.log_le_log (by norm_num) hge
  have h2 : Real.log ((1 : ℝ) / 2 ^ 51) = -(51 * Real.log 2) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast; ring
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h2] at h1
  linarith

/-! ## §2 — THE WITNESS MODULUS AND ITS TWO-SIDED BOUND -/

/-- **⟦THE WITNESS MODULUS⟧** (`s15WitM`) — the join of the register's three `M`-LOWERS:
`Mfl` (the graded twin's floor), `x₀` (the opaque threshold), and `⌈24·Cg/δ₀⌉₊` (the spine's
`hMδ`).  `max 1` keeps `1 ≤ M` free of every hypothesis. -/
def s15WitM (Cg δ₀ : ℝ) (x₀ Mfl : ℕ) : ℕ :=
  max (max Mfl x₀) (max 1 ⌈24 * Cg / δ₀⌉₊)

theorem s15WitM_one_le (Cg δ₀ : ℝ) (x₀ Mfl : ℕ) : 1 ≤ s15WitM Cg δ₀ x₀ Mfl :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem s15WitM_mfl_le (Cg δ₀ : ℝ) (x₀ Mfl : ℕ) : Mfl ≤ s15WitM Cg δ₀ x₀ Mfl :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem s15WitM_x0_le (Cg δ₀ : ℝ) (x₀ Mfl : ℕ) : x₀ ≤ s15WitM Cg δ₀ x₀ Mfl :=
  le_trans (le_max_right _ _) (le_max_left _ _)

/-- The `hMδ` floor, met by construction. -/
theorem s15WitM_bfloor {Cg δ₀ : ℝ} (x₀ Mfl : ℕ) :
    24 * Cg / δ₀ ≤ ((s15WitM Cg δ₀ x₀ Mfl : ℕ) : ℝ) := by
  refine le_trans (Nat.le_ceil _) ?_
  have h : ⌈24 * Cg / δ₀⌉₊ ≤ s15WitM Cg δ₀ x₀ Mfl :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  exact_mod_cast h

/-- **⟦THE `M`-CEILING AT THE CONSTANT WINDOW⟧** — `M ≤ 2^56`. -/
theorem s15WitM_le {Cg δ₀ : ℝ} {x₀ Mfl : ℕ} (hδ : 0 < δ₀) (hCgb : Cg ≤ 2 ^ 41)
    (hδb : 1 / 2 ^ 10 ≤ δ₀) (hx₀ : x₀ ≤ 2 ^ 56) (hMfl : Mfl ≤ 2 ^ 56) :
    s15WitM Cg δ₀ x₀ Mfl ≤ 2 ^ 56 := by
  have hceil : ⌈24 * Cg / δ₀⌉₊ ≤ 2 ^ 56 := by
    rw [Nat.ceil_le]
    rw [div_le_iff₀ hδ]
    have h1 : ((2 ^ 56 : ℕ) : ℝ) = 2 ^ 56 := by push_cast; ring
    rw [h1]
    nlinarith [hCgb, hδb]
  simp only [s15WitM, max_le_iff]
  exact ⟨⟨hMfl, hx₀⟩, by norm_num, hceil⟩

/-- `Nat.log 2 M ≤ 56` under the `M`-ceiling. -/
theorem s15w_natlog_le {M : ℕ} (hM : M ≤ 2 ^ 56) : Nat.log 2 M ≤ 56 := by
  have h := Nat.log_mono_right (b := 2) hM
  rwa [Nat.log_pow (by norm_num)] at h

/-- `A(M) ≤ 2^42` under the `M`-ceiling. -/
theorem s15w_Adoor_le {M : ℕ} (hM : M ≤ 2 ^ 56) : Adoor M ≤ 2 ^ 42 := by
  have h := s15w_natlog_le hM
  calc Adoor M = 2 ^ 36 * (Nat.log 2 M + 1) := rfl
    _ ≤ 2 ^ 36 * 64 := by omega
    _ = 2 ^ 42 := by norm_num

/-- `doorRowFloor M = M·A(M) ≤ 2^98` under the `M`-ceiling. -/
theorem s15w_doorRowFloor_le {M : ℕ} (hM : M ≤ 2 ^ 56) : doorRowFloor M ≤ 2 ^ 98 := by
  have hA := s15w_Adoor_le hM
  calc doorRowFloor M = M * Adoor M := rfl
    _ ≤ 2 ^ 56 * 2 ^ 42 := Nat.mul_le_mul hM hA
    _ = 2 ^ 98 := by norm_num

/-- **⟦THE BLOCK EXPONENT AT THE `M`-CEILING⟧** — `s13BlockExp M ≤ 2^342`. -/
theorem s15w_blockExp_le {M : ℕ} (hM : M ≤ 2 ^ 56) : s13BlockExp M ≤ 2 ^ 342 := by
  have hlg := s15w_natlog_le hM
  have hA := s15w_Adoor_le hM
  have hG : 3072 * M ≤ 2 ^ 68 := by
    calc 3072 * M ≤ 3072 * 2 ^ 56 := Nat.mul_le_mul_left _ hM
      _ ≤ 2 ^ 68 := by norm_num
  have hprod : Adoor M * (3072 * M) * M ≤ 2 ^ 166 := by
    calc Adoor M * (3072 * M) * M ≤ 2 ^ 42 * 2 ^ 68 * 2 ^ 56 :=
          Nat.mul_le_mul (Nat.mul_le_mul hA hG) hM
      _ = 2 ^ 166 := by norm_num
  have hsq : (Adoor M * (3072 * M) * M) ^ 2 ≤ 2 ^ 332 := by
    calc (Adoor M * (3072 * M) * M) ^ 2 ≤ (2 ^ 166 : ℕ) ^ 2 :=
          Nat.pow_le_pow_left hprod 2
      _ = 2 ^ 332 := by norm_num
  have hmain : 400 * (Adoor M * (3072 * M) * M) ^ 2 ≤ 2 ^ 341 := by
    calc 400 * (Adoor M * (3072 * M) * M) ^ 2 ≤ 400 * 2 ^ 332 :=
          Nat.mul_le_mul_left _ hsq
      _ ≤ 2 ^ 341 := by norm_num
  have : s13BlockExp M = 14427 + (64 + 8 * (Nat.log 2 M + 1))
      + 400 * (Adoor M * (3072 * M) * M) ^ 2 := rfl
  omega

/-! ## §3 — THE REGIME FLOOR

`log H₋ ≥ 10^30` puts `H₊ ≥ H₋ ≥ 2^400`, which is all ⟦`M`-UPPER 1⟧ (`blk`) needs on the
window side. -/

/-- `2^400 ≤ H₊` from `log H₋ ≥ 10^30`. -/
theorem s15w_Hhi_ge {R : ChowlaRegime} (hlo : (10 : ℝ) ^ 30 ≤ Real.log ((R.Hlo : ℕ) : ℝ)) :
    (2 : ℕ) ^ 400 ≤ R.Hhi := by
  have hpos : (0 : ℝ) < ((R.Hlo : ℕ) : ℝ) := by
    have := R.hHlo_floor
    have : (0 : ℕ) < R.Hlo := by omega
    exact_mod_cast this
  have hexp : Real.exp 1000 ≤ ((R.Hlo : ℕ) : ℝ) := by
    have h1 : (1000 : ℝ) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
      refine le_trans ?_ hlo
      norm_num
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log hpos] at h2
  have h2e : (2 : ℝ) ≤ Real.exp (5 / 2) := by
    have := Real.add_one_le_exp (5 / 2 : ℝ)
    linarith
  have hpow : (2 : ℝ) ^ (400 : ℕ) ≤ Real.exp 1000 := by
    calc (2 : ℝ) ^ (400 : ℕ) ≤ (Real.exp (5 / 2)) ^ (400 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) h2e 400
      _ = Real.exp 1000 := by rw [← Real.exp_nat_mul]; norm_num
  have hlo' : ((2 : ℕ) ^ 400 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by
    push_cast
    linarith
  have hnat : (2 : ℕ) ^ 400 ≤ R.Hlo := by exact_mod_cast hlo'
  exact le_trans hnat R.hHlohi

/-- **⟦`M`-UPPER 1's WINDOW SIDE⟧** — `2^341 ≤ ⌊ε²·H₊⌋₊` at `ε ≥ 2^{-9}`. -/
theorem s15w_blk_floor {R : ChowlaRegime} (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : (10 : ℝ) ^ 30 ≤ Real.log ((R.Hlo : ℕ) : ℝ)) :
    (2 : ℕ) ^ 341 ≤ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by
  have hHhi := s15w_Hhi_ge hlo
  have hHq : ((2 : ℕ) ^ 400 : ℚ) ≤ (R.Hhi : ℚ) := by exact_mod_cast hHhi
  have hHq' : (2 : ℚ) ^ 400 ≤ (R.Hhi : ℚ) := by push_cast at hHq; linarith
  have hepspos : (0 : ℚ) < R.eps := R.heps
  have hsq : (1 : ℚ) / 2 ^ 18 ≤ R.eps ^ 2 := by nlinarith [heps, hepspos]
  refine Nat.le_floor ?_
  have hstep : ((2 : ℕ) ^ 341 : ℚ) ≤ (1 / 2 ^ 18) * 2 ^ 400 := by
    push_cast
    norm_num
  refine le_trans hstep ?_
  exact mul_le_mul hsq hHq' (by positivity) (sq_nonneg _)

/-! ## §4 — ⟦THE WITNESS⟧ -/

set_option maxHeartbeats 800000 in
-- eleven register lines discharged in one `refine`, each an `nlinarith`/`linarith` over casts
-- of `2^342`-sized numerals; the default budget is exhausted by `gP1` and `lvl`
/-- **⟦THE `M`-SELECTION REGISTER, WITNESSED⟧** (`s15_sel'_witness`).

Every one of `S15Sel'`'s eleven lines, discharged at `M = s15WitM Cg δ₀ x₀ Mfl` against the
stated numeric window for the opaque constants and two numeric facts about the regime:

* `hlo` — `log H₋ ≥ 10^30`.  At the compose this is a CHOICE: `R.Hlo = U1floor`.
* `hhi` — `λ₊ ≤ 2·10^8`.  At the compose this is the tower conjunct read at `λ₋ ≈ 69.08`.

⟦THE LEDGER⟧ `hM`/`mfloor`/`x0M`/`bfloor` by construction of `s15WitM`; `rho`/`anchor` off
§1's `log(1/ρ) ≤ 36`; `gRows`/`gP1`/`lvl` off `A(M) ≥ 2^36 = 6.87·10^10` against
`242·λ₊ ≤ 4.84·10^10`; `half` off `doorRowFloor M ≤ 2^98 = 3.17·10^29` against
`log H₋/2 ≥ 5·10^29`; `blk` off §3.

⟦THE ONE BINDING HYPOTHESIS⟧ `1/2^10 ≤ δ₀`.  See §5. -/
theorem s15_sel'_witness {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    (hCgb : Cg ≤ 2 ^ 41)
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 10 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 20)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 20)
    (hx₀ : x₀ ≤ 2 ^ 56) (hMfl : Mfl ≤ 2 ^ 56)
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : (10 : ℝ) ^ 30 ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * 10 ^ 8) :
    S15Sel' Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (s15WitM Cg δ₀ x₀ Mfl) := by
  set M : ℕ := s15WitM Cg δ₀ x₀ Mfl with hMdef
  have hM1 : 1 ≤ M := s15WitM_one_le _ _ _ _
  have hMcap : M ≤ 2 ^ 56 := s15WitM_le hδ hCgb hδb hx₀ hMfl
  -- ⟦the anchor's numerals⟧
  have hρlog : -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 36 :=
    s15w_neglog_rho_le hδ hK hδb hKb
  have hρpos : 0 < doorRhoOfDelta (s12DeltaSock δ₀ K) :=
    doorRhoOfDelta_pos (s12DeltaSock_pos hδ hK).ne'
  have hinv : Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ K))
      = -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by
    rw [one_div, Real.log_inv]
  -- ⟦the door anchor⟧
  have hAd : (68719476736 : ℝ) ≤ ((Adoor M : ℕ) : ℝ) := by
    have h := Adoor_ge M
    have : ((2 ^ 36 : ℕ) : ℝ) ≤ ((Adoor M : ℕ) : ℝ) := by exact_mod_cast h
    calc (68719476736 : ℝ) = ((2 ^ 36 : ℕ) : ℝ) := by push_cast; norm_num
      _ ≤ ((Adoor M : ℕ) : ℝ) := this
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- ⟦the row floor, in ℝ⟧
  have hdrf : ((doorRowFloor M : ℕ) : ℝ) ≤ 2 ^ 98 := by
    have h := s15w_doorRowFloor_le hMcap
    have : ((doorRowFloor M : ℕ) : ℝ) ≤ ((2 ^ 98 : ℕ) : ℝ) := by exact_mod_cast h
    calc ((doorRowFloor M : ℕ) : ℝ) ≤ ((2 ^ 98 : ℕ) : ℝ) := this
      _ = 2 ^ 98 := by push_cast; ring
  have hdrf1 : (1 : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := by
    have h : 1 ≤ doorRowFloor M := le_trans (by norm_num) (s15_doorRowFloor_ge hM1)
    exact_mod_cast h
  refine
    { hM := hM1
      mfloor := s15WitM_mfl_le _ _ _ _
      bfloor := s15WitM_bfloor _ _
      x0M := s15WitM_x0_le _ _ _ _
      gRows := ?_
      blk := ?_
      half := ?_
      rho := ?_
      anchor := ?_
      gP1 := ?_
      lvl := ?_ }
  · -- ⟦`M`-LOWER 2⟧ `242·λ₊ ≤ A(M)`
    linarith [hhi, hAd]
  · -- ⟦`M`-UPPER 1⟧ the block ceiling
    have hbe : ((s13BlockExp M : ℕ) : ℝ) ≤ 2 ^ 342 := by
      have h := s15w_blockExp_le hMcap
      have h' : ((s13BlockExp M : ℕ) : ℝ) ≤ ((2 ^ 342 : ℕ) : ℝ) := by exact_mod_cast h
      calc ((s13BlockExp M : ℕ) : ℝ) ≤ ((2 ^ 342 : ℕ) : ℝ) := h'
        _ = 2 ^ 342 := by push_cast; ring
    have hfl := s15w_blk_floor heps hlo
    have hfl' : (2 : ℝ) ^ 341 ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
      have h : ((2 ^ 341 : ℕ) : ℝ) ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hfl
      calc (2 : ℝ) ^ 341 = ((2 ^ 341 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ _ := h
    have hgap : (2 : ℝ) ^ 342 + 1 + 18 * (2 * 10 ^ 8) ≤ 4 * (2 : ℝ) ^ 341 := by
      norm_num
    linarith [hbe, hfl', hhi, hgap]
  · -- ⟦`M`-UPPER 2⟧ the window gate
    rw [hinv]
    have h1 : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ) ≤ (7 / 10 : ℝ) * 2 ^ 98 := by
      linarith [hdrf]
    have h2 : (7 / 10 : ℝ) * 2 ^ 98 + 3 * 36 ≤ (10 : ℝ) ^ 30 / 2 := by norm_num
    linarith [h1, h2, hρlog, hlo]
  · -- the clearing charge
    linarith [hρlog]
  · -- the `ρ`-frame's anchor
    rw [hinv]
    linarith [hhi, hρlog]
  · -- the `𝒯`-leg budget
    have hCtl : Real.log Ct ≤ 20 * Real.log 2 := by
      have h := Real.log_le_log hCt hCtb
      rwa [Real.log_pow] at h
    have hρ' : -(36 : ℝ) ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by
      linarith [hρlog]
    nlinarith [hAd, hlog2lo, hhi, hCtl, hρ', hlog2hi]
  · -- the `level1` budget
    have hQ : Real.log (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ≤ 68 := by
      rw [s15_log_calQK_one M]
      have hpos : (0 : ℝ) < ((doorRowFloor M : ℕ) : ℝ) * Real.log 2 := by
        have : (0 : ℝ) < Real.log 2 := by linarith
        nlinarith [hdrf1]
      have hle : ((doorRowFloor M : ℕ) : ℝ) * Real.log 2 ≤ (2 : ℝ) ^ 98 := by
        nlinarith [hdrf, hdrf1, hlog2hi]
      have h := Real.log_le_log hpos hle
      have h98 : Real.log ((2 : ℝ) ^ 98) = 98 * Real.log 2 := by
        rw [Real.log_pow]; push_cast; ring
      rw [h98] at h
      linarith [h, hlog2hi]
    have hρ' : -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 36 := hρlog
    nlinarith [hAd, hlog2lo, hhi, hQ, hρ']

/-! ## §5 — ⟦THE WINDOW⟧ WHAT THE REGISTER COSTS THE SPINE'S `b`-FLOOR

Nothing above is conditional on the road's constants MEETING the window of §4.  This section
is the converse read, and it is unconditional: any inhabitant of `S15Sel'` at all caps the
spine's `hMδ` floor `24·Cg/δ₀` by the window scale `log H₋`, because `half` caps `M` and
`bfloor` is a floor on the same `M`.  Sharpened by `anchor` (which through the compose's
`9/2` tower caps `λ₋`), this is the exact arithmetic the road must beat. -/

/-- **⟦THE REGISTER'S `b`-FLOOR CEILING⟧** (`s15_sel'_bfloor_window`) — every inhabitant of
the sharp register caps the spine's `hMδ` floor by the window:

`24·Cg/δ₀ ≤ M ≤ log H₋ / (1.4·2^36)`.

`half` (⟦`M`-UPPER 2⟧) gives the right inequality through `doorRowFloor M = M·A(M) ≥ M·2^36`
and `log(1/ρ) ≥ 0`; `bfloor` (⟦`M`-LOWER 1⟧) gives the left.  No constant bound is assumed:
this is a statement ABOUT the register, true wherever it is true. -/
theorem s15_sel'_bfloor_window {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hsel : S15Sel' Cg δ₀ Ct ρ x₀ Mfl R M) :
    24 * Cg / δ₀ ≤ Real.log ((R.Hlo : ℕ) : ℝ) / (14 / 10 * 2 ^ 36) := by
  have hlρ : (0 : ℝ) ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]
    have : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
    linarith
  have hdrf : ((M : ℕ) : ℝ) * 2 ^ 36 ≤ ((doorRowFloor M : ℕ) : ℝ) := by
    have h : M * 2 ^ 36 ≤ doorRowFloor M := by
      calc M * 2 ^ 36 ≤ M * Adoor M := Nat.mul_le_mul_left _ (Adoor_ge M)
        _ = doorRowFloor M := rfl
    have h' : ((M * 2 ^ 36 : ℕ) : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := by exact_mod_cast h
    calc ((M : ℕ) : ℝ) * 2 ^ 36 = ((M * 2 ^ 36 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := h'
  have hhalf := hsel.half
  have hM : ((M : ℕ) : ℝ) ≤ Real.log ((R.Hlo : ℕ) : ℝ) / (14 / 10 * 2 ^ 36) := by
    rw [le_div_iff₀ (by norm_num)]
    linarith [hhalf, hdrf, hlρ]
  exact le_trans hsel.bfloor hM

/-- **⟦THE WINDOW, AT THE TOWER-CERTIFIABLE `λ₋`⟧** (`s15_sel'_bfloor_window_num`) — the same
read with the window scale pinned at a numeral.

`log H₋ ≤ 2^110` is `λ₋ ≤ 76.25`, which is IMPLIED by the only `λ₋`-cap the compose can
certify: `anchor` reads `λ₊ ≤ 2.7857·10^8`, and the compose's sole exported `λ₊`-handle is
its `9/2` tower conjunct `λ₊ ≤ λ₋^{9/2}`, so `anchor` is provable only where
`λ₋^{9/2} ≤ 2.7857·10^8`, i.e. `λ₋ ≤ 75.29 < 76.25`.  There the register forces

`24·Cg/δ₀ ≤ 2^74`.

⟦THE GAP⟧ `ConstantsExposed.b_floor_cert` certifies the road's own floor at `24·Cg/δ₀ ≤ 2^603`
(true value `1.68·10^181 = 2^602.02`).  **529 BITS** against the certificate, 528 against the
true value.  That is the whole distance between
`logChowla2_conditional_sharp` and a witness through the exported interface — and it is the
same wall `ConstantsExposed`'s preamble names against the DRIFT cap, read here at the
register.  (It is NOT a proof that the register is empty: `bfloor` bounds `24·Cg/δ₀` from
ABOVE, and no landed statement bounds `δ₀` from above, so a road with a larger `δ₀` — or a
sharper tower export than `9/2` — walks straight through.) -/
theorem s15_sel'_bfloor_window_num {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hsel : S15Sel' Cg δ₀ Ct ρ x₀ Mfl R M)
    (hw : Real.log ((R.Hlo : ℕ) : ℝ) ≤ 2 ^ 110) :
    24 * Cg / δ₀ ≤ 2 ^ 74 := by
  refine le_trans (s15_sel'_bfloor_window hρ0 hρ1 hsel) ?_
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [hw]

/-! ## §6 — ⟦THE COMPOSE⟧ THE SHARP CONDITIONAL, REGISTER DISCHARGED -/

/-- **⟦THE WITNESS SCALE⟧** (`s15WitFloor`) — `⌈e^{10^30}⌉₊`, the `U1floor` the compose is
fired at.  `log s15WitFloor ∈ [10^30, 10^30 + 1]`, so `λ₋ ∈ [68.6, 69.32]`: above the `50`
floor the spine demands, below the `75.29` the `anchor` line allows through the `9/2`
tower. -/
def s15WitFloor : ℕ := ⌈Real.exp (10 ^ 30)⌉₊

theorem s15WitFloor_log_ge : (10 : ℝ) ^ 30 ≤ Real.log ((s15WitFloor : ℕ) : ℝ) := by
  have h : Real.exp ((10 : ℝ) ^ 30) ≤ ((s15WitFloor : ℕ) : ℝ) := Nat.le_ceil _
  have h2 := Real.log_le_log (Real.exp_pos _) h
  rwa [Real.log_exp] at h2

theorem s15WitFloor_log_le : Real.log ((s15WitFloor : ℕ) : ℝ) ≤ (10 : ℝ) ^ 30 + 1 := by
  have hc : ((s15WitFloor : ℕ) : ℝ) < Real.exp ((10 : ℝ) ^ 30) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hb : Real.exp ((10 : ℝ) ^ 30) + 1 ≤ 2 * Real.exp ((10 : ℝ) ^ 30) := by
    have : (1 : ℝ) ≤ Real.exp ((10 : ℝ) ^ 30) := Real.one_le_exp (by norm_num)
    linarith
  have hle : ((s15WitFloor : ℕ) : ℝ) ≤ 2 * Real.exp ((10 : ℝ) ^ 30) := by linarith
  have hpos : (0 : ℝ) < ((s15WitFloor : ℕ) : ℝ) := by
    have h : Real.exp ((10 : ℝ) ^ 30) ≤ ((s15WitFloor : ℕ) : ℝ) := Nat.le_ceil _
    have := Real.exp_pos ((10 : ℝ) ^ 30)
    linarith
  have h1 := Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- `2^99 ≤ e^{10^30}` — the crude step that puts `λ₋` above `50`. -/
theorem s15WitFloor_loglog_ge : (50 : ℝ) ≤ Real.log (Real.log ((s15WitFloor : ℕ) : ℝ)) := by
  have hlo := s15WitFloor_log_ge
  have hstep : (2 : ℝ) ^ (99 : ℕ) ≤ (10 : ℝ) ^ 30 := by norm_num
  have h1 : (2 : ℝ) ^ (99 : ℕ) ≤ Real.log ((s15WitFloor : ℕ) : ℝ) := le_trans hstep hlo
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  push_cast at h2
  linarith

/-- `λ₋ ≤ 69.315` at the witness scale. -/
theorem s15WitFloor_loglog_le :
    Real.log (Real.log ((s15WitFloor : ℕ) : ℝ)) ≤ 69315 / 1000 := by
  have hhi := s15WitFloor_log_le
  have hstep : (10 : ℝ) ^ 30 + 1 ≤ (2 : ℝ) ^ (100 : ℕ) := by norm_num
  have hpos : (0 : ℝ) < Real.log ((s15WitFloor : ℕ) : ℝ) := by
    have := s15WitFloor_log_ge
    have : (0 : ℝ) < (10 : ℝ) ^ 30 := by norm_num
    linarith [s15WitFloor_log_ge]
  have h1 : Real.log ((s15WitFloor : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 : ℕ) := by linarith
  have h2 := Real.log_le_log hpos h1
  rw [Real.log_pow] at h2
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  push_cast at h2
  linarith

/-- **⟦THE TOWER, AT THE WITNESS SCALE⟧** — `λ₋ ≤ 69.315 ⟹ λ₋^{9/2} ≤ 2·10^8`, the `λ₊`-cap
every `λ₊`-carrying line of the register is discharged against. -/
theorem s15w_tower_bound {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 69315 / 1000) :
    x ^ ((9 : ℝ) / 2) ≤ 2 * 10 ^ 8 := by
  have hpow : x ^ ((9 : ℝ) / 2) ≤ (69315 / 1000 : ℝ) ^ ((9 : ℝ) / 2) :=
    Real.rpow_le_rpow hx0 hx (by norm_num)
  have hnn : (0 : ℝ) ≤ (69315 / 1000 : ℝ) ^ ((9 : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hsq : ((69315 / 1000 : ℝ) ^ ((9 : ℝ) / 2)) ^ (2 : ℕ) = (69315 / 1000 : ℝ) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast ((69315 / 1000 : ℝ) ^ ((9 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (69315 / 1000 : ℝ) 9]
    norm_num
  have hb : (69315 / 1000 : ℝ) ^ ((9 : ℝ) / 2) ≤ 2 * 10 ^ 8 := by
    nlinarith [hsq, hnn]
  linarith

/-- `arcFloor36 = 10^138 ≤ s15WitFloor`. -/
theorem s15WitFloor_arc : arcFloor36 ≤ s15WitFloor := by
  have h2e : (2 : ℝ) ≤ Real.exp (5 / 2) := by
    have := Real.add_one_le_exp (5 / 2 : ℝ)
    linarith
  have hpow : (2 : ℝ) ^ (1000 : ℕ) ≤ Real.exp 2500 := by
    calc (2 : ℝ) ^ (1000 : ℕ) ≤ (Real.exp (5 / 2)) ^ (1000 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) h2e 1000
      _ = Real.exp 2500 := by rw [← Real.exp_nat_mul]; norm_num
  have hmono : Real.exp 2500 ≤ Real.exp ((10 : ℝ) ^ 30) :=
    Real.exp_le_exp.mpr (by norm_num)
  have h10 : ((arcFloor36 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (1000 : ℕ) := by
    rw [arcFloor36]
    push_cast
    norm_num
  have hfin : ((arcFloor36 : ℕ) : ℝ) ≤ ((s15WitFloor : ℕ) : ℝ) :=
    le_trans (le_trans (le_trans h10 hpow) hmono) (Nat.le_ceil _)
  exact_mod_cast hfin

/-- `loglogFloor50 = ⌈e^{e^{50}}⌉₊ ≤ s15WitFloor`, since `e^{50} ≤ 10^30`. -/
theorem s15WitFloor_ll : loglogFloor50 ≤ s15WitFloor := by
  have h1 : Real.exp 1 ≤ 2.72 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h50 : Real.exp 50 ≤ (10 : ℝ) ^ 30 := by
    have he : Real.exp 50 = Real.exp 1 ^ (50 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc Real.exp 1 ^ (50 : ℕ) ≤ (2.72 : ℝ) ^ (50 : ℕ) :=
          pow_le_pow_left₀ (Real.exp_pos 1).le h1 50
      _ ≤ (10 : ℝ) ^ 30 := by norm_num
  have hmono : Real.exp (Real.exp 50) ≤ Real.exp ((10 : ℝ) ^ 30) :=
    Real.exp_le_exp.mpr h50
  rw [loglogFloor50, s15WitFloor]
  exact Nat.ceil_le_ceil hmono

set_option maxHeartbeats 800000 in
-- the `∃`-block re-elaborates the capstone's instantiated prefix, as in `S15Compose` §9
/-- **⟦THE SHARP CONDITIONAL, REGISTER DISCHARGED⟧**
(`logChowla2_conditional_sharp_nonvacuous`).

`S15Compose.logChowla2_conditional_sharp` fired at `U1floor := s15WitFloor` and at
`M := s15WitM Cg δ₀ x₀ Mfl`, with `S15Sel'` DISCHARGED by §4's witness.  What remains inside
the `∃`-block is a single implication whose antecedent is a list of NUMERALS about the
capstone's opaque constants — the conjunct-carry the twinning campaign would deliver as
`∃`-prefix conjuncts, here carried as one honest hypothesis apiece — and whose consequent
names `S15CrossingBound` as the ONLY surviving analytic hypothesis.

⟦WHAT MOVED⟧ `logChowla2_conditional_sharp` carried TWO objects (`S15Sel'` + `S15CrossingBound`)
and no witness.  This carries ONE object plus a numeric window, and exhibits `(R, M)`.

⟦WHAT DID NOT⟧ nothing claims the road's constants sit in the window; §5 measures the
distance (529 bits at `b_floor_cert`). -/
theorem logChowla2_conditional_sharp_nonvacuous :
    ∃ (ε : ℚ) (Cg K δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      ((1 : ℚ) / 2 ^ 9 ≤ ε → Cg ≤ 2 ^ 41 → 1 / 2 ^ 10 ≤ δ₀ → K ≤ 2 ^ 20 → Ct ≤ 2 ^ 20 →
        x₀ ≤ 2 ^ 56 → Mfl ≤ 2 ^ 56 → Hcap ≤ s15WitFloor →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel' Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R M ∧
          (S15CrossingBound R M → ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl1, hbody⟩ :=
    logChowla2_conditional_sharp
  refine ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl1, ?_⟩
  intro hεb hCgb hδb hKb hCtb hx₀b hMflb hHcap g
  have hU : max Hcap (max arcFloor36 loglogFloor50) ≤ s15WitFloor := by
    have h1 := s15WitFloor_arc
    have h2 := s15WitFloor_ll
    omega
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ := hbody s15WitFloor g hU
  have hlo : (10 : ℝ) ^ 30 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact s15WitFloor_log_ge
  have h50 : (50 : ℝ) ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := by
    rw [hHlo]; exact s15WitFloor_loglog_ge
  have hlam : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 69315 / 1000 := by
    rw [hHlo]; exact s15WitFloor_loglog_le
  have hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * 10 ^ 8 := by
    refine le_trans (hRtow h50) ?_
    exact s15w_tower_bound (by linarith) hlam
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by rw [hReps]; exact hεb
  refine ⟨R, s15WitM Cg δ₀ x₀ Mfl, hReps, hHlo, hRg, ?_, ?_⟩
  · exact s15_sel'_witness hCgb hδ₀ hδb hK hKb hCt hCtb hx₀b hMflb heps hlo hhi
  · exact hfire (s15WitM Cg δ₀ x₀ Mfl)
      (s15_sel'_witness hCgb hδ₀ hδb hK hKb hCt hCtb hx₀b hMflb heps hlo hhi)

/-! ## §7 — ⟦THE WALL, IN THE KERNEL⟧ THE REGISTER AT THE ROAD'S CLOSED FORMS

§5 caps `24·Cg/δ₀` from ABOVE at any register inhabitant.  `ConstantsExposed` bounds the
road's own `Cg` from above and its `δ₀` from below.  Those two are the same direction, so
they do not meet.  This section supplies the missing direction — `Cg` from BELOW and `δ₀`
from ABOVE, at the closed forms — and the two caps then CROSS: the register is EMPTY at the
road's constants inside the tower-certifiable window.

⚠ **THE REACHABILITY CAVEAT APPLIES** (`ConstantsExposed`'s preamble, verbatim in force):
`CgExpr` and `delta0Expr` are the closed forms of the `refine` witnesses, not the opaque
constants the landed `∃`s deliver.  The identification is a proof-term reading.  What is a
kernel fact is the arithmetic below and its consequence FOR THOSE CLOSED FORMS. -/

/-- `2·10^11 ≤ exp(19/log 2)` — the `Cg` lower bound's engine, off `S15Compose.s15_exp27`. -/
theorem s15w_CgExpr_ge : (832240189441 : ℝ) ≤ CgExpr := by
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h27 : (27 : ℝ) ≤ 19 / Real.log 2 := by
    rw [le_div_iff₀ hpos]
    linarith
  have hexp : Real.exp 27 ≤ Real.exp (19 / Real.log 2) := Real.exp_le_exp.mpr h27
  have h := s15_exp27
  rw [CgExpr_eq]
  linarith

/-- `6.5 ≤ C` (the circle-method constant `1 + 8·log 2`). -/
theorem s15w_CcmExpr_ge : (65 / 10 : ℝ) ≤ CcmExpr := by
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [CcmExpr, h4]
  linarith

/-- `6·10^16 ≤ K_lcm = exp(4π²)`. -/
theorem s15w_KlcmExpr_ge : (6 * 10 ^ 16 : ℝ) ≤ KlcmExpr := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have h39 : (39 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [hpi, hpi0]
  have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : (6 * 10 ^ 16 : ℝ) ≤ Real.exp 39 := by
    have hid : Real.exp 39 = Real.exp 1 ^ (39 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hid]
    calc (6 * 10 ^ 16 : ℝ) ≤ (2.7 : ℝ) ^ (39 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (39 : ℕ) := pow_le_pow_left₀ (by norm_num) he.le 39
  rw [KlcmExpr_eq]
  exact le_trans hpow (Real.exp_le_exp.mpr h39)

/-- `2.56·10^10 ≤ C₁` at every `H₁` — the `CL` arm alone (`CS ≥ 0`). -/
theorem s15w_C1Expr_ge (H₁ : ℕ) : (25600051200 : ℝ) ≤ C1Expr H₁ := by
  have h := CSExpr_nonneg H₁
  rw [C1Expr, CLExpr_eq]
  linarith

/-- `1.2·10^66 ≤ K` at every `H₁` — the crude read (`K_lcm` and `CL` only; `CS`'s `2^100`
is thrown away, which is why this is 320 bits short of the true `1.04·10^162`). -/
theorem s15w_KExpr_ge (H₁ : ℕ) : (12 * 10 ^ 65 : ℝ) ≤ KExpr H₁ := by
  have hK := s15w_KlcmExpr_ge
  have hC := s15w_C1Expr_ge H₁
  have hCpos := C1Expr_pos H₁
  have hsq : (25600051200 : ℝ) ^ 2 ≤ (C1Expr H₁) ^ 2 := by nlinarith [hC, hCpos]
  rw [KExpr_eq]
  nlinarith [hK, hsq, KlcmExpr_pos, sq_nonneg (C1Expr H₁)]

/-- **⟦THE ROAD'S `b`-FLOOR, FROM BELOW⟧** (`s15w_bfloor_expr_ge`) — at the closed forms,
`2^282 ≤ 24·Cg/δ₀`.  (The true value is `2^602.02`; this crude read keeps only `K_lcm` and
`CL`, so it is 320 bits conservative — and still 208 bits above §5's ceiling.) -/
theorem s15w_bfloor_expr_ge (H₁ : ℕ) : (2 : ℝ) ^ 282 ≤ 24 * CgExpr / delta0Expr H₁ := by
  have hCg := s15w_CgExpr_ge
  have hCcm := s15w_CcmExpr_ge
  have hK := s15w_KExpr_ge H₁
  have hCcmpos := CcmExpr_pos
  have hKpos := KExpr_pos H₁
  rw [delta0Expr_eq, one_div, div_inv_eq_mul]
  have hCK : (65 / 10 : ℝ) * (12 * 10 ^ 65) ≤ CcmExpr * KExpr H₁ := by
    nlinarith [hCcm, hK, hCcmpos, hKpos]
  have hstep : (2 : ℝ) ^ 282
      ≤ 24 * (832240189441 : ℝ) * (64000 * ((65 / 10 : ℝ) * (12 * 10 ^ 65))) := by
    norm_num
  refine le_trans hstep ?_
  have hCgpos : (0 : ℝ) < CgExpr := CgExpr_pos
  nlinarith [hCg, hCK, hCgpos, hCcmpos, hKpos]

/-- **⟦THE REGISTER IS EMPTY AT THE ROAD'S CLOSED FORMS⟧**
(`s15_sel'_empty_at_closed_forms`).

`S15Sel'` instantiated at `Cg := CgExpr`, `δ₀ := delta0Expr H₁` and at ANY regime whose
window satisfies `log H₋ ≤ 2^110` (which is `λ₋ ≤ 76.25`, and every `λ₋` at which the
compose's `9/2` tower can certify the register's own `anchor` line satisfies `λ₋ ≤ 75.28`)
is CONTRADICTORY: §5 caps `24·Cg/δ₀ ≤ 2^74`, §7 floors it at `2^282`.

⟦WHAT THIS IS⟧ the exact shape of the wall between `logChowla2_conditional_sharp` and a
witness.  It is NOT a refutation of the conditional (which is true and kernel-checked), and
NOT a proof that the road's opaque `δ₀` equals `delta0Expr` (the reachability caveat).  It is
the statement that the register and the road's constants cannot both be right inside the
window the exported tower certifies — so the witness needs either a bigger `δ₀`, or a tower
export sharper than `9/2` (at `λ₋ ≈ 449`, where `half` admits `M ≈ 2^602`, `anchor` needs
`λ₊ ≤ λ₋^{3.18}`, and the width law already gives `λ₊ ≥ λ₋³` — the two are 0.18 of an
exponent apart). -/
theorem s15_sel'_empty_at_closed_forms {Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    {M H₁ : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hw : Real.log ((R.Hlo : ℕ) : ℝ) ≤ 2 ^ 110)
    (hsel : S15Sel' CgExpr (delta0Expr H₁) Ct ρ x₀ Mfl R M) : False := by
  have hup := s15_sel'_bfloor_window_num hρ0 hρ1 hsel hw
  have hdn := s15w_bfloor_expr_ge (H₁ := H₁)
  have hgap : (2 : ℝ) ^ 74 < (2 : ℝ) ^ 282 := by norm_num
  linarith

/-! ## §8 — ⟦SEL-RECUT⟧ THE RE-CUT REGISTER, WITNESSED

PURELY ADDITIVE: §1–§7 are untouched.

`S15Compose` §10's `S15Sel''` states `x0M` and `anchor` at their suppliers' own forms.  This
section witnesses IT, and both restorations pay:

| slot | §4 (at `S15Sel'`) | here (at `S15Sel''`) |
|---|---|---|
| `λ₋` | `≈ 69.08` (`log H₋ ≥ 10^30`) | `≈ 277.26` (`log H₋ ≥ 2^400`) |
| `λ₊` | `≤ 2·10^8` | `≤ 9.87·10^10` |
| `M` | `≤ 2^56` | `= 2^355` |
| `Mfl` | `≤ 2^56` | `≤ 2^355` |
| `24·Cg/δ₀` | `≤ 2^56` (from `Cg ≤ 2^41`, `δ₀ ≥ 2^{-10}`) | `≤ 2^355`, stated directly |
| `x₀` | `≤ 2^56` | `≤ e^{e^{275}}` |

⟦WHY THE CEILING MOVES⟧ §4's `M`-ceiling was forced by the WEAK anchor: `λ₊ ≤ 2.7857·10^8`
against the compose's only `λ₊`-handle `λ₊ ≤ λ₋^{9/2}` capped `λ₋ ≤ 75.28`, hence
`log H₋ ≤ e^{75.28}` and (through `half`) `M ≤ 2^{66}`.  Restored, the cap reads
`λ₋^{9/2} ≤ 2.7857·10^8·(log₂M + 1)` and GROWS with `M`; `half` is the only remaining
`M`-upper, and the two meet at `λ₋ ≈ 277.7`, `M ≈ 2^{356}`.  `2^{400} ≤ log H₋` sits just
inside that.

⟦THE `x₀` WINDOW, AND WHY IT IS A HYPOTHESIS⟧ `S13BandGate'.x0_le` asks `x₀ ≤ 2^{doorRowFloor
M}`, i.e. `log₂ x₀ ≤ 356·2^{391}`, i.e. `x₀ ≤ e^{e^{276.53}}` at this working point (the
extremal read; `275` below keeps the discharge on `log 2` alone).  That is 175 DOUBLE-LOG
units above the analytic chain's own pinned floor `exp (exp 100)`
(`mmu1Chi_rate_of_pinned`'s `filter_upwards`).  It is nevertheless carried as the NAMED
hypothesis `hx0win` and is NOT discharged, because the threshold `x₀` the chain produces is
Siegel-INEFFECTIVE (`PortClose`'s `K`: the port's one ineffective constant).  No theorem can
say the window is met without an effective Siegel–Landau–Page input; that is a research-tier
wall of the field, not of this file.  ⚠ **The register itself carries no such cap** — the
hypothesis lives only in this witness.

⟦THE `b`-FLOOR READ⟧ §5's ceiling on `24·Cg/δ₀` moves from `2^{74}` to `2^{355}`, so the gap
against `ConstantsExposed.b_floor_cert` (`2^{603}`) narrows from **529 bits to 248**. -/

/-! ### §8.1 — the witness scale `⌈e^{2^400}⌉₊` -/

/-- **⟦THE RE-CUT WITNESS SCALE⟧** (`s15WitFloor2`) — `⌈e^{2^{400}}⌉₊`, so
`log H₋ ∈ [2^{400}, 2^{400} + 1]` and `λ₋ ≤ 400·log 2 = 277.2589`: above the `50` floor the
spine demands, below the `277.7` the RESTORED `anchor` allows through the `9/2` tower. -/
def s15WitFloor2 : ℕ := ⌈Real.exp ((2 : ℝ) ^ 400)⌉₊

theorem s15WitFloor2_log_ge : (2 : ℝ) ^ 400 ≤ Real.log ((s15WitFloor2 : ℕ) : ℝ) := by
  have h : Real.exp ((2 : ℝ) ^ 400) ≤ ((s15WitFloor2 : ℕ) : ℝ) := Nat.le_ceil _
  have h2 := Real.log_le_log (Real.exp_pos _) h
  rwa [Real.log_exp] at h2

theorem s15WitFloor2_log_le : Real.log ((s15WitFloor2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 400 + 1 := by
  have hc : ((s15WitFloor2 : ℕ) : ℝ) < Real.exp ((2 : ℝ) ^ 400) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hb : Real.exp ((2 : ℝ) ^ 400) + 1 ≤ 2 * Real.exp ((2 : ℝ) ^ 400) := by
    have : (1 : ℝ) ≤ Real.exp ((2 : ℝ) ^ 400) := Real.one_le_exp (by positivity)
    linarith
  have hle : ((s15WitFloor2 : ℕ) : ℝ) ≤ 2 * Real.exp ((2 : ℝ) ^ 400) := by linarith
  have hpos : (0 : ℝ) < ((s15WitFloor2 : ℕ) : ℝ) := by
    have h : Real.exp ((2 : ℝ) ^ 400) ≤ ((s15WitFloor2 : ℕ) : ℝ) := Nat.le_ceil _
    have := Real.exp_pos ((2 : ℝ) ^ 400)
    linarith
  have h1 := Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- `λ₋ ≥ 50` at the re-cut scale (crudely: `2^{99} ≤ 2^{400}`). -/
theorem s15WitFloor2_loglog_ge :
    (50 : ℝ) ≤ Real.log (Real.log ((s15WitFloor2 : ℕ) : ℝ)) := by
  have hlo := s15WitFloor2_log_ge
  have h1 : (2 : ℝ) ^ (99 : ℕ) ≤ Real.log ((s15WitFloor2 : ℕ) : ℝ) := by
    refine le_trans ?_ hlo
    norm_num
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  push_cast at h2
  linarith

/-- **⟦THE RE-CUT `λ₋` CEILING⟧** — `λ₋ ≤ 277.2589 = 400·log 2 + 2^{-400}`. -/
theorem s15WitFloor2_loglog_le :
    Real.log (Real.log ((s15WitFloor2 : ℕ) : ℝ)) ≤ 2772589 / 10000 := by
  have hhi := s15WitFloor2_log_le
  have hpos : (0 : ℝ) < Real.log ((s15WitFloor2 : ℕ) : ℝ) := by
    have := s15WitFloor2_log_ge
    have h0 : (0 : ℝ) < (2 : ℝ) ^ 400 := by positivity
    linarith
  have h1 := Real.log_le_log hpos hhi
  -- `log (2^400 + 1) ≤ 400·log 2 + 2^{-400}`
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ (400 : ℕ) := by positivity
  have hdiv : Real.log (((2 : ℝ) ^ (400 : ℕ) + 1) / (2 : ℝ) ^ (400 : ℕ))
      ≤ ((2 : ℝ) ^ (400 : ℕ) + 1) / (2 : ℝ) ^ (400 : ℕ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at hdiv
  have hsmall : ((2 : ℝ) ^ (400 : ℕ) + 1) / (2 : ℝ) ^ (400 : ℕ) - 1 ≤ 1 / 10 ^ 7 := by
    rw [div_sub_one (by positivity)]
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    norm_num
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  push_cast at hdiv
  norm_num at h1 ⊢
  linarith

/-- **⟦THE TOWER, AT THE RE-CUT SCALE⟧** — `λ₋ ≤ 277.2589 ⟹ λ₋^{9/2} ≤ 9.87·10^{10}`. -/
theorem s15w2_tower_bound {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2772589 / 10000) :
    x ^ ((9 : ℝ) / 2) ≤ 987 * 10 ^ 8 := by
  have hpow : x ^ ((9 : ℝ) / 2) ≤ (2772589 / 10000 : ℝ) ^ ((9 : ℝ) / 2) :=
    Real.rpow_le_rpow hx0 hx (by norm_num)
  have hnn : (0 : ℝ) ≤ (2772589 / 10000 : ℝ) ^ ((9 : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hsq : ((2772589 / 10000 : ℝ) ^ ((9 : ℝ) / 2)) ^ (2 : ℕ)
      = (2772589 / 10000 : ℝ) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast ((2772589 / 10000 : ℝ) ^ ((9 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2772589 / 10000 : ℝ) 9]
    norm_num
  have hb : (2772589 / 10000 : ℝ) ^ ((9 : ℝ) / 2) ≤ 987 * 10 ^ 8 := by
    nlinarith [hsq, hnn]
  linarith

/-- `2 ≤ e^{0.694}` — the base step of the window's `ℕ`-floors. -/
theorem s15w2_two_le_exp : (2 : ℝ) ≤ Real.exp (694 / 1000) := by
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (694 / 1000) := Real.exp_le_exp.mpr (by linarith)

/-- `arcFloor36 = 10^138 ≤ s15WitFloor2`. -/
theorem s15WitFloor2_arc : arcFloor36 ≤ s15WitFloor2 := by
  have hpow : (2 : ℝ) ^ (1000 : ℕ) ≤ Real.exp 694 := by
    calc (2 : ℝ) ^ (1000 : ℕ) ≤ (Real.exp (694 / 1000)) ^ (1000 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) s15w2_two_le_exp 1000
      _ = Real.exp 694 := by rw [← Real.exp_nat_mul]; norm_num
  have hmono : Real.exp 694 ≤ Real.exp ((2 : ℝ) ^ 400) :=
    Real.exp_le_exp.mpr (by norm_num)
  have h10 : ((arcFloor36 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (1000 : ℕ) := by
    rw [arcFloor36]; push_cast; norm_num
  have hfin : ((arcFloor36 : ℕ) : ℝ) ≤ ((s15WitFloor2 : ℕ) : ℝ) :=
    le_trans (le_trans (le_trans h10 hpow) hmono) (Nat.le_ceil _)
  exact_mod_cast hfin

/-- `loglogFloor50 = ⌈e^{e^{50}}⌉₊ ≤ s15WitFloor2`, since `e^{50} ≤ 2^{400}`. -/
theorem s15WitFloor2_ll : loglogFloor50 ≤ s15WitFloor2 := by
  have h1 : Real.exp 1 ≤ 2.72 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h50 : Real.exp 50 ≤ (2 : ℝ) ^ 400 := by
    have he : Real.exp 50 = Real.exp 1 ^ (50 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc Real.exp 1 ^ (50 : ℕ) ≤ (2.72 : ℝ) ^ (50 : ℕ) :=
          pow_le_pow_left₀ (Real.exp_pos 1).le h1 50
      _ ≤ (2 : ℝ) ^ 400 := by norm_num
  have hmono : Real.exp (Real.exp 50) ≤ Real.exp ((2 : ℝ) ^ 400) := Real.exp_le_exp.mpr h50
  rw [loglogFloor50, s15WitFloor2]
  exact Nat.ceil_le_ceil hmono

/-! ### §8.2 — the witness modulus `M = 2^355` and its exact door row -/

/-- `Adoor (2^355) = 2^{36}·356`. -/
theorem s15w2_Adoor : Adoor (2 ^ 355) = 2 ^ 36 * 356 := by
  rw [Adoor, Nat.log_pow (by norm_num)]

/-- `doorRowFloor (2^355) = 356·2^{391}` — the row the whole witness is read against. -/
theorem s15w2_doorRowFloor : doorRowFloor (2 ^ 355) = 356 * 2 ^ 391 := by
  rw [doorRowFloor, s15w2_Adoor]
  norm_num [← pow_add]

/-- `s13BlockExp (2^355) ≤ 2^{1542}`. -/
theorem s15w2_blockExp_le : s13BlockExp (2 ^ 355) ≤ 2 ^ 1542 := by
  have hid : s13BlockExp (2 ^ 355)
      = 14427 + (64 + 8 * (Nat.log 2 (2 ^ 355) + 1))
        + 400 * (Adoor (2 ^ 355) * (3072 * 2 ^ 355) * 2 ^ 355) ^ 2 := rfl
  rw [hid, s15w2_Adoor, Nat.log_pow (by norm_num)]
  norm_num

/-- `2^{1600} ≤ H₊` at the re-cut scale. -/
theorem s15w2_Hhi_ge {R : ChowlaRegime} (hlo : (2 : ℝ) ^ 400 ≤ Real.log ((R.Hlo : ℕ) : ℝ)) :
    (2 : ℕ) ^ 1600 ≤ R.Hhi := by
  have hpos : (0 : ℝ) < ((R.Hlo : ℕ) : ℝ) := by
    have := R.hHlo_floor
    have hp : (0 : ℕ) < R.Hlo := by omega
    exact_mod_cast hp
  have hexp : Real.exp 1111 ≤ ((R.Hlo : ℕ) : ℝ) := by
    have h1 : (1111 : ℝ) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
      refine le_trans ?_ hlo; norm_num
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log hpos] at h2
  have hpow : (2 : ℝ) ^ (1600 : ℕ) ≤ Real.exp 1111 := by
    calc (2 : ℝ) ^ (1600 : ℕ) ≤ (Real.exp (694 / 1000)) ^ (1600 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) s15w2_two_le_exp 1600
      _ = Real.exp 1110.4 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp 1111 := Real.exp_le_exp.mpr (by norm_num)
  have hlo' : ((2 : ℕ) ^ 1600 : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by
    push_cast; linarith
  have hnat : (2 : ℕ) ^ 1600 ≤ R.Hlo := by exact_mod_cast hlo'
  exact le_trans hnat R.hHlohi

/-- **⟦`M`-UPPER 1's WINDOW SIDE, RE-CUT⟧** — `2^{1541} ≤ ⌊ε²·H₊⌋₊` at `ε ≥ 2^{-9}`. -/
theorem s15w2_blk_floor {R : ChowlaRegime} (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : (2 : ℝ) ^ 400 ≤ Real.log ((R.Hlo : ℕ) : ℝ)) :
    (2 : ℕ) ^ 1541 ≤ ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by
  have hHhi := s15w2_Hhi_ge hlo
  have hHq : ((2 : ℕ) ^ 1600 : ℚ) ≤ (R.Hhi : ℚ) := by exact_mod_cast hHhi
  have hHq' : (2 : ℚ) ^ 1600 ≤ (R.Hhi : ℚ) := by push_cast at hHq; linarith
  have hepspos : (0 : ℚ) < R.eps := R.heps
  have hsq : (1 : ℚ) / 2 ^ 18 ≤ R.eps ^ 2 := by nlinarith [heps, hepspos]
  refine Nat.le_floor ?_
  have hstep : ((2 : ℕ) ^ 1541 : ℚ) ≤ (1 / 2 ^ 18) * 2 ^ 1600 := by
    push_cast; norm_num
  refine le_trans hstep ?_
  exact mul_le_mul hsq hHq' (by positivity) (sq_nonneg _)

/-- **⟦THE `level1` NUMERAL⟧** (`s15w2_lvl_num`) — the register's binding const-pool line at
`A(M) = 2^{36}·356`, abstracted from its three atoms: `26 + 14λ₊ + loglog𝒬/3 + log(1/ρ)`
spends `1.3818·10^{12}` against `(1/12)·2.4464·10^{13}·log 2 ≥ 1.4131·10^{12}`. -/
theorem s15w2_lvl_num {X Q Y : ℝ} (hX : X ≤ 987 * 10 ^ 8) (hQ : Q ≤ 277) (hY : -Y ≤ 36) :
    26 + 14 * X + 1 / 3 * Q + -Y ≤ 1 / 12 * 24464133718016 * Real.log 2 := by
  linarith only [Real.log_two_gt_d9, hX, hQ, hY]

/-! ### §8.3 — ⟦THE WITNESS⟧ -/

set_option maxHeartbeats 1600000 in
-- eleven register lines at `M = 2^355`: the `blk` line alone carries `2^1542`-sized casts and
-- the `x0M` line an `exp∘exp` chain, so the default budget is exhausted well before `lvl`
/-- **⟦THE RE-CUT REGISTER, WITNESSED⟧** (`s15_sel''_witness`).

Every one of `S15Sel''`'s eleven lines, discharged at `M = 2^{355}` against the stated
numeric window and two numeric facts about the regime (`hlo`: `log H₋ ≥ 2^{400}`, a CHOICE at
the compose; `hhi`: `λ₊ ≤ 9.87·10^{10}`, the tower conjunct at `λ₋ ≤ 277.2589`).

⟦THE LEDGER⟧ `hM` free; `mfloor`/`bfloor` are the window's own two lines at `2^{355}`;
`rho`/`anchor` off §1's `log(1/ρ) ≤ 36` against `3.9·10^9·356 = 1.3884·10^{12}` (`14·λ₊`
spends `1.3818·10^{12}` — 0.48% of margin, the binding line); `gRows`/`gP1`/`lvl` off
`A(M) = 2^{36}·356 = 2.4464·10^{13}`; `half` off `doorRowFloor M = 356·2^{391}` against
`2^{399}` (2.7%); `blk` off §8.2; `x0M` off `hx0win` through `e^{275} ≤ 2^{398} ≤
doorRowFloor M · log 2`.

⟦THE ONE UNDISCHARGEABLE HYPOTHESIS⟧ `hx0win`.  See the section preamble: `x₀` is
Siegel-ineffective, so no theorem places it in any window. -/
theorem s15_sel''_witness {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 10 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 20)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 20)
    (hbfl : 24 * Cg / δ₀ ≤ 2 ^ 355)
    (hMfl : Mfl ≤ 2 ^ 355)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp 275))
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : (2 : ℝ) ^ 400 ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 987 * 10 ^ 8) :
    S15Sel'' Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (2 ^ 355) := by
  have hρlog : -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 36 :=
    s15w_neglog_rho_le hδ hK hδb hKb
  have hinv : Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ K))
      = -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by
    rw [one_div, Real.log_inv]
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- ⟦the door row, exactly⟧
  have hAdR : ((Adoor (2 ^ 355) : ℕ) : ℝ) = 24464133718016 := by
    rw [s15w2_Adoor]; norm_num
  have hdrfR : ((doorRowFloor (2 ^ 355) : ℕ) : ℝ) = 356 * 2 ^ 391 := by
    rw [s15w2_doorRowFloor]; push_cast; ring
  have hnR : ((Nat.log 2 (2 ^ 355) + 1 : ℕ) : ℝ) = 356 := by
    rw [Nat.log_pow (by norm_num)]; norm_num
  refine
    { hM := Nat.one_le_two_pow
      mfloor := hMfl
      bfloor := ?_
      gRows := ?_
      x0M := ?_
      blk := ?_
      half := ?_
      rho := ?_
      anchor := ?_
      gP1 := ?_
      lvl := ?_ }
  · -- ⟦`M`-LOWER 1⟧ the spine's `hMδ`, stated at the window
    exact_mod_cast hbfl
  · -- ⟦`M`-LOWER 2⟧ `242·λ₊ ≤ A(M)`
    rw [hAdR]; linarith [hhi]
  · -- ⟦RESTORED⟧ `x₀ ≤ 2^{doorRowFloor M}`
    have h398 : Real.exp 275 ≤ (2 : ℝ) ^ (398 : ℕ) := by
      have hl : (275 : ℝ) ≤ Real.log ((2 : ℝ) ^ (398 : ℕ)) := by
        rw [Real.log_pow]; push_cast; linarith
      calc Real.exp 275 ≤ Real.exp (Real.log ((2 : ℝ) ^ (398 : ℕ))) := Real.exp_le_exp.mpr hl
        _ = (2 : ℝ) ^ (398 : ℕ) := Real.exp_log (by positivity)
    have hrow : (2 : ℝ) ^ (398 : ℕ)
        ≤ ((doorRowFloor (2 ^ 355) : ℕ) : ℝ) * Real.log 2 := by
      rw [hdrfR]; nlinarith [hlog2lo]
    have hpowid : ((2 : ℝ) ^ (doorRowFloor (2 ^ 355) : ℕ))
        = Real.exp (((doorRowFloor (2 ^ 355) : ℕ) : ℝ) * Real.log 2) := by
      rw [← Real.log_pow]
      exact (Real.exp_log (by positivity)).symm
    have hfin : (x₀ : ℝ) ≤ (2 : ℝ) ^ (doorRowFloor (2 ^ 355) : ℕ) := by
      rw [hpowid]
      refine le_trans hx0win (Real.exp_le_exp.mpr ?_)
      linarith [h398, hrow]
    exact_mod_cast hfin
  · -- ⟦`M`-UPPER 1⟧ the block ceiling
    have hbe : ((s13BlockExp (2 ^ 355) : ℕ) : ℝ) ≤ 2 ^ 1542 := by
      have h := s15w2_blockExp_le
      have h' : ((s13BlockExp (2 ^ 355) : ℕ) : ℝ) ≤ ((2 ^ 1542 : ℕ) : ℝ) := by exact_mod_cast h
      calc ((s13BlockExp (2 ^ 355) : ℕ) : ℝ) ≤ ((2 ^ 1542 : ℕ) : ℝ) := h'
        _ = 2 ^ 1542 := by push_cast; ring
    have hfl := s15w2_blk_floor heps hlo
    have hfl' : (2 : ℝ) ^ 1541 ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
      have h : ((2 ^ 1541 : ℕ) : ℝ) ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hfl
      calc (2 : ℝ) ^ 1541 = ((2 ^ 1541 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ _ := h
    have hgap : (2 : ℝ) ^ 1542 + 1 + 18 * (987 * 10 ^ 8) ≤ 4 * (2 : ℝ) ^ 1541 := by
      norm_num
    linarith [hbe, hfl', hhi, hgap]
  · -- ⟦`M`-UPPER 2⟧ the window gate
    rw [hinv, hdrfR]
    have h2 : (7 / 10 : ℝ) * (356 * 2 ^ 391) + 3 * 36 ≤ (2 : ℝ) ^ 400 / 2 := by norm_num
    linarith [h2, hρlog, hlo]
  · -- the clearing charge
    linarith [hρlog]
  · -- ⟦RESTORED⟧ the `ρ`-frame's anchor at `3.9·10^9·(log₂M + 1)`
    rw [hinv, hnR]
    linarith [hhi, hρlog]
  · -- the `𝒯`-leg budget
    rw [hAdR]
    have hCtl : Real.log Ct ≤ 20 * Real.log 2 := by
      have h := Real.log_le_log hCt hCtb
      rwa [Real.log_pow] at h
    have hρ' : -(36 : ℝ) ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by
      linarith [hρlog]
    nlinarith [hlog2lo, hhi, hCtl, hρ', hlog2hi]
  · -- the `level1` budget
    rw [hAdR, s15_log_calQK_one (2 ^ 355), hdrfR]
    have hQ : Real.log ((356 : ℝ) * 2 ^ 391 * Real.log 2) ≤ 277 := by
      have hl2 : (0 : ℝ) < Real.log 2 := by linarith only [hlog2lo]
      have hpos : (0 : ℝ) < 356 * 2 ^ 391 * Real.log 2 := by positivity
      have hle : (356 : ℝ) * 2 ^ 391 * Real.log 2 ≤ (2 : ℝ) ^ (399 : ℕ) := by
        linarith only [hlog2hi]
      have h := Real.log_le_log hpos hle
      rw [Real.log_pow] at h
      push_cast at h
      linarith only [h, hlog2hi]
    exact s15w2_lvl_num hhi hQ hρlog

/-! ### §8.4 — ⟦THE COMPOSE⟧ THE RE-CUT CONDITIONAL, REGISTER DISCHARGED -/

set_option maxHeartbeats 800000 in
-- the `∃`-block re-elaborates the capstone's instantiated prefix, as in `S15Compose` §10
/-- **⟦THE RE-CUT CONDITIONAL, REGISTER DISCHARGED⟧**
(`logChowla2_conditional_sharp2_nonvacuous`).

`S15Compose.logChowla2_conditional_sharp2` fired at `U1floor := s15WitFloor2` and
`M := 2^{355}`, with `S15Sel''` DISCHARGED by §8.3's witness.  What remains inside the
`∃`-block is one implication whose antecedent is the numeric window and whose consequent
names `S15CrossingBound` as the only surviving analytic hypothesis.

⟦AGAINST §6⟧ the window moved: `Mfl ≤ 2^{56} → Mfl ≤ 2^{355}` (the graded twin's floor is
`2` once `S11HoistGrade` §4's numeral is kept — 353 bits of room), `24·Cg/δ₀ ≤ 2^{56} →
2^{355}` (the `b`-floor gap 529 bits → 248), and `x₀ ≤ 2^{56}` became the DOUBLE-EXPONENTIAL
window `x₀ ≤ e^{e^{275}}`, against a chain whose own `x₀` floor is `e^{e^{100}}`.

⟦WHAT DID NOT MOVE⟧ `hx0win` is a hypothesis, not a discharge: `x₀` is Siegel-ineffective.
And `S15CrossingBound` is still the one analytic survivor. -/
theorem logChowla2_conditional_sharp2_nonvacuous :
    ∃ (ε : ℚ) (Cg K δ₀ Ct : ℝ) (x₀ Hcap Mfl : ℕ),
      0 < ε ∧ 1 ≤ Cg ∧ 0 < K ∧ 0 < δ₀ ∧ 0 < Ct ∧ 1 ≤ Mfl ∧
      ((1 : ℚ) / 2 ^ 9 ≤ ε → 24 * Cg / δ₀ ≤ 2 ^ 355 → 1 / 2 ^ 10 ≤ δ₀ → K ≤ 2 ^ 20 →
        Ct ≤ 2 ^ 20 → (x₀ : ℝ) ≤ Real.exp (Real.exp 275) → Mfl ≤ 2 ^ 355 →
        Hcap ≤ s15WitFloor2 →
        ∀ g : ℕ → ℕ → ℕ, ∃ (R : ChowlaRegime) (M : ℕ),
          R.eps = ε ∧ R.Hlo = s15WitFloor2 ∧ g R.Hhi R.ω ≤ R.x ∧
          S15Sel'' Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R M ∧
          (S15CrossingBound R M → ¬ logChowla2Fails R.eps R.x R.ω)) := by
  obtain ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl1, hbody⟩ :=
    logChowla2_conditional_sharp2
  refine ⟨ε, Cg, K, δ₀, Ct, x₀, Hcap, Mfl, hε, hCg, hK, hδ₀, hCt, hMfl1, ?_⟩
  intro hεb hbfl hδb hKb hCtb hx0b hMflb hHcap g
  have hU : max Hcap (max arcFloor36 loglogFloor50) ≤ s15WitFloor2 := by
    have h1 := s15WitFloor2_arc
    have h2 := s15WitFloor2_ll
    omega
  obtain ⟨R, hReps, hHlo, hRg, hRtow, hfire⟩ := hbody s15WitFloor2 g hU
  have hlo : (2 : ℝ) ^ 400 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact s15WitFloor2_log_ge
  have h50 : (50 : ℝ) ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) := by
    rw [hHlo]; exact s15WitFloor2_loglog_ge
  have hlam : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 2772589 / 10000 := by
    rw [hHlo]; exact s15WitFloor2_loglog_le
  have hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 987 * 10 ^ 8 := by
    refine le_trans (hRtow h50) ?_
    exact s15w2_tower_bound (by linarith) hlam
  have heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps := by rw [hReps]; exact hεb
  refine ⟨R, 2 ^ 355, hReps, hHlo, hRg, ?_, ?_⟩
  · exact s15_sel''_witness hδ₀ hδb hK hKb hCt hCtb hbfl hMflb hx0b heps hlo hhi
  · exact hfire (2 ^ 355)
      (s15_sel''_witness hδ₀ hδb hK hKb hCt hCtb hbfl hMflb hx0b heps hlo hhi)

/-- **⟦THE `b`-FLOOR CEILING, RE-CUT⟧** (`s15_sel''_bfloor_window`) — §5's unconditional read
at `S15Sel''`: `half` and `bfloor` did not move, so the arithmetic is §5's verbatim.  What
moved is the `λ₋` the RESTORED `anchor` certifies through the `9/2` tower — `75.28 → 277.7`,
i.e. `log H₋ ≤ 2^{110} → 2^{401}` — and with it the ceiling `2^{74} → 2^{365}`: **238 bits**
against `ConstantsExposed.b_floor_cert`'s `2^{603}`, where §5 measured 529.  (At the witness's
own `M = 2^{355}` the read is 248 bits; the extra ten are the crude `A(M) ≥ 2^{36}` step this
`M`-free statement is forced to take.) -/
theorem s15_sel''_bfloor_window {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hsel : S15Sel'' Cg δ₀ Ct ρ x₀ Mfl R M)
    (hw : Real.log ((R.Hlo : ℕ) : ℝ) ≤ 2 ^ 401) :
    24 * Cg / δ₀ ≤ 2 ^ 365 := by
  have hlρ : (0 : ℝ) ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]
    have : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
    linarith
  have hdrf : ((M : ℕ) : ℝ) * 2 ^ 36 ≤ ((doorRowFloor M : ℕ) : ℝ) := by
    have h : M * 2 ^ 36 ≤ doorRowFloor M := by
      calc M * 2 ^ 36 ≤ M * Adoor M := Nat.mul_le_mul_left _ (Adoor_ge M)
        _ = doorRowFloor M := rfl
    have h' : ((M * 2 ^ 36 : ℕ) : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := by exact_mod_cast h
    calc ((M : ℕ) : ℝ) * 2 ^ 36 = ((M * 2 ^ 36 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := h'
  have hhalf := hsel.half
  have hM : ((M : ℕ) : ℝ) ≤ 2 ^ 365 := by
    linarith [hhalf, hdrf, hlρ, hw]
  exact le_trans hsel.bfloor hM

