/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# (B1) at `2^12` — THE LEAVES OF THE GRADED LANE THAT BOTH READINGS OF THE RUNG CONSUME

Council 2026-09-12, item ⑦: the Captain set the door envelope's dial from `2^11` to `2^12` with the
split re-cut.  `StrideGradeWalls.lean` (F5-β) runs the graded lane at the threaded pin
`1/(838400·2^11·h²) ≤ δ₀`; this module holds the members of the `2^12` lane whose STATEMENTS carry
no cap of any kind — no `log h ≤ N` binder, no `log (a·h) ≤ N`, no stride bound `a ≤ 1096` — so they
are consumed unchanged whichever cap the rest of the lane is stated at.  Every name is NEW; **no
landed declaration moves and no landed statement is re-pointed.**

WHY THE RUNG NEEDS MORE THAN THE DIAL (the §0 certificates below).  The composition
(`StridePrize.lean:213-228`) bounds `a` only through the PRODUCT cap `a·h ≤ 1096`, and the prize is
read at `h = 2`, so the landed prize is capped at `primorial z ≤ 548` whatever the exponent
(`landed_prize_cap_refuses_primorial_eleven`).  At `2^12` the door arm admits `a = primorial 11 =
2310` at a split below `1` (`grade12_split_admits_primorial_eleven`) but refuses `a·h = 4620` even
at split `1` (`grade12_product_cap_refuses_primorial_eleven`), and the landed `2^11` refuses `2310`
outright (`grade11_refuses_primorial_eleven`).  ⇒ moving `z` past `10` at `2^12` needs a separate
bound on `a` beside a lifted product cap — statement acts that are NOT taken here.

THE NUMERALS (each re-derived, none copied from a docstring; `log 2 < 0.6931471808`):
  · the pin `838400·2^12 = 3434086400 ≤ 2^32 = 4294967296` (×1.2507, the landed bridge's ratio);
  · the envelope floor is KEPT at `2^592`: `16·110525·2^539·2^32 = 110525·2^575 ≤ 2^592 ⇔ 1768400 ≤
    2^21 = 2097152` (×1.186).  The landed ×2.37 is not needed, and spending the spare bit would
    move the charge by one nat and re-twin the landed charge-generic register
    `s15_sel''_L_witness_flat_charge_g` and its four lines, for no gain;
  · the charge therefore stays `592·log 2 = 410.343 ≤ 411` (0.657 nats, as landed);
  · the bump `24·2·10¹²·838400·4096 = 1.648361472·10²³`, `× 1202604² = 2.384·10³⁵ ≤ 10³⁶ ≤ 2^355`
    (70 orders).

HONEST LABEL.  Numerals only; nothing here proves an estimate, no cap is raised, and **nothing bears
on twin primes.**
-/
import Salt.MR.StrideGradeWalls
import Mathlib

noncomputable section

open Salt.Entropy.Chowla

set_option exponentiation.threshold 4000

namespace Salt.MR

/-! ## §0 — CENSUS CERTIFICATES OF THE RUNG, EACH POSITIVE WITH ITS CONTROL

These five pins are consumed by NO reading of the rung (the lane proves its bridges and its door
arm inline); they are the rung's price, put in the kernel so it is re-checked rather than
re-derived. -/

/-- **⟦THE PIN BRIDGE AT `2^12`⟧ (class A)** — `838400·2^12 = 3434086400 ≤ 2^32`, the twin of the
landed `838400·2^11 ≤ 2^31`; the same ratio `1.2507`. -/
theorem grade12_pin_bridge : (838400 : ℕ) * 2 ^ 12 ≤ 2 ^ 32 := by norm_num

/-- **⟦THE DOOR ARM ADMITS `primorial 11` AT `2^12`, AT SOME SPLIT BELOW `1`⟧ (class A)** — with
`a = 2310`, `Zr ≤ 1.02` and the door ceiling `1/(837782·2^12·k²)` against the head's floor
`1/(838400·k²)`: `2310·1.02·838400 = 1975438080 < 837782·4096 = 3431555072`, so the door arm's share
of `δ₀` is `0.5757 < 1`.  No split is chosen here. -/
theorem grade12_split_admits_primorial_eleven :
    (2310 : ℚ) * (102 / 100) * 838400 < 837782 * 2 ^ 12 := by norm_num

/-- **⟦CONTROL — A PRODUCT-ONLY READING REFUSES `z = 11` AT `2^12` AT EVERY SPLIT⟧ (class A)** — if
`a` is read through `a ≤ a·h ≤ K` (as `StridePrize.lean:213-214` reads it), the door arm must admit
`a = K ≥ 2·primorial 11 = 4620`, and at split `1` it needs `4620·1.02·838400 = 3950876160 ≤
837782·4096 = 3431555072`, which is FALSE (`sup = 4012.7`). -/
theorem grade12_product_cap_refuses_primorial_eleven :
    ¬ ((4620 : ℚ) * (102 / 100) * 838400 ≤ 837782 * 2 ^ 12) := by norm_num

/-- **⟦CONTROL — THE LANDED `2^11` REFUSES `primorial 11` EVEN WITH A SEPARATE BOUND ON `a`⟧
(class A)** — at split `1`: `2310·1.02·838400 = 1975438080 > 837782·2048 = 1715777536`
(`sup = 2006.4`).  Without this the positive above reads as *"the split re-cut alone moves `z`"*. -/
theorem grade11_refuses_primorial_eleven :
    ¬ ((2310 : ℚ) * (102 / 100) * 838400 ≤ 837782 * 2 ^ 11) := by norm_num

/-- **⟦CONTROL — THE LANDED PRIZE'S `548` IS THE PRODUCT CAP, NOT THE WALL⟧ (class A)** — the landed
door arm at `2^11` and split `0.55` (`StridePrize.lean:224-228`) admits `a = 1103`, but the prize
(`StrideGradeReceipt.lean:70-76`) reads `a` through `a·h ≤ 1096` at `h = 2`, which refuses it.  (The
bare `¬ (2310 · 2 ≤ 1096)` would not discriminate: `¬ (2310 ≤ 1096)` holds as well.) -/
theorem landed_prize_cap_refuses_primorial_eleven :
    (1103 : ℚ) * (102 / 100) * 838400 ≤ (55 / 100) * (837782 * 2 ^ 11) ∧ ¬ (1103 * 2 ≤ 1096) := by
  norm_num

/-! ## §1 — THE CHARGE CHAIN AT THE `2^12` PIN (`StrideGradeWalls.lean:65-111`'s two walls) -/

/-- **⟦W15 AT THE `2^12` PIN⟧ (class B)** — `s16_audit_rho_ge_wide_h_g` (`StrideGradeWalls.lean:65`)
with `2 ^ 31 ↦ 2 ^ 32` in `hδb` ONLY; the conclusion stays at `2 ^ 592`.  BODY:
`StrideGradeWalls.lean:68-90` verbatim with `2 ^ 31 ↦ 2 ^ 32` at `hkey` and `hsplit2`; the
`nlinarith [hKb, hK]` closing `hkey` compares `1768400 = 16·110525` against
`2^592/(2^539·2^32) = 2^21 = 2097152` — ×1.186 (the landed ×2.37 had one bit to spare). -/
theorem s16_audit_rho_ge_wide_h_g12 {h : ℕ} (hh : 0 < h) {δ₀ K : ℝ} (hδ : 0 < δ₀) (hK : 0 < K)
    (hδb : 1 / (2 ^ 32 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    (1 : ℝ) / (2 ^ 592 * (h : ℝ) ^ 2) ≤ doorRhoOfDelta (s12DeltaSock δ₀ K) := by
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhsq : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith
  have hh0 : (0 : ℝ) < (h : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 / (h : ℝ) ^ 2 := by positivity
  rw [doorRhoOfDelta, le_min_iff]
  refine ⟨?_, ?_⟩
  · rw [div_le_one (by positivity)]
    nlinarith [hhsq]
  rw [s12DeltaSock_sq hδ hK, div_div, le_div_iff₀ (by positivity)]
  -- ⟦THE SPLIT⟧ the `h²` is a common factor on both sides; peel it off so the
  -- numeral comparison `1768400 ≤ 2^21` is seen by `nlinarith` on its own.
  have hkey : 1 / (2 : ℝ) ^ 592 * (16 * K * 110525) ≤ 1 / (2 : ℝ) ^ 32 := by
    nlinarith [hKb, hK]
  have hsplit1 : 1 / ((2 : ℝ) ^ 592 * (h : ℝ) ^ 2) * (16 * K * 110525)
      = 1 / (2 : ℝ) ^ 592 * (16 * K * 110525) * (1 / (h : ℝ) ^ 2) := by
    field_simp
  have hsplit2 : 1 / (2 : ℝ) ^ 32 * (1 / (h : ℝ) ^ 2)
      = 1 / ((2 : ℝ) ^ 32 * (h : ℝ) ^ 2) := by
    field_simp
  rw [hsplit1]
  refine le_trans (mul_le_mul_of_nonneg_right hkey hinv.le) ?_
  rw [hsplit2]
  exact hδb

/-- **⟦W16 AT THE `2^12` PIN⟧ (class A)** — `s16_audit_neglog_rho_le_wide_h_g`
(`StrideGradeWalls.lean:96`) with `2 ^ 31 ↦ 2 ^ 32` in `hδb` ONLY; the conclusion stays
`411 + 2·log h`.  BODY: `StrideGradeWalls.lean:99-111` verbatim with the ONE swap
`s16_audit_rho_ge_wide_h_g ↦ s16_audit_rho_ge_wide_h_g12` at `hge`; the closing `linarith` has
`411 − 592·0.6931471808 = 0.657` nats, as landed. -/
theorem s16_audit_neglog_rho_le_wide_h_g12 {h : ℕ} (hh : 0 < h) {δ₀ K : ℝ} (hδ : 0 < δ₀)
    (hK : 0 < K) (hδb : 1 / (2 ^ 32 * (h : ℝ) ^ 2) ≤ δ₀) (hKb : K ≤ 2 ^ 539) :
    -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 411 + 2 * Real.log (h : ℝ) := by
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hge := s16_audit_rho_ge_wide_h_g12 hh hδ hK hδb hKb
  have hpos : (0 : ℝ) < 1 / (2 ^ 592 * (h : ℝ) ^ 2) := by positivity
  have h1 : Real.log ((1 : ℝ) / (2 ^ 592 * (h : ℝ) ^ 2))
      ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := Real.log_le_log hpos hge
  have h2 : Real.log ((1 : ℝ) / (2 ^ 592 * (h : ℝ) ^ 2))
      = -(592 * Real.log 2) - 2 * Real.log (h : ℝ) := by
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    push_cast; ring
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [h2] at h1
  linarith

/-! ## §2 — THE BUMP AT THE `2^12` PIN (`StrideGradeWalls.lean:347-372`) -/

/-- **⟦BUMP 1 AT THE `2^12` PIN⟧ (class B)** — `flatDoorM_bfloor_bump_g`
(`StrideGradeWalls.lean:347`) with `hδb : 1/(838400·2^11·c²) ≤ δ₀ ↦ 1/(838400·2^12·c²) ≤ δ₀` and
`hcb : c ≤ 1096 ↦ c ≤ 1202604` (a numeral ceiling on the bump's argument; `1202604 = ⌊e^14⌋` is a
CHOICE — the widest cap image in the family — while the bump's own wall is
`c ≤ √(2^355/1.648·10²³) ≈ 6.7·10⁴¹`).  BODY:
`StrideGradeWalls.lean:351-372` verbatim with the moved sites by `have`-name: `hcRb` and
`hcsqb : c² ≤ 1446256380816`; `hkey` (statement and `calc`) at `838400 * 2 ^ 12`;
`hstep : 24·Cg/δ₀ ≤ 164836147200000000000000·c²` (`= 24·2·10¹²·838400·4096`); `hcap`'s constant and
`h355 : 10^36 ≤ 2^355` (`1.648·10²³·1.446·10¹² = 2.384·10³⁵`); then `flatDoorM_ge_pow355 hA` as
landed. -/
theorem flatDoorM_bfloor_bump_g12 {A Cg δ₀ : ℝ} {c : ℕ} (hc1 : 1 ≤ c) (hcb : c ≤ 1202604)
    (hA : 162 ≤ A) (hδ : 0 < δ₀)
    (hδb : 1 / (838400 * 2 ^ 12 * (c : ℝ) ^ 2) ≤ δ₀) (hCg : Cg ≤ 2 * 10 ^ 12) :
    24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ) := by
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hcRb : (c : ℝ) ≤ 1202604 := by exact_mod_cast hcb
  have hcsqb : (c : ℝ) ^ 2 ≤ 1446256380816 := by nlinarith [hcR1, hcRb]
  have hcsq1 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by nlinarith [hcR1]
  -- ⟦THE ROUTE⟧ as in the landed bump: `flatDoorM_ge_pow355` (`2^355 ≈ 7.3·10^106`), which
  -- clears `2.4·10^35` by 70 orders.
  have hcsqpos : (0 : ℝ) < (c : ℝ) ^ 2 := by nlinarith [hcR1]
  have hkey : (1 : ℝ) / (838400 * 2 ^ 12) ≤ (c : ℝ) ^ 2 * δ₀ := by
    have h := mul_le_mul_of_nonneg_left hδb hcsqpos.le
    calc (1 : ℝ) / (838400 * 2 ^ 12)
        = (c : ℝ) ^ 2 * (1 / (838400 * 2 ^ 12 * (c : ℝ) ^ 2)) := by field_simp
      _ ≤ (c : ℝ) ^ 2 * δ₀ := h
  have hstep : 24 * Cg / δ₀ ≤ (164836147200000000000000 : ℝ) * (c : ℝ) ^ 2 := by
    rw [div_le_iff₀ hδ]
    nlinarith [hkey, hCg]
  have hcap : (164836147200000000000000 : ℝ) * (c : ℝ) ^ 2 ≤ (2 : ℝ) ^ (355 : ℕ) := by
    have h355 : (10 ^ 36 : ℝ) ≤ (2 : ℝ) ^ (355 : ℕ) := by norm_num
    nlinarith [hcsqb, h355]
  have hpow : (2 : ℝ) ^ (355 : ℕ) ≤ ((flatDoorM A : ℕ) : ℝ) := by
    exact_mod_cast flatDoorM_ge_pow355 hA
  linarith [hstep, hcap, hpow]

end Salt.MR

end
