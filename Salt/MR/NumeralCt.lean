/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowsChiPrimeLinear
import Salt.MR.TLegExit
import Salt.MR.MomentsA2
import Salt.MR.ShiuMoment

/-!
# ⟦ROUTE 2 — THE `Ct` CEILING, LEAF TO THE FENCE⟧ (NUMERAL wave)

`logChowla2_ineffective`'s second inner rider is `Ct ≤ 2^23`.  `Ct` is
`S16FlatTerminalLinear.m4_closure_fuse_zero'_const_nonneg_L_gk`'s opaque
`∃ Ct, 0 < Ct` — POSITIVITY ONLY — but the constant is not opaque at the
bottom: it is `ShiuMoment.shiu_moment_sq`'s OWN `refine` witness `2·exp 14`,
carried up thirteen hops with EXACTLY ONE rescale (`lemma13_moment`'s `C ↦ 3C`).
So the true value is `6·e^14 = 7.216·10^6 = 2^22.78`, against the asked
`2^23 = 8.389·10^6` — 14% of headroom, and the rider is TRUE.

This file mints the thirteen `_bounded` twins: each is the landed statement
with ONE conjunct added (`Ct ≤ 6·exp 14`) and the landed proof replayed
verbatim against the twin below it.  ⟦IRON RULE 1⟧ every landed declaration is
untouched; nothing here is a restatement of anything.

THE CHAIN (bottom to top):
`shiu_moment_sq` → `blockDiv_sq_div_sq_sum_le` → `lemma13_moment` (×3) →
`mix_moment` → `cell_bound_raw` → `cell_bound_pinned` → `Ej_bound_gen` →
`TLeg_bound_gen` → `TLeg_feeds_capstone_gen` →
`m4_rowChi_number_of_capstone_zero'` → `m4_hrowsSum_chi_zero'` →
`m4_hrowsSum_chi_door_zero'_L_gk` → `m4_hrowsSlot_at_door_zero'_L_gk`.

THE FENCE: the next hop up, `m4_closure_fuse_zero'_const_nonneg_L_gk`, lives in
`S16FlatTerminalLinear.lean`, which is owned by another wave; the twin for it
(one `obtain`/`refine` edit against `m4_hrowsSlot_at_door_zero'_L_gk_bounded`)
is the compose pass's, not this file's.

No `sorry`, no `native_decide`, no new axioms.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral Complex
open Finset

-- ⟦BYTE-FAITHFUL REPLAY⟧ every proof body below is the landed proof, copied verbatim so
-- that the twin is auditable against its original line for line; the long lines are the
-- originals' own, and reflowing them would destroy exactly the property that makes the
-- replay checkable.  (Same device as `Salt/Chen/SuperPanelsO.lean`.)
set_option linter.style.longLine false

namespace Salt.MR

open Salt.Entropy.Chowla

set_option maxHeartbeats 1000000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `shiu_moment_sq` + the conjunct `C ≤ 2 * Real.exp 14`.
`shiu_moment_sq` with its own `refine` witness `2·exp 14` IN THE STATEMENT. -/
theorem shiu_moment_sq_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 * Real.exp 14 ∧ ∀ (Y₁ Y : ℕ), 1 ≤ Y₁ →
      ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 ≤ C * (Y : ℝ) := by
  refine ⟨2 * Real.exp 14, by positivity, le_rfl, ?_⟩
  intro Y₁ Y hY₁
  have hg0 : (blockDiv Y₁ 0 : ℝ) ^ 2 = 0 := by simp [blockDiv]
  have hstep1 : ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 := by
    have hsub : Finset.Icc Y (2 * Y) ⊆ insert 0 (Finset.Icc 1 (2 * Y)) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨hpos, hn.2⟩)
    calc ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2
        ≤ ∑ n ∈ insert 0 (Finset.Icc 1 (2 * Y)), (blockDiv Y₁ n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ = ∑ n ∈ Finset.Icc 1 (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 := by
          rw [Finset.sum_insert (by simp), hg0, zero_add]
  calc ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 := hstep1
    _ ≤ ((2 * Y : ℕ) : ℝ) * ∑ d ∈ (Finset.Icc 1 (2 * Y)).filter (BlockSmooth Y₁),
          (d.divisors.card : ℝ) ^ 2 / (d : ℝ) := shiu_moment_reduce Y₁ (2 * Y)
    _ ≤ ((2 * Y : ℕ) : ℝ) * Real.exp 14 :=
        mul_le_mul_of_nonneg_left (block_tauSq_div_sum_le Y₁ (2 * Y) hY₁) (by positivity)
    _ = 2 * Real.exp 14 * (Y : ℝ) := by push_cast; ring

set_option maxHeartbeats 1000000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `blockDiv_sq_div_sq_sum_le` + the conjunct `C ≤ 2 * Real.exp 14`.
the dyadic Shiu sum, ceiling passed through verbatim. -/
lemma blockDiv_sq_div_sq_sum_le_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 2 * Real.exp 14 ∧ ∀ (Y₁ X M : ℕ), 1 ≤ Y₁ → 1 ≤ X →
      ∑ n ∈ Finset.Icc X M, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
        ≤ 3 * C / (X : ℝ) := by
  obtain ⟨C, hC, hCb, hShiu⟩ := shiu_moment_sq_bounded
  refine ⟨C, hC, hCb, ?_⟩
  intro Y₁ X M hY₁ hX
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  -- one dyadic block: Σ_{Y≤n≤2Y} g²/n² ≤ C/Y (shiu_moment_sq + 1/n²≤1/Y²).
  have block : ∀ Y : ℕ, 1 ≤ Y →
      ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
        ≤ C / (Y : ℝ) := by
    intro Y hY
    have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
    calc ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (Y : ℝ) ^ 2 := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hYn : (Y : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          gcongr
      _ = (1 / (Y : ℝ) ^ 2) * ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => by ring)
      _ ≤ (1 / (Y : ℝ) ^ 2) * (C * (Y : ℝ)) :=
          mul_le_mul_of_nonneg_left (hShiu Y₁ Y hY₁) (by positivity)
      _ = C / (Y : ℝ) := by field_simp
  -- induction on K: Σ_{X≤n≤2^K X} g²/n² ≤ (C/X)(3−2/2^K), geometric-slack invariant.
  have key : ∀ K : ℕ,
      ∑ n ∈ Finset.Icc X (2 ^ K * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
      ≤ (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ K) := by
    intro K
    induction K with
    | zero =>
      have h1 : Finset.Icc X (2 ^ 0 * X) ⊆ Finset.Icc X (2 * X) := by
        apply Finset.Icc_subset_Icc_right; simp only [pow_zero, one_mul]; omega
      calc ∑ n ∈ Finset.Icc X (2 ^ 0 * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
          ≤ ∑ n ∈ Finset.Icc X (2 * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg h1 (fun _ _ _ => by positivity)
        _ ≤ C / (X : ℝ) := block X hX
        _ = (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ 0) := by norm_num
    | succ K ih =>
      set Y : ℕ := 2 ^ K * X with hYdef
      have hYpos : 1 ≤ Y := by rw [hYdef]; exact Nat.mul_pos (by positivity) hX
      have hYr : (0 : ℝ) < Y := by exact_mod_cast hYpos
      have hXne : (X : ℝ) ≠ 0 := hXr.ne'
      have hp0 : (2 : ℝ) ^ K ≠ 0 := by positivity
      have hYeq : (Y : ℝ) = (2 : ℝ) ^ K * (X : ℝ) := by rw [hYdef]; push_cast; ring
      have hcover : Finset.Icc X (2 ^ (K + 1) * X)
          ⊆ Finset.Icc X Y ∪ Finset.Icc Y (2 * Y) := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        have h2Y : 2 ^ (K + 1) * X = 2 * Y := by rw [hYdef]; ring
        rw [h2Y] at hn
        rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
        by_cases hnY : n ≤ Y
        · exact Or.inl ⟨hn.1, hnY⟩
        · exact Or.inr ⟨by omega, hn.2⟩
      have hsplit :
          ∑ n ∈ Finset.Icc X (2 ^ (K + 1) * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
          ≤ (∑ n ∈ Finset.Icc X Y, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
            + ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
        have hle :
            ∑ n ∈ Finset.Icc X (2 ^ (K + 1) * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
            ≤ ∑ n ∈ Finset.Icc X Y ∪ Finset.Icc Y (2 * Y),
                (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover (fun i _ _ => by positivity)
        have hui : (∑ n ∈ Finset.Icc X Y ∪ Finset.Icc Y (2 * Y),
                (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
              + (∑ n ∈ Finset.Icc X Y ∩ Finset.Icc Y (2 * Y),
                (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
            = (∑ n ∈ Finset.Icc X Y, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
              + ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
          Finset.sum_union_inter
        have hinter : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc X Y ∩ Finset.Icc Y (2 * Y),
            (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
          Finset.sum_nonneg (fun _ _ => by positivity)
        linarith [hle, hui, hinter]
      have hXYr : ∑ n ∈ Finset.Icc X Y, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
          ≤ (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ K) := ih
      calc ∑ n ∈ Finset.Icc X (2 ^ (K + 1) * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
          ≤ (∑ n ∈ Finset.Icc X Y, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2)
            + ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 := hsplit
        _ ≤ (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ K)
              + (C / (X : ℝ)) * (1 / (2 : ℝ) ^ K) := by
            refine add_le_add hXYr ((block Y hYpos).trans_eq ?_)
            rw [mul_one_div, div_div, mul_comm (X : ℝ) ((2 : ℝ) ^ K), ← hYeq]
        _ = (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ (K + 1)) := by
            have hp : (2 : ℝ) ^ (K + 1) = 2 * (2 : ℝ) ^ K := by rw [pow_succ]; ring
            rw [hp]; ring
  -- choose `K = M`, so `M ≤ 2^M·X` and `Icc X M ⊆ Icc X (2^M·X)`.
  have hMsub : Finset.Icc X M ⊆ Finset.Icc X (2 ^ M * X) := by
    apply Finset.Icc_subset_Icc_right
    calc M ≤ 2 ^ M := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ M * X := Nat.le_mul_of_pos_right _ hX
  have hgeo : (0 : ℝ) < 2 / (2 : ℝ) ^ M := by positivity
  calc ∑ n ∈ Finset.Icc X M, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc X (2 ^ M * X), (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hMsub (fun _ _ _ => by positivity)
    _ ≤ (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ M) := key M
    _ ≤ 3 * C / (X : ℝ) := by
        have hCX : (0 : ℝ) ≤ C / (X : ℝ) := by positivity
        have hstep : (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ M) ≤ (C / (X : ℝ)) * 3 :=
          mul_le_mul_of_nonneg_left (by linarith [hgeo]) hCX
        calc (C / (X : ℝ)) * (3 - 2 / (2 : ℝ) ^ M) ≤ (C / (X : ℝ)) * 3 := hstep
          _ = 3 * C / (X : ℝ) := by ring

set_option maxHeartbeats 1000000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `lemma13_moment` + the conjunct `C ≤ 6 * Real.exp 14`.
THE ONLY RESCALE ON THE ROUTE: `C ↦ 3·C`, so `2·e^14 ↦ 6·e^14`. -/
theorem lemma13_moment_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 6 * Real.exp 14 ∧ ∀ (Y₁ X N ℓ : ℕ) (a : ℕ → ℂ) (T : ℝ),
      1 ≤ Y₁ → 1 ≤ X → 0 ≤ T → (∀ n, n < X → a n = 0) →
      (∀ n, ‖a n‖ ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ)) →
      (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
        ≤ (2 * T + 20 * (N : ℝ)) * ((ℓ.factorial : ℝ) ^ 2 * (C / (X : ℝ))) := by
  obtain ⟨C, hC, hCb, hShiuSum⟩ := blockDiv_sq_div_sq_sum_le_bounded
  refine ⟨3 * C, by positivity, by linarith, ?_⟩
  intro Y₁ X N ℓ a T hY₁ hX hT hsupp hcoeff
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hpre : (0 : ℝ) ≤ 2 * T + 20 * (N : ℝ) := by
    have hN := Nat.cast_nonneg (α := ℝ) N; linarith
  -- the coefficient L²-sum bound (eq (17) → (18))
  have hkey : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ (ℓ.factorial : ℝ) ^ 2 * (3 * C / (X : ℝ)) := by
    have hsub : Finset.Icc X N ⊆ Finset.Icc 1 N := by
      intro n hn; rw [Finset.mem_Icc] at *; omega
    have heq : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        = ∑ n ∈ Finset.Icc X N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
      refine (Finset.sum_subset hsub ?_).symm
      intro x hx hxni
      have hxX : x < X := by
        rw [Finset.mem_Icc] at hx
        by_contra h; exact hxni (Finset.mem_Icc.mpr ⟨not_lt.mp h, hx.2⟩)
      rw [hsupp x hxX, norm_zero]; simp
    rw [heq]
    calc ∑ n ∈ Finset.Icc X N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Icc X N,
            ((ℓ.factorial : ℝ) ^ 2 * (blockDiv Y₁ n : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          have h1 : ‖a n‖ ^ 2 ≤ (ℓ.factorial : ℝ) ^ 2 * (blockDiv Y₁ n : ℝ) ^ 2 := by
            nlinarith [hcoeff n, norm_nonneg (a n),
              mul_nonneg (Nat.cast_nonneg (α := ℝ) ℓ.factorial)
                (Nat.cast_nonneg (α := ℝ) (blockDiv Y₁ n))]
          gcongr
      _ = (ℓ.factorial : ℝ) ^ 2
            * ∑ n ∈ Finset.Icc X N, (blockDiv Y₁ n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => by ring)
      _ ≤ (ℓ.factorial : ℝ) ^ 2 * (3 * C / (X : ℝ)) :=
          mul_le_mul_of_nonneg_left (hShiuSum Y₁ X N hY₁ hX) (by positivity)
  -- assemble via the keystone MVT
  calc (∫ t in (-T)..T, ‖spoly N a t‖ ^ 2)
      ≤ (2 * T + 20 * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
        moment_core_bound N a T
    _ ≤ (2 * T + 20 * (N : ℝ)) * ((ℓ.factorial : ℝ) ^ 2 * (3 * C / (X : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey hpre

set_option maxHeartbeats 1000000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `mix_moment` + the conjunct `C ≤ 6 * Real.exp 14`.
pass-through. -/
theorem mix_moment_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 6 * Real.exp 14 ∧ ∀ (Hq : ℝ) (Pq Qq r : ℕ) (Hr : ℝ) (N X Pr Qr v Y₁ Mr X₀ ℓ : ℕ)
      (b c : ℕ → ℂ) (T : ℝ), 1 ≤ Y₁ → 1 ≤ X₀ → 0 ≤ T →
      (∀ p ∈ ramQblock Hq Pq Qq r, Y₁ ≤ p ∧ p ≤ 2 * Y₁) →
      (∀ m ∈ ramRrange Hr N X v, X₀ ≤ m) →
      ramRrange Hr N X v ⊆ Finset.Icc 1 Mr →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∫ t in (-T)..T, ‖ramQ Hq Pq Qq r c t ^ ℓ * ramR Hr N X Pr Qr v b t‖ ^ 2)
        ≤ (2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ))
            * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hCb, hL13⟩ := lemma13_moment_bounded
  refine ⟨C, hC, hCb, ?_⟩
  intro Hq Pq Qq r Hr N X Pr Qr v Y₁ Mr X₀ ℓ b c T hY₁ hX₀ hT hblock hRlow hMr hb hc
  have hMq : ramQblock Hq Pq Qq r ⊆ Finset.Icc 1 (2 * Y₁) := by
    intro p hp
    obtain ⟨hlo, hhi⟩ := hblock p hp
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hint : (∫ t in (-T)..T, ‖ramQ Hq Pq Qq r c t ^ ℓ * ramR Hr N X Pr Qr v b t‖ ^ 2)
      = ∫ t in (-T)..T,
          ‖spoly ((2 * Y₁) ^ ℓ * Mr)
            (⇑(mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ)) t‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [ramQ_pow_mul_ramR_eq_spoly_mix Hq Pq Qq r Hr N X Pr Qr v (2 * Y₁) Mr b c hMq hMr ℓ t]
  rw [hint]
  have hXpos : 1 ≤ Y₁ ^ ℓ * X₀ := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (pow_ne_zero ℓ (by omega)) (by omega))
  exact hL13 Y₁ (Y₁ ^ ℓ * X₀) ((2 * Y₁) ^ ℓ * Mr) ℓ
    (⇑(mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ)) T hY₁ hXpos hT
    (mixCoeff_support_low Hq Pq Qq r Hr N X Pr Qr v Y₁ X₀ b c ℓ
      (fun p hp => (hblock p hp).1) hRlow)
    (coeff_bound_mix Hq Pq Qq r Hr N X Pr Qr v Y₁ hb hc hblock ℓ)

set_option maxHeartbeats 1000000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `cell_bound_raw` + the conjunct `C ≤ 6 * Real.exp 14`.
pass-through. -/
theorem cell_bound_raw_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 6 * Real.exp 14 ∧ ∀ (c b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
      (J j r ℓ N Xd v Y₁ Mr X₀ : ℕ) (T : ℝ) (A : Set ℝ),
      1 ≤ Y₁ → 1 ≤ X₀ → 0 ≤ T → MeasurableSet A → A ⊆ Set.Icc (-T) T →
      A ⊆ TsetGr c Pseq Qseq Hseq αseq J j r →
      (∀ p ∈ ramQblock (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r, Y₁ ≤ p ∧ p ≤ 2 * Y₁) →
      (∀ m ∈ ramRrange (Hseq j) N Xd v, X₀ ≤ m) →
      ramRrange (Hseq j) N Xd v ⊆ Finset.Icc 1 Mr →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
        ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
            * ((2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ))
                * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ)))) := by
  obtain ⟨C, hC, hCb, hmom⟩ := mix_moment_bounded
  refine ⟨C, hC, hCb, ?_⟩
  intro c b Pseq Qseq Hseq αseq J j r ℓ N Xd v Y₁ Mr X₀ T A hY₁ hX₀ hT hAm hAsub hAT
    hblock hRlow hMr hb hc
  -- the entry ticket at the cell
  have hstep := cell_ramR_normalized c b Pseq Qseq Hseq αseq J j r ℓ N Xd v hT A hAm hAsub hAT
  -- the integrand is Lemma 13's, and `A ⊆ [−T,T]` transfers to the full range
  have hcontG : Continuous fun t : ℝ =>
      ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    ((continuous_ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c).norm.pow
      (2 * ℓ)).mul ((continuous_ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b).norm.pow 2)
  have hmono : (∫ t in A, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      ≤ ∫ t in Set.Icc (-T) T,
          ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    setIntegral_mono_set hcontG.integrableOn_Icc
      (Filter.Eventually.of_forall (fun t => by positivity)) hAsub.eventuallyLE
  have hfull : (∫ t in Set.Icc (-T) T,
        ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      = ∫ t in (-T)..T, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
  have hshape : (∫ t in (-T)..T,
        ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      = ∫ t in (-T)..T,
          ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t ^ ℓ
            * ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => norm_pow_mul_sq _ _ ℓ)
  have hL13 := hmom (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r (Hseq j) N Xd
    (Pseq j) (Qseq j) v Y₁ Mr X₀ ℓ b c T hY₁ hX₀ hT hblock hRlow hMr hb hc
  have hE0 : (0 : ℝ)
      ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1)) := (Real.exp_pos _).le
  refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ hE0)
  calc (∫ t in A, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      ≤ ∫ t in (-T)..T, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
        rw [← hfull]; exact hmono
    _ = ∫ t in (-T)..T, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t ^ ℓ
          * ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := hshape
    _ ≤ (2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ))
          * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := hL13

set_option maxHeartbeats 1000000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `cell_bound_pinned` + the conjunct `C ≤ 6 * Real.exp 14`.
pass-through. -/
theorem cell_bound_pinned_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 6 * Real.exp 14 ∧ ∀ (c b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
      (J j r N Xd v : ℕ) (T : ℝ) (A : Set ℝ),
      2 ≤ Hseq (j - 1) → 0 < r → 1 ≤ Xd → 0 ≤ T →
      MeasurableSet A → A ⊆ Set.Icc (-T) T → A ⊆ TsetGr c Pseq Qseq Hseq αseq J j r →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
        ≤ Real.exp (2 * ((ellPin (Hseq j) (Hseq (j - 1)) v r : ℕ) : ℝ) * αseq (j - 1)
              * (r : ℝ) / Hseq (j - 1))
            * ((2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hseq (j - 1))⌉₊)
                      ^ (ellPin (Hseq j) (Hseq (j - 1)) v r)
                    * ⌈2 * ramRbot (Hseq j) Xd v⌉₊ : ℕ) : ℝ))
                * ((((ellPin (Hseq j) (Hseq (j - 1)) v r).factorial : ℕ) : ℝ) ^ 2
                    * (C / (Xd : ℝ)))) := by
  obtain ⟨C, hC, hCb, hraw⟩ := cell_bound_raw_bounded
  refine ⟨C, hC, hCb, ?_⟩
  intro c b Pseq Qseq Hseq αseq J j r N Xd v T A hHp2 hr hXd hT hAm hAsub hAT hb hc
  set Hp : ℝ := Hseq (j - 1) with hHpdef
  set ℓ : ℕ := ellPin (Hseq j) Hp v r with hℓdef
  set Y₁ : ℕ := ⌈Real.exp ((r : ℝ) / Hp)⌉₊ with hY₁def
  set X₀ : ℕ := ⌈ramRbot (Hseq j) Xd v⌉₊ with hX₀def
  set Mr : ℕ := ⌈2 * ramRbot (Hseq j) Xd v⌉₊ with hMrdef
  have hHp0 : (0 : ℝ) < Hp := by rw [hHpdef]; linarith
  have hXdR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hbot : 0 < ramRbot (Hseq j) Xd v := by rw [ramRbot]; positivity
  have hY₁1 : 1 ≤ Y₁ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hX₀1 : 1 ≤ X₀ := Nat.ceil_pos.mpr hbot
  have hstep := hraw c b Pseq Qseq Hseq αseq J j r ℓ N Xd v Y₁ Mr X₀ T A hY₁1 hX₀1 hT
    hAm hAsub hAT (ramQblock_subset_dyadic_block Hp hHp2 (Pseq (j - 1)) (Qseq (j - 1)) r)
    (ramRrange_ceil_bot_le (Hseq j) N Xd v)
    (ramRrange_subset_Icc_sharp (Hseq j) N Xd v Mr (Nat.le_ceil _)) hb hc
  refine le_trans hstep ?_
  -- THE PIN'S SECOND FACE: the Lemma-13 denominator is at least the row length
  have hden : (Xd : ℝ) ≤ ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ) := by
    have h := ellPin_window_bottom_ge (Hseq j) Hp v r Xd hHp0 hr
    push_cast
    exact h
  have hdenpos : (0 : ℝ) < ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ) := lt_of_lt_of_le hXdR hden
  have hCdiv : C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ) ≤ C / (Xd : ℝ) :=
    (div_le_div_iff_of_pos_left hC hdenpos hXdR).mpr hden
  have hfacnn : (0 : ℝ) ≤ ((ℓ.factorial : ℕ) : ℝ) ^ 2 := by positivity
  have hprenn : (0 : ℝ) ≤ 2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hE0 : (0 : ℝ) ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hp) :=
    (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hprenn) hE0
  exact mul_le_mul_of_nonneg_left hCdiv hfacnn

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `Ej_bound_gen` + the conjunct `C ≤ 6 * Real.exp 14`.
pass-through. -/
theorem Ej_bound_gen_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 6 * Real.exp 14 ∧ ∀ (c a b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ) (η : ℝ)
      (Jb j N Xd P1 : ℕ) (X T t₁ row : ℝ),
      LevelGates Pseq Qseq Hseq η P1 Xd j →
      1 ≤ Xd → 0 ≤ T →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      ((∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
            ‖spoly N a t‖ ^ 2)
          ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
              * (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
                  ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
                    ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
            + row) →
      (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
          ‖spoly N a t‖ ^ 2)
        ≤ 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)
              * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
          + row := by
  obtain ⟨C, hC, hCb, hcell⟩ := cell_bound_pinned_bounded
  refine ⟨C, hC, hCb, ?_⟩
  intro c a b Pseq Qseq Hseq η Jb j N Xd P1 X T t₁ row hG hXd hT hb hc hL12
  -- ⟦THE GATES, UNPACKED⟧
  have hη2 : (0 : ℝ) < η / 2 := hG.cell.eta_pos
  have hη : (0 : ℝ) < η := by linarith
  have hj : 2 ≤ j := hG.cell.two_le_j
  have hjR : (2 : ℝ) ≤ (j : ℝ) := hG.cell.jR_two
  have hHj : 2 ≤ Hseq j := hG.two_le_Hj
  have hHp : 2 ≤ Hseq (j - 1) := hG.two_le_Hp
  have hHj0 : (0 : ℝ) < Hseq j := by linarith
  have hHp0 : (0 : ℝ) < Hseq (j - 1) := by linarith
  have hlogQj : (16 : ℝ) ≤ Real.log (Qseq j : ℝ) := hG.logQj_ge
  have hlogPj : (2 : ℝ) ≤ Real.log (Pseq j : ℝ) := hG.logPj_ge
  have hlogPp : (2 : ℝ) ≤ Real.log (Pseq (j - 1) : ℝ) := hG.logPp_ge
  have hlogQp : (2 : ℝ) ≤ Real.log (Qseq (j - 1) : ℝ) := le_trans hlogPp hG.cell.logP_le_logQ
  have hQj1 : 1 ≤ Qseq j := by
    rcases Nat.eq_zero_or_pos (Qseq j) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hlogQj; linarith
    · exact h
  have hPj1 : 1 ≤ Pseq j := by
    rcases Nat.eq_zero_or_pos (Pseq j) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hlogPj; linarith
    · exact h
  have hQjR : (1 : ℝ) ≤ (Qseq j : ℝ) := by exact_mod_cast hQj1
  have hPjR : (0 : ℝ) < (Pseq j : ℝ) := by exact_mod_cast hPj1
  have hQp1 : (1 : ℝ) < (Qseq (j - 1) : ℝ) := hG.cell.one_lt_Qpred
  have hP1R : (0 : ℝ) < (P1 : ℝ) := by exact_mod_cast hG.one_le_P1
  have hXdR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  -- `log 2 ≤ (1/4)loglog Q_j`, from `16 ≤ log Q_j`
  have hlog2 : Real.log 2 ≤ (1 / 4) * Real.log (Real.log (Qseq j : ℝ)) := by
    have h16 : Real.log (16 : ℝ) ≤ Real.log (Real.log (Qseq j : ℝ)) :=
      Real.log_le_log (by norm_num) hlogQj
    have hid : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ (4:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [h16, hid.le, hid.ge]
  -- the SHARP-`M` gate on all of `I_j`
  have hbot : ∀ v ∈ ramI (Hseq j) (Pseq j) (Qseq j), 1 ≤ ramRbot (Hseq j) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI hHj0 hQj1 hG.Qj_le_Xd hv
  -- gate `(3)` at the FULL `η`, from the halved-`η` bundle
  have hg3 : 8 * Real.log (Qseq (j - 1) : ℝ) + 16 * Real.log (j : ℝ)
      ≤ (η / (j : ℝ) ^ 2) * Real.log (Pseq j : ℝ) := by
    have h := hG.cell.gate3
    have hjsq : (0 : ℝ) < (j : ℝ) ^ 2 := by nlinarith
    have hmono : η / 2 / (j : ℝ) ^ 2 ≤ η / (j : ℝ) ^ 2 :=
      (div_le_div_iff_of_pos_right hjsq).mpr (by linarith)
    have hstep := mul_le_mul_of_nonneg_right hmono (by linarith : (0:ℝ) ≤ Real.log (Pseq j : ℝ))
    linarith
  have hkill := level_kill_collected_P1 η j (Pseq j) (Qseq (j - 1)) P1 hj hQp1 hPjR hP1R
    hG.P1_le_Qp hg3
  -- ⟦THE WINDOW⟧
  have hAm : MeasurableSet (seamAnn X T \ seamBall X t₁) :=
    (measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)
  have hAsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  set cp : ℝ := (2 * T / (Xd : ℝ) + 240) * C * Real.exp 3
      * (4 * Real.log (Qseq j : ℝ) ^ 2) * (Qseq (j - 1) : ℝ) ^ 2
      * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2)))) with hcpdef
  -- ⟦THE PER-BLOCK BOUND: gain → covering → cell → the uniform price⟧
  have hstep : ∀ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
      (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
          ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        ≤ ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp := by
    intro v hv
    have hvpos : 0 < v := ramI_pos_of_mem hHj hlogPj hv
    have hufloor : Real.log (Pseq j : ℝ) - 1 / Hseq j ≤ (v : ℝ) / Hseq j :=
      ramI_bottom_deficit hHj0 hv
    have hutop0 : (v : ℝ) / Hseq j ≤ Real.log (Qseq j : ℝ) := ramI_top_le hHj0 hQjR hv
    have hcellB : ∀ r ∈ ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)),
        (∫ t in (seamAnn X T \ seamBall X t₁)
              ∩ TsetGr c Pseq Qseq Hseq (mrAlpha η) Jb j r,
            ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
          ≤ Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j) * cp := by
      intro r hr
      have hrpos : 0 < r := ramI_pos_of_mem hHp hlogPp hr
      have hlow : Real.log (Pseq (j - 1) : ℝ) - 1 ≤ (r : ℝ) / Hseq (j - 1) := by
        have h := ramI_bottom_deficit hHp0 hr
        have h2 : 1 / Hseq (j - 1) ≤ 1 := by
          rw [div_le_one hHp0]; linarith
        linarith
      have hstop : (r : ℝ) / Hseq (j - 1) ≤ Real.log (Qseq (j - 1) : ℝ) :=
        ramI_top_le hHp0 (by linarith) hr
      have hcb := hcell c b Pseq Qseq Hseq (mrAlpha η) Jb j r N Xd v T _
        hHp hrpos hXd hT
        (measurableSet_annulus_TsetGr c Pseq Qseq Hseq (mrAlpha η) Jb j r X T t₁)
        (annulus_TsetGr_subset_Icc c Pseq Qseq Hseq (mrAlpha η) Jb j r X T t₁)
        Set.inter_subset_right hb hc
      have hcp := cell_price_uniform η T C (Real.log (Pseq (j - 1) : ℝ) - 1)
        (Hseq j) (Hseq (j - 1)) j v r Xd (Pseq j) (Qseq j) (Qseq (j - 1))
        hη hG.eta_lt6 hj hHj hHp hC hT hXd hvpos hrpos (by linarith) hlow
        (by linarith) (by linarith) hstop (by linarith) hufloor hPjR (hbot v hv)
        hG.cell.gate2 hlog2
      rw [← hcpdef] at hcp
      refine le_trans hcb ?_
      have hE : Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j)
          * Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j) = 1 := by
        rw [← Real.exp_add,
          show 2 * mrAlpha η j * (v : ℝ) / Hseq j
              + -(2 * mrAlpha η j) * (v : ℝ) / Hseq j = 0 by ring, Real.exp_zero]
      have h2 := mul_le_mul_of_nonneg_left hcp
        (Real.exp_pos (2 * mrAlpha η j * (v : ℝ) / Hseq j)).le
      rw [← mul_assoc, hE, one_mul] at h2
      exact h2
    have hcov := integral_TsetG_le_card_mul c Pseq Qseq Hseq (mrAlpha η) Jb j hj
      ((continuous_ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b).norm.pow 2)
      (fun t => sq_nonneg _) hT (seamAnn X T \ seamBall X t₁) hAm hAsub _ hcellB
    have hgain := integral_ramMain_le_exp_mul_ramR c b Pseq Qseq Hseq (mrAlpha η) Jb j N Xd T
      ((seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j)
      (hAm.inter (measurableSet_TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j))
      (fun _ ht => hAsub ht.1) Set.inter_subset_right v hv
    have hE' : Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j)
        * Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j) = 1 := by
      rw [← Real.exp_add,
        show -(2 * mrAlpha η j) * (v : ℝ) / Hseq j
            + 2 * mrAlpha η j * (v : ℝ) / Hseq j = 0 by ring, Real.exp_zero]
    calc (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
            ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        ≤ Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j)
            * ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
                ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := hgain
      _ ≤ Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j)
            * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
                * (Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j) * cp)) :=
          mul_le_mul_of_nonneg_left hcov (Real.exp_pos _).le
      _ = (Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j)
              * Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j))
            * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp) := by
          ring
      _ = ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp := by
          rw [hE', one_mul]
  -- ⟦THE `v`-SUM: free, the summand is `v`-independent⟧
  have hsum : (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
        ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
          ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
      ≤ ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
          * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp) := by
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  -- ⟦THE GEOMETRY AND THE KILL⟧
  have hTX0 : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) + 240 := by
    have h : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) := div_nonneg (by linarith) hXdR.le
    linarith
  have hGpos : (0 : ℝ) ≤ (2 * T / (Xd : ℝ) + 240) * C * Real.exp 3 :=
    mul_nonneg (mul_nonneg hTX0 hC.le) (Real.exp_pos 3).le
  have hPjrpow : (0 : ℝ) ≤ (Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))) :=
    Real.rpow_nonneg hPjR.le _
  have hc1 : ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
      ≤ 2 * (Hseq j * Real.log (Qseq j : ℝ)) := ramI_card_two_mul _ _ (by nlinarith)
  have hc2 : ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
      ≤ 2 * (Hseq (j - 1) * Real.log (Qseq (j - 1) : ℝ)) := ramI_card_two_mul _ _ (by nlinarith)
  have hgeom := level_geometry_collapse (Hseq j) (Hseq (j - 1)) j P1 (Qseq j) (Qseq (j - 1))
    hG.Hp_le_Hj (by linarith) (by linarith) hG.cell.logQ_le_rpow_of_gate2 (by linarith)
    hG.Hj_pin hG.P1_le_Qp
  have hcardgeom : 2 * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)) ^ 2
        * ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
        * (4 * Real.log (Qseq j : ℝ) ^ 2) * (Qseq (j - 1) : ℝ) ^ 2
      ≤ 1536 * (j : ℝ) ^ 6 * (Qseq (j - 1) : ℝ) ^ 3 := by
    refine le_trans ?_ hgeom
    have h1 : (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)) ^ 2
        ≤ (2 * (Hseq j * Real.log (Qseq j : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hc1 2
    have hA : 2 * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)) ^ 2
        ≤ 2 * (2 * (Hseq j * Real.log (Qseq j : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hB := mul_le_mul hA hc2 (Nat.cast_nonneg _) (by positivity)
    have hD := mul_le_mul_of_nonneg_right hB
      (by positivity : (0:ℝ) ≤ 4 * Real.log (Qseq j : ℝ) ^ 2)
    exact mul_le_mul_of_nonneg_right hD (by positivity)
  have hmain : 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
        * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
            * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp))
      ≤ 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)
          * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ))) := by
    rw [hcpdef]
    calc 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
            * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
                * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
                    * ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3
                        * (4 * Real.log (Qseq j : ℝ) ^ 2) * (Qseq (j - 1) : ℝ) ^ 2
                        * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2)))))))
        = (2 * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)) ^ 2
              * ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
              * (4 * Real.log (Qseq j : ℝ) ^ 2) * (Qseq (j - 1) : ℝ) ^ 2)
            * (((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3)
                * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))))) := by ring
      _ ≤ (1536 * (j : ℝ) ^ 6 * (Qseq (j - 1) : ℝ) ^ 3)
            * (((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3)
                * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))))) :=
          mul_le_mul_of_nonneg_right hcardgeom (mul_nonneg hGpos hPjrpow)
      _ = ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3 * 1536)
            * ((j : ℝ) ^ 6 * (Qseq (j - 1) : ℝ) ^ 3
                * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))))) := by ring
      _ ≤ ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3 * 1536)
            * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hkill (mul_nonneg hGpos (by norm_num))
      _ = 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)
            * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ))) := by ring
  -- ⟦THE CARRIED LEMMA-12 ROW⟧
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0:ℝ) ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ))
  linarith [hL12, hscaled, hmain]

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `TLeg_bound_gen` + the conjunct `C ≤ 6 * Real.exp 14`.
pass-through. -/
theorem TLeg_bound_gen_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 6 * Real.exp 14 ∧ ∀ (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
      (η : ℝ) (Jb N Xd P1 : ℕ) (X T t₁ : ℝ) (row : ℕ → ℝ),
      0 < η → η < 1 / 6 → 1 ≤ Jb → 1 ≤ Xd → 0 ≤ T → (0 : ℝ) < (P1 : ℝ) →
      (∀ j ∈ Finset.Icc 2 Jb, LevelGates Pseq Qseq Hseq η P1 Xd j) →
      2 ≤ Hseq 1 → 1 ≤ Pseq 1 → Pseq 1 ≤ Qseq 1 →
      (∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) →
      (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ j ∈ Finset.Icc 1 Jb,
        (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
            ‖spoly N a t‖ ^ 2)
          ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
              * (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
                  ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
                    ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) (b j) c v t‖ ^ 2)
            + row j) →
      (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtotG c Pseq Qseq Hseq (mrAlpha η) Jb,
          ‖spoly N a t‖ ^ 2)
        ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
              * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
              * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
              * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
                    * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
                  + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
          + 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240) * (1 / (P1 : ℝ))
          + ∑ j ∈ Finset.Icc 1 Jb, row j := by
  obtain ⟨C, hC, hCb, hEj⟩ := Ej_bound_gen_bounded
  refine ⟨C, hC, hCb, ?_⟩
  intro c a b Pseq Qseq Hseq η Jb N Xd P1 X T t₁ row hη h6 hJb hXd hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hb hc hrow
  have hXdR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  obtain ⟨hα1, hα1', -⟩ := alpha_gates_from_eta η hη h6
  -- ⟦THE SPLIT OVER THE DISJOINT LEVELS⟧
  have hAm : MeasurableSet (seamAnn X T \ seamBall X t₁) :=
    (measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)
  have hAsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  have hadd := seam_T_additivityG (f := c) (Pseq := Pseq) (Qseq := Qseq) (Hseq := Hseq)
    (αseq := mrAlpha η) (J := Jb) (F := fun t : ℝ => ‖spoly N a t‖ ^ 2)
    ((continuous_spoly N a).norm.pow 2) hT hAm hAsub
  have hIcc : Finset.Icc 1 Jb = insert 1 (Finset.Icc 2 Jb) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 Jb := by simp
  -- ⟦LEVEL 1: MR §8.1 at the pins⟧
  have h1 := E1_pin_gen c Pseq Qseq Hseq (mrAlpha η) Jb hH1 hα1 hα1' N Xd hXd hP1s hPQ1 a (b 1)
    (hb 1) X T t₁ hT hbot1 (row 1) (hrow 1 (by simp [Finset.mem_Icc]; omega))
  -- ⟦LEVELS `j ≥ 2`: MR §8.2⟧
  have h2 : ∀ j ∈ Finset.Icc 2 Jb,
      (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
          ‖spoly N a t‖ ^ 2)
        ≤ (1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)) * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
          + row j := by
    intro j hj
    have hj1 : j ∈ Finset.Icc 1 Jb := by
      rw [Finset.mem_Icc] at hj ⊢
      omega
    have h := hEj c a (b j) Pseq Qseq Hseq η Jb j N Xd P1 X T t₁ (row j) (hG j hj) hXd hT
      (hb j) hc (hrow j hj1)
    calc (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
            ‖spoly N a t‖ ^ 2)
        ≤ 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)
              * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
            + row j := h
      _ = (1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)) * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
            + row j := by ring
  have hK0 : (0 : ℝ) ≤ 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240) := by
    have hTX0 : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) + 240 := by
      have h : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) := div_nonneg (by linarith) hXdR.le
      linarith
    exact mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1536 * C) (Real.exp_pos 3).le) hTX0
  have hcol := sum_Ej_collected (1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)) hK0 P1 Jb hP1
    (fun j => ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
      ‖spoly N a t‖ ^ 2)
    (fun j => row j) h2
  -- ⟦THE ASSEMBLY⟧
  rw [hadd, hIcc, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem]
  linarith [h1, hcol]

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `TLeg_feeds_capstone_gen` + the conjunct `C ≤ 6 * Real.exp 14`.
pass-through. -/
theorem TLeg_feeds_capstone_gen_bounded :
    ∃ C : ℝ, 0 < C ∧ C ≤ 6 * Real.exp 14 ∧ ∀ (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
      (η : ℝ) (Jset N Xd P1 : ℕ) (X Tann t₁ S ε : ℝ) (row : ℕ → ℝ),
      0 < η → η < 1 / 6 → 1 ≤ Jset → 1 ≤ Xd → 0 ≤ Tann → (0 : ℝ) < (P1 : ℝ) →
      (∀ j ∈ Finset.Icc 2 Jset, LevelGates Pseq Qseq Hseq η P1 Xd j) →
      2 ≤ Hseq 1 → 1 ≤ Pseq 1 → Pseq 1 ≤ Qseq 1 →
      (∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) →
      (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ j ∈ Finset.Icc 1 Jset,
        (∫ t in (seamAnn X Tann \ seamBall X t₁)
              ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jset j, ‖spoly N a t‖ ^ 2)
          ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
              * (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
                  ∫ t in (seamAnn X Tann \ seamBall X t₁)
                      ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jset j,
                    ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) (b j) c v t‖ ^ 2)
            + row j) →
      -- ⟦THE CAPSTONE ROW⟧ `GradedCapstone.hUG34_unconditional`'s conclusion, verbatim,
      -- at `fb := c` and `αseq := mrAlpha η`
      (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG c Pseq Qseq Hseq (mrAlpha η) Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) →
      (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
        ≤ 8 * S ^ 2
          + (2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
                * (Tann * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
                * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
                * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
                      * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
                    + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
              + 1536 * C * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240) * (1 / (P1 : ℝ))
              + ∑ j ∈ Finset.Icc 1 Jset, row j)
          + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨C, hC, hCb, hleg⟩ := TLeg_bound_gen_bounded
  refine ⟨C, hC, hCb, ?_⟩
  intro c a b Pseq Qseq Hseq η Jset N Xd P1 X Tann t₁ S ε row hη h6 hJ hXd hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hb hc hrow hcap
  have h := hleg c a b Pseq Qseq Hseq η Jset N Xd P1 X Tann t₁ row hη h6 hJ hXd hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hb hc hrow
  linarith [hcap, h]

set_option maxHeartbeats 2000000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `m4_rowChi_number_of_capstone_zero'` + the conjunct `Ct ≤ 6 * Real.exp 14`.
pass-through (the row as a number). -/
theorem m4_rowChi_number_of_capstone_zero'_bounded :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 6 * Real.exp 14 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X Tann t₁ S η ε : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        0 ≤ Tann → 2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE STRICT RELATIVIZED PAIR LAW, UNTWISTED⟧
        (∀ j ∈ Finset.Icc 1 Jb,
          SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        -- ⟦THE `𝒮`-SUPPORT⟧ in place of the density gate
        (∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) →
        -- ⟦THE RECONCILIATION GATES (R1), (R2)⟧ — (R4) is GONE
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        -- ⟦THE A3 CAPSTONE ROW, CARRIED⟧
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S ^ 2
              + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) →
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Ct * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 24 / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + Cp * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Ct, hCt, hCtb, hfeed⟩ := TLeg_feeds_capstone_gen_bounded
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro Cp hCp q _ χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X Tann t₁ S η ε hF hT0 hNXd hN4
    hcoefWS hasupp hlive hQXd hXdbig hcap
  -- ⟦THE FRAME'S OWN READS⟧
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hM1 := hF.one_le_M
  have hA2 : 2 ≤ A := le_trans (by norm_num) hF.A_floor
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1two : (2 : ℝ) ≤ calH H1 1 := by rw [hcalH1]; exact hF.H1_two
  have hP1nat : 1 ≤ calP A G 1 := by simp only [calP]; exact Nat.one_le_two_pow
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) := by exact_mod_cast hP1nat
    linarith
  have hQ1Xd : calQK A G M 1 ≤ Xd := le_trans (calQK_mono A hG1 hJb1) hF.Q_le_Xd
  have hbot1 : ∀ v ∈ ramI (calH H1 1) (calP A G 1) (calQK A G M 1),
      1 ≤ ramRbot (calH H1 1) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI (by linarith) (one_le_calQK A G M 1) hQ1Xd hv
  have hHj : ∀ j ∈ Finset.Icc 1 Jb, (2 : ℝ) ≤ calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    rw [calH]
    nlinarith [hF.H1_two]
  have hPj1 : ∀ j : ℕ, 1 ≤ calP A G j := fun j => by
    simp only [calP]; exact Nat.one_le_two_pow
  have hasuppχ := chiBarCoeff_dyadic_supp χ hasupp
  -- ⟦THE ROW SLOT, AT THE FOUR-ROW STRICT/FUSED EXIT⟧
  have hrowfam : ∀ j ∈ Finset.Icc 1 Jb,
      (∫ t in (seamAnn X Tann \ seamBall X t₁)
            ∩ TsetG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1) (mrAlpha η) Jb j,
          ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 2 * ((ramI (calH H1 j) (calP A G j) (calQK A G M j)).card : ℝ)
            * (∑ v ∈ ramI (calH H1 j) (calP A G j) (calQK A G M j),
                ∫ t in (seamAnn X Tann \ seamBall X t₁)
                    ∩ TsetG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                        (mrAlpha η) Jb j,
                  ‖ramMain (calH H1 j) N Xd (calP A G j) (calQK A G M j)
                    (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) v t‖ ^ 2)
          + lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann
              (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) := by
    intro j hj
    exact lemma12_on_TsetG_mr_windowed_end (chiBarCoeff q χ c) (calP A G) (calQK A G M)
      (calH H1) (mrAlpha η) Jb j (hHj j hj) N Xd hXd1 hNXd (hPj1 j)
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c)
      (chiBarCoeff_seamCoefWS χ (hcoefWS j hj)) (chiBarCoeff_bfam_le_one χ hb1 j)
      (chiBarCoeff_cseq_le_one χ hc1) (hasupp_real_of_nat hasuppχ) X Tann t₁ hT0
  have hleg := hfeed (chiBarCoeff q χ c) (chiBarCoeff q χ a)
    (fun j => chiBarCoeff q χ (bfam j)) (calP A G) (calQK A G M) (calH H1) η Jb N Xd
    (calP A G 1) X Tann t₁ S ε
    (fun j => lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c))
    hη hη6 hJb1 hXd1 hT0 hP1pos (levelGates_calibratedK hF) hH1two hP1nat
    (calP_le_calQK hM1 le_rfl) hbot1 (chiBarCoeff_bfam_le_one χ hb1)
    (chiBarCoeff_cseq_le_one χ hc1) hrowfam hcap
  -- ⟦THE PRICE OF `Σ_j lemma12RowsMR_end`, AT THE TWISTED `𝒮`-SUPPORTED DATUM⟧
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  have hK2 := sum_lemma12RowsMR_priced_chi_end_zero' Cp hCp q χ A G M Jb N Xd H1 Tann a c bfam
    hA2 hG1 hM1 hXd1 hNXd hT0 hF.H1_two hN4 hreg hXdbig ha1 hb1 hc1 hlive
  exact hleg.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2)) le_rfl)

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `m4_hrowsSum_chi_zero'` + the conjunct `Ct ≤ 6 * Real.exp 14`.
pass-through. -/
theorem m4_hrowsSum_chi_zero'_bounded :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 6 * Real.exp 14 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X h η ε : ℝ)
        (t₁ S : DirichletCharacter ℂ q → ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        (∀ j ∈ Finset.Icc 1 Jb, BlockLive (calP A G j) (calQK A G M j) a) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK A G M 1 : ℕ) : ℝ) ≤ h →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S χ ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ m4MrowChiEnd' Ct Cp A G M Jb Xd H1 η X ε (S χ) := by
  obtain ⟨Ct, hCt, hCtb, hnum⟩ := m4_rowChi_number_of_capstone_zero'_bounded
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro Cp hCp q _ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X h η ε t₁ S hF hNXd hN4 hcoefWS
    hasupp hlive hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hrow := hnum Cp hCp q χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X (2 * T) (t₁ χ) (S χ) η ε
    hF (by linarith) hNXd hN4 hcoefWS hasupp hlive hQXd hXdbig
    (hcap χ T hT hTX2 hTgate hTll)
  exact m4_rowChi_weighed_end' hXd1 hF.H1_two hF.eta_pos hF.eta_lt hCt.le hCp hF.one_le_M
    hh4 hX0 hL0 hX4Xd hQ1h hT hrow

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `m4_hrowsSum_chi_door_zero'_L_gk` + the conjunct `Ct ≤ 6 * Real.exp 14`.
pass-through at the linear door. -/
theorem m4_hrowsSum_chi_door_zero'_L_gk_bounded (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 6 * Real.exp 14 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            (winCutH Xd (doorCoeffU_L_gk K M)) (bfam j) c) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ a2Mrow'_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hCtb, hrows⟩ := m4_hrowsSum_chi_zero'_bounded
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_L_gk K M)) bfam ha1 hb1 hc1 N Xd
    (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_L_gk K M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_L_gk K hM hXd1 hCp

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦Ct BOUNDED TWIN⟧** `m4_hrowsSlot_at_door_zero'_L_gk` + the conjunct `Ct ≤ 6 * Real.exp 14`.
⟦THE TOP UNFENCED HOP OF ROUTE 2⟧ — the compose pass's hook. -/
theorem m4_hrowsSlot_at_door_zero'_L_gk_bounded (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 6 * Real.exp 14 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hCtb, hrows⟩ := m4_hrowsSum_chi_door_zero'_L_gk_bounded K hK
  refine ⟨Ct, hCt, hCtb, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

/-! ## §14 — the ceiling in the terminal's own shape -/

/-- `6·e^14 ≤ 2^23` — the rider's numeral, at 86% of the ceiling
(`6·e^14 = 7215625.7`, `2^23 = 8388608`). -/
theorem six_exp_fourteen_le_two_pow_23 : 6 * Real.exp 14 ≤ 2 ^ 23 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have h2 : Real.exp 14 = Real.exp 1 ^ (14 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 1 ^ (14 : ℕ) ≤ (2.7182818286 : ℝ) ^ (14 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h1 14
  rw [h2]
  nlinarith [h3]

set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
/-- **⟦THE COMPOSE HOOK OF ROUTE 2⟧** — `m4_hrowsSlot_at_door_zero'_L_gk_bounded`
with the ceiling stated in the terminal's own numeral `2^23`. -/
theorem m4_hrowsSlot_at_door_zero'_L_gk_ceiling (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧ Ct ≤ 2 ^ 23 ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hCtb, hslot⟩ := m4_hrowsSlot_at_door_zero'_L_gk_bounded K hK
  exact ⟨Ct, hCt, le_trans hCtb six_exp_fourteen_le_two_pow_23, hslot⟩

end Salt.MR
