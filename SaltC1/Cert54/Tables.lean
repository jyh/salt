/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.Cert54.Checks

/-!
# C1 — the `k = 54` certificate's tables, certified

Every table of `SaltC1.Cert54.Data` against its definition, by `decide +kernel` on the literal data:
`factT` is `n!`; `gT46`/`gT48` are the coefficients of `GM 13` (`checkG`); `p54T`/`p53T` satisfy the
Miller power recurrence of `GM 13 ^ 54` / `GM 13 ^ 53` at every key, the box and its coefficients
generated in the kernel (`checkRecGen`); `WItree`/`WJtree` are the closed forms (`checkWI`,
`checkWJ`); `WBT` is the collected marginal of the coefficient vector (`checkWChain`).

The kernel's memory grows with the work one declaration does, so each check is cut into shard
theorems of bounded work (`scripts/c1/lean_cert54.py` writes this file); each shard generates only
its own block `keysRange w lo hi` of the key list. The whole-list theorems (`g46_ok`, `rec54_ok`,
`wi_ok`, …) are derived from the shards by the list lemmas below — no `decide`. Nothing here bears
on twin primes.
-/

set_option maxRecDepth 1000000
set_option linter.style.longLine false
-- One theorem at a time, and nothing of a checked theorem kept: with asynchronous elaboration each
-- theorem's snapshot is retained to the end of the file, and a file of these theorems grows to
-- ~15 GB (measured); synchronously the file's peak is its largest theorem's (~3 GB).
set_option Elab.async false

namespace SaltC1.Cert54

/-! ## Assembling shards: list lemmas, no `decide` -/

theorem checkAllL_append {α : Type} (f : α → Bool) (l₁ l₂ : List α) :
    checkAllL f (l₁ ++ l₂) = (checkAllL f l₁ && checkAllL f l₂) := by
  simp [checkAllL, List.all_append]

/-- A tail is checked once its next `n` elements and the tail after them are. -/
theorem checkAllL_drop_of {α : Type} (f : α → Bool) (L : List α) (s n : Nat)
    (h₁ : checkAllL f ((L.drop s).take n) = true) (h₂ : checkAllL f (L.drop (s + n)) = true) :
    checkAllL f (L.drop s) = true := by
  have h : L.drop s = (L.drop s).take n ++ L.drop (s + n) := by
    conv_lhs => rw [← List.take_append_drop n (L.drop s)]
    rw [List.drop_drop]
  rw [h, checkAllL_append, h₁, h₂]
  rfl

theorem checkAllL_of_drop_zero {α : Type} {f : α → Bool} {L : List α}
    (h : checkAllL f (L.drop 0) = true) : checkAllL f L = true := by
  simpa using h

theorem keysRange_append (w a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    keysRange w a c = keysRange w a b ++ keysRange w b c := by
  unfold keysRange
  have hc : c - a = (b - a) + (c - b) := by omega
  rw [hc, List.range_add, List.flatMap_append, List.flatMap_map]
  congr 2
  funext t
  have : a + (b - a + t) = b + t := by omega
  rw [this]

/-- `keysW 13 w` is the block of all `c₁ ∈ [0, w/2 + 1)`. -/
theorem keysW_eq_keysRange (w n : Nat) (hn : n = w / 2 + 1) : keysW 13 w = keysRange w 0 n := by
  subst hn
  have h : keysW 13 w = keysW (12 + 1) w := rfl
  rw [h, keysW, keysRange]
  simp

theorem checkAllL_keysRange_append (f : List Nat → Bool) (w a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : checkAllL f (keysRange w a b) = true) (h₂ : checkAllL f (keysRange w b c) = true) :
    checkAllL f (keysRange w a c) = true := by
  rw [keysRange_append w a b c hab hbc, checkAllL_append, h₁, h₂]
  rfl

theorem checkAllL_wiEntriesR_append (f : FEntry → Bool) (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : checkAllL f (wiEntriesR a b) = true) (h₂ : checkAllL f (wiEntriesR b c) = true) :
    checkAllL f (wiEntriesR a c) = true := by
  unfold wiEntriesR at *
  rw [keysRange_append 46 a b c hab hbc, List.flatMap_append, checkAllL_append, h₁, h₂]
  rfl

theorem checkAllL_wjEntriesR_append (f : FEntry → Bool) (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : checkAllL f (wjEntriesR a b) = true) (h₂ : checkAllL f (wjEntriesR b c) = true) :
    checkAllL f (wjEntriesR a c) = true := by
  unfold wjEntriesR at *
  rw [keysRange_append 48 a b c hab hbc, List.flatMap_append, checkAllL_append, h₁, h₂]
  rfl

theorem wiEntries_eq_R : wiEntries = wiEntriesR 0 24 := by
  unfold wiEntries wiEntriesR
  rw [keysW_eq_keysRange 46 24 rfl]

theorem wjEntries_eq_R : wjEntries = wjEntriesR 0 25 := by
  unfold wjEntries wjEntriesR
  rw [keysW_eq_keysRange 48 25 rfl]

/-- A marginal fold state shifted by a count `c` and a flag `o`. -/
def wShift (c : Nat) (o : Bool) (q : Nat × Nat × Nat × Bool) : Nat × Nat × Nat × Bool :=
  (q.1, q.2.1, c + q.2.2.1, o && q.2.2.2)

theorem wShardStep_shift (c : Nat) (o : Bool) (q : Nat × Nat × Nat × Bool) (s : List WTerm) :
    wShardStep (wShift c o q) s = wShift c o (wShardStep q s) := by
  obtain ⟨p, k, c', o'⟩ := q
  simp only [wShift, wShardStep, Nat.add_assoc, Bool.and_assoc]

theorem wShards_foldl_shift (sh : List (List WTerm)) :
    ∀ (c : Nat) (o : Bool) (q : Nat × Nat × Nat × Bool),
      sh.foldl wShardStep (wShift c o q) = wShift c o (sh.foldl wShardStep q) := by
  induction sh with
  | nil => intro c o q; rfl
  | cons s ss ih => intro c o q; simp only [List.foldl_cons, wShardStep_shift, ih]

theorem wfold_of_chain {sh : List (List WTerm)} {p k p' k' c' : Nat} {o' : Bool}
    (h : checkWChain sh p k = (o', p', k', c')) :
    sh.foldl wShardStep (p, k, 0, true) = (p', k', c', o') := by
  simp only [checkWChain, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h1))

/-! ## The factorial table and the series' constant terms -/

theorem fact_ok : checkFact = true := by decide +kernel
theorem p54_zero : p54T.findB 0 = 1 := by decide +kernel
theorem p53_zero : p53T.findB 0 = 1 := by decide +kernel

/-! ## `checkG gT46` over the keys of weight `≤ 46`: 4 shards -/

theorem g46_ok_0 : checkAllL (checkG gT46) (keysRange 46 0 1) = true := by decide +kernel
theorem g46_ok_1 : checkAllL (checkG gT46) (keysRange 46 1 3) = true := by decide +kernel
theorem g46_ok_2 : checkAllL (checkG gT46) (keysRange 46 3 7) = true := by decide +kernel
theorem g46_ok_3 : checkAllL (checkG gT46) (keysRange 46 7 24) = true := by decide +kernel

/-- `checkG gT46` on every key of weight `≤ 46`, from the shards. -/
theorem g46_ok : checkAllL (checkG gT46) (keysW 13 46) = true := by
  rw [keysW_eq_keysRange 46 24 rfl]
  exact (checkAllL_keysRange_append _ 46 0 1 24 (by omega) (by omega) (g46_ok_0)
    (checkAllL_keysRange_append _ 46 1 3 24 (by omega) (by omega) (g46_ok_1)
    (checkAllL_keysRange_append _ 46 3 7 24 (by omega) (by omega) (g46_ok_2)
    (g46_ok_3))))

/-! ## `checkG gT48` over the keys of weight `≤ 48`: 5 shards -/

theorem g48_ok_0 : checkAllL (checkG gT48) (keysRange 48 0 1) = true := by decide +kernel
theorem g48_ok_1 : checkAllL (checkG gT48) (keysRange 48 1 2) = true := by decide +kernel
theorem g48_ok_2 : checkAllL (checkG gT48) (keysRange 48 2 4) = true := by decide +kernel
theorem g48_ok_3 : checkAllL (checkG gT48) (keysRange 48 4 8) = true := by decide +kernel
theorem g48_ok_4 : checkAllL (checkG gT48) (keysRange 48 8 25) = true := by decide +kernel

/-- `checkG gT48` on every key of weight `≤ 48`, from the shards. -/
theorem g48_ok : checkAllL (checkG gT48) (keysW 13 48) = true := by
  rw [keysW_eq_keysRange 48 25 rfl]
  exact (checkAllL_keysRange_append _ 48 0 1 25 (by omega) (by omega) (g48_ok_0)
    (checkAllL_keysRange_append _ 48 1 2 25 (by omega) (by omega) (g48_ok_1)
    (checkAllL_keysRange_append _ 48 2 4 25 (by omega) (by omega) (g48_ok_2)
    (checkAllL_keysRange_append _ 48 4 8 25 (by omega) (by omega) (g48_ok_3)
    (g48_ok_4)))))

/-! ## `checkRecGen p54T gT46 54` over the keys of weight `≤ 46`: 52 shards -/

theorem rec54_ok_0 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 0 1).drop 0).take 397) = true := by decide +kernel
theorem rec54_ok_1 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 0 1).drop 397).take 251) = true := by decide +kernel
theorem rec54_ok_2 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 0 1).drop 648).take 184) = true := by decide +kernel
theorem rec54_ok_3 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 0 1).drop 832).take 139) = true := by decide +kernel
theorem rec54_ok_4 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 0 1).drop 971).take 125) = true := by decide +kernel
theorem rec54_ok_5 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 0 1).drop 1096) = true := by decide +kernel
theorem rec54_ok_6 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 1 2).drop 0).take 286) = true := by decide +kernel
theorem rec54_ok_7 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 1 2).drop 286).take 193) = true := by decide +kernel
theorem rec54_ok_8 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 1 2).drop 479).take 130) = true := by decide +kernel
theorem rec54_ok_9 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 1 2).drop 609).take 97) = true := by decide +kernel
theorem rec54_ok_10 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 1 2).drop 706).take 98) = true := by decide +kernel
theorem rec54_ok_11 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 1 2).drop 804).take 86) = true := by decide +kernel
theorem rec54_ok_12 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 1 2).drop 890) = true := by decide +kernel
theorem rec54_ok_13 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 2 3).drop 0).take 231) = true := by decide +kernel
theorem rec54_ok_14 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 2 3).drop 231).take 154) = true := by decide +kernel
theorem rec54_ok_15 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 2 3).drop 385).take 102) = true := by decide +kernel
theorem rec54_ok_16 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 2 3).drop 487).take 82) = true := by decide +kernel
theorem rec54_ok_17 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 2 3).drop 569).take 80) = true := by decide +kernel
theorem rec54_ok_18 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 2 3).drop 649).take 73) = true := by decide +kernel
theorem rec54_ok_19 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 2 3).drop 722) = true := by decide +kernel
theorem rec54_ok_20 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 3 4).drop 0).take 194) = true := by decide +kernel
theorem rec54_ok_21 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 3 4).drop 194).take 130) = true := by decide +kernel
theorem rec54_ok_22 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 3 4).drop 324).take 89) = true := by decide +kernel
theorem rec54_ok_23 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 3 4).drop 413).take 74) = true := by decide +kernel
theorem rec54_ok_24 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 3 4).drop 487).take 63) = true := by decide +kernel
theorem rec54_ok_25 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 3 4).drop 550) = true := by decide +kernel
theorem rec54_ok_26 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 4 5).drop 0).take 169) = true := by decide +kernel
theorem rec54_ok_27 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 4 5).drop 169).take 107) = true := by decide +kernel
theorem rec54_ok_28 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 4 5).drop 276).take 78) = true := by decide +kernel
theorem rec54_ok_29 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 4 5).drop 354).take 64) = true := by decide +kernel
theorem rec54_ok_30 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 4 5).drop 418) = true := by decide +kernel
theorem rec54_ok_31 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 5 6).drop 0).take 154) = true := by decide +kernel
theorem rec54_ok_32 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 5 6).drop 154).take 87) = true := by decide +kernel
theorem rec54_ok_33 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 5 6).drop 241).take 72) = true := by decide +kernel
theorem rec54_ok_34 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 5 6).drop 313).take 58) = true := by decide +kernel
theorem rec54_ok_35 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 5 6).drop 371) = true := by decide +kernel
theorem rec54_ok_36 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 6 7).drop 0).take 142) = true := by decide +kernel
theorem rec54_ok_37 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 6 7).drop 142).take 77) = true := by decide +kernel
theorem rec54_ok_38 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 6 7).drop 219).take 58) = true := by decide +kernel
theorem rec54_ok_39 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 6 7).drop 277) = true := by decide +kernel
theorem rec54_ok_40 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 7 8).drop 0).take 129) = true := by decide +kernel
theorem rec54_ok_41 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 7 8).drop 129).take 67) = true := by decide +kernel
theorem rec54_ok_42 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 7 8).drop 196) = true := by decide +kernel
theorem rec54_ok_43 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 8 9).drop 0).take 114) = true := by decide +kernel
theorem rec54_ok_44 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 8 9).drop 114) = true := by decide +kernel
theorem rec54_ok_45 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 9 10).drop 0).take 105) = true := by decide +kernel
theorem rec54_ok_46 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 9 10).drop 105) = true := by decide +kernel
theorem rec54_ok_47 : checkAllL (checkRecGen p54T gT46 54) (((keysRange 46 10 11).drop 0).take 95) = true := by decide +kernel
theorem rec54_ok_48 : checkAllL (checkRecGen p54T gT46 54) ((keysRange 46 10 11).drop 95) = true := by decide +kernel
theorem rec54_ok_49 : checkAllL (checkRecGen p54T gT46 54) (keysRange 46 11 12) = true := by decide +kernel
theorem rec54_ok_50 : checkAllL (checkRecGen p54T gT46 54) (keysRange 46 12 14) = true := by decide +kernel
theorem rec54_ok_51 : checkAllL (checkRecGen p54T gT46 54) (keysRange 46 14 24) = true := by decide +kernel

/-- `checkRecGen p54T gT46 54` on every key of weight `≤ 46`, from the shards. -/
theorem rec54_ok : checkAllL (checkRecGen p54T gT46 54) (keysW 13 46) = true := by
  rw [keysW_eq_keysRange 46 24 rfl]
  exact (checkAllL_keysRange_append _ 46 0 1 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 397 rec54_ok_0 (checkAllL_drop_of _ _ 397 251 rec54_ok_1 (checkAllL_drop_of _ _ 648 184 rec54_ok_2 (checkAllL_drop_of _ _ 832 139 rec54_ok_3 (checkAllL_drop_of _ _ 971 125 rec54_ok_4 (rec54_ok_5)))))))
    (checkAllL_keysRange_append _ 46 1 2 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 286 rec54_ok_6 (checkAllL_drop_of _ _ 286 193 rec54_ok_7 (checkAllL_drop_of _ _ 479 130 rec54_ok_8 (checkAllL_drop_of _ _ 609 97 rec54_ok_9 (checkAllL_drop_of _ _ 706 98 rec54_ok_10 (checkAllL_drop_of _ _ 804 86 rec54_ok_11 (rec54_ok_12))))))))
    (checkAllL_keysRange_append _ 46 2 3 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 231 rec54_ok_13 (checkAllL_drop_of _ _ 231 154 rec54_ok_14 (checkAllL_drop_of _ _ 385 102 rec54_ok_15 (checkAllL_drop_of _ _ 487 82 rec54_ok_16 (checkAllL_drop_of _ _ 569 80 rec54_ok_17 (checkAllL_drop_of _ _ 649 73 rec54_ok_18 (rec54_ok_19))))))))
    (checkAllL_keysRange_append _ 46 3 4 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 194 rec54_ok_20 (checkAllL_drop_of _ _ 194 130 rec54_ok_21 (checkAllL_drop_of _ _ 324 89 rec54_ok_22 (checkAllL_drop_of _ _ 413 74 rec54_ok_23 (checkAllL_drop_of _ _ 487 63 rec54_ok_24 (rec54_ok_25)))))))
    (checkAllL_keysRange_append _ 46 4 5 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 169 rec54_ok_26 (checkAllL_drop_of _ _ 169 107 rec54_ok_27 (checkAllL_drop_of _ _ 276 78 rec54_ok_28 (checkAllL_drop_of _ _ 354 64 rec54_ok_29 (rec54_ok_30))))))
    (checkAllL_keysRange_append _ 46 5 6 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 154 rec54_ok_31 (checkAllL_drop_of _ _ 154 87 rec54_ok_32 (checkAllL_drop_of _ _ 241 72 rec54_ok_33 (checkAllL_drop_of _ _ 313 58 rec54_ok_34 (rec54_ok_35))))))
    (checkAllL_keysRange_append _ 46 6 7 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 142 rec54_ok_36 (checkAllL_drop_of _ _ 142 77 rec54_ok_37 (checkAllL_drop_of _ _ 219 58 rec54_ok_38 (rec54_ok_39)))))
    (checkAllL_keysRange_append _ 46 7 8 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 129 rec54_ok_40 (checkAllL_drop_of _ _ 129 67 rec54_ok_41 (rec54_ok_42))))
    (checkAllL_keysRange_append _ 46 8 9 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 114 rec54_ok_43 (rec54_ok_44)))
    (checkAllL_keysRange_append _ 46 9 10 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 105 rec54_ok_45 (rec54_ok_46)))
    (checkAllL_keysRange_append _ 46 10 11 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 95 rec54_ok_47 (rec54_ok_48)))
    (checkAllL_keysRange_append _ 46 11 12 24 (by omega) (by omega) (rec54_ok_49)
    (checkAllL_keysRange_append _ 46 12 14 24 (by omega) (by omega) (rec54_ok_50)
    (rec54_ok_51))))))))))))))

/-! ## `checkRecGen p53T gT48 53` over the keys of weight `≤ 48`: 74 shards -/

theorem rec53_ok_0 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 0 1).drop 0).take 404) = true := by decide +kernel
theorem rec53_ok_1 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 0 1).drop 404).take 267) = true := by decide +kernel
theorem rec53_ok_2 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 0 1).drop 671).take 160) = true := by decide +kernel
theorem rec53_ok_3 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 0 1).drop 831).take 167) = true := by decide +kernel
theorem rec53_ok_4 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 0 1).drop 998).take 123) = true := by decide +kernel
theorem rec53_ok_5 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 0 1).drop 1121).take 99) = true := by decide +kernel
theorem rec53_ok_6 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 0 1).drop 1220).take 97) = true := by decide +kernel
theorem rec53_ok_7 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 0 1).drop 1317).take 87) = true := by decide +kernel
theorem rec53_ok_8 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 0 1).drop 1404) = true := by decide +kernel
theorem rec53_ok_9 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 0).take 287) = true := by decide +kernel
theorem rec53_ok_10 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 287).take 195) = true := by decide +kernel
theorem rec53_ok_11 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 482).take 134) = true := by decide +kernel
theorem rec53_ok_12 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 616).take 115) = true := by decide +kernel
theorem rec53_ok_13 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 731).take 95) = true := by decide +kernel
theorem rec53_ok_14 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 826).take 88) = true := by decide +kernel
theorem rec53_ok_15 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 914).take 65) = true := by decide +kernel
theorem rec53_ok_16 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 979).take 71) = true := by decide +kernel
theorem rec53_ok_17 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 1 2).drop 1050).take 69) = true := by decide +kernel
theorem rec53_ok_18 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 1 2).drop 1119) = true := by decide +kernel
theorem rec53_ok_19 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 0).take 233) = true := by decide +kernel
theorem rec53_ok_20 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 233).take 154) = true := by decide +kernel
theorem rec53_ok_21 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 387).take 111) = true := by decide +kernel
theorem rec53_ok_22 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 498).take 91) = true := by decide +kernel
theorem rec53_ok_23 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 589).take 81) = true := by decide +kernel
theorem rec53_ok_24 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 670).take 72) = true := by decide +kernel
theorem rec53_ok_25 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 742).take 56) = true := by decide +kernel
theorem rec53_ok_26 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 798).take 62) = true := by decide +kernel
theorem rec53_ok_27 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 2 3).drop 860).take 61) = true := by decide +kernel
theorem rec53_ok_28 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 2 3).drop 921) = true := by decide +kernel
theorem rec53_ok_29 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 3 4).drop 0).take 196) = true := by decide +kernel
theorem rec53_ok_30 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 3 4).drop 196).take 133) = true := by decide +kernel
theorem rec53_ok_31 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 3 4).drop 329).take 91) = true := by decide +kernel
theorem rec53_ok_32 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 3 4).drop 420).take 82) = true := by decide +kernel
theorem rec53_ok_33 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 3 4).drop 502).take 60) = true := by decide +kernel
theorem rec53_ok_34 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 3 4).drop 562).take 66) = true := by decide +kernel
theorem rec53_ok_35 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 3 4).drop 628).take 54) = true := by decide +kernel
theorem rec53_ok_36 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 3 4).drop 682).take 53) = true := by decide +kernel
theorem rec53_ok_37 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 3 4).drop 735) = true := by decide +kernel
theorem rec53_ok_38 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 4 5).drop 0).take 172) = true := by decide +kernel
theorem rec53_ok_39 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 4 5).drop 172).take 115) = true := by decide +kernel
theorem rec53_ok_40 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 4 5).drop 287).take 73) = true := by decide +kernel
theorem rec53_ok_41 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 4 5).drop 360).take 76) = true := by decide +kernel
theorem rec53_ok_42 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 4 5).drop 436).take 58) = true := by decide +kernel
theorem rec53_ok_43 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 4 5).drop 494).take 53) = true := by decide +kernel
theorem rec53_ok_44 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 4 5).drop 547) = true := by decide +kernel
theorem rec53_ok_45 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 5 6).drop 0).take 153) = true := by decide +kernel
theorem rec53_ok_46 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 5 6).drop 153).take 101) = true := by decide +kernel
theorem rec53_ok_47 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 5 6).drop 254).take 69) = true := by decide +kernel
theorem rec53_ok_48 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 5 6).drop 323).take 58) = true := by decide +kernel
theorem rec53_ok_49 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 5 6).drop 381).take 53) = true := by decide +kernel
theorem rec53_ok_50 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 5 6).drop 434) = true := by decide +kernel
theorem rec53_ok_51 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 6 7).drop 0).take 137) = true := by decide +kernel
theorem rec53_ok_52 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 6 7).drop 137).take 87) = true := by decide +kernel
theorem rec53_ok_53 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 6 7).drop 224).take 63) = true := by decide +kernel
theorem rec53_ok_54 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 6 7).drop 287).take 54) = true := by decide +kernel
theorem rec53_ok_55 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 6 7).drop 341) = true := by decide +kernel
theorem rec53_ok_56 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 7 8).drop 0).take 129) = true := by decide +kernel
theorem rec53_ok_57 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 7 8).drop 129).take 74) = true := by decide +kernel
theorem rec53_ok_58 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 7 8).drop 203).take 54) = true := by decide +kernel
theorem rec53_ok_59 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 7 8).drop 257) = true := by decide +kernel
theorem rec53_ok_60 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 8 9).drop 0).take 120) = true := by decide +kernel
theorem rec53_ok_61 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 8 9).drop 120).take 62) = true := by decide +kernel
theorem rec53_ok_62 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 8 9).drop 182) = true := by decide +kernel
theorem rec53_ok_63 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 9 10).drop 0).take 108) = true := by decide +kernel
theorem rec53_ok_64 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 9 10).drop 108).take 57) = true := by decide +kernel
theorem rec53_ok_65 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 9 10).drop 165) = true := by decide +kernel
theorem rec53_ok_66 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 10 11).drop 0).take 100) = true := by decide +kernel
theorem rec53_ok_67 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 10 11).drop 100) = true := by decide +kernel
theorem rec53_ok_68 : checkAllL (checkRecGen p53T gT48 53) (((keysRange 48 11 12).drop 0).take 91) = true := by decide +kernel
theorem rec53_ok_69 : checkAllL (checkRecGen p53T gT48 53) ((keysRange 48 11 12).drop 91) = true := by decide +kernel
theorem rec53_ok_70 : checkAllL (checkRecGen p53T gT48 53) (keysRange 48 12 13) = true := by decide +kernel
theorem rec53_ok_71 : checkAllL (checkRecGen p53T gT48 53) (keysRange 48 13 14) = true := by decide +kernel
theorem rec53_ok_72 : checkAllL (checkRecGen p53T gT48 53) (keysRange 48 14 17) = true := by decide +kernel
theorem rec53_ok_73 : checkAllL (checkRecGen p53T gT48 53) (keysRange 48 17 25) = true := by decide +kernel

/-- `checkRecGen p53T gT48 53` on every key of weight `≤ 48`, from the shards. -/
theorem rec53_ok : checkAllL (checkRecGen p53T gT48 53) (keysW 13 48) = true := by
  rw [keysW_eq_keysRange 48 25 rfl]
  exact (checkAllL_keysRange_append _ 48 0 1 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 404 rec53_ok_0 (checkAllL_drop_of _ _ 404 267 rec53_ok_1 (checkAllL_drop_of _ _ 671 160 rec53_ok_2 (checkAllL_drop_of _ _ 831 167 rec53_ok_3 (checkAllL_drop_of _ _ 998 123 rec53_ok_4 (checkAllL_drop_of _ _ 1121 99 rec53_ok_5 (checkAllL_drop_of _ _ 1220 97 rec53_ok_6 (checkAllL_drop_of _ _ 1317 87 rec53_ok_7 (rec53_ok_8))))))))))
    (checkAllL_keysRange_append _ 48 1 2 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 287 rec53_ok_9 (checkAllL_drop_of _ _ 287 195 rec53_ok_10 (checkAllL_drop_of _ _ 482 134 rec53_ok_11 (checkAllL_drop_of _ _ 616 115 rec53_ok_12 (checkAllL_drop_of _ _ 731 95 rec53_ok_13 (checkAllL_drop_of _ _ 826 88 rec53_ok_14 (checkAllL_drop_of _ _ 914 65 rec53_ok_15 (checkAllL_drop_of _ _ 979 71 rec53_ok_16 (checkAllL_drop_of _ _ 1050 69 rec53_ok_17 (rec53_ok_18)))))))))))
    (checkAllL_keysRange_append _ 48 2 3 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 233 rec53_ok_19 (checkAllL_drop_of _ _ 233 154 rec53_ok_20 (checkAllL_drop_of _ _ 387 111 rec53_ok_21 (checkAllL_drop_of _ _ 498 91 rec53_ok_22 (checkAllL_drop_of _ _ 589 81 rec53_ok_23 (checkAllL_drop_of _ _ 670 72 rec53_ok_24 (checkAllL_drop_of _ _ 742 56 rec53_ok_25 (checkAllL_drop_of _ _ 798 62 rec53_ok_26 (checkAllL_drop_of _ _ 860 61 rec53_ok_27 (rec53_ok_28)))))))))))
    (checkAllL_keysRange_append _ 48 3 4 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 196 rec53_ok_29 (checkAllL_drop_of _ _ 196 133 rec53_ok_30 (checkAllL_drop_of _ _ 329 91 rec53_ok_31 (checkAllL_drop_of _ _ 420 82 rec53_ok_32 (checkAllL_drop_of _ _ 502 60 rec53_ok_33 (checkAllL_drop_of _ _ 562 66 rec53_ok_34 (checkAllL_drop_of _ _ 628 54 rec53_ok_35 (checkAllL_drop_of _ _ 682 53 rec53_ok_36 (rec53_ok_37))))))))))
    (checkAllL_keysRange_append _ 48 4 5 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 172 rec53_ok_38 (checkAllL_drop_of _ _ 172 115 rec53_ok_39 (checkAllL_drop_of _ _ 287 73 rec53_ok_40 (checkAllL_drop_of _ _ 360 76 rec53_ok_41 (checkAllL_drop_of _ _ 436 58 rec53_ok_42 (checkAllL_drop_of _ _ 494 53 rec53_ok_43 (rec53_ok_44))))))))
    (checkAllL_keysRange_append _ 48 5 6 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 153 rec53_ok_45 (checkAllL_drop_of _ _ 153 101 rec53_ok_46 (checkAllL_drop_of _ _ 254 69 rec53_ok_47 (checkAllL_drop_of _ _ 323 58 rec53_ok_48 (checkAllL_drop_of _ _ 381 53 rec53_ok_49 (rec53_ok_50)))))))
    (checkAllL_keysRange_append _ 48 6 7 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 137 rec53_ok_51 (checkAllL_drop_of _ _ 137 87 rec53_ok_52 (checkAllL_drop_of _ _ 224 63 rec53_ok_53 (checkAllL_drop_of _ _ 287 54 rec53_ok_54 (rec53_ok_55))))))
    (checkAllL_keysRange_append _ 48 7 8 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 129 rec53_ok_56 (checkAllL_drop_of _ _ 129 74 rec53_ok_57 (checkAllL_drop_of _ _ 203 54 rec53_ok_58 (rec53_ok_59)))))
    (checkAllL_keysRange_append _ 48 8 9 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 120 rec53_ok_60 (checkAllL_drop_of _ _ 120 62 rec53_ok_61 (rec53_ok_62))))
    (checkAllL_keysRange_append _ 48 9 10 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 108 rec53_ok_63 (checkAllL_drop_of _ _ 108 57 rec53_ok_64 (rec53_ok_65))))
    (checkAllL_keysRange_append _ 48 10 11 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 100 rec53_ok_66 (rec53_ok_67)))
    (checkAllL_keysRange_append _ 48 11 12 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 91 rec53_ok_68 (rec53_ok_69)))
    (checkAllL_keysRange_append _ 48 12 13 25 (by omega) (by omega) (rec53_ok_70)
    (checkAllL_keysRange_append _ 48 13 14 25 (by omega) (by omega) (rec53_ok_71)
    (checkAllL_keysRange_append _ 48 14 17 25 (by omega) (by omega) (rec53_ok_72)
    (rec53_ok_73))))))))))))))))

/-! ## `checkWI WItree` on the entries of weight `≤ 46`: 24 shards -/

theorem wi_ok_0 : checkAllL (checkWI WItree) (((wiEntriesR 0 1).drop 0).take 2750) = true := by decide +kernel
theorem wi_ok_1 : checkAllL (checkWI WItree) (((wiEntriesR 0 1).drop 2750).take 2150) = true := by decide +kernel
theorem wi_ok_2 : checkAllL (checkWI WItree) (((wiEntriesR 0 1).drop 4900).take 1700) = true := by decide +kernel
theorem wi_ok_3 : checkAllL (checkWI WItree) (((wiEntriesR 0 1).drop 6600).take 1350) = true := by decide +kernel
theorem wi_ok_4 : checkAllL (checkWI WItree) (((wiEntriesR 0 1).drop 7950).take 1000) = true := by decide +kernel
theorem wi_ok_5 : checkAllL (checkWI WItree) (((wiEntriesR 0 1).drop 8950).take 750) = true := by decide +kernel
theorem wi_ok_6 : checkAllL (checkWI WItree) ((wiEntriesR 0 1).drop 9700) = true := by decide +kernel
theorem wi_ok_7 : checkAllL (checkWI WItree) (((wiEntriesR 1 2).drop 0).take 2750) = true := by decide +kernel
theorem wi_ok_8 : checkAllL (checkWI WItree) (((wiEntriesR 1 2).drop 2750).take 2150) = true := by decide +kernel
theorem wi_ok_9 : checkAllL (checkWI WItree) (((wiEntriesR 1 2).drop 4900).take 1650) = true := by decide +kernel
theorem wi_ok_10 : checkAllL (checkWI WItree) ((wiEntriesR 1 2).drop 6550) = true := by decide +kernel
theorem wi_ok_11 : checkAllL (checkWI WItree) (((wiEntriesR 2 3).drop 0).take 2750) = true := by decide +kernel
theorem wi_ok_12 : checkAllL (checkWI WItree) (((wiEntriesR 2 3).drop 2750).take 2100) = true := by decide +kernel
theorem wi_ok_13 : checkAllL (checkWI WItree) ((wiEntriesR 2 3).drop 4850) = true := by decide +kernel
theorem wi_ok_14 : checkAllL (checkWI WItree) (((wiEntriesR 3 4).drop 0).take 2750) = true := by decide +kernel
theorem wi_ok_15 : checkAllL (checkWI WItree) ((wiEntriesR 3 4).drop 2750) = true := by decide +kernel
theorem wi_ok_16 : checkAllL (checkWI WItree) (((wiEntriesR 4 5).drop 0).take 2700) = true := by decide +kernel
theorem wi_ok_17 : checkAllL (checkWI WItree) ((wiEntriesR 4 5).drop 2700) = true := by decide +kernel
theorem wi_ok_18 : checkAllL (checkWI WItree) (((wiEntriesR 5 6).drop 0).take 2700) = true := by decide +kernel
theorem wi_ok_19 : checkAllL (checkWI WItree) ((wiEntriesR 5 6).drop 2700) = true := by decide +kernel
theorem wi_ok_20 : checkAllL (checkWI WItree) (wiEntriesR 6 7) = true := by decide +kernel
theorem wi_ok_21 : checkAllL (checkWI WItree) (wiEntriesR 7 8) = true := by decide +kernel
theorem wi_ok_22 : checkAllL (checkWI WItree) (wiEntriesR 8 10) = true := by decide +kernel
theorem wi_ok_23 : checkAllL (checkWI WItree) (wiEntriesR 10 24) = true := by decide +kernel

/-- `checkWI WItree` on all of `wiEntries`, from the shards. -/
theorem wi_ok : checkAllL (checkWI WItree) wiEntries = true := by
  rw [wiEntries_eq_R]
  exact (checkAllL_wiEntriesR_append _ 0 1 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2750 wi_ok_0 (checkAllL_drop_of _ _ 2750 2150 wi_ok_1 (checkAllL_drop_of _ _ 4900 1700 wi_ok_2 (checkAllL_drop_of _ _ 6600 1350 wi_ok_3 (checkAllL_drop_of _ _ 7950 1000 wi_ok_4 (checkAllL_drop_of _ _ 8950 750 wi_ok_5 (wi_ok_6))))))))
    (checkAllL_wiEntriesR_append _ 1 2 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2750 wi_ok_7 (checkAllL_drop_of _ _ 2750 2150 wi_ok_8 (checkAllL_drop_of _ _ 4900 1650 wi_ok_9 (wi_ok_10)))))
    (checkAllL_wiEntriesR_append _ 2 3 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2750 wi_ok_11 (checkAllL_drop_of _ _ 2750 2100 wi_ok_12 (wi_ok_13))))
    (checkAllL_wiEntriesR_append _ 3 4 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2750 wi_ok_14 (wi_ok_15)))
    (checkAllL_wiEntriesR_append _ 4 5 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2700 wi_ok_16 (wi_ok_17)))
    (checkAllL_wiEntriesR_append _ 5 6 24 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2700 wi_ok_18 (wi_ok_19)))
    (checkAllL_wiEntriesR_append _ 6 7 24 (by omega) (by omega) (wi_ok_20)
    (checkAllL_wiEntriesR_append _ 7 8 24 (by omega) (by omega) (wi_ok_21)
    (checkAllL_wiEntriesR_append _ 8 10 24 (by omega) (by omega) (wi_ok_22)
    (wi_ok_23))))))))))

/-! ## `checkWJ WJtree` on the entries of weight `≤ 48`: 40 shards -/

theorem wj_ok_0 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 0).take 2800) = true := by decide +kernel
theorem wj_ok_1 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 2800).take 2150) = true := by decide +kernel
theorem wj_ok_2 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 4950).take 1700) = true := by decide +kernel
theorem wj_ok_3 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 6650).take 1350) = true := by decide +kernel
theorem wj_ok_4 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 8000).take 1050) = true := by decide +kernel
theorem wj_ok_5 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 9050).take 850) = true := by decide +kernel
theorem wj_ok_6 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 9900).take 650) = true := by decide +kernel
theorem wj_ok_7 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 10550).take 500) = true := by decide +kernel
theorem wj_ok_8 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 11050).take 350) = true := by decide +kernel
theorem wj_ok_9 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 11400).take 300) = true := by decide +kernel
theorem wj_ok_10 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 11700).take 200) = true := by decide +kernel
theorem wj_ok_11 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 11900).take 150) = true := by decide +kernel
theorem wj_ok_12 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 12050).take 150) = true := by decide +kernel
theorem wj_ok_13 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 12200).take 100) = true := by decide +kernel
theorem wj_ok_14 : checkAllL (checkWJ WJtree) (((wjEntriesR 0 1).drop 12300).take 50) = true := by decide +kernel
theorem wj_ok_15 : checkAllL (checkWJ WJtree) ((wjEntriesR 0 1).drop 12350) = true := by decide +kernel
theorem wj_ok_16 : checkAllL (checkWJ WJtree) (((wjEntriesR 1 2).drop 0).take 2750) = true := by decide +kernel
theorem wj_ok_17 : checkAllL (checkWJ WJtree) (((wjEntriesR 1 2).drop 2750).take 2150) = true := by decide +kernel
theorem wj_ok_18 : checkAllL (checkWJ WJtree) (((wjEntriesR 1 2).drop 4900).take 1700) = true := by decide +kernel
theorem wj_ok_19 : checkAllL (checkWJ WJtree) (((wjEntriesR 1 2).drop 6600).take 1350) = true := by decide +kernel
theorem wj_ok_20 : checkAllL (checkWJ WJtree) (((wjEntriesR 1 2).drop 7950).take 1000) = true := by decide +kernel
theorem wj_ok_21 : checkAllL (checkWJ WJtree) (((wjEntriesR 1 2).drop 8950).take 750) = true := by decide +kernel
theorem wj_ok_22 : checkAllL (checkWJ WJtree) ((wjEntriesR 1 2).drop 9700) = true := by decide +kernel
theorem wj_ok_23 : checkAllL (checkWJ WJtree) (((wjEntriesR 2 3).drop 0).take 2750) = true := by decide +kernel
theorem wj_ok_24 : checkAllL (checkWJ WJtree) (((wjEntriesR 2 3).drop 2750).take 2150) = true := by decide +kernel
theorem wj_ok_25 : checkAllL (checkWJ WJtree) (((wjEntriesR 2 3).drop 4900).take 1650) = true := by decide +kernel
theorem wj_ok_26 : checkAllL (checkWJ WJtree) ((wjEntriesR 2 3).drop 6550) = true := by decide +kernel
theorem wj_ok_27 : checkAllL (checkWJ WJtree) (((wjEntriesR 3 4).drop 0).take 2750) = true := by decide +kernel
theorem wj_ok_28 : checkAllL (checkWJ WJtree) (((wjEntriesR 3 4).drop 2750).take 2100) = true := by decide +kernel
theorem wj_ok_29 : checkAllL (checkWJ WJtree) ((wjEntriesR 3 4).drop 4850) = true := by decide +kernel
theorem wj_ok_30 : checkAllL (checkWJ WJtree) (((wjEntriesR 4 5).drop 0).take 2750) = true := by decide +kernel
theorem wj_ok_31 : checkAllL (checkWJ WJtree) ((wjEntriesR 4 5).drop 2750) = true := by decide +kernel
theorem wj_ok_32 : checkAllL (checkWJ WJtree) (((wjEntriesR 5 6).drop 0).take 2700) = true := by decide +kernel
theorem wj_ok_33 : checkAllL (checkWJ WJtree) ((wjEntriesR 5 6).drop 2700) = true := by decide +kernel
theorem wj_ok_34 : checkAllL (checkWJ WJtree) (((wjEntriesR 6 7).drop 0).take 2700) = true := by decide +kernel
theorem wj_ok_35 : checkAllL (checkWJ WJtree) ((wjEntriesR 6 7).drop 2700) = true := by decide +kernel
theorem wj_ok_36 : checkAllL (checkWJ WJtree) (wjEntriesR 7 8) = true := by decide +kernel
theorem wj_ok_37 : checkAllL (checkWJ WJtree) (wjEntriesR 8 9) = true := by decide +kernel
theorem wj_ok_38 : checkAllL (checkWJ WJtree) (wjEntriesR 9 11) = true := by decide +kernel
theorem wj_ok_39 : checkAllL (checkWJ WJtree) (wjEntriesR 11 25) = true := by decide +kernel

/-- `checkWJ WJtree` on all of `wjEntries`, from the shards. -/
theorem wj_ok : checkAllL (checkWJ WJtree) wjEntries = true := by
  rw [wjEntries_eq_R]
  exact (checkAllL_wjEntriesR_append _ 0 1 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2800 wj_ok_0 (checkAllL_drop_of _ _ 2800 2150 wj_ok_1 (checkAllL_drop_of _ _ 4950 1700 wj_ok_2 (checkAllL_drop_of _ _ 6650 1350 wj_ok_3 (checkAllL_drop_of _ _ 8000 1050 wj_ok_4 (checkAllL_drop_of _ _ 9050 850 wj_ok_5 (checkAllL_drop_of _ _ 9900 650 wj_ok_6 (checkAllL_drop_of _ _ 10550 500 wj_ok_7 (checkAllL_drop_of _ _ 11050 350 wj_ok_8 (checkAllL_drop_of _ _ 11400 300 wj_ok_9 (checkAllL_drop_of _ _ 11700 200 wj_ok_10 (checkAllL_drop_of _ _ 11900 150 wj_ok_11 (checkAllL_drop_of _ _ 12050 150 wj_ok_12 (checkAllL_drop_of _ _ 12200 100 wj_ok_13 (checkAllL_drop_of _ _ 12300 50 wj_ok_14 (wj_ok_15)))))))))))))))))
    (checkAllL_wjEntriesR_append _ 1 2 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2750 wj_ok_16 (checkAllL_drop_of _ _ 2750 2150 wj_ok_17 (checkAllL_drop_of _ _ 4900 1700 wj_ok_18 (checkAllL_drop_of _ _ 6600 1350 wj_ok_19 (checkAllL_drop_of _ _ 7950 1000 wj_ok_20 (checkAllL_drop_of _ _ 8950 750 wj_ok_21 (wj_ok_22))))))))
    (checkAllL_wjEntriesR_append _ 2 3 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2750 wj_ok_23 (checkAllL_drop_of _ _ 2750 2150 wj_ok_24 (checkAllL_drop_of _ _ 4900 1650 wj_ok_25 (wj_ok_26)))))
    (checkAllL_wjEntriesR_append _ 3 4 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2750 wj_ok_27 (checkAllL_drop_of _ _ 2750 2100 wj_ok_28 (wj_ok_29))))
    (checkAllL_wjEntriesR_append _ 4 5 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2750 wj_ok_30 (wj_ok_31)))
    (checkAllL_wjEntriesR_append _ 5 6 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2700 wj_ok_32 (wj_ok_33)))
    (checkAllL_wjEntriesR_append _ 6 7 25 (by omega) (by omega) (checkAllL_of_drop_zero (checkAllL_drop_of _ _ 0 2700 wj_ok_34 (wj_ok_35)))
    (checkAllL_wjEntriesR_append _ 7 8 25 (by omega) (by omega) (wj_ok_36)
    (checkAllL_wjEntriesR_append _ 8 9 25 (by omega) (by omega) (wj_ok_37)
    (checkAllL_wjEntriesR_append _ 9 11 25 (by omega) (by omega) (wj_ok_38)
    (wj_ok_39)))))))))))

/-! ## The collected marginal, three chained links (E3-3, E3-9) -/

theorem w_ok_0 : checkWChain wsh0 0 0 = (true, 170, 4110, 3756) := by decide +kernel
theorem w_ok_1 : checkWChain wsh1 170 4110 = (true, 689, 16777227, 3975) := by decide +kernel
theorem w_ok_2 : checkWChain wsh2 689 16777227 = (true, 1236, 73786976294838206466, 2029) := by decide +kernel
theorem w_close : 1236 = nW ∧ 3756 + 3975 + 2029 = expectedLen := by decide +kernel

/-- The marginal check on all eleven shards, from the three links by rewriting; the close is one
kernel `decide` on a literal `Bool` (no shard is re-run). -/
theorem w_ok : checkWShards wshards = true := by
  have h0 := wfold_of_chain w_ok_0
  have h1 := wfold_of_chain w_ok_1
  have h2 := wfold_of_chain w_ok_2
  obtain ⟨hn, hl⟩ := w_close
  have e : (wsh0 ++ wsh1 ++ wsh2).foldl wShardStep (0, 0, 0, true) =
      (1236, 73786976294838206466, 3756 + 3975 + 2029, true) := by
    rw [List.foldl_append, List.foldl_append, h0,
      show ((170, 4110, 3756, true) : Nat × Nat × Nat × Bool) = wShift 3756 true (170, 4110, 0, true) from rfl,
      wShards_foldl_shift, h1,
      show wShift 3756 true (689, 16777227, 3975, true) = wShift (3756 + 3975) true (689, 16777227, 0, true) from rfl,
      wShards_foldl_shift, h2]
    rfl
  unfold checkWShards wshards
  rw [e, ← hn, ← hl]
  decide

end SaltC1.Cert54
