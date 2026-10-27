/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.Tuple
import Salt.MaynardK.Cert105

/-!
# C1 · B5.4 — Engelsma's 105-tuple as a tuple choice (diameter 600)

`engelsmaTuple` is the `TupleChoice` whose `105`-tuple is `Cert105.H600` (the `k = 105` entry of
Sutherland's table of narrow admissible tuples, after Engelsma; its admissibility is checked by the
kernel in `Cert105`) and whose every other `k`-tuple is the standard one. Its four fields are proved
here, plus the two facts the `k = 105` chain consumes from its tuple: every entry is `≤ 743`, and
the diameter is `≤ 600`.

⛔ `engelsmaTuple` is a `def`, NEVER an `instance`: a global instance at default priority would
outrank the low-priority default `stdTuple` and silently re-point every later `hSeq`/`H`/`D₀`/`W`
in any module that imports this one. Use it explicitly (`@… engelsmaTuple …` or `letI`).
Nothing here bears on twin primes.
-/

namespace Salt.MaynardK

open Finset Salt.Maynard

/-- The entries of `H600`, by index. -/
def h600 (i : ℕ) : ℕ := H600.getD i 0

/-- The entries of `H600` are pairwise distinct over `Fin 105`: `h600 i = h600 j → i = j`, by
`decide +kernel`. -/
theorem h600_injective : ∀ i j : Fin 105, h600 i = h600 j → i = j := by decide +kernel

/-- Every entry of `H600` is `≤ 600` (its diameter), over `Fin 105`, by `decide +kernel`. -/
theorem h600_le : ∀ i : Fin 105, h600 i ≤ 600 := by decide +kernel

/-- `h600 i` is an element of `H600` for `i : Fin 105`: `getD` reads inside the list, whose
length is `105` (`H600_length`). -/
theorem h600_mem (i : Fin 105) : h600 i ∈ H600 := by
  have hi : (i : ℕ) < H600.length := by rw [H600_length]; exact i.isLt
  unfold h600
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- The tuple: `H600` at `k = 105`, the standard tuple at every other `k`. -/
noncomputable def engelsmaSeq (k : ℕ) (i : Fin k) : ℕ := if k = 105 then h600 i else stdSeq k i

/-- `engelsmaSeq` at `k = 105` is `h600` (the `if` fires). -/
theorem engelsmaSeq_105 (i : Fin 105) : engelsmaSeq 105 i = h600 i := by
  rw [engelsmaSeq, if_pos rfl]

/-- `engelsmaSeq k` at `k ≠ 105` is the standard tuple `stdSeq k` (the `if` does not fire). -/
theorem engelsmaSeq_ne {k : ℕ} (hk : k ≠ 105) : engelsmaSeq k = stdSeq k := by
  funext i
  rw [engelsmaSeq, if_neg hk]

/-- `engelsmaSeq k` is injective for every `k`: by `h600_injective` at `k = 105` and by
`stdSeq_injective` elsewhere (the `inj` field of `engelsmaTuple`). -/
theorem engelsmaSeq_injective (k : ℕ) : Function.Injective (engelsmaSeq k) := by
  by_cases hk : k = 105
  · subst hk
    intro i j h
    rw [engelsmaSeq_105, engelsmaSeq_105] at h
    exact h600_injective i j h
  · rw [engelsmaSeq_ne hk]
    exact stdSeq_injective k

/-- The image of `engelsmaSeq k` is `Admissible` for every `k`: at `k = 105` by
`admissible_of_small_primes` from `H600_admissible` (every prime `p ≤ 105` misses a residue
class mod `p`); elsewhere by `std_admissible` (the `admissible` field of `engelsmaTuple`). -/
theorem engelsma_admissible (k : ℕ) :
    Admissible ((Finset.univ : Finset (Fin k)).image (engelsmaSeq k)) := by
  by_cases hk : k = 105
  · subst hk
    apply admissible_of_small_primes
    intro p hp hpS
    have hp105 : p ≤ 105 :=
      hpS.trans (Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin]))
    have hmem : p ∈ (List.range 106).filter (fun p => decide (Nat.Prime p)) := by
      rw [List.mem_filter, List.mem_range]
      exact ⟨by omega, by simpa using hp⟩
    obtain ⟨r, hr, hmiss⟩ := H600_admissible p hmem
    rw [List.mem_range] at hr
    refine ⟨(r : ZMod p), fun h hh hcontra => ?_⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
    rw [engelsmaSeq_105] at hcontra
    apply hmiss (h600 i) (h600_mem i)
    have := (ZMod.natCast_eq_natCast_iff' (h600 i) r p).mp hcontra
    rwa [Nat.mod_eq_of_lt hr] at this
  · rw [engelsmaSeq_ne hk]
    exact std_admissible k

/-- For `k ≥ 20` the image of `engelsmaSeq k` has `sup id ≤ k ^ 3`: at `k = 105` from `h600_le`
(`600 ≤ 105 ^ 3`); elsewhere by `std_sup_le_cube` (the `sup_cube` field of `engelsmaTuple`). -/
theorem engelsma_sup_cube (k : ℕ) (hk20 : 20 ≤ k) :
    ((Finset.univ : Finset (Fin k)).image (engelsmaSeq k)).sup id ≤ k ^ 3 := by
  by_cases hk : k = 105
  · subst hk
    apply Finset.sup_le
    intro h hh
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
    rw [id_eq, engelsmaSeq_105]
    have := h600_le i
    norm_num
    omega
  · rw [engelsmaSeq_ne hk]
    exact std_sup_le_cube k hk20

/-- **Engelsma's tuple as a tuple choice.** A `def`, never an `instance` (see the module doc);
`@[reducible]` as Lean asks of a def of class type, which does not register it as an instance. -/
@[reducible] noncomputable def engelsmaTuple : TupleChoice :=
  ⟨engelsmaSeq, engelsmaSeq_injective, engelsma_admissible, engelsma_sup_cube⟩

/-! ## The facts the `k = 105` chain consumes -/

/-- Under `engelsmaTuple`, `hSeq 105 i = h600 i` (`engelsmaSeq_105`, the `tup` field read
back). -/
theorem hSeq_engelsma_105 (i : Fin 105) : @hSeq engelsmaTuple 105 i = h600 i :=
  engelsmaSeq_105 i

/-- Every entry of the chosen `105`-tuple is `≤ 743` (the bound the `k = 105` chain was built on;
here it holds with room, since the entries are `≤ 600`). -/
theorem hSeq_engelsma_le_743 (i : Fin 105) : @hSeq engelsmaTuple 105 i ≤ 743 := by
  rw [hSeq_engelsma_105]
  have := h600_le i
  omega

/-- Under `engelsmaTuple`, for a level `D ≥ 744` every entry of the `105`-tuple is `< D` (from
`hSeq_engelsma_le_743`). -/
theorem hSeq_engelsma_lt_D {D : ℕ} (hD : 744 ≤ D) (i : Fin 105) :
    @hSeq engelsmaTuple 105 i < D := by
  have := hSeq_engelsma_le_743 i
  omega

/-- The diameter of the chosen `105`-tuple is at most `600`. -/
theorem hSeq_engelsma_diam_le_600 (i j : Fin 105) :
    (@hSeq engelsmaTuple 105 j : ℤ) - (@hSeq engelsmaTuple 105 i : ℤ) ∈ Set.Icc (-600 : ℤ) 600 := by
  rw [hSeq_engelsma_105, hSeq_engelsma_105, Set.mem_Icc]
  have hi := h600_le i
  have hj := h600_le j
  omega

end Salt.MaynardK
