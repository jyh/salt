/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.Tuple

/-!
# C1 · A4 — an admissible 54-tuple of diameter 270 as a tuple choice

`H270` is the `k = 54` entry of A. V. Sutherland's table of narrow admissible tuples
(`math.mit.edu/~primegaps`, file `admissible_54_270.txt`), the diameter used for DHL[54, 2] in
Polymath 8b (arXiv:1407.4897v4, Thm 3.9(vii)). Its length, diameter and admissibility are checked
here by the kernel: the source is cited, not trusted.

`polymath54Tuple` is the `TupleChoice` whose `54`-tuple is `H270` and whose every other `k`-tuple
is the standard one. Its four fields are proved here, plus the two facts the `k = 54` chain
consumes from its tuple: every entry is `≤ 270`, and the diameter is `≤ 270`.

⛔ `polymath54Tuple` is a `def`, NEVER registered for typeclass resolution: a global registration
at default priority would outrank the low-priority default `stdTuple` and silently re-point every
later `hSeq`/`H`/`D₀`/`W` in any module that imports this one. Use it explicitly
(`@… polymath54Tuple …` or `letI`).
Nothing here bears on twin primes.
-/

namespace SaltC1.MaynardK

open Finset Salt.Maynard

/-- an admissible 54-tuple of diameter 270, the `k = 54` entry of A. V. Sutherland's table of
narrow admissible tuples (`math.mit.edu/~primegaps`, file `admissible_54_270.txt`). Its
admissibility is checked here by the kernel: the source is cited, not trusted. -/
def H270 : List ℕ := [
  0, 4, 10, 18, 24, 28, 30, 40, 54, 58, 60, 70, 72, 82, 84, 88, 94, 102, 108, 112, 114, 118,
  124, 130, 132, 138, 142, 150, 154, 160, 168, 172, 174, 180, 184, 192, 198, 202, 208, 214,
  220, 222, 228, 234, 238, 240, 244, 250, 252, 258, 262, 264, 268, 270]

theorem H270_length : H270.length = 54 := by decide +kernel
theorem H270_diam : H270.getLast? = some 270 ∧ H270.head? = some 0 := by decide +kernel
/-- admissible: for every prime `p ≤ 54` some residue class mod `p` is missed. -/
theorem H270_admissible : ∀ p ∈ (List.range 55).filter (fun p => decide (Nat.Prime p)),
    ∃ r ∈ List.range p, ∀ h ∈ H270, h % p ≠ r := by decide +kernel

/-- The entries of `H270`, by index. -/
def h270 (i : ℕ) : ℕ := H270.getD i 0

theorem h270_injective : ∀ i j : Fin 54, h270 i = h270 j → i = j := by decide +kernel

theorem h270_le : ∀ i : Fin 54, h270 i ≤ 270 := by decide +kernel

theorem h270_mem (i : Fin 54) : h270 i ∈ H270 := by
  have hi : (i : ℕ) < H270.length := by rw [H270_length]; exact i.isLt
  unfold h270
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- The tuple: `H270` at `k = 54`, the standard tuple at every other `k`. -/
noncomputable def polymathSeq (k : ℕ) (i : Fin k) : ℕ := if k = 54 then h270 i else stdSeq k i

theorem polymathSeq_54 (i : Fin 54) : polymathSeq 54 i = h270 i := by
  rw [polymathSeq, if_pos rfl]

theorem polymathSeq_ne {k : ℕ} (hk : k ≠ 54) : polymathSeq k = stdSeq k := by
  funext i
  rw [polymathSeq, if_neg hk]

theorem polymathSeq_injective (k : ℕ) : Function.Injective (polymathSeq k) := by
  by_cases hk : k = 54
  · subst hk
    intro i j h
    rw [polymathSeq_54, polymathSeq_54] at h
    exact h270_injective i j h
  · rw [polymathSeq_ne hk]
    exact stdSeq_injective k

theorem polymath_admissible (k : ℕ) :
    Admissible ((Finset.univ : Finset (Fin k)).image (polymathSeq k)) := by
  by_cases hk : k = 54
  · subst hk
    apply admissible_of_small_primes
    intro p hp hpS
    have hp54 : p ≤ 54 :=
      hpS.trans (Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin]))
    have hmem : p ∈ (List.range 55).filter (fun p => decide (Nat.Prime p)) := by
      rw [List.mem_filter, List.mem_range]
      exact ⟨by omega, by simpa using hp⟩
    obtain ⟨r, hr, hmiss⟩ := H270_admissible p hmem
    rw [List.mem_range] at hr
    refine ⟨(r : ZMod p), fun h hh hcontra => ?_⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
    rw [polymathSeq_54] at hcontra
    apply hmiss (h270 i) (h270_mem i)
    have := (ZMod.natCast_eq_natCast_iff' (h270 i) r p).mp hcontra
    rwa [Nat.mod_eq_of_lt hr] at this
  · rw [polymathSeq_ne hk]
    exact std_admissible k

theorem polymath_sup_cube (k : ℕ) (hk20 : 20 ≤ k) :
    ((Finset.univ : Finset (Fin k)).image (polymathSeq k)).sup id ≤ k ^ 3 := by
  by_cases hk : k = 54
  · subst hk
    apply Finset.sup_le
    intro h hh
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hh
    rw [id_eq, polymathSeq_54]
    have := h270_le i
    norm_num
    omega
  · rw [polymathSeq_ne hk]
    exact std_sup_le_cube k hk20

/-- **The diameter-270 tuple as a tuple choice.** A `def`, never registered for typeclass
resolution (see the module doc); `@[reducible]` as Lean asks of a def of class type, which does not
register it. -/
@[reducible] noncomputable def polymath54Tuple : TupleChoice :=
  ⟨polymathSeq, polymathSeq_injective, polymath_admissible, polymath_sup_cube⟩

/-! ## The facts the `k = 54` chain consumes -/

theorem hSeq_polymath_54 (i : Fin 54) : @hSeq polymath54Tuple 54 i = h270 i :=
  polymathSeq_54 i

/-- Every entry of the chosen `54`-tuple is `≤ 270` (the bound the `k = 54` chain was built on). -/
theorem hSeq_polymath_le_270 (i : Fin 54) : @hSeq polymath54Tuple 54 i ≤ 270 := by
  rw [hSeq_polymath_54]
  exact h270_le i

theorem hSeq_polymath_lt_D {D : ℕ} (hD : 271 ≤ D) (i : Fin 54) :
    @hSeq polymath54Tuple 54 i < D := by
  have := hSeq_polymath_le_270 i
  omega

/-- The diameter of the chosen `54`-tuple is at most `270`. -/
theorem hSeq_polymath_diam_le_270 (i j : Fin 54) :
    (@hSeq polymath54Tuple 54 j : ℤ) - (@hSeq polymath54Tuple 54 i : ℤ) ∈
      Set.Icc (-270 : ℤ) 270 := by
  rw [hSeq_polymath_54, hSeq_polymath_54, Set.mem_Icc]
  have hi := h270_le i
  have hj := h270_le j
  omega

end SaltC1.MaynardK
