/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.Strip

/-!
# VK-TWIST VT-1 — affine blindness of the `k`-th difference operator

The VK-TWIST campaign threads an additive-linear twist `e(βn)` through the landed
van der Corput ladder, so that the ζ-machinery applies verbatim to the twisted
sums `∑ χ(n)·n^{−σ−it}` after Gauss completion.  The whole campaign rests on one
elementary fact, landed here:

**the `k`-th forward difference (`k ≥ 2`) does not see an affine phase.**

`IsVdCBound k C` (`Salt/ExpSum/DerivTestK.lean`) consumes exactly two hypotheses
about the phase `f : ℤ → ℝ` — the window bounds `λ ≤ dk k f n ≤ c·λ` on `(a,b)`.
Since `dk k (f + affine) = dk k f` for `k ≥ 2` (`dk_add_affine`), those hypotheses
transfer *unchanged* from `f` to `f + affine`; `isVdCBound_affine` is the transfer
lemma at the entry point, and `dk_window_affine_iff` is its hypothesis-level `iff`.

## The twist in the corpus's conventions

* `eR x = exp(2πi·x)` (the `2π` is **inside**, `Salt/ExpSum/Basic.lean`), so the
  twisted summand `e(βn)·n^{−it}` is `eR (phi t n + β·n)` with
  `phi t n = −(t/2π)·log n` (`Salt/ExpSum/ZetaBlock.lean`).  The twist is therefore
  an additive `β·n` in the **phase**, `β : ℝ`.
* `dk : ℕ → (ℤ → ℝ) → ℤ → ℝ` is the recursive forward difference, ℝ-valued on
  integer arguments, so an affine phase is `fun x : ℤ => a + b * (x : ℝ)`.
* The engine is fed the *sign-corrected* phase `(−1)^k·φ`; sign correction maps the
  twist `β` to the twist `(−1)^k·β`, so it stays affine (`dk_signed_add_linear`),
  and the ζ-window `zeta_dk_window` transfers verbatim (`zeta_dk_window_twist`).

No numerals are introduced: every bound here is the landed one, untouched.
-/

namespace Salt.ExpSum

open Real Finset

/-! ## Section 0 — additivity, constants, and the affine kernel of `dk` -/

/-- `dk` is additive: `dk n (g + f) = dk n g + dk n f` (the companion of the landed
`dk_sub`). -/
lemma dk_add (g f : ℤ → ℝ) (n : ℕ) :
    ∀ m : ℤ, dk n (fun x => g x + f x) m = dk n g m + dk n f m := by
  induction n with
  | zero => intro m; rfl
  | succ n ih =>
      intro m
      rw [dk_succ, dk_succ, dk_succ, ih (m + 1), ih m]; ring

/-- Every difference of order `≥ 1` of a constant phase vanishes. -/
lemma dk_const (a : ℝ) (n : ℕ) (m : ℤ) : dk (n + 1) (fun _ : ℤ => a) m = 0 := by
  induction n generalizing m with
  | zero => rw [dk_succ]; simp
  | succ n ih => rw [dk_succ, ih (m + 1), ih m]; ring

/-- **The affine kernel of `dk`.**  If the *first* difference of `f` is the constant
`b`, then every difference of order `≥ 2` vanishes: peel from inside
(`dk_peel_inside`) and apply `dk_const`. -/
lemma dk_eq_zero_of_diff_const {f : ℤ → ℝ} {b : ℝ}
    (hf : ∀ x : ℤ, f (x + 1) - f x = b) {k : ℕ} (hk : 2 ≤ k) (m : ℤ) :
    dk k f m = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  rw [dk_peel_inside f (j + 1) m]
  have hfun : (fun x : ℤ => f (x + 1) - f x) = fun _ : ℤ => b := funext hf
  rw [hfun]
  exact dk_const b j m

/-- **`dk` annihilates a linear phase** at every order `k ≥ 2`. -/
lemma dk_linear (b : ℝ) {k : ℕ} (hk : 2 ≤ k) (m : ℤ) :
    dk k (fun x : ℤ => b * (x : ℝ)) m = 0 :=
  dk_eq_zero_of_diff_const (b := b) (fun x => by push_cast; ring) hk m

/-- **`dk` annihilates an affine phase** at every order `k ≥ 2`.  This is the
foundation stone of VK-TWIST: the twist `e(βn)` moves only the degree-1 Taylor
coefficient, which the `k`-th difference (`k ≥ 2`) never reads. -/
lemma dk_affine (a b : ℝ) {k : ℕ} (hk : 2 ≤ k) (m : ℤ) :
    dk k (fun x : ℤ => a + b * (x : ℝ)) m = 0 :=
  dk_eq_zero_of_diff_const (b := b) (fun x => by push_cast; ring) hk m

/-! ## Section 1 — VT-1(a): affine blindness of the phase -/

/-- **VT-1(a) — affine blindness (linear form).**  `dk k (f + β·id) = dk k f` for
`k ≥ 2`: the twist `e(βn)` is invisible to the `k`-th difference. -/
theorem dk_add_linear (f : ℤ → ℝ) (β : ℝ) {k : ℕ} (hk : 2 ≤ k) (m : ℤ) :
    dk k (fun x : ℤ => f x + β * (x : ℝ)) m = dk k f m := by
  have h : dk k (fun x : ℤ => f x + β * (x : ℝ)) m
      = dk k f m + dk k (fun x : ℤ => β * (x : ℝ)) m :=
    dk_add f (fun x : ℤ => β * (x : ℝ)) k m
  rw [h, dk_linear β hk m, add_zero]

/-- **VT-1(a) — affine blindness (affine form).**  `dk k (f + (a + b·id)) = dk k f`
for `k ≥ 2`. -/
theorem dk_add_affine (f : ℤ → ℝ) (a b : ℝ) {k : ℕ} (hk : 2 ≤ k) (m : ℤ) :
    dk k (fun x : ℤ => f x + (a + b * (x : ℝ))) m = dk k f m := by
  have h : dk k (fun x : ℤ => f x + (a + b * (x : ℝ))) m
      = dk k f m + dk k (fun x : ℤ => a + b * (x : ℝ)) m :=
    dk_add f (fun x : ℤ => a + b * (x : ℝ)) k m
  rw [h, dk_affine a b hk m, add_zero]

/-- Affine blindness, function form (for rewriting under binders). -/
theorem dk_add_affine_fun (f : ℤ → ℝ) (a b : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    dk k (fun x : ℤ => f x + (a + b * (x : ℝ))) = dk k f :=
  funext fun m => dk_add_affine f a b hk m

/-- Linear blindness, function form. -/
theorem dk_add_linear_fun (f : ℤ → ℝ) (β : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    dk k (fun x : ℤ => f x + β * (x : ℝ)) = dk k f :=
  funext fun m => dk_add_linear f β hk m

/-- **Sign-corrected twist.**  The engine is fed `s·φ` (with `s = (−1)^k`); the
twisted phase `s·(φ + β·id)` differs from `s·φ` by the linear `(s·β)·id`, so its
`k`-th differences (`k ≥ 2`) are unchanged. -/
theorem dk_signed_add_linear (g : ℤ → ℝ) (s β : ℝ) {k : ℕ} (hk : 2 ≤ k) (m : ℤ) :
    dk k (fun x : ℤ => s * (g x + β * (x : ℝ))) m = dk k (fun x : ℤ => s * g x) m := by
  have hfun : (fun x : ℤ => s * (g x + β * (x : ℝ)))
      = fun x : ℤ => s * g x + (s * β) * (x : ℝ) := by
    funext x; ring
  rw [hfun]
  exact dk_add_linear (fun x : ℤ => s * g x) (s * β) hk m

/-! ## Section 2 — VT-1(b): the transfer at the van der Corput entry point -/

/-- **VT-1(b) — hypothesis transfer.**  The two window hypotheses `IsVdCBound k C`
consumes hold for the twisted phase `f + affine` **iff** they hold for `f`
(`k ≥ 2`).  This is the site-by-site rewrite VK-TWIST invokes. -/
theorem dk_window_affine_iff (f : ℤ → ℝ) (a₀ β : ℝ) {k : ℕ} (hk : 2 ≤ k)
    (a b : ℤ) (lam c : ℝ) :
    ((∀ n : ℤ, a < n → n < b → lam ≤ dk k (fun x : ℤ => f x + (a₀ + β * (x : ℝ))) n)
      ∧ (∀ n : ℤ, a < n → n < b → dk k (fun x : ℤ => f x + (a₀ + β * (x : ℝ))) n ≤ c * lam))
    ↔ ((∀ n : ℤ, a < n → n < b → lam ≤ dk k f n)
      ∧ (∀ n : ℤ, a < n → n < b → dk k f n ≤ c * lam)) := by
  simp only [dk_add_affine f a₀ β hk]

/-- **VT-1(b) — the twist transfer at the vdC entry point.**  A phase `f` whose
`k`-th differences lie in the window `[λ, cλ]` on `(a, b)` gives the *same* van der
Corput bound for the **twisted** exponential sum `∑ eR (f n + (a₀ + β·n))`: the
hypotheses are read only through `dk k`, which is affine-blind. -/
theorem isVdCBound_affine {k : ℕ} (hk : 2 ≤ k) {C : ℝ} (hC : IsVdCBound k C)
    (f : ℤ → ℝ) (a₀ β : ℝ) (a b : ℤ) (lam c : ℝ) (hab : a ≤ b) (hlam : 0 < lam)
    (hc : 1 ≤ c)
    (hlb : ∀ n : ℤ, a < n → n < b → lam ≤ dk k f n)
    (hub : ∀ n : ℤ, a < n → n < b → dk k f n ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a b, eR (f n + (a₀ + β * (n : ℝ)))‖
      ≤ C * c ^ (4 / (2 : ℝ) ^ k)
        * (((b : ℝ) - a) * lam ^ (1 / ((2 : ℝ) ^ k - 2))
          + ((b : ℝ) - a) ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(1 / ((2 : ℝ) ^ k - 2)))) :=
  hC (fun x : ℤ => f x + (a₀ + β * (x : ℝ))) a b lam c hab hlam hc
    (fun n h1 h2 => by rw [dk_add_affine f a₀ β hk n]; exact hlb n h1 h2)
    (fun n h1 h2 => by rw [dk_add_affine f a₀ β hk n]; exact hub n h1 h2)

/-- **The twisted vdC bound at the uniform engine constant.**  `isVdCBound_affine`
specialised to the landed `isVdCBound_16` (`C = 16` for every `k ≥ 2`). -/
theorem isVdCBound_16_affine {k : ℕ} (hk : 2 ≤ k)
    (f : ℤ → ℝ) (a₀ β : ℝ) (a b : ℤ) (lam c : ℝ) (hab : a ≤ b) (hlam : 0 < lam)
    (hc : 1 ≤ c)
    (hlb : ∀ n : ℤ, a < n → n < b → lam ≤ dk k f n)
    (hub : ∀ n : ℤ, a < n → n < b → dk k f n ≤ c * lam) :
    ‖∑ n ∈ Finset.Ioc a b, eR (f n + (a₀ + β * (n : ℝ)))‖
      ≤ 16 * c ^ (4 / (2 : ℝ) ^ k)
        * (((b : ℝ) - a) * lam ^ (1 / ((2 : ℝ) ^ k - 2))
          + ((b : ℝ) - a) ^ (1 - 4 / (2 : ℝ) ^ k) * lam ^ (-(1 / ((2 : ℝ) ^ k - 2)))) :=
  isVdCBound_affine hk (isVdCBound_16 k hk) f a₀ β a b lam c hab hlam hc hlb hub

/-! ## Section 3 — the ζ site: the twisted phase's difference window -/

/-- **The twisted per-`n` window bound.**  For `N < n < 2N` the `k`-th forward
difference (`k = i+1 ≥ 2`) of the sign-corrected **twisted** ζ-phase
`(−1)^k·(φ(t,·) + β·id)` lies in the *same* window `[λ, cλ]` as the untwisted one
(`zeta_dk_window`): the twist is affine, and `k ≥ 2`. -/
theorem zeta_dk_window_twist (t : ℝ) (ht : 0 < t) (β : ℝ) (i : ℕ) (hi : 1 ≤ i)
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (hn1 : (N : ℤ) < n) (hn2 : n < 2 * (N : ℤ)) :
    t / (2 * π) * (i.factorial : ℝ) * (((2 * N + (i + 1) : ℕ) : ℝ) ^ (i + 1))⁻¹
        ≤ dk (i + 1) (fun m : ℤ => (-1 : ℝ) ^ (i + 1) * (phi t m + β * (m : ℝ))) n
      ∧ dk (i + 1) (fun m : ℤ => (-1 : ℝ) ^ (i + 1) * (phi t m + β * (m : ℝ))) n
        ≤ t / (2 * π) * (i.factorial : ℝ) * ((N : ℝ) ^ (i + 1))⁻¹ := by
  have hk : 2 ≤ i + 1 := Nat.succ_le_succ hi
  rw [dk_signed_add_linear (phi t) ((-1 : ℝ) ^ (i + 1)) β hk n]
  exact zeta_dk_window t ht i N hN n hn1 hn2

end Salt.ExpSum
