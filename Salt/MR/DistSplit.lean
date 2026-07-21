/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PretentiousTriangle
import Salt.MR.NonPret
import Salt.MR.HalaszSeam

/-!
# MR wave-3 rung H3 — the `𝔻`-split / recentering layer (`DistSplit`)

The distance-algebra core of the H3 recentering (`s8-freeze.md:33`, R3.1
`dist_split_A4`): the reusable `pretDistSq` lemmas that transfer a distance floor
from `f` to the windowed–twisted `f·g_J`, and between frequency centers.  The
concrete numeral/branch bookkeeping and the window-loss (MULT-SHIU) bound live in
the consuming `PropA3Core` rung; this file is the pure algebra beneath it.

## The two engines (both grounded in landed surfaces)

1. **The `fg_J`-vs-`f` halving** (`dist_split_A4`).  The keystone stone.  From the
   landed reverse-triangle halving `dist_mul_half`
   (`PretentiousTriangle.lean:213`, `(1/2)·𝔻(f,h)² − 𝔻(f,g)² ≤ 𝔻(g,h)²`),
   instantiated at the *middle* argument `g ↦ g_J` and third argument `h ↦ n^{it}`,
   an `f`-side floor `Lf ≤ 𝔻(f, n^{it})²` and a window-loss bound `𝔻(f, g_J)² ≤ W`
   yield `(1/2)·Lf − W ≤ 𝔻(g_J, n^{it})²` — the halved `1/32` form.
   **`dist_mul_half` ORIENTATION VERDICT (confirmed AT CONSUMPTION):** the general
   `{f g h}` halving instantiates with its middle slot `g` set to the windowed
   factor and its third slot `h` set to the twist `costwist t`; the produced
   `𝔻(g_J, costwist t)²` floor is exactly the R3.1 target.  No re-orientation is
   needed — the frozen `dist_mul_half` statement already faces the right way.

2. **The center-to-center transfer** (`dist_recenter` / `dist_recenter_sq`).  The
   character translation-invariance `pretDistSq_costwist_shift`
   (`𝔻(n^{it₁}, n^{it})² = 𝔻(1, n^{i(t−t₁)})²`) plus the landed triangle
   inequality `pretDist_triangle` give the reverse-triangle recentering
   `𝔻(f, n^{it}) ≥ 𝔻(1, n^{i(t−t₁)}) − 𝔻(f, n^{it₁})` (branch b of R3.1).  This is
   the center-`t₀` exit that REPLACES GS[10] Lemma 7.1 (I-3 gate-check verdict);
   NO Lipschitz machinery is imported.

## Contents
* `norm_costwist_le`, `costwist_add`, `costwist_conj` — the unimodular character algebra.
* `pretDistSq_comm` / `pretDist_comm` — symmetry of the pretentious distance.
* `pretDistSq_costwist_shift` / `pretDist_costwist_shift` — the center transfer core.
* `dist_recenter` / `dist_recenter_sq` — the reverse-triangle recentering (branch b).
* `dist_split_A4` — the `fg_J`-vs-`f` halving keystone.
* `dist_split_A4_recentered` — branch b fully composed (recenter ▸ halve).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## The unimodular character algebra of `costwist` -/

/-- The `n^{it}` twist is 1-bounded (unimodular): `‖costwist t n‖ ≤ 1`. -/
lemma norm_costwist_le (t : ℝ) (n : ℕ) : ‖costwist t n‖ ≤ 1 := by
  rw [show ‖costwist t n‖ = 1 from by unfold costwist; exact Complex.norm_exp_ofReal_mul_I _]

/-- Additivity of the phase: `n^{it_a}·n^{it_b} = n^{i(t_a+t_b)}`. -/
lemma costwist_add (a b : ℝ) (n : ℕ) : costwist a n * costwist b n = costwist (a + b) n := by
  unfold costwist
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Conjugation flips the phase: `conj (n^{it}) = n^{-it}`. -/
lemma costwist_conj (a : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (costwist a n) = costwist (-a) n := by
  unfold costwist
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-! ## Symmetry of the pretentious distance -/

/-- **`pretDistSq` is symmetric.**  `𝔻(f, g; x)² = 𝔻(g, f; x)²` (the summand
`1 − Re(f·conj g)` is unchanged under swapping, since `Re(g·conj f) = Re(f·conj g)`). -/
theorem pretDistSq_comm (f g : ℕ → ℂ) (x : ℝ) :
    pretDistSq f g x = pretDistSq g f x := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hre : (f p * (starRingEnd ℂ) (g p)).re = (g p * (starRingEnd ℂ) (f p)).re := by
    rw [Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [hre]

/-- **`pretDist` is symmetric.**  `𝔻(f, g; x) = 𝔻(g, f; x)`. -/
theorem pretDist_comm (f g : ℕ → ℂ) (x : ℝ) : pretDist f g x = pretDist g f x := by
  unfold pretDist; rw [pretDistSq_comm]

/-! ## The center-to-center transfer (character translation invariance) -/

/-- **The center shift** (branch-b core).  `𝔻(n^{it₁}, n^{it}; x)² = 𝔻(1, n^{i(t−t₁)}; x)²`:
the pretentious distance between two pure characters depends only on the frequency
difference, because `n^{it₁}·conj(n^{it}) = n^{-i(t−t₁)}` has the same real part
(`cos((t−t₁)log p)`) as `1·conj(n^{i(t−t₁)})`. -/
theorem pretDistSq_costwist_shift (t₁ t x : ℝ) :
    pretDistSq (costwist t₁) (costwist t) x
      = pretDistSq (fun _ => 1) (costwist (t - t₁)) x := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hre : (costwist t₁ p * (starRingEnd ℂ) (costwist t p)).re
      = ((fun _ : ℕ => (1 : ℂ)) p * (starRingEnd ℂ) (costwist (t - t₁) p)).re := by
    change (costwist t₁ p * (starRingEnd ℂ) (costwist t p)).re
      = ((1 : ℂ) * (starRingEnd ℂ) (costwist (t - t₁) p)).re
    rw [costwist_conj t p, costwist_add t₁ (-t) p, one_mul, costwist_conj (t - t₁) p,
      show t₁ + -t = -(t - t₁) from by ring]
  rw [hre]

/-- **The center shift, `pretDist` form.**  `𝔻(n^{it₁}, n^{it}; x) = 𝔻(1, n^{i(t−t₁)}; x)`. -/
theorem pretDist_costwist_shift (t₁ t x : ℝ) :
    pretDist (costwist t₁) (costwist t) x = pretDist (fun _ => 1) (costwist (t - t₁)) x := by
  unfold pretDist; rw [pretDistSq_costwist_shift]

/-- **The recentering reverse-triangle** (R3.1 branch b; GS[10] Lemma 7.1 REPLACED).
For 1-bounded `f`, `𝔻(1, n^{i(t−t₁)}; x) − 𝔻(f, n^{it₁}; x) ≤ 𝔻(f, n^{it}; x)`:
the distance floor of `f` against the far frequency `n^{it}` is recovered from the
`f = 1` floor at the *shifted* frequency `t − t₁` minus the (small) center distance
at `t₁`.  Proof: `pretDist_triangle` on `(n^{it₁}, f, n^{it})`, then the center shift
and symmetry. -/
theorem dist_recenter {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t t₁ x : ℝ) :
    pretDist (fun _ => 1) (costwist (t - t₁)) x - pretDist f (costwist t₁) x
      ≤ pretDist f (costwist t) x := by
  have htri := pretDist_triangle (f := costwist t₁) (g := f) (h := costwist t) x
    (norm_costwist_le t₁) hf (norm_costwist_le t)
  rw [pretDist_costwist_shift] at htri
  rw [pretDist_comm f (costwist t₁) x]
  linarith [htri]

/-- **The recentering, squared** (R3.1 branch b, the `(√(1/4) − √(1/16))²` form).
Given a floor `L ≤ 𝔻(1, n^{i(t−t₁)}; x)²`, a center cap `𝔻(f, n^{it₁}; x)² ≤ S`, and
`S ≤ L` (so the shifted floor dominates the center), the far distance obeys
`(√L − √S)² ≤ 𝔻(f, n^{it}; x)²`.  With `L = (1/4)loglog`, `S = (1/16)loglog` this is
the `(1/16)loglog` `f`-floor the halving then turns into `(1/32)loglog`. -/
theorem dist_recenter_sq {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {t t₁ x L S : ℝ}
    (hL : L ≤ pretDistSq (fun _ => 1) (costwist (t - t₁)) x)
    (hS : pretDistSq f (costwist t₁) x ≤ S) (hSL : S ≤ L) :
    (Real.sqrt L - Real.sqrt S) ^ 2 ≤ pretDistSq f (costwist t) x := by
  have hrec := dist_recenter hf t t₁ x
  have h1 : Real.sqrt L ≤ pretDist (fun _ => 1) (costwist (t - t₁)) x := by
    unfold pretDist; exact Real.sqrt_le_sqrt hL
  have h2 : pretDist f (costwist t₁) x ≤ Real.sqrt S := by
    unfold pretDist; exact Real.sqrt_le_sqrt hS
  have h3 : Real.sqrt L - Real.sqrt S ≤ pretDist f (costwist t) x := by
    linarith [hrec, h1, h2]
  have hnn : 0 ≤ Real.sqrt L - Real.sqrt S := by
    have := Real.sqrt_le_sqrt hSL; linarith
  have hsq : pretDist f (costwist t) x ^ 2 = pretDistSq f (costwist t) x :=
    Real.sq_sqrt (pretDistSq_nonneg f (costwist t) x hf (norm_costwist_le t))
  have hmul : (Real.sqrt L - Real.sqrt S) * (Real.sqrt L - Real.sqrt S)
      ≤ pretDist f (costwist t) x * pretDist f (costwist t) x :=
    mul_le_mul h3 h3 hnn (le_trans hnn h3)
  calc (Real.sqrt L - Real.sqrt S) ^ 2
      = (Real.sqrt L - Real.sqrt S) * (Real.sqrt L - Real.sqrt S) := by ring
    _ ≤ pretDist f (costwist t) x * pretDist f (costwist t) x := hmul
    _ = pretDist f (costwist t) x ^ 2 := by ring
    _ = pretDistSq f (costwist t) x := hsq

/-! ## The `fg_J`-vs-`f` halving — the keystone -/

/-- **R3.1 `dist_split_A4` — the `fg_J`-vs-`f` halving** (the keystone stone).  For
1-bounded `f`, `g_J` and any twist `costwist t`, an `f`-side floor `Lf ≤ 𝔻(f, n^{it})²`
and a window-loss bound `𝔻(f, g_J)² ≤ W` give
`(1/2)·Lf − W ≤ 𝔻(g_J, n^{it})²` — the halved floor transferred onto the windowed
factor.  Consumes the landed `dist_mul_half` at the orientation verified above
(middle argument `↦ g_J`, third `↦ costwist t`).  Instantiate `g_J ↦ fgJ f t₀ y Y`
downstream; the loss `W` is the R3.1/A2 (MULT-SHIU) window mass, carried here as the
named hypothesis `hloss` (the sanctioned conditional form). -/
theorem dist_split_A4 {f gJ : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hgJ : ∀ n, ‖gJ n‖ ≤ 1)
    {t x Lf W : ℝ}
    (hfloor : Lf ≤ pretDistSq f (costwist t) x)
    (hloss : pretDistSq f gJ x ≤ W) :
    (1 / 2) * Lf - W ≤ pretDistSq gJ (costwist t) x := by
  have hkey := dist_mul_half (f := f) (g := gJ) (h := costwist t) x hf hgJ (norm_costwist_le t)
  linarith [hkey, hfloor, hloss]

/-- **R3.1 branch b, fully composed.**  The recentering (`dist_recenter_sq`) produces
the `f`-floor `(√L − √S)²`, which the halving (`dist_split_A4`) transfers onto `g_J`:
`(1/2)·(√L − √S)² − W ≤ 𝔻(g_J, n^{it})²`.  This is R3.1's branch-b conclusion up to
the numeral instantiation `L = (1/4)loglog`, `S = (1/16)loglog` (giving `(1/32)loglog`)
and the window-loss bound `W`, both discharged by `PropA3Core`. -/
theorem dist_split_A4_recentered {f gJ : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hgJ : ∀ n, ‖gJ n‖ ≤ 1) {t t₁ x L S W : ℝ}
    (hL : L ≤ pretDistSq (fun _ => 1) (costwist (t - t₁)) x)
    (hS : pretDistSq f (costwist t₁) x ≤ S) (hSL : S ≤ L)
    (hloss : pretDistSq f gJ x ≤ W) :
    (1 / 2) * (Real.sqrt L - Real.sqrt S) ^ 2 - W ≤ pretDistSq gJ (costwist t) x :=
  dist_split_A4 hf hgJ (dist_recenter_sq hf hL hS hSL) hloss

/-- **R3.1, on the concrete windowed factor `fg_J`.**  `dist_split_A4` specialized to
`g_J ↦ fgJ f t₀ y Y` (the seam's windowed–twisted `f`, `HalaszSeam.lean:269`):
an `f`-side floor `Lf ≤ 𝔻(f, n^{it})²` and the window-loss bound
`𝔻(f, fg_J)² ≤ W` give `(1/2)·Lf − W ≤ 𝔻(fg_J, n^{it})²` — R3.1's frozen conclusion
shape up to the `Lf = (1/16)loglog` / `W`-numeral discharge in `PropA3Core`.  The
1-boundedness of `fg_J` is `norm_fgJ_le` (unimodular twist × `{0,1}` window). -/
theorem dist_split_fgJ {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t₀ y Y : ℝ) {t x Lf W : ℝ}
    (hfloor : Lf ≤ pretDistSq f (costwist t) x)
    (hloss : pretDistSq f (fgJ f t₀ y Y) x ≤ W) :
    (1 / 2) * Lf - W ≤ pretDistSq (fgJ f t₀ y Y) (costwist t) x :=
  dist_split_A4 hf (norm_fgJ_le hf t₀ y Y) hfloor hloss

end Salt.MR
