/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Block

/-!
# VMVT-VK rung R4 — the orbit `j*`-coordinate Diophantine spacing (`VK-POINTWISE`)

The residual piece (b) of `vk_block_core`: the box centers
`c y j* = fract(β_{j*}(y+1))` are pairwise `2δ_{j*}`-separated mod 1 (feeding
`vk_box_disjoint_avg_of_centers`'s `hsep`).

The orbit `β_{j*}(w) = vkOrbit k (vkCoef t N₀) w j*` is a degree-`k−j*` polynomial in
`w` whose linear coefficient `L = (j*+1)·c_{j*+1}` has exact magnitude
`s = t/(2π·N₀^{j*+1})`, and whose degree-`≥2` tail is geometrically dominated:
each degree-`p` term is `≤ s·|w−w'|·4^{−(p−1)}` (via the `W2c` linearity budget
`4k²Y ≤ N₀` and `C(j,j*)·(j−j*) ≤ k^{j−j*}`).  Hence for integer shifts
`w = y+1 ∈ [1,Y]`,

  `(2/3)·s·|w−w'| ≤ |β(w) − β(w')| ≤ (4/3)·s·|w−w'|`.

The lower bound with `|w−w'| ≥ 1` and `s ≥ 4δ` (`W2a`) gives separation `≥ 2δ`; the
upper bound with `s·Y ≤ 1/6` (`W2b`) gives spread `≤ 2/9 < 1/2`, so `fract` does not
collide (`|fract a − fract b| ≥ |a−b|` when `|a−b| < 1/2`).
-/

namespace Salt.Vk

open Finset Real Salt.ExpSum
open scoped BigOperators

/-- **The spacing hypothesis** (freeze `VkSpaced`).  For a coordinate `js`:
`W2a` the `js`-step `s = t/(2πN₀^{js+1})` dominates `4·δ_{js} = P^{−js−ρ}/(4k)`;
`W2b` the total drift `s·Y ≤ 1/6`; `W2c` linearity `4k²Y ≤ N₀`. -/
def VkSpaced (t : ℝ) (N₀ P Y js : ℕ) (ρbl : ℝ) (k : ℕ) : Prop :=
  (P : ℝ) ^ (-(js : ℝ) - ρbl) / (4 * k) ≤ t / (2 * π * (N₀ : ℝ) ^ (js + 1))
    ∧ t * (Y : ℝ) / (2 * π * (N₀ : ℝ) ^ (js + 1)) ≤ 1 / 6
    ∧ 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N₀ : ℝ)

/-! ## The `fract` no-collision bound -/

/-- **`fract` does not collide inside a length-`<½` window.**  If `|a − b| ≤ 1/4` and
`2δ ≤ |a − b|` (with `2δ ≤ 3/4`), then `2δ ≤ |fract a − fract b|`: the floors differ by
at most one, and the three cases `⌊a⌋−⌊b⌋ ∈ {−1,0,1}` all keep the gap `≥ 2δ`. -/
lemma fract_sub_abs_ge {a b δ : ℝ} (hδ : 2 * δ ≤ |a - b|) (hspread : |a - b| ≤ 1 / 4) :
    2 * δ ≤ |Int.fract a - Int.fract b| := by
  have hfa := Int.fract_nonneg a; have hfa1 := Int.fract_lt_one a
  have hfb := Int.fract_nonneg b; have hfb1 := Int.fract_lt_one b
  have hkey : Int.fract a - Int.fract b = (a - b) - ((⌊a⌋ : ℝ) - (⌊b⌋ : ℝ)) := by
    simp only [Int.fract]; ring
  set n : ℤ := ⌊a⌋ - ⌊b⌋ with hn
  have hnr : ((⌊a⌋ : ℝ) - (⌊b⌋ : ℝ)) = (n : ℝ) := by rw [hn]; push_cast; ring
  rw [hnr] at hkey
  have habs := abs_le.mp hspread
  -- `fract a − fract b ∈ (−1, 1)`
  have h1 : (a - b) - (n : ℝ) < 1 := by rw [← hkey]; linarith
  have h2 : (-1 : ℝ) < (a - b) - (n : ℝ) := by rw [← hkey]; linarith
  -- hence `n ∈ {−1, 0, 1}`
  have hnle : n ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have h' : (2 : ℤ) ≤ n := by omega
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h'
    linarith [habs.2, h2]
  have hnge : -1 ≤ n := by
    by_contra h
    rw [not_le] at h
    have h' : n ≤ (-2 : ℤ) := by omega
    have : (n : ℝ) ≤ -2 := by exact_mod_cast h'
    linarith [habs.1, h1]
  interval_cases n
  · -- n = −1 : fract diff = (a−b)+1 ≥ 3/4
    rw [hkey]; push_cast
    rw [abs_of_pos (by linarith [habs.1])]; linarith [habs.1, hδ, hspread]
  · -- n = 0 : fract diff = a−b
    rw [hkey]; push_cast; simpa using hδ
  · -- n = 1 : fract diff = (a−b)−1 ≤ −3/4
    rw [hkey]; push_cast
    rw [abs_of_neg (by linarith [habs.2])]; linarith [habs.2, hδ, hspread]

/-! ## The `vkCoef` magnitude -/

/-- `|vkCoef t N₀ j| = (t/2π)/(j·N₀^j)` for `t ≥ 0`, `1 ≤ j`, `0 < N₀`. -/
lemma vkCoef_abs {t : ℝ} (ht : 0 ≤ t) {N₀ : ℝ} (hN : 0 < N₀) {j : ℕ} (hj : 1 ≤ j) :
    |vkCoef t N₀ j| = (t / (2 * π)) / ((j : ℝ) * N₀ ^ j) := by
  rw [vkCoef]
  have hden : (0 : ℝ) < (j : ℝ) * N₀ ^ j := by
    have : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    positivity
  rw [abs_div, abs_mul, abs_neg]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ t / (2 * π))]
  rw [abs_of_pos hden]
  rw [abs_pow, abs_neg, abs_one, one_pow, mul_one]

/-! ## The geometric tail of the orbit -/

/-- Peel the two lowest terms of an `Icc` sum. -/
lemma sum_Icc_peel_two {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (hab : a + 1 ≤ b) :
    ∑ j ∈ Finset.Icc a b, f j = f a + f (a + 1) + ∑ j ∈ Finset.Icc (a + 2) b, f j := by
  have h1 : Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h2 : Finset.Icc (a + 1) b = insert (a + 1) (Finset.Icc (a + 2) b) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h1, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), h2,
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  abel

/-- **The binomial linearity budget.**  `C(j,js)·(j−js) ≤ k^{j−js}` for `js ≤ j ≤ k`
(via `descFactorial_le_pow` after `choose_symm_add`; the `·(j−js)` is absorbed by `p ≤ p!`). -/
lemma choose_mul_sub_le {js j k : ℕ} (hjs : js ≤ j) (hjk : j ≤ k) :
    j.choose js * (j - js) ≤ k ^ (j - js) := by
  set p := j - js with hp
  have hjp : j = js + p := by omega
  have hchoose : j.choose js = (js + p).choose p := by
    rw [hjp]; exact Nat.choose_symm_add
  have hdesc : (js + p).descFactorial p = Nat.factorial p * (js + p).choose p :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hchoose_fac : (js + p).choose p * Nat.factorial p ≤ k ^ p := by
    rw [mul_comm]
    calc Nat.factorial p * (js + p).choose p = (js + p).descFactorial p := hdesc.symm
      _ ≤ (js + p) ^ p := Nat.descFactorial_le_pow _ _
      _ ≤ k ^ p := Nat.pow_le_pow_left (by omega) p
  calc j.choose js * (j - js) = (js + p).choose p * p := by rw [hchoose, ← hp]
    _ ≤ (js + p).choose p * Nat.factorial p :=
        Nat.mul_le_mul (le_refl _) (Nat.self_le_factorial p)
    _ ≤ k ^ p := hchoose_fac

/-- **Power-difference mean-value bound.**  `|w^p − w'^p| ≤ p·Y^{p−1}·|w − w'|` for
`0 ≤ w, w' ≤ Y` (via `geom_sum₂_mul`, each of the `p` summands `≤ Y^{p−1}`). -/
lemma pow_diff_abs_le {w w' Y : ℝ} (hw'0 : 0 ≤ w') (hw'Y : w' ≤ Y) (hw0 : 0 ≤ w)
    (hwY : w ≤ Y) (p : ℕ) : |w ^ p - w' ^ p| ≤ (p : ℝ) * Y ^ (p - 1) * |w - w'| := by
  have hfact : w ^ p - w' ^ p = (∑ i ∈ Finset.range p, w ^ i * w' ^ (p - 1 - i)) * (w - w') :=
    (geom_sum₂_mul w w' p).symm
  rw [hfact, abs_mul]
  have hsum : |∑ i ∈ Finset.range p, w ^ i * w' ^ (p - 1 - i)| ≤ (p : ℝ) * Y ^ (p - 1) := by
    calc |∑ i ∈ Finset.range p, w ^ i * w' ^ (p - 1 - i)|
        ≤ ∑ i ∈ Finset.range p, |w ^ i * w' ^ (p - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range p, Y ^ (p - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          rw [abs_of_nonneg (mul_nonneg (pow_nonneg hw0 i) (pow_nonneg hw'0 _))]
          calc w ^ i * w' ^ (p - 1 - i) ≤ Y ^ i * Y ^ (p - 1 - i) :=
                mul_le_mul (pow_le_pow_left₀ hw0 hwY i) (pow_le_pow_left₀ hw'0 hw'Y _)
                  (pow_nonneg hw'0 _) (pow_nonneg (le_trans hw0 hwY) i)
            _ = Y ^ (p - 1) := by rw [← pow_add]; congr 1; omega
      _ = (p : ℝ) * Y ^ (p - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc |∑ i ∈ Finset.range p, w ^ i * w' ^ (p - 1 - i)| * |w - w'|
      ≤ ((p : ℝ) * Y ^ (p - 1)) * |w - w'| := mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
    _ = (p : ℝ) * Y ^ (p - 1) * |w - w'| := by ring

/-- **The per-term geometric bound.**  Each degree-`p` orbit-difference term
(`p = j − js ≥ 2`) is `≤ s·|w−w'|·(1/4)^{p−1}` with `s = t/(2πN₀^{js+1})`, using the
linearity budget `4k²Y ≤ N₀`. -/
lemma orbit_term_bound {t : ℝ} (ht : 0 ≤ t) {N₀ : ℝ} (hN : 0 < N₀) {k : ℕ} (hk1 : 1 ≤ k)
    {j js : ℕ} (hjs2 : js + 2 ≤ j) (hjk : j ≤ k) {Y w w' : ℝ}
    (hW2c : 4 * (k : ℝ) ^ 2 * Y ≤ N₀) (hw'0 : 0 ≤ w') (hw'Y : w' ≤ Y)
    (hw0 : 0 ≤ w) (hwY : w ≤ Y) :
    |(j.choose js : ℝ) * vkCoef t N₀ j * (w ^ (j - js) - w' ^ (j - js))|
      ≤ t / (2 * π * N₀ ^ (js + 1)) * |w - w'| * (1 / 4) ^ (j - js - 1) := by
  have hj1 : 1 ≤ j := by omega
  set p := j - js with hp
  set q := j - js - 1 with hq
  have hpq : p = q + 1 := by omega
  have hq1 : 1 ≤ q := by omega
  have hY0 : 0 ≤ Y := le_trans hw0 hwY
  -- factor out the common phase amplitude and shift
  set Q : ℝ := t / (2 * π) * |w - w'| with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  -- the choose·(j−js) ≤ j·k^{2q} nat bound, cast
  have hnat : (j.choose js : ℝ) * (p : ℝ) ≤ (j : ℝ) * (k : ℝ) ^ (2 * q) := by
    have h1 : j.choose js * p ≤ k ^ p := choose_mul_sub_le (by omega) hjk
    have h2 : k ^ p ≤ k ^ (2 * q) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : k ^ (2 * q) ≤ j * k ^ (2 * q) := Nat.le_mul_of_pos_left _ (by omega)
    have : j.choose js * p ≤ j * k ^ (2 * q) := le_trans (le_trans h1 h2) h3
    calc (j.choose js : ℝ) * (p : ℝ) = ((j.choose js * p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((j * k ^ (2 * q) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (j : ℝ) * (k : ℝ) ^ (2 * q) := by push_cast; ring
  -- the reduced core inequality
  have hfinal : (j.choose js : ℝ) * (p : ℝ) * Y ^ q ≤ (j : ℝ) * (1 / 4) ^ q * N₀ ^ q := by
    have hkY : (k : ℝ) ^ 2 * Y ≤ N₀ / 4 := by nlinarith [hW2c]
    have hkY0 : 0 ≤ (k : ℝ) ^ 2 * Y := by positivity
    calc (j.choose js : ℝ) * (p : ℝ) * Y ^ q
        ≤ ((j : ℝ) * (k : ℝ) ^ (2 * q)) * Y ^ q :=
          mul_le_mul_of_nonneg_right hnat (by positivity)
      _ = (j : ℝ) * ((k : ℝ) ^ 2 * Y) ^ q := by
          rw [pow_mul, mul_assoc, ← mul_pow]
      _ ≤ (j : ℝ) * (N₀ / 4) ^ q :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hkY0 hkY q) (by positivity)
      _ = (j : ℝ) * (1 / 4) ^ q * N₀ ^ q := by
          rw [show N₀ / 4 = N₀ * (1 / 4) by ring, mul_pow]; ring
  -- assemble the per-term bound
  have hNjs : (0 : ℝ) < N₀ ^ (js + 1) := by positivity
  have hjNj : (0 : ℝ) < (j : ℝ) * N₀ ^ j := by
    have : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    positivity
  have hcross : (j.choose js : ℝ) * (p : ℝ) * Y ^ q * N₀ ^ (js + 1)
      ≤ (1 / 4) ^ q * ((j : ℝ) * N₀ ^ j) := by
    have hNj : N₀ ^ j = N₀ ^ (js + 1) * N₀ ^ q := by rw [← pow_add]; congr 1; omega
    calc (j.choose js : ℝ) * (p : ℝ) * Y ^ q * N₀ ^ (js + 1)
        ≤ ((j : ℝ) * (1 / 4) ^ q * N₀ ^ q) * N₀ ^ (js + 1) :=
          mul_le_mul_of_nonneg_right hfinal (by positivity)
      _ = (1 / 4) ^ q * ((j : ℝ) * N₀ ^ j) := by rw [hNj]; ring
  have hAB : (j.choose js : ℝ) * (p : ℝ) * Y ^ q / ((j : ℝ) * N₀ ^ j)
      ≤ (1 / 4) ^ q / N₀ ^ (js + 1) := by
    rw [div_le_div_iff₀ hjNj hNjs]; linarith [hcross]
  -- rewrite both sides through Q
  have hvk := vkCoef_abs ht hN hj1
  have hpd := pow_diff_abs_le hw'0 hw'Y hw0 hwY p
  have hCnn : (0 : ℝ) ≤ (j.choose js : ℝ) := by positivity
  calc |(j.choose js : ℝ) * vkCoef t N₀ j * (w ^ p - w' ^ p)|
      = (j.choose js : ℝ) * |vkCoef t N₀ j| * |w ^ p - w' ^ p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hCnn]
    _ ≤ (j.choose js : ℝ) * ((t / (2 * π)) / ((j : ℝ) * N₀ ^ j))
          * ((p : ℝ) * Y ^ (p - 1) * |w - w'|) := by
        rw [hvk]
        apply mul_le_mul_of_nonneg_left hpd
        positivity
    _ = Q * ((j.choose js : ℝ) * (p : ℝ) * Y ^ q / ((j : ℝ) * N₀ ^ j)) := by
        rw [hQ, show p - 1 = q from by omega]; ring
    _ ≤ Q * ((1 / 4) ^ q / N₀ ^ (js + 1)) := mul_le_mul_of_nonneg_left hAB hQ0
    _ = t / (2 * π * N₀ ^ (js + 1)) * |w - w'| * (1 / 4) ^ (j - js - 1) := by
        rw [hQ, ← hq]; ring

/-- Partial geometric sum: `∑_{i<n} (1/4)^i ≤ 4/3`. -/
lemma geom_quarter_range_le (n : ℕ) : ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i ≤ 4 / 3 := by
  have h := geom_sum_mul (1 / 4 : ℝ) n
  have hpow : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := by positivity
  nlinarith [h, hpow]

/-- **The orbit geometric tail.**  `∑_{j∈Icc(js+2)k} (1/4)^{j−js−1} ≤ 1/3` (the exponents
`j−js−1` are distinct and `≥ 1`, so the sum is dominated by `∑_{i≥1}(1/4)^i = 1/3`). -/
lemma orbit_tail_geom_le (js k : ℕ) :
    ∑ j ∈ Finset.Icc (js + 2) k, (1 / 4 : ℝ) ^ (j - js - 1) ≤ 1 / 3 := by
  have hinj : ∀ x ∈ Finset.Icc (js + 2) k, ∀ y ∈ Finset.Icc (js + 2) k,
      x - js - 1 = y - js - 1 → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_Icc] at hx hy; omega
  have himg : (Finset.Icc (js + 2) k).image (fun j => j - js - 1) ⊆ Finset.Icc 1 k := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Icc] at hj ⊢; omega
  calc ∑ j ∈ Finset.Icc (js + 2) k, (1 / 4 : ℝ) ^ (j - js - 1)
      = ∑ i ∈ (Finset.Icc (js + 2) k).image (fun j => j - js - 1), (1 / 4 : ℝ) ^ i :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.Icc 1 k, (1 / 4 : ℝ) ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => by positivity)
    _ ≤ 1 / 3 := by
        have hsplit : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
          ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
        have hrange : ∑ i ∈ Finset.range (k + 1), (1 / 4 : ℝ) ^ i
            = 1 + ∑ i ∈ Finset.Icc 1 k, (1 / 4 : ℝ) ^ i := by
          rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]; norm_num
        have hle := geom_quarter_range_le (k + 1)
        linarith [hrange, hle]

/-! ## The orbit difference and its linear leading term -/

/-- **The orbit-difference tail bound.**  Writing the `js`-orbit difference as its linear
term `L·(w−w')` (`L = (js+1)·c_{js+1}`) plus a degree-`≥2` tail, the tail is bounded by
`(1/3)·s·|w−w'|` with `s = t/(2πN₀^{js+1})`. -/
lemma vkOrbit_diff_sub_linear_bound {t : ℝ} (ht : 0 ≤ t) {N₀ : ℝ} (hN : 0 < N₀) {k js : ℕ}
    (hk1 : 1 ≤ k) (hjsk : js + 1 ≤ k) {Y w w' : ℝ} (hW2c : 4 * (k : ℝ) ^ 2 * Y ≤ N₀)
    (hw'0 : 0 ≤ w') (hw'Y : w' ≤ Y) (hw0 : 0 ≤ w) (hwY : w ≤ Y) :
    |vkOrbit k (vkCoef t N₀) w js - vkOrbit k (vkCoef t N₀) w' js
        - ((js + 1 : ℕ) : ℝ) * vkCoef t N₀ (js + 1) * (w - w')|
      ≤ 1 / 3 * (t / (2 * π * N₀ ^ (js + 1))) * |w - w'| := by
  set c := vkCoef t N₀ with hc
  set s := t / (2 * π * N₀ ^ (js + 1)) with hs
  have hs0 : 0 ≤ s * |w - w'| := by rw [hs]; positivity
  have hdiff : vkOrbit k c w js - vkOrbit k c w' js
      = ∑ j ∈ Finset.Icc js k, ((j.choose js : ℝ) * c j * (w ^ (j - js) - w' ^ (j - js))) := by
    rw [vkOrbit, vkOrbit, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hdiff, sum_Icc_peel_two
    (fun j => (j.choose js : ℝ) * c j * (w ^ (j - js) - w' ^ (j - js))) hjsk]
  have e1 : (js.choose js : ℝ) * c js * (w ^ (js - js) - w' ^ (js - js)) = 0 := by
    simp
  have e2 : ((js + 1).choose js : ℝ) * c (js + 1)
        * (w ^ ((js + 1) - js) - w' ^ ((js + 1) - js))
      = ((js + 1 : ℕ) : ℝ) * c (js + 1) * (w - w') := by
    have hch : (js + 1).choose js = js + 1 := by
      rw [Nat.choose_symm_add, Nat.choose_one_right]
    rw [hch, show (js + 1) - js = 1 from by omega]; push_cast; ring
  rw [e1, e2]
  have hcollapse : (0 : ℝ) + ((js + 1 : ℕ) : ℝ) * c (js + 1) * (w - w')
      + (∑ j ∈ Finset.Icc (js + 2) k, (j.choose js : ℝ) * c j * (w ^ (j - js) - w' ^ (j - js)))
      - ((js + 1 : ℕ) : ℝ) * c (js + 1) * (w - w')
      = ∑ j ∈ Finset.Icc (js + 2) k, (j.choose js : ℝ) * c j * (w ^ (j - js) - w' ^ (j - js)) := by
    ring
  rw [hcollapse]
  calc |∑ j ∈ Finset.Icc (js + 2) k, (j.choose js : ℝ) * c j * (w ^ (j - js) - w' ^ (j - js))|
      ≤ ∑ j ∈ Finset.Icc (js + 2) k,
          |(j.choose js : ℝ) * c j * (w ^ (j - js) - w' ^ (j - js))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc (js + 2) k, s * |w - w'| * (1 / 4) ^ (j - js - 1) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        exact orbit_term_bound ht hN hk1 hj.1 hj.2 hW2c hw'0 hw'Y hw0 hwY
    _ = s * |w - w'| * ∑ j ∈ Finset.Icc (js + 2) k, (1 / 4) ^ (j - js - 1) := by
        rw [Finset.mul_sum]
    _ ≤ s * |w - w'| * (1 / 3) := mul_le_mul_of_nonneg_left (orbit_tail_geom_le js k) hs0
    _ = 1 / 3 * s * |w - w'| := by ring

/-- The linear orbit coefficient `L = (js+1)·c_{js+1}` has magnitude exactly
`s = t/(2πN₀^{js+1})`. -/
lemma vkOrbit_linear_abs {t : ℝ} (ht : 0 ≤ t) {N₀ : ℝ} (hN : 0 < N₀) (js : ℕ) :
    |((js + 1 : ℕ) : ℝ) * vkCoef t N₀ (js + 1)| = t / (2 * π * N₀ ^ (js + 1)) := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((js + 1 : ℕ) : ℝ)),
    vkCoef_abs ht hN (by omega : 1 ≤ js + 1)]
  have hjs1 : ((js + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hNne : N₀ ≠ 0 := ne_of_gt hN
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## The orbit `fract`-separation (residual (b)) -/

/-- **The `j*`-coordinate Diophantine spacing** (freeze residual (b)).  Under `VkSpaced`,
for integer shifts `w, w' ∈ [1,Y]` at distance `≥ 1`, the `fract`-reduced `js`-orbit centers
are `2δ_{js}`-separated (`δ_{js} = P^{−js−ρ}/(16k)`).  Combines the two-sided orbit bound
`(2/3)s|w−w'| ≤ |β(w)−β(w')| ≤ (4/3)s|w−w'|` with the no-collision `fract` bound. -/
lemma vk_orbit_fract_sep {t : ℝ} {N₀ P Y js k : ℕ} {ρbl : ℝ}
    (hk : 1 ≤ k) (hjsk : js + 1 ≤ k)
    (hspaced : VkSpaced t N₀ P Y js ρbl k)
    {w w' : ℝ} (hw1 : 1 ≤ w) (hwY : w ≤ (Y : ℝ)) (hw'1 : 1 ≤ w') (hw'Y : w' ≤ (Y : ℝ))
    (hne : (1 : ℝ) ≤ |w - w'|) :
    2 * ((P : ℝ) ^ (-(js : ℝ) - ρbl) / (16 * (k : ℝ)))
      ≤ |Int.fract (vkOrbit k (vkCoef t N₀) w js)
          - Int.fract (vkOrbit k (vkCoef t N₀) w' js)| := by
  obtain ⟨hW2a, hW2b, hW2c⟩ := hspaced
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hYR : (1 : ℝ) ≤ (Y : ℝ) := le_trans hw1 hwY
  have hN : (0 : ℝ) < (N₀ : ℝ) := by
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hYpos : (0 : ℝ) < (Y : ℝ) := by linarith
    have hpos : (0 : ℝ) < 4 * (k : ℝ) ^ 2 * (Y : ℝ) := by positivity
    linarith [hW2c]
  set s := t / (2 * π * (N₀ : ℝ) ^ (js + 1)) with hs
  set δ := (P : ℝ) ^ (-(js : ℝ) - ρbl) / (16 * (k : ℝ)) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have h4δ : 4 * δ ≤ s := by
    have he : 4 * δ = (P : ℝ) ^ (-(js : ℝ) - ρbl) / (4 * (k : ℝ)) := by rw [hδ]; ring
    rw [he]; exact hW2a
  have hsnn : 0 ≤ s := le_trans (by linarith) h4δ
  have hden : (0 : ℝ) < 2 * π * (N₀ : ℝ) ^ (js + 1) := by positivity
  have ht : 0 ≤ t := by
    by_contra h; rw [not_le] at h
    have : s < 0 := by rw [hs]; exact div_neg_of_neg_of_pos h hden
    linarith
  have hw0 : 0 ≤ w := by linarith
  have hw'0 : 0 ≤ w' := by linarith
  have hrest := vkOrbit_diff_sub_linear_bound ht hN hk hjsk hW2c hw'0 hw'Y hw0 hwY
  have hLabs := vkOrbit_linear_abs ht hN js
  rw [← hs] at hrest hLabs
  set D := vkOrbit k (vkCoef t N₀) w js - vkOrbit k (vkCoef t N₀) w' js with hDdef
  set X := ((js + 1 : ℕ) : ℝ) * vkCoef t N₀ (js + 1) * (w - w') with hXdef
  have hXabs : |X| = s * |w - w'| := by rw [hXdef, abs_mul, hLabs]
  set M := s * |w - w'| with hM
  -- hrest : |D - X| ≤ 1/3 * s * |w-w'|; normalize the RHS to 1/3 * M
  have hrestM : |D - X| ≤ 1 / 3 * M := by rw [hM, ← mul_assoc]; exact hrest
  have hup : |D| ≤ |X| + |D - X| := by
    have h := abs_add_le X (D - X)
    rw [show X + (D - X) = D from by ring] at h
    exact h
  have hlo : |X| ≤ |D| + |D - X| := by
    have h := abs_add_le D (X - D)
    rw [show D + (X - D) = X from by ring, abs_sub_comm X D] at h
    exact h
  rw [hXabs] at hup hlo
  have hDlow : 2 / 3 * M ≤ |D| := by linarith [hlo, hrestM]
  have hDhigh : |D| ≤ 4 / 3 * M := by linarith [hup, hrestM]
  have hMs : s ≤ M := by
    rw [hM]
    calc s = s * 1 := (mul_one s).symm
      _ ≤ s * |w - w'| := mul_le_mul_of_nonneg_left hne hsnn
  have hδsep : 2 * δ ≤ |D| := by linarith [hDlow, hMs, h4δ, hδ0]
  have hwwY : |w - w'| ≤ (Y : ℝ) := by rw [abs_le]; constructor <;> linarith
  have hsY : s * (Y : ℝ) ≤ 1 / 6 := by
    have he : s * (Y : ℝ) = t * (Y : ℝ) / (2 * π * (N₀ : ℝ) ^ (js + 1)) := by rw [hs]; ring
    rw [he]; exact hW2b
  have hMY : M ≤ s * (Y : ℝ) := by rw [hM]; exact mul_le_mul_of_nonneg_left hwwY hsnn
  have hspreadD : |D| ≤ 1 / 4 := by linarith [hDhigh, hMY, hsY]
  exact fract_sub_abs_ge hδsep hspreadD

end Salt.Vk
