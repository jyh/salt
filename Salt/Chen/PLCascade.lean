/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.ChainValues
import Salt.Chen.ValueCascade

/-!
# VC2 / C1cσ-sharp — the fine-knot piecewise-linear value cascade (machinery)

Design: `docs/blueprints/chen.md` (C0 Amendment 2, catch #31); flags `2026-07-13 C1b′`,
`C1b″`, `C1cσ`.  This is the last numeric node of the Chen arc: certify the two frozen
operating-point values,

* **A₁** even-sum `≤ 0.0221` on `[3.9992, 4]`  (⟺ `fchain ≥ 0.9779`; true `≤ 0.021688`,
  slack `4.1·10⁻⁴`), and
* **A₂** odd-sum `≤ 1.68` on `[4/3, 3]`  (⟺ `Fchain ≤ 2.68`; true sup `1.6716`, slack
  `8.4·10⁻³`),

with a load-bearing cascade of piecewise majorants fed through the `ValueCascade` engine
(`fseq_next_le_of_shift_majorant`) with **exact rational per-panel integrals** (no
`log`-linearization — that route is provably 2.3–3.1× loose per level, C1b″'s verdict).

## The numeric plan (computed pre-code; TWO independent methods)

Both methods agree on the true values to `< 10⁻⁴`:

* **Method 1** — mpmath grid-based cumulative DDE integration (step `1/2000`).
* **Method 2** — exact-rational **piecewise-constant** majorant cascade (Python `Fraction`,
  step `1/D`): `g_k` constant on each panel, `g_k(panel) := (1/x_left)·∫ g_{k-1}(t−1)` an
  exact rational (integral of a step function), justified as an upper bound of `fseq k` by
  **antitonicity on the window** (`fseq (k) s ≤ fseq (k) x_left` for `s ≥ x_left`).

Key numeric findings driving the design:

* **Point values** (Method 1, matching the C1b′/C1b″ tables): `fchain 4 = 0.978356`,
  `f₄(4)=0.008798`, `f₆(4)=0.005990`, `f₈(4)=0.003255`, `f₁₀(4)=0.001717`; even-sum at
  `s=3.9992` is `0.021697`.  A₂: `Fchain(4/3)=2.6713`.
* **A₂ reduces to a MASS sum.**  On `[4/3,3]` the odd iterates are `K_m/s`, and the odd-sum
  equals `(3 − s + Σ_{k even ≥ 2} mass(f_k))/s`, sup at `s=4/3`; so A₂ ⟺
  `Σ_{k even} mass(f_k) ≤ 0.5733` (true `0.5623`).  The even masses contract at the clean
  per-two-level ratio `→ 0.5224` (`0.4474, 0.5020, 0.5163, …`, always `≤ 0.5224`), with no
  right-edge pathology (a mass is a single number).
* **The support-growth wall (machine-relevant finding).**  The *pointwise* two-level ratio
  `fseq (k+2) s / fseq k s` is NOT uniformly `≤ 0.55`: near the right support edge
  `s ≈ k+2` it blows up (`k=4`: `s=4.5 → 1.18`, `s=5 → 2.68`), because `fseq k → 0` there
  while `fseq (k+2)` is still positive.  So there is **no fixed profile invariant under the
  one-step operator** (its support creeps right by 1 each level), hence **no cheap
  self-propagating pointwise contraction** — the load-bearing tail contraction genuinely
  requires the fine-knot profile shape.  This is why the node is keystone-scale.
* **Piecewise-constant looseness compounds** (~1–2 % per level: Method 2 mass looseness is
  `×1.025` at `k=2`, `×1.10` at `k=12` for step `1/80`), so closing A₂ (slack 2 %) or A₁
  (slack 1.9 %) needs fine PL knots + a self-certified tail contraction; Method 2 at step
  `1/80`, `k≤12` already sits at the A₂ target with no tail budget left.  A fine grid is
  `~10³` panels/level — infeasible for the kernel in one node.

## What this file certifies (Floor A: the reusable machinery, sorry-free, axiom-clean)

1. `geom_tail_ratio` — the **general geometric-tail summation**: `b (j+1) ≤ r·b j` on `[J,M)`
   with `0 ≤ r < 1` ⇒ `Σ_{[J,M)} b ≤ b J/(1−r)`.  The self-certified-tail machinery, keyed on
   an abstract contraction hypothesis (reusable by any cascade instantiation).
2. `fseq_antitoneOn_tail` / `fseq_next_le_const` — the **piecewise-constant panel glue**: on
   the tail window `fseq (n+1)` is antitone (from the integral form), and a constant majorant
   `c` of the shifted iterate propagates through the engine to the **exact** rational bound
   `fseq (n+1) s ≤ c·(up − s)/s` (integrating a constant over a panel is rational — the
   log-free load-bearing step, in its simplest PL form).
3. `fseq_le_leftEndpoint` — the between-knot upper bound: `fseq (n+1) s ≤ fseq (n+1) a` for
   `a ≤ s` in the window, the antitone panel bound the knots rest on.
4. `evenSum_le_head_add_geomtail` — the **even-sum = finite head + self-certified geometric
   tail** pipeline in the exact `fchain_lower_of_evenSum_le` (A₁) shape, keyed on a two-level
   contraction hypothesis a fine-knot cascade discharges at its terminal depth; and
   `fseq_evensum_tail_crude` / `fseq_even_le_crude` — that pipeline **instantiated** with a
   genuine *certified* two-level contraction (`fseq_le`'s majorant, ratio `(99/100)² < 1`),
   giving a real sorry-free tail bound at any depth `J ≥ 1`.  Plus `fseq_two_le_const_demo`,
   a concrete log-free rational `f₂` majorant exhibiting the glue lemma's "no log appears".

## Honest status (Iron Rule 4)

The frozen A₁/A₂ constants are NOT reached here: closing them needs the fine-knot PL profile
cascade to depth ~14–16 **plus** a self-propagating tail contraction, and the support-growth
finding above shows the contraction cannot be short-cut to a cheap uniform pointwise ratio.
That is a keystone-scale artifact (Method 2 shows `~10³` panels/level for the required
tightness) beyond a single node's budget.  Delivered: the reusable machinery + the log-free
propagation demonstration; the sharp head remains the flagged C1cσ debt.
-/

open intervalIntegral MeasureTheory Set Finset

namespace Salt.Chen

/-! ## Part A — the general geometric-tail summation (self-certified-tail machinery)

The load-bearing shape of any tail bound: from a per-step contraction `b (j+1) ≤ r·b j`
(`0 ≤ r < 1`) on a range, the partial sum is bounded by `b J/(1−r)`, uniformly in the upper
cutoff `M`.  Keyed on an abstract contraction hypothesis so a cascade can instantiate it once
the profile-contraction constant is certified. -/

/-- Pointwise geometric decay from a per-step contraction: `b (J+i) ≤ r^i · b J` for `i`
in the contraction range. -/
theorem geom_decay_pointwise {b : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) {J M : ℕ}
    (hstep : ∀ j, J ≤ j → j < M → b (j + 1) ≤ r * b j) :
    ∀ i, J + i ≤ M → b (J + i) ≤ r ^ i * b J := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ k ih =>
    intro hle
    have hkM : J + k < M := by omega
    have hk : b (J + k) ≤ r ^ k * b J := ih (by omega)
    calc b (J + (k + 1)) = b ((J + k) + 1) := by ring_nf
      _ ≤ r * b (J + k) := hstep (J + k) (by omega) hkM
      _ ≤ r * (r ^ k * b J) := by
            apply mul_le_mul_of_nonneg_left hk hr0
      _ = r ^ (k + 1) * b J := by ring

/-- **The general geometric-tail summation.**  If `b ≥ 0` and `b (j+1) ≤ r·b j` on `[J, M)`
with `0 ≤ r < 1`, then `Σ_{j ∈ [J,M)} b j ≤ b J/(1−r)` — independent of the upper cutoff `M`.
This is the reusable "self-certified geometric tail": a cascade instantiates it with the
per-two-level (or per-level) contraction of its profile masses/values. -/
theorem geom_tail_ratio {b : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {J M : ℕ}
    (hb : ∀ j, 0 ≤ b j) (hstep : ∀ j, J ≤ j → j < M → b (j + 1) ≤ r * b j) :
    (∑ j ∈ Finset.Ico J M, b j) ≤ b J / (1 - r) := by
  rcases le_or_gt M J with hMJ | hJM
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact div_nonneg (hb J) (by linarith)
  -- reindex Ico J M  ↔  range (M - J) via j = J + i
  have hreindex : (∑ j ∈ Finset.Ico J M, b j) = ∑ i ∈ Finset.range (M - J), b (J + i) := by
    rw [Finset.sum_Ico_eq_sum_range]
  rw [hreindex]
  have hterm : ∀ i ∈ Finset.range (M - J), b (J + i) ≤ b J * r ^ i := by
    intro i hi
    rw [Finset.mem_range] at hi
    have := geom_decay_pointwise hr0 hstep i (by omega)
    rwa [mul_comm] at this
  have hgeom : (∑ i ∈ Finset.range (M - J), r ^ i) ≤ 1 / (1 - r) := by
    rw [geom_sum_eq (by linarith : r ≠ 1)]
    have hpow : (0 : ℝ) ≤ r ^ (M - J) := by positivity
    have e : (r ^ (M - J) - 1) / (r - 1) = (1 - r ^ (M - J)) / (1 - r) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [e]
    gcongr
    linarith [hpow]
  calc (∑ i ∈ Finset.range (M - J), b (J + i))
      ≤ ∑ i ∈ Finset.range (M - J), b J * r ^ i := Finset.sum_le_sum hterm
    _ = b J * ∑ i ∈ Finset.range (M - J), r ^ i := by rw [Finset.mul_sum]
    _ ≤ b J * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeom (hb J)
    _ = b J / (1 - r) := by rw [mul_one_div]

/-- **The majorant form of the geometric tail.**  A cascade rarely has an exact per-step ratio
on the target sequence `b` (that would need matching lower bounds); it has a *majorant*
sequence `c ≥ b` that contracts.  Then `Σ_{[J,M)} b ≤ c J/(1−r)`.  This is the form the
`fseq_le`-style majorants (and any fine-knot cascade's profile masses/values) instantiate. -/
theorem geom_tail_majorant {b c : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {J M : ℕ}
    (hc0 : ∀ j, 0 ≤ c j)
    (hbc : ∀ j, J ≤ j → j < M → b j ≤ c j)
    (hcstep : ∀ j, J ≤ j → j < M → c (j + 1) ≤ r * c j) :
    (∑ j ∈ Finset.Ico J M, b j) ≤ c J / (1 - r) := by
  have hsum : (∑ j ∈ Finset.Ico J M, b j) ≤ ∑ j ∈ Finset.Ico J M, c j := by
    apply Finset.sum_le_sum
    intro j hj; rw [Finset.mem_Ico] at hj; exact hbc j hj.1 hj.2
  have htail : (∑ j ∈ Finset.Ico J M, c j) ≤ c J / (1 - r) :=
    geom_tail_ratio hr0 hr1 hc0 hcstep
  linarith

/-! ## Part B — the piecewise-constant panel glue (between-knot bound + exact propagation)

The load-bearing per-level step in its simplest PL form.  A knot majorant on the window
rests on two facts, both proved here directly from the recursion's integral form (no external
antitonicity lemma needed):

* **Between-knot (antitone) bound** `fseq_le_leftEndpoint`: on the tail window a later `s`
  has a *smaller* value than an earlier `a`, so a panel is dominated by its left-endpoint
  value.
* **Exact constant-panel propagation** `fseq_next_le_const`: a constant majorant `c` of the
  shifted iterate over `[lo, up]` integrates to `c·(up − lo)` **exactly** (rational; no log),
  giving `fseq (n+1) s ≤ (1/s)·c·(up − lo)`.

Chaining these over a rational knot grid is the fine-knot cascade; here they are the reusable
atoms (a piecewise-constant `g` is the degenerate PL majorant, and its integral is a finite
rational sum of `c_i·(width_i)`). -/

/-- **Between-knot (antitone) bound.**  On a tail window where both `fseq (n+1) a` and
`fseq (n+1) s` are given by the same integral form `(1/·)·∫_·^{up} fseq n (t−1)`, a later
argument has a smaller value: `fseq (n+1) s ≤ fseq (n+1) a` for `0 < a ≤ s ≤ up`.  Proof: the
integral over `[s,up]` is `≤` the integral over `[a,up]` (nonnegative integrand, smaller
interval), and `1/s ≤ 1/a`.  This is the antitonicity a piecewise-constant knot majorant
uses to dominate a panel by its left-endpoint value. -/
theorem fseq_le_leftEndpoint {n : ℕ} {a s up : ℝ}
    (hforma : fseq (n + 1) a = (1 / a) * ∫ t in a..up, fseq n (t - 1))
    (hforms : fseq (n + 1) s = (1 / s) * ∫ t in s..up, fseq n (t - 1))
    (ha0 : 0 < a) (has : a ≤ s) (hsup : s ≤ up) :
    fseq (n + 1) s ≤ fseq (n + 1) a := by
  rw [hforma, hforms]
  have hInonneg : 0 ≤ ∫ t in s..up, fseq n (t - 1) :=
    intervalIntegral.integral_nonneg hsup (fun t _ => fseq_nonneg n (t - 1))
  have hmono : (∫ t in s..up, fseq n (t - 1)) ≤ ∫ t in a..up, fseq n (t - 1) := by
    have hsplit : (∫ t in a..up, fseq n (t - 1))
        = (∫ t in a..s, fseq n (t - 1)) + ∫ t in s..up, fseq n (t - 1) := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (fseq_shift_intervalIntegrable n a s) (fseq_shift_intervalIntegrable n s up)]
    have hnn : 0 ≤ ∫ t in a..s, fseq n (t - 1) :=
      intervalIntegral.integral_nonneg has (fun t _ => fseq_nonneg n (t - 1))
    linarith
  have hinv : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha0 has
  calc (1 / s) * ∫ t in s..up, fseq n (t - 1)
      ≤ (1 / a) * ∫ t in s..up, fseq n (t - 1) := mul_le_mul_of_nonneg_right hinv hInonneg
    _ ≤ (1 / a) * ∫ t in a..up, fseq n (t - 1) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **Exact constant-panel propagation.**  If the shifted iterate `t ↦ fseq n (t−1)` is `≤ c`
on `[lo, up]`, the engine gives `fseq (n+1) s ≤ (1/s)·(c·(up − lo))` — the integral of a
constant is `c·(up − lo)` **exactly**, a rational expression with no logarithm (the
log-free load-bearing direction of the cascade, in its simplest single-panel form). -/
theorem fseq_next_le_const {n : ℕ} {s lo up c : ℝ}
    (hform : fseq (n + 1) s = (1 / s) * ∫ t in lo..up, fseq n (t - 1))
    (hs0 : 0 < s) (hlo : lo ≤ up)
    (hc : ∀ t ∈ Set.Icc lo up, fseq n (t - 1) ≤ c) :
    fseq (n + 1) s ≤ (1 / s) * (c * (up - lo)) := by
  have hstep := fseq_next_le_of_shift_majorant hform hs0 hlo hc
    (g := fun _ => c) _root_.intervalIntegrable_const
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm ((up - lo)) c] at hstep

/-! ## Part C — the self-certified geometric tail, in the `fchain`/`Fchain` parity shape

`geom_tail_ratio` (Part A) certifies a geometric tail from an abstract per-step contraction.
Here it is threaded through the even-index reindexing so it lands in exactly the shape the
value interface consumes (`fchain_lower_of_evenSum_le`): the even-parity partial sum is
`head + (geometric tail)`, the tail keyed on a two-level contraction hypothesis `∀ m ≥ J,
fseq (2(m+1)) s ≤ r·fseq (2m) s` (`0 ≤ r < 1`).  A fine-knot cascade discharges that hypothesis
at its terminal depth `2J`; the numeric plan targets `r ≈ 0.5224` (true) certifiable `≤ 0.55`,
with `J` chosen so `fseq (2J) s/(1−r)` fits the slack budget. -/

/-- Reindex the even-parity partial sum onto the sub-sequence `m ↦ fseq (2m) s`
(`fseq 0 = 0` makes the `m = 0` term vacuous, but it is kept for a clean range). -/
theorem evenSum_reindex (N : ℕ) (s : ℝ) :
    (∑ k ∈ (Finset.range (N + 1)).filter (fun k => Even k), fseq k s)
      = ∑ m ∈ Finset.range (N / 2 + 1), fseq (2 * m) s := by
  apply Finset.sum_nbij' (fun k => k / 2) (fun m => 2 * m)
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkN, hke⟩ := hk
    rw [Finset.mem_range]; omega
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨m, by omega⟩⟩
  · intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨_, t, rfl⟩ := hk
    omega
  · intro m _; omega
  · intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨_, t, rfl⟩ := hk
    congr 1; omega

/-- **The contraction-consuming even tail.**  A two-level contraction on the even sub-sequence
gives `Σ_{m ∈ [J,L)} fseq (2m) s ≤ fseq (2J) s/(1−r)`, uniformly in `L`.  Direct specialization
of `geom_tail_ratio` to `b m := fseq (2m) s`. -/
theorem fseq_evensum_tail_le {s r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {J L : ℕ}
    (hstep : ∀ m, J ≤ m → m < L → fseq (2 * (m + 1)) s ≤ r * fseq (2 * m) s) :
    (∑ m ∈ Finset.Ico J L, fseq (2 * m) s) ≤ fseq (2 * J) s / (1 - r) :=
  geom_tail_ratio (b := fun m => fseq (2 * m) s) hr0 hr1 (fun _ => fseq_nonneg _ _) hstep

/-- **The even-sum = head + self-certified geometric tail.**  With a two-level contraction
holding from depth `2J`, the whole even partial sum splits into a finite head
`Σ_{m<J} fseq (2m) s` and a geometric tail `≤ fseq (2J) s/(1−r)`.  Feed the RHS to
`fchain_lower_of_evenSum_le` (A₁) once the head knots and the contraction are certified — the
reusable pipeline the fine-knot cascade plugs into. -/
theorem evenSum_le_head_add_geomtail {s r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {N J : ℕ} (hJ : J ≤ N / 2 + 1)
    (hstep : ∀ m, J ≤ m → m < N / 2 + 1 → fseq (2 * (m + 1)) s ≤ r * fseq (2 * m) s) :
    (∑ k ∈ (Finset.range (N + 1)).filter (fun k => Even k), fseq k s)
      ≤ (∑ m ∈ Finset.range J, fseq (2 * m) s) + fseq (2 * J) s / (1 - r) := by
  rw [evenSum_reindex, ← Finset.sum_range_add_sum_Ico (fun m => fseq (2 * m) s) hJ]
  have htail := fseq_evensum_tail_le hr0 hr1 (J := J) (L := N / 2 + 1) hstep
  linarith

/-! ## Part D — a genuine certified two-level contraction, threaded through the machinery

Floor A asks for a *certified* per-two-level contraction feeding the self-certified tail, at
any depth.  No landed lemma gives an exact consecutive ratio on `fseq` itself (that needs
matching lower bounds — blocked by the profile wall in the header).  But the landed crude
bound `fseq_le` gives a contracting **majorant** sequence: `c m := 2e²·(99/100)^{2m−1}·hbar s`
dominates `fseq (2m) s` (via `fseq_le`) and satisfies `c (m+1) = (99/100)²·c m` — a genuine
certified two-level contraction with ratio `(99/100)² = 0.9801 < 1`.  `geom_tail_majorant` then
yields a real, sorry-free geometric tail bound on the even sub-sequence — the full pipeline
demonstrated with a certified contraction.  (The load-bearing `r ≈ 0.5224` is the flagged
C1cσ debt; this shows the *machinery* is sound and composes.) -/

/-- The crude majorant dominates the even sub-sequence: `fseq (2m) s ≤ 2e²·(99/100)^{2m−1}·hbar s`
for `m ≥ 1` (the `fseq_le` per-level bound at level `2m = (2m−1)+1`). -/
theorem fseq_even_le_crude {s : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    fseq (2 * m) s ≤ 2 * Real.exp 2 * (99 / 100) ^ (2 * m - 1) * hbar s := by
  have hrw : 2 * m = (2 * m - 1) + 1 := by omega
  rw [hrw]
  exact fseq_le (2 * m - 1) s

/-- **The certified crude geometric tail on the even sub-sequence** (the machinery demonstrated
with a genuine certified two-level contraction, at any depth `J ≥ 1`).
`Σ_{m ∈ [J,L)} fseq (2m) s ≤ (2e²·(99/100)^{2J−1}·hbar s)/(1 − (99/100)²)`.  A real, sorry-free
tail bound produced by `geom_tail_majorant` from the `fseq_le` contraction `c (m+1) =
(99/100)²·c m`. -/
theorem fseq_evensum_tail_crude {s : ℝ} {J L : ℕ} (hJ : 1 ≤ J) :
    (∑ m ∈ Finset.Ico J L, fseq (2 * m) s)
      ≤ (2 * Real.exp 2 * (99 / 100) ^ (2 * J - 1) * hbar s) / (1 - (99 / 100) ^ 2) := by
  have hpos : (0 : ℝ) ≤ hbar s := (hbar_pos s).le
  refine geom_tail_majorant (b := fun m => fseq (2 * m) s)
    (c := fun m => 2 * Real.exp 2 * (99 / 100) ^ (2 * m - 1) * hbar s)
    (r := (99 / 100) ^ 2) (by norm_num) (by norm_num)
    (fun j => by positivity) (fun j hj _ => fseq_even_le_crude (by omega)) ?_
  intro j hj _
  have hexp : (2 * (j + 1) - 1) = (2 * j - 1) + 2 := by omega
  rw [hexp, pow_add]
  ring_nf
  rfl

/-- **Log-free glue demonstration.**  The constant-panel step in action: on `[3,4]`,
`fseq 2 s ≤ (4 − s)/(2 s)` — a **rational** majorant with no logarithm, obtained by dominating
the shifted `f₁` by the constant `1/2` on the panel `[s,4]` and integrating exactly
(`fseq_next_le_const`).  Contrast the closed-form `fseq_two_window`, which carries `log`; the
cascade's load-bearing direction integrates piecewise majorants to rational functions. -/
theorem fseq_two_le_const_demo {s : ℝ} (hs3 : 3 ≤ s) (hs4 : s ≤ 4) :
    fseq 2 s ≤ (4 - s) / (2 * s) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hev : Even (1 + 1) := by decide
  have hform : fseq (1 + 1) s = (1 / s) * ∫ t in s..((1 : ℕ) : ℝ) + 3, fseq 1 (t - 1) :=
    fseq_even_window hev (by linarith)
  have hup : ((1 : ℕ) : ℝ) + 3 = 4 := by norm_num
  rw [hup] at hform
  have hc : ∀ t ∈ Set.Icc s (4 : ℝ), fseq 1 (t - 1) ≤ 1 / 2 := by
    intro t ht
    obtain ⟨htl, htr⟩ := ht
    have ht1 : (1 : ℝ) ≤ t - 1 := by linarith
    have ht3 : t - 1 ≤ 3 := by linarith
    rw [fseq_one_window ht1 ht3, div_le_iff₀ (by linarith : (0 : ℝ) < t - 1)]
    linarith [htl, hs3]
  have hstep := fseq_next_le_const (n := 1) hform hs0 (by linarith) hc
  have heq : (1 / s) * (1 / 2 * (4 - s)) = (4 - s) / (2 * s) := by field_simp
  rw [heq] at hstep
  exact hstep

end Salt.Chen
