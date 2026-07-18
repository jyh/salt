/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.StarStep
import Salt.Maynard.TauSpike

/-!
# The star-step residual on the honest window (HB-ENGINE, WP1, node HB-L4b)

The concrete discharge of the `S⁽²⁾ − S⁽³⁾` exceptional majorant sum on HB's honest
support window.  The master inequality `S2_sub_S3_le` (`Salt.HB.StarStep`) bounds
`|S⁽²⁾ − S⁽³⁾|` by the exceptional-majorant sum
`Σ_{n∈A} (starErrBound χ z n · τ(n+2)log(n+2) + τ(n)log n · starErrBound χ z (n+2))`;
this file discharges that sum to the HB-Lemma-4 grade `C·x^{1+2ε}log²x / z + junk`.

## The mechanism (and the P-coprimality resolution of catch #80)

`HasExcSq χ z m` (`StarStep`) is `∃ p prime, p²∣m ∧ ¬(p < z ∧ χ_ℝ(p) = −1)` — the
honest exceptional set is `{p ≥ z} ∪ {p < z : χ_ℝ(p) ≠ −1}`, i.e. it *also* contains
the small `χ_ℝ(p) ∈ {0,1}` prime squares that the landed `Λ*` truncation does not kill.
The house resolution (design `HB-L4 adjudicated`): **no `Λ*` def change is needed** —
on HB's support `(n(n+2), q·P) = 1` the P-coprimality KILLS every small `χ ≠ −1` prime
square, collapsing the exceptional set to `p ≥ z` exactly as the paper states.

Here that P is realized as **`excPrimorial χ z = ∏_{p<z prime, χ_ℝ(p) ≠ −1} p`** — the
minimal honest modulus.  It subsumes HB's `q·P`:

* `χ_ℝ(p) = 0` (i.e. `p ∣ q`, `p < z`): in `excPrimorial` — the `q`-part;
* `χ_ℝ(p) = +1`, `2 < p < z`: in `excPrimorial` — HB's `P`-part; and
* **`p = 2` with `χ_ℝ(2) = +1`** (the gap HB's `P = ∏_{2<p<z}` misses): also in
  `excPrimorial`.  So the honest window's coprimality **forces `n` odd exactly when
  `χ_ℝ(2) ≠ −1`** — the honest twin case — with no separate oddness hypothesis.  When
  `χ_ℝ(2) = −1`, `p = 2` is a *small `χ = −1`* prime, never a `HasExcSq` witness, so no
  oddness is needed.  This is the clean resolution of the p = 2 direction flag.

## The rungs

* **`excSq_ge_z_of_window`** — the support collapse (the stone): on the coprime window
  every `HasExcSq` witness prime is `≥ z`.
* **`dvd_count_Ioc_le` / `card_shift_eq` / `shift_count_le`** — the interval square-
  multiple counts (the `n` and shifted `n+2` sides).
* **`exc_sum_le`** — the fibration + count master: the exceptional-`n` weight sum,
  union-bounded over the witness prime square then per-prime counted, is
  `≤ Wsq · (2x/z + √(2x+2))` (`Wsq` a uniform product-weight cap).
* **`hstar_window`** — the node: with the crude `τ ≤ C_ε·m^ε` weight
  (`card_divisors_le_rpow`), the honest bound
  `≤ 2·(C_ε (2x+2)^ε log(2x+2))² · (2x/z + √(2x+2))` (grade `x^{1+2ε}log²x/z + x^{½+2ε}log²x`).
* **`S2_sub_S3_window`** — composed with `S2_sub_S3_le`: `|S⁽²⁾ − S⁽³⁾|` on the window.

R4 framing: this discharges the star step (Lemma 4 transfer) only; the *analytic*
control of the remaining sums to level `x^{1/2+δ}` is the Kloosterman wall (R4, the
documented death rung).  No twin claim here — a transfer-error estimate.
-/

open Finset
open scoped ArithmeticFunction
open Salt.TwinBar

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the honest small-prime modulus and the support collapse -/

open Classical in
/-- **The honest exceptional modulus** `P = ∏_{p < z prime, χ_ℝ(p) ≠ −1} p`.  The
    minimal squarefree modulus whose coprimality kills every *small non-`χ=−1`* prime
    square (the `q`-part `χ_ℝ = 0`, HB's `P`-part `χ_ℝ = +1` for `2 < p`, and the
    `p = 2`, `χ_ℝ(2) = +1` case HB's `∏_{2<p<z}` misses). -/
noncomputable def excPrimorial (χ : DirichletCharacter ℂ q) (z : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p ≠ -1), p

/-- **The support collapse (the stone).**  On the honest window (`n(n+2)` coprime to
    `excPrimorial χ z`), any exceptional square of a factor `t ∣ n(n+2)` is a `p ≥ z`
    square: the small `χ_ℝ(p) ≠ −1` witnesses are all removed by the P-coprimality, so
    the honest exceptional set collapses to `p ≥ z`, exactly the paper's display. -/
lemma excSq_ge_z_of_window (χ : DirichletCharacter ℂ q) (z : ℕ) {n t : ℕ}
    (hcop : Nat.Coprime (n * (n + 2)) (excPrimorial χ z))
    (ht : t ∣ n * (n + 2)) (hE : HasExcSq χ z t) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ t ∧ z ≤ p := by
  obtain ⟨p, hp, hpt, hne⟩ := hE
  rcases Nat.lt_or_ge p z with hpz | hpz
  · exfalso
    have hchi : chiRe χ p ≠ -1 := fun h => hne ⟨hpz, h⟩
    have hmem : p ∈ (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p ≠ -1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpz, hp, hchi⟩
    have hdvdP : p ∣ excPrimorial χ z := Finset.dvd_prod_of_mem _ hmem
    have hpn : p ∣ n * (n + 2) :=
      (((dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0) : p ∣ p ^ 2).trans hpt).trans ht)
    have hgcd : p ∣ Nat.gcd (n * (n + 2)) (excPrimorial χ z) := Nat.dvd_gcd hpn hdvdP
    have hc1 : Nat.gcd (n * (n + 2)) (excPrimorial χ z) = 1 := hcop
    rw [hc1] at hgcd
    exact hp.ne_one (Nat.dvd_one.mp hgcd)
  · exact ⟨p, hp, hpt, hpz⟩

/-! ## §2 — the interval square-multiple counts -/

/-- **The general interval square-multiple count.**  At most `(b−a)/k + 1` integers of
    `(a, b]` are divisible by `k` (the two floors `b/k`, `a/k` differ by `≤ (b−a)/k + 1`).
    Feeds both the `n`-side (`a = x`, `b = 2x`) and the shifted `n+2`-side. -/
lemma dvd_count_Ioc_le {a b k : ℕ} (hk : 0 < k) (hab : a ≤ b) :
    (((Finset.Ioc a b).filter (fun n => k ∣ n)).card : ℝ)
      ≤ ((b : ℝ) - (a : ℝ)) / (k : ℝ) + 1 := by
  have hdisj : Disjoint (Finset.Ioc 0 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    rw [Finset.mem_Ioc] at hn1 hn2; omega
  have hdisjf : Disjoint ((Finset.Ioc 0 a).filter (fun m => k ∣ m))
      ((Finset.Ioc a b).filter (fun m => k ∣ m)) :=
    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj
  have hcardunion : ((Finset.Ioc 0 b).filter (fun m => k ∣ m)).card
      = ((Finset.Ioc 0 a).filter (fun m => k ∣ m)).card
        + ((Finset.Ioc a b).filter (fun m => k ∣ m)).card := by
    rw [← Finset.card_union_of_disjoint hdisjf, ← Finset.filter_union,
        Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hcardunion
  have hcast : ((((Finset.Ioc a b).filter (fun m => k ∣ m)).card : ℕ) : ℝ)
      = ((b / k : ℕ) : ℝ) - ((a / k : ℕ) : ℝ) := by
    have hnat : (((Finset.Ioc a b).filter (fun m => k ∣ m)).card : ℕ) = b / k - a / k := by
      omega
    rw [hnat, Nat.cast_sub (by omega)]
  rw [hcast]
  have hb : ((b / k : ℕ) : ℝ) ≤ (b : ℝ) / (k : ℝ) := Nat.cast_div_le
  have ha : (a : ℝ) / (k : ℝ) < ((a / k : ℕ) : ℝ) + 1 := by
    have hmod : (k : ℝ) * ((a / k : ℕ) : ℝ) + ((a % k : ℕ) : ℝ) = (a : ℝ) := by
      exact_mod_cast Nat.div_add_mod a k
    have hlt : ((a % k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast Nat.mod_lt a hk
    have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [div_lt_iff₀ hk']
    have hexp : (((a / k : ℕ) : ℝ) + 1) * (k : ℝ) = (k : ℝ) * ((a / k : ℕ) : ℝ) + (k : ℝ) := by
      ring
    rw [hexp]; linarith
  have hbak : ((b : ℝ) - (a : ℝ)) / (k : ℝ) = (b : ℝ) / (k : ℝ) - (a : ℝ) / (k : ℝ) := by
    rw [sub_div]
  rw [hbak]; linarith

/-- The `n+2`-side reindex: `#{n∈(x,2x] : k∣(n+2)} = #{m∈(x+2,2x+2] : k∣m}` via `n ↦ n+2`. -/
lemma card_shift_eq (x k : ℕ) :
    ((Finset.Ioc x (2 * x)).filter (fun n => k ∣ (n + 2))).card
      = ((Finset.Ioc (x + 2) (2 * x + 2)).filter (fun m => k ∣ m)).card := by
  apply Finset.card_bij (fun n _ => n + 2)
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    exact ⟨⟨by omega, by omega⟩, h3⟩
  · intro n1 _ n2 _ h; omega
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨h1, h2⟩, h3⟩ := hm
    refine ⟨m - 2, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hm2 : m - 2 + 2 = m := by omega
    rw [hm2]; exact h3

/-- **The shifted square-multiple count.**  `#{n∈(x,2x] : p²∣(n+2)} ≤ x/p² + 1` — the
    `n+2`-side count, via `card_shift_eq` and `dvd_count_Ioc_le` on `(x+2, 2x+2]`. -/
lemma shift_count_le {x p : ℕ} (hp : 0 < p) :
    (((Finset.Ioc x (2 * x)).filter (fun n => p ^ 2 ∣ (n + 2))).card : ℝ)
      ≤ (x : ℝ) / (p : ℝ) ^ 2 + 1 := by
  rw [card_shift_eq]
  have hc := dvd_count_Ioc_le (a := x + 2) (b := 2 * x + 2) (k := p ^ 2)
    (pow_pos hp 2) (by omega)
  refine le_trans hc (le_of_eq ?_)
  push_cast; ring

/-! ## §3 — the fibration + count master -/

/-- **The fibration + count master.**  For a dyadic window `A ⊆ (x, 2x]` on which every
    `HasExcSq χ z (target n)` witness collapses to a `p ≥ z` square (`hcollapse`), the
    exceptional-`n` product-weight sum is majorized by the union bound over the witness
    prime square: each exceptional `n` is caught by its witness `p ∈ (z, √(2x+2)]`, the
    per-prime count is `≤ x/p² + 1` (`hcount`), the `p ≥ z` reciprocal-square tail is
    `≤ 2/z` (`sq_recip_tail_le`) and the `+1` count is `≤ √(2x+2)` primes.  Uniform
    product-weight cap `Wsq`. -/
lemma exc_sum_le (χ : DirichletCharacter ℂ q) (z x : ℕ) (hz : 1 ≤ z)
    (A : Finset ℕ) (target : ℕ → ℕ)
    (htgt : ∀ n ∈ A, 1 ≤ target n ∧ target n ≤ 2 * x + 2)
    (hcollapse : ∀ n ∈ A, HasExcSq χ z (target n) →
        ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ target n ∧ z ≤ p)
    (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (Wsq : ℝ) (hWpos : 0 ≤ Wsq) (hW : ∀ n ∈ A, g n ≤ Wsq)
    (hcount : ∀ p : ℕ, 0 < p →
        ((A.filter (fun n => p ^ 2 ∣ target n)).card : ℝ) ≤ (x : ℝ) / (p : ℝ) ^ 2 + 1) :
    ∑ n ∈ A.filter (fun n => HasExcSq χ z (target n)), g n
      ≤ Wsq * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
  set M := Nat.sqrt (2 * x + 2) with hM
  set Q := (Finset.Ioc (z - 1) M).filter (fun p => p.Prime) with hQ
  -- each exceptional n has its witness prime square in Q
  have hwit : ∀ n ∈ A.filter (fun n => HasExcSq χ z (target n)),
      ∃ p ∈ Q, p ^ 2 ∣ target n := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnA, hnE⟩ := hn
    obtain ⟨p, hp, hpdvd, hpz⟩ := hcollapse n hnA hnE
    have htn := htgt n hnA
    have hple : p ≤ M := by
      rw [hM]; apply Nat.le_sqrt.mpr
      have hp2 : p ^ 2 ≤ target n := Nat.le_of_dvd (by omega) hpdvd
      have : p * p = p ^ 2 := (sq p).symm
      omega
    refine ⟨p, ?_, hpdvd⟩
    rw [hQ, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, hple⟩, hp⟩
  -- the fibration: sum over exceptional n ≤ sum over Q of the p²-fiber weight sums
  have hfib : ∑ n ∈ A.filter (fun n => HasExcSq χ z (target n)), g n
      ≤ ∑ p ∈ Q, ∑ n ∈ A.filter (fun n => p ^ 2 ∣ target n), g n := by
    calc ∑ n ∈ A.filter (fun n => HasExcSq χ z (target n)), g n
        ≤ ∑ n ∈ A.filter (fun n => HasExcSq χ z (target n)),
            ∑ p ∈ Q.filter (fun p => p ^ 2 ∣ target n), g n := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨p, hpQ, hpdvd⟩ := hwit n hn
          exact Finset.single_le_sum (f := fun _ => g n) (fun i _ => hg n)
            (Finset.mem_filter.mpr ⟨hpQ, hpdvd⟩)
      _ = ∑ n ∈ A.filter (fun n => HasExcSq χ z (target n)),
            ∑ p ∈ Q, (if p ^ 2 ∣ target n then g n else 0) := by
          apply Finset.sum_congr rfl; intro n _; rw [Finset.sum_filter]
      _ = ∑ p ∈ Q, ∑ n ∈ A.filter (fun n => HasExcSq χ z (target n)),
            (if p ^ 2 ∣ target n then g n else 0) := Finset.sum_comm
      _ = ∑ p ∈ Q, ∑ n ∈ (A.filter (fun n => HasExcSq χ z (target n))).filter
            (fun n => p ^ 2 ∣ target n), g n := by
          apply Finset.sum_congr rfl; intro p _; rw [← Finset.sum_filter]
      _ ≤ ∑ p ∈ Q, ∑ n ∈ A.filter (fun n => p ^ 2 ∣ target n), g n := by
          apply Finset.sum_le_sum; intro p _
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
          · intro n _ _; exact hg n
  -- the count: each fiber weight sum ≤ Wsq · (x/p² + 1)
  have hfiber : ∀ p ∈ Q, ∑ n ∈ A.filter (fun n => p ^ 2 ∣ target n), g n
      ≤ Wsq * ((x : ℝ) / (p : ℝ) ^ 2 + 1) := by
    intro p hpQ
    have hp : p.Prime := (Finset.mem_filter.mp hpQ).2
    calc ∑ n ∈ A.filter (fun n => p ^ 2 ∣ target n), g n
        ≤ ∑ _n ∈ A.filter (fun n => p ^ 2 ∣ target n), Wsq := by
          apply Finset.sum_le_sum; intro n hn
          exact hW n (Finset.filter_subset _ _ hn)
      _ = Wsq * ((A.filter (fun n => p ^ 2 ∣ target n)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ Wsq * ((x : ℝ) / (p : ℝ) ^ 2 + 1) :=
          mul_le_mul_of_nonneg_left (hcount p hp.pos) hWpos
  -- the tail: sum the fiber bounds, split into the z⁻¹ tail and the √-junk
  have htail : ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 / (z : ℝ) := by
    apply sq_recip_tail_le hz Q
    · intro p hpQ
      have := (Finset.mem_filter.mp hpQ).1; rw [Finset.mem_Ioc] at this; omega
    · intro p hpQ
      have := (Finset.mem_filter.mp hpQ).1; rw [Finset.mem_Ioc] at this
      exact Nat.lt_succ_of_le this.2
  have hcardle : (Q.card : ℝ) ≤ (M : ℝ) := by
    have h1 : Q.card ≤ M := by
      rw [hQ]
      calc ((Finset.Ioc (z - 1) M).filter (fun p => p.Prime)).card
          ≤ (Finset.Ioc (z - 1) M).card := Finset.card_filter_le _ _
        _ = M - (z - 1) := Nat.card_Ioc _ _
        _ ≤ M := by omega
    exact_mod_cast h1
  have hsplit : ∑ p ∈ Q, ((x : ℝ) / (p : ℝ) ^ 2 + 1)
      = (x : ℝ) * (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) + (Q.card : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro p _; rw [div_eq_mul_one_div]
  calc ∑ n ∈ A.filter (fun n => HasExcSq χ z (target n)), g n
      ≤ ∑ p ∈ Q, ∑ n ∈ A.filter (fun n => p ^ 2 ∣ target n), g n := hfib
    _ ≤ ∑ p ∈ Q, Wsq * ((x : ℝ) / (p : ℝ) ^ 2 + 1) := Finset.sum_le_sum hfiber
    _ = Wsq * (∑ p ∈ Q, ((x : ℝ) / (p : ℝ) ^ 2 + 1)) := by rw [Finset.mul_sum]
    _ ≤ Wsq * (2 * (x : ℝ) / (z : ℝ) + (M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hWpos
        rw [hsplit]
        have hxnn : (0 : ℝ) ≤ (x : ℝ) := by positivity
        have hstep : (x : ℝ) * (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (x : ℝ) * (2 / (z : ℝ)) :=
          mul_le_mul_of_nonneg_left htail hxnn
        have hxz : (x : ℝ) * (2 / (z : ℝ)) = 2 * (x : ℝ) / (z : ℝ) := by ring
        linarith

/-! ## §4 — the assembled star-step residual on the honest window (the node) -/

/-- **Node HB-L4b — the star-step residual on the honest window.**  On a dyadic window
    `A ⊆ (x, 2x]` whose support is coprime to `excPrimorial χ z` (the honest HB support
    `(n(n+2), q·P) = 1`, realized minimally), the exceptional majorant sum of the star
    step is bounded to the HB-Lemma-4 grade.  With the crude divisor weight
    `τ(m) ≤ C_ε·m^ε` (`card_divisors_le_rpow`), the honest final shape is
    `2·(C_ε (2x+2)^ε log(2x+2))² · (2x/z + √(2x+2))`
    — grade `x^{1+2ε}log²x / z` (the paper's `x·z⁻¹`) plus the `x^{½+2ε}log²x`
    prime-count junk.  The `p = 2`/oddness gap is resolved by `excPrimorial` including
    `2` exactly when `χ_ℝ(2) ≠ −1` (see module header). -/
theorem hstar_window (χ : DirichletCharacter ℂ q) (z x : ℕ) (hz : 1 ≤ z)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Ioc x (2 * x))
    (hcop : ∀ n ∈ A, Nat.Coprime (n * (n + 2)) (excPrimorial χ z))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∑ n ∈ A, (starErrBound χ z n * tauLog (n + 2)
          + tauLog n * starErrBound χ z (n + 2))
        ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
            * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
  obtain ⟨C, hC0, hCbound⟩ := Salt.Maynard.card_divisors_le_rpow ε hε
  refine ⟨C, hC0, ?_⟩
  set Wcap : ℝ := C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2) with hWcap
  have hbase1 : (1 : ℝ) ≤ 2 * (x : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) x; linarith
  have hWcap0 : 0 ≤ Wcap := by
    rw [hWcap]
    exact mul_nonneg (mul_nonneg hC0.le (Real.rpow_nonneg (by positivity) _))
      (Real.log_nonneg hbase1)
  -- the uniform per-factor weight cap on the window
  have huniform : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * x + 2 → tauLog m ≤ Wcap := by
    intro m hm1 hm2
    rw [tauLog]
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmR2 : (m : ℝ) ≤ 2 * (x : ℝ) + 2 := by exact_mod_cast hm2
    have htau : (m.divisors.card : ℝ) ≤ C * (2 * (x : ℝ) + 2) ^ ε := by
      refine le_trans (hCbound m hm1) ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg m) hmR2 hε.le) hC0.le
    have hlog : Real.log (m : ℝ) ≤ Real.log (2 * (x : ℝ) + 2) :=
      Real.log_le_log (by linarith) hmR2
    have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
    calc (m.divisors.card : ℝ) * Real.log (m : ℝ)
        ≤ (C * (2 * (x : ℝ) + 2) ^ ε) * Real.log (2 * (x : ℝ) + 2) :=
          mul_le_mul htau hlog hlog0 (by positivity)
      _ = Wcap := by rw [hWcap]
  -- shared pieces for the two symmetric sides
  have hg_nonneg : ∀ n, 0 ≤ tauLog n * tauLog (n + 2) :=
    fun n => mul_nonneg (tauLog_nonneg n) (tauLog_nonneg (n + 2))
  have hW : ∀ n ∈ A, tauLog n * tauLog (n + 2) ≤ Wcap ^ 2 := by
    intro n hn
    have hmem := hAsub hn; rw [Finset.mem_Ioc] at hmem
    have h1 : tauLog n ≤ Wcap := huniform n (by omega) (by omega)
    have h2 : tauLog (n + 2) ≤ Wcap := huniform (n + 2) (by omega) (by omega)
    calc tauLog n * tauLog (n + 2) ≤ Wcap * Wcap :=
          mul_le_mul h1 h2 (tauLog_nonneg _) hWcap0
      _ = Wcap ^ 2 := by ring
  have htgt1 : ∀ n ∈ A, 1 ≤ n ∧ n ≤ 2 * x + 2 := by
    intro n hn; have := hAsub hn; rw [Finset.mem_Ioc] at this; omega
  have htgt2 : ∀ n ∈ A, 1 ≤ n + 2 ∧ n + 2 ≤ 2 * x + 2 := by
    intro n hn; have := hAsub hn; rw [Finset.mem_Ioc] at this; omega
  have hcollapse1 : ∀ n ∈ A, HasExcSq χ z n → ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n ∧ z ≤ p :=
    fun n hn hE => excSq_ge_z_of_window χ z (hcop n hn) (dvd_mul_right n (n + 2)) hE
  have hcollapse2 : ∀ n ∈ A, HasExcSq χ z (n + 2) →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ (n + 2) ∧ z ≤ p :=
    fun n hn hE => excSq_ge_z_of_window χ z (hcop n hn) (dvd_mul_left (n + 2) n) hE
  have hcount1 : ∀ p : ℕ, 0 < p →
      ((A.filter (fun n => p ^ 2 ∣ n)).card : ℝ) ≤ (x : ℝ) / (p : ℝ) ^ 2 + 1 := by
    intro p hp
    have hsub : (A.filter (fun n => p ^ 2 ∣ n)).card
        ≤ ((Finset.Ioc x (2 * x)).filter (fun n => p ^ 2 ∣ n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hAsub)
    exact le_trans (by exact_mod_cast hsub) (sq_dvd_count_le x p hp)
  have hcount2 : ∀ p : ℕ, 0 < p →
      ((A.filter (fun n => p ^ 2 ∣ (n + 2))).card : ℝ) ≤ (x : ℝ) / (p : ℝ) ^ 2 + 1 := by
    intro p hp
    have hsub : (A.filter (fun n => p ^ 2 ∣ (n + 2))).card
        ≤ ((Finset.Ioc x (2 * x)).filter (fun n => p ^ 2 ∣ (n + 2))).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hAsub)
    exact le_trans (by exact_mod_cast hsub) (shift_count_le hp)
  -- the two exceptional sums, via the fibration master
  have hexc1 := exc_sum_le χ z x hz A (fun n => n) htgt1 hcollapse1
    (fun n => tauLog n * tauLog (n + 2)) hg_nonneg (Wcap ^ 2) (by positivity) hW hcount1
  have hexc2 := exc_sum_le χ z x hz A (fun n => n + 2) htgt2 hcollapse2
    (fun n => tauLog n * tauLog (n + 2)) hg_nonneg (Wcap ^ 2) (by positivity) hW hcount2
  -- reduce the two star-step sides to the exceptional-filter sums
  have hterm1 : ∀ n, starErrBound χ z n * tauLog (n + 2)
      = if HasExcSq χ z n then tauLog n * tauLog (n + 2) else 0 := by
    intro n; rw [starErrBound]; split_ifs with hE
    · rfl
    · exact zero_mul _
  have hterm2 : ∀ n, tauLog n * starErrBound χ z (n + 2)
      = if HasExcSq χ z (n + 2) then tauLog n * tauLog (n + 2) else 0 := by
    intro n; rw [starErrBound]; split_ifs with hE
    · rfl
    · exact mul_zero _
  have hside1 : ∑ n ∈ A, starErrBound χ z n * tauLog (n + 2)
      = ∑ n ∈ A.filter (fun n => HasExcSq χ z n), tauLog n * tauLog (n + 2) := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl (fun n _ => hterm1 n)
  have hside2 : ∑ n ∈ A, tauLog n * starErrBound χ z (n + 2)
      = ∑ n ∈ A.filter (fun n => HasExcSq χ z (n + 2)), tauLog n * tauLog (n + 2) := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl (fun n _ => hterm2 n)
  have key : ∑ n ∈ A, (starErrBound χ z n * tauLog (n + 2)
        + tauLog n * starErrBound χ z (n + 2))
      ≤ Wcap ^ 2 * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ))
        + Wcap ^ 2 * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
    rw [Finset.sum_add_distrib, hside1, hside2]
    exact add_le_add hexc1 hexc2
  refine le_trans key (le_of_eq ?_)
  ring

/-! ## §5 — composition with the master transfer inequality -/

/-- **The composed window bound.**  Feeding `hstar_window` through the landed master
    `S2_sub_S3_le` yields the star-step transfer error `|S⁽²⁾ − S⁽³⁾|` on the honest
    window, at the HB-Lemma-4 grade. -/
theorem S2_sub_S3_window (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ)
    (hz : 1 ≤ z) (A : Finset ℕ) (hAsub : A ⊆ Finset.Ioc x (2 * x))
    (hcop : ∀ n ∈ A, Nat.Coprime (n * (n + 2)) (excPrimorial χ z))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      |S2 χ A - S3 χ z A|
        ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
            * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) := by
  obtain ⟨C, hC0, hbound⟩ := hstar_window χ z x hz A hAsub hcop ε hε
  exact ⟨C, hC0, le_trans (S2_sub_S3_le χ hsq z A) hbound⟩

/-! ## §6 — the concrete honest window -/

/-- **The honest HB support window** `A = {n ∈ (x, 2x] : (n(n+2), excPrimorial χ z) = 1}`
    — HB's `(n(n+2), q·P) = 1` support realized with the minimal honest modulus. -/
noncomputable def honestWindow (χ : DirichletCharacter ℂ q) (z x : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => Nat.Coprime (n * (n + 2)) (excPrimorial χ z))

lemma honestWindow_subset (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    honestWindow χ z x ⊆ Finset.Ioc x (2 * x) := Finset.filter_subset _ _

lemma honestWindow_coprime (χ : DirichletCharacter ℂ q) (z x : ℕ) :
    ∀ n ∈ honestWindow χ z x, Nat.Coprime (n * (n + 2)) (excPrimorial χ z) :=
  fun _ hn => (Finset.mem_filter.mp hn).2

/-- **The star-step residual on the concrete honest window** (`hstar_window` instance). -/
theorem hstar_honestWindow (χ : DirichletCharacter ℂ q) (z x : ℕ) (hz : 1 ≤ z)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∑ n ∈ honestWindow χ z x, (starErrBound χ z n * tauLog (n + 2)
          + tauLog n * starErrBound χ z (n + 2))
        ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
            * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) :=
  hstar_window χ z x hz _ (honestWindow_subset χ z x) (honestWindow_coprime χ z x) ε hε

/-- **`|S⁽²⁾ − S⁽³⁾|` on the concrete honest window** (`S2_sub_S3_window` instance). -/
theorem S2_sub_S3_honestWindow (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z x : ℕ)
    (hz : 1 ≤ z) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      |S2 χ (honestWindow χ z x) - S3 χ z (honestWindow χ z x)|
        ≤ 2 * (C * (2 * (x : ℝ) + 2) ^ ε * Real.log (2 * (x : ℝ) + 2)) ^ 2
            * (2 * (x : ℝ) / (z : ℝ) + (Nat.sqrt (2 * x + 2) : ℝ)) :=
  S2_sub_S3_window χ hsq z x hz _ (honestWindow_subset χ z x) (honestWindow_coprime χ z x) ε hε

end Salt.HB
