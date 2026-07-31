/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4WaveClosed

/-!
# `M4Maximal` — ⟦R1⟧, THE DYADIC MAXIMAL STEP

`M4WaveClosed` §6 lands the χ-uniform block mean square at the FIXED window length `K = H`
and names the passage to the sub-window sup (`doorChiSup`, the sup over `K ≤ H`) as ⟦R1⟧.
This file executes that passage by the dyadic (Rademacher–Menshov) route and lands
`M4ChiBlockMeanSq` — the M4 wave's analytic item — from a per-dyadic-length row datum, at

  `Cmax = 54/5 = 10.8`   (`m4Cmax`, a CONSTANT — ⟦LEVER 1′⟧; no log at all).

## ⟦THE STATEMENT FINDING⟧ — why `M4ChiMaximalStep` is not the shape that can be proved

`M4WaveClosed.M4ChiMaximalStep` asks for

  `∑_{n ∈ block} sup_{K ≤ H}‖S(n,K)‖² ≤ Cmax H · ∑_{n ∈ block}‖S(n,H)‖²`,

i.e. it prices the sub-window sup against the block's FIXED-length-`H` sums *of the same
block*.  No maximal inequality can deliver that, and it is false for general data: a datum
that is `+1, −1` alternating on the sieved window has `S(n,H) = 0` for every `n` (even `H`)
while `S(n,1) = ±1`, so the right-hand side vanishes and the left-hand side is the block
length.  The dyadic argument does not compare the sup to the length-`H` sums; it compares it
to the length-`2^j` sums, `j ≤ log₂ H`, **at the shifted bases the sub-windows actually
have** — the pieces of `(n, n+K]` start at `n + P`, `0 ≤ P < K ≤ H`.  This is the same genre
as the ⟦F1⟧ kill recorded in `M4WaveClosed`'s header (a pointwise datum no supplier
produces), and per iron rule 1 the statement is left standing where it is: this file adds
the provable route beside it rather than rewriting it.

## ⟦THE LENGTH GRADING⟧ — why the row datum is `MS j H` and not `MS H`

⟦WALL 2⟧ (`M4DoorRow` §7, two kernel witnesses) killed the UNIFORM-in-`j` row datum:

* `M4DoorRow.door_length_gate` solves the capstone's own window gate `𝒬K_1 ≤ h` at the
  dyadic length `h = 2^j` into the ARITHMETIC statement `M·Adoor M ≤ j`.  So every
  `j < M·Adoor M` — and `Adoor M ≥ 2^18` — is outside the capstone's STATEMENT, before any
  estimate is attempted (`door_length_gate_fails_of_small`);
* at `j = 0` the row quantity IS the block density of the live sieved residues (one integer
  per unit `y`-interval), which is `≍ 1/loglog H` — while the close's own drift/budget gates
  force `≲ (log H)^{-30}`.  No single `MS` serves both ends.

The dyadic assembly never needed uniformity, and this file now says so: the row grade is
`MS : ℕ → ℕ → ℝ`, read `MS j H` — THE GRADE AT DYADIC LENGTH `2^j`.  §4 is where the
length-dependence dies, and it dies asymmetrically:

* the FULL weighted count is
  `(∑_{j ≤ L}(3/2)^j)·∑_{j ≤ L}(⌊H/2^{j+1}⌋+1)(2^j)²(2/3)^j ≤ (54/5)H²`
  (`dyadic_count_weight_geom_le`) — quadratic in `H`, the block's own normalisation, and the
  prefactor is now the Cauchy–Schwarz weight sum, NOT the piece count;
* the SMALL head is
  `(∑_{j ≤ L}(3/2)^j)·∑_{j < j₀}(⌊H/2^{j+1}⌋+1)(2^j)²(2/3)^j
     ≤ (9/2)H(3/2)^L(4/3)^{j₀} + (9/5)(3/2)^L(8/3)^{j₀}`
  (`dyadic_count_weight_geom_small_le`) — TWO summands, because the term bound's two halves
  run at the two different ratios `2/(3/2) = 4/3` and `4/(3/2) = 8/3`.

So the split assembly charges `Fan H` (the analytic grade) at `j₀ ≤ j` and `Ftr H` (the
trivial grade — the block density, `≍ 1`) at `j < j₀`, and pays

  `Bcl H = m4Cmax H·Fan H
             + ((9/2)(3/2)^{log₂H}(4/3)^{j₀}/H + (9/5)(3/2)^{log₂H}(8/3)^{j₀}/H²)·Ftr H`

(`m4BclGraded`).  Since `(3/2)^{log₂H} = H^{0.58496}`, the second term is
`4.5(4/3)^{j₀}H^{-0.415} + 1.8(8/3)^{j₀}H^{-1.415}`: at fixed `M` the small-`j` charge
DECAYS, which is the whole point of the re-cut.  The floor `j₀` is carried as a NAMED
PARAMETER everywhere — never inlined as `2^18`, because the `M`-dependence
(`j₀ = M·Adoor M` at the door, `M4DoorRow.doorRowFloor`) is exactly what makes `(4/3)^{j₀}`
and `(8/3)^{j₀}` constants against `H` and not functions of it.  The comparison is stated
symbolically as `m4SmallGradeFits` — the whole small-`j` charge under `H²·(m4Cmax·Fan H)`,
i.e. the graded split costs at most a factor `2` (`m4BclGraded_le_of_fits`), with the
threshold in `H` alone (`m4SmallGradeFits_of_threshold`).  Both summands read as the SAME
floor demand `H ≳ 2^{j₀}` — `log₂(4/3) = 0.41504` and `log₂(8/3) = 1.41504` are exactly the
two `H`-exponents — where the uniform route demanded `4^{j₀}`.  **The floor's exponent
halves**; that is ⟦LEVER 1′⟧'s second dividend, after the constant `Cmax`.

## ⟦THE ROUTE⟧

* **§1 — the window split.**  `(n, n+a+c] = (n, n+a] ⊔ (n+a, n+a+c]`, the sieve being a
  pointwise filter: `sum_sievedWindow_add`.  Half-open throughout; no ±1 is spent.
* **§2 — the binary tiling** (`norm_sum_sievedWindow_le_dyadic`).  For `K < 2^{L+1}`,
  writing `P_j K = 2^{j+1}·⌊K/2^{j+1}⌋` (`K` with its low `j+1` bits cleared),

    `‖S(n,K)‖ ≤ ∑_{j ≤ L} ‖S(n + P_j K, 2^j)‖`.

  The pieces present are exactly the set bits of `K`, taken high-to-low; the absent ones are
  added on the right for free (norms are nonnegative).  The base of the `j`-piece is
  `n + P_j K` and `P_j K` is a MULTIPLE OF `2^{j+1}` — the alignment is the whole content:
  at scale `j` only `⌊H/2^{j+1}⌋ + 1` offsets can occur, and that geometric decay is what
  makes the price one log rather than `H`.
* **§3 — the pointwise maximal bound**, ⟦LEVER 1′⟧.  Square, then weighted Cauchy–Schwarz at
  the geometric weights `a_j = (3/2)^j` — packaged in the ENGEL/Sedrakyan form
  (`Finset.sq_sum_div_le_sum_sq_div`), which is sqrt-free and one step — then replace the
  single aligned offset by the sum over all admissible ones (nonneg terms):

    `sup_{K ≤ H}‖S(n,K)‖²
       ≤ (∑_{j ≤ log₂H}(3/2)^j)·∑_{j ≤ log₂H}(2/3)^j ∑_{t ≤ ⌊H/2^{j+1}⌋}‖S(n+t·2^{j+1},2^j)‖²`

  — `doorChiSup_sq_le_dyadic`, the sup being attained (`Finset.exists_mem_eq_sup'`).  The
  uniform Chebyshev `sq_sum_le_card_mul_sum_sq` (piece count `log₂H + 1`) is what this
  replaces, and the replacement is FREE: the weights cost nothing on the supply side, and
  they turn the price from `3(log₂H + 1)` into the constant `54/5`.
* **§4 — the block sum, and the two counts.**  The `n`-sum and the `(j,t)`-sums commute; the
  shift `n ↦ n+s` carries `Ioc A B` onto `Ioc (A+s) (B+s)` EXACTLY
  (`Finset.map_add_right_Ioc`), so no overhang cell is created and none is discarded.  What
  is left is arithmetic: one term bound (`dyadic_count_weight_term_le`), weighted by
  `(2/3)^j` and summed twice against the weight-sum prefactor — over all `j ≤ L` for
  `(54/5)H²` (`dyadic_count_weight_geom_le`) and over `j < j₀` for the two-summand head
  (`dyadic_count_weight_geom_small_le`).  The unweighted pair (`dyadic_count_weight_le`,
  `dyadic_count_weight_small_le`) is kept beside them: still true, no longer on the road.
* **§5 — the shifted-block datum** (`M4ChiShiftBlockMeanSq`, LENGTH-GRADED: `F j H`) and the
  split maximal step (`m4_chiBlockMeanSq_of_shiftBlock`), at the graded price `m4BclGraded`.
* **§6 — the row datum** (`M4ChiDyadicRowMeanSq`, LENGTH-GRADED: `MS j H`): the capstone's
  own currency at the window length `2^j` and the block scale `X = X_{i+1} + s`, `s ≤ H`.
  The fit is honest and it is exactly `M4Door.doorLadder_fit`'s room: at `X := A + s` the
  bridge's two gates read `X ≤ A + s` (`le_rfl`) and `(B+s) + 2^j ≤ 2(A+s)`, which follows
  from `B + H ≤ 2A` and `2^j ≤ H` — the shift pays for itself, and the exchange's factor is
  the ladder's own `2` (`B + s ≤ B + H ≤ 2A`), not `4`.
* **§7 — the close** (`m4_wave_closed_of_dyadicRow`), `m4_wave_closed_of_chi`'s analytic
  slot filled at `Bcl H = m4BclGraded j₀ (2·MSan) (2·MStr) H`, i.e.
  `(108/5)·MSan H + (9(3/2)^{log₂H}(4/3)^{j₀}/H + (18/5)(3/2)^{log₂H}(8/3)^{j₀}/H²)·MStr H`.

## ⟦THE TRAPS RESPECTED⟧

* **the four log scales** — `m4Cmax` is now a NUMERAL and reads no log at all; the only
  `log` anywhere in the file is `Nat.log 2` (in the tiling depth and in the head's
  `(3/2)^{Nat.log 2 H}`): no `Real.log`, no `log X`, no `loglog`.  The budget's `(log H)²`
  allowance is not spent, and neither is the one log the uniform route spent, because the
  maximum over offsets is paid by SUMMING the `⌊H/2^{j+1}⌋+1` aligned offsets against
  geometric weights whose ratio `3/2` sits strictly between the offset decay `1/2` and the
  window growth `4`.
* **the fatal route avoided** — `sup² ≤ ∑_{K ≤ H}` is never taken; the cost here is
  `3(log₂H+1)`, never `H+1`.
* **the floor is NAMED** — `j₀` is a parameter of every graded statement; `2^18` is never
  written, and neither is `M·Adoor M`.  The consumer supplies it (at the door,
  `M4DoorRow.doorRowFloor M = M·Adoor M`), so the `M`-dependence of `4^{j₀}` stays visible
  where the threshold is checked instead of being buried as a numeral here.
* **half-open** — every window is `Finset.Ioc n (n+K)`, every block `Finset.Ioc A B`, and
  the tiling's boundary arithmetic is `Finset.Ioc_union_Ioc_eq_Ioc` at `n+a`: exact, with no
  endpoint counted twice and none lost.
* **strict gates** — `0 < q`, `R.Hlo ≤ H ≤ R.Hhi`, `0 < H` (via `R.hHlo_floor`) carried
  everywhere; `0 < 2^j` and `2^j ≤ H` (via `Nat.pow_log_le_self`) at every piece.
* **the un-phased datum** — the carrier is `doorChiCoeff χ M` BARE and the frequency is `0`
  throughout (`M4ClassPrice.doorCoeffPhase_zero`), exactly as §6's fixed-length bridge.
* `liouChi` only — never `lamChi`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE WINDOW SPLIT

The sieve is a pointwise filter, so a window sum splits at any interior point exactly as the
half-open interval does.  This is the only place a boundary is touched, and it is `Ioc`'s own
`a ≤ b ≤ c` union law — no `±1` is spent. -/

/-- **THE SPLIT** — `S(n, a+c) = S(n, a) + S(n+a, c)` on the sieved window. -/
theorem sum_sievedWindow_add (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℂ) (n a c : ℕ) :
    ∑ m ∈ sievedWindow p (a + c) n, f m
      = (∑ m ∈ sievedWindow p a n, f m) + ∑ m ∈ sievedWindow p c (n + a), f m := by
  have h1 : n ≤ n + a := Nat.le_add_right _ _
  have h2 : n + a ≤ n + (a + c) := by omega
  have hsplit : Finset.Ioc n (n + (a + c))
      = Finset.Ioc n (n + a) ∪ Finset.Ioc (n + a) (n + a + c) := by
    have hrw : n + a + c = n + (a + c) := by omega
    rw [hrw, Finset.Ioc_union_Ioc_eq_Ioc h1 h2]
  have hdisj : Disjoint (Finset.Ioc n (n + a)) (Finset.Ioc (n + a) (n + a + c)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  simp only [sievedWindow, hsplit, Finset.filter_union]
  exact Finset.sum_union (Finset.disjoint_filter_filter hdisj)

/-! ## §2 — THE BINARY TILING

`K`'s binary decomposition tiles `(n, n+K]` by dyadic-length pieces at ALIGNED offsets: the
`j`-piece sits at `n + P_j K` with `P_j K = 2^{j+1}·⌊K/2^{j+1}⌋`, a multiple of `2^{j+1}`.
The induction peels the top bit. -/

/-- **THE PREFIX ARITHMETIC** — clearing the low `j+1` bits commutes with adding a multiple
of `2^{L+1}`, for `j ≤ L`.  This is the alignment fact the tiling's induction needs. -/
theorem dyadic_prefix_shift {L j : ℕ} (hj : j ≤ L) (K : ℕ) :
    2 ^ (j + 1) * ((2 ^ (L + 1) + K) / 2 ^ (j + 1))
      = 2 ^ (L + 1) + 2 ^ (j + 1) * (K / 2 ^ (j + 1)) := by
  have hpos : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
  have hpow : 2 ^ (j + 1) * 2 ^ (L - j) = 2 ^ (L + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : (2 ^ (L + 1) + K) / 2 ^ (j + 1) = K / 2 ^ (j + 1) + 2 ^ (L - j) := by
    rw [← hpow, Nat.add_comm (2 ^ (j + 1) * 2 ^ (L - j)) K,
      Nat.add_mul_div_left _ _ hpos]
  rw [hdiv, Nat.mul_add, hpow]
  omega

/-- **THE TILING** — for `K < 2^{L+1}` the window sum is dominated by the `L+1` dyadic
pieces of `K`'s binary decomposition, each at its own aligned base `n + P_j K`.  Bits that
are `0` contribute a term that is not needed; it is kept (nonnegative) so the index set is
`range (L+1)` for every `K`. -/
theorem norm_sum_sievedWindow_le_dyadic (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℂ) :
    ∀ (L K n : ℕ), K < 2 ^ (L + 1) →
      ‖∑ m ∈ sievedWindow p K n, f m‖
        ≤ ∑ j ∈ Finset.range (L + 1),
            ‖∑ m ∈ sievedWindow p (2 ^ j) (n + 2 ^ (j + 1) * (K / 2 ^ (j + 1))), f m‖ := by
  intro L
  induction L with
  | zero =>
      intro K n hK
      have hK2 : K < 2 := by simpa using hK
      have hdiv : K / 2 ^ (0 + 1) = 0 := Nat.div_eq_of_lt (by simpa using hK2)
      have hsum : ∑ j ∈ Finset.range (0 + 1),
          ‖∑ m ∈ sievedWindow p (2 ^ j) (n + 2 ^ (j + 1) * (K / 2 ^ (j + 1))), f m‖
          = ‖∑ m ∈ sievedWindow p 1 n, f m‖ := by
        rw [Finset.sum_range_succ, Finset.sum_range_zero, hdiv]
        norm_num
      rw [hsum]
      rcases (by omega : K = 0 ∨ K = 1) with rfl | rfl
      · simp only [sievedWindow, Nat.add_zero, Finset.Ioc_self, Finset.filter_empty,
          Finset.sum_empty, norm_zero]
        exact norm_nonneg _
      · exact le_rfl
  | succ L ih =>
      intro K n hK
      have hposL : 0 < 2 ^ (L + 1) := Nat.two_pow_pos _
      have hb : K / 2 ^ (L + 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul hposL]
        calc K < 2 ^ (L + 1 + 1) := hK
          _ = 2 * 2 ^ (L + 1) := by ring
      have hK' : K % 2 ^ (L + 1) < 2 ^ (L + 1) := Nat.mod_lt _ hposL
      have hdec : K / 2 ^ (L + 1) * 2 ^ (L + 1) + K % 2 ^ (L + 1) = K :=
        Nat.div_add_mod' K (2 ^ (L + 1))
      -- ⟦the top term⟧: `P_{L+1} K = 0`, because `K < 2^{L+2}`
      have htop : K / 2 ^ (L + 1 + 1) = 0 := Nat.div_eq_of_lt hK
      have htop2 : n + 2 ^ (L + 1 + 1) * (K / 2 ^ (L + 1 + 1)) = n := by
        rw [htop, Nat.mul_zero, Nat.add_zero]
      rw [Finset.sum_range_succ, htop2]
      have hb01 : ∀ b : ℕ, b < 2 → b = 0 ∨ b = 1 := by intro b hb2; omega
      rcases hb01 _ hb with hb0 | hb1
      · -- ⟦the top bit is absent⟧: the IH applies to `K` itself
        have hKlt : K < 2 ^ (L + 1) := by
          rw [hb0, Nat.zero_mul, Nat.zero_add] at hdec
          omega
        have hle := ih K n hKlt
        have hnn : (0 : ℝ) ≤ ‖∑ m ∈ sievedWindow p (2 ^ (L + 1)) n, f m‖ := norm_nonneg _
        linarith
      · -- ⟦the top bit is present⟧: peel it, then the IH at the shifted base
        obtain ⟨K', hK'lt, hKeq⟩ : ∃ K', K' < 2 ^ (L + 1) ∧ K = 2 ^ (L + 1) + K' :=
          ⟨K % 2 ^ (L + 1), hK', by rw [hb1, Nat.one_mul] at hdec; omega⟩
        subst hKeq
        have hsplit : ∑ m ∈ sievedWindow p (2 ^ (L + 1) + K') n, f m
            = (∑ m ∈ sievedWindow p (2 ^ (L + 1)) n, f m)
              + ∑ m ∈ sievedWindow p K' (n + 2 ^ (L + 1)), f m :=
          sum_sievedWindow_add p f n (2 ^ (L + 1)) K'
        have hIH := ih K' (n + 2 ^ (L + 1)) hK'lt
        have hbase : ∀ j ∈ Finset.range (L + 1),
            ‖∑ m ∈ sievedWindow p (2 ^ j) (n + 2 ^ (L + 1) + 2 ^ (j + 1) * (K' / 2 ^ (j + 1))),
                f m‖
              = ‖∑ m ∈ sievedWindow p (2 ^ j)
                  (n + 2 ^ (j + 1) * ((2 ^ (L + 1) + K') / 2 ^ (j + 1))), f m‖ := by
          intro j hj
          have hjL : j ≤ L := by
            have := Finset.mem_range.mp hj
            omega
          have hsh := dyadic_prefix_shift hjL K'
          have : n + 2 ^ (L + 1) + 2 ^ (j + 1) * (K' / 2 ^ (j + 1))
              = n + 2 ^ (j + 1) * ((2 ^ (L + 1) + K') / 2 ^ (j + 1)) := by omega
          rw [this]
        rw [Finset.sum_congr rfl hbase] at hIH
        have htri := norm_add_le (∑ m ∈ sievedWindow p (2 ^ (L + 1)) n, f m)
          (∑ m ∈ sievedWindow p K' (n + 2 ^ (L + 1)), f m)
        rw [hsplit]
        linarith

/-! ## §3 — THE POINTWISE MAXIMAL BOUND

Square the tiling, pay the piece count once by Chebyshev, then forget WHICH aligned offset
each piece has by summing over all of them.  The right-hand side is `K`-free, so it bounds
the sup. -/

/-! ### The geometric weights `a_j = (3/2)^j`

⟦LEVER 1′⟧ replaces the uniform Chebyshev of the maximal step by weighted Cauchy–Schwarz at
the ratio `c = 3/2`.  The weight sum is a CONSTANT multiple of `(3/2)^L` and the weighted
count is `H²` up to a constant — so the `log₂H` that the uniform step paid disappears.  The
ratio is all-rational, which is why the two geometric series below close under `norm_num`
alone; the packaging is the Engel/Sedrakyan form (`Finset.sq_sum_div_le_sum_sq_div`), which
is sqrt-free. -/

/-- **THE WEIGHT SUM** — `∑_{j ≤ n} (3/2)^j = 3·(3/2)^n − 2`.  The Cauchy–Schwarz prefactor:
it is `≤ 3·(3/2)^n`, and against the weighted count's `(4/3)^n` / `(8/3)^n` it produces `2^n`
/ `4^n` exactly. -/
theorem geom_weight_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (3 / 2 : ℝ) ^ j = 3 * (3 / 2 : ℝ) ^ n - 2 := by
  rw [geom_sum_eq (by norm_num : (3 / 2 : ℝ) ≠ 1)]
  rw [pow_succ]
  ring

theorem geom_weight_sum_pos (n : ℕ) :
    (0 : ℝ) < ∑ j ∈ Finset.range (n + 1), (3 / 2 : ℝ) ^ j :=
  Finset.sum_pos (fun j _ => by positivity) ⟨0, Finset.mem_range.mpr (by omega)⟩

theorem geom_weight_sum_le (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (3 / 2 : ℝ) ^ j ≤ 3 * (3 / 2 : ℝ) ^ n := by
  rw [geom_weight_sum n]; linarith

/-- Dividing by the weight is multiplying by its reciprocal — the one rewrite that turns the
Engel form's `x²/a_j` into the multiplicative shape the count is stated in. -/
theorem inv_geom_weight (x : ℝ) (j : ℕ) : x / (3 / 2 : ℝ) ^ j = x * (2 / 3 : ℝ) ^ j := by
  rw [div_eq_mul_inv, ← inv_pow]
  norm_num

/-- The two mixed products the weighted count closes on: `(3/2)^j·(2/3)^j` collapses the
scale weights exactly. -/
theorem geom_term_eq (H : ℕ) (j : ℕ) :
    ((H : ℝ) / 2 * 2 ^ j + 4 ^ j) * (2 / 3 : ℝ) ^ j
      = (H : ℝ) / 2 * (4 / 3 : ℝ) ^ j + (8 / 3 : ℝ) ^ j := by
  have h1 : (2 : ℝ) ^ j * (2 / 3 : ℝ) ^ j = (4 / 3 : ℝ) ^ j := by
    rw [← mul_pow]; norm_num
  have h2 : (4 : ℝ) ^ j * (2 / 3 : ℝ) ^ j = (8 / 3 : ℝ) ^ j := by
    rw [← mul_pow]; norm_num
  calc ((H : ℝ) / 2 * 2 ^ j + 4 ^ j) * (2 / 3 : ℝ) ^ j
      = (H : ℝ) / 2 * ((2 : ℝ) ^ j * (2 / 3 : ℝ) ^ j) + (4 : ℝ) ^ j * (2 / 3 : ℝ) ^ j := by ring
    _ = (H : ℝ) / 2 * (4 / 3 : ℝ) ^ j + (8 / 3 : ℝ) ^ j := by rw [h1, h2]

/-- **THE SQUARED TILING** — the `K`-free bound on a single window sum's square, at the
GEOMETRIC weights.  The prefactor is the weight sum `∑_{j ≤ log₂H}(3/2)^j` (a constant times
`(3/2)^{log₂H}`) instead of the piece count `log₂H + 1`, and each scale's square is charged
at `(2/3)^j`.  The trade is the whole of ⟦LEVER 1′⟧: the top scales, which carry the mass,
are charged at a weight that decays exactly fast enough for the count to stay `O(H²)`. -/
theorem norm_sum_sievedWindow_sq_le_dyadic (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℂ)
    (H K n : ℕ) (hK : K ≤ H) :
    ‖∑ m ∈ sievedWindow p K n, f m‖ ^ 2
      ≤ (∑ j ∈ Finset.range (Nat.log 2 H + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range (Nat.log 2 H + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
              ‖∑ m ∈ sievedWindow p (2 ^ j) (n + 2 ^ (j + 1) * t), f m‖ ^ 2)
              * (2 / 3 : ℝ) ^ j := by
  set L := Nat.log 2 H with hL
  set b : ℕ → ℝ := fun j =>
    ‖∑ m ∈ sievedWindow p (2 ^ j) (n + 2 ^ (j + 1) * (K / 2 ^ (j + 1))), f m‖ with hb
  have hKlt : K < 2 ^ (L + 1) :=
    lt_of_le_of_lt hK (Nat.lt_pow_succ_log_self (by norm_num) H)
  have htile := norm_sum_sievedWindow_le_dyadic p f L K n hKlt
  have h0 : (0 : ℝ) ≤ ‖∑ m ∈ sievedWindow p K n, f m‖ := norm_nonneg _
  have hsq : ‖∑ m ∈ sievedWindow p K n, f m‖ ^ 2
      ≤ (∑ j ∈ Finset.range (L + 1), b j) ^ 2 := by
    have := mul_self_le_mul_self h0 htile
    nlinarith [this]
  -- ⟦THE ENGEL FORM⟧ — Cauchy–Schwarz at the weights `a_j = (3/2)^j`, sqrt-free
  have hSpos : (0 : ℝ) < ∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j :=
    geom_weight_sum_pos L
  have hengel := Finset.sq_sum_div_le_sum_sq_div (Finset.range (L + 1)) b
    (g := fun j => (3 / 2 : ℝ) ^ j) (fun j _ => by positivity)
  have hcs : (∑ j ∈ Finset.range (L + 1), b j) ^ 2
      ≤ (∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range (L + 1), b j ^ 2 * (2 / 3 : ℝ) ^ j := by
    have hconv : ∑ j ∈ Finset.range (L + 1), b j ^ 2 / (3 / 2 : ℝ) ^ j
        = ∑ j ∈ Finset.range (L + 1), b j ^ 2 * (2 / 3 : ℝ) ^ j :=
      Finset.sum_congr rfl fun j _ => inv_geom_weight (b j ^ 2) j
    rw [hconv, div_le_iff₀ hSpos] at hengel
    linarith [hengel]
  -- ⟦the pick⟧ the single aligned offset, forgotten into the sum over all of them
  have hpick : ∀ j ∈ Finset.range (L + 1),
      b j ^ 2 * (2 / 3 : ℝ) ^ j
        ≤ (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
            ‖∑ m ∈ sievedWindow p (2 ^ j) (n + 2 ^ (j + 1) * t), f m‖ ^ 2)
            * (2 / 3 : ℝ) ^ j := by
    intro j _
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine Finset.single_le_sum
      (f := fun t => ‖∑ m ∈ sievedWindow p (2 ^ j) (n + 2 ^ (j + 1) * t), f m‖ ^ 2)
      (fun t _ => by positivity) (Finset.mem_range.mpr ?_)
    have hdd : K / 2 ^ (j + 1) ≤ H / 2 ^ (j + 1) := Nat.div_le_div_right hK
    omega
  calc ‖∑ m ∈ sievedWindow p K n, f m‖ ^ 2
      ≤ (∑ j ∈ Finset.range (L + 1), b j) ^ 2 := hsq
    _ ≤ (∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j)
          * ∑ j ∈ Finset.range (L + 1), b j ^ 2 * (2 / 3 : ℝ) ^ j := hcs
    _ ≤ (∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j)
          * ∑ j ∈ Finset.range (L + 1),
              (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
                ‖∑ m ∈ sievedWindow p (2 ^ j) (n + 2 ^ (j + 1) * t), f m‖ ^ 2)
                * (2 / 3 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpick) hSpos.le

/-- **THE SUB-WINDOW SUP, PRICED** — `doorChiSup`'s square against the aligned dyadic
family, at the geometric weights.  The sup is over a nonempty finite set, hence attained
(`Finset.exists_mem_eq_sup'`), and the bound is `K`-free. -/
theorem doorChiSup_sq_le_dyadic {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) :
    (doorChiSup χ M H n) ^ 2
      ≤ (∑ j ∈ Finset.range (Nat.log 2 H + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range (Nat.log 2 H + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
              ‖∑ m ∈ doorSievedWindow M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2)
              * (2 / 3 : ℝ) ^ j := by
  obtain ⟨K, hKmem, hKeq⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.Icc 0 H)
      ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
      (fun K => ‖∑ m ∈ doorSievedWindow M K n, liouChi χ m‖)
  have hKH : K ≤ H := (Finset.mem_Icc.mp hKmem).2
  have hval : doorChiSup χ M H n = ‖∑ m ∈ doorSievedWindow M K n, liouChi χ m‖ := hKeq
  rw [hval]
  simp only [doorSievedWindow]
  exact norm_sum_sievedWindow_sq_le_dyadic _ (liouChi χ) H K n hKH

/-! ## §4 — THE BLOCK SUM: THE SHIFT, AND THE COUNT

The `n`-sum meets the `(j,t)`-sums by `Finset.sum_comm`; the shift `n ↦ n + s` carries the
block onto the shifted block EXACTLY.  What is left is arithmetic: the number of aligned
offsets at scale `j` is `⌊H/2^{j+1}⌋ + 1`, and against the weight `(2^j)²` the two geometric
series close at `3H²`. -/

/-- **THE SHIFT IS EXACT** — no overhang cell is created and none is lost. -/
theorem sum_Ioc_shift (g : ℕ → ℝ) (A B s : ℕ) :
    ∑ n ∈ Finset.Ioc A B, g (n + s) = ∑ n ∈ Finset.Ioc (A + s) (B + s), g n := by
  rw [← Finset.map_add_right_Ioc A B s, Finset.sum_map]
  rfl

/-- **THE TERM** (`dyadic_count_weight_term_le`) — one scale's count × weight, against the
two geometric pieces `H·2^j/2` and `4^j`.  Both counts of this section are this single bound
summed: over `j ≤ log₂H` it gives `3H²`, over `j < j₀` it gives `2H·4^{j₀}`. -/
theorem dyadic_count_weight_term_le (H j : ℕ) :
    (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2
      ≤ (H : ℝ) / 2 * 2 ^ j + 4 ^ j := by
  have hcast : (((2 ^ j : ℕ) : ℝ)) ^ 2 = (4 : ℝ) ^ j := by
    push_cast
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  have hdiv : (((H / 2 ^ (j + 1) : ℕ)) : ℝ) ≤ (H : ℝ) / (2 : ℝ) ^ (j + 1) := by
    have h := Nat.cast_div_le (α := ℝ) (m := H) (n := 2 ^ (j + 1))
    push_cast at h
    exact h
  have hkey : (H : ℝ) / (2 : ℝ) ^ (j + 1) * (4 : ℝ) ^ j = (H : ℝ) / 2 * 2 ^ j := by
    have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
    have hne : ((2 : ℝ) ^ j) ≠ 0 := by positivity
    rw [h4, pow_succ]
    field_simp
  have h4nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
  calc (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2
      = (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (4 : ℝ) ^ j := by rw [hcast]
    _ ≤ ((H : ℝ) / (2 : ℝ) ^ (j + 1) + 1) * (4 : ℝ) ^ j := by
        refine mul_le_mul_of_nonneg_right ?_ h4nn
        linarith
    _ = (H : ℝ) / (2 : ℝ) ^ (j + 1) * (4 : ℝ) ^ j + (4 : ℝ) ^ j := by ring
    _ = (H : ℝ) / 2 * 2 ^ j + 4 ^ j := by rw [hkey]

/-- The weighted count's terms are nonnegative — used when the graded split forgets some of
them (`Finset.sum_le_sum_of_subset_of_nonneg`). -/
theorem dyadic_count_weight_term_nonneg (H j : ℕ) :
    (0 : ℝ) ≤ (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 := by positivity

/-- **THE COUNT** — `∑_{j ≤ log₂H} (⌊H/2^{j+1}⌋+1)·(2^j)² ≤ 3H²`.  The `H·2^j/2` half sums
to `H·2^L ≤ H²`; the `4^j` half sums to `4·4^L/3 ≤ 4H²/3`; `7/3 ≤ 3`.  THIS is why the
maximal step costs one log and not `H`: the offset count decays exactly as fast as the
window weight grows. -/
theorem dyadic_count_weight_le {H : ℕ} (hH : 0 < H) :
    ∑ j ∈ Finset.range (Nat.log 2 H + 1),
        ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) ≤ 3 * (H : ℝ) ^ 2 := by
  set L := Nat.log 2 H with hL
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hpow : ((2 : ℝ) ^ L) ≤ (H : ℝ) := by
    have h := Nat.pow_log_le_self 2 hH.ne'
    rw [← hL] at h
    exact_mod_cast h
  have hterm : ∀ j ∈ Finset.range (L + 1),
      (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2
        ≤ (H : ℝ) / 2 * 2 ^ j + 4 ^ j := fun j _ => dyadic_count_weight_term_le H j
  have hg2 : ∑ j ∈ Finset.range (L + 1), (2 : ℝ) ^ j = 2 ^ (L + 1) - 1 := by
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    norm_num
  have hg4 : ∑ j ∈ Finset.range (L + 1), (4 : ℝ) ^ j = ((4 : ℝ) ^ (L + 1) - 1) / 3 := by
    rw [geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1)]
    norm_num
  have h4L : (4 : ℝ) ^ (L + 1) = 4 * ((2 : ℝ) ^ L) ^ 2 := by
    have h4 : (4 : ℝ) ^ L = 2 ^ L * 2 ^ L := by rw [← mul_pow]; norm_num
    rw [pow_succ, h4]
    ring
  have h2L : (2 : ℝ) ^ (L + 1) = 2 * (2 : ℝ) ^ L := by rw [pow_succ]; ring
  have h2Lpos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  calc ∑ j ∈ Finset.range (L + 1),
        ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2)
      ≤ ∑ j ∈ Finset.range (L + 1), ((H : ℝ) / 2 * 2 ^ j + 4 ^ j) := Finset.sum_le_sum hterm
    _ = (H : ℝ) / 2 * (∑ j ∈ Finset.range (L + 1), (2 : ℝ) ^ j)
          + ∑ j ∈ Finset.range (L + 1), (4 : ℝ) ^ j := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (H : ℝ) / 2 * ((2 : ℝ) ^ (L + 1) - 1) + ((4 : ℝ) ^ (L + 1) - 1) / 3 := by
        rw [hg2, hg4]
    _ ≤ 3 * (H : ℝ) ^ 2 := by
        rw [h2L, h4L]
        nlinarith [hpow, h2Lpos, hHR, mul_le_mul_of_nonneg_left hpow hHR.le,
          mul_self_le_mul_self h2Lpos.le hpow]

/-- **THE SMALL-`j` COUNT** (`dyadic_count_weight_small_le`) — the head `j < j₀` of the same
weighted sum, against `2·H·4^{j₀}`: **linear** in `H`, times a constant depending on the
floor `j₀` alone.  The two geometric series are the same ones, cut at `j₀` instead of `L`:
`H/2·(2^{j₀}−1) + (4^{j₀}−1)/3 ≤ (5/6)·H·4^{j₀}`.

This is where the length-graded split pays for itself.  The block's own normalisation is
`H²`, so a charge that is `H·4^{j₀}` costs `4^{j₀}/H` in the currency — and at a floor `j₀`
that does not move with `H` (at the door, `j₀ = M·Adoor M`), the `j < j₀` lengths may carry a
grade as large as `≍ 1` — the block density — and still be free at the regime's `H`. -/
theorem dyadic_count_weight_small_le {H : ℕ} (hH : 0 < H) (j₀ : ℕ) :
    ∑ j ∈ Finset.range j₀, ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2)
      ≤ 2 * (H : ℝ) * (4 : ℝ) ^ j₀ := by
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hg2 : ∑ j ∈ Finset.range j₀, (2 : ℝ) ^ j = (2 : ℝ) ^ j₀ - 1 := by
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    norm_num
  have hg4 : ∑ j ∈ Finset.range j₀, (4 : ℝ) ^ j = ((4 : ℝ) ^ j₀ - 1) / 3 := by
    rw [geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1)]
    norm_num
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ j₀ := by positivity
  have h24 : (2 : ℝ) ^ j₀ ≤ (4 : ℝ) ^ j₀ := by
    gcongr
    norm_num
  calc ∑ j ∈ Finset.range j₀, ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2)
      ≤ ∑ j ∈ Finset.range j₀, ((H : ℝ) / 2 * 2 ^ j + 4 ^ j) :=
        Finset.sum_le_sum fun j _ => dyadic_count_weight_term_le H j
    _ = (H : ℝ) / 2 * (∑ j ∈ Finset.range j₀, (2 : ℝ) ^ j)
          + ∑ j ∈ Finset.range j₀, (4 : ℝ) ^ j := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (H : ℝ) / 2 * ((2 : ℝ) ^ j₀ - 1) + ((4 : ℝ) ^ j₀ - 1) / 3 := by rw [hg2, hg4]
    _ ≤ 2 * (H : ℝ) * (4 : ℝ) ^ j₀ := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (H : ℝ))
            (by linarith : (0 : ℝ) ≤ (4 : ℝ) ^ j₀ - (2 : ℝ) ^ j₀),
          mul_nonneg (by linarith : (0 : ℝ) ≤ (H : ℝ) - 1) h4pos.le,
          mul_pos (by linarith : (0 : ℝ) < (H : ℝ)) h4pos]

/-- **THE WEIGHTED COUNT** (`dyadic_count_weight_geom_le`) — ⟦LEVER 1′⟧'s replacement for the
pair (`log₂H + 1`) × (`dyadic_count_weight_le`).  The Cauchy–Schwarz prefactor and the
`(2/3)^j`-weighted count TOGETHER are `≤ (54/5)·H²`:

  `(3(3/2)^L)·((H/2)·4(4/3)^L + (8/5)(8/3)^L) = 6H·2^L + (24/5)·4^L ≤ (6 + 24/5)H²`.

`54/5 = 10.8` is the CONSTANT that replaces `3·(log₂H + 1)`.  `c = 3/2` is near-optimal —
the true minimum over `c` is about `1%` lower, and every ratio here (`4/3`, `8/3`, `3/2`) is
rational, which is what keeps the two geometric series inside `norm_num`. -/
theorem dyadic_count_weight_geom_le {H : ℕ} (hH : 0 < H) :
    (∑ j ∈ Finset.range (Nat.log 2 H + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range (Nat.log 2 H + 1),
            ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (H : ℝ) ^ 2 := by
  set L := Nat.log 2 H with hL
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hpow : ((2 : ℝ) ^ L) ≤ (H : ℝ) := by
    have h := Nat.pow_log_le_self 2 hH.ne'
    rw [← hL] at h
    exact_mod_cast h
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hterm : ∀ j ∈ Finset.range (L + 1),
      ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
        ≤ (H : ℝ) / 2 * (4 / 3 : ℝ) ^ j + (8 / 3 : ℝ) ^ j := by
    intro j _
    have h := dyadic_count_weight_term_le H j
    have h0 : (0 : ℝ) < (2 / 3 : ℝ) ^ j := by positivity
    calc ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
        ≤ ((H : ℝ) / 2 * 2 ^ j + 4 ^ j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right h h0.le
      _ = (H : ℝ) / 2 * (4 / 3 : ℝ) ^ j + (8 / 3 : ℝ) ^ j := geom_term_eq H j
  have hg43 : ∑ j ∈ Finset.range (L + 1), (4 / 3 : ℝ) ^ j = 4 * (4 / 3 : ℝ) ^ L - 3 := by
    rw [geom_sum_eq (by norm_num : (4 / 3 : ℝ) ≠ 1), pow_succ]
    ring
  have hg83 : ∑ j ∈ Finset.range (L + 1), (8 / 3 : ℝ) ^ j
      = 8 / 5 * (8 / 3 : ℝ) ^ L - 3 / 5 := by
    rw [geom_sum_eq (by norm_num : (8 / 3 : ℝ) ≠ 1), pow_succ]
    ring
  have hsum : ∑ j ∈ Finset.range (L + 1),
      ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
      ≤ 2 * (H : ℝ) * (4 / 3 : ℝ) ^ L + 8 / 5 * (8 / 3 : ℝ) ^ L := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hg43, hg83]
    nlinarith [hHR]
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j :=
    (geom_weight_sum_pos L).le
  have hmix1 : (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ L = 2 ^ L := by
    rw [← mul_pow]; norm_num
  have hmix2 : (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ L = 4 ^ L := by
    rw [← mul_pow]; norm_num
  have h4L : (4 : ℝ) ^ L = ((2 : ℝ) ^ L) ^ 2 := by
    rw [← pow_mul, mul_comm L 2, pow_mul]; norm_num
  calc (∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range (L + 1),
            ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
      ≤ (∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j)
          * (2 * (H : ℝ) * (4 / 3 : ℝ) ^ L + 8 / 5 * (8 / 3 : ℝ) ^ L) :=
        mul_le_mul_of_nonneg_left hsum hS0
    _ ≤ (3 * (3 / 2 : ℝ) ^ L) * (2 * (H : ℝ) * (4 / 3 : ℝ) ^ L + 8 / 5 * (8 / 3 : ℝ) ^ L) := by
        refine mul_le_mul_of_nonneg_right (geom_weight_sum_le L) ?_
        positivity
    _ = 6 * (H : ℝ) * ((3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ L)
          + 24 / 5 * ((3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ L) := by ring
    _ = 6 * (H : ℝ) * (2 : ℝ) ^ L + 24 / 5 * ((2 : ℝ) ^ L) ^ 2 := by rw [hmix1, hmix2, h4L]
    _ ≤ 54 / 5 * (H : ℝ) ^ 2 := by nlinarith [hpow, h2pos, hHR]

/-- **THE WEIGHTED SMALL-`j` COUNT** (`dyadic_count_weight_geom_small_le`) — the head `j < j₀`
of the same weighted sum, prefactor included:

  `(3(3/2)^L)·((3H/2)(4/3)^{j₀} + (3/5)(8/3)^{j₀})
     = (9/2)·H·(3/2)^L·(4/3)^{j₀} + (9/5)·(3/2)^L·(8/3)^{j₀}`.

TWO summands, not one — the `H·2^{j-1}` half of the term bound is top-heavy at the ratio
`2/(3/2) = 4/3` and the `4^j` half at `4/(3/2) = 8/3`, and the two ratios no longer collapse
into a single `4^{j₀}` the way they did under the uniform prefactor.  Against the block's own
`H²` normalisation the two decay as `(3/2)^{log₂H}/H ≍ H^{-0.415}` and
`(3/2)^{log₂H}/H² ≍ H^{-1.415}`, and BOTH give the same floor demand `H ≳ 2^{j₀}` —
exactly half the exponent the uniform route's `4^{j₀}` demanded
(`log₂(4/3) = 0.41504`, `log₂(8/3) = 1.41504`). -/
theorem dyadic_count_weight_geom_small_le {H : ℕ} (hH : 0 < H) (j₀ : ℕ) :
    (∑ j ∈ Finset.range (Nat.log 2 H + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range j₀,
            ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ := by
  set L := Nat.log 2 H with hL
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hterm : ∀ j ∈ Finset.range j₀,
      ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
        ≤ (H : ℝ) / 2 * (4 / 3 : ℝ) ^ j + (8 / 3 : ℝ) ^ j := by
    intro j _
    have h := dyadic_count_weight_term_le H j
    have h0 : (0 : ℝ) < (2 / 3 : ℝ) ^ j := by positivity
    calc ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
        ≤ ((H : ℝ) / 2 * 2 ^ j + 4 ^ j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right h h0.le
      _ = (H : ℝ) / 2 * (4 / 3 : ℝ) ^ j + (8 / 3 : ℝ) ^ j := geom_term_eq H j
  have hg43 : ∑ j ∈ Finset.range j₀, (4 / 3 : ℝ) ^ j = 3 * (4 / 3 : ℝ) ^ j₀ - 3 := by
    rw [geom_sum_eq (by norm_num : (4 / 3 : ℝ) ≠ 1)]
    ring
  have hg83 : ∑ j ∈ Finset.range j₀, (8 / 3 : ℝ) ^ j = 3 / 5 * (8 / 3 : ℝ) ^ j₀ - 3 / 5 := by
    rw [geom_sum_eq (by norm_num : (8 / 3 : ℝ) ≠ 1)]
    ring
  have hsum : ∑ j ∈ Finset.range j₀,
      ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
      ≤ 3 / 2 * (H : ℝ) * (4 / 3 : ℝ) ^ j₀ + 3 / 5 * (8 / 3 : ℝ) ^ j₀ := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hg43, hg83]
    nlinarith [hHR]
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j :=
    (geom_weight_sum_pos L).le
  calc (∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range j₀,
            ((((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2) * (2 / 3 : ℝ) ^ j
      ≤ (∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j)
          * (3 / 2 * (H : ℝ) * (4 / 3 : ℝ) ^ j₀ + 3 / 5 * (8 / 3 : ℝ) ^ j₀) :=
        mul_le_mul_of_nonneg_left hsum hS0
    _ ≤ (3 * (3 / 2 : ℝ) ^ L)
          * (3 / 2 * (H : ℝ) * (4 / 3 : ℝ) ^ j₀ + 3 / 5 * (8 / 3 : ℝ) ^ j₀) := by
        refine mul_le_mul_of_nonneg_right (geom_weight_sum_le L) ?_
        positivity
    _ = 9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀ := by ring

/-! ## §5 — THE MAXIMAL STEP, LENGTH-GRADED

The input is the block mean square of the FIXED dyadic lengths at the SHIFTED blocks — the
bases the sub-windows' pieces actually have — and it is graded BY THE LENGTH: `F j H`, one
grade per dyadic scale.  The output is `M4ChiBlockMeanSq`, the wave's analytic item, at the
split price `m4BclGraded j₀ Fan Ftr`: the maximal price `m4Cmax H` on the analytic envelope
`Fan` (the lengths `j₀ ≤ j`) plus the `H`-linear small head on the trivial envelope `Ftr`
(the lengths `j < j₀`). -/

/-- **THE MAXIMAL PRICE**, ⟦LEVER 1′⟧: `Cmax = 54/5 = 10.8`, a CONSTANT.  The uniform
Chebyshev of the maximal step charged `3·(log₂H + 1)`; the geometric-weight Cauchy–Schwarz at
`c = 3/2` charges `(∑(3/2)^j)·(weighted count)/H² ≤ 54/5` — no log at all.  The signature
keeps its `H` (every consumer reads `m4Cmax H`), and the body no longer uses it: THIS is the
content of the lever. -/
def m4Cmax (_H : ℕ) : ℝ := 54 / 5

theorem m4Cmax_nonneg (H : ℕ) : 0 ≤ m4Cmax H := by
  unfold m4Cmax
  positivity

/-- **THE GRADED BLOCK PRICE** (`m4BclGraded`) — what the length-graded shifted datum
assembles to at the floor `j₀`, re-cut at the geometric weights:

  `m4BclGraded j₀ Fan Ftr H
     = m4Cmax H·Fan H
       + ((9/2)·(3/2)^{log₂H}·(4/3)^{j₀}/H + (9/5)·(3/2)^{log₂H}·(8/3)^{j₀}/H²)·Ftr H`.

The first summand is §4's weighted full count `(54/5)H²` against the analytic envelope — a
CONSTANT price, ⟦LEVER 1′⟧'s whole point.  The second is §4's weighted small head against the
trivial envelope, divided by the block's own `H²` normalisation, and it is TWO summands
because the weighted head's two geometric halves run at DIFFERENT ratios (`4/3` and `8/3`).
Numerically `(3/2)^{log₂H} = H^{0.58496}`, so the head is

  `4.5·(4/3)^{j₀}·H^{-0.41504} + 1.8·(8/3)^{j₀}·H^{-1.41504}`,

and both summands impose the SAME floor `H ≳ 2^{j₀}` — half the exponent of the uniform
route's `4^{j₀}`.  `j₀` is a PARAMETER: `(4/3)^{j₀}` and `(8/3)^{j₀}` are constants against
`H` exactly because the floor is the consumer's (at the door, `M·Adoor M`). -/
def m4BclGraded (j₀ : ℕ) (Fan Ftr : ℕ → ℝ) (H : ℕ) : ℝ :=
  m4Cmax H * Fan H
    + (9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ / (H : ℝ)
        + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2) * Ftr H

theorem m4BclGraded_nonneg {j₀ : ℕ} {Fan Ftr : ℕ → ℝ} {H : ℕ}
    (hFan : 0 ≤ Fan H) (hFtr : 0 ≤ Ftr H) : 0 ≤ m4BclGraded j₀ Fan Ftr H := by
  have h1 : (0 : ℝ) ≤ m4Cmax H * Fan H := mul_nonneg (m4Cmax_nonneg H) hFan
  have hA : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ / (H : ℝ)
      + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 := by positivity
  have h2 := mul_nonneg hA hFtr
  unfold m4BclGraded
  linarith

/-- **THE SMALL-`j` THRESHOLD** (`m4SmallGradeFits`) — the comparison that makes the graded
split cost at most a factor `2`: the WHOLE small-`j` charge (§4's weighted head, both
summands) sits under `H²·(m4Cmax·Fan H)`, the analytic half's own contribution to the same
count.

Stated symbolically on purpose, and cleared of the `H²` normalisation so no division
appears.  Neither `(4/3)^{j₀}` nor `(8/3)^{j₀}` moves with `H`, so this is a threshold in
`H` ALONE — see `m4SmallGradeFits_of_threshold`.  Against the uniform route's
`2·4^{j₀}·Ftr H ≤ H·(3·Fan H)` the demand is `2^{j₀}`-genre rather than `4^{j₀}`-genre: the
floor's exponent HALVES. -/
def m4SmallGradeFits (j₀ : ℕ) (Fan Ftr : ℕ → ℝ) (H : ℕ) : Prop :=
  (9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ * (H : ℝ)
      + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀) * Ftr H
    ≤ (H : ℝ) ^ 2 * (m4Cmax H * Fan H)

/-- **THE THRESHOLD, IN `H` ALONE** — any envelope `Ftr H ≤ D` on the trivial grade fits as
soon as the weighted head against `D` sits under `H²·Fan H`.  Both `(4/3)^{j₀}`, `(8/3)^{j₀}`
and `D` are `H`-free at the door (`j₀ = M·Adoor M`, `D ≍ 1` the block density), and
`(3/2)^{log₂H}·H = H^{1.585}` against `H²` is the honest `H^{0.415}` of head room, so this is
one inequality in `H`.  (The `54/5` of `m4Cmax` is left as slack — asking for `Fan H` alone
on the right is strictly stronger and keeps the numeral out of the consumer's hypothesis.) -/
theorem m4SmallGradeFits_of_threshold {j₀ : ℕ} {Fan Ftr : ℕ → ℝ} {H : ℕ} {D : ℝ}
    (hFtr : Ftr H ≤ D) (hFan : 0 ≤ Fan H)
    (hthr : (9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ * (H : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀) * D
        ≤ (H : ℝ) ^ 2 * Fan H) :
    m4SmallGradeFits j₀ Fan Ftr H := by
  have h4 : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ * (H : ℝ)
      + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀ := by positivity
  have h1 := mul_le_mul_of_nonneg_left hFtr h4
  have hH : (0 : ℝ) ≤ (H : ℝ) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ (H : ℝ) ^ 2 * Fan H := mul_nonneg hH hFan
  unfold m4SmallGradeFits m4Cmax
  nlinarith

/-- **THE SPLIT COSTS A FACTOR `2`** (`m4BclGraded_le_of_fits`) — under the threshold the
graded price is at most twice the ungraded one at the analytic envelope.  Nothing in the
close's budget is spent by the small lengths; they are absorbed.  The STATEMENT is the
landed one, byte for byte; only the threshold it reads has moved. -/
theorem m4BclGraded_le_of_fits {j₀ : ℕ} {Fan Ftr : ℕ → ℝ} {H : ℕ} (hH : 0 < H)
    (hfit : m4SmallGradeFits j₀ Fan Ftr H) :
    m4BclGraded j₀ Fan Ftr H ≤ 2 * (m4Cmax H * Fan H) := by
  have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
  have hfit' := hfit
  unfold m4SmallGradeFits at hfit'
  have hkey : (9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ / (H : ℝ)
        + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2) * Ftr H
      ≤ m4Cmax H * Fan H := by
    have heq : (9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ / (H : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2) * Ftr H
        = ((9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ j₀ * (H : ℝ)
            + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ j₀) * Ftr H) / (H : ℝ) ^ 2 := by
      field_simp
    rw [heq, div_le_iff₀ hH2]
    linarith [hfit']
  unfold m4BclGraded
  linarith

/-- **THE SHIFTED FIXED-LENGTH DATUM** (`M4ChiShiftBlockMeanSq`) — the block mean square of
the sieved, χ-twisted window sums at the DYADIC lengths `2^j ≤ H` and at every shift `s ≤ H`
of the ladder block, LENGTH-GRADED: the grade is `F j H`, one per dyadic scale.  The shifts
are exactly the bases the dyadic pieces of a sub-window have; the grade is normalised by the
UNSHIFTED block bottom `X_{i+1}`, so the shift costs nothing in the currency. -/
def M4ChiShiftBlockMeanSq (R : ChowlaRegime) (M k : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, ∀ s ≤ H,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1) + s) (doorLadder R.x H i + s),
          ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **ANTI-VACUITY** (M4-1's lesson: a hypothesis may be kernel-true and consumable by
nobody).  The shifted family is INHABITED at the trivial grade `1`, AT EVERY LENGTH: every
sieved window sum is bounded by its length and the shifted block has `B − A ≤ A` cells
(`doorLadder_fit`).  The saving — the whole content of ⟦R3⟧ — is what makes the grade small
at the LARGE lengths; the SHAPE costs nothing, and at the small lengths this trivial grade is
the one the split actually charges. -/
theorem m4_chiShiftBlock_trivial (R : ChowlaRegime) (M k : ℕ) :
    M4ChiShiftBlockMeanSq R M k (fun _ _ => 1) := by
  intro H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2 ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro n _
    have hsub : doorSievedWindow M (2 ^ j) n ⊆ Finset.Ioc n (n + 2 ^ j) := by
      simp only [doorSievedWindow, sievedWindow]
      exact Finset.filter_subset _ _
    have hcard : (doorSievedWindow M (2 ^ j) n).card ≤ 2 ^ j := by
      calc (doorSievedWindow M (2 ^ j) n).card ≤ (Finset.Ioc n (n + 2 ^ j)).card :=
            Finset.card_le_card hsub
        _ = 2 ^ j := by simp [Nat.card_Ioc]
    have hnorm : ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ≤ ((2 ^ j : ℕ) : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ m ∈ doorSievedWindow M (2 ^ j) n, ‖liouChi χ m‖
          ≤ ∑ _m ∈ doorSievedWindow M (2 ^ j) n, (1 : ℝ) :=
            Finset.sum_le_sum fun m _ => norm_liouChi_le_one χ m
        _ = ((doorSievedWindow M (2 ^ j) n).card : ℝ) := by simp
        _ ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hcard
    have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
    nlinarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have hcast : ((B + s - (A + s) : ℕ) : ℝ) ≤ (A : ℝ) := by
    have hnat : B + s - (A + s) ≤ A := by omega
    exact_mod_cast hnat
  have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
  calc ((B + s - (A + s) : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2
      ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcast h2j
    _ = 1 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by ring

/-- **⟦R1⟧, EXECUTED, LENGTH-GRADED** (`m4_chiBlockMeanSq_of_shiftBlock`) — the sub-window
sup's block mean square from the fixed dyadic lengths, at the SPLIT price `m4BclGraded`.

The trivial route `sup² ≤ ∑_{K ≤ H}` would cost `H+1` and is fatal; this route costs one
log, because the `≤ log₂H+1` dyadic pieces are paid once by Chebyshev and the offsets at
scale `j` number only `⌊H/2^{j+1}⌋+1`.

⟦THE SPLIT⟧ the length-graded input `F j H` is charged through TWO envelopes at the named
floor `j₀`: `Fan` on the lengths the capstone can actually speak about (`j₀ ≤ j`, where §4's
full count `3H²` applies) and `Ftr` on the lengths below it (`j < j₀`, where §4's small count
`2H·4^{j₀}` applies — linear in `H`).  Neither envelope is required to be small; the
arithmetic of the two counts is what makes the small half free (`m4SmallGradeFits`). -/
theorem m4_chiBlockMeanSq_of_shiftBlock {R : ChowlaRegime} {M k : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (htr : ∀ j H : ℕ, j < j₀ → F j H ≤ Ftr H)
    (hfix : M4ChiShiftBlockMeanSq R M k F) :
    M4ChiBlockMeanSq R M k (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi q hq hqQ i hik χ
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  set L := Nat.log 2 H with hL
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set S : ℝ := ∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j with hS
  have hS0 : (0 : ℝ) ≤ S := (geom_weight_sum_pos L).le
  -- ⟦STEP 1⟧ the pointwise maximal bound (§3), at the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M H n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, S
          * ∑ j ∈ Finset.range (L + 1),
              (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic χ M H n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, S
        * ∑ j ∈ Finset.range (L + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = S * ∑ j ∈ Finset.range (L + 1),
          (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hjt : ∀ j ∈ Finset.range (L + 1), ∀ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
      ∑ n ∈ Finset.Ioc A B, X j t n ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by
    intro j hj t ht
    have hjL : j ≤ L := by
      have := Finset.mem_range.mp hj
      omega
    have ht' : t ≤ H / 2 ^ (j + 1) := by
      have := Finset.mem_range.mp ht
      omega
    have hs : 2 ^ (j + 1) * t ≤ H := by
      calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (H / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht'
        _ = H / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
        _ ≤ H := Nat.div_mul_le_self H (2 ^ (j + 1))
    have hre : ∑ n ∈ Finset.Ioc A B, X j t n
        = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2 :=
      sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
    rw [hre]
    exact hfix H hlo hhi q hq hqQ i hik χ j hjL _ hs
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j => (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg H j
  have hj : ∀ j ∈ Finset.range (L + 1),
      (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hle : ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (H / 2 ^ (j + 1) + 1), F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) :=
      Finset.sum_le_sum fun t ht => hjt j hjm t ht
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (F j H * (A : ℝ)) * W j := by
      calc ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
          ≤ (((H / 2 ^ (j + 1) : ℕ) + 1 : ℕ) : ℝ) * (F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)) :=
            hle
        _ = (F j H * (A : ℝ)) * W j := by
            simp only [hW]
            push_cast
            ring
    calc (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((F j H * (A : ℝ)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT: the large lengths against the weighted full count, the small ones
  -- against the weighted head.  This is the only place the floor `j₀` is read.
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hlarge : ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
        (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
      ≤ Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j := by
    have hFanA : (0 : ℝ) ≤ Fan H * (A : ℝ) := mul_nonneg (hFan0 H) hA0
    calc ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
          (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
        ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj₀ := (Finset.mem_filter.mp hjm).2
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (han j H hj₀) hA0) (hWw0 j)
      _ ≤ ∑ j ∈ Finset.range (L + 1), (Fan H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hFanA (hWw0 j))
      _ = Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
        (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
      ≤ Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hFtrA : (0 : ℝ) ≤ Ftr H * (A : ℝ) := mul_nonneg (hFtr0 H) hA0
    have hsub : (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
          (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
        ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
            (Ftr H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj₀ : j < j₀ := by have := (Finset.mem_filter.mp hjm).2; omega
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (htr j H hj₀) hA0) (hWw0 j)
      _ ≤ ∑ j ∈ Finset.range j₀, (Ftr H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hFtrA (hWw0 j))
      _ = Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (L + 1),
        (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j
        + Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    refine le_trans (Finset.sum_le_sum hj) ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (L + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ the two weighted counts, prefactor included (§4)
  have hHne : ((H : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
    exact ne_of_gt this
  have hfull : S * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j ≤ 54 / 5 * (H : ℝ) ^ 2 := by
    rw [hS, hW, hL]
    exact dyadic_count_weight_geom_le hH0
  have hhead : S * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀ := by
    rw [hS, hW, hL]
    exact dyadic_count_weight_geom_small_le hH0 j₀
  have hFanA : (0 : ℝ) ≤ Fan H * (A : ℝ) := mul_nonneg (hFan0 H) hA0
  have hFtrA : (0 : ℝ) ≤ Ftr H * (A : ℝ) := mul_nonneg (hFtr0 H) hA0
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup χ M H n) ^ 2
      ≤ S * ∑ j ∈ Finset.range (L + 1),
          (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ S * (Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j
          + Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hS0
    _ = Fan H * (A : ℝ) * (S * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j)
          + Ftr H * (A : ℝ) * (S * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ Fan H * (A : ℝ) * (54 / 5 * (H : ℝ) ^ 2)
          + Ftr H * (A : ℝ) * (9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hFanA
        have h2 := mul_le_mul_of_nonneg_left hhead hFtrA
        linarith
    _ = m4BclGraded j₀ Fan Ftr H * (H : ℝ) ^ 2 * (A : ℝ) := by
        unfold m4BclGraded m4Cmax
        rw [← hL]
        field_simp

/-! ## §6 — THE ROW DATUM AT THE DYADIC LENGTHS AND THE SHIFTED SCALES

`M4WaveClosed` §6's bridge, re-run at the window length `2^j` and the block scale
`X := X_{i+1} + s`.  Both fits are honest: `X ≤ A + s` is `le_rfl`, and
`(B+s) + 2^j ≤ 2(A+s)` is `doorLadder_fit`'s `B + H ≤ 2A` with `2^j ≤ H` — the shift `s`
appears on both sides and pays for itself.  The harmonic→flat exchange costs the ladder's
own factor `2`, because `B + s ≤ B + H ≤ 2A`. -/

/-- **THE ROW INPUT, PER DYADIC LENGTH AND SHIFT** (`M4ChiDyadicRowMeanSq`) — the mean square
of the door's sieved, χ-twisted, UN-PHASED datum in `ThmA2.thm_a2'_of_rows`' own currency, at
the window length `h = 2^j` (`j ≤ log₂H`) and the scale `X = X_{i+1} + s` (`s ≤ H`), with the
capstone's two pins `X_d = X` and `N = 2X_d` intact at every instance.

**LENGTH-GRADED**: the grade is `MS j H` — one per dyadic length, not one for all of them.
⟦WALL 2⟧ (the header) is why: the capstone cannot be STATED below `j = M·Adoor M`, and at
`j = 0` the quantity is the block density, `≍ 1`.  A supplier therefore owes a small grade
only where the capstone speaks, and the trivial grade everywhere else; §5's split is what
makes that enough. -/
def M4ChiDyadicRowMeanSq (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, ∀ s ≤ H,
      1 / ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)
          * (∫ y in ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)..(2
                * ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)),
              ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                  * shortSum (doorChiCoeff χ M)
                      (seamS0 (2 * (doorLadder R.x H (i + 1) + s))
                        ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
        ≤ MS j H

/-- **THE SHIFTED BRIDGE** (`m4_chiShiftBlock_of_dyadicRow`) — the per-length, per-shift row
mean square becomes the shifted block sum of squared sieved-twisted window sums, at the grade
`2·MS`: B-4's `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` at the frequency `0` and the
scale `X := X_{i+1}+s`, then the harmonic→flat exchange against `B + s ≤ 2·X_{i+1}`. -/
theorem m4_chiShiftBlock_of_dyadicRow {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    (hrow : M4ChiDyadicRowMeanSq R M k MS) :
    M4ChiShiftBlockMeanSq R M k (fun j H => 2 * MS j H) := by
  intro H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  have hstepd := doorLadder_step_le hxH i
  have hfloor := doorLadder_floor hxH (i + 1)
  have h2j : 2 ^ j ≤ H := by
    calc 2 ^ j ≤ 2 ^ Nat.log 2 H := Nat.pow_le_pow_right (by norm_num) hjL
      _ ≤ H := Nat.pow_log_le_self 2 hH0.ne'
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAB : A + s ≤ B + s := by omega
  have hXpos : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by
    have : 0 < A + s := by omega
    exact_mod_cast this
  have hBfit : (((B + s : ℕ)) : ℝ) + ((2 ^ j : ℕ) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s + 2 ^ j ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff χ M m = 0 :=
    hcov_of_seamS0 (doorChiCoeff χ M) (A := A + s) (B := B + s) (N := 2 * (A + s))
      (H := 2 ^ j) le_rfl (by omega)
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hladder := sum_Ioc_absWindowSum_sq_div_le (doorChiCoeff χ M)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (X := (((A + s : ℕ)) : ℝ)) (MS := MS j H) hh0 hAB hXpos le_rfl hBfit hcov hMSrow
  -- ⟦the grade is nonnegative, because the harmonic sum is⟧
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H :=
    le_trans (Finset.sum_nonneg fun n _ => by positivity) hladder
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hladder (Nat.cast_nonneg _)
  have hBs : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : B + s ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by
    refine le_trans hex ?_
    have := mul_le_mul_of_nonneg_right hBs hP0
    calc (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        ≤ 2 * (A : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) := this
      _ = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by ring
  simpa only [absWindowSum_doorChiCoeff_zero] using hfinal

/-! ## §7 — THE CLOSE

`m4_wave_closed_of_chi`'s analytic slot, filled from the LENGTH-GRADED row datum: `Cmax` is
explicit, ⟦R1⟧ is no longer a hypothesis, and the two envelopes (`MSan` at `j₀ ≤ j`, `MStr`
at `j < j₀`) are what a supplier owes. -/

/-- **THE WAVE'S ANALYTIC ITEM, FROM THE GRADED ROW DATUM** — `M4ChiBlockMeanSq` at the grade
`m4BclGraded j₀ (2·MSan) (2·MStr) H`,
⟦R1⟧ discharged.  The bridge's own factor `2` (the harmonic→flat exchange) rides both
envelopes. -/
theorem m4_chiBlockMeanSq_of_dyadicRow {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ} (j₀ : ℕ)
    (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H)
    (htr : ∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H)
    (hrow : M4ChiDyadicRowMeanSq R M k MS) :
    M4ChiBlockMeanSq R M k
      (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  refine m4_chiBlockMeanSq_of_shiftBlock (F := fun j H => 2 * MS j H) j₀ ?_ ?_ ?_ ?_
    (m4_chiShiftBlock_of_dyadicRow hrow)
  · intro H; have := hMSan0 H; linarith
  · intro H; have := hMStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro j H hj; have := htr j H hj; linarith

/-- **THE CLOSE AT THE GRADED DYADIC ROW DATUM** (`m4_wave_closed_of_dyadicRow`) —
`m4_wave_closed` with class (c) read down to the capstone's own currency, ⟦R1⟧ EXECUTED
rather than assumed.

The consumption list is `m4_wave_closed_of_row`'s with the maximal step removed: the
`M4ChiMaximalStep` slot is gone, `Cmax` is the explicit constant `m4Cmax H = 54/5`, and the row
datum is asked for at the dyadic window lengths `2^j ≤ H` and the shifted scales
`X_{i+1} + s`, `s ≤ H` — the instances the sub-windows' dyadic pieces actually need.  ⟦R2⟧
(the non-coprime classes) and ⟦R3⟧ (the capstone at the door's datum) are unchanged.

⟦THE REGISTER'S GRADED ITEMS⟧, the only change from the uniform version:

* the row grade is `MS : ℕ → ℕ → ℝ` and the nonnegativity slot is now TWO envelopes,
  `0 ≤ MSan H` and `0 ≤ MStr H`, plus the two envelope gates `MS j H ≤ MSan H` (`j₀ ≤ j`)
  and `MS j H ≤ MStr H` (`j < j₀`);
* the floor `j₀` is a BOUND PARAMETER of the register, supplied by the consumer (at the door
  it is `M·Adoor M`), never a numeral;
* the drift line and the non-coprime line read the assembled
  `m4BclGraded j₀ (2·MSan) (2·MStr) H` in place of `m4Cmax H·(2·MS H)`.

The conclusion `¬ logChowla2Fails R.eps R.x R.ω` is untouched.

⟦THE CONSUMPTION NOTE, HONESTLY⟧ nothing here forces `j₀ ≤ log₂H`.  When `log₂H < j₀` the
large-`j` half of §5's split is EMPTY and every length is charged at `Ftr` — the bound is
then true and useless, exactly as it should be, and `m4SmallGradeFits` is what excludes that
regime: it needs `H ≳ 2^{j₀}` (⟦LEVER 1′⟧ halved the uniform route's `4^{j₀}`).  At the door
`j₀ = M·Adoor M ≥ 2^18`, so the window floor must swallow `2^{M·Adoor M}`.  The register
admits this: `U1floor ≤ R.Hlo` is chosen
BEFORE `R`, and `M` is constrained only through `Cg`/`δ` (`M4DoorGates.hMδ`), which are
available then — so a consumer fixes `M` first and asks for the matching floor.  The
ordering is workable; it is not free, and it is the item the supplier's threshold check must
carry. -/
theorem m4_wave_closed_of_dyadicRow :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (j₀ M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded j₀ (fun H => 2 * MSan H)
                      (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiDyadicRowMeanSq R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff M) H n q r) ^ 2
                  ≤ m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                      * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS MSan MStr j₀ M k hgates hMSan0 hMStr0 hBraw0
    han htr hdrift hdel hrest hrow hnoncop => ?_⟩
  refine hR δ Braw (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) M k hgates
    (fun H => m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith))
    hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_dyadicRow j₀ hMSan0 hMStr0 han htr hrow) hnoncop

/-- **THE CLOSE AT THE GRADED DYADIC ROW DATUM, SPLIT** (`m4_wave_closed_of_dyadicRow_split`)
— the twin of `m4_wave_closed_of_dyadicRow` (:912) at the head's constant grade
(second-road freeze v2, wave ①; the family's contract is `M4Exit` §7).

**This is the row-level host of the split family**, and it adopts its own graded shape
VERBATIM: `m4BclGraded j₀ (2·MSan) (2·MStr)`, the two envelopes with their two gates, the
bound parameter `j₀`, and the four envelope-reading conjuncts (the drift line and the
non-coprime line both read the assembled grade).  ⟦R1⟧ stays EXECUTED, ⟦R2⟧ and ⟦R3⟧
unchanged, and the ⟦CONSUMPTION NOTE⟧ above (the `4^{j₀}` floor demand riding `U1floor`)
applies here word for word.

⟦THE DIFF against the landed statement⟧, exactly three lines:

* `∀ (C : ℝ), 0 ≤ C →` — DELETED (⟦THE C-BINDER WARNING⟧);
* `√(Braw H) ≤ mrtDeliveredGrade (C/2) H` → `√(Braw H) ≤ δ₀/2`;
* `δ/4 + 4·2^k/x ≤ mrtDeliveredGrade (C/2) H` → `δ/4 + 4·2^k/x ≤ δ₀/2`.

Every other byte — including the conclusion `¬ logChowla2Fails R.eps R.x R.ω` — is the
landed one's. -/
theorem m4_wave_closed_of_dyadicRow_split :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (j₀ M k : ℕ),
            M4DoorGates Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded j₀ (fun H => 2 * MSan H)
                      (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.sqrt (Braw H) ≤ δ₀ / 2) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 2) →
            M4ChiDyadicRowMeanSq R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff M) H n q r) ^ 2
                  ≤ m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                      * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS MSan MStr j₀ M k hgates hMSan0 hMStr0 hBraw0
    han htr hdrift hdel hrest hrow hnoncop => ?_⟩
  refine hR δ Braw (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) M k hgates
    (fun H => m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith))
    hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_dyadicRow j₀ hMSan0 hMStr0 han htr hrow) hnoncop

/-! ## §GK — the G-lever twin

The additive `_gk` family at `G := s13GK K M` (`GLever`): each declaration below is its
landed original with `(K : ℕ)` as a new FIRST binder and the door datum read at the lever
(`doorSievedWindow_gk`, `doorChiSup_gk`, `doorSievedCoeff_gk`).  `J` stays `2`; the sup's
window binder `K` in §3 is α-renamed `Kw`; every other byte of the proof text is the landed
one's, with `_gk` names in place of their landed originals.
-/

/-- **THE POINTWISE MAXIMAL BOUND AT THE LEVER** — `doorChiSup_sq_le_dyadic` (:396). -/
theorem doorChiSup_sq_le_dyadic_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) :
    (doorChiSup_gk K χ M H n) ^ 2
      ≤ (∑ j ∈ Finset.range (Nat.log 2 H + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range (Nat.log 2 H + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
              ‖∑ m ∈ doorSievedWindow_gk K M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2)
              * (2 / 3 : ℝ) ^ j := by
  obtain ⟨Kw, hKmem, hKeq⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.Icc 0 H)
      ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
      (fun Kw => ‖∑ m ∈ doorSievedWindow_gk K M Kw n, liouChi χ m‖)
  have hKH : Kw ≤ H := (Finset.mem_Icc.mp hKmem).2
  have hval : doorChiSup_gk K χ M H n = ‖∑ m ∈ doorSievedWindow_gk K M Kw n, liouChi χ m‖ := hKeq
  rw [hval]
  simp only [doorSievedWindow_gk]
  exact norm_sum_sievedWindow_sq_le_dyadic _ (liouChi χ) H Kw n hKH

/-- **THE SHIFTED FIXED-LENGTH FAMILY AT THE LEVER** — `M4ChiShiftBlockMeanSq` (:776). -/
def M4ChiShiftBlockMeanSq_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, ∀ s ≤ H,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1) + s) (doorLadder R.x H i + s),
          ‖∑ m ∈ doorSievedWindow_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **ANTI-VACUITY AT THE LEVER** — `m4_chiShiftBlock_trivial` (:789). -/
theorem m4_chiShiftBlock_trivial_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) :
    M4ChiShiftBlockMeanSq_gk K R M k (fun _ _ => 1) := by
  intro H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖∑ m ∈ doorSievedWindow_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2 ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro n _
    have hsub : doorSievedWindow_gk K M (2 ^ j) n ⊆ Finset.Ioc n (n + 2 ^ j) := by
      simp only [doorSievedWindow_gk, sievedWindow]
      exact Finset.filter_subset _ _
    have hcard : (doorSievedWindow_gk K M (2 ^ j) n).card ≤ 2 ^ j := by
      calc (doorSievedWindow_gk K M (2 ^ j) n).card ≤ (Finset.Ioc n (n + 2 ^ j)).card :=
            Finset.card_le_card hsub
        _ = 2 ^ j := by simp [Nat.card_Ioc]
    have hnorm : ‖∑ m ∈ doorSievedWindow_gk K M (2 ^ j) n, liouChi χ m‖ ≤ ((2 ^ j : ℕ) : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ m ∈ doorSievedWindow_gk K M (2 ^ j) n, ‖liouChi χ m‖
          ≤ ∑ _m ∈ doorSievedWindow_gk K M (2 ^ j) n, (1 : ℝ) :=
            Finset.sum_le_sum fun m _ => norm_liouChi_le_one χ m
        _ = ((doorSievedWindow_gk K M (2 ^ j) n).card : ℝ) := by simp
        _ ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hcard
    have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_gk K M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
    nlinarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have hcast : ((B + s - (A + s) : ℕ) : ℝ) ≤ (A : ℝ) := by
    have hnat : B + s - (A + s) ≤ A := by omega
    exact_mod_cast hnat
  have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
  calc ((B + s - (A + s) : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2
      ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcast h2j
    _ = 1 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by ring

/-- **THE MAXIMAL STEP AT THE LEVER** — `m4_chiBlockMeanSq_of_shiftBlock` (:838). -/
theorem m4_chiBlockMeanSq_of_shiftBlock_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (htr : ∀ j H : ℕ, j < j₀ → F j H ≤ Ftr H)
    (hfix : M4ChiShiftBlockMeanSq_gk K R M k F) :
    M4ChiBlockMeanSq_gk K R M k (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi q hq hqQ i hik χ
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  set L := Nat.log 2 H with hL
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow_gk K M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set S : ℝ := ∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j with hS
  have hS0 : (0 : ℝ) ≤ S := (geom_weight_sum_pos L).le
  -- ⟦STEP 1⟧ the pointwise maximal bound (§3), at the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_gk K χ M H n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, S
          * ∑ j ∈ Finset.range (L + 1),
              (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_gk K χ M H n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, S
        * ∑ j ∈ Finset.range (L + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = S * ∑ j ∈ Finset.range (L + 1),
          (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hjt : ∀ j ∈ Finset.range (L + 1), ∀ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
      ∑ n ∈ Finset.Ioc A B, X j t n ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by
    intro j hj t ht
    have hjL : j ≤ L := by
      have := Finset.mem_range.mp hj
      omega
    have ht' : t ≤ H / 2 ^ (j + 1) := by
      have := Finset.mem_range.mp ht
      omega
    have hs : 2 ^ (j + 1) * t ≤ H := by
      calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (H / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht'
        _ = H / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
        _ ≤ H := Nat.div_mul_le_self H (2 ^ (j + 1))
    have hre : ∑ n ∈ Finset.Ioc A B, X j t n
        = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2 :=
      sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
    rw [hre]
    exact hfix H hlo hhi q hq hqQ i hik χ j hjL _ hs
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j => (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg H j
  have hj : ∀ j ∈ Finset.range (L + 1),
      (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hle : ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (H / 2 ^ (j + 1) + 1), F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) :=
      Finset.sum_le_sum fun t ht => hjt j hjm t ht
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (F j H * (A : ℝ)) * W j := by
      calc ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
          ≤ (((H / 2 ^ (j + 1) : ℕ) + 1 : ℕ) : ℝ) * (F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)) :=
            hle
        _ = (F j H * (A : ℝ)) * W j := by
            simp only [hW]
            push_cast
            ring
    calc (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((F j H * (A : ℝ)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT: the large lengths against the weighted full count, the small ones
  -- against the weighted head.  This is the only place the floor `j₀` is read.
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hlarge : ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
        (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
      ≤ Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j := by
    have hFanA : (0 : ℝ) ≤ Fan H * (A : ℝ) := mul_nonneg (hFan0 H) hA0
    calc ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
          (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
        ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj₀ := (Finset.mem_filter.mp hjm).2
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (han j H hj₀) hA0) (hWw0 j)
      _ ≤ ∑ j ∈ Finset.range (L + 1), (Fan H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hFanA (hWw0 j))
      _ = Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
        (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
      ≤ Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hFtrA : (0 : ℝ) ≤ Ftr H * (A : ℝ) := mul_nonneg (hFtr0 H) hA0
    have hsub : (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
          (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
        ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
            (Ftr H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj₀ : j < j₀ := by have := (Finset.mem_filter.mp hjm).2; omega
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (htr j H hj₀) hA0) (hWw0 j)
      _ ≤ ∑ j ∈ Finset.range j₀, (Ftr H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hFtrA (hWw0 j))
      _ = Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (L + 1),
        (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j
        + Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    refine le_trans (Finset.sum_le_sum hj) ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (L + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ the two weighted counts, prefactor included (§4)
  have hHne : ((H : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
    exact ne_of_gt this
  have hfull : S * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j ≤ 54 / 5 * (H : ℝ) ^ 2 := by
    rw [hS, hW, hL]
    exact dyadic_count_weight_geom_le hH0
  have hhead : S * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀ := by
    rw [hS, hW, hL]
    exact dyadic_count_weight_geom_small_le hH0 j₀
  have hFanA : (0 : ℝ) ≤ Fan H * (A : ℝ) := mul_nonneg (hFan0 H) hA0
  have hFtrA : (0 : ℝ) ≤ Ftr H * (A : ℝ) := mul_nonneg (hFtr0 H) hA0
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup_gk K χ M H n) ^ 2
      ≤ S * ∑ j ∈ Finset.range (L + 1),
          (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ S * (Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j
          + Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hS0
    _ = Fan H * (A : ℝ) * (S * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j)
          + Ftr H * (A : ℝ) * (S * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ Fan H * (A : ℝ) * (54 / 5 * (H : ℝ) ^ 2)
          + Ftr H * (A : ℝ) * (9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hFanA
        have h2 := mul_le_mul_of_nonneg_left hhead hFtrA
        linarith
    _ = m4BclGraded j₀ Fan Ftr H * (H : ℝ) ^ 2 * (A : ℝ) := by
        unfold m4BclGraded m4Cmax
        rw [← hL]
        field_simp

/-- **THE GRADED DYADIC ROW DATUM AT THE LEVER** — `M4ChiDyadicRowMeanSq` (:1026). -/
def M4ChiDyadicRowMeanSq_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, ∀ s ≤ H,
      1 / ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)
          * (∫ y in ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)..(2
                * ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)),
              ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                  * shortSum (doorChiCoeff_gk K χ M)
                      (seamS0 (2 * (doorLadder R.x H (i + 1) + s))
                        ((doorLadder R.x H (i + 1) + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
        ≤ MS j H

/-- **THE SHIFTED BRIDGE AT THE LEVER** — `m4_chiShiftBlock_of_dyadicRow` (:1042). -/
theorem m4_chiShiftBlock_of_dyadicRow_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    (hrow : M4ChiDyadicRowMeanSq_gk K R M k MS) :
    M4ChiShiftBlockMeanSq_gk K R M k (fun j H => 2 * MS j H) := by
  intro H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  have hstepd := doorLadder_step_le hxH i
  have hfloor := doorLadder_floor hxH (i + 1)
  have h2j : 2 ^ j ≤ H := by
    calc 2 ^ j ≤ 2 ^ Nat.log 2 H := Nat.pow_le_pow_right (by norm_num) hjL
      _ ≤ H := Nat.pow_log_le_self 2 hH0.ne'
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAB : A + s ≤ B + s := by omega
  have hXpos : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by
    have : 0 < A + s := by omega
    exact_mod_cast this
  have hBfit : (((B + s : ℕ)) : ℝ) + ((2 ^ j : ℕ) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s + 2 ^ j ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_gk K χ M m = 0 :=
    hcov_of_seamS0 (doorChiCoeff_gk K χ M) (A := A + s) (B := B + s) (N := 2 * (A + s))
      (H := 2 ^ j) le_rfl (by omega)
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_gk K χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hladder := sum_Ioc_absWindowSum_sq_div_le (doorChiCoeff_gk K χ M)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (X := (((A + s : ℕ)) : ℝ)) (MS := MS j H) hh0 hAB hXpos le_rfl hBfit hcov hMSrow
  -- ⟦the grade is nonnegative, because the harmonic sum is⟧
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H :=
    le_trans (Finset.sum_nonneg fun n _ => by positivity) hladder
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_gk K χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_gk K χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hladder (Nat.cast_nonneg _)
  have hBs : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : B + s ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by
    refine le_trans hex ?_
    have := mul_le_mul_of_nonneg_right hBs hP0
    calc (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        ≤ 2 * (A : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) := this
      _ = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by ring
  simpa only [absWindowSum_doorChiCoeff_zero_gk K] using hfinal

/-- **THE χ-BLOCK STEP AT THE LEVER** — `m4_chiBlockMeanSq_of_dyadicRow` (:1134). -/
theorem m4_chiBlockMeanSq_of_dyadicRow_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ} (j₀ : ℕ)
    (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H)
    (htr : ∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H)
    (hrow : M4ChiDyadicRowMeanSq_gk K R M k MS) :
    M4ChiBlockMeanSq_gk K R M k
      (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  refine m4_chiBlockMeanSq_of_shiftBlock_gk K (F := fun j H => 2 * MS j H) j₀ ?_ ?_ ?_ ?_
    (m4_chiShiftBlock_of_dyadicRow_gk K hrow)
  · intro H; have := hMSan0 H; linarith
  · intro H; have := hMStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro j H hj; have := htr j H hj; linarith

/-- **THE CLOSE AT THE GRADED DYADIC ROW DATUM, AT THE LEVER** —
`m4_wave_closed_of_dyadicRow` (:1181). -/
theorem m4_wave_closed_of_dyadicRow_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (j₀ M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded j₀ (fun H => 2 * MSan H)
                      (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiDyadicRowMeanSq_gk K R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
                  ≤ m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                      * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS MSan MStr j₀ M k hgates hMSan0 hMStr0 hBraw0
    han htr hdrift hdel hrest hrow hnoncop => ?_⟩
  refine hR δ Braw (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) M k hgates
    (fun H => m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith))
    hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_dyadicRow_gk K j₀ hMSan0 hMStr0 han htr hrow) hnoncop

/-- **THE CLOSE AT THE GRADED DYADIC ROW DATUM, SPLIT, AT THE LEVER** —
`m4_wave_closed_of_dyadicRow_split` (:1238). -/
theorem m4_wave_closed_of_dyadicRow_split_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (j₀ M k : ℕ),
            M4DoorGates_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded j₀ (fun H => 2 * MSan H)
                      (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → Real.sqrt (Braw H) ≤ δ₀ / 2) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ δ₀ / 2) →
            M4ChiDyadicRowMeanSq_gk K R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_gk K M) H n q r) ^ 2
                  ≤ m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                      * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi_split_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS MSan MStr j₀ M k hgates hMSan0 hMStr0 hBraw0
    han htr hdrift hdel hrest hrow hnoncop => ?_⟩
  refine hR δ Braw (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) M k hgates
    (fun H => m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith))
    hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_dyadicRow_gk K j₀ hMSan0 hMStr0 han htr hrow) hnoncop

end Salt.MR

end

-- #audit (temporary)
