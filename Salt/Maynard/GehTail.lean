/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehTypeI
import Salt.Brun.CongruenceCounting

/-!
# The GEH door — the Type-I₁ TAIL bound (smooth-AP equidistribution)

Design freeze: `docs/exploration/s2-b3-design.md`; boundary recon adjudicated
`docs/exploration/pilot.md` (2026-07-17 ~12:50).  The `GehTypeI` executor landed
the tail *subtraction interface* (`vP1tail x n = vP1 (dtrunc x) n`,
`vP1_eq_tail_add_mid`) but flagged the tail *bound* as C-tier: the tail is
long-supported (the truncation is on the divisor `d < x^{1/8000}`, not on `n`),
so the crude ℓ¹ mass bound blows up and the per-`q` saving needs genuine smooth
arithmetic-progression equidistribution.  This file discharges

* `tail_obligation_vP1 : PieceObligationU (3999/4000) (fun x n => vP1tail x n)`.

## The route (the flagged primitives, now assembled)

The Type-I₁ tail weight is `vP1 D n = ∑_{d ∣ n, d ≤ D} μ(d) log(n/d)`.  Split it
into single-divisor pieces `g_d n = μ(d) log(n/d) · 1_{d ∣ n}` (`vP1tail_eq_sum`);
by subadditivity (`seqDiscrepancy_sum_le`) the summed discrepancy is `≤ ∑_{d ≤ D}
seqDiscrepancy (g_d)`.  For a *fixed* `d`:

* **`(d, q) > 1`** — every multiple of `d` shares the factor `gcd(d,q) > 1` with
  `q`, so it lies in no reduced residue class and is not coprime to `q`; both the
  residue sum and the coprime mean vanish, so `seqDiscrepancy (g_d) y q = 0`.
* **`(d, q) = 1`** — reindex `n = d·m` (`single_div_residue_eq`): the residue
  class `n ≡ a (q), d ∣ n` becomes `m` with `(d m) ≡ a (q)`, a single residue
  class `s(a)` mod `q` (the twisted map `s ↦ d s % q` is a bijection of
  `range q`, `twisted_fiber_card`).  The coprime mean is the average of the
  `φ(q)` reduced-class sums (`coprimeMeanSum_eq_sum_residues`), so the deviation
  is `≤ max` pairwise gap `|T_s − T_{s'}|`.  Abel summation over the increasing
  log weight (`abel_log_bound`) turns the per-class count error `O(1)`
  (`congCount_bound`) into `≤ 4 log y`.

Summing `4 log y` over `d ≤ dtrunc x` and `q ≤ x^θ/(log x)^B` gives
`4 · dtrunc x · Q · log x = x^{1/8000 + θ} · polylog = x^{7999/8000} · polylog`,
closed by the landed `power_log_absorb` at `θ' = 7999/8000 < 1`.  Every constant
is fixed OUTSIDE the `∀ x` (III.4).

## The Type-I₂ tail (`vP2tail`) is NOT here — see the executor report

`vP2tail x n = vP2 (dtrunc x) (cbrt x) n` truncates the *outer* factor at
`d < x^{1/8000}` but keeps the *inner* smooth factor at `c ≤ cbrt x = x^{1/3}`.
Its inner weight `L_V(m) = ∑_{c ∣ m, c ≤ cbrt x} Λ(c)` does NOT have bounded total
variation (it is `~ M log V`, not `log M`), so the Abel route above does not
apply.  Its residue-class discrepancy reduces (character-sum viewpoint) to
`∑_{c ≤ x^{1/3}} Λ(c) χ(c)`, whose cancellation is Siegel–Walfisz strength, and at
`q ≤ x^{3999/4000} ≫ √(x^{1/3})` even that exceeds the large sieve.  Elementary
counting gives only `~ x^{1/3}` per `(d,q)`, i.e. total `x^{θ + 1/8000 + 1/3} ≫ x`.
Corroborating structural evidence: there is no `vP2mid` / `vP2_eq_tail_add_mid`
split (only `vP1` has one).  `tail_obligation_vP2` is therefore FLAGGED, not
proven here: it needs the SW/GEH supplier, same as the mid block.
-/

open Finset ArithmeticFunction

open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## Finset subadditivity of `seqDiscrepancy` -/

/-- **Subadditivity over a `Finset`.**  The sequence discrepancy of a finite sum
of weights is at most the sum of the discrepancies.  Induction on `s` from the
binary `seqDiscrepancy_add_le` and `seqDiscrepancy_const_zero`. -/
theorem seqDiscrepancy_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (y q : ℕ) :
    seqDiscrepancy (fun n => ∑ i ∈ s, f i n) y q ≤ ∑ i ∈ s, seqDiscrepancy (f i) y q := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [seqDiscrepancy_const_zero]
  | @insert a s ha ih =>
    have hfun : (fun n => ∑ i ∈ insert a s, f i n)
        = (fun n => f a n + (fun n => ∑ i ∈ s, f i n) n) := by
      funext n; rw [Finset.sum_insert ha]
    rw [hfun, Finset.sum_insert ha]
    refine (seqDiscrepancy_add_le (f a) (fun n => ∑ i ∈ s, f i n) y q).trans ?_
    linarith [ih]

/-! ## The twisted residue fiber has a single element -/

/-- **The twisted map `s ↦ d s % q` is a bijection of `range q`.**  For `d`
coprime to `q ≥ 1` and any target `a < q`, exactly one residue `s < q` has
`d s % q = a` — injectivity is coprime cancellation, surjectivity is finiteness.
This is the fact that makes the single-divisor residue class a genuine residue
class mod `q`. -/
theorem twisted_fiber_card {d q : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime d q)
    (a : ℕ) (ha : a < q) :
    ((Finset.range q).filter (fun s => d * s % q = a)).card = 1 := by
  have hqpos : 0 < q := hq
  have hmaps : Set.MapsTo (fun s => d * s % q) (↑(Finset.range q)) (↑(Finset.range q)) := by
    intro s _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ hqpos
  have hinj : Set.InjOn (fun s => d * s % q) (↑(Finset.range q)) := by
    intro s hs t ht hst
    simp only [Finset.coe_range, Set.mem_Iio] at hs ht
    simp only at hst
    have hmod : d * s ≡ d * t [MOD q] := hst
    have hst' : s ≡ t [MOD q] := Nat.ModEq.cancel_left_of_coprime hcop.symm hmod
    have := hst'
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at this
  have hsurj : Set.SurjOn (fun s => d * s % q) (↑(Finset.range q)) (↑(Finset.range q)) :=
    Finset.surjOn_of_injOn_of_card_le _ hmaps hinj (le_refl _)
  have hamem : a ∈ (↑(Finset.range q) : Set ℕ) := by
    simp only [Finset.coe_range, Set.mem_Iio]; exact ha
  obtain ⟨s, hs, hsa⟩ := hsurj hamem
  simp only [Finset.coe_range, Set.mem_Iio] at hs
  rw [Finset.card_eq_one]
  refine ⟨s, ?_⟩
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  have hsa' : d * s % q = a := hsa
  constructor
  · rintro ⟨ht, hta⟩
    have hkey : d * t % q = d * s % q := by rw [hta, hsa']
    exact hinj (by simp only [Finset.coe_range, Set.mem_Iio]; exact ht)
      (by simp only [Finset.coe_range, Set.mem_Iio]; exact hs) hkey
  · rintro rfl
    exact ⟨hs, hsa'⟩

/-! ## The twisted count and its per-class error -/

/-- The mod identity `d·(n % q) % q = d·n % q` (both equal `(d % q)·(n % q) % q`). -/
theorem mul_mod_mod_eq (d q n : ℕ) : d * (n % q) % q = d * n % q := by
  rw [Nat.mul_mod d (n % q) q, Nat.mod_mod_of_dvd n (dvd_refl q), ← Nat.mul_mod d n q]

/-- The range-`j` twisted count equals `congCount` at `j - 1`: the `i = 0` term is
dropped because `d·0 % q = 0 ≠ a`, and `n % q ∈ S_a ↔ d·n % q = a`. -/
theorem range_twisted_card_eq {d q : ℕ} (hq : 0 < q) {a : ℕ} (ha0 : a ≠ 0) (j : ℕ) :
    ((Finset.range j).filter (fun i => d * i % q = a)).card
      = congCount q ((Finset.range q).filter (fun s => d * s % q = a)) (j - 1) := by
  have hpred : ∀ n, (n % q ∈ (Finset.range q).filter (fun s => d * s % q = a))
      ↔ d * n % q = a := by
    intro n
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h⟩; rw [← h, mul_mod_mod_eq]
    · intro h; exact ⟨Nat.mod_lt _ hq, by rw [mul_mod_mod_eq]; exact h⟩
  unfold congCount
  have hcong : ((Finset.Icc 1 (j - 1)).filter
        (fun n => n % q ∈ (Finset.range q).filter (fun s => d * s % q = a)))
      = (Finset.Icc 1 (j - 1)).filter (fun n => d * n % q = a) := by
    apply Finset.filter_congr; intro n _; simp only [hpred]
  rw [hcong]
  apply Finset.card_bij (fun n _ => n)
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hne : n ≠ 0 := by rintro rfl; simp at hn; omega
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  · intro a1 _ a2 _ h; exact h
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    refine ⟨n, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hn.2⟩

/-- **The per-class count error.**  For `d` coprime to `q ≥ 1` and `a < q`, `a ≠ 0`,
the range-`j` twisted count is within `1` of `(j-1 : ℕ)/q` (the ℕ-subtraction cast,
so the centre is shared across residues and cancels in the pairwise difference). -/
theorem range_twisted_count_error {d q : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime d q)
    {a : ℕ} (ha : a < q) (ha0 : a ≠ 0) (j : ℕ) :
    |(((Finset.range j).filter (fun i => d * i % q = a)).card : ℝ)
        - ((j - 1 : ℕ) : ℝ) / q| ≤ 1 := by
  have hqpos : 0 < q := hq
  set S := (Finset.range q).filter (fun s => d * s % q = a) with hS
  have hcard : (S ∩ Finset.range q).card = 1 := by
    have hsub : S ∩ Finset.range q = S := by
      rw [Finset.inter_eq_left]; exact Finset.filter_subset _ _
    rw [hsub, hS]; exact twisted_fiber_card hq hcop a ha
  have hbd := congCount_bound q S hqpos (j - 1)
  rw [hcard] at hbd
  rw [range_twisted_card_eq hqpos ha0 j]
  simpa using hbd

/-! ## Abel summation over the log weight -/

/-- **Abel summation bound.**  If the partial sums of `u` are bounded by `2` at
every cutoff, then the log-weighted sum over `[0, M]` is `≤ 4 log M`.  Summation
by parts (`Finset.sum_range_by_parts`): the boundary term is `log M · G(M+1)` and
the telescoping `∑ (log(i+1) − log i) = log M` absorbs the interior. -/
theorem abel_log_bound (u : ℕ → ℝ) (M : ℕ)
    (hpart : ∀ j, |∑ m ∈ Finset.range j, u m| ≤ 2) :
    |∑ m ∈ Finset.range (M + 1), Real.log m * u m| ≤ 4 * Real.log M := by
  have hlognn : ∀ k : ℕ, (0 : ℝ) ≤ Real.log k := by
    intro k
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hmono : ∀ i : ℕ, (0 : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ) := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · have : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.le_succ i)
      linarith
  have hby := Finset.sum_range_by_parts (fun i => Real.log (i : ℝ)) u (M + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hby
  rw [hby]
  set G : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, u i with hG
  have htele : (∑ i ∈ Finset.range M, (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)))
      = Real.log (M : ℝ) := by
    rw [Finset.sum_range_sub (fun i => Real.log (i : ℝ)) M]
    simp
  calc |Real.log (M : ℝ) * G (M + 1)
          - ∑ i ∈ Finset.range M,
              (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) * G (i + 1)|
      ≤ |Real.log (M : ℝ) * G (M + 1)|
          + |∑ i ∈ Finset.range M,
              (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) * G (i + 1)| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ Real.log (M : ℝ) * 2 + Real.log (M : ℝ) * 2 := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (hlognn M)]
          exact mul_le_mul_of_nonneg_left (hpart (M + 1)) (hlognn M)
        · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ i ∈ Finset.range M,
                  |(Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) * G (i + 1)|
              ≤ ∑ i ∈ Finset.range M,
                  (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) * 2 := by
                apply Finset.sum_le_sum
                intro i _
                rw [abs_mul, abs_of_nonneg (hmono i)]
                exact mul_le_mul_of_nonneg_left (hpart (i + 1)) (hmono i)
            _ = (∑ i ∈ Finset.range M,
                  (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ))) * 2 := by
                rw [Finset.sum_mul]
            _ = Real.log (M : ℝ) * 2 := by rw [htele]
    _ = 4 * Real.log (M : ℝ) := by ring

/-! ## The single-divisor residue reindex `n = d·m` -/

/-- **The single-divisor residue sum, reindexed.**  For `d ≥ 1`, the residue-class
sum of the single-divisor weight `μ(d) log(n/d) · 1_{d ∣ n}` over `n ≡ a (q)` in
`[1, y]` equals `μ(d)` times the log-weighted twisted sum over `m ∈ [0, ⌊y/d⌋]`
(substitute `n = d m`, so `d ∣ n` is automatic, `n/d = m`, `n ≡ a (q)` becomes
`d m ≡ a (q)`, and the `m = 0` term vanishes as `log 0 = 0`). -/
theorem single_div_residueSum {d : ℕ} (hd : 1 ≤ d) (q y a : ℕ) :
    (∑ n ∈ Finset.Icc 1 y, if n % q = a then
        (if d ∣ n then (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) else 0) else 0)
      = (μ d : ℝ) * ∑ m ∈ Finset.range (y / d + 1),
          Real.log (m : ℝ) * (if d * m % q = a then (1 : ℝ) else 0) := by
  have hdpos : 0 < d := hd
  set M := y / d with hM
  -- combine the two `if`s and drop to a filter
  have hstep1 : (∑ n ∈ Finset.Icc 1 y, if n % q = a then
        (if d ∣ n then (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) else 0) else 0)
      = ∑ n ∈ (Finset.Icc 1 y).filter (fun n => d ∣ n ∧ n % q = a),
          (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h1 : n % q = a <;> by_cases h2 : d ∣ n <;> simp [h1, h2]
  rw [hstep1]
  -- reindex n = d·m
  have hbij : ∑ n ∈ (Finset.Icc 1 y).filter (fun n => d ∣ n ∧ n % q = a),
        (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ)
      = ∑ m ∈ (Finset.Icc 1 M).filter (fun m => d * m % q = a),
          (μ d : ℝ) * Real.log (m : ℝ) := by
    apply Finset.sum_bij' (fun n _ => n / d) (fun m _ => d * m)
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hn2⟩, hdvd, hmod⟩ := hn
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Nat.one_le_div_iff hdpos |>.mpr (Nat.le_of_dvd (by omega) hdvd)
      · exact hM ▸ Nat.div_le_div_right hn2
      · rw [Nat.mul_div_cancel' hdvd]; exact hmod
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hm2⟩, hmod⟩ := hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.mul_pos hdpos (by omega), ?_⟩, ⟨m, rfl⟩, hmod⟩
      calc d * m ≤ d * M := Nat.mul_le_mul_left d hm2
        _ ≤ y := by rw [hM]; exact Nat.mul_div_le y d
    · intro n hn
      rw [Finset.mem_filter] at hn
      rw [Nat.mul_div_cancel' hn.2.1]
    · intro m _
      rw [Nat.mul_div_cancel_left m hdpos]
    · intro n _
      rfl
  rw [hbij, ← Finset.mul_sum, Finset.sum_filter]
  congr 1
  -- extend Icc 1 M to range (M+1); the m = 0 term is log 0 = 0
  have hrange : ∀ K : ℕ, Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
    intro K
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc, Nat.lt_succ_iff]
    omega
  rw [hrange M, Finset.sum_insert (by simp)]
  have hzero : Real.log ((0 : ℕ) : ℝ) * (if d * 0 % q = a then (1 : ℝ) else 0) = 0 := by
    simp
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : d * m % q = a <;> simp [h]

/-! ## The pairwise log-residue gap -/

/-- **The pairwise log-residue gap.**  For `d` coprime to `q ≥ 1` and nonzero
targets `a, b < q`, the log-weighted twisted sums over `[0, M]` differ by at most
`4 log M`.  Abel summation (`abel_log_bound`) over the difference indicator, whose
partial sums are bounded by `2` (`range_twisted_count_error`: each twisted count is
within `1` of the shared centre `(j-1)/q`). -/
theorem twisted_log_pairwise_le {d q : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime d q)
    {a b : ℕ} (ha : a < q) (ha0 : a ≠ 0) (hb : b < q) (hb0 : b ≠ 0) (M : ℕ) :
    |(∑ m ∈ Finset.range (M + 1), Real.log (m : ℝ) * (if d * m % q = a then (1 : ℝ) else 0))
        - ∑ m ∈ Finset.range (M + 1),
            Real.log (m : ℝ) * (if d * m % q = b then (1 : ℝ) else 0)|
      ≤ 4 * Real.log M := by
  have hcombine : (∑ m ∈ Finset.range (M + 1),
          Real.log (m : ℝ) * (if d * m % q = a then (1 : ℝ) else 0))
        - ∑ m ∈ Finset.range (M + 1),
            Real.log (m : ℝ) * (if d * m % q = b then (1 : ℝ) else 0)
      = ∑ m ∈ Finset.range (M + 1), Real.log (m : ℝ) *
          ((if d * m % q = a then (1 : ℝ) else 0)
            - (if d * m % q = b then (1 : ℝ) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [hcombine]
  apply abel_log_bound
  intro j
  have hsplit : (∑ m ∈ Finset.range j,
        ((if d * m % q = a then (1 : ℝ) else 0) - (if d * m % q = b then (1 : ℝ) else 0)))
      = (((Finset.range j).filter (fun m => d * m % q = a)).card : ℝ)
        - (((Finset.range j).filter (fun m => d * m % q = b)).card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  rw [hsplit]
  have hea := range_twisted_count_error hq hcop ha ha0 j
  have heb := range_twisted_count_error hq hcop hb hb0 j
  refine (abs_sub_le _ (((j - 1 : ℕ) : ℝ) / q) _).trans ?_
  have heb' : |((j - 1 : ℕ) : ℝ) / q
      - (((Finset.range j).filter (fun m => d * m % q = b)).card : ℝ)| ≤ 1 := by
    rw [abs_sub_comm]; exact heb
  linarith [hea, heb']

/-! ## The single-divisor discrepancy bound -/

/-- **The single-divisor discrepancy bound.**  For `d, q ≥ 1`, the sequence
discrepancy of the single-divisor weight `g_d n = μ(d) log(n/d) · 1_{d ∣ n}` is
`≤ 4 log y`.  When `(d, q) > 1` every multiple of `d` shares `gcd(d,q)` with `q`,
so both the residue sum and the coprime mean vanish; when `(d, q) = 1` the reindex
`n = d m` turns each reduced-residue sum into `μ(d)` times a log-weighted twisted
sum, the coprime mean into their average, and the deviation is bounded by the
pairwise gap `4 log ⌊y/d⌋ ≤ 4 log y`. -/
theorem single_div_disc_le {d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) (y : ℕ) :
    seqDiscrepancy
        (fun n => if d ∣ n then (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) else 0) y q
      ≤ 4 * Real.log y := by
  have hq0 : q ≠ 0 := by omega
  have hqpos : 0 < q := hq
  have hlogy : (0 : ℝ) ≤ Real.log y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · subst h; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  set f : ℕ → ℝ :=
    fun n => if d ∣ n then (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) else 0 with hf
  rw [seqDiscrepancy_eq f y q hq0]
  apply Finset.sup'_le
  intro a ha
  rw [Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨haq, hacop⟩ := ha
  by_cases hcop : Nat.Coprime d q
  · -- (d, q) = 1
    by_cases hq2 : 2 ≤ q
    · have hb0 : ∀ b : ℕ, Nat.Coprime b q → b ≠ 0 := by
        intro b hbc; rintro rfl; rw [Nat.coprime_zero_left] at hbc; omega
      have ha0 : a ≠ 0 := hb0 a hacop
      set M := y / d with hMdef
      set RS := (Finset.range q).filter (fun b => Nat.Coprime b q) with hRS
      set T : ℕ → ℝ := fun c => ∑ m ∈ Finset.range (M + 1),
        Real.log (m : ℝ) * (if d * m % q = c then (1 : ℝ) else 0) with hT
      have hφcard : RS.card = q.totient := by
        rw [hRS, Nat.totient_eq_card_coprime]
        congr 1
        exact Finset.filter_congr (fun b _ => by rw [Nat.coprime_comm])
      have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqpos
      have hRa : (∑ n ∈ Finset.Icc 1 y, if n % q = a then f n else 0) = (μ d : ℝ) * T a :=
        single_div_residueSum hd q y a
      have hMean : (∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0)
          = (μ d : ℝ) * ∑ b ∈ RS, T b := by
        rw [coprimeMeanSum_eq_sum_residues f y q hqpos, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => single_div_residueSum hd q y b)
      have hmu : |(μ d : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      rw [hRa, hMean]
      have hfactor : (μ d : ℝ) * T a - (μ d : ℝ) * (∑ b ∈ RS, T b) / (q.totient : ℝ)
          = (μ d : ℝ) * (T a - (∑ b ∈ RS, T b) / (q.totient : ℝ)) := by ring
      rw [hfactor, abs_mul]
      refine le_trans (mul_le_of_le_one_left (abs_nonneg _) hmu) ?_
      have hXeq : T a - (∑ b ∈ RS, T b) / (q.totient : ℝ)
          = (∑ b ∈ RS, (T a - T b)) / (q.totient : ℝ) := by
        have hne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφpos
        rw [Finset.sum_sub_distrib, Finset.sum_const, hφcard, nsmul_eq_mul]
        field_simp
      have hMley : Real.log (M : ℝ) ≤ Real.log (y : ℝ) := by
        rcases Nat.eq_zero_or_pos M with hM0 | hMpos
        · rw [hM0]; simpa using hlogy
        · exact Real.log_le_log (by exact_mod_cast hMpos)
            (by exact_mod_cast Nat.div_le_self y d)
      rw [hXeq, abs_div, abs_of_pos hφpos, div_le_iff₀ hφpos]
      calc |∑ b ∈ RS, (T a - T b)|
          ≤ ∑ b ∈ RS, |T a - T b| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b ∈ RS, 4 * Real.log (M : ℝ) := by
            apply Finset.sum_le_sum
            intro b hb
            rw [hRS, Finset.mem_filter, Finset.mem_range] at hb
            exact twisted_log_pairwise_le hq hcop haq ha0 hb.1 (hb0 b hb.2) M
        _ = (RS.card : ℝ) * (4 * Real.log (M : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 4 * Real.log (y : ℝ) * (q.totient : ℝ) := by
            rw [hφcard]
            have : (q.totient : ℝ) * (4 * Real.log (M : ℝ))
                ≤ (q.totient : ℝ) * (4 * Real.log (y : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith [hMley]) (le_of_lt hφpos)
            linarith
    · -- q = 1: the single reduced residue is `0`, so `R_a = Mean` and the deviation is `0`
      have hq1 : q = 1 := by omega
      subst hq1
      have ha00 : a = 0 := by omega
      subst ha00
      have hR : (∑ n ∈ Finset.Icc 1 y, if n % 1 = 0 then f n else 0)
          = ∑ n ∈ Finset.Icc 1 y, f n :=
        Finset.sum_congr rfl (fun n _ => by simp [Nat.mod_one])
      have hM1 : (∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n 1 then f n else 0)
          = ∑ n ∈ Finset.Icc 1 y, f n :=
        Finset.sum_congr rfl (fun n _ => by simp)
      rw [hR, hM1]
      simp only [Nat.totient_one, Nat.cast_one, div_one, sub_self, abs_zero]
      linarith [hlogy]
  · -- (d, q) > 1: both the residue sum and the coprime mean vanish
    have hgpos : 1 < Nat.gcd d q := by
      have hg0 : Nat.gcd d q ≠ 0 := by
        have : 0 < Nat.gcd d q := Nat.gcd_pos_iff.mpr (Or.inl hd)
        omega
      have hg1 : Nat.gcd d q ≠ 1 := hcop
      omega
    have hRa : (∑ n ∈ Finset.Icc 1 y, if n % q = a then f n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n _
      by_cases h1 : n % q = a
      · rw [if_pos h1]
        by_cases h2 : d ∣ n
        · exfalso
          have hgn : Nat.gcd d q ∣ n := (Nat.gcd_dvd_left d q).trans h2
          have hgq : Nat.gcd d q ∣ q := Nat.gcd_dvd_right d q
          have hga : Nat.gcd d q ∣ a := h1 ▸ (Nat.dvd_mod_iff hgq).mpr hgn
          have : Nat.gcd d q ∣ 1 := hacop ▸ Nat.dvd_gcd hga hgq
          have := Nat.le_of_dvd (by norm_num) this; omega
        · rw [hf]; exact if_neg h2
      · exact if_neg h1
    have hMean : (∑ n ∈ Finset.Icc 1 y, if Nat.Coprime n q then f n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n _
      by_cases h1 : Nat.Coprime n q
      · rw [if_pos h1]
        by_cases h2 : d ∣ n
        · exfalso
          have hgn : Nat.gcd d q ∣ n := (Nat.gcd_dvd_left d q).trans h2
          have hgq : Nat.gcd d q ∣ q := Nat.gcd_dvd_right d q
          have : Nat.gcd d q ∣ 1 := h1 ▸ Nat.dvd_gcd hgn hgq
          have := Nat.le_of_dvd (by norm_num) this; omega
        · rw [hf]; exact if_neg h2
      · exact if_neg h1
    rw [hRa, hMean]
    simp only [zero_div, sub_zero, abs_zero]
    linarith [hlogy]

/-! ## The tail obligation for `vP1tail` -/

/-- **`vP1tail` as a sum of single-divisor weights.**  The Type-I₁ tail
`vP1 (dtrunc x) n = ∑_{d ∣ n, d ≤ dtrunc x} μ(d) log(n/d)` reindexes as a sum over
`d ∈ [1, dtrunc x]` of the single-divisor weights `μ(d) log(n/d) · 1_{d ∣ n}`
(the `n = 0` term vanishes: `log 0 = 0`). -/
theorem vP1tail_eq_sum (x : ℕ) :
    (fun n => vP1tail x n)
      = fun n => ∑ d ∈ Finset.Icc 1 (dtrunc x),
          (if d ∣ n then (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) else 0) := by
  funext n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [vP1tail, vP1]
    simp only [Nat.divisors_zero, Finset.filter_empty, Finset.sum_empty]
    symm
    exact Finset.sum_eq_zero (fun d _ => by simp)
  · rw [vP1tail, vP1, ← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdvd, _⟩, hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hpos, hle⟩, hdvd⟩
    · rintro ⟨⟨_, hle⟩, hdvd⟩
      exact ⟨⟨hdvd, by omega⟩, hle⟩

/-- **The Type-I₁ TAIL obligation** (the smooth-AP equidistribution build).  The
short-factor tail `vP1tail x n = vP1 (dtrunc x) n` satisfies the `y`-uniform piece
obligation at `θ = 3999/4000`.  Route: decompose into `dtrunc x` single-divisor
weights (`vP1tail_eq_sum`), each with sequence discrepancy `≤ 4 log y ≤ 4 log x`
(`single_div_disc_le`, via `subadditivity`); summing over `q ≤ x^θ` and
`d ≤ dtrunc x ≤ x^{1/8000}` gives `4 · x^θ · x^{1/8000} · log x = 4 x^{7999/8000} log x`,
`≪ x/(log x)^A` by `power_log_absorb` (`θ' = 7999/8000 < 1`, `B = 0`, `C = 4 Cabs`). -/
theorem tail_obligation_vP1 :
    PieceObligationU (3999 / 4000) (fun x n => vP1tail x n) := by
  intro A hA
  obtain ⟨Cabs, hCabs0, hCabs⟩ := power_log_absorb (θ' := (7999 / 8000 : ℝ)) (by norm_num) hA
  refine ⟨0, 4 * Cabs, le_refl 0, fun x y hx hyx => ?_⟩
  have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hlog0 : (0 : ℝ) ≤ Real.log x := le_of_lt hlogpos
  have hlogyx : Real.log (y : ℝ) ≤ Real.log (x : ℝ) := by
    rcases Nat.eq_zero_or_pos y with h | h
    · rw [h]; simpa using hlog0
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hyx)
  simp only [Real.rpow_zero, div_one]
  set Q := ⌊(x : ℝ) ^ (3999 / 4000 : ℝ)⌋₊ with hQdef
  set D := dtrunc x with hDdef
  have hQx : (Q : ℝ) ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (le_of_lt hxpos) _)
  have hDx : (D : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8000) :=
    Nat.floor_le (Real.rpow_nonneg (le_of_lt hxpos) _)
  -- per q: the tail discrepancy is `≤ D · 4 log x`
  have hperq : ∀ q, 1 ≤ q →
      seqDiscrepancy (fun n => vP1tail x n) y q ≤ (D : ℝ) * (4 * Real.log x) := by
    intro q hq
    calc seqDiscrepancy (fun n => vP1tail x n) y q
        ≤ ∑ d ∈ Finset.Icc 1 D,
            seqDiscrepancy (fun n =>
              if d ∣ n then (μ d : ℝ) * Real.log ((n / d : ℕ) : ℝ) else 0) y q := by
          rw [vP1tail_eq_sum x]
          exact seqDiscrepancy_sum_le (Finset.Icc 1 D) _ y q
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, 4 * Real.log x := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          exact (single_div_disc_le hd.1 hq y).trans (by linarith [hlogyx])
      _ = (D : ℝ) * (4 * Real.log x) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  calc ∑ q ∈ Finset.Icc 1 Q, seqDiscrepancy (fun n => vP1tail x n) y q
      ≤ ∑ _q ∈ Finset.Icc 1 Q, (D : ℝ) * (4 * Real.log x) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [Finset.mem_Icc] at hq
        exact hperq q hq.1
    _ = (Q : ℝ) * ((D : ℝ) * (4 * Real.log x)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = ((Q : ℝ) * (D : ℝ)) * (4 * Real.log x) := by ring
    _ ≤ (x : ℝ) ^ (7999 / 8000 : ℝ) * (4 * Real.log x) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc (Q : ℝ) * (D : ℝ)
            ≤ (x : ℝ) ^ (3999 / 4000 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 8000) :=
              mul_le_mul hQx hDx (Nat.cast_nonneg _)
                (Real.rpow_nonneg (le_of_lt hxpos) _)
          _ = (x : ℝ) ^ (7999 / 8000 : ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
    _ = 4 * ((x : ℝ) ^ (7999 / 8000 : ℝ) * Real.log x) := by ring
    _ ≤ 4 * (Cabs * (x : ℝ) / Real.log x ^ A) :=
        mul_le_mul_of_nonneg_left (hCabs x hx) (by norm_num)
    _ = 4 * Cabs * (x : ℝ) / Real.log x ^ A := by ring
