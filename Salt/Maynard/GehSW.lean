/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehDoor
import Salt.LS.TypeSums
import Salt.SW.Gate

/-!
# The Type-II Siegel–Walfisz supplier for the GEH door (node S2-B3-SW)

Design: `docs/exploration/pilot.md`, the boundary recon (2026-07-17 ~12:50) — the
`SWAt` slot of `GEH_min` (`Salt/Maynard/GehDoor.lean`) for the balanced Type-II
block family `β x m = 1_{Ioc (M x) (2 M x)}(m) · typeIIData (V x) m`.

The recon's **two-range split**, at divisor-exponent `j = 3`:

* **Large `q`** (`q > (log x)^{A+1}`): the *trivial* bound.  The twisted class
  sum has `≤ (2 M x)/q + 1` residue representatives (`ap_count_le`), each of
  weight `≤ log (2 M x)`; the coprime mean is an average of such class sums, so
  the whole discrepancy is `≤ log (2 M x) · ((2 M x + 1)/q + 1)`
  (`seqDiscrepancy_interval_le`).  Because `q > (log x)^{A+1}` and the scale
  obeys `x^{ε₀} ≤ M x ≤ x` (`hMlo`/`hMhi`), the `log`-over-`log^{A+1}` shape is
  *weaker* than `M x / log^A x` — closed with the explicit `Real.log_le_rpow_div`
  growth bound (`log_pow_le_scale`).  This half is **proven here**, uniform in
  `x, r`, with `K = 6 + 2·((A+1)/ε₀)^{A+1}`.

* **Small `q`** (`q ≤ (log x)^{A+1}`): the genuine Siegel–Walfisz content, where
  `typeIIData`'s AP distribution reduces (Möbius/CRT over `gcd(c,q)` of the
  divisor `c > V`) to `Λ`'s distribution, fed by `Salt.SW.siegelWalfisz_holds`.
  That reduction is the flagged floor (a C/D-tier nested-modulus proof); it is
  taken here as the explicit hypothesis `SmallQTypeII M V 3` (**FLAG** — see the
  executor report / `docs/blueprints/flags.md`).  `j = 3` gives headroom for the
  `τ(q)` from the `gcd(c,q)` classes, the `τ(r)` from the `r`-coprimality twist,
  and one factor for the divisor sum over `c`.

The single-scale statement is generic in `M`/`V`; the multi-block family that the
GEH bridge (`Salt/Maynard/GehVaughan.lean`) ultimately consumes is a later node.
-/

open Finset

namespace Salt.Maynard

/-- **Interval AP count.**  The number of `n ∈ (M, 2M]` with `n % q = a` is at
most `(2M+1)/q + 1`: inject into `[0, 2M]` and apply `Nat.count_modEq_card`
(`= (2M+1)/q + Iverson`). -/
private lemma ap_count_le (M q a : ℕ) (hq : 0 < q) (ha : a < q) :
    ((Finset.Ioc M (2 * M)).filter (fun n => n % q = a)).card ≤ (2 * M + 1) / q + 1 := by
  have hsub : (Finset.Ioc M (2 * M)).filter (fun n => n % q = a)
      ⊆ (Finset.range (2 * M + 1)).filter (fun n => n ≡ a [MOD q]) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hn ⊢
    obtain ⟨⟨_, hn2⟩, hmod⟩ := hn
    refine ⟨by omega, ?_⟩
    change n % q = a % q
    rw [hmod, Nat.mod_eq_of_lt ha]
  calc ((Finset.Ioc M (2 * M)).filter (fun n => n % q = a)).card
      ≤ ((Finset.range (2 * M + 1)).filter (fun n => n ≡ a [MOD q])).card :=
        Finset.card_le_card hsub
    _ = Nat.count (fun n => n ≡ a [MOD q]) (2 * M + 1) :=
        (Nat.count_eq_card_filter_range _ _).symm
    _ = (2 * M + 1) / q + (if a % q < (2 * M + 1) % q then 1 else 0) :=
        Nat.count_modEq_card (2 * M + 1) hq a
    _ ≤ (2 * M + 1) / q + 1 := by split_ifs <;> omega

/-- Cast of `ap_count_le` into `ℝ`, with the nat floor relaxed to the real
quotient (`Nat.cast_div_le`). -/
private lemma ap_count_le_real (M q a : ℕ) (hq : 0 < q) (ha : a < q) :
    (((Finset.Ioc M (2 * M)).filter (fun n => n % q = a)).card : ℝ)
      ≤ (2 * (M : ℝ) + 1) / (q : ℝ) + 1 := by
  have h : (((Finset.Ioc M (2 * M)).filter (fun n => n % q = a)).card : ℝ)
      ≤ (((2 * M + 1) / q + 1 : ℕ) : ℝ) := by exact_mod_cast ap_count_le M q a hq ha
  refine h.trans ?_
  have hcd := Nat.cast_div_le (m := 2 * M + 1) (n := q) (α := ℝ)
  push_cast at hcd ⊢
  linarith

/-- **The trivial (large-`q`) discrepancy bound.**  For any weight `f ≥ 0`
bounded by `c` on `Ioc M (2 M)` and vanishing off it, the sequence discrepancy at
modulus `q > 0` is `≤ c · ((2M+1)/q + 1)`: each reduced class sum is
`≤ c · #{AP reps} ≤ c·((2M+1)/q + 1)` (`ap_count_le`), and the coprime mean is
the `φ(q)`-average of those class sums (`sum_fiberwise_of_maps_to`), hence also
`≤` that bound; the discrepancy of two nonnegatives each `≤ B` is `≤ B`. -/
private lemma seqDiscrepancy_interval_le (f : ℕ → ℝ) (x q M : ℕ) (c : ℝ)
    (hq : 0 < q) (hc : 0 ≤ c) (hf0 : ∀ n, 0 ≤ f n)
    (hfle : ∀ n, f n ≤ if n ∈ Finset.Ioc M (2 * M) then c else 0) :
    seqDiscrepancy f x q ≤ c * ((2 * (M : ℝ) + 1) / (q : ℝ) + 1) := by
  set B : ℝ := c * ((2 * (M : ℝ) + 1) / (q : ℝ) + 1) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; apply mul_nonneg hc; positivity
  -- Every reduced class sum is `≤ B`.
  have hclass : ∀ a : ℕ, a < q →
      (∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0) ≤ B := by
    intro a ha
    have hsub2 : ((Finset.Icc 1 x).filter
          (fun n => n % q = a ∧ n ∈ Finset.Ioc M (2 * M)))
        ⊆ (Finset.Ioc M (2 * M)).filter (fun n => n % q = a) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
      exact ⟨hn.2.2, hn.2.1⟩
    have hcard : (((Finset.Icc 1 x).filter
          (fun n => n % q = a ∧ n ∈ Finset.Ioc M (2 * M))).card : ℝ)
        ≤ (2 * (M : ℝ) + 1) / (q : ℝ) + 1 :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub2) (ap_count_le_real M q a hq ha)
    calc (∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0)
        ≤ ∑ n ∈ Finset.Icc 1 x,
            if n % q = a then (if n ∈ Finset.Ioc M (2 * M) then c else 0) else 0 := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          by_cases h : n % q = a
          · rw [if_pos h, if_pos h]; exact hfle n
          · simp [if_neg h]
      _ = ∑ n ∈ Finset.Icc 1 x,
            if (n % q = a ∧ n ∈ Finset.Ioc M (2 * M)) then c else 0 := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          by_cases h1 : n % q = a <;> by_cases h2 : n ∈ Finset.Ioc M (2 * M) <;>
            simp [h1, h2]
      _ = ∑ n ∈ (Finset.Icc 1 x).filter
            (fun n => n % q = a ∧ n ∈ Finset.Ioc M (2 * M)), c :=
          (Finset.sum_filter (fun n => n % q = a ∧ n ∈ Finset.Ioc M (2 * M))
            (fun _ => c)).symm
      _ = (((Finset.Icc 1 x).filter
            (fun n => n % q = a ∧ n ∈ Finset.Ioc M (2 * M))).card : ℝ) * c := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * (M : ℝ) + 1) / (q : ℝ) + 1) * c := mul_le_mul_of_nonneg_right hcard hc
      _ = B := by rw [hBdef]; ring
  -- The coprime mean is the `φ(q)`-average of reduced class sums, hence `≤ B`.
  set t : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q) with htdef
  have hmaps : ∀ n ∈ (Finset.Icc 1 x).filter (fun n => Nat.Coprime n q), n % q ∈ t := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [htdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt n hq, (Salt.BV.coprime_mod_left n q).mp hn.2⟩
  have htcard : (t.card : ℝ) = (q.totient : ℝ) := by
    congr 1
    rw [htdef, Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp only [Finset.mem_filter, Nat.coprime_comm]
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hmeanφ : (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0)
      / (q.totient : ℝ) ≤ B := by
    rw [div_le_iff₀ hφpos, ← htcard, ← Finset.sum_filter,
      ← Finset.sum_fiberwise_of_maps_to hmaps f]
    calc ∑ a ∈ t, ∑ n ∈ ((Finset.Icc 1 x).filter (fun n => Nat.Coprime n q)).filter
            (fun n => n % q = a), f n
        ≤ ∑ _a ∈ t, B := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          have haq : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
          calc ∑ n ∈ ((Finset.Icc 1 x).filter (fun n => Nat.Coprime n q)).filter
                  (fun n => n % q = a), f n
              ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = a), f n :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (by intro n hn; simp only [Finset.mem_filter] at hn ⊢;
                      exact ⟨hn.1.1, hn.2⟩)
                  (fun n _ _ => hf0 n)
            _ = ∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0 :=
                Finset.sum_filter (fun n => n % q = a) f
            _ ≤ B := hclass a haq
      _ = B * (t.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- Discrepancy of two nonnegatives, each `≤ B`, is `≤ B`.
  unfold seqDiscrepancy
  rw [dif_neg hq.ne']
  apply Finset.sup'_le
  intro a ha
  have haq : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hTaB := hclass a haq
  have hTa0 : 0 ≤ ∑ n ∈ Finset.Icc 1 x, if n % q = a then f n else 0 :=
    Finset.sum_nonneg (fun n _ => by split_ifs; exacts [hf0 n, le_refl 0])
  have hMn0 : 0 ≤ (∑ n ∈ Finset.Icc 1 x, if Nat.Coprime n q then f n else 0)
      / (q.totient : ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun n _ => by split_ifs; exacts [hf0 n, le_refl 0]))
      (le_of_lt hφpos)
  rw [abs_le]
  exact ⟨by linarith [hMn0, hmeanφ], by linarith [hTaB, hMn0]⟩

/-- **Polynomial-scale growth.**  If `x^{ε₀} ≤ M` then `(log x)^{A+1} ≤ C · M`
with the explicit `C = ((A+1)/ε₀)^{A+1}`, via `Real.log_le_rpow_div` at exponent
`ε₀/(A+1)`.  The engine that beats the large-`q` `+1` remainder. -/
private lemma log_pow_le_scale {ε₀ : ℝ} (hε₀ : 0 < ε₀) {A : ℝ} (hA : 0 < A)
    (x M : ℕ) (hx : 2 ≤ x) (hMlo : (x : ℝ) ^ ε₀ ≤ (M : ℝ)) :
    Real.log x ^ (A + 1) ≤ ((A + 1) / ε₀) ^ (A + 1) * (M : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (show 1 ≤ x by omega)
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hApos : (0 : ℝ) < A + 1 := by linarith
  have hε₀' : ε₀ ≠ 0 := ne_of_gt hε₀
  have hA1' : A + 1 ≠ 0 := ne_of_gt hApos
  set e : ℝ := ε₀ / (A + 1) with hedef
  have hepos : 0 < e := by rw [hedef]; positivity
  have hlog_le : Real.log x ≤ ((A + 1) / ε₀) * (x : ℝ) ^ e := by
    have h := Real.log_le_rpow_div (le_of_lt hxpos) hepos
    calc Real.log x ≤ (x : ℝ) ^ e / e := h
      _ = ((A + 1) / ε₀) * (x : ℝ) ^ e := by rw [hedef]; field_simp
  have hpow : Real.log x ^ (A + 1) ≤ (((A + 1) / ε₀) * (x : ℝ) ^ e) ^ (A + 1) :=
    Real.rpow_le_rpow hL0 hlog_le (le_of_lt hApos)
  have hexp : (((A + 1) / ε₀) * (x : ℝ) ^ e) ^ (A + 1)
      = ((A + 1) / ε₀) ^ (A + 1) * (x : ℝ) ^ ε₀ := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (le_of_lt hxpos) e)]
    congr 1
    rw [← Real.rpow_mul (le_of_lt hxpos)]
    congr 1
    rw [hedef]; field_simp
  calc Real.log x ^ (A + 1)
      ≤ ((A + 1) / ε₀) ^ (A + 1) * (x : ℝ) ^ ε₀ := hpow.trans_eq hexp
    _ ≤ ((A + 1) / ε₀) ^ (A + 1) * (M : ℝ) := mul_le_mul_of_nonneg_left hMlo (by positivity)

/-- **The small-modulus Type-II obligation** (the flagged Siegel–Walfisz floor).
For `q ≤ (log x)^{A+1}` and under the **polynomial-scale guard** `x^{1/3} ≤ V x`
(the divisor threshold is a genuine power of `x`, not polylog — without it the
block collapses to pure `Λ` and the mod-`q` discrepancy is `Ω`-large, so the
estimate is FALSE; house ruling N-SMALLQ, 2026-07-20), the `r`-twisted
discrepancy of the Type-II block family is `≤ K · τ(qr)^j · M x / (log x)^A`.
Discharged by `siegelWalfisz_holds` through the Möbius/CRT reduction of
`typeIIData` over the divisor `c > V x` (`gcd(a,q)=1 ⟹ gcd(m,q)=1` makes the
reindex a clean `m⁻¹`-bijection); taken here as a hypothesis pending that node
(see the module docstring / `flags.md`). -/
def SmallQTypeII (M V : ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧ ∀ x r q : ℕ,
    2 ≤ x → 0 < r → 0 < q → (q : ℝ) ≤ Real.log x ^ (A + 1) →
    (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (V x : ℝ) →
    seqDiscrepancy (fun n => if Nat.Coprime n r then
        (if n ∈ Finset.Ioc (M x) (2 * M x) then Salt.LS.typeIIData (V x) n else 0)
        else 0) x q
      ≤ K * ((q * r).divisors.card : ℝ) ^ j * (M x : ℝ) / Real.log x ^ A

/-- **The Type-II SW supplier** (single-scale, node S2-B3-SW).  The balanced
Type-II block family `β x m = 1_{Ioc (M x) (2 M x)}(m) · typeIIData (V x) m`
satisfies `GEH_min`'s `SWAt` slot at `j = 3`, given the polynomial-scale window
`x^{ε₀} ≤ M x ≤ x`, the polynomial-scale threshold `hV : x^{1/3} ≤ V x` (fed to
`SmallQTypeII`'s guard — see the N-SMALLQ ruling), and the small-`q` obligation
`SmallQTypeII M V 3`.  The large-`q` half is proven here; the small-`q` half is
the flagged Siegel–Walfisz floor. -/
theorem swAt_typeIIData (M V : ℕ → ℕ) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hMlo : ∀ x : ℕ, 2 ≤ x → (x : ℝ) ^ ε₀ ≤ (M x : ℝ))
    (hMhi : ∀ x : ℕ, 2 ≤ x → (M x : ℝ) ≤ (x : ℝ))
    (hV : ∀ x : ℕ, 2 ≤ x → (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (V x : ℝ))
    (hSmall : SmallQTypeII M V 3) :
    SWAt (fun x m =>
        if m ∈ Finset.Ioc (M x) (2 * M x) then Salt.LS.typeIIData (V x) m else 0) M := by
  refine ⟨3, fun A hA => ?_⟩
  obtain ⟨Ks, hKs0, hKs⟩ := hSmall A hA
  set Kl : ℝ := 6 + 2 * ((A + 1) / ε₀) ^ (A + 1) with hKldef
  have hKl0 : 0 ≤ Kl := by rw [hKldef]; positivity
  refine ⟨max Ks Kl, le_trans hKs0 (le_max_left _ _), fun x r q hx hr hq => ?_⟩
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  set L : ℝ := Real.log x with hLdef
  have hLpos : 0 < L := Real.log_pos hx1
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hLApos : (0 : ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos A
  have hτ1 : (1 : ℝ) ≤ ((q * r).divisors.card : ℝ) ^ (3 : ℕ) := by
    have hqr : q * r ≠ 0 := Nat.mul_ne_zero hq.ne' hr.ne'
    have hpos : 0 < (q * r).divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hqr⟩
    exact one_le_pow₀ (by exact_mod_cast hpos)
  by_cases hsmall : (q : ℝ) ≤ L ^ (A + 1)
  · -- SMALL q: the flagged hypothesis, relaxed `Ks → max Ks Kl`.
    have hb := hKs x r q hx hr hq hsmall (hV x hx)
    rw [← hLdef] at hb
    refine le_trans hb ((div_le_div_iff_of_pos_right hLApos).mpr ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Ks Kl) (by positivity)) (by positivity)
  · -- LARGE q: the trivial bound beats `M x / log^A x`.
    have hqlt : L ^ (A + 1) < (q : ℝ) := not_le.mp hsmall
    have hMloR : (x : ℝ) ^ ε₀ ≤ (M x : ℝ) := hMlo x hx
    have hMhiR : (M x : ℝ) ≤ (x : ℝ) := hMhi x hx
    have hMx1 : (1 : ℝ) ≤ (M x : ℝ) := by
      refine le_trans ?_ hMloR
      calc (1 : ℝ) = (1 : ℝ) ^ ε₀ := (Real.one_rpow ε₀).symm
        _ ≤ (x : ℝ) ^ ε₀ := Real.rpow_le_rpow zero_le_one hx1.le (le_of_lt hε₀)
    set c : ℝ := Real.log (2 * (M x : ℝ)) with hcdef
    have hc0 : 0 ≤ c := by rw [hcdef]; exact Real.log_nonneg (by linarith [hMx1])
    have hxne : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
    have hc2 : c ≤ 2 * L := by
      rw [hcdef]
      have h1 : Real.log (2 * (M x : ℝ)) ≤ Real.log (2 * (x : ℝ)) :=
        Real.log_le_log (by linarith [hMx1]) (by linarith [hMhiR])
      have h2 : Real.log (2 * (x : ℝ)) = Real.log 2 + L := by
        rw [Real.log_mul (by norm_num) hxne, ← hLdef]
      have h3 : Real.log 2 ≤ L := by
        rw [hLdef]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast (show (2 : ℕ) ≤ x by omega))
      linarith
    have hP1 : L ^ (A + 1) = L ^ A * L := by rw [Real.rpow_add hLpos, Real.rpow_one]
    have hP1pos : (0 : ℝ) < L ^ (A + 1) := Real.rpow_pos_of_pos hLpos _
    have hgrow : L ^ (A + 1) ≤ ((A + 1) / ε₀) ^ (A + 1) * (M x : ℝ) := by
      have h := log_pow_le_scale hε₀ hA x (M x) hx hMloR
      rw [← hLdef] at h; exact h
    have hgen := seqDiscrepancy_interval_le
      (fun n => if Nat.Coprime n r then
        (if n ∈ Finset.Ioc (M x) (2 * M x) then Salt.LS.typeIIData (V x) n else 0) else 0)
      x q (M x) c hq hc0
      (fun n => by
        split_ifs <;> first | exact Salt.LS.typeIIData_nonneg _ _ | exact le_refl 0)
      (fun n => by
        split_ifs with hcop hn hn
        · refine le_trans (Salt.LS.typeIIData_le_log (V x) n) ?_
          have hn' := Finset.mem_Ioc.mp hn
          have hub : (n : ℝ) ≤ 2 * (M x : ℝ) := by
            have : (n : ℝ) ≤ ((2 * M x : ℕ) : ℝ) := by exact_mod_cast hn'.2
            push_cast at this; linarith
          rw [hcdef]; exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hub
        · exact le_refl 0
        · exact hc0
        · exact le_refl 0)
    -- The large-`q` arithmetic: `c·((2Mx+1)/q + 1) ≤ Kl·(M x)/L^A`.
    have hnum0 : 0 ≤ c * (2 * (M x : ℝ) + 1) := mul_nonneg hc0 (by positivity)
    have hT1 : c * ((2 * (M x : ℝ) + 1) / (q : ℝ)) ≤ 6 * (M x : ℝ) / L ^ A := by
      rw [← mul_div_assoc]
      have hT1a : c * (2 * (M x : ℝ) + 1) / (q : ℝ)
          ≤ c * (2 * (M x : ℝ) + 1) / (L ^ A * L) := by
        rw [← hP1]; exact div_le_div_of_nonneg_left hnum0 hP1pos (le_of_lt hqlt)
      have hcMx : c * (2 * (M x : ℝ) + 1) ≤ 6 * L * (M x : ℝ) := by
        have hh : 2 * (M x : ℝ) + 1 ≤ 3 * (M x : ℝ) := by linarith [hMx1]
        calc c * (2 * (M x : ℝ) + 1) ≤ (2 * L) * (3 * (M x : ℝ)) :=
              mul_le_mul hc2 hh (by positivity) (by linarith [hL0])
          _ = 6 * L * (M x : ℝ) := by ring
      have hT1b : c * (2 * (M x : ℝ) + 1) / (L ^ A * L) ≤ 6 * (M x : ℝ) / L ^ A := by
        rw [div_le_div_iff₀ (mul_pos hLApos hLpos) hLApos]
        calc c * (2 * (M x : ℝ) + 1) * L ^ A ≤ (6 * L * (M x : ℝ)) * L ^ A :=
              mul_le_mul_of_nonneg_right hcMx (le_of_lt hLApos)
          _ = 6 * (M x : ℝ) * (L ^ A * L) := by ring
      exact le_trans hT1a hT1b
    have hT2 : c ≤ 2 * ((A + 1) / ε₀) ^ (A + 1) * (M x : ℝ) / L ^ A := by
      rw [le_div_iff₀ hLApos]
      calc c * L ^ A ≤ (2 * L) * L ^ A := mul_le_mul_of_nonneg_right hc2 (le_of_lt hLApos)
        _ = 2 * (L ^ A * L) := by ring
        _ = 2 * L ^ (A + 1) := by rw [hP1]
        _ ≤ 2 * (((A + 1) / ε₀) ^ (A + 1) * (M x : ℝ)) := by linarith [hgrow]
        _ = 2 * ((A + 1) / ε₀) ^ (A + 1) * (M x : ℝ) := by ring
    have harith : c * ((2 * (M x : ℝ) + 1) / (q : ℝ) + 1) ≤ Kl * (M x : ℝ) / L ^ A := by
      have hsplit : c * ((2 * (M x : ℝ) + 1) / (q : ℝ) + 1)
          = c * ((2 * (M x : ℝ) + 1) / (q : ℝ)) + c := by ring
      rw [hsplit, hKldef]
      calc c * ((2 * (M x : ℝ) + 1) / (q : ℝ)) + c
          ≤ 6 * (M x : ℝ) / L ^ A + 2 * ((A + 1) / ε₀) ^ (A + 1) * (M x : ℝ) / L ^ A :=
            add_le_add hT1 hT2
        _ = (6 + 2 * ((A + 1) / ε₀) ^ (A + 1)) * (M x : ℝ) / L ^ A := by ring
    have hcoef : Kl ≤ max Ks Kl * ((q * r).divisors.card : ℝ) ^ (3 : ℕ) := by
      calc Kl ≤ max Ks Kl := le_max_right _ _
        _ = max Ks Kl * 1 := (mul_one _).symm
        _ ≤ max Ks Kl * ((q * r).divisors.card : ℝ) ^ (3 : ℕ) :=
            mul_le_mul_of_nonneg_left hτ1 (le_trans hKl0 (le_max_right _ _))
    refine le_trans hgen (le_trans harith ?_)
    exact (div_le_div_iff_of_pos_right hLApos).mpr
      (mul_le_mul_of_nonneg_right hcoef (by positivity))

end Salt.Maynard
