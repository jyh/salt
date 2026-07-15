/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PDiag
import Salt.Chen.GlueFinal
import Salt.Chen.TwinA1W
import Salt.Chen.TwinA2W
import Salt.Chen.CountW
import Salt.Chen.H4Cond
import Salt.Chen.WLower
import Salt.Chen.MertensPNT
import Salt.Chen.WRatioSharp

namespace Salt.Chen

-- PREAMBLE (GLU-2W frozen operating point; ε = 2·10⁻⁸ per C0 Amendment 3; A = 13, C0 = 18)
noncomputable def opEps : ℝ := 2 / 100000000
noncomputable def opW' : ℕ := w0N opEps
noncomputable def opQ : ℕ := Qval opEps
noncomputable def opA : ℕ := opQ - 1
noncomputable def opZ (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊
noncomputable def opY (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊
noncomputable def opD (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)⌋₊
noncomputable def opDlev (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((497 : ℝ) / 1000)⌋₊
noncomputable def opP (x : ℕ) : ℕ := ∏ p ∈ (Finset.Ico opW' (opZ x)).filter Nat.Prime, p
noncomputable def opPs (x : ℕ) : ℕ := ∏ p ∈ (Finset.Ico opW' (opY x)).filter Nat.Prime, p
-- END PREAMBLE

-- BEGIN FRAGMENT OPPOINT

/-! ### Part 1 — the ε rows (all pure `norm_num` at ε = 2·10⁻⁸) -/

/-- `ε > 0`. -/
theorem opf_eps_pos : 0 < opEps := by norm_num [opEps]

/-- `ε < 1/249` (margin: 2·10⁻⁸ vs 4.016·10⁻³, factor ≈ 2·10⁵). -/
theorem opf_eps49 : opEps < 1 / 249 := by norm_num [opEps]

/-- `ε ≤ 1/1000` (margin: 2·10⁻⁸ vs 10⁻³, factor 5·10⁴). -/
theorem opf_eps1000 : opEps ≤ 1 / 1000 := by norm_num [opEps]

/-- **`w0R` is huge at the operating point**: `w0R(2·10⁻⁸) = exp(40/log(1+ε)) ≥ exp(2·10⁹)`,
so certainly `≥ 10⁶`.  Proof: `log(1+ε) ≤ ε` gives `40/log(1+ε) ≥ 40/ε = 2·10⁹`, and
`exp t ≥ t + 1`.  (Margin: exp(2·10⁹) vs 10⁶ — astronomical.) -/
theorem opf_w0R_big : (10 : ℝ) ^ 6 ≤ w0R opEps := by
  have hε : (0 : ℝ) < opEps := opf_eps_pos
  have hL : (0 : ℝ) < Real.log (1 + opEps) := Real.log_pos (by linarith)
  have hle : Real.log (1 + opEps) ≤ opEps := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + opEps by linarith)
    linarith
  have hdiv : (40 : ℝ) / opEps ≤ 40 / Real.log (1 + opEps) :=
    div_le_div_of_nonneg_left (by norm_num) hL hle
  have hval : (40 : ℝ) / opEps = 2000000000 := by norm_num [opEps]
  have hexp := Real.add_one_le_exp (40 / Real.log (1 + opEps))
  rw [w0R]
  have h6 : ((10 : ℝ) ^ 6 : ℝ) = 1000000 := by norm_num
  linarith

/-- `3 ≤ w0R opEps` (from `10⁶ ≤ w0R`). -/
theorem opf_w0R3 : 3 ≤ w0R opEps := le_trans (by norm_num) opf_w0R_big

/-- `10⁶ ≤ opW'` in `ℝ` (ceiling dominates: `w0R ≤ w0N = opW'`). -/
theorem opf_w'big : (10 : ℝ) ^ 6 ≤ (opW' : ℝ) := le_trans opf_w0R_big (w0R_le_w0N opEps)

/-- **Deliverable 2**: `3 ≤ opW'` (via `w0N ≥ w0R ≥ 3` and `Nat.ceil`). -/
theorem opf_w'3 : 3 ≤ opW' := by
  have h : ((3 : ℕ) : ℝ) ≤ (opW' : ℝ) := le_trans (by norm_num) opf_w'big
  exact_mod_cast h

/-! ### Part 2 — the modulus `Q` (positivity, fullness, residue coprimality) -/

/-- `opQ`'s prime support is exactly the primes below `opW'`. -/
theorem opf_Q_primeFactors : opQ.primeFactors = (Finset.range opW').filter Nat.Prime := by
  have hq : opQ = ∏ p ∈ (Finset.range opW').filter Nat.Prime, p := rfl
  rw [hq]
  exact Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2

/-- `opQ > 0` (a product of primes). -/
theorem opf_Q_pos : 0 < opQ := by
  have hq : opQ = ∏ p ∈ (Finset.range opW').filter Nat.Prime, p := rfl
  rw [hq]
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos

/-- **Deliverable 4**: every prime `q < opW'` divides `opQ`. -/
theorem opf_Qfull : ∀ q, q.Prime → q < opW' → q ∣ opQ := by
  intro q hq hlt
  have hqe : opQ = ∏ p ∈ (Finset.range opW').filter Nat.Prime, p := rfl
  rw [hqe]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hq⟩)

/-- **Deliverable 3**: `2 ≤ opQ` (2 is prime and `2 < opW'`, so `2 ∣ opQ ≠ 0`). -/
theorem opf_Q2 : 2 ≤ opQ :=
  Nat.le_of_dvd opf_Q_pos (opf_Qfull 2 Nat.prime_two (lt_of_lt_of_le (by norm_num) opf_w'3))

/-- **Deliverable 5a**: `gcd(Q, a+2) = 1` at `a = Q − 1` (the D1 residue witness). -/
theorem opf_Qa2 : Nat.Coprime opQ (opA + 2) := by
  have h : opA = opQ - 1 := rfl
  rw [h]
  exact residue_witness opQ opf_Q2

/-- **Deliverable 5b**: `gcd(Q, a) = 1` at `a = Q − 1` (consecutive integers). -/
theorem opf_Qma : Nat.Coprime opQ opA := by
  have h : opA = opQ - 1 := rfl
  rw [h]
  exact residue_witness' opQ opf_Q2

/-- **The crude `Q`-size bound**: `opQ ≤ opW' ^ opW'` — each of the `≤ opW'` prime factors is
`< opW'`.  (Feeds the tower row `Q ≤ log x`; no primorial 4^n bound needed at a tower.) -/
theorem opf_Q_le : opQ ≤ opW' ^ opW' := by
  have hq : opQ = ∏ p ∈ (Finset.range opW').filter Nat.Prime, p := rfl
  have h1 : ∀ p ∈ (Finset.range opW').filter Nat.Prime, p ≤ opW' := by
    intro p hp
    have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    omega
  have hcard : ((Finset.range opW').filter Nat.Prime).card ≤ opW' := by
    calc ((Finset.range opW').filter Nat.Prime).card
        ≤ (Finset.range opW').card := Finset.card_filter_le _ _
      _ = opW' := Finset.card_range _
  calc opQ = ∏ p ∈ (Finset.range opW').filter Nat.Prime, p := hq
    _ ≤ opW' ^ ((Finset.range opW').filter Nat.Prime).card :=
        Finset.prod_le_pow_card _ _ _ h1
    _ ≤ opW' ^ opW' :=
        Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) opf_w'3) hcard

/-! ### Part 3 — the sifting moduli `P`, `P⋆` (squarefree, supports, coprimality) -/

/-- A finite product of distinct primes is squarefree (local copy of the landed
`Salt.M5Assembly.prod_primes_squarefree` pattern — that one lives on the Brun track). -/
theorem opf_prod_primes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hap : a.Prime := hs a (Finset.mem_insert_self a s)
    have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      exact (Nat.coprime_primes hap (hsp p hp)).mpr (by rintro rfl; exact ha hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, hap.squarefree, ih hsp⟩

/-- **Deliverable 6a**: `opP x` is squarefree. -/
theorem opf_P_sq : ∀ x, Squarefree (opP x) := by
  intro x
  have h : opP x = ∏ p ∈ (Finset.Ico opW' (opZ x)).filter Nat.Prime, p := rfl
  rw [h]
  exact opf_prod_primes_squarefree fun p hp => (Finset.mem_filter.mp hp).2

/-- **Deliverable 6b**: `opPs x` is squarefree. -/
theorem opf_Ps_sq : ∀ x, Squarefree (opPs x) := by
  intro x
  have h : opPs x = ∏ p ∈ (Finset.Ico opW' (opY x)).filter Nat.Prime, p := rfl
  rw [h]
  exact opf_prod_primes_squarefree fun p hp => (Finset.mem_filter.mp hp).2

/-- **Deliverable 7a**: the prime support of `opP x` is the prime window `[opW', opZ x)`. -/
theorem opf_P_primeFactors :
    ∀ x, (opP x).primeFactors = (Finset.Ico opW' (opZ x)).filter Nat.Prime := by
  intro x
  have h : opP x = ∏ p ∈ (Finset.Ico opW' (opZ x)).filter Nat.Prime, p := rfl
  rw [h]
  exact Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2

/-- **Deliverable 7b**: the prime support of `opPs x` is the prime window `[opW', opY x)`. -/
theorem opf_Ps_primeFactors :
    ∀ x, (opPs x).primeFactors = (Finset.Ico opW' (opY x)).filter Nat.Prime := by
  intro x
  have h : opPs x = ∏ p ∈ (Finset.Ico opW' (opY x)).filter Nat.Prime, p := rfl
  rw [h]
  exact Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2

/-- `opP x > 0` (a product of primes). -/
theorem opf_P_pos : ∀ x, 0 < opP x := by
  intro x
  have h : opP x = ∏ p ∈ (Finset.Ico opW' (opZ x)).filter Nat.Prime, p := rfl
  rw [h]
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos

/-- `opPs x > 0` (a product of primes). -/
theorem opf_Ps_pos : ∀ x, 0 < opPs x := by
  intro x
  have h : opPs x = ∏ p ∈ (Finset.Ico opW' (opY x)).filter Nat.Prime, p := rfl
  rw [h]
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos

/-! ### Part 4 — the derived support rows (deliverable 8) -/

/-- Every prime factor of `opP x` is `≥ 3` (it is `≥ opW' ≥ 3`). -/
theorem opf_Podd : ∀ x, ∀ p ∈ (opP x).primeFactors, 3 ≤ p := by
  intro x p hp
  rw [opf_P_primeFactors x] at hp
  have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
  have h3 := opf_w'3
  omega

/-- Every prime factor of `opPs x` is `≥ 3`. -/
theorem opf_Psodd : ∀ x, ∀ p ∈ (opPs x).primeFactors, 3 ≤ p := by
  intro x p hp
  rw [opf_Ps_primeFactors x] at hp
  have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
  have h3 := opf_w'3
  omega

/-- Every prime factor of `opP x` is `< opZ x`. -/
theorem opf_Pz : ∀ x, ∀ p ∈ (opP x).primeFactors, p < opZ x := by
  intro x p hp
  rw [opf_P_primeFactors x] at hp
  exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2

/-- Every prime factor of `opPs x` is `< opY x`. -/
theorem opf_Psy : ∀ x, ∀ p ∈ (opPs x).primeFactors, p < opY x := by
  intro x p hp
  rw [opf_Ps_primeFactors x] at hp
  exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2

/-- Every prime factor of `opP x` clears the real threshold `w0R opEps`
(`p ≥ opW' = ⌈w0R⌉ ≥ w0R`). -/
theorem opf_Plow : ∀ x, ∀ p ∈ (opP x).primeFactors, w0R opEps ≤ (p : ℝ) := by
  intro x p hp
  rw [opf_P_primeFactors x] at hp
  have h1 : opW' ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
  exact le_trans (w0R_le_w0N opEps) (Nat.cast_le.mpr h1)

/-- Every prime factor of `opPs x` clears the real threshold `w0R opEps`. -/
theorem opf_Pslow : ∀ x, ∀ p ∈ (opPs x).primeFactors, w0R opEps ≤ (p : ℝ) := by
  intro x p hp
  rw [opf_Ps_primeFactors x] at hp
  have h1 : opW' ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
  exact le_trans (w0R_le_w0N opEps) (Nat.cast_le.mpr h1)

/-- Every prime factor of `opPs x` is `≥ opW'`. -/
theorem opf_Psw' : ∀ x, ∀ p ∈ (opPs x).primeFactors, opW' ≤ p := by
  intro x p hp
  rw [opf_Ps_primeFactors x] at hp
  exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1

/-- **The windowed fullness row**: every prime `q ∈ [opW', opZ x)` divides `opP x`. -/
theorem opf_Pfull' : ∀ x, ∀ q, q.Prime → opW' ≤ q → q < opZ x → q ∣ opP x := by
  intro x q hq h1 h2
  have h : opP x = ∏ p ∈ (Finset.Ico opW' (opZ x)).filter Nat.Prime, p := rfl
  rw [h]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h1, h2⟩, hq⟩)

/-! ### Part 5 — the `Q ⊥ P` rows (deliverables 9–11; disjoint prime supports) -/

/-- **Deliverable 9a**: `gcd(opQ, opP x) = 1` — `opQ`'s primes live below `opW'`, `opP`'s at
or above it. -/
theorem opf_QP : ∀ x, Nat.Coprime opQ (opP x) := by
  intro x
  have hdisj : Disjoint opQ.primeFactors (opP x).primeFactors := by
    rw [opf_Q_primeFactors, opf_P_primeFactors x, Finset.disjoint_left]
    intro p hpQ hpP
    have h1 : p < opW' := Finset.mem_range.mp (Finset.mem_filter.mp hpQ).1
    have h2 : opW' ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hpP).1).1
    omega
  exact (Nat.disjoint_primeFactors opf_Q_pos.ne' (opf_P_pos x).ne').mp hdisj

/-- **Deliverable 9b**: `gcd(opQ, opPs x) = 1`. -/
theorem opf_QPs : ∀ x, Nat.Coprime opQ (opPs x) := by
  intro x
  have hdisj : Disjoint opQ.primeFactors (opPs x).primeFactors := by
    rw [opf_Q_primeFactors, opf_Ps_primeFactors x, Finset.disjoint_left]
    intro p hpQ hpP
    have h1 : p < opW' := Finset.mem_range.mp (Finset.mem_filter.mp hpQ).1
    have h2 : opW' ≤ p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hpP).1).1
    omega
  exact (Nat.disjoint_primeFactors opf_Q_pos.ne' (opf_Ps_pos x).ne').mp hdisj

/-- **Deliverable 10**: `opP x ∣ opPs x` once `opZ x ≤ opY x` (window inclusion). -/
theorem opf_PdvdPs : ∀ x, opZ x ≤ opY x → opP x ∣ opPs x := by
  intro x hzy
  have hP : opP x = ∏ p ∈ (Finset.Ico opW' (opZ x)).filter Nat.Prime, p := rfl
  have hPs : opPs x = ∏ p ∈ (Finset.Ico opW' (opY x)).filter Nat.Prime, p := rfl
  rw [hP, hPs]
  exact Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl hzy))

/-- **Deliverable 11**: `opQ` is coprime to every prime in the switch window `[opZ x, opY x]`
(once `opW' ≤ opZ x`) — such a `p` is `≥ opW'`, but all of `opQ`'s primes are `< opW'`. -/
theorem opf_QmPr : ∀ x, opW' ≤ opZ x →
    ∀ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime, Nat.Coprime opQ p := by
  intro x hwz p hp
  obtain ⟨hmem, hprime⟩ := Finset.mem_filter.mp hp
  have hzp : opZ x ≤ p := (Finset.mem_Icc.mp hmem).1
  have hnd : ¬ p ∣ opQ := by
    intro hdvd
    have hpf : p ∈ opQ.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hprime, hdvd, opf_Q_pos.ne'⟩
    rw [opf_Q_primeFactors] at hpf
    have hlt : p < opW' := Finset.mem_range.mp (Finset.mem_filter.mp hpf).1
    omega
  exact ((Nat.Prime.coprime_iff_not_dvd hprime).mpr hnd).symm

/-! ### Part 6 — the floor-bracket helpers (local copies of `WindowMembership`'s private
`window_floor_bounds` / `log_ge_96`, with the un-floored `10⁶ ≤ x^γ` component exported too) -/

/-- Floor bracketing for `x ≥ 10⁴⁸`, `γ ≥ 1/8`: `x^γ ≥ 10⁶`, `⌊x^γ⌋ ≥ 10⁶`, and
`γ·log x − 1/999999 ≤ log⌊x^γ⌋ ≤ γ·log x`. -/
theorem opf_window_floor_bounds (x : ℕ) (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) {γ : ℝ}
    (hγ : (1 / 8 : ℝ) ≤ γ) :
    (10 : ℝ) ^ 6 ≤ (x : ℝ) ^ γ
      ∧ (10 : ℝ) ^ 6 ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ)
      ∧ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ γ * Real.log (x : ℝ)
      ∧ γ * Real.log (x : ℝ) - 1 / 999999 ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
  have hX1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx
  have hXpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
  have hpow48 : ((10 : ℝ) ^ (48 : ℕ)) ^ ((1 : ℝ) / 8) = (10 : ℝ) ^ 6 := by
    have h6 : ((48 : ℕ) : ℝ) * (1 / 8) = ((6 : ℕ) : ℝ) := by norm_num
    rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10), h6,
      Real.rpow_natCast]
  have hstep1 : (10 : ℝ) ^ 6 ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← hpow48]; exact Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hstep2 : (x : ℝ) ^ ((1 : ℝ) / 8) ≤ (x : ℝ) ^ γ :=
    Real.rpow_le_rpow_of_exponent_le hX1 hγ
  have hApow : (10 : ℝ) ^ 6 ≤ (x : ℝ) ^ γ := le_trans hstep1 hstep2
  have hA6 : (1000000 : ℝ) ≤ (x : ℝ) ^ γ := le_trans (by norm_num) hApow
  have hXγnn : (0 : ℝ) ≤ (x : ℝ) ^ γ := Real.rpow_nonneg hXpos.le γ
  have hfloor_ge : (10 : ℝ) ^ 6 ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    have h1 : ((1000000 : ℕ) : ℝ) ≤ (x : ℝ) ^ γ := by
      rw [show ((1000000 : ℕ) : ℝ) = (10 : ℝ) ^ 6 by norm_num]; exact hApow
    have h2 : (1000000 : ℕ) ≤ ⌊(x : ℝ) ^ γ⌋₊ := Nat.le_floor h1
    calc (10 : ℝ) ^ 6 = ((1000000 : ℕ) : ℝ) := by norm_num
      _ ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by exact_mod_cast h2
  have hfloor_le : (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ (x : ℝ) ^ γ := Nat.floor_le hXγnn
  have hfloor_gt : (x : ℝ) ^ γ - 1 < (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one ((x : ℝ) ^ γ)]
  have hzfpos : (0 : ℝ) < (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := lt_of_lt_of_le (by norm_num) hfloor_ge
  have hXγ1pos : (0 : ℝ) < (x : ℝ) ^ γ - 1 := by linarith [hA6]
  have hlogXγ : Real.log ((x : ℝ) ^ γ) = γ * Real.log (x : ℝ) := Real.log_rpow hXpos γ
  have hlog_le : Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ γ * Real.log (x : ℝ) := by
    rw [← hlogXγ]; exact Real.log_le_log hzfpos hfloor_le
  have hratio : (x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1) ≤ 1000000 / 999999 := by
    rw [div_le_div_iff₀ hXγ1pos (by norm_num : (0 : ℝ) < 999999)]
    nlinarith [hA6]
  have hcorr : Real.log ((x : ℝ) ^ γ) - Real.log ((x : ℝ) ^ γ - 1) ≤ 1 / 999999 := by
    have h1 : Real.log ((x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1)) ≤ (x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (ne_of_gt hXγ1pos)] at h1
    linarith [h1, hratio]
  have hlog_ge : γ * Real.log (x : ℝ) - 1 / 999999 ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    have hlog_floor_ge : Real.log ((x : ℝ) ^ γ - 1) ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) :=
      Real.log_le_log hXγ1pos (le_of_lt hfloor_gt)
    rw [hlogXγ] at hcorr
    linarith [hlog_floor_ge, hcorr]
  exact ⟨hApow, hfloor_ge, hlog_le, hlog_ge⟩

/-- `log 10 ≥ 2`, hence `log x ≥ 96` for `x ≥ 10⁴⁸` (local copy). -/
theorem opf_log_ge_96 (x : ℕ) (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) :
    (96 : ℝ) ≤ Real.log (x : ℝ) := by
  have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hmono : Real.log ((10 : ℝ) ^ 48) ≤ Real.log (x : ℝ) := Real.log_le_log (by positivity) hx
  rw [Real.log_pow] at hmono
  push_cast at hmono
  linarith [hmono, hlog10]

/-! ### Part 7 — the tower bundle (deliverable 12)

Threshold `x₁ = max ⌈exp(opW' ^ opW')⌉ 10⁴⁸`: the first branch makes `log x ≥ opW'^opW' ≥ opQ`
(crude `Q ≤ w'^w'` bound) with room `w'^w'/w'² ≈ exp(w' log w')` to spare; the `10⁴⁸` branch
runs the floor-bracket rows.  Per the GLU-2W operating convention (A3W2/GlueFinal: the consumer
takes any `Dlev ∈ [x^{497/1000}, x^{1/2}]`), the raw `x^{497/1000} ≤ ⌊x^{497/1000}⌋` row —
false by a floor hair — is replaced by the pair `x^{496/1000} ≤ opDlev x` (room `x^{1/1000}`)
plus the DIRECT window membership `logRatio (opY x) (opDlev x) ∈ [149/100, 151/100]`
(un-floored value 1.491, floor loss ≤ 10⁻⁶ against margins ≥ 3·10⁻²), so downstream never
needs the exact-497 lower bound. -/
theorem opf_tower : ∃ x₁ : ℕ, 8 ≤ x₁ ∧ ∀ x : ℕ, x₁ ≤ x →
    ((opQ : ℝ) ≤ Real.log x
      ∧ w0R opEps ≤ ((opZ x : ℕ) : ℝ)
      ∧ opW' ≤ opZ x
      ∧ 3 ≤ opZ x
      ∧ opZ x ≤ opD x
      ∧ 1 ≤ opD x
      ∧ opZ x ≤ opY x
      ∧ opY x ≤ x / 2
      ∧ x < (opY x + 1) ^ 3
      ∧ 2 ≤ logRatio (opZ x) (opD x)
      ∧ 1 ≤ logRatio (opY x) (opDlev x)
      ∧ 2 ≤ opDlev x
      ∧ (opD x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2)
      ∧ (x : ℝ) ^ ((496 : ℝ) / 1000) ≤ (opDlev x : ℝ)
      ∧ logRatio (opY x) (opDlev x) ∈ Set.Icc (149 / 100 : ℝ) (151 / 100 : ℝ)
      ∧ (opDlev x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2)
      ∧ 4 ≤ x) := by
  refine ⟨max ⌈Real.exp ((opW' ^ opW' : ℕ) : ℝ)⌉₊ (10 ^ 48),
    le_trans (by norm_num) (le_max_right _ _), fun x hx => ?_⟩
  -- global facts at the operating point
  have hx48 : 10 ^ 48 ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hxR
  have hL96 : (96 : ℝ) ≤ Real.log (x : ℝ) := opf_log_ge_96 x hxR
  have hxT : Real.exp ((opW' ^ opW' : ℕ) : ℝ) ≤ (x : ℝ) := by
    have h1 : ⌈Real.exp ((opW' ^ opW' : ℕ) : ℝ)⌉₊ ≤ x := le_trans (le_max_left _ _) hx
    calc Real.exp ((opW' ^ opW' : ℕ) : ℝ)
        ≤ (⌈Real.exp ((opW' ^ opW' : ℕ) : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (x : ℝ) := Nat.cast_le.mpr h1
  have hlogT : ((opW' ^ opW' : ℕ) : ℝ) ≤ Real.log (x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hxT
    rwa [Real.log_exp] at h
  -- row 1: Q ≤ log x  (margin: opQ ≤ w'^w' ≤ log x by the tower choice)
  have hrow1 : (opQ : ℝ) ≤ Real.log (x : ℝ) := by
    have h2 : (opQ : ℝ) ≤ ((opW' ^ opW' : ℕ) : ℝ) := Nat.cast_le.mpr opf_Q_le
    linarith [hlogT]
  -- rows 2–4: w' ≤ z = ⌊x^{1/8}⌋  (log x ≥ w'² so x^{1/8} ≥ exp(w'²/8) ≥ 2w'−7 ≥ w')
  have hw'R : (10 : ℝ) ^ 6 ≤ (opW' : ℝ) := opf_w'big
  have hsq_le_T : (opW' : ℝ) * (opW' : ℝ) ≤ ((opW' ^ opW' : ℕ) : ℝ) := by
    have h1 : opW' ^ 2 ≤ opW' ^ opW' :=
      Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) opf_w'3)
        (le_trans (by norm_num) opf_w'3)
    have h2 : ((opW' ^ 2 : ℕ) : ℝ) ≤ ((opW' ^ opW' : ℕ) : ℝ) := Nat.cast_le.mpr h1
    have h3 : ((opW' ^ 2 : ℕ) : ℝ) = (opW' : ℝ) * (opW' : ℝ) := by push_cast; ring
    linarith
  have hlogx_sq : (opW' : ℝ) * (opW' : ℝ) ≤ Real.log (x : ℝ) := le_trans hsq_le_T hlogT
  have hw'x18 : ((opW' : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [Real.rpow_def_of_pos hxpos]
    have hexp := Real.add_one_le_exp (Real.log (x : ℝ) * ((1 : ℝ) / 8))
    nlinarith [hw'R, hlogx_sq, hexp, sq_nonneg ((opW' : ℝ) - 8)]
  have hrow3 : opW' ≤ opZ x := by
    rw [opZ]
    exact Nat.le_floor hw'x18
  have hrow2 : w0R opEps ≤ ((opZ x : ℕ) : ℝ) :=
    le_trans (w0R_le_w0N opEps) (Nat.cast_le.mpr hrow3)
  have hrow4 : 3 ≤ opZ x := le_trans opf_w'3 hrow3
  -- rows 5–7: floor monotonicity in the exponent (1/8 ≤ 1/2 − 9·10⁻⁵, 1/8 ≤ 1/3)
  have hrow5 : opZ x ≤ opD x := by
    rw [opZ, opD]
    exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num))
  have hrow6 : 1 ≤ opD x := by
    rw [opD]
    refine Nat.le_floor ?_
    have h4 : (1 : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
      Real.rpow_le_rpow (by norm_num) hx1R (by norm_num)
    rw [Real.one_rpow] at h4
    exact_mod_cast h4
  have hrow7 : opZ x ≤ opY x := by
    rw [opZ, opY]
    exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num))
  -- row 8: y ≤ x/2  (2·x^{1/3} ≤ x since x^{2/3} ≥ 10³² ≥ 2)
  have hy_leR : (opY x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [opY]
    exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have hx23 : (2 : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) := by
    have hpow : ((10 : ℝ) ^ (48 : ℕ)) ^ ((2 : ℝ) / 3) = (10 : ℝ) ^ (32 : ℕ) := by
      rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
        show ((48 : ℕ) : ℝ) * (2 / 3) = ((32 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h1 : ((10 : ℝ) ^ (48 : ℕ)) ^ ((2 : ℝ) / 3) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hxR (by norm_num)
    rw [hpow] at h1
    have h2 : (2 : ℝ) ≤ (10 : ℝ) ^ (32 : ℕ) := by norm_num
    linarith
  have hsplit13 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((2 : ℝ) / 3) = (x : ℝ) := by
    rw [← Real.rpow_add hxpos, show (1 : ℝ) / 3 + 2 / 3 = 1 by norm_num, Real.rpow_one]
  have h13nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hxpos.le _
  have hAB : 2 * ((x : ℝ) ^ ((1 : ℝ) / 3))
      ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((2 : ℝ) / 3) := by
    nlinarith [h13nn, hx23]
  have hrow8 : opY x ≤ x / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have hR : (opY x : ℝ) * 2 ≤ (x : ℝ) := by linarith [hy_leR, hAB, hsplit13]
    exact_mod_cast hR
  -- row 9: the landed hyx row
  have hrow9 : x < (opY x + 1) ^ 3 := by
    rw [opY]
    exact hyx_at_op x (le_trans (by norm_num) hx48)
  -- the four floor-bracket windows
  obtain ⟨-, hz6, hz_le, -⟩ :=
    opf_window_floor_bounds x hxR (γ := (1 : ℝ) / 8) (by norm_num)
  obtain ⟨-, -, -, hD_ge⟩ :=
    opf_window_floor_bounds x hxR (γ := (1 : ℝ) / 2 - 9 / 100000) (by norm_num)
  obtain ⟨-, hy6, hy_le, hy_ge⟩ :=
    opf_window_floor_bounds x hxR (γ := (1 : ℝ) / 3) (by norm_num)
  obtain ⟨-, hDl6, hDl_le, hDl_ge⟩ :=
    opf_window_floor_bounds x hxR (γ := (497 : ℝ) / 1000) (by norm_num)
  have hlogz_pos : (0 : ℝ) < Real.log (⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hz6)
  have hlogy_pos : (0 : ℝ) < Real.log (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hy6)
  -- row 10: logRatio z D ≥ 2  (un-floored (1/2−9·10⁻⁵)/(1/8) = 3.99928; slack 0.24991·t ≥ 24)
  have hrow10 : 2 ≤ logRatio (opZ x) (opD x) := by
    rw [opZ, opD, logRatio, le_div_iff₀ hlogz_pos]
    linarith [hz_le, hD_ge, hL96]
  -- row 15: logRatio y Dlev ∈ [1.49, 1.51]  (un-floored 0.497/(1/3) = 1.491;
  -- lower slack t/3000 ≥ 0.032 ≥ 10⁻⁶ loss, upper slack 19t/3000 ≥ 0.608 ≥ 1.51·10⁻⁶ loss)
  have hrow15 : logRatio (opY x) (opDlev x) ∈ Set.Icc (149 / 100 : ℝ) (151 / 100 : ℝ) := by
    rw [opY, opDlev, Set.mem_Icc]
    constructor
    · rw [logRatio, le_div_iff₀ hlogy_pos]
      linarith [hy_le, hDl_ge, hL96]
    · rw [logRatio, div_le_iff₀ hlogy_pos]
      linarith [hDl_le, hy_ge, hL96]
  -- row 11: from the membership (1 ≤ 149/100 ≤ logRatio)
  have hrow11 : 1 ≤ logRatio (opY x) (opDlev x) := by
    have h := (Set.mem_Icc.mp hrow15).1
    linarith
  -- row 12: Dlev ≥ 2  (⌊x^{497/1000}⌋ ≥ 10⁶)
  have hrow12 : 2 ≤ opDlev x := by
    rw [opDlev]
    have h2 : ((2 : ℕ) : ℝ) ≤ (⌊(x : ℝ) ^ ((497 : ℝ) / 1000)⌋₊ : ℝ) :=
      le_trans (by norm_num) hDl6
    exact_mod_cast h2
  -- row 13: D ≤ x^{1/2}  (floor ≤ x^{1/2−9·10⁻⁵} ≤ x^{1/2})
  have hrow13 : (opD x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [opD]
    calc (⌊(x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)⌋₊ : ℝ)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := Nat.floor_le (Real.rpow_nonneg hxpos.le _)
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
  -- row 14: x^{496/1000} ≤ Dlev  (gap x^{0.497} − x^{0.496} = x^{0.496}(x^{10⁻³} − 1)
  -- ≥ 10⁶·0.096 = 96000 ≥ 1, so the floor loss of 1 is absorbed with 5 digits of room)
  have hrow14 : (x : ℝ) ^ ((496 : ℝ) / 1000) ≤ (opDlev x : ℝ) := by
    rw [opDlev]
    obtain ⟨h496, -, -, -⟩ :=
      opf_window_floor_bounds x hxR (γ := (496 : ℝ) / 1000) (by norm_num)
    have hsplit : (x : ℝ) ^ ((497 : ℝ) / 1000)
        = (x : ℝ) ^ ((496 : ℝ) / 1000) * (x : ℝ) ^ ((1 : ℝ) / 1000) := by
      rw [← Real.rpow_add hxpos, show (496 : ℝ) / 1000 + 1 / 1000 = 497 / 1000 by norm_num]
    have h1000 : (1 : ℝ) + Real.log (x : ℝ) * (1 / 1000) ≤ (x : ℝ) ^ ((1 : ℝ) / 1000) := by
      rw [Real.rpow_def_of_pos hxpos]
      linarith [Real.add_one_le_exp (Real.log (x : ℝ) * (1 / 1000))]
    have h1096 : (1096 / 1000 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 1000) := by linarith [hL96, h1000]
    have h496nn : (0 : ℝ) ≤ (x : ℝ) ^ ((496 : ℝ) / 1000) := Real.rpow_nonneg hxpos.le _
    have hprod : (x : ℝ) ^ ((496 : ℝ) / 1000) * (1096 / 1000)
        ≤ (x : ℝ) ^ ((496 : ℝ) / 1000) * (x : ℝ) ^ ((1 : ℝ) / 1000) :=
      mul_le_mul_of_nonneg_left h1096 h496nn
    have hfl := Nat.lt_floor_add_one ((x : ℝ) ^ ((497 : ℝ) / 1000))
    linarith [hprod, h496, hfl, hsplit.ge, hsplit.le]
  -- row 16: Dlev ≤ x^{1/2}  (497/1000 ≤ 1/2)
  have hrow16 : (opDlev x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [opDlev]
    calc (⌊(x : ℝ) ^ ((497 : ℝ) / 1000)⌋₊ : ℝ)
        ≤ (x : ℝ) ^ ((497 : ℝ) / 1000) := Nat.floor_le (Real.rpow_nonneg hxpos.le _)
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
  -- row 17: 4 ≤ x
  have hrow17 : 4 ≤ x := le_trans (by norm_num) hx48
  exact ⟨hrow1, hrow2, hrow3, hrow4, hrow5, hrow6, hrow7, hrow8, hrow9, hrow10, hrow11,
    hrow12, hrow13, hrow14, hrow15, hrow16, hrow17⟩

-- END FRAGMENT OPPOINT


-- BEGIN FRAGMENT A1A2

open Finset ArithmeticFunction Salt.LS Salt.BV

/-! ### Part 0 — numeric helpers (local mirrors of GlueFinal's private toolkit) -/

/-- The tower threshold: past `⌈exp M⌉ + 1` both `exp M ≤ x` and `M ≤ log x` hold. -/
theorem a12_log_ge (M : ℝ) : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    Real.exp M ≤ (x : ℝ) ∧ M ≤ Real.log x := by
  refine ⟨⌈Real.exp M⌉₊ + 1, ?_⟩
  intro x hx
  have h1 : Real.exp M ≤ (x : ℝ) := by
    have h2 : (⌈Real.exp M⌉₊ : ℝ) ≤ (x : ℝ) := by
      have h3 : ⌈Real.exp M⌉₊ ≤ x := by omega
      exact_mod_cast h3
    exact le_trans (Nat.le_ceil _) h2
  refine ⟨h1, ?_⟩
  have h4 := Real.log_le_log (Real.exp_pos M) h1
  rwa [Real.log_exp] at h4

/-- **Polylog beats power** (the `log_rpow_le_poly` mirror, thresholded): for any exponent
`E ≥ 0` and any power `c > 0`, `(log x)^E ≤ x^c` for all large `x`.  Route: at
`δ := c/(E+1)`, `log x ≤ x^δ/δ` (`Real.log_le_rpow_div`) and `(1/δ)^E ≤ x^δ` past the
threshold `log x ≥ E·log(1/δ)/δ`; the exponents recombine to `δE + δ = c` exactly. -/
theorem a12_logpow_le_rpow (E c : ℝ) (hE : 0 ≤ E) (hc : 0 < c) :
    ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x → (Real.log x) ^ E ≤ (x : ℝ) ^ c := by
  have hE1 : (0 : ℝ) < E + 1 := by linarith
  set δ : ℝ := c / (E + 1) with hδdef
  have hδ : 0 < δ := div_pos hc hE1
  obtain ⟨x₁, hx₁⟩ := a12_log_ge (max 1 (E * Real.log (1 / δ) / δ))
  refine ⟨x₁, ?_⟩
  intro x hx
  obtain ⟨hexpx, hlogx⟩ := hx₁ x hx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hL1 : (1 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hlogx
  have hL0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hMδ : E * Real.log (1 / δ) / δ ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  have h1 : Real.log x ≤ (x : ℝ) ^ δ / δ := Real.log_le_rpow_div hxpos.le hδ
  have h2 : (1 / δ) ^ E ≤ (x : ℝ) ^ δ := by
    have hlog2 : E * Real.log (1 / δ) ≤ Real.log (x : ℝ) * δ := by
      have h := mul_le_mul_of_nonneg_right hMδ hδ.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at h
    have hδinv : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδ
    have hpos : (0 : ℝ) < (1 / δ) ^ E := Real.rpow_pos_of_pos hδinv E
    calc (1 / δ) ^ E = Real.exp (Real.log ((1 / δ) ^ E)) := (Real.exp_log hpos).symm
      _ = Real.exp (E * Real.log (1 / δ)) := by rw [Real.log_rpow hδinv]
      _ ≤ Real.exp (Real.log (x : ℝ) * δ) := Real.exp_le_exp.mpr hlog2
      _ = (x : ℝ) ^ δ := (Real.rpow_def_of_pos hxpos δ).symm
  have hxδnn : (0 : ℝ) ≤ (x : ℝ) ^ δ := (Real.rpow_pos_of_pos hxpos δ).le
  have hE1' : E + 1 ≠ 0 := ne_of_gt hE1
  calc (Real.log x) ^ E
      ≤ ((x : ℝ) ^ δ / δ) ^ E := Real.rpow_le_rpow hL0 h1 hE
    _ = ((x : ℝ) ^ δ) ^ E * (1 / δ) ^ E := by
        rw [div_eq_mul_one_div, Real.mul_rpow hxδnn (by positivity)]
    _ = (x : ℝ) ^ (δ * E) * (1 / δ) ^ E := by rw [← Real.rpow_mul hxpos.le]
    _ ≤ (x : ℝ) ^ (δ * E) * (x : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hxpos.le _)
    _ = (x : ℝ) ^ (δ * E + δ) := (Real.rpow_add hxpos _ _).symm
    _ = (x : ℝ) ^ c := by
        rw [hδdef]
        congr 1
        field_simp

/-- `(27/10)^n ≤ exp n` — GlueFinal's `pow27_le_exp`, reproved locally. -/
theorem a12_pow27_le_exp (n : ℕ) : ((27 : ℝ) / 10) ^ n ≤ Real.exp n := by
  have h9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h1 : ((27 : ℝ) / 10) ≤ Real.exp 1 := by
    have h2 : (27 : ℝ) / 10 ≤ 2.7182818283 := by norm_num
    linarith
  calc ((27 : ℝ) / 10) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h1 n
    _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]

/-! ### Part 1 — the frozen-point ε/Q constants -/

theorem a12_eps_pos : (0 : ℝ) < opEps := by simp only [opEps]; norm_num

theorem a12_eps_le_1000 : opEps ≤ 1 / 1000 := by simp only [opEps]; norm_num

theorem a12_eps_lt_249 : opEps < 1 / 249 := by simp only [opEps]; norm_num

/-- `3 ≤ w0R opEps`: `log(1+ε) ≤ ε ≤ 20` gives `40/log(1+ε) ≥ 2`, so `w0R ≥ e² ≥ 3`.
(Margin: at ε = 2·10⁻⁸ the true value is `≈ exp(2·10⁹)`.) -/
theorem a12_hw0 : (3 : ℝ) ≤ w0R opEps := by
  have hεpos := a12_eps_pos
  have hlogpos : 0 < Real.log (1 + opEps) := Real.log_pos (by linarith)
  have hlogle : Real.log (1 + opEps) ≤ opEps := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + opEps by linarith)
    linarith
  have hεle := a12_eps_le_1000
  have h2 : (2 : ℝ) ≤ 40 / Real.log (1 + opEps) := by
    rw [le_div_iff₀ hlogpos]
    linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by nlinarith [Real.add_one_le_exp (2 : ℝ)]
  calc (3 : ℝ) ≤ Real.exp 2 := h3
    _ ≤ Real.exp (40 / Real.log (1 + opEps)) := Real.exp_le_exp.mpr h2
    _ = w0R opEps := by rw [w0R]

/-- `1 ≤ log(w0R opEps) = 40/log(1+ε)` (margin: the true value is `≈ 2·10⁹`). -/
theorem a12_logw0_ge_one : (1 : ℝ) ≤ Real.log (w0R opEps) := by
  have hεpos := a12_eps_pos
  have hlogpos : 0 < Real.log (1 + opEps) := Real.log_pos (by linarith)
  have hlogle : Real.log (1 + opEps) ≤ opEps := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + opEps by linarith)
    linarith
  have hεle := a12_eps_le_1000
  have hlogw : Real.log (w0R opEps) = 40 / Real.log (1 + opEps) := by
    rw [w0R, Real.log_exp]
  rw [hlogw, le_div_iff₀ hlogpos]
  linarith

/-- `2 ≤ opQ`: `2` is a prime below `w0N opEps ≥ 3`, so it divides the positive `Qval`. -/
theorem a12_Q2 : 2 ≤ opQ := by
  have h3 : (3 : ℝ) ≤ (w0N opEps : ℝ) := le_trans a12_hw0 (w0R_le_w0N opEps)
  have h3N : 3 ≤ w0N opEps := by exact_mod_cast h3
  have hmem : 2 ∈ (Finset.range (w0N opEps)).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hpos : 0 < Qval opEps := by
    apply Finset.prod_pos
    intro p hp
    exact (Finset.mem_filter.mp hp).2.pos
  have hdvd : 2 ∣ Qval opEps := Finset.dvd_prod_of_mem _ hmem
  exact Nat.le_of_dvd hpos hdvd

/-- The crude `ω(n) ≤ n` (prime factors inject into `[1, n]`); anything `≤ log x` works. -/
theorem a12_omega_le (n : ℕ) : n.primeFactors.card ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : n.primeFactors.card ≤ (Finset.Icc 1 n).card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_Icc]
      exact ⟨(Nat.prime_of_mem_primeFactors hp).pos, Nat.le_of_mem_primeFactors hp⟩
    have h2 : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
    omega

/-! ### Part 2 — the operating-point floor facts (`z ≥ 3`, `z·y + 1 ≤ D`)

Margins at `log x ≥ 200`: `z = ⌊x^{1/8}⌋ ≥ exp 25 − 1`, and `x^γ/x^{11/24} = x^{1/24 − 9/10⁵}
≥ exp(8.31) ≥ 3` absorbs `z·y + 2 ≤ x^{11/24} + 2 ≤ 3·x^{11/24} ≤ x^γ`. -/
theorem a12_zyD : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    3 ≤ opZ x ∧ opZ x * opY x + 1 ≤ opD x := by
  obtain ⟨x₁, h₁⟩ := a12_log_ge 200
  refine ⟨x₁, ?_⟩
  intro x hx
  obtain ⟨hexpx, hlogx⟩ := h₁ x hx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by nlinarith [Real.add_one_le_exp (200 : ℝ)]
  constructor
  · have h3 : (3 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
      have he : Real.exp 25 ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
        rw [Real.rpow_def_of_pos hxpos]
        apply Real.exp_le_exp.mpr
        linarith
      nlinarith [Real.add_one_le_exp (25 : ℝ)]
    simp only [opZ]
    exact Nat.le_floor (by exact_mod_cast h3)
  · have hz : (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
      simp only [opZ]
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    have hy : (opY x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      simp only [opY]
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    have hDgt : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) - 1 < (opD x : ℝ) := by
      simp only [opD]
      have h := Nat.lt_floor_add_one ((x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000))
      linarith
    have hzy : (opZ x : ℝ) * (opY x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) := by
      calc (opZ x : ℝ) * (opY x : ℝ)
          ≤ (x : ℝ) ^ ((1 : ℝ) / 8) * (x : ℝ) ^ ((1 : ℝ) / 3) :=
            mul_le_mul hz hy (Nat.cast_nonneg _) (Real.rpow_nonneg hxpos.le _)
        _ = (x : ℝ) ^ ((11 : ℝ) / 24) := by
            rw [← Real.rpow_add hxpos, show (1 : ℝ) / 8 + 1 / 3 = 11 / 24 by norm_num]
    have hgap : (x : ℝ) ^ ((11 : ℝ) / 24) + 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
      have hsplit : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)
          = (x : ℝ) ^ ((1 : ℝ) / 24 - 9 / 100000) * (x : ℝ) ^ ((11 : ℝ) / 24) := by
        rw [← Real.rpow_add hxpos,
          show (1 : ℝ) / 24 - 9 / 100000 + 11 / 24 = 1 / 2 - 9 / 100000 by norm_num]
      have hbig : (3 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 24 - 9 / 100000) := by
        have he : Real.exp 8 ≤ (x : ℝ) ^ ((1 : ℝ) / 24 - 9 / 100000) := by
          rw [Real.rpow_def_of_pos hxpos]
          apply Real.exp_le_exp.mpr
          nlinarith
        nlinarith [Real.add_one_le_exp (8 : ℝ)]
      have h11nn : (1 : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 24) := by
        calc (1 : ℝ) = (x : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
          _ ≤ (x : ℝ) ^ ((11 : ℝ) / 24) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      calc (x : ℝ) ^ ((11 : ℝ) / 24) + 2 ≤ 3 * (x : ℝ) ^ ((11 : ℝ) / 24) := by linarith
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 24 - 9 / 100000) * (x : ℝ) ^ ((11 : ℝ) / 24) :=
            mul_le_mul_of_nonneg_right hbig (by linarith)
        _ = (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := hsplit.symm
    have hfin : ((opZ x * opY x + 1 : ℕ) : ℝ) ≤ (opD x : ℝ) := by
      push_cast
      nlinarith [hzy, hgap, hDgt]
    exact_mod_cast hfin

/-- The aggregated `Σ 1/(p−1)` window mass, harmonically: `1/(p−1) ≤ 2/p`, then the harmonic
sum `Σ_{n ≤ y} 1/n ≤ 1 + log y ≤ 2·log x`; total `≤ 4·log x`.  Crude but polylog. -/
theorem a12_primeInv_le (z y x : ℕ) (hyx : y ≤ x) (hL1 : 1 ≤ Real.log x) :
    ∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1) ≤ 4 * Real.log x := by
  have hstep1 : ∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      ≤ ∑ n ∈ Finset.Icc 2 y, 1 / ((n : ℝ) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, hp.1.2⟩
    · intro n hn _
      rw [Finset.mem_Icc] at hn
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      positivity
  have hstep2 : ∑ n ∈ Finset.Icc 2 y, 1 / ((n : ℝ) - 1)
      ≤ ∑ n ∈ Finset.Icc 2 y, 2 * (1 / (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    rw [mul_one_div, div_le_div_iff₀ hn1 hn0]
    linarith
  have hstep4 : ∑ n ∈ Finset.Icc 2 y, 1 / (n : ℝ) ≤ ∑ n ∈ Finset.Icc 1 y, 1 / (n : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc (by norm_num) le_rfl
    · intro n _ _
      positivity
  have hstep5 : ∑ n ∈ Finset.Icc 1 y, 1 / (n : ℝ) = ((harmonic y : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl (fun n _ => one_div _)
  have hstep6 : ((harmonic y : ℚ) : ℝ) ≤ 1 + Real.log y := harmonic_le_one_add_log y
  have hlogy : Real.log y ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos y with rfl | hpos
    · simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hyx)
  calc ∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      ≤ ∑ n ∈ Finset.Icc 2 y, 1 / ((n : ℝ) - 1) := hstep1
    _ ≤ ∑ n ∈ Finset.Icc 2 y, 2 * (1 / (n : ℝ)) := hstep2
    _ = 2 * ∑ n ∈ Finset.Icc 2 y, 1 / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ n ∈ Finset.Icc 1 y, 1 / (n : ℝ) := by linarith [hstep4]
    _ = 2 * ((harmonic y : ℚ) : ℝ) := by rw [hstep5]
    _ ≤ 2 * (1 + Real.log y) := by linarith [hstep6]
    _ ≤ 4 * Real.log x := by linarith

/-! ### Part 3 — work item (a): the Finding-4 rederivations (∃ B C pulled outside ∀ x)

`twinA1_hBV_W`/`twinA2_hBVagg_W` put `∃ B C` after `x`; the proof bodies below are their
VERBATIM copies (public ingredients only) with `B, C` obtained from the x-independent
`psi_BV_of_siegelWalfisz'` BEFORE the `∀ x` — legal, and exactly what the ∃-first
consumers (Part 6) need to choose `x₁ = x₁(B, C)`. -/

set_option linter.unusedVariables false in
/-- `twinA1_hBV_W` with `∃ B C` OUTSIDE the `∀ x` (Finding-4 rederivation; body verbatim). -/
theorem a12_hBV_A1 : ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
    ∀ (Qm a x z D P : ℕ) (ε Qlev : ℝ)
      (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
      (hPz : ∀ p ∈ P.primeFactors, p < z)
      (hPlow : ∀ p ∈ P.primeFactors, w0R ε ≤ (p : ℝ))
      (hx : 4 ≤ x) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
      (hwz : w0R ε ≤ (z : ℝ)) (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P)
      (hQma : Nat.Coprime Qm a) (hQlev : 1 ≤ Qlev) (hD : 1 ≤ D),
      (Qm : ℝ) * (Qlev * D) ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B →
      C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
          + 2 * Real.log x
              * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * D) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
        ≤ (x : ℝ) / (Real.log x) ^ 10 →
      rosserRemainder (twinA1SieveW Qm a x P hP hPodd) (Qlev * D)
        ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, ?_⟩
  intro Qm a x z D P ε Qlev hP hPodd hPz hPlow hx hε hw0 hwz hQm1 hQmP hQma hQlev hD
    hlevel hclose
  have hx2 : 2 ≤ x := by omega
  -- the split into two Q·d-modulus BV sums + the conversion sum
  have hsplit := rosserRemainderW_le_split Qm a x P hP hPodd hQm1 hQma hQmP hx
    (Qlev * (D : ℝ))
  -- the two dispDisc endpoint sums: image under d ↦ Qm·d ⊆ BV index set, then the BV bound
  have hbv1 := hbv x (x - 2) hx2 (by omega : x - 2 ≤ x)
  have hbv2 := hbv x (x / 2 - 1) hx2 (by omega : x / 2 - 1 ≤ x)
  have hS1 : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then dispDisc (x - 2) (Qm * d) else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDiscW_filtered_le_Icc Qm (x - 2) hQm1 hlevel) hbv1
  have hS2 : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then dispDisc (x / 2 - 1) (Qm * d) else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDiscW_filtered_le_Icc Qm (x / 2 - 1) hQm1 hlevel) hbv2
  -- the `∑ 1/φ(d)` bound via the V-ratio product (C1d, at the W instance — `nu` is defeq)
  have hb1 : (1 : ℝ) ≤ Qlev * (D : ℝ) := by
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    nlinarith [hQlev, hD1]
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (twinA1SieveW Qm a x P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hPlow p hp,
        by exact_mod_cast hPz p hp, twinA1_hnu P p hp⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  -- the conversion sum
  have hlogQD : 0 ≤ Real.log (Qlev * (D : ℝ)) := Real.log_nonneg hb1
  have hconvfac : 0 ≤ 2 * Real.log x
      * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3) := by
    have h0 : 0 ≤ Real.log x := Real.log_natCast_nonneg x
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hq : 0 ≤ Real.log (Qlev * (D : ℝ)) / Real.log 3 := div_nonneg hlogQD h3.le
    have hω : (0 : ℝ) ≤ (Qm.primeFactors.card : ℝ) := by positivity
    have hsum : 0 ≤ (Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3 := by
      linarith
    exact mul_nonneg (by positivity) hsum
  have hConv : (∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (D : ℝ) then convTerm x (Qm * d) else 0)
      ≤ 2 * Real.log x
          * ((Qm.primeFactors.card : ℝ) + Real.log (Qlev * (D : ℝ)) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε)) :=
    le_trans (convSumW_le Qm hP hPodd hQm1 hQmP hx hb1)
      (mul_le_mul_of_nonneg_left hMbound hconvfac)
  -- assemble
  linarith [hsplit, hS1, hS2, hConv, hclose]

set_option linter.unusedVariables false in
/-- `twinA2_hBVagg_W` with `∃ B C` OUTSIDE the `∀ x` (Finding-4 rederivation; body verbatim). -/
theorem a12_hBV_A2 : ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
    ∀ (Qm a x z y Dtot P : ℕ) (ε Qlev : ℝ)
      (hP : Squarefree P) (hPodd : ∀ q ∈ P.primeFactors, 3 ≤ q)
      (hPz : ∀ q ∈ P.primeFactors, q < z)
      (hPlow : ∀ q ∈ P.primeFactors, w0R ε ≤ (q : ℝ))
      (hx : 4 ≤ x) (hz3 : 3 ≤ z) (hε : 0 < ε) (hw0 : 3 ≤ w0R ε)
      (hwz : w0R ε ≤ (z : ℝ))
      (hQm1 : 1 ≤ Qm) (hQmP : Nat.Coprime Qm P) (hQma : Nat.Coprime Qm a)
      (hQmPr : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, Nat.Coprime Qm p)
      (hQlev : 1 ≤ Qlev) (hD1 : 1 ≤ Dtot),
      (Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B →
      C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
          + 2 * Real.log x
              * ((Qm.primeFactors.card : ℝ)
                  + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
              * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
              * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1))
        ≤ (x : ℝ) / (Real.log x) ^ 10 →
      ∑ p ∈ (Finset.Icc z y).filter Nat.Prime,
          rosserRemainder (twinA2SieveW Qm a x P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ))
        ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  obtain ⟨B, C, hB, hC, hbv⟩ :=
    psi_BV_of_siegelWalfisz' Salt.SW.siegelWalfisz_holds 11 (by norm_num)
  refine ⟨B, C, hB, hC, ?_⟩
  intro Qm a x z y Dtot P ε Qlev hP hPodd hPz hPlow hx hz3 hε hw0 hwz hQm1 hQmP hQma
    hQmPr hQlev hD1 hlevel hclose
  classical
  have hx2 : 2 ≤ x := by omega
  have hQlev0 : (0 : ℝ) ≤ Qlev := by linarith
  -- 1 ≤ BND := Qlev·(Dtot + y)
  have hBND1 : (1 : ℝ) ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
    have hD1R : (1 : ℝ) ≤ (Dtot : ℝ) := by exact_mod_cast hD1
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    nlinarith [hQlev, hD1R, hy0]
  -- the collapsed level bound: in-cut pairs satisfy p·d ≤ Qlev·(Dtot + y)
  have hpdB : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
      (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) →
      (p : ℝ) * (d : ℝ) ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
    intro p hpR d _hd hlt
    rw [Finset.mem_filter, Finset.mem_Icc] at hpR
    obtain ⟨⟨_hzp, hpy⟩, hpp⟩ := hpR
    have hppos : 0 < p := hpp.pos
    have hpposR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
    -- ℕ: p·⌈Dtot/p⌉ ≤ Dtot + p
    have hcd : p * cdiv Dtot p ≤ Dtot + p := by
      have h1 : (Dtot - 1) / p * p ≤ Dtot - 1 := Nat.div_mul_le_self _ _
      unfold cdiv
      calc p * ((Dtot - 1) / p + 1) = (Dtot - 1) / p * p + p := by ring
        _ ≤ Dtot + p := by omega
    have hcdR : (p : ℝ) * (cdiv Dtot p : ℝ) ≤ (Dtot : ℝ) + (p : ℝ) := by
      calc (p : ℝ) * (cdiv Dtot p : ℝ) = ((p * cdiv Dtot p : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((Dtot + p : ℕ) : ℝ) := by exact_mod_cast hcd
        _ = (Dtot : ℝ) + (p : ℝ) := by push_cast; ring
    have hpyR : (p : ℝ) ≤ (y : ℝ) := by exact_mod_cast hpy
    calc (p : ℝ) * (d : ℝ)
        ≤ (p : ℝ) * (Qlev * (cdiv Dtot p : ℝ)) :=
          mul_le_mul_of_nonneg_left hlt.le hpposR.le
      _ = Qlev * ((p : ℝ) * (cdiv Dtot p : ℝ)) := by ring
      _ ≤ Qlev * ((Dtot : ℝ) + (p : ℝ)) := mul_le_mul_of_nonneg_left hcdR hQlev0
      _ ≤ Qlev * ((Dtot : ℝ) + (y : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hQlev0
          linarith
  -- the modulus-level bound for the injection
  have hlev' : ∀ p ∈ (Finset.Icc z y).filter Nat.Prime, ∀ d ∈ P.divisors,
      (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) →
      ((Qm * (p * d) : ℕ) : ℝ) ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B := by
    intro p hpR d hd hlt
    have h1 := hpdB p hpR d hd hlt
    have hQm0 : (0 : ℝ) ≤ (Qm : ℝ) := Nat.cast_nonneg _
    calc ((Qm * (p * d) : ℕ) : ℝ) = (Qm : ℝ) * ((p : ℝ) * (d : ℝ)) := by push_cast; ring
      _ ≤ (Qm : ℝ) * (Qlev * ((Dtot : ℝ) + (y : ℝ))) := mul_le_mul_of_nonneg_left h1 hQm0
      _ ≤ Real.sqrt (x : ℝ) / (Real.log x) ^ B := hlevel
  -- the per-prime split, summed
  have hsum : (∑ p ∈ (Finset.Icc z y).filter Nat.Prime,
        rosserRemainder (twinA2SieveW Qm a x P p hP hPodd) (Qlev * (cdiv Dtot p : ℝ)))
      ≤ (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then dispDisc (x - 2) (Qm * (p * d)) else 0)
        + (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then dispDisc (x / 2 - 1) (Qm * (p * d)) else 0)
        + (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
            if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
            then convTerm x (Qm * (p * d)) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hpR
    have hpR' := hpR
    rw [Finset.mem_filter, Finset.mem_Icc] at hpR'
    obtain ⟨⟨hzp, _hpy⟩, hpp⟩ := hpR'
    have hp3 : 3 ≤ p := by omega
    have hpP : Nat.Coprime p P := (Nat.Prime.coprime_iff_not_dvd hpp).mpr (fun hpdvd =>
      absurd (hPz p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, hP.ne_zero⟩)) (by omega))
    exact rosserRemainderW2_le_split Qm a x P p hP hPodd hQm1 hQma hQmP
      (hQmPr p hpR) hpp hp3 hpP hx _
  -- the two dispDisc double sums via the injection + the unconditional BV
  have hbv1 := hbv x (x - 2) hx2 (by omega : x - 2 ≤ x)
  have hbv2 := hbv x (x / 2 - 1) hx2 (by omega : x / 2 - 1 ≤ x)
  have hS1 : (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
        then dispDisc (x - 2) (Qm * (p * d)) else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDiscW2_double_le_Icc Qm (x - 2) hQm1 hP.ne_zero hPz hlev') hbv1
  have hS2 : (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ)
        then dispDisc (x / 2 - 1) (Qm * (p * d)) else 0)
      ≤ C * x / (Real.log x) ^ (11 : ℝ) :=
    le_trans (dispDiscW2_double_le_Icc Qm (x / 2 - 1) hQm1 hP.ne_zero hPz hlev') hbv2
  -- the conversion double sum, then the `Σ 1/φ(d)` V-ratio bound (the A1W route)
  have hconv := convSumW2_le Qm hP hPodd hQm1 hPz hz3 hx hBND1 hpdB
  have hMbound : ∑ d ∈ P.divisors, (1 : ℝ) / (Nat.totient d)
      ≤ (1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε) := by
    have hvr := vratio_prod_le (twinA1SieveW Qm a x P hP hPodd) P.primeFactors hε.le hw0 hwz
      (w0R_threshold hε) (fun q hq => ⟨Nat.prime_of_mem_primeFactors hq, hPlow q hq,
        by exact_mod_cast hPz q hq, twinA1_hnu P q hq⟩)
    exact le_trans (sum_inv_totient_le_Winv hP hPodd) hvr
  have hSp0 : (0 : ℝ) ≤ ∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1) := by
    apply Finset.sum_nonneg
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have h3p : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hK0 : 0 ≤ 2 * Real.log x
      * ((Qm.primeFactors.card : ℝ)
          + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3) := by
    have h0 : 0 ≤ Real.log x := Real.log_natCast_nonneg x
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlogB : 0 ≤ Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) := Real.log_nonneg hBND1
    have hsum0 : 0 ≤ (Qm.primeFactors.card : ℝ)
        + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3 := by positivity
    exact mul_nonneg (by positivity) hsum0
  have hconv2 : (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, ∑ d ∈ P.divisors,
        if (d : ℝ) < Qlev * (cdiv Dtot p : ℝ) then convTerm x (Qm * (p * d)) else 0)
      ≤ 2 * Real.log x
          * ((Qm.primeFactors.card : ℝ)
              + Real.log (Qlev * ((Dtot : ℝ) + (y : ℝ))) / Real.log 3)
          * ((1 + ε) * Real.log (z : ℝ) / Real.log (w0R ε))
          * (∑ p ∈ (Finset.Icc z y).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
    refine le_trans hconv ?_
    apply mul_le_mul_of_nonneg_right _ hSp0
    exact mul_le_mul_of_nonneg_left hMbound hK0
  linarith [hsum, hS1, hS2, hconv2, hclose]

/-! ### Part 4 — work items (b)/(c): the A1 W-LEVEL and W-CLOSE rows

W-LEVEL margin: `Q·(Q·D) ≤ L²·x^{1/2−9/10⁵}` and `L^{B+2} ≤ x^{9/10⁵}` (polylog-beats-power),
so LHS·L^B ≤ x^{1/2} = √x.
W-CLOSE margin: third term ≤ 2L·(L+2L)·(2L) = 12L³ (ω(Q) ≤ Q ≤ L; log(QD) ≤ log x² = 2L;
log 3 ≥ 1; (1+ε)·log z ≤ 2L; log w₀ ≥ 1); then 2C·x/L¹¹ ≤ x/(2L¹⁰) at L ≥ 4C and
12L³ ≤ x/(2L¹⁰) ⟺ 24L¹³ ≤ x ⟸ L¹³ ≤ √x and 24 ≤ √x (both at log x ≥ 200). -/

theorem a12_level : ∀ B : ℝ, 0 ≤ B → ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (opQ : ℝ) ≤ Real.log x →
    (opQ : ℝ) * ((opQ : ℝ) * (opD x : ℝ)) ≤ Real.sqrt x / (Real.log x) ^ B := by
  intro B hB
  obtain ⟨x₂, h₂⟩ := a12_log_ge 1
  obtain ⟨x₃, h₃⟩ := a12_logpow_le_rpow (B + 2) (9 / 100000) (by linarith) (by norm_num)
  refine ⟨max x₂ x₃, ?_⟩
  intro x hx hQlog
  obtain ⟨hexpx, hlogx⟩ := h₂ x (by omega)
  have hpow := h₃ x (by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hL1 : (1 : ℝ) ≤ Real.log x := hlogx
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hD : (opD x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
    simp only [opD]
    exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have hQ0 : (0 : ℝ) ≤ (opQ : ℝ) := Nat.cast_nonneg _
  have hLB : (0 : ℝ) < (Real.log x) ^ B := Real.rpow_pos_of_pos hLpos B
  rw [le_div_iff₀ hLB]
  have hγnn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
    Real.rpow_nonneg hxpos.le _
  have step1 : (opQ : ℝ) * ((opQ : ℝ) * (opD x : ℝ))
      ≤ Real.log x * (Real.log x * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)) := by
    have hin : (opQ : ℝ) * (opD x : ℝ)
        ≤ Real.log x * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
      mul_le_mul hQlog hD (Nat.cast_nonneg _) (by linarith)
    exact mul_le_mul hQlog hin (mul_nonneg hQ0 (Nat.cast_nonneg _)) (by linarith)
  calc (opQ : ℝ) * ((opQ : ℝ) * (opD x : ℝ)) * (Real.log x) ^ B
      ≤ Real.log x * (Real.log x * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000))
          * (Real.log x) ^ B := mul_le_mul_of_nonneg_right step1 hLB.le
    _ = (Real.log x) ^ (B + 2) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
        rw [Real.rpow_add hLpos B 2, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        ring
    _ ≤ (x : ℝ) ^ ((9 : ℝ) / 100000) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
        mul_le_mul_of_nonneg_right hpow hγnn
    _ = (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hxpos,
          show (9 : ℝ) / 100000 + ((1 : ℝ) / 2 - 9 / 100000) = 1 / 2 by norm_num]
    _ = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow (x : ℝ)).symm

theorem a12_close : ∀ C : ℝ, 0 ≤ C → ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (opQ : ℝ) ≤ Real.log x →
    C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
        + 2 * Real.log x
            * ((opQ.primeFactors.card : ℝ) + Real.log ((opQ : ℝ) * (opD x)) / Real.log 3)
            * ((1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps))
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  intro C hC
  obtain ⟨x₂, h₂⟩ := a12_log_ge (max 200 (4 * C))
  obtain ⟨x₃, h₃⟩ := a12_logpow_le_rpow 13 (1 / 2) (by norm_num) (by norm_num)
  refine ⟨max x₂ x₃, ?_⟩
  intro x hx hQlog
  obtain ⟨hexpx, hlogx⟩ := h₂ x (by omega)
  have h13 := h₃ x (by omega)
  have hL200 : (200 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hlogx
  have hL4C : 4 * C ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hx201 : (201 : ℝ) ≤ (x : ℝ) := by
    have h := Real.add_one_le_exp (max (200 : ℝ) (4 * C))
    have h200 : (200 : ℝ) ≤ max 200 (4 * C) := le_max_left _ _
    linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have h13' : (Real.log x) ^ (13 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rwa [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h13
  have h11 : (Real.log x) ^ (11 : ℝ) = (Real.log x) ^ (11 : ℕ) := by
    rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h11]
  -- Term A: C·x/L¹¹ ≤ (x/L¹⁰)/4 at L ≥ 4C
  have htermA : C * (x : ℝ) / (Real.log x) ^ (11 : ℕ)
      ≤ (x : ℝ) / (Real.log x) ^ 10 / 4 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hkeyL : C * (x : ℝ) * ((Real.log x) ^ 10 * 4)
        = (4 * C) * ((x : ℝ) * (Real.log x) ^ 10) := by ring
    have hkeyR : (x : ℝ) * (Real.log x) ^ (11 : ℕ)
        = Real.log x * ((x : ℝ) * (Real.log x) ^ 10) := by ring
    rw [hkeyL, hkeyR]
    exact mul_le_mul_of_nonneg_right hL4C (by positivity)
  -- the third term ≤ 12·L³
  have hQx : (opQ : ℝ) ≤ (x : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hDle : (opD x : ℝ) ≤ (x : ℝ) := by
    have h1 : (opD x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
      simp only [opD]
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hD1 : 1 ≤ opD x := by
    simp only [opD]
    apply Nat.le_floor
    rw [Nat.cast_one]
    calc (1 : ℝ) = (x : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hQD1 : (1 : ℝ) ≤ (opQ : ℝ) * (opD x : ℝ) := by
    have hQ2R : (2 : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast a12_Q2
    have hD1R : (1 : ℝ) ≤ (opD x : ℝ) := by exact_mod_cast hD1
    nlinarith
  have hlogQD_nn : 0 ≤ Real.log ((opQ : ℝ) * (opD x)) := Real.log_nonneg hQD1
  have hlogQD : Real.log ((opQ : ℝ) * (opD x)) ≤ 2 * Real.log x := by
    have hle : (opQ : ℝ) * (opD x : ℝ) ≤ (x : ℝ) * (x : ℝ) :=
      mul_le_mul hQx hDle (by positivity) hxpos.le
    calc Real.log ((opQ : ℝ) * (opD x))
        ≤ Real.log ((x : ℝ) * (x : ℝ)) := Real.log_le_log (by linarith) hle
      _ = Real.log x + Real.log x := Real.log_mul (ne_of_gt hxpos) (ne_of_gt hxpos)
      _ = 2 * Real.log x := by ring
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hexp1 : Real.exp 1 ≤ 3 := by linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) hexp1
  have hωle : (opQ.primeFactors.card : ℝ) ≤ (opQ : ℝ) := by
    exact_mod_cast a12_omega_le opQ
  have hf2 : (opQ.primeFactors.card : ℝ) + Real.log ((opQ : ℝ) * (opD x)) / Real.log 3
      ≤ 3 * Real.log x := by
    have hd : Real.log ((opQ : ℝ) * (opD x)) / Real.log 3 ≤ 2 * Real.log x :=
      le_trans (div_le_self hlogQD_nn hlog3) hlogQD
    linarith
  have hf2nn : 0 ≤ (opQ.primeFactors.card : ℝ)
      + Real.log ((opQ : ℝ) * (opD x)) / Real.log 3 := by
    have hd : 0 ≤ Real.log ((opQ : ℝ) * (opD x)) / Real.log 3 :=
      div_nonneg hlogQD_nn (by linarith)
    positivity
  have hzleR : (opZ x : ℝ) ≤ (x : ℝ) := by
    have h1 : (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
      simp only [opZ]
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 8) ≤ (x : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hzle : Real.log ((opZ x : ℕ) : ℝ) ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos (opZ x) with h0 | hposz
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast hposz) hzleR
  have hznn : (0 : ℝ) ≤ Real.log ((opZ x : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have h1eps_nn : (0 : ℝ) ≤ 1 + opEps := by linarith [a12_eps_pos]
  have h1eps2 : (1 : ℝ) + opEps ≤ 2 := by linarith [a12_eps_le_1000]
  have hnumnn : 0 ≤ (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) := mul_nonneg h1eps_nn hznn
  have hf3 : (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps)
      ≤ 2 * Real.log x := by
    have hnum : (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) ≤ 2 * Real.log x := by
      calc (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ)
          ≤ 2 * Real.log ((opZ x : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h1eps2 hznn
        _ ≤ 2 * Real.log x := by linarith
    exact le_trans (div_le_self hnumnn a12_logw0_ge_one) hnum
  have hf3nn : 0 ≤ (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps) :=
    div_nonneg hnumnn (by linarith [a12_logw0_ge_one])
  have hthird : 2 * Real.log x
      * ((opQ.primeFactors.card : ℝ) + Real.log ((opQ : ℝ) * (opD x)) / Real.log 3)
      * ((1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps))
      ≤ 12 * (Real.log x) ^ 3 := by
    have h2L : (0 : ℝ) ≤ 2 * Real.log x := by linarith
    have hstep1 : 2 * Real.log x
        * ((opQ.primeFactors.card : ℝ) + Real.log ((opQ : ℝ) * (opD x)) / Real.log 3)
        ≤ 2 * Real.log x * (3 * Real.log x) := mul_le_mul_of_nonneg_left hf2 h2L
    have hstepnn : (0 : ℝ) ≤ 2 * Real.log x * (3 * Real.log x) := by positivity
    calc 2 * Real.log x
        * ((opQ.primeFactors.card : ℝ) + Real.log ((opQ : ℝ) * (opD x)) / Real.log 3)
        * ((1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps))
        ≤ 2 * Real.log x * (3 * Real.log x) * (2 * Real.log x) :=
          mul_le_mul hstep1 hf3 hf3nn hstepnn
      _ = 12 * (Real.log x) ^ 3 := by ring
  -- Term B: 12·L³ ≤ (x/L¹⁰)/2 ⟺ 24·L¹³ ≤ x
  have htermB : 12 * (Real.log x) ^ 3 ≤ (x : ℝ) / (Real.log x) ^ 10 / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have h24 : (24 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      have hh : Real.exp 100 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.rpow_def_of_pos hxpos]
        apply Real.exp_le_exp.mpr
        linarith
      nlinarith [Real.add_one_le_exp (100 : ℝ)]
    have hsq : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
      rw [← Real.rpow_add hxpos, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
    calc 12 * (Real.log x) ^ 3 * ((Real.log x) ^ 10 * 2)
        = 24 * (Real.log x) ^ (13 : ℕ) := by ring
      _ ≤ 24 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left h13' (by norm_num)
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h24 (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) := hsq
  linarith [htermA, hthird, htermB]

/-! ### Part 5 — work item (d): the A2 analogues (level at `Q·(Q·(D+y))`; close with `Σ 1/(p−1)`)

W2-LEVEL margin: `D + y ≤ 2D` (from `hyD`), and `2·L^{B+2} ≤ x^{9/2·10⁵}·x^{9/2·10⁵}
= x^{9/10⁵}` at `log x ≥ 25000` (so `x^{9/2·10⁵} ≥ e^{9/8} ≥ 2`).
W2-CLOSE margin: the extra factor `Σ_p 1/(p−1) ≤ 4L` (harmonic), `log(Q(D+y)) ≤ log x³ = 3L`,
so third ≤ 2L·4L·2L·4L = 64L⁴ and `128·L¹⁴ ≤ x` ⟸ `L¹⁴ ≤ √x`, `128 ≤ (27/10)⁵ ≤ e¹⁰⁰ ≤ √x`. -/

theorem a12_level2 : ∀ B : ℝ, 0 ≤ B → ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (opQ : ℝ) ≤ Real.log x → opY x ≤ opD x →
    (opQ : ℝ) * ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ)))
      ≤ Real.sqrt x / (Real.log x) ^ B := by
  intro B hB
  obtain ⟨x₂, h₂⟩ := a12_log_ge 25000
  obtain ⟨x₃, h₃⟩ := a12_logpow_le_rpow (B + 2) (9 / 200000) (by linarith) (by norm_num)
  refine ⟨max x₂ x₃, ?_⟩
  intro x hx hQlog hyD
  obtain ⟨hexpx, hlogx⟩ := h₂ x (by omega)
  have hpow := h₃ x (by omega)
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hD : (opD x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
    simp only [opD]
    exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have hyDR : (opY x : ℝ) ≤ (opD x : ℝ) := by exact_mod_cast hyD
  have hsum2 : (opD x : ℝ) + (opY x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
    linarith
  have h2small : (2 : ℝ) ≤ (x : ℝ) ^ ((9 : ℝ) / 200000) := by
    have he : Real.exp (9 / 8) ≤ (x : ℝ) ^ ((9 : ℝ) / 200000) := by
      rw [Real.rpow_def_of_pos hxpos]
      apply Real.exp_le_exp.mpr
      nlinarith [hlogx]
    nlinarith [Real.add_one_le_exp ((9 : ℝ) / 8)]
  have hLB : (0 : ℝ) < (Real.log x) ^ B := Real.rpow_pos_of_pos hLpos B
  rw [le_div_iff₀ hLB]
  have hγnn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
    Real.rpow_nonneg hxpos.le _
  have hDy0 : (0 : ℝ) ≤ (opD x : ℝ) + (opY x : ℝ) := by positivity
  have step1 : (opQ : ℝ) * ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ)))
      ≤ Real.log x * (Real.log x * (2 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000))) := by
    have hin : (opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))
        ≤ Real.log x * (2 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)) :=
      mul_le_mul hQlog hsum2 hDy0 (by linarith)
    exact mul_le_mul hQlog hin (mul_nonneg (Nat.cast_nonneg _) hDy0) (by linarith)
  calc (opQ : ℝ) * ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) * (Real.log x) ^ B
      ≤ Real.log x * (Real.log x * (2 * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)))
          * (Real.log x) ^ B := mul_le_mul_of_nonneg_right step1 hLB.le
    _ = 2 * ((Real.log x) ^ (B + 2) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)) := by
        rw [Real.rpow_add hLpos B 2, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        ring
    _ ≤ 2 * ((x : ℝ) ^ ((9 : ℝ) / 200000) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)) := by
        have h := mul_le_mul_of_nonneg_right hpow hγnn
        linarith
    _ ≤ (x : ℝ) ^ ((9 : ℝ) / 200000)
          * ((x : ℝ) ^ ((9 : ℝ) / 200000) * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000)) := by
        have hnn : (0 : ℝ) ≤ (x : ℝ) ^ ((9 : ℝ) / 200000)
            * (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
          mul_nonneg (Real.rpow_nonneg hxpos.le _) hγnn
        exact mul_le_mul_of_nonneg_right h2small hnn
    _ = (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos,
          show (9 : ℝ) / 200000 + (9 / 200000 + ((1 : ℝ) / 2 - 9 / 100000)) = 1 / 2
            by norm_num]
    _ = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow (x : ℝ)).symm

theorem a12_close2 : ∀ C : ℝ, 0 ≤ C → ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (opQ : ℝ) ≤ Real.log x →
    C * (x : ℝ) / (Real.log x) ^ (11 : ℝ) + C * (x : ℝ) / (Real.log x) ^ (11 : ℝ)
        + 2 * Real.log x
            * ((opQ.primeFactors.card : ℝ)
                + Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3)
            * ((1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps))
            * (∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime, 1 / ((p : ℝ) - 1))
      ≤ (x : ℝ) / (Real.log x) ^ 10 := by
  intro C hC
  obtain ⟨x₂, h₂⟩ := a12_log_ge (max 200 (4 * C))
  obtain ⟨x₃, h₃⟩ := a12_logpow_le_rpow 14 (1 / 2) (by norm_num) (by norm_num)
  refine ⟨max x₂ x₃, ?_⟩
  intro x hx hQlog
  obtain ⟨hexpx, hlogx⟩ := h₂ x (by omega)
  have h14 := h₃ x (by omega)
  have hL200 : (200 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hlogx
  have hL4C : 4 * C ≤ Real.log x := le_trans (le_max_right _ _) hlogx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexpx
  have hx201 : (201 : ℝ) ≤ (x : ℝ) := by
    have h := Real.add_one_le_exp (max (200 : ℝ) (4 * C))
    have h200 : (200 : ℝ) ≤ max 200 (4 * C) := le_max_left _ _
    linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have h14' : (Real.log x) ^ (14 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rwa [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h14
  have h11 : (Real.log x) ^ (11 : ℝ) = (Real.log x) ^ (11 : ℕ) := by
    rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h11]
  -- Term A (as in the A1 close row)
  have htermA : C * (x : ℝ) / (Real.log x) ^ (11 : ℕ)
      ≤ (x : ℝ) / (Real.log x) ^ 10 / 4 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hkeyL : C * (x : ℝ) * ((Real.log x) ^ 10 * 4)
        = (4 * C) * ((x : ℝ) * (Real.log x) ^ 10) := by ring
    have hkeyR : (x : ℝ) * (Real.log x) ^ (11 : ℕ)
        = Real.log x * ((x : ℝ) * (Real.log x) ^ 10) := by ring
    rw [hkeyL, hkeyR]
    exact mul_le_mul_of_nonneg_right hL4C (by positivity)
  -- the scale bounds
  have hQx : (opQ : ℝ) ≤ (x : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hDle : (opD x : ℝ) ≤ (x : ℝ) := by
    have h1 : (opD x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) := by
      simp only [opD]
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) ≤ (x : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hyle : (opY x : ℝ) ≤ (x : ℝ) := by
    have h1 : (opY x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      simp only [opY]
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hD1 : 1 ≤ opD x := by
    simp only [opD]
    apply Nat.le_floor
    rw [Nat.cast_one]
    calc (1 : ℝ) = (x : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hQDy1 : (1 : ℝ) ≤ (opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ)) := by
    have hQ2R : (2 : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast a12_Q2
    have hD1R : (1 : ℝ) ≤ (opD x : ℝ) := by exact_mod_cast hD1
    have hy0 : (0 : ℝ) ≤ (opY x : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hlogQDy_nn : 0 ≤ Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) :=
    Real.log_nonneg hQDy1
  have hlogQDy : Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) ≤ 3 * Real.log x := by
    have hle : (opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ)) ≤ (x : ℝ) * ((x : ℝ) * (x : ℝ)) := by
      have hDy : (opD x : ℝ) + (opY x : ℝ) ≤ (x : ℝ) * (x : ℝ) := by nlinarith
      exact mul_le_mul hQx hDy (by positivity) hxpos.le
    calc Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ)))
        ≤ Real.log ((x : ℝ) * ((x : ℝ) * (x : ℝ))) := Real.log_le_log (by linarith) hle
      _ = Real.log x + (Real.log x + Real.log x) := by
          rw [Real.log_mul (ne_of_gt hxpos) (by positivity),
            Real.log_mul (ne_of_gt hxpos) (ne_of_gt hxpos)]
      _ = 3 * Real.log x := by ring
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hexp1 : Real.exp 1 ≤ 3 := by linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) hexp1
  have hωle : (opQ.primeFactors.card : ℝ) ≤ (opQ : ℝ) := by
    exact_mod_cast a12_omega_le opQ
  have hf2 : (opQ.primeFactors.card : ℝ)
      + Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3
      ≤ 4 * Real.log x := by
    have hd : Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3
        ≤ 3 * Real.log x := le_trans (div_le_self hlogQDy_nn hlog3) hlogQDy
    linarith
  have hf2nn : 0 ≤ (opQ.primeFactors.card : ℝ)
      + Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3 := by
    have hd : 0 ≤ Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3 :=
      div_nonneg hlogQDy_nn (by linarith)
    positivity
  have hzleR : (opZ x : ℝ) ≤ (x : ℝ) := by
    have h1 : (opZ x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
      simp only [opZ]
      exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    have h2 : (x : ℝ) ^ ((1 : ℝ) / 8) ≤ (x : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hzle : Real.log ((opZ x : ℕ) : ℝ) ≤ Real.log x := by
    rcases Nat.eq_zero_or_pos (opZ x) with h0 | hposz
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast hposz) hzleR
  have hznn : (0 : ℝ) ≤ Real.log ((opZ x : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have h1eps_nn : (0 : ℝ) ≤ 1 + opEps := by linarith [a12_eps_pos]
  have h1eps2 : (1 : ℝ) + opEps ≤ 2 := by linarith [a12_eps_le_1000]
  have hnumnn : 0 ≤ (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) := mul_nonneg h1eps_nn hznn
  have hf3 : (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps)
      ≤ 2 * Real.log x := by
    have hnum : (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) ≤ 2 * Real.log x := by
      calc (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ)
          ≤ 2 * Real.log ((opZ x : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h1eps2 hznn
        _ ≤ 2 * Real.log x := by linarith
    exact le_trans (div_le_self hnumnn a12_logw0_ge_one) hnum
  have hf3nn : 0 ≤ (1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps) :=
    div_nonneg hnumnn (by linarith [a12_logw0_ge_one])
  -- the aggregated density factor: Σ 1/(p−1) ≤ 4·L (harmonic route)
  have hyx : opY x ≤ x := by
    exact_mod_cast le_trans hyle (le_refl (x : ℝ))
  have hS4L : ∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime, 1 / ((p : ℝ) - 1)
      ≤ 4 * Real.log x := a12_primeInv_le (opZ x) (opY x) x hyx hL1
  have hSnn : (0 : ℝ)
      ≤ ∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime, 1 / ((p : ℝ) - 1) := by
    apply Finset.sum_nonneg
    intro p hp
    rw [Finset.mem_filter] at hp
    have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  -- the third term ≤ 64·L⁴
  have hthird : 2 * Real.log x
      * ((opQ.primeFactors.card : ℝ)
          + Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3)
      * ((1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps))
      * (∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime, 1 / ((p : ℝ) - 1))
      ≤ 64 * (Real.log x) ^ 4 := by
    have h2L : (0 : ℝ) ≤ 2 * Real.log x := by linarith
    have hstep1 : 2 * Real.log x
        * ((opQ.primeFactors.card : ℝ)
            + Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3)
        ≤ 2 * Real.log x * (4 * Real.log x) := mul_le_mul_of_nonneg_left hf2 h2L
    have hstep1nn : (0 : ℝ) ≤ 2 * Real.log x * (4 * Real.log x) := by positivity
    have hstep2 : 2 * Real.log x
        * ((opQ.primeFactors.card : ℝ)
            + Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3)
        * ((1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps))
        ≤ 2 * Real.log x * (4 * Real.log x) * (2 * Real.log x) :=
      mul_le_mul hstep1 hf3 hf3nn hstep1nn
    have hstep2nn : (0 : ℝ) ≤ 2 * Real.log x * (4 * Real.log x) * (2 * Real.log x) := by
      positivity
    calc 2 * Real.log x
        * ((opQ.primeFactors.card : ℝ)
            + Real.log ((opQ : ℝ) * ((opD x : ℝ) + (opY x : ℝ))) / Real.log 3)
        * ((1 + opEps) * Real.log ((opZ x : ℕ) : ℝ) / Real.log (w0R opEps))
        * (∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime, 1 / ((p : ℝ) - 1))
        ≤ 2 * Real.log x * (4 * Real.log x) * (2 * Real.log x) * (4 * Real.log x) :=
          mul_le_mul hstep2 hS4L hSnn hstep2nn
      _ = 64 * (Real.log x) ^ 4 := by ring
  -- Term B: 64·L⁴ ≤ (x/L¹⁰)/2 ⟺ 128·L¹⁴ ≤ x
  have htermB : 64 * (Real.log x) ^ 4 ≤ (x : ℝ) / (Real.log x) ^ 10 / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have h128 : (128 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      have hh : Real.exp 100 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.rpow_def_of_pos hxpos]
        apply Real.exp_le_exp.mpr
        linarith
      have hp5 : (128 : ℝ) ≤ ((27 : ℝ) / 10) ^ (5 : ℕ) := by norm_num
      have hp100 : ((27 : ℝ) / 10) ^ (5 : ℕ) ≤ ((27 : ℝ) / 10) ^ (100 : ℕ) :=
        pow_le_pow_right₀ (by norm_num) (by norm_num)
      have hexp := a12_pow27_le_exp 100
      push_cast at hexp
      linarith
    have hsq : (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) = (x : ℝ) := by
      rw [← Real.rpow_add hxpos, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
    calc 64 * (Real.log x) ^ 4 * ((Real.log x) ^ 10 * 2)
        = 128 * (Real.log x) ^ (14 : ℕ) := by ring
      _ ≤ 128 * (x : ℝ) ^ ((1 : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left h14' (by norm_num)
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h128 (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) := hsq
  linarith [htermA, hthird, htermB]

/-! ### Part 6 — work item (e): the per-prime A2 operating rows

Margins: `p ≤ y ≤ z·y ≤ D − 1` gives `⌈D/p⌉ ≥ 2`; `(z−1)·p ≤ z·y ≤ D − 1` gives
`⌈D/p⌉ ≥ z`, hence `logRatio z ⌈D/p⌉ ≥ 1` (true value `≥ 1.33`; only `≥ 1` is owed). -/

theorem a12_cdiv2 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∀ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime, 2 ≤ cdiv (opD x) p := by
  obtain ⟨x₁, h₁⟩ := a12_zyD
  refine ⟨x₁, ?_⟩
  intro x hx p hp
  obtain ⟨hz3, hzyD⟩ := h₁ x hx
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hzp, hpy⟩, hpp⟩ := hp
  have hppos : 0 < p := hpp.pos
  have hyz : opY x ≤ opZ x * opY x := Nat.le_mul_of_pos_left _ (by omega)
  have h1 : 1 ≤ (opD x - 1) / p := by
    rw [Nat.le_div_iff_mul_le hppos]
    omega
  have hcd : cdiv (opD x) p = (opD x - 1) / p + 1 := rfl
  omega

theorem a12_cdivStop : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∀ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
      1 ≤ logRatio (opZ x) (cdiv (opD x) p) := by
  obtain ⟨x₁, h₁⟩ := a12_zyD
  refine ⟨x₁, ?_⟩
  intro x hx p hp
  obtain ⟨hz3, hzyD⟩ := h₁ x hx
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hzp, hpy⟩, hpp⟩ := hp
  have hppos : 0 < p := hpp.pos
  have hstep : opZ x - 1 ≤ (opD x - 1) / p := by
    rw [Nat.le_div_iff_mul_le hppos]
    have hmul : (opZ x - 1) * p ≤ opZ x * opY x := Nat.mul_le_mul (by omega) hpy
    omega
  have hcz : opZ x ≤ cdiv (opD x) p := by
    have hcd : cdiv (opD x) p = (opD x - 1) / p + 1 := rfl
    omega
  have hz1R : (1 : ℝ) < ((opZ x : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < opZ x)
  have hlogz : (0 : ℝ) < Real.log (opZ x) := Real.log_pos hz1R
  have hle : Real.log ((opZ x : ℕ) : ℝ) ≤ Real.log ((cdiv (opD x) p : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < opZ x)) (by exact_mod_cast hcz)
  rw [logRatio, le_div_iff₀ hlogz]
  linarith

/-! ### Part 7 — work item (f): the terminal `hA1`/`hA2` slot discharges

Chain shapes: the Part F / Part G examples of `TwinA1W`/`TwinA2W`, with the two named rows
supplied by Parts 4/5, the per-prime rows by Part 6, `h4 := h4_cond_of_base`,
`hstepWPC := stepHypWPC_sharpB`, and the Finding-4 `∃ B C`-first BV forms of Part 3. -/

set_option linter.unusedVariables false in
/-- **The `hA1` slot of `chen_of_hypotheses_W` at the frozen operating point.** -/
theorem a12_hA1 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∀ (hP : Squarefree (opP x)) (hPodd : ∀ p ∈ (opP x).primeFactors, 3 ≤ p)
      (hPz : ∀ p ∈ (opP x).primeFactors, p < opZ x)
      (hPlow : ∀ p ∈ (opP x).primeFactors, w0R opEps ≤ (p : ℝ))
      (hQP : Nat.Coprime opQ (opP x))
      (hQma : Nat.Coprime opQ opA)
      (hz3 : 3 ≤ opZ x) (hzD : opZ x ≤ opD x) (hD1 : 1 ≤ opD x)
      (hStop : 2 ≤ logRatio (opZ x) (opD x))
      (hwz : w0R opEps ≤ ((opZ x : ℕ) : ℝ))
      (hQ2 : 2 ≤ opQ) (hQlog : (opQ : ℝ) ≤ Real.log x),
    (twinA1SieveW opQ opA x (opP x) hP hPodd).totalMass *
        (Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) hP hPodd) *
          (fchain (maxDepth (twinA1SieveW opQ opA x (opP x) hP hPodd))
              (logRatio (opZ x) (opD x))
            - opEps * CsharpB opEps * Real.exp 2 * hBJS (logRatio (opZ x) (opD x))))
      - (x : ℝ) / (Real.log x) ^ 10
      - Real.sqrt x * (Nat.log 2 x : ℝ) * Real.log x
    ≤ A1primeSumW opQ opA x (opP x) := by
  obtain ⟨B, C, hB, hC, hbvfun⟩ := a12_hBV_A1
  obtain ⟨x₂, hlev⟩ := a12_level B hB
  obtain ⟨x₃, hcl⟩ := a12_close C hC
  refine ⟨max (max x₂ x₃) 4, ?_⟩
  intro x hx hP hPodd hPz hPlow hQP hQma hz3 hzD hD1 hStop hwz hQ2 hQlog
  have hx4 : 4 ≤ x := by omega
  have hrow1 := hlev x (by omega) hQlog
  have hrow2 := hcl x (by omega) hQlog
  have hε : (0 : ℝ) < opEps := a12_eps_pos
  have hw0 : (3 : ℝ) ≤ w0R opEps := a12_hw0
  have hQm1 : 1 ≤ opQ := by omega
  have hQlevR : (1 : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast hQm1
  have hz2 : 2 ≤ opZ x := by omega
  -- deliverable 4 (Finding-4 form): the BV row
  have hBV := hbvfun opQ opA x (opZ x) (opD x) (opP x) opEps ((opQ : ℝ)) hP hPodd hPz hPlow
    hx4 hε hw0 hwz hQm1 hQP hQma hQlevR hD1 hrow1 hrow2
  -- deliverable 3: the supplier lower bound at the AP-restricted coprime Λ-sum
  have hsup := twin_A1_lower_B_W opQ opA x (opZ x) (opD x) (opP x) opEps (1 + opEps)
    ((opQ : ℝ)) hP hPodd hPz hPlow hz2 hzD hD1 hStop hε hw0 (le_refl _) a12_eps_lt_249
    (stepHypWPC_sharpB opEps hε.le a12_eps_le_1000)
    (h4_cond_of_base opEps (1 + opEps) hε.le (le_refl _)) hQlevR hBV
  -- deliverable 5: the Finding-6 prime-power bridge
  have hbridge := A1primeSumW_bridge opQ opA x (opP x) hx4
  linarith [hsup, hbridge]

set_option linter.unusedVariables false in
/-- **The `hA2` slot of `chen_of_hypotheses_W` at the frozen operating point.** -/
theorem a12_hA2 : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∀ (hP : Squarefree (opP x)) (hPodd : ∀ p ∈ (opP x).primeFactors, 3 ≤ p)
      (hPz : ∀ p ∈ (opP x).primeFactors, p < opZ x)
      (hPlow : ∀ p ∈ (opP x).primeFactors, w0R opEps ≤ (p : ℝ))
      (hQP : Nat.Coprime opQ (opP x))
      (hQma : Nat.Coprime opQ opA)
      (hQfull : ∀ q, q.Prime → q < opW' → q ∣ opQ)
      (hPfull' : ∀ q, q.Prime → opW' ≤ q → q < opZ x → q ∣ opP x)
      (hQa2 : Nat.Coprime opQ (opA + 2))
      (hQmPr : ∀ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime, Nat.Coprime opQ p)
      (hz3 : 3 ≤ opZ x) (hD1 : 1 ≤ opD x)
      (hwz : w0R opEps ≤ ((opZ x : ℕ) : ℝ))
      (hQ2 : 2 ≤ opQ) (hQlog : (opQ : ℝ) ≤ Real.log x)
      (hyD : opY x ≤ opD x),
    omegaPrimeSumW opQ opA x (opP x) (opY x)
      ≤ ((twinA1SieveW opQ opA x (opP x) hP hPodd).totalMass
            * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) hP hPodd))
          * (A2grid ((Finset.Icc (opZ x) (opY x)).filter Nat.Prime) (opZ x) (opD x)
                (fun p => maxDepth (twinA2SieveW opQ opA x (opP x) p hP hPodd))
              + ∑ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
                  (1 / ((p : ℝ) - 1))
                    * (opEps * CsharpB opEps * Real.exp 2
                        * hBJS (logRatio (opZ x) (cdiv (opD x) p))))
        + (x : ℝ) / (Real.log x) ^ 10 := by
  obtain ⟨B, C, hB, hC, hbvfun⟩ := a12_hBV_A2
  obtain ⟨x₂, hlev⟩ := a12_level2 B hB
  obtain ⟨x₃, hcl⟩ := a12_close2 C hC
  obtain ⟨x₄, hcd2⟩ := a12_cdiv2
  obtain ⟨x₅, hcds⟩ := a12_cdivStop
  refine ⟨max (max (max x₂ x₃) (max x₄ x₅)) 4, ?_⟩
  intro x hx hP hPodd hPz hPlow hQP hQma hQfull hPfull' hQa2 hQmPr hz3 hD1 hwz hQ2
    hQlog hyD
  have hx4 : 4 ≤ x := by omega
  have hrow1 := hlev x (by omega) hQlog hyD
  have hrow2 := hcl x (by omega) hQlog
  have hD2 := hcd2 x (by omega)
  have hStopP := hcds x (by omega)
  have hε : (0 : ℝ) < opEps := a12_eps_pos
  have hw0 : (3 : ℝ) ≤ w0R opEps := a12_hw0
  have hQm1 : 1 ≤ opQ := by omega
  have hQlevR : (1 : ℝ) ≤ (opQ : ℝ) := by exact_mod_cast hQm1
  classical
  -- deliverable 2: the carrier identification
  have hdecomp := omegaPrimeSumW_decomp (x := x) (y := opY x) (z := opZ x)
    hQfull hPfull' hQa2
  -- slack nonnegativity (CsharpB ≥ 0 at ε < 1/249; hBJS > 0)
  have hCs : 0 ≤ CsharpB opEps := by
    rw [CsharpB]
    apply div_nonneg (by norm_num)
    have h := chSharpB_lt_one a12_eps_lt_249
    linarith
  have hslacknn : ∀ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
      0 ≤ opEps * CsharpB opEps * Real.exp 2
          * hBJS (logRatio (opZ x) (cdiv (opD x) p)) := fun p _ =>
    mul_nonneg (mul_nonneg (mul_nonneg hε.le hCs) (Real.exp_pos 2).le)
      (hBJS_pos (logRatio (opZ x) (cdiv (opD x) p))).le
  -- deliverables 1+3: the per-prime supplier bounds (twin_A2_upper's hper slot)
  have hper : ∀ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
      A2pW opQ opA x (opP x) p
        ≤ ((twinA2SieveW opQ opA x (opP x) p hP hPodd).totalMass
              * Salt.BrunLower.W (twinA2SieveW opQ opA x (opP x) p hP hPodd))
            * (Fchain (maxDepth (twinA2SieveW opQ opA x (opP x) p hP hPodd))
                  (logRatio (opZ x) (cdiv (opD x) p))
                + opEps * CsharpB opEps * Real.exp 2
                    * hBJS (logRatio (opZ x) (cdiv (opD x) p)))
          + rosserRemainder (twinA2SieveW opQ opA x (opP x) p hP hPodd)
              ((opQ : ℝ) * (cdiv (opD x) p : ℝ)) := by
    intro p hp
    have hp' := hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp'
    exact le_trans (A2pW_le_siftedSumW opQ opA x (opP x) p hP hPodd)
      (twin_A2_per_prime_W opQ opA x (opP x) p (opZ x) (cdiv (opD x) p) opEps (1 + opEps)
        ((opQ : ℝ)) hP hPodd hPz hPlow hp'.2.one_lt.le (hD2 p hp) hQlevR hε hw0 (le_refl _)
        a12_eps_lt_249 (stepHypWPC_sharpB opEps hε.le a12_eps_le_1000)
        (h4_cond_of_base opEps (1 + opEps) hε.le (le_refl _)) (hStopP p hp))
  -- deliverable 4: the density coefficient (twin_A2_upper's hcoef slot)
  have hcoef : ∀ p ∈ (Finset.Icc (opZ x) (opY x)).filter Nat.Prime,
      (twinA2SieveW opQ opA x (opP x) p hP hPodd).totalMass
          * Salt.BrunLower.W (twinA2SieveW opQ opA x (opP x) p hP hPodd)
        ≤ ((twinA1SieveW opQ opA x (opP x) hP hPodd).totalMass
            * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) hP hPodd))
            * (1 / ((p : ℝ) - 1)) :=
    fun p _ => twinA2W_hcoef opQ opA x (opP x) p hP hPodd
  -- the aggregation keystone
  have hupper := twin_A2_upper
    (Λmass := (twinA1SieveW opQ opA x (opP x) hP hPodd).totalMass)
    (V := Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) hP hPodd))
    ((Finset.Icc (opZ x) (opY x)).filter Nat.Prime) (opZ x) (opD x)
    (fun p => A2pW opQ opA x (opP x) p)
    (fun p => (twinA2SieveW opQ opA x (opP x) p hP hPodd).totalMass
        * Salt.BrunLower.W (twinA2SieveW opQ opA x (opP x) p hP hPodd))
    (fun p => rosserRemainder (twinA2SieveW opQ opA x (opP x) p hP hPodd)
        ((opQ : ℝ) * (cdiv (opD x) p : ℝ)))
    (fun p => opEps * CsharpB opEps * Real.exp 2
        * hBJS (logRatio (opZ x) (cdiv (opD x) p)))
    (fun p => maxDepth (twinA2SieveW opQ opA x (opP x) p hP hPodd))
    hslacknn hper hcoef
  -- deliverable 5 (Finding-4 form): the aggregated BV row
  have hagg := hbvfun opQ opA x (opZ x) (opY x) (opD x) (opP x) opEps ((opQ : ℝ)) hP hPodd
    hPz hPlow hx4 hz3 hε hw0 hwz hQm1 hQP hQma hQmPr hQlevR hD1 hrow1 hrow2
  -- compose
  rw [hdecomp]
  linarith [hupper, hagg]

-- END FRAGMENT A1A2

end Salt.Chen
