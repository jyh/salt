/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Lemma53
import Salt.Maynard.TensorA1
import Salt.Maynard.HOmit
import Salt.Maynard.S2DiagRestricted
import Salt.Maynard.LamBoundSharp

/-!
# Node A (V_abs) — the pointwise bound on the restricted contraction `Vₘ`

Design: `docs/blueprints/s2-inner-design.md`, Node A.  For the concrete tensor
weight `y = yTensor` and any `v` with `vₘ = 1`,

  `|Vₘ(v)| ≤ 2·B₁·∏_{i≠m} f₀(vᵢ)·vᵢ/φ(vᵢ)² ≤ 2·B₁·∏_{i≠m} f₀(vᵢ)/g(vᵢ)`,

where `Vₘ = lamPhiContractM`, `f₀ = fTilde` and `g = gMult`.  Route:

* `lamPhiContractM_collapse` (Lemma53) rewrites `Vₘ(v)` as the guarded `a`-sum
  over `𝒟` with the Möbius `i ≠ m` cofactor; termwise absolute values give
  the weight `∏ᵢ f₀(aᵢ)/φ(aᵢ) · ∏_{i≠m} vᵢ/φ(aᵢ)` (`term_abs_le`).
* Per coordinate `i ≠ m` write `aᵢ = vᵢ·cᵢ` (coprime split of a squarefree),
  pull out `f₀(vᵢ)·vᵢ/φ(vᵢ)²` by `fTilde_anti`, leaving `1/φ(cᵢ)²`.
* The **joint** deviation `c = ∏_{i≠m} cᵢ` is a single squarefree modulus with
  all prime factors `> D₀ k`; the fiber of `(aₘ, c)` has at most `k^{ω(c)}`
  elements (prime-to-coordinate assignments, `vAssignSet`), and each fiber's
  `m`-coordinate sum is `≤ B₁` (`fiber_count_le`).  This is what yields the
  *absolute* constant `2` instead of `2^{k-1}`: the tail
  `∑_{c>1} k^{ω(c)}/φ(c)² ≤ 12k²/D₀ ≤ 1` by `euler_tail` (`count_tail_le`).
* Finally `vᵢ/φ(vᵢ)² ≤ 1/g(vᵢ)` per prime (`p(p−2) ≤ (p−1)²`) gives the
  `f₀/g` form (`lamPhiContractM_abs_le_g`).

The degenerate cases (`vₘ ≠ 1`, a non-squarefree coordinate, a pairwise
incompatible pair, `∏ vᵢ ≥ R`) force `Vₘ(v) = 0` term-by-term.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## `fTilde` antitonicity -/

/-- **`fTilde` divisor-antitonicity.**  For `a ∣ b`, `b > 0`, one has
`fTilde b ≤ fTilde a`: the `sqfCop` cutoff set is divisor-closed
(`a ≤ b < R₀`, squarefree and `W`-coprime pass to divisors), and on it
`fWt` is divisor-antitone (`fWt_anti`); off it `fTilde b = 0 ≤ fTilde a`. -/
lemma fTilde_anti (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) :
    ∀ a b : ℕ, 0 < b → a ∣ b → fTilde k R T b ≤ fTilde k R T a := by
  intro a b hb hab
  by_cases hbmem : b ∈ sqfCop (R0 k R T) (W k)
  · have hamem : a ∈ sqfCop (R0 k R T) (W k) := by
      rw [sqfCop, Finset.mem_filter, Finset.mem_range] at hbmem ⊢
      obtain ⟨hblt, hbsq, hbcop⟩ := hbmem
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd hb hab) hblt,
        hbsq.squarefree_of_dvd hab, hbcop.coprime_dvd_left hab⟩
    simp only [fTilde]
    rw [if_pos hbmem, if_pos hamem]
    exact fWt_anti k R hR a b hb hab
  · calc fTilde k R T b = 0 := by simp only [fTilde]; rw [if_neg hbmem]
      _ ≤ fTilde k R T a := fTilde_nonneg k R T a hR

/-! ## The degenerate `V = 0` lemmas

Each kills the guard `∀ i, vᵢ ∣ dᵢ` (or uses `dₘ = 1`) term-by-term in the
defining `d`-sum of `lamPhiContractM`; they hold for every weight `y` and
modulus `W'`. -/

/-- **Degenerate case `vₘ ≠ 1`.**  On the pinned sub-lattice `dₘ = 1` the
guard forces `vₘ ∣ 1`, so `Vₘ(v) = 0`. -/
theorem lamPhiContractM_eq_zero_of_coord_ne_one (k R W' : ℕ) (m : Fin k)
    (y : (Fin k → ℕ) → ℝ) (v : Fin k → ℕ) (hvm : v m ≠ 1) :
    lamPhiContractM k R W' m y v = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [if_neg]
  intro hall
  exact hvm (Nat.dvd_one.mp (hd.2 ▸ hall m))

/-- **Degenerate case: a non-squarefree coordinate.**  Coordinates of sieve
tuples are squarefree, and squarefreeness passes to divisors, so the divisor
guard is empty and `Vₘ(v) = 0`. -/
theorem lamPhiContractM_eq_zero_of_not_squarefree (k R W' : ℕ) (m : Fin k)
    (y : (Fin k → ℕ) → ℝ) (v : Fin k → ℕ) {i : Fin k}
    (hi : ¬ Squarefree (v i)) :
    lamPhiContractM k R W' m y v = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [if_neg]
  intro hall
  exact hi ((((mem_kSieveIndex_iff d).mp hd.1).1 i).squarefree_of_dvd (hall i))

/-- **Degenerate case: an incompatible coordinate pair.**  Distinct
coordinates of sieve tuples are coprime, so a non-coprime pair `vᵢ, vⱼ`
(`i ≠ j`) empties the divisor guard and `Vₘ(v) = 0`. -/
theorem lamPhiContractM_eq_zero_of_not_coprime (k R W' : ℕ) (m : Fin k)
    (y : (Fin k → ℕ) → ℝ) (v : Fin k → ℕ) {i j : Fin k} (hij : i ≠ j)
    (h : ¬ Nat.Coprime (v i) (v j)) :
    lamPhiContractM k R W' m y v = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [if_neg]
  intro hall
  have hco := ((mem_kSieveIndex_iff d).mp hd.1).2.1 i j hij
  exact h ((hco.coprime_dvd_left (hall i)).coprime_dvd_right (hall j))

/-- **Degenerate case `∏ vᵢ ≥ R`.**  Sieve tuples have `∏ dᵢ < R`, and the
guard gives `∏ vᵢ ∣ ∏ dᵢ`, so `R ≤ ∏ vᵢ` empties the guard and `Vₘ(v) = 0`. -/
theorem lamPhiContractM_eq_zero_of_le_prod (k R W' : ℕ) (m : Fin k)
    (y : (Fin k → ℕ) → ℝ) (v : Fin k → ℕ) (h : R ≤ ∏ i, v i) :
    lamPhiContractM k R W' m y v = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [if_neg]
  intro hall
  obtain ⟨hsq, -, -, hlt⟩ := (mem_kSieveIndex_iff d).mp hd.1
  have hdpos : 0 < ∏ i, d i := Finset.prod_pos fun i _ => Squarefree.pos (hsq i)
  have hle : (∏ i, v i) ≤ ∏ i, d i :=
    Nat.le_of_dvd hdpos (Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hall i))
  omega

/-! ## Prime-to-coordinate assignments (the `k^{ω(c)}` fiber count)

A tuple of pairwise-coprime squarefree cofactors `(cᵢ)_{i≠m}` with product `c`
is recovered from `c` plus the assignment of each prime of `c` to the (unique)
coordinate it divides.  `vAssignSet` is the finite set of such assignments,
`vCoordProd` the per-coordinate reconstruction, `thetaFun` the canonical
assignment of a tuple. -/

/-- The cofactor `a/v` of a divisor `v ∣ a` divides `a`. -/
private theorem div_dvd_self_of_dvd {v a : ℕ} (h : v ∣ a) : a / v ∣ a :=
  ⟨v, by rw [mul_comm]; exact (Nat.mul_div_cancel' h).symm⟩

/-- The finite set of prime-to-coordinate assignments for a modulus `c`. -/
private def vAssignSet (k c : ℕ) :
    Finset ((p : ℕ) → p ∈ c.primeFactors → Fin k) :=
  c.primeFactors.pi (fun _ => (Finset.univ : Finset (Fin k)))

private theorem vAssignSet_card (k c : ℕ) :
    (vAssignSet k c).card = k ^ c.primeFactors.card := by
  rw [vAssignSet, Finset.card_pi]
  simp [Finset.card_univ]

/-- The coordinate reconstruction of an assignment: coordinate `i` gets the
product of the primes of `c` assigned to it (cf. `slotProd`). -/
private def vCoordProd {k : ℕ} (c : ℕ)
    (θ : (p : ℕ) → p ∈ c.primeFactors → Fin k) (i : Fin k) : ℕ :=
  ∏ q ∈ c.primeFactors.attach.filter (fun q => θ q.1 q.2 = i), (q : ℕ)

/-- Each coordinate reconstruction divides `c` (cf. `slotProd_dvd`). -/
private theorem vCoordProd_dvd {k c : ℕ} (hc : Squarefree c)
    (θ : (p : ℕ) → p ∈ c.primeFactors → Fin k) (i : Fin k) :
    vCoordProd c θ i ∣ c := by
  have h1 : vCoordProd c θ i ∣ ∏ q ∈ c.primeFactors.attach, (q : ℕ) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  rwa [Finset.prod_attach c.primeFactors (fun p => p),
    Nat.prod_primeFactors_of_squarefree hc] at h1

/-- Prime divisibility of a coordinate reconstruction: exactly the primes of
`c` assigned to that coordinate (cf. `prime_dvd_slotProd_iff`). -/
private theorem prime_dvd_vCoordProd_iff {k c : ℕ}
    (θ : (p : ℕ) → p ∈ c.primeFactors → Fin k) {p : ℕ} (hp : p.Prime)
    (i : Fin k) :
    p ∣ vCoordProd c θ i ↔ ∃ h : p ∈ c.primeFactors, θ p h = i := by
  constructor
  · intro hdvd
    rw [vCoordProd] at hdvd
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd
    rw [Finset.mem_filter] at hq
    have hqprime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    have hpe : p = (q : ℕ) := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
    subst hpe
    exact ⟨q.2, hq.2⟩
  · rintro ⟨h, hθ⟩
    exact Finset.dvd_prod_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_attach _ ⟨p, h⟩, hθ⟩)

open Classical in
/-- The canonical assignment of a tuple `a`: `p` goes to the coordinate it
divides (unique on sieve tuples), defaulting to `m`. -/
private noncomputable def thetaFun {k : ℕ} (m : Fin k) (a : Fin k → ℕ)
    (p : ℕ) : Fin k :=
  if h : ∃ j, p ∣ a j then h.choose else m

/-- On a sieve tuple, `thetaFun` picks exactly the coordinate divisible
by `p` (well-defined by `prime_dvd_coord_unique`). -/
private theorem thetaFun_spec {k R W' : ℕ} (m : Fin k) {a : Fin k → ℕ}
    (ha : a ∈ kSieveIndex k R W') {p : ℕ} (hp : p.Prime) {j : Fin k}
    (hpj : p ∣ a j) : thetaFun m a p = j := by
  have hex : ∃ j', p ∣ a j' := ⟨j, hpj⟩
  simp only [thetaFun]
  rw [dif_pos hex]
  exact prime_dvd_coord_unique ha hp hex.choose_spec hpj

/-- **Recovery.**  A guarded sieve tuple `a` (with `vᵢ ∣ aᵢ`) is recovered on
`i ≠ m` from its joint cofactor `c = ∏_{j≠m} aⱼ/vⱼ` and its canonical
assignment: `aᵢ = vᵢ · vCoordProd c (thetaFun m a) i`. -/
private theorem coord_recover {k R : ℕ} (m : Fin k) {v a : Fin k → ℕ} {c : ℕ}
    (ha : a ∈ kSieveIndex k R (W k)) (hdvd : ∀ i, v i ∣ a i)
    (hc : (∏ j ∈ Finset.univ.erase m, (a j / v j)) = c)
    {i : Fin k} (him : i ≠ m) :
    a i = v i * vCoordProd c (fun p _ => thetaFun m a p) i := by
  subst hc
  obtain ⟨hsq, hcop, -, -⟩ := (mem_kSieveIndex_iff a).mp ha
  have hpos : ∀ j, 0 < a j := fun j => kSieveIndex_coord_pos ha j
  have hcdvd : ∀ j, (a j / v j) ∣ a j := fun j => div_dvd_self_of_dvd (hdvd j)
  have hcsq : ∀ j, Squarefree (a j / v j) :=
    fun j => (hsq j).squarefree_of_dvd (hcdvd j)
  have hcpair : ∀ i₁ ∈ Finset.univ.erase m, ∀ j₁ ∈ Finset.univ.erase m,
      i₁ ≠ j₁ → Nat.Coprime (a i₁ / v i₁) (a j₁ / v j₁) := fun i₁ _ j₁ _ hne =>
    ((hcop i₁ j₁ hne).coprime_dvd_left (hcdvd i₁)).coprime_dvd_right (hcdvd j₁)
  have hCsq : Squarefree (∏ j ∈ Finset.univ.erase m, (a j / v j)) :=
    squarefree_prod_coprime _ _ (fun j _ => hcsq j) hcpair
  have hCne : (∏ j ∈ Finset.univ.erase m, (a j / v j)) ≠ 0 := hCsq.ne_zero
  set c := ∏ j ∈ Finset.univ.erase m, (a j / v j) with hcdef
  set θ : (p : ℕ) → p ∈ c.primeFactors → Fin k :=
    fun p _ => thetaFun m a p with hθdef
  -- both `aᵢ/vᵢ` and the reconstruction are squarefree; compare their primes
  have hXdvd : vCoordProd c θ i ∣ c := vCoordProd_dvd hCsq θ i
  have hXsq : Squarefree (vCoordProd c θ i) := hCsq.squarefree_of_dvd hXdvd
  have d1 : (a i / v i) ∣ vCoordProd c θ i := by
    rw [squarefree_dvd_iff_primes (hcsq i)]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpci : p ∣ a i / v i := Nat.dvd_of_mem_primeFactors hp
    have hpai : p ∣ a i := hpci.trans (hcdvd i)
    have hθi : thetaFun m a p = i := thetaFun_spec m ha hpp hpai
    have hpc : p ∣ c := hpci.trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨him, Finset.mem_univ i⟩))
    have hpmem : p ∈ c.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpc, hCne⟩
    exact (prime_dvd_vCoordProd_iff θ hpp i).mpr ⟨hpmem, hθi⟩
  have d2 : vCoordProd c θ i ∣ (a i / v i) := by
    rw [squarefree_dvd_iff_primes hXsq]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpX : p ∣ vCoordProd c θ i := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨hpmem, hθi⟩ := (prime_dvd_vCoordProd_iff θ hpp i).mp hpX
    have hpc : p ∣ c := Nat.dvd_of_mem_primeFactors hpmem
    rw [hcdef] at hpc
    obtain ⟨j, hjmem, hpcj⟩ := (hpp.prime.dvd_finsetProd_iff _).mp hpc
    have hpaj : p ∣ a j := hpcj.trans (hcdvd j)
    have hji : j = i := by
      have := thetaFun_spec m ha hpp hpaj
      rw [← hθi]; exact this.symm
    rw [← hji]
    exact hpcj
  have heq : a i / v i = vCoordProd c θ i := Nat.dvd_antisymm d1 d2
  rw [← heq]
  exact (Nat.mul_div_cancel' (hdvd i)).symm

/-! ## The per-fiber count and the joint tail -/

/-- **Fiber count.**  On any set of guarded sieve tuples with fixed joint
cofactor `c`, the `m`-coordinate sum of `f₀/φ` is at most
`k^{ω(c)} · ∑_{x<R} f₀(x)/φ(x)`: fibering by the canonical assignment
(`≤ k^{ω(c)}` fibers) leaves `a ↦ aₘ` injective (`coord_recover`). -/
private theorem fiber_count_le (k R : ℕ) (T : ℝ) (m : Fin k) (v : Fin k → ℕ)
    (hR : 2 ≤ R) (c : ℕ) (S : Finset (Fin k → ℕ))
    (hS : ∀ a ∈ S, a ∈ kSieveIndex k R (W k) ∧ (∀ i, v i ∣ a i)
      ∧ (∏ j ∈ Finset.univ.erase m, (a j / v j)) = c) :
    ∑ a ∈ S, fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
      ≤ (k : ℝ) ^ c.primeFactors.card
          * ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) := by
  classical
  have hmaps : ∀ a ∈ S,
      (fun p (_ : p ∈ c.primeFactors) => thetaFun m a p) ∈ vAssignSet k c :=
    fun a _ => Finset.mem_pi.mpr (fun p hp => Finset.mem_univ _)
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun a => (fun p (_ : p ∈ c.primeFactors) => thetaFun m a p)) hmaps
    (fun a => fTilde k R T (a m) / (Nat.totient (a m) : ℝ))]
  have hper : ∀ θ ∈ vAssignSet k c,
      (∑ a ∈ S.filter
          (fun a => (fun p (_ : p ∈ c.primeFactors) => thetaFun m a p) = θ),
        fTilde k R T (a m) / (Nat.totient (a m) : ℝ))
      ≤ ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) := by
    intro θ _
    have hinj : ∀ a ∈ S.filter
        (fun a => (fun p (_ : p ∈ c.primeFactors) => thetaFun m a p) = θ),
        ∀ b ∈ S.filter
        (fun b => (fun p (_ : p ∈ c.primeFactors) => thetaFun m b p) = θ),
        a m = b m → a = b := by
      intro a haf b hbf hab
      have haθ : (fun p (_ : p ∈ c.primeFactors) => thetaFun m a p) = θ :=
        (Finset.mem_filter.mp haf).2
      have hbθ : (fun p (_ : p ∈ c.primeFactors) => thetaFun m b p) = θ :=
        (Finset.mem_filter.mp hbf).2
      obtain ⟨haK, hadvd, hac⟩ := hS a (Finset.mem_filter.mp haf).1
      obtain ⟨hbK, hbdvd, hbc⟩ := hS b (Finset.mem_filter.mp hbf).1
      funext i
      by_cases him : i = m
      · rw [him]; exact hab
      · have ra := coord_recover m haK hadvd hac him
        have rb := coord_recover m hbK hbdvd hbc him
        rw [haθ] at ra
        rw [hbθ] at rb
        rw [ra, rb]
    calc (∑ a ∈ S.filter
            (fun a => (fun p (_ : p ∈ c.primeFactors) => thetaFun m a p) = θ),
          fTilde k R T (a m) / (Nat.totient (a m) : ℝ))
        = ∑ x ∈ (S.filter
            (fun a => (fun p (_ : p ∈ c.primeFactors) => thetaFun m a p) = θ)).image
              (fun a => a m),
            fTilde k R T x / (Nat.totient x : ℝ) :=
          (Finset.sum_image (f := fun x => fTilde k R T x / (Nat.totient x : ℝ))
            hinj).symm
      _ ≤ ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ =>
            div_nonneg (fTilde_nonneg k R T x hR) (Nat.cast_nonneg _))
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨a, haf, rfl⟩ := hx
          obtain ⟨haK, -, -⟩ := hS a (Finset.mem_filter.mp haf).1
          exact Finset.mem_range.mpr (kSieveIndex_coord_lt haK m)
  calc (∑ θ ∈ vAssignSet k c, ∑ a ∈ S.filter
          (fun a => (fun p (_ : p ∈ c.primeFactors) => thetaFun m a p) = θ),
        fTilde k R T (a m) / (Nat.totient (a m) : ℝ))
      ≤ (vAssignSet k c).card
          • ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ hper
    _ = (k : ℝ) ^ c.primeFactors.card
          * ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) := by
        rw [vAssignSet_card, nsmul_eq_mul, Nat.cast_pow]

/-- The joint cofactor of a guarded sieve tuple lands in the deviation
moduli set: squarefree, all primes `> D₀ k`, and `< R`. -/
private theorem cOf_mem (k R : ℕ) (m : Fin k) (v : Fin k → ℕ)
    {a : Fin k → ℕ} (ha : a ∈ kSieveIndex k R (W k))
    (hdvd : ∀ i, v i ∣ a i) :
    (∏ j ∈ Finset.univ.erase m, (a j / v j)) ∈ (Finset.range R).filter
      (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p) := by
  obtain ⟨hsq, hcop, -, hprodR⟩ := (mem_kSieveIndex_iff a).mp ha
  have hcdvd : ∀ j, (a j / v j) ∣ a j := fun j => div_dvd_self_of_dvd (hdvd j)
  have hcsq : ∀ j, Squarefree (a j / v j) :=
    fun j => (hsq j).squarefree_of_dvd (hcdvd j)
  have hCsq : Squarefree (∏ j ∈ Finset.univ.erase m, (a j / v j)) :=
    squarefree_prod_coprime _ _ (fun j _ => hcsq j) (fun i₁ _ j₁ _ hne =>
      ((hcop i₁ j₁ hne).coprime_dvd_left (hcdvd i₁)).coprime_dvd_right (hcdvd j₁))
  have hdvd2 : (∏ j ∈ Finset.univ.erase m, (a j / v j)) ∣ ∏ j, a j := by
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hcdvd j)) ?_
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _)
  have hpos : 0 < ∏ j, a j :=
    Finset.prod_pos fun j _ => kSieveIndex_coord_pos ha j
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨lt_of_le_of_lt (Nat.le_of_dvd hpos hdvd2) hprodR, hCsq, ?_⟩
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨j, -, hpj⟩ := (hpp.prime.dvd_finsetProd_iff _).mp
    (Nat.dvd_of_mem_primeFactors hp)
  exact D₀_lt_of_prime_dvd_coord ha hpp (hpj.trans (hcdvd j))

/-- The full `m`-coordinate range sum is at most `B₁` (`fTilde` vanishes off
`sqfCop (R0 …) (W k)` and `fWt/φ ≥ 0`). -/
private theorem sum_fTilde_div_le_B1 (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) :
    ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ)
      ≤ B1 k R (W k) T := by
  have hterm : ∀ x, fTilde k R T x / (Nat.totient x : ℝ)
      = if x ∈ sqfCop (R0 k R T) (W k)
          then fWt k R x / (Nat.totient x : ℝ) else 0 := by
    intro x
    simp only [fTilde]
    split_ifs with h
    · rfl
    · rw [zero_div]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ =>
    div_nonneg (fWt_nonneg_all k R x hR) (Nat.cast_nonneg _))
  intro x hx
  exact (Finset.mem_filter.mp hx).2

/-- **The joint deviation tail.**  Over squarefree moduli `c < R` with all
primes `> D₀ k`, `∑ k^{ω(c)}/φ(c)² ≤ 2`: the `c = 1` term is `1`, and the
`c > 1` tail is `≤ 12k²/D₀ ≤ 1` by `euler_tail` (per prime `k ≤ 3k²`). -/
private theorem count_tail_le (k R : ℕ) (hk : 1 ≤ k) (hR : 2 ≤ R)
    (hD : 12 * k ^ 2 ≤ D₀ k) :
    ∑ c ∈ (Finset.range R).filter
        (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p),
      (k : ℝ) ^ c.primeFactors.card * ((Nat.totient c : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD0 : 0 < D₀ k := by omega
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hD0
  have h1mem : (1 : ℕ) ∈ (Finset.range R).filter
      (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, squarefree_one, ?_⟩
    simp [Nat.primeFactors_one]
  rw [← Finset.add_sum_erase _ _ h1mem]
  have hf1 : (k : ℝ) ^ (Nat.primeFactors 1).card
      * ((Nat.totient 1 : ℝ) ^ 2)⁻¹ = 1 := by
    simp [Nat.primeFactors_one]
  have htermle : ∀ c ∈ ((Finset.range R).filter
      (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p)).erase 1,
      (k : ℝ) ^ c.primeFactors.card * ((Nat.totient c : ℝ) ^ 2)⁻¹
        ≤ (3 * (k : ℝ) ^ 2) ^ c.primeFactors.card
            * ∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 := by
    intro c hc
    rw [Finset.mem_erase, Finset.mem_filter] at hc
    obtain ⟨-, -, hcsq, -⟩ := hc
    have hrhs : (∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
        = ((Nat.totient c : ℝ) ^ 2)⁻¹ := by
      rw [Finset.prod_pow, Finset.prod_inv_distrib,
        ← totient_squarefree_cast hcsq, inv_pow]
    rw [← hrhs]
    refine mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg k) ?_ _)
      (Finset.prod_nonneg fun p _ => by positivity)
    have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have htail : (∑ c ∈ ((Finset.range R).filter
      (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p)).erase 1,
      (k : ℝ) ^ c.primeFactors.card * ((Nat.totient c : ℝ) ^ 2)⁻¹) ≤ 1 := by
    calc (∑ c ∈ ((Finset.range R).filter
          (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p)).erase 1,
          (k : ℝ) ^ c.primeFactors.card * ((Nat.totient c : ℝ) ^ 2)⁻¹)
        ≤ ∑ c ∈ ((Finset.range R).filter
            (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p)).erase 1,
            (3 * (k : ℝ) ^ 2) ^ c.primeFactors.card
              * ∏ p ∈ c.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
          Finset.sum_le_sum htermle
      _ ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := euler_tail k R hk hD
      _ ≤ 1 := by
          rw [div_le_one hD0R]
          exact_mod_cast hD
  rw [hf1]
  linarith

/-! ## The pointwise term bound -/

/-- **Termwise majorant.**  For a guarded sieve tuple `a` (`vᵢ ∣ aᵢ`), the
collapsed summand of `Vₘ(v)` is bounded by
`P · (f₀(aₘ)/φ(aₘ)) · 1/φ(c(a))²` with `P = ∏_{i≠m} f₀(vᵢ)vᵢ/φ(vᵢ)²` and
`c(a) = ∏_{i≠m} aᵢ/vᵢ`: strip `|μ| ≤ 1` and `|y| = ∏ f₀`, split `aᵢ = vᵢ·cᵢ`
(coprime, `φ` multiplicative), and use `fTilde_anti`. -/
private theorem term_abs_le (k R : ℕ) (T : ℝ) (m : Fin k) (v : Fin k → ℕ)
    (hR : 2 ≤ R) {a : Fin k → ℕ} (ha : a ∈ kSieveIndex k R (W k))
    (hdvd : ∀ i, v i ∣ a i) :
    |(yTensor k R T a / ∏ i, (Nat.totient (a i) : ℝ))
        * ∏ i ∈ Finset.univ.erase m,
            (((μ (a i) : ℤ) : ℝ) * ((v i : ℝ) / (Nat.totient (a i) : ℝ)))|
      ≤ (∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
          * (fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
              * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ)
                  ^ 2)⁻¹) := by
  obtain ⟨hsq, hcop, -, -⟩ := (mem_kSieveIndex_iff a).mp ha
  have hpos : ∀ i, 0 < a i := fun i => kSieveIndex_coord_pos ha i
  have hφpos : ∀ i, (0 : ℝ) < (Nat.totient (a i) : ℝ) := fun i => by
    exact_mod_cast Nat.totient_pos.mpr (hpos i)
  have hfT0 : ∀ n, 0 ≤ fTilde k R T n := fun n => fTilde_nonneg k R T n hR
  have hcdvd : ∀ j, (a j / v j) ∣ a j := fun j => div_dvd_self_of_dvd (hdvd j)
  have haeq : ∀ j, a j = v j * (a j / v j) :=
    fun j => (Nat.mul_div_cancel' (hdvd j)).symm
  have hccop : ∀ j, Nat.Coprime (v j) (a j / v j) := fun j =>
    Nat.coprime_of_squarefree_mul (by rw [← haeq j]; exact hsq j)
  have hφsplit : ∀ j, (Nat.totient (a j) : ℝ)
      = (Nat.totient (v j) : ℝ) * (Nat.totient (a j / v j) : ℝ) := by
    intro j
    conv_lhs => rw [haeq j]
    rw [Nat.totient_mul (hccop j)]
    push_cast
    ring
  have hy : yTensor k R T a = ∏ i, fTilde k R T (a i) := by
    simp only [yTensor]
    rw [if_pos ha]
  -- Step 1: strip absolute values (`|y| = ∏ f₀`, `|μ| ≤ 1`)
  have hA1 : |(yTensor k R T a / ∏ i, (Nat.totient (a i) : ℝ))
        * ∏ i ∈ Finset.univ.erase m,
            (((μ (a i) : ℤ) : ℝ) * ((v i : ℝ) / (Nat.totient (a i) : ℝ)))|
      ≤ (∏ i, fTilde k R T (a i)) / (∏ i, (Nat.totient (a i) : ℝ))
          * ∏ i ∈ Finset.univ.erase m,
              ((v i : ℝ) / (Nat.totient (a i) : ℝ)) := by
    rw [abs_mul, abs_div, hy,
      abs_of_nonneg (Finset.prod_nonneg (fun i _ => hfT0 (a i))),
      abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hφpos i).le)),
      Finset.abs_prod]
    have hleft : (0 : ℝ) ≤ (∏ i, fTilde k R T (a i))
        / (∏ i, (Nat.totient (a i) : ℝ)) :=
      div_nonneg (Finset.prod_nonneg (fun i _ => hfT0 (a i)))
        (Finset.prod_nonneg (fun i _ => (hφpos i).le))
    refine mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)) hleft
    rw [abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (v i : ℝ) / (Nat.totient (a i) : ℝ))]
    calc |((μ (a i) : ℤ) : ℝ)| * ((v i : ℝ) / (Nat.totient (a i) : ℝ))
        ≤ 1 * ((v i : ℝ) / (Nat.totient (a i) : ℝ)) :=
          mul_le_mul_of_nonneg_right (abs_moebius_real_le_one _) (by positivity)
      _ = (v i : ℝ) / (Nat.totient (a i) : ℝ) := one_mul _
  -- Step 2: split off the `m`-coordinate
  have hA2 : (∏ i, fTilde k R T (a i)) / (∏ i, (Nat.totient (a i) : ℝ))
        * ∏ i ∈ Finset.univ.erase m, ((v i : ℝ) / (Nat.totient (a i) : ℝ))
      = (fTilde k R T (a m) / (Nat.totient (a m) : ℝ))
        * ∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (a i) * (v i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => fTilde k R T (a i))
        (Finset.mem_univ m),
      ← Finset.mul_prod_erase Finset.univ (fun i => (Nat.totient (a i) : ℝ))
        (Finset.mem_univ m),
      Finset.prod_div_distrib,
      show (∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (a i) * (v i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2))
          = (∏ i ∈ Finset.univ.erase m, fTilde k R T (a i))
              * (∏ i ∈ Finset.univ.erase m, (v i : ℝ))
              / (∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ)) ^ 2 from by
        rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow]]
    have hφm : (Nat.totient (a m) : ℝ) ≠ 0 := (hφpos m).ne'
    have hφe : (∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ)) ≠ 0 :=
      (Finset.prod_pos (fun i _ => hφpos i)).ne'
    field_simp
  -- Step 3: per-coordinate relaxation to `v` (antitone `f₀`, `φ` split)
  have hA3 : ∀ i ∈ Finset.univ.erase m,
      fTilde k R T (a i) * (v i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2
        ≤ (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2)
            * ((Nat.totient (a i / v i) : ℝ) ^ 2)⁻¹ := by
    intro i _
    have hvpos : 0 < v i := Nat.pos_of_dvd_of_pos (hdvd i) (hpos i)
    have hcpos : 0 < a i / v i :=
      Nat.div_pos (Nat.le_of_dvd (hpos i) (hdvd i)) hvpos
    have hφv : (0 : ℝ) < (Nat.totient (v i) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hvpos
    have hφc : (0 : ℝ) < (Nat.totient (a i / v i) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hcpos
    have hanti : fTilde k R T (a i) ≤ fTilde k R T (v i) :=
      fTilde_anti k R T hR (v i) (a i) (hpos i) (hdvd i)
    have hnum : fTilde k R T (a i) * (v i : ℝ)
        ≤ fTilde k R T (v i) * (v i : ℝ) :=
      mul_le_mul_of_nonneg_right hanti (Nat.cast_nonneg _)
    calc fTilde k R T (a i) * (v i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2
        ≤ fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2)
            * ((Nat.totient (a i / v i) : ℝ) ^ 2)⁻¹ := by
          rw [hφsplit i]
          field_simp
  -- Step 4: assemble; the cofactor `φ`'s multiply to `φ(c(a))`
  have hcpair : ∀ i₁ ∈ Finset.univ.erase m, ∀ j₁ ∈ Finset.univ.erase m,
      i₁ ≠ j₁ → Nat.Coprime (a i₁ / v i₁) (a j₁ / v j₁) := fun i₁ _ j₁ _ hne =>
    ((hcop i₁ j₁ hne).coprime_dvd_left (hcdvd i₁)).coprime_dvd_right (hcdvd j₁)
  have hφcprod : (∏ i ∈ Finset.univ.erase m,
        ((Nat.totient (a i / v i) : ℝ) ^ 2)⁻¹)
      = ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹ := by
    have h1 : (Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ)
        = ∏ j ∈ Finset.univ.erase m, (Nat.totient (a j / v j) : ℝ) := by
      rw [prod_totient_coprime _ _ hcpair]
      push_cast
      rfl
    rw [h1, Finset.prod_inv_distrib, Finset.prod_pow]
  have hA4 : (∏ i ∈ Finset.univ.erase m,
        (fTilde k R T (a i) * (v i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2))
      ≤ (∏ i ∈ Finset.univ.erase m,
          (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
        * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹ := by
    calc (∏ i ∈ Finset.univ.erase m,
          (fTilde k R T (a i) * (v i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2))
        ≤ ∏ i ∈ Finset.univ.erase m,
            ((fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2)
              * ((Nat.totient (a i / v i) : ℝ) ^ 2)⁻¹) :=
          Finset.prod_le_prod (fun i _ => by
            have := hfT0 (a i); positivity) hA3
      _ = (∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
          * ∏ i ∈ Finset.univ.erase m, ((Nat.totient (a i / v i) : ℝ) ^ 2)⁻¹ :=
          Finset.prod_mul_distrib
      _ = (∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
          * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹ :=
          by rw [hφcprod]
  calc |(yTensor k R T a / ∏ i, (Nat.totient (a i) : ℝ))
        * ∏ i ∈ Finset.univ.erase m,
            (((μ (a i) : ℤ) : ℝ) * ((v i : ℝ) / (Nat.totient (a i) : ℝ)))|
      ≤ (∏ i, fTilde k R T (a i)) / (∏ i, (Nat.totient (a i) : ℝ))
          * ∏ i ∈ Finset.univ.erase m,
              ((v i : ℝ) / (Nat.totient (a i) : ℝ)) := hA1
    _ = (fTilde k R T (a m) / (Nat.totient (a m) : ℝ))
          * ∏ i ∈ Finset.univ.erase m,
              (fTilde k R T (a i) * (v i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := hA2
    _ ≤ (fTilde k R T (a m) / (Nat.totient (a m) : ℝ))
          * ((∏ i ∈ Finset.univ.erase m,
              (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
            * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hA4
          (div_nonneg (hfT0 (a m)) (hφpos m).le)
    _ = (∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
          * (fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
              * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ)
                  ^ 2)⁻¹) := by ring

/-! ## Node A — the `V_abs` bound -/

/-- **Node A, `V_abs` (first form).**  For the tensor weight and `vₘ = 1`,
`|Vₘ(v)| ≤ 2·B₁·∏_{i≠m} f₀(vᵢ)·vᵢ/φ(vᵢ)²`.  Collapse (`lamPhiContractM_collapse`),
termwise majorant (`term_abs_le`), fiber the guarded `a`-sum over the joint
cofactor `c` (`cOf_mem`), count each fiber by `k^{ω(c)}·B₁`
(`fiber_count_le` + `sum_fTilde_div_le_B1`), and close the `c`-tail with
`euler_tail` (`count_tail_le`): total factor `1 + 12k²/D₀ ≤ 2`. -/
theorem lamPhiContractM_abs_le (k R : ℕ) (T : ℝ) (m : Fin k) (v : Fin k → ℕ)
    (hR : 2 ≤ R) (hD : 12 * k ^ 2 ≤ D₀ k) (hvm : v m = 1) :
    |lamPhiContractM k R (W k) m (yTensor k R T) v|
      ≤ 2 * B1 k R (W k) T
          * ∏ i ∈ Finset.univ.erase m,
              (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2) := by
  classical
  have hk : 1 ≤ k := m.pos
  have hP0 : (0 : ℝ) ≤ ∏ i ∈ Finset.univ.erase m,
      (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2) :=
    Finset.prod_nonneg fun i _ =>
      div_nonneg (mul_nonneg (fTilde_nonneg k R T _ hR) (Nat.cast_nonneg _))
        (by positivity)
  have hB0nn : (0 : ℝ) ≤ ∑ x ∈ Finset.range R,
      fTilde k R T x / (Nat.totient x : ℝ) :=
    Finset.sum_nonneg fun x _ =>
      div_nonneg (fTilde_nonneg k R T x hR) (Nat.cast_nonneg _)
  -- Step 1: collapse and take absolute values termwise
  have step1 : |lamPhiContractM k R (W k) m (yTensor k R T) v|
      ≤ ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i),
          |(yTensor k R T a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((v i : ℝ) / (Nat.totient (a i) : ℝ)))| := by
    rw [lamPhiContractM_collapse k R (W k) m (yTensor k R T) v hvm]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    split_ifs with h
    · rfl
    · exact abs_zero
  -- Step 2: termwise majorant
  have step2 : (∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i),
        |(yTensor k R T a / ∏ i, (Nat.totient (a i) : ℝ))
          * ∏ i ∈ Finset.univ.erase m,
              (((μ (a i) : ℤ) : ℝ) * ((v i : ℝ) / (Nat.totient (a i) : ℝ)))|)
      ≤ ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i),
          (∏ i ∈ Finset.univ.erase m,
              (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
            * (fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
                * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ)
                    ^ 2)⁻¹) := by
    refine Finset.sum_le_sum (fun a haA => ?_)
    rw [Finset.mem_filter] at haA
    exact term_abs_le k R T m v hR haA.1 haA.2
  -- Step 3: the guarded majorant sum is `≤ 2·B₁`
  have step3 : (∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i),
        fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
          * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹)
      ≤ 2 * B1 k R (W k) T := by
    have hmaps : ∀ a ∈ (kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i),
        (∏ j ∈ Finset.univ.erase m, (a j / v j)) ∈ (Finset.range R).filter
          (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p) := by
      intro a haA
      rw [Finset.mem_filter] at haA
      exact cOf_mem k R m v haA.1 haA.2
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun a : Fin k → ℕ => ∏ j ∈ Finset.univ.erase m, (a j / v j)) hmaps
      (fun a : Fin k → ℕ => fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
        * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹)]
    have hper : ∀ c ∈ (Finset.range R).filter
        (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p),
        (∑ a ∈ ((kSieveIndex k R (W k)).filter
              (fun a => ∀ i, v i ∣ a i)).filter
              (fun a => (∏ j ∈ Finset.univ.erase m, (a j / v j)) = c),
          fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
            * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹)
        ≤ ((k : ℝ) ^ c.primeFactors.card * ((Nat.totient c : ℝ) ^ 2)⁻¹)
            * ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) := by
      intro c _
      have hcongr : ∀ a ∈ ((kSieveIndex k R (W k)).filter
            (fun a => ∀ i, v i ∣ a i)).filter
            (fun a => (∏ j ∈ Finset.univ.erase m, (a j / v j)) = c),
          fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
            * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹
          = fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
              * ((Nat.totient c : ℝ) ^ 2)⁻¹ := by
        intro a haf
        rw [(Finset.mem_filter.mp haf).2]
      rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]
      have hcnt := fiber_count_le k R T m v hR c
        (((kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i)).filter
          (fun a => (∏ j ∈ Finset.univ.erase m, (a j / v j)) = c))
        (fun a haf => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp haf).1).1,
          (Finset.mem_filter.mp (Finset.mem_filter.mp haf).1).2,
          (Finset.mem_filter.mp haf).2⟩)
      calc (∑ a ∈ ((kSieveIndex k R (W k)).filter
              (fun a => ∀ i, v i ∣ a i)).filter
              (fun a => (∏ j ∈ Finset.univ.erase m, (a j / v j)) = c),
            fTilde k R T (a m) / (Nat.totient (a m) : ℝ))
              * ((Nat.totient c : ℝ) ^ 2)⁻¹
          ≤ ((k : ℝ) ^ c.primeFactors.card
              * ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ))
              * ((Nat.totient c : ℝ) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hcnt (by positivity)
        _ = ((k : ℝ) ^ c.primeFactors.card * ((Nat.totient c : ℝ) ^ 2)⁻¹)
              * ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) := by
            ring
    calc (∑ c ∈ (Finset.range R).filter
          (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p),
          ∑ a ∈ ((kSieveIndex k R (W k)).filter
              (fun a => ∀ i, v i ∣ a i)).filter
              (fun a => (∏ j ∈ Finset.univ.erase m, (a j / v j)) = c),
            fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
              * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ) ^ 2)⁻¹)
        ≤ ∑ c ∈ (Finset.range R).filter
            (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p),
            ((k : ℝ) ^ c.primeFactors.card * ((Nat.totient c : ℝ) ^ 2)⁻¹)
              * ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) :=
          Finset.sum_le_sum hper
      _ = (∑ c ∈ (Finset.range R).filter
            (fun c => Squarefree c ∧ ∀ p ∈ c.primeFactors, D₀ k < p),
            (k : ℝ) ^ c.primeFactors.card * ((Nat.totient c : ℝ) ^ 2)⁻¹)
            * ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) := by
          rw [← Finset.sum_mul]
      _ ≤ 2 * ∑ x ∈ Finset.range R, fTilde k R T x / (Nat.totient x : ℝ) :=
          mul_le_mul_of_nonneg_right (count_tail_le k R hk hR hD) hB0nn
      _ ≤ 2 * B1 k R (W k) T := by
          have := sum_fTilde_div_le_B1 k R T hR
          linarith
  -- assemble
  calc |lamPhiContractM k R (W k) m (yTensor k R T) v|
      ≤ ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i),
          |(yTensor k R T a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((v i : ℝ) / (Nat.totient (a i) : ℝ)))| :=
        step1
    _ ≤ ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i),
          (∏ i ∈ Finset.univ.erase m,
              (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
            * (fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
                * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ)
                    ^ 2)⁻¹) := step2
    _ = (∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
          * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => ∀ i, v i ∣ a i),
              fTilde k R T (a m) / (Nat.totient (a m) : ℝ)
                * ((Nat.totient (∏ j ∈ Finset.univ.erase m, (a j / v j)) : ℝ)
                    ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (∏ i ∈ Finset.univ.erase m,
            (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2))
          * (2 * B1 k R (W k) T) :=
        mul_le_mul_of_nonneg_left step3 hP0
    _ = 2 * B1 k R (W k) T
          * ∏ i ∈ Finset.univ.erase m,
              (fTilde k R T (v i) * (v i : ℝ) / (Nat.totient (v i) : ℝ) ^ 2) := by
        ring

/-- **Node A, `V_abs` (second form).**  The per-coordinate weight relaxes to
`f₀(vᵢ)/g(vᵢ)`: per prime `p(p−2) ≤ (p−1)²`, so `vᵢ/φ(vᵢ)² ≤ 1/g(vᵢ)` on the
support of `f₀` (all primes `> D₀ k ≥ 3` there), and off the support both
sides vanish. -/
theorem lamPhiContractM_abs_le_g (k R : ℕ) (T : ℝ) (m : Fin k) (v : Fin k → ℕ)
    (hR : 2 ≤ R) (hD : 12 * k ^ 2 ≤ D₀ k) (hvm : v m = 1) :
    |lamPhiContractM k R (W k) m (yTensor k R T) v|
      ≤ 2 * B1 k R (W k) T
          * ∏ i ∈ Finset.univ.erase m,
              (fTilde k R T (v i) / (gMult (v i) : ℝ)) := by
  have hk : 1 ≤ k := m.pos
  refine le_trans (lamPhiContractM_abs_le k R T m v hR hD hvm) ?_
  have h2B : (0 : ℝ) ≤ 2 * B1 k R (W k) T := by
    have := B1_nonneg k R (W k) T hR
    linarith
  refine mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)) h2B
  · exact div_nonneg (mul_nonneg (fTilde_nonneg k R T _ hR) (Nat.cast_nonneg _))
      (by positivity)
  · by_cases hmem : v i ∈ sqfCop (R0 k R T) (W k)
    · have hmem' := hmem
      rw [sqfCop, Finset.mem_filter, Finset.mem_range] at hmem'
      obtain ⟨-, hsqv, hcopv⟩ := hmem'
      have hvpos : 0 < v i := Squarefree.pos hsqv
      have hodd : ∀ p ∈ (v i).primeFactors, 3 ≤ p := by
        intro p hp
        have hpD := D₀_lt_of_prime_dvd_coprime hcopv
          (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
        have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
        omega
      have hgpos : (0 : ℝ) < (gMult (v i) : ℝ) := by
        rw [gMult_cast hodd]
        refine Finset.prod_pos fun p hp => ?_
        have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
        linarith
      have hφv : (0 : ℝ) < (Nat.totient (v i) : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hvpos
      have hkey : (gMult (v i) : ℝ) * (v i : ℝ) ≤ (Nat.totient (v i) : ℝ) ^ 2 := by
        rw [gMult_cast hodd, totient_squarefree_cast hsqv,
          show ((v i : ℕ) : ℝ) = ∏ p ∈ (v i).primeFactors, (p : ℝ) from by
            rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsqv],
          ← Finset.prod_mul_distrib, ← Finset.prod_pow]
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
        · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
          nlinarith
        · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
          nlinarith
      rw [div_le_div_iff₀ (by positivity) hgpos]
      calc fTilde k R T (v i) * (v i : ℝ) * (gMult (v i) : ℝ)
          = fTilde k R T (v i) * ((gMult (v i) : ℝ) * (v i : ℝ)) := by ring
        _ ≤ fTilde k R T (v i) * (Nat.totient (v i) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hkey (fTilde_nonneg k R T _ hR)
    · simp only [fTilde, if_neg hmem]
      simp

end Salt.Maynard
