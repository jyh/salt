/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Witness

/-!
# The twin-bar rung (`twinbar`) — the rational tie (node T7)

Design: `docs/blueprints/twinbar.md`, node T7 — *the rational tie*, the designed
follow-on to the landed impossibility rung. This module builds the exact
`ℚ`-arithmetic dual of the real Maynard–Selberg carriers `I₂`/`J₁`/`J₂`
(`Salt/TwinBar/Defs.lean`) at `k = 2`, mirroring the landed `k = 5` certificate
layer (`Salt/Twelve/Certificate.lean`, `Salt/Twelve/BudgetPoly.lean`), and — the
`C`-content — the **bridge** that connects the rational simplex forms to the real
nested `intervalIntegral` carriers through the multivariate Dirichlet integral.
This is the corpus's first real↔rational simplex tie.

The payoff is the rational dual of the landed `M5_cert`:

  `no_twin_certificate : ¬ ∃ p : Poly₂, 0 < Ical₂ p ∧ 2 * Ical₂ p < JcalTot₂ p`

— for the twin tuple `{0, 2}` no *rational polynomial* weight can cross the twin
gate, obtained by casting the rational data through the bridge into `twin_bar`.
Together with the positive companion `twin_certificate_example` (the degree-1
witness of `Witness.lean` in rational dress, ratio `≥ 1.383`) it re-certifies the
squeeze `1.383 ≤ M₂ ≤ 2·log 2 < 2` in the polynomial class.

## Honesty contract (unchanged from the rung)

These are per-weight statements over polynomial (hence continuous) `F`; the density
bridge to Polymath8b's `L²`-sup `M₂` is a possible later strengthening, not part of
the floor. Neither the impossibility nor the witness claims "sieves (can/cannot)
prove twin primes": parity-breaking (type-II / bilinear) inputs modify the
functional and lie outside this bound. See `Salt.TwinBar.All`.

## The Dirichlet arithmetic (independently re-derived)

For a monomial `t₁^a t₂^b`, `∫_{R₂} t₁^a t₂^b = a! b! / (a+b+2)!` (`DInt₂`). The
`J`-kernels come from the `contractAt` peel `∫₀^{1−t₂} t₁^a dt₁ = (1−t₂)^{a+1}/(a+1)`,
so squaring the peeled sum and integrating in the Beta integral
`∫₀¹ t^p (1−t)^q dt = p! q!/(p+q+1)!` (`betaNat`) gives

  `jKer₁ a b a' b' = (b+b')!·(a+a'+2)! / ((a+1)(a'+1)·(a+a'+b+b'+3)!)`  (the `J₁` kernel),
  `jKer₂ a b a' b' = (a+a')!·(b+b'+2)! / ((b+1)(b'+1)·(a+a'+b+b'+3)!)`  (the `J₂` mirror).

Both were re-derived from scratch and agree with the design sketch; the numeric
cross-check `Ical₂ = 209/196`, `JcalTot₂ = 1084/735` at the witness matches
`Witness.lean`'s real values `I₂ Fw`, `J₁ Fw + J₂ Fw`.
-/

open Nat MeasureTheory intervalIntegral Set

namespace Salt.TwinBar

/-! ## The Beta atom and the budget monomial -/

/-- **The natural Beta integral.** `∫₀¹ t^m (1−t)^n dt = m! n! / (m+n+1)!`, proved
by induction on `n` (`∀ m`) via one integration by parts per step
(`intervalIntegral.integral_mul_deriv_eq_deriv_mul`); mathlib carries only the
complex `Complex.betaIntegral`, so the real natural-argument value is proved here. -/
theorem betaNat : ∀ (n m : ℕ),
    (∫ t in (0:ℝ)..1, t ^ m * (1 - t) ^ n)
      = (m.factorial * n.factorial : ℝ) / (m + n + 1).factorial := by
  intro n
  induction n with
  | zero =>
    intro m
    have hc : (∫ t in (0:ℝ)..1, t ^ m * (1 - t) ^ 0) = ∫ t in (0:ℝ)..1, t ^ m := by
      apply integral_congr; intro t _; simp
    rw [hc, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero m), sub_zero,
      Nat.factorial_zero, Nat.add_zero, Nat.factorial_succ]
    push_cast
    field_simp
  | succ n ih =>
    intro m
    have hu : ∀ x ∈ uIcc (0:ℝ) 1,
        HasDerivAt (fun t : ℝ => (1 - t) ^ (n + 1)) (-(((n:ℝ) + 1)) * (1 - x) ^ n) x := by
      intro x _
      have hb : HasDerivAt (fun t : ℝ => (1:ℝ) - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1:ℝ)
      have h := (hb.pow (n + 1))
      have heq : (↑(n + 1) * (1 - x) ^ (n + 1 - 1) * (-1)) = -(((n:ℝ) + 1)) * (1 - x) ^ n := by
        push_cast; ring
      rwa [heq] at h
    have hv : ∀ x ∈ uIcc (0:ℝ) 1,
        HasDerivAt (fun t : ℝ => t ^ (m + 1) / (m + 1)) (x ^ m) x := by
      intro x _
      have h := (hasDerivAt_pow (m + 1) x).div_const ((m : ℝ) + 1)
      have heq : (↑(m + 1) * x ^ (m + 1 - 1)) / ((m:ℝ) + 1) = x ^ m := by
        have : ((m:ℝ) + 1) ≠ 0 := by positivity
        push_cast; field_simp
      rwa [heq] at h
    have hu' : IntervalIntegrable (fun x => -(((n:ℝ) + 1)) * (1 - x) ^ n) volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have hv' : IntervalIntegrable (fun x => x ^ m) volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have hIBP := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    have hmne : ((m:ℝ) + 1) ≠ 0 := by positivity
    have hR : (∫ x in (0:ℝ)..1, -((n:ℝ) + 1) * (1 - x) ^ n * (x ^ (m + 1) / ((m:ℝ) + 1)))
        = (-((n:ℝ) + 1) / ((m:ℝ) + 1))
          * ((m + 1).factorial * n.factorial / ((m + 1) + n + 1).factorial : ℝ) := by
      rw [← ih (m + 1), ← intervalIntegral.integral_const_mul]
      apply integral_congr; intro x _; ring
    rw [show (∫ t in (0:ℝ)..1, t ^ m * (1 - t) ^ (n + 1))
          = ∫ t in (0:ℝ)..1, (1 - t) ^ (n + 1) * t ^ m from
        integral_congr (fun t _ => by ring)]
    rw [hIBP, hR, Nat.factorial_succ n]
    have hden : (m + 1) + n + 1 = m + (n + 1) + 1 := by omega
    rw [hden, Nat.factorial_succ m]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero n), zero_mul, one_pow,
      zero_pow (Nat.succ_ne_zero m), mul_zero, zero_div, sub_zero, zero_sub]
    have hfac : (0:ℝ) < ((m + (n + 1) + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    push_cast
    field_simp

/-- A **budget monomial** `bmono e d c t = c · t^e · (1−t)^d`, the shared shape of
every inner-peeled integrand. Its `∫₀¹` value follows from `betaNat`. -/
noncomputable def bmono (e d : ℕ) (c : ℝ) (t : ℝ) : ℝ := c * t ^ e * (1 - t) ^ d

/-- `bmono` is continuous (polynomial). -/
theorem bmono_continuous (e d : ℕ) (c : ℝ) : Continuous (bmono e d c) := by
  unfold bmono; fun_prop

/-- `bmono e d c · bmono e' d' c' = bmono (e+e') (d+d') (c·c')` pointwise. -/
theorem bmono_mul (e d e' d' : ℕ) (c c' t : ℝ) :
    bmono e d c t * bmono e' d' c' t = bmono (e + e') (d + d') (c * c') t := by
  unfold bmono; rw [pow_add, pow_add]; ring

/-- `∫₀¹ bmono e d c = c · e! d! / (e+d+1)!`. -/
theorem bmono_integral (e d : ℕ) (c : ℝ) :
    (∫ t in (0:ℝ)..1, bmono e d c t)
      = c * (e.factorial * d.factorial / (e + d + 1).factorial) := by
  unfold bmono
  rw [show (∫ t in (0:ℝ)..1, c * t ^ e * (1 - t) ^ d)
        = ∫ t in (0:ℝ)..1, c * (t ^ e * (1 - t) ^ d) from integral_congr (fun t _ => by ring),
    intervalIntegral.integral_const_mul, betaNat d e]

/-! ## The `ℚ`-valued carriers (mirror of `Salt/Twelve/Certificate.lean` at `k = 2`) -/

/-- A monomial `t₁^a t₂^b` with rational coefficient: `((a, b), c)`. -/
abbrev Mono₂ : Type := (ℕ × ℕ) × ℚ

/-- A rational polynomial in `t₁, t₂` as a finite formal `ℚ`-combination of monomials. -/
abbrev Poly₂ : Type := List Mono₂

/-- The `n = 2` Dirichlet integral `∫_{R₂} t₁^a t₂^b = a! b! / (a+b+2)!` (exact `ℚ`). -/
def DInt₂ (a b : ℕ) : ℚ := (a.factorial * b.factorial : ℚ) / (a + b + 2).factorial

/-- The `J₁` bilinear kernel:
`jKer₁ a b a' b' = (b+b')!·(a+a'+2)! / ((a+1)(a'+1)·(a+a'+b+b'+3)!)`. -/
def jKer₁ (a b a' b' : ℕ) : ℚ :=
  ((b + b').factorial * (a + a' + 2).factorial : ℚ) /
    (((a + 1) * (a' + 1) : ℕ) * (a + a' + b + b' + 3).factorial)

/-- The `J₂` bilinear kernel (the `a ↔ b` mirror):
`jKer₂ a b a' b' = (a+a')!·(b+b'+2)! / ((b+1)(b'+1)·(a+a'+b+b'+3)!)`. -/
def jKer₂ (a b a' b' : ℕ) : ℚ :=
  ((a + a').factorial * (b + b' + 2).factorial : ℚ) /
    (((b + 1) * (b' + 1) : ℕ) * (a + a' + b + b' + 3).factorial)

/-- `Ical₂ p = Σ_{m,m'} c c' · DInt₂ (a+a') (b+b')`, the exact `ℚ` value of
`∫_{R₂} (eval₂ p)²` — the `k = 2` mirror of `Salt.Twelve.Ical`. -/
def Ical₂ (p : Poly₂) : ℚ :=
  (p.map (fun m => (p.map (fun m' =>
    m.2 * m'.2 * DInt₂ (m.1.1 + m'.1.1) (m.1.2 + m'.1.2))).sum)).sum

/-- `JcalTot₂ p = Σ_{m,m'} c c' · (jKer₁ + jKer₂)`, the exact `ℚ` value of
`J₁ + J₂` at `eval₂ p`. -/
def JcalTot₂ (p : Poly₂) : ℚ :=
  (p.map (fun m => (p.map (fun m' =>
    m.2 * m'.2 * (jKer₁ m.1.1 m.1.2 m'.1.1 m'.1.2 + jKer₂ m.1.1 m.1.2 m'.1.1 m'.1.2))).sum)).sum

/-- The real polynomial `eval₂ p t₁ t₂ = Σ_{((a,b),c) ∈ p} c · t₁^a · t₂^b`. -/
noncomputable def eval₂ (p : Poly₂) (t₁ t₂ : ℝ) : ℝ :=
  (p.map (fun m => (m.2 : ℝ) * t₁ ^ m.1.1 * t₂ ^ m.1.2)).sum

/-! ## `dirichlet₂` — the atomic bridge -/

/-- **`dirichlet₂`.** The `n = 2` Dirichlet integral in real form, tied to the
rational `DInt₂`: `∫_{R₂} t₁^a t₂^b = (DInt₂ a b : ℝ)`. Inner slice by `integral_pow`,
outer by `betaNat`. -/
theorem dirichlet₂ (a b : ℕ) :
    (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), t₁ ^ a * t₂ ^ b)
      = ((DInt₂ a b : ℚ) : ℝ) := by
  have hinner : ∀ t₂ : ℝ, (∫ t₁ in (0:ℝ)..(1 - t₂), t₁ ^ a * t₂ ^ b)
      = bmono b (a + 1) ((1 : ℝ) / ((a:ℝ) + 1)) t₂ := by
    intro t₂
    rw [intervalIntegral.integral_mul_const, integral_pow, zero_pow (Nat.succ_ne_zero a), sub_zero]
    unfold bmono
    have hne : ((a:ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [integral_congr (fun t₂ _ => hinner t₂), bmono_integral]
  rw [DInt₂, show b + (a + 1) + 1 = a + b + 2 from by omega, Nat.factorial_succ a]
  have hne : ((a:ℝ) + 1) ≠ 0 := by positivity
  have hfac : (0:ℝ) < ((a + b + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp

/-! ## Continuity and the list-linearity of the outer `∫₀¹` -/

/-- `eval₂ p` is jointly continuous on the plane (a finite sum of monomials). -/
theorem eval₂_continuous (p : Poly₂) :
    Continuous (fun q : ℝ × ℝ => eval₂ p q.1 q.2) := by
  unfold eval₂
  induction p with
  | nil => simpa using continuous_const
  | cons m p' ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (by fun_prop : Continuous
      (fun q : ℝ × ℝ => (m.2 : ℝ) * q.1 ^ m.1.1 * q.2 ^ m.1.2)).add ih

/-- The `J₁`/`I₂` inner slice `t₁ ↦ eval₂ p t₁ t₂` is continuous. -/
theorem eval₂_slice₁_continuous (p : Poly₂) (t₂ : ℝ) :
    Continuous (fun t₁ => eval₂ p t₁ t₂) :=
  (eval₂_continuous p).comp (by fun_prop : Continuous (fun t₁ : ℝ => (t₁, t₂)))

/-- The `J₂` inner slice `t₂ ↦ eval₂ p t₁ t₂` is continuous. -/
theorem eval₂_slice₂_continuous (p : Poly₂) (t₁ : ℝ) :
    Continuous (fun t₂ => eval₂ p t₁ t₂) :=
  (eval₂_continuous p).comp (by fun_prop : Continuous (fun t₂ : ℝ => (t₁, t₂)))

/-- `eval₂ p` is continuous on `R₂` (trivially, from global continuity). -/
theorem eval₂_continuousOn (p : Poly₂) :
    ContinuousOn (Function.uncurry (eval₂ p)) R₂ :=
  (eval₂_continuous p).continuousOn

/-- Continuity of a finite list-sum of continuous functions. -/
theorem continuous_listSum {ι : Type*} (l : List ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i, Continuous (g i)) :
    Continuous (fun t => (l.map (fun i => g i t)).sum) := by
  induction l with
  | nil => simpa using continuous_const
  | cons i l' ih => simp only [List.map_cons, List.sum_cons]; exact (hg i).add ih

/-- **List-linearity of the outer integral.** For a family of continuous functions,
`∫₀¹` distributes over the finite list-sum. -/
theorem outer_split {ι : Type*} (l : List ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i, Continuous (g i)) :
    (∫ t in (0:ℝ)..1, (l.map (fun i => g i t)).sum)
      = (l.map (fun i => ∫ t in (0:ℝ)..1, g i t)).sum := by
  induction l with
  | nil => simp
  | cons i l' ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [intervalIntegral.integral_add ((hg i).intervalIntegrable 0 1)
      ((continuous_listSum l' g hg).intervalIntegrable 0 1), ih]

/-! ## List algebra of `eval₂` and the product `prod₂` -/

/-- `eval₂` of a cons. -/
theorem eval₂_cons (m : Mono₂) (q : Poly₂) (t₁ t₂ : ℝ) :
    eval₂ (m :: q) t₁ t₂ = (m.2 : ℝ) * t₁ ^ m.1.1 * t₂ ^ m.1.2 + eval₂ q t₁ t₂ := by
  simp [eval₂]

/-- `eval₂` is additive over list append. -/
theorem eval₂_append (p q : Poly₂) (t₁ t₂ : ℝ) :
    eval₂ (p ++ q) t₁ t₂ = eval₂ p t₁ t₂ + eval₂ q t₁ t₂ := by
  simp [eval₂, List.map_append, List.sum_append]

/-- The monomial product list: `prod₂ p q` represents `(eval₂ p)·(eval₂ q)`. -/
def prod₂ (p q : Poly₂) : Poly₂ :=
  p.flatMap (fun m => q.map (fun m' => ((m.1.1 + m'.1.1, m.1.2 + m'.1.2), m.2 * m'.2)))

/-- A monomial-scaled `eval₂`: multiplying every monomial of `q` by `c·t₁^a·t₂^b`. -/
theorem eval₂_map_mul (a b : ℕ) (c : ℚ) (q : Poly₂) (t₁ t₂ : ℝ) :
    eval₂ (q.map (fun m' => ((a + m'.1.1, b + m'.1.2), c * m'.2))) t₁ t₂
      = ((c : ℝ) * t₁ ^ a * t₂ ^ b) * eval₂ q t₁ t₂ := by
  induction q with
  | nil => simp [eval₂]
  | cons m' q' ih =>
    rw [List.map_cons, eval₂_cons, ih, eval₂_cons]
    push_cast [pow_add]
    ring

/-- **`eval₂` respects the product.** `eval₂ (prod₂ p q) = eval₂ p · eval₂ q` pointwise. -/
theorem eval₂_prod₂ (p q : Poly₂) (t₁ t₂ : ℝ) :
    eval₂ (prod₂ p q) t₁ t₂ = eval₂ p t₁ t₂ * eval₂ q t₁ t₂ := by
  induction p with
  | nil => simp [prod₂, eval₂]
  | cons m p' ih =>
    have hstep : prod₂ (m :: p') q
        = (q.map (fun m' => ((m.1.1 + m'.1.1, m.1.2 + m'.1.2), m.2 * m'.2))) ++ prod₂ p' q := by
      simp only [prod₂, List.flatMap_cons]
    rw [hstep, eval₂_append, eval₂_map_mul m.1.1 m.1.2 m.2 q, ih, eval₂_cons]
    ring

/-- The rational double-sum identity: the flat product-list sum equals the double sum
(the `k = 2` analogue of `Salt.Twelve.simplexInt_mul`). -/
theorem map_sum_prod₂ (f : ℕ → ℕ → ℚ) (p q : Poly₂) :
    ((prod₂ p q).map (fun m => m.2 * f m.1.1 m.1.2)).sum
      = (p.map (fun a =>
          (q.map (fun b => a.2 * b.2 * f (a.1.1 + b.1.1) (a.1.2 + b.1.2))).sum)).sum := by
  induction p with
  | nil => simp [prod₂]
  | cons a p' ih =>
    have hstep : prod₂ (a :: p') q
        = (q.map (fun b => ((a.1.1 + b.1.1, a.1.2 + b.1.2), a.2 * b.2))) ++ prod₂ p' q := by
      simp only [prod₂, List.flatMap_cons]
    rw [hstep, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def]

/-- Casting `ℚ→ℝ` commutes with the list sum. -/
theorem cast_sum_map {α : Type*} (l : List α) (g : α → ℚ) :
    (l.map (fun m => ((g m : ℚ) : ℝ))).sum = (((l.map g).sum : ℚ) : ℝ) := by
  induction l with
  | nil => simp
  | cons a l' ih => simp [ih]

/-- The per-monomial outer integral of the `I₂` inner peel: `∫₀¹ bmono b (a+1) (c/(a+1))
= (c · DInt₂ a b : ℝ)`. -/
theorem bmono_val₁ (a b : ℕ) (c : ℚ) :
    (∫ t₂ in (0:ℝ)..1, bmono b (a + 1) ((c : ℝ) / ((a:ℝ) + 1)) t₂)
      = ((c * DInt₂ a b : ℚ) : ℝ) := by
  rw [bmono_integral, DInt₂, show b + (a + 1) + 1 = a + b + 2 from by omega, Nat.factorial_succ a]
  have hne : ((a:ℝ) + 1) ≠ 0 := by positivity
  have hfac : (0:ℝ) < ((a + b + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp

/-- **The `J₁`/`I₂` inner peel.** `∫₀^{1−t₂} eval₂ q t₁ dt₁` collapses to a finite sum
of budget monomials in `t₂`. -/
theorem inner_peel₁ (q : Poly₂) (t₂ : ℝ) :
    (∫ t₁ in (0:ℝ)..(1 - t₂), eval₂ q t₁ t₂)
      = (q.map (fun m => bmono m.1.2 (m.1.1 + 1) ((m.2 : ℝ) / ((m.1.1:ℝ) + 1)) t₂)).sum := by
  induction q with
  | nil => simp [eval₂]
  | cons m q' ih =>
    rw [integral_congr (fun t₁ _ => eval₂_cons m q' t₁ t₂),
      intervalIntegral.integral_add
        ((by fun_prop : Continuous
            (fun t₁ : ℝ => (m.2:ℝ) * t₁ ^ m.1.1 * t₂ ^ m.1.2)).intervalIntegrable 0 (1 - t₂))
        ((eval₂_slice₁_continuous q' t₂).intervalIntegrable 0 (1 - t₂)),
      ih]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    rw [integral_congr (fun t₁ _ =>
        (by ring : (m.2:ℝ) * t₁ ^ m.1.1 * t₂ ^ m.1.2 = t₁ ^ m.1.1 * ((m.2:ℝ) * t₂ ^ m.1.2))),
      intervalIntegral.integral_mul_const, integral_pow, zero_pow (Nat.succ_ne_zero m.1.1),
      sub_zero]
    unfold bmono
    have hne : ((m.1.1:ℝ) + 1) ≠ 0 := by positivity
    field_simp

/-! ## The bridge (linearity through the iterated integrals) -/

/-- **The `I₂` bridge.** `I₂ (eval₂ p) = (Ical₂ p : ℝ)`. -/
theorem I₂_eval₂ (p : Poly₂) : I₂ (eval₂ p) = ((Ical₂ p : ℚ) : ℝ) := by
  unfold I₂
  have hpt : ∀ t₁ t₂ : ℝ, (eval₂ p t₁ t₂) ^ 2 = eval₂ (prod₂ p p) t₁ t₂ := by
    intro t₁ t₂; rw [eval₂_prod₂, pow_two]
  have hsq : (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), (eval₂ p t₁ t₂) ^ 2)
      = ∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), eval₂ (prod₂ p p) t₁ t₂ := by
    apply integral_congr; intro t₂ _
    apply integral_congr; intro t₁ _
    exact hpt t₁ t₂
  rw [hsq,
    integral_congr (fun t₂ _ => inner_peel₁ (prod₂ p p) t₂),
    outer_split (prod₂ p p)
      (fun m t₂ => bmono m.1.2 (m.1.1 + 1) ((m.2:ℝ) / ((m.1.1:ℝ) + 1)) t₂)
      (fun m => bmono_continuous _ _ _),
    List.map_congr_left (fun m _ => bmono_val₁ m.1.1 m.1.2 m.2),
    cast_sum_map]
  congr 1
  exact map_sum_prod₂ DInt₂ p p

/-! ### The `J` bridge: peel, square, split -/

/-- Square of a finite list-sum as a double sum. -/
theorem sum_sq {α : Type*} (l : List α) (f : α → ℝ) :
    ((l.map f).sum) ^ 2 = (l.map (fun a => (l.map (fun b => f a * f b)).sum)).sum := by
  rw [pow_two, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  rw [← List.sum_map_mul_left]

/-- List-sum distributes over pointwise addition. -/
theorem listSum_map_add {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l' ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The `J₁` half of the rational total: `Σ_{m,m'} c c' · jKer₁`. -/
def Jcal₂A (p : Poly₂) : ℚ :=
  (p.map (fun m => (p.map (fun m' =>
    m.2 * m'.2 * jKer₁ m.1.1 m.1.2 m'.1.1 m'.1.2)).sum)).sum

/-- The `J₂` half of the rational total: `Σ_{m,m'} c c' · jKer₂`. -/
def Jcal₂B (p : Poly₂) : ℚ :=
  (p.map (fun m => (p.map (fun m' =>
    m.2 * m'.2 * jKer₂ m.1.1 m.1.2 m'.1.1 m'.1.2)).sum)).sum

/-- `JcalTot₂ = Jcal₂A + Jcal₂B` (the `jKer₁ + jKer₂` splits over the double sum). -/
theorem JcalTot₂_split (p : Poly₂) : JcalTot₂ p = Jcal₂A p + Jcal₂B p := by
  unfold JcalTot₂ Jcal₂A Jcal₂B
  rw [← listSum_map_add]
  refine congrArg List.sum (List.map_congr_left (fun m _ => ?_))
  rw [← listSum_map_add]
  exact congrArg List.sum (List.map_congr_left (fun m' _ => by rw [mul_add]))

/-- **The `J₂` inner peel** (mirror of `inner_peel₁`, roles of `t₁, t₂` swapped). -/
theorem inner_peel₂ (q : Poly₂) (t₁ : ℝ) :
    (∫ t₂ in (0:ℝ)..(1 - t₁), eval₂ q t₁ t₂)
      = (q.map (fun m => bmono m.1.1 (m.1.2 + 1) ((m.2 : ℝ) / ((m.1.2:ℝ) + 1)) t₁)).sum := by
  induction q with
  | nil => simp [eval₂]
  | cons m q' ih =>
    rw [integral_congr (fun t₂ _ => eval₂_cons m q' t₁ t₂),
      intervalIntegral.integral_add
        ((by fun_prop : Continuous
            (fun t₂ : ℝ => (m.2:ℝ) * t₁ ^ m.1.1 * t₂ ^ m.1.2)).intervalIntegrable 0 (1 - t₁))
        ((eval₂_slice₂_continuous q' t₁).intervalIntegrable 0 (1 - t₁)),
      ih]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    rw [integral_congr (fun t₂ _ =>
        (by ring : (m.2:ℝ) * t₁ ^ m.1.1 * t₂ ^ m.1.2 = t₂ ^ m.1.2 * ((m.2:ℝ) * t₁ ^ m.1.1))),
      intervalIntegral.integral_mul_const, integral_pow, zero_pow (Nat.succ_ne_zero m.1.2),
      sub_zero]
    unfold bmono
    have hne : ((m.1.2:ℝ) + 1) ≠ 0 := by positivity
    field_simp

/-- The per-pair `J₁` integral: `∫₀¹ (peel_m)(peel_m') = (c c' · jKer₁ : ℝ)`. -/
theorem jpair₁ (a b a' b' : ℕ) (c c' : ℚ) :
    (∫ t in (0:ℝ)..1, bmono b (a + 1) ((c:ℝ) / ((a:ℝ) + 1)) t
        * bmono b' (a' + 1) ((c':ℝ) / ((a':ℝ) + 1)) t)
      = ((c * c' * jKer₁ a b a' b' : ℚ) : ℝ) := by
  rw [integral_congr (fun t _ => bmono_mul b (a + 1) b' (a' + 1) _ _ t), bmono_integral,
    show (a + 1) + (a' + 1) = a + a' + 2 from by omega,
    show b + b' + (a + a' + 2) + 1 = a + a' + b + b' + 3 from by omega, jKer₁]
  have h1 : ((a:ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((a':ℝ) + 1) ≠ 0 := by positivity
  have hfac : (0:ℝ) < ((a + a' + b + b' + 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp

/-- The per-pair `J₂` integral: `∫₀¹ (peel_m)(peel_m') = (c c' · jKer₂ : ℝ)`. -/
theorem jpair₂ (a b a' b' : ℕ) (c c' : ℚ) :
    (∫ t in (0:ℝ)..1, bmono a (b + 1) ((c:ℝ) / ((b:ℝ) + 1)) t
        * bmono a' (b' + 1) ((c':ℝ) / ((b':ℝ) + 1)) t)
      = ((c * c' * jKer₂ a b a' b' : ℚ) : ℝ) := by
  rw [integral_congr (fun t _ => bmono_mul a (b + 1) a' (b' + 1) _ _ t), bmono_integral,
    show (b + 1) + (b' + 1) = b + b' + 2 from by omega,
    show a + a' + (b + b' + 2) + 1 = a + a' + b + b' + 3 from by omega, jKer₂]
  have h1 : ((b:ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((b':ℝ) + 1) ≠ 0 := by positivity
  have hfac : (0:ℝ) < ((a + a' + b + b' + 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp

/-- One row of the `J₁` double sum: integrate a fixed peel `m` against every peel `m'`. -/
theorem J₁_row (p : Poly₂) (m : Mono₂) :
    (∫ t in (0:ℝ)..1, (p.map (fun m' =>
        bmono m.1.2 (m.1.1 + 1) ((m.2:ℝ) / ((m.1.1:ℝ) + 1)) t
          * bmono m'.1.2 (m'.1.1 + 1) ((m'.2:ℝ) / ((m'.1.1:ℝ) + 1)) t)).sum)
      = (((p.map (fun m' => m.2 * m'.2 * jKer₁ m.1.1 m.1.2 m'.1.1 m'.1.2)).sum : ℚ) : ℝ) := by
  rw [outer_split p (fun m' t => bmono m.1.2 (m.1.1 + 1) ((m.2:ℝ) / ((m.1.1:ℝ) + 1)) t
        * bmono m'.1.2 (m'.1.1 + 1) ((m'.2:ℝ) / ((m'.1.1:ℝ) + 1)) t)
      (fun m' => (bmono_continuous _ _ _).mul (bmono_continuous _ _ _)),
    List.map_congr_left (fun m' _ => jpair₁ m.1.1 m.1.2 m'.1.1 m'.1.2 m.2 m'.2),
    cast_sum_map]

/-- One row of the `J₂` double sum. -/
theorem J₂_row (p : Poly₂) (m : Mono₂) :
    (∫ t in (0:ℝ)..1, (p.map (fun m' =>
        bmono m.1.1 (m.1.2 + 1) ((m.2:ℝ) / ((m.1.2:ℝ) + 1)) t
          * bmono m'.1.1 (m'.1.2 + 1) ((m'.2:ℝ) / ((m'.1.2:ℝ) + 1)) t)).sum)
      = (((p.map (fun m' => m.2 * m'.2 * jKer₂ m.1.1 m.1.2 m'.1.1 m'.1.2)).sum : ℚ) : ℝ) := by
  rw [outer_split p (fun m' t => bmono m.1.1 (m.1.2 + 1) ((m.2:ℝ) / ((m.1.2:ℝ) + 1)) t
        * bmono m'.1.1 (m'.1.2 + 1) ((m'.2:ℝ) / ((m'.1.2:ℝ) + 1)) t)
      (fun m' => (bmono_continuous _ _ _).mul (bmono_continuous _ _ _)),
    List.map_congr_left (fun m' _ => jpair₂ m.1.1 m.1.2 m'.1.1 m'.1.2 m.2 m'.2),
    cast_sum_map]

/-- **The `J₁` bridge.** `J₁ (eval₂ p) = (Jcal₂A p : ℝ)`. -/
theorem J₁_eval₂ (p : Poly₂) : J₁ (eval₂ p) = ((Jcal₂A p : ℚ) : ℝ) := by
  unfold J₁
  have hpt : ∀ t₂ : ℝ, (∫ t₁ in (0:ℝ)..(1 - t₂), eval₂ p t₁ t₂) ^ 2
      = (p.map (fun m => (p.map (fun m' =>
          bmono m.1.2 (m.1.1 + 1) ((m.2:ℝ) / ((m.1.1:ℝ) + 1)) t₂
            * bmono m'.1.2 (m'.1.1 + 1) ((m'.2:ℝ) / ((m'.1.1:ℝ) + 1)) t₂)).sum)).sum := by
    intro t₂; rw [inner_peel₁ p t₂, sum_sq]
  rw [integral_congr (fun t₂ _ => hpt t₂),
    outer_split p (fun m t₂ => (p.map (fun m' =>
        bmono m.1.2 (m.1.1 + 1) ((m.2:ℝ) / ((m.1.1:ℝ) + 1)) t₂
          * bmono m'.1.2 (m'.1.1 + 1) ((m'.2:ℝ) / ((m'.1.1:ℝ) + 1)) t₂)).sum)
      (fun m => continuous_listSum p _
        (fun m' => (bmono_continuous _ _ _).mul (bmono_continuous _ _ _))),
    List.map_congr_left (fun m _ => J₁_row p m),
    cast_sum_map]
  rfl

/-- **The `J₂` bridge.** `J₂ (eval₂ p) = (Jcal₂B p : ℝ)`. -/
theorem J₂_eval₂ (p : Poly₂) : J₂ (eval₂ p) = ((Jcal₂B p : ℚ) : ℝ) := by
  unfold J₂
  have hpt : ∀ t₁ : ℝ, (∫ t₂ in (0:ℝ)..(1 - t₁), eval₂ p t₁ t₂) ^ 2
      = (p.map (fun m => (p.map (fun m' =>
          bmono m.1.1 (m.1.2 + 1) ((m.2:ℝ) / ((m.1.2:ℝ) + 1)) t₁
            * bmono m'.1.1 (m'.1.2 + 1) ((m'.2:ℝ) / ((m'.1.2:ℝ) + 1)) t₁)).sum)).sum := by
    intro t₁; rw [inner_peel₂ p t₁, sum_sq]
  rw [integral_congr (fun t₁ _ => hpt t₁),
    outer_split p (fun m t₁ => (p.map (fun m' =>
        bmono m.1.1 (m.1.2 + 1) ((m.2:ℝ) / ((m.1.2:ℝ) + 1)) t₁
          * bmono m'.1.1 (m'.1.2 + 1) ((m'.2:ℝ) / ((m'.1.2:ℝ) + 1)) t₁)).sum)
      (fun m => continuous_listSum p _
        (fun m' => (bmono_continuous _ _ _).mul (bmono_continuous _ _ _))),
    List.map_congr_left (fun m _ => J₂_row p m),
    cast_sum_map]
  rfl

/-- **The `J` bridge.** `J₁ (eval₂ p) + J₂ (eval₂ p) = (JcalTot₂ p : ℝ)`. -/
theorem J_eval₂ (p : Poly₂) :
    J₁ (eval₂ p) + J₂ (eval₂ p) = ((JcalTot₂ p : ℚ) : ℝ) := by
  rw [J₁_eval₂, J₂_eval₂, JcalTot₂_split]
  push_cast
  ring

/-! ## The headliner and the witness example -/

/-- **The rational dual of `M5_cert`.** No rational polynomial weight can cross the
twin gate. -/
theorem no_twin_certificate :
    ¬ ∃ p : Poly₂, 0 < Ical₂ p ∧ 2 * Ical₂ p < JcalTot₂ p := by
  rintro ⟨p, hI, hJ⟩
  apply no_twin_weight
  refine ⟨eval₂ p, eval₂_continuousOn p, ?_, ?_⟩
  · rw [I₂_eval₂]; exact_mod_cast hI
  · rw [I₂_eval₂, J_eval₂]; exact_mod_cast hJ

/-- The degree-1 witness `Fw = 1 + (9/7)(1−t₁−t₂)` as a `Poly₂`
`[((0,0), 16/7), ((1,0), −9/7), ((0,1), −9/7)]`. -/
def FwPoly : Poly₂ := [((0, 0), 16 / 7), ((1, 0), -9 / 7), ((0, 1), -9 / 7)]

/-- **The positive companion.** The witness certifies `(1383/1000)·Ical₂ ≤ JcalTot₂`,
grounding non-vacuity; `Ical₂ FwPoly = 209/196`, `JcalTot₂ FwPoly = 1084/735` match
`Witness.lean`'s real values through the bridge. -/
theorem twin_certificate_example :
    ∃ p : Poly₂, 0 < Ical₂ p ∧ (1383 / 1000 : ℚ) * Ical₂ p ≤ JcalTot₂ p := by
  refine ⟨FwPoly, ?_, ?_⟩ <;>
    · norm_num [Ical₂, JcalTot₂, FwPoly, DInt₂, jKer₁, jKer₂, Nat.factorial]

/-! ## Cross-check against `Witness.lean` (the bridge in action)

The rational carriers of `FwPoly` equal `Witness.lean`'s independently-landed real
carriers of `Fw`, *through the bridge* — validating the whole tie end to end. -/

/-- `FwPoly` evaluates to `Witness.lean`'s `Fw` pointwise: both are `16/7 − (9/7)(t₁+t₂)`. -/
theorem eval₂_FwPoly (t₁ t₂ : ℝ) : eval₂ FwPoly t₁ t₂ = Fw t₁ t₂ := by
  simp only [eval₂, FwPoly, Fw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pow_zero, pow_one, mul_one]
  push_cast; ring

/-- The rational values `Ical₂ FwPoly`, `JcalTot₂ FwPoly` coincide with the real
carriers `I₂ Fw`, `J₁ Fw + J₂ Fw` of `Witness.lean` — the bridge closes the loop
(`I₂ Fw = 209/196`, `J₁ Fw + J₂ Fw = 1084/735`). -/
theorem bridge_consistency :
    (Ical₂ FwPoly : ℝ) = I₂ Fw ∧ (JcalTot₂ FwPoly : ℝ) = J₁ Fw + J₂ Fw := by
  have hfun : eval₂ FwPoly = Fw := by funext t₁ t₂; exact eval₂_FwPoly t₁ t₂
  refine ⟨?_, ?_⟩
  · rw [← I₂_eval₂, hfun]
  · rw [← J_eval₂, hfun]

/-- The exact rational value `Ical₂ FwPoly = 209/196` (matches `Witness.I₂_Fw`). -/
example : Ical₂ FwPoly = 209 / 196 := by
  norm_num [Ical₂, FwPoly, DInt₂, Nat.factorial]

/-- The exact rational value `JcalTot₂ FwPoly = 1084/735` (matches `Witness.J₁_Fw + J₂_Fw`). -/
example : JcalTot₂ FwPoly = 1084 / 735 := by
  norm_num [JcalTot₂, FwPoly, jKer₁, jKer₂, Nat.factorial]

end Salt.TwinBar
