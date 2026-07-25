/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CenterSupply

/-!
# RHS-GRADE — the `hRHS` socket of `center_halasz_supply` (the joint-head composition)

`CenterSupply.center_halasz_supply` (:296) carries ONE named hypothesis, `hRHS`:

```
∀ k ∈ [⌊X⌋₊, N],
  ‖prop21RHS (fun p => g p · p^{−i(t₀+t₁)}) (t₀+t₁) k (k/√log k) (1+1/log k)
      ((log k)⁴) (1/log((log k)⁴))‖
    ≤ C₁·k·exp(−(1/(2e))·𝔻²(seamCoeff (ellLin g) 1 t₀, p^{it₁}; X))
```

This file works that socket on the composable chain named in `CenterSupply`'s route note:
`joint_cs_factoring` → `bridge_adapter` → `joint_sigma_integral` (the FLAT exit — NOT
`sigma_wiring`'s heritage `(1+M)` shape).

## §0 — THE BOOKKEEPING PAGE (the datum/twist reconciliation, worked first)

Two distinct presentations of the same distance meet here, and the reconciliation is
EXACT (no inequality is spent on it):

* the target's distance is `𝔻²(seamCoeff (ellLin g) 1 t₀, costwist t₁; X)`, i.e. — by
  `HalaszHead.seamCoeff_trivial_dist_eq` — `𝔻²(ellLin g, costwist (t₁+t₀); X)`: the bare
  datum's distance to the frequency `t₀+t₁`, at the OUTER scale `X`;
* `PretSupply.supF_pret_pointwise`, instantiated at the joint head's own datum
  `g' := (p ↦ g p·p^{−i(t₀+t₁)})` and centre `t₀' := t₀+t₁`, carries
  `𝔻²(ellLin g', costwist (t−t₀'); k)`, which is `𝔻²(ellLin g, costwist t; k)` — the bare
  datum's distance to the RUNNING frequency `t`, at the REPRESENTATION's scale `k ≥ X`.

So the ∀t sup over the joint head's `t`-line needs exactly two moves:

1. **the scale bridge (FREE direction)** — `pretDistSq_mono_scale`: the prime sum over
   `p ≤ k` extends the one over `p ≤ X` and every term is `≥ 0` (1-bounded data), so
   `𝔻²(·;X) ≤ 𝔻²(·;k)` and `e^{−c𝔻²(k)} ≤ e^{−c𝔻²(X)}`.  Nothing is lost;
2. **the minimality** (`hmin`, the row's minimizer semantics, ⟦THE TWO-M READING⟧) —
   stated in the TARGET's slot, `∀v, 𝔻²(seam, costwist t₁; X) ≤ 𝔻²(seam, costwist v; X)`,
   and transported to the running frequency by `seamCoeff_trivial_dist_eq` at `v := t−t₀`
   (the shift identity `𝔻²(seamCoeff f 1 t₀, costwist v) = 𝔻²(f, costwist (v+t₀))` is what
   aligns the two twist slots).

`center_dist_floor` is the composite: `∀t, M ≤ 𝔻²(ellLin g', costwist (t−t₀'); k)` with
`M` the target's own distance.  This is the `hMt` antecedent of
`PretSupply.supF_pret_majorant_sigma` byte-for-byte, and it is what makes the `t`-uniform
`supF` of `joint_cs_factoring` exist at all (the residual PretSupply's docstring records:
"a `t`-uniform `supF` needs a floor valid on the WHOLE line").

**THE `hmin` QUANTIFIER RANGE — recorded, not papered over.**  `hmin` here quantifies over
`∀ v : ℝ` (the minimality on the WHOLE frequency line), which is STRICTLY STRONGER than the
⟦TWO-M⟧-ratified centre semantics (`t₁` the global minimizer of `M(f;X)` over `|t| ≤ X`).
The gap is forced, not chosen: `joint_cs_factoring`'s `hsupF` quantifies over all `t : ℝ`
(PretSupply's own recorded residual), so the floor must hold there.  Two honest closures
exist and neither is attempted here: (a) restrict the `t`-range BEFORE the sup (the A-10
ball-centre dichotomy — the ball leg only ever sees `|t−t₁| ≤ seamRad X`), or (b) a
large-`|t|` argument at the representation scale `k`.  Note also that the infimum over `ℝ`
of `v ↦ 𝔻²(f, costwist v; X)` — an almost-periodic function — need not be ATTAINED, so a
consumer must supply `hmin` from structure, not from compactness.

## §5 — THE GRADE, HONESTLY (read this before consuming anything below)

The composition lands the SHAPE `‖prop21RHS‖ ≤ Cfin(k)·k·e^{−cM}` with an EXPLICIT `Cfin`,
and `Cfin` is **not** at the ε-cap: with `L := log k`,

  `Cfin ≍ C·L·log L`   (the `Tsplit`-sharp kernel face; `C·L^{3/2}` on the crude face),

against the cap `C₁ ≍ (log X)^{1/1000}` the ε-page allows.  The deficit is a full `L·log L`,
and it is STRUCTURAL on this route, not a slack: the σ-cutoff returns `L`
(`joint_sigma_integral`), the window-mass product returns a second `L`
(`min(L,1/σ)² ≤ L·(1/σ)`, `window_bridge`), and the `α`-integral returns only `1/L`
(`(X+h)^{−α}`), so the kernel's own `L¹` mass — `Θ(X·log L)` sharp, `Θ(X·√L)` crude — is
multiplied by `L`, not divided.  **`BridgeAdapt`'s own grade page states this landing
verbatim** ("the sharp kernel face improves the `√L` to `log L` (`Agrade ≍ X·L·log L`)");
`JointHead`'s HGRADE page quotes `X·log log X` for the KERNEL LEG ALONE (it does not carry
the window-mass `L`), and `CenterSupply`'s docstring inherits that reading.  Recorded as a
finding; per iron rule 1 / the SF-EXIT law the socket is NOT forced.

Consequently the terminal statements here are stated **against the grade socket**
(`hgrade : Agrade ≤ C₁·k`, the `hRHS_discharged_joint` pattern), with `rhs_grade_at_scale`
supplying the machine-checked concrete `Agrade` so that the deficit is a checked
inequality rather than a prose claim.  The constant-`X` grade remains reachable only
through the mixed-line Plancherel bridge (`JointHead`'s OTHER named residual), which
diagonalizes the kernel WITH the window legs and never incurs the standalone mass.

## The integrability sockets (which are discharged, which are carried)

DISCHARGED here (continuity ⇒ interval-integrability, at the concrete `Fbound`):
`hIσ` and `hIshift` of `bridge_adapter`, and `hint` of `joint_sigma_integral`
(`sigma_core_integrable_rhs`, the local re-derivation of `PretSupply`'s private
`sigma_core_integrable_pret`).  CARRIED as named hypotheses (the house
conditional-assembly form, exactly as `joint_cs_factoring` itself carries them):
`hIβ`, `hIβ'`, `hIα`, `hIα'` — the `β`- and `α`-level integrability of `supF·crossKer`
and of the `prop21RHS` integrand.  These are plumbing over `crossKer`, whose
`β`-continuity is a dominated-convergence page in its own right; nothing here weakens
them and nothing here assumes an analytic input beyond them.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §0 — the bookkeeping page: the datum/twist/scale reconciliation -/

/-- **The scale bridge (`pretDistSq_mono_scale`) — the FREE direction.**  For 1-bounded
data the pretentious distance is monotone in the scale: the prime sum over `p ≤ z`
contains the one over `p ≤ x` and every term is nonnegative
(`pretDistSq_term_nonneg`).  Hence `e^{−c·𝔻²(·;z)} ≤ e^{−c·𝔻²(·;x)}` for `x ≤ z` — which
is why the joint head may carry its distance at the REPRESENTATION scale `k` while the
target states it at the OUTER scale `X ≤ k`. -/
theorem pretDistSq_mono_floor {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {x z : ℝ} (hfloor : ⌊x⌋₊ ≤ ⌊z⌋₊) :
    pretDistSq f g x ≤ pretDistSq f g z := by
  unfold pretDistSq
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p hp _
    rw [Finset.mem_filter] at hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
    exact div_nonneg (pretDistSq_term_nonneg (hf p) (hg p)) hppos.le

/-- The scale bridge in its `x ≤ z` form (`Nat.floor_mono`). -/
theorem pretDistSq_mono_scale {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {x z : ℝ} (hxz : x ≤ z) : pretDistSq f g x ≤ pretDistSq f g z :=
  pretDistSq_mono_floor hf hg (Nat.floor_mono hxz)

/-- `pretDistSq` reads its left datum only at primes. -/
theorem pretDistSq_congr_primes {f₁ f₂ g : ℕ → ℂ} (h : ∀ p : ℕ, p.Prime → f₁ p = f₂ p)
    (x : ℝ) : pretDistSq f₁ g x = pretDistSq f₂ g x := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [h p (Finset.mem_filter.mp hp).2]

/-- **The two datum presentations agree at primes.**  `ellLin` of the TWISTED prime datum
(what `prop21RHS`/`joint_cs_factoring` carry) and the seam coefficient at the twisted
centre (what the target's distance carries) are the same function on primes:
`ellLin (p ↦ g p·p^{−iu}) p = seamCoeff (ellLin g) 1 u p`. -/
lemma ellLin_twist_prime (g : ℕ → ℂ) (u : ℝ) {p : ℕ} (hp : p.Prime) :
    ellLin (fun q => g q * (q : ℂ) ^ (-(u : ℂ) * I)) p
      = seamCoeff (ellLin g) (fun _ => 1) u p := by
  rw [ellLin_apply_prime (fun q => g q * (q : ℂ) ^ (-(u : ℂ) * I)) hp]
  unfold seamCoeff
  rw [if_neg hp.ne_zero, ellLin_apply_prime g hp]
  ring

/-- **The twisted-datum distance identity.**  `𝔻²(ellLin (g·p^{−iu}), costwist v; z)
= 𝔻²(ellLin g, costwist (v+u); z)`: the joint head's twisted datum at frequency `v` is the
bare datum at the shifted frequency `v+u`.  (`pretDistSq_congr_primes` ∘
`HalaszHead.seamCoeff_trivial_dist_eq`.) -/
theorem twisted_datum_dist_eq (g : ℕ → ℂ) (u v z : ℝ) :
    pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(u : ℂ) * I))) (costwist v) z
      = pretDistSq (ellLin g) (costwist (v + u)) z := by
  rw [pretDistSq_congr_primes (fun p hp => ellLin_twist_prime g u hp),
    seamCoeff_trivial_dist_eq]

/-- **§0's EXIT — the `t`-uniform distance floor (`center_dist_floor`).**  Under the row's
minimality semantics at the centre (`hmin`, ⟦THE TWO-M READING⟧: `t₁` minimizes the
twist slot at scale `X`), the target's own distance

  `M := 𝔻²(seamCoeff (ellLin g) 1 t₀, costwist t₁; X)`

is a floor for the joint head's distance at EVERY frequency `t` and at the representation
scale `k ≥ X`:

  `∀ t, M ≤ 𝔻²(ellLin (g·p^{−i(t₀+t₁)}), costwist (t−(t₀+t₁)); k)`.

Two exact moves and one free inequality: the twist-shift identity aligns the slots
(`twisted_datum_dist_eq` / `seamCoeff_trivial_dist_eq`), `hmin` at `v := t−t₀` supplies the
frequency, and `pretDistSq_mono_floor` the scale (the hypothesis is the FLOOR form
`⌊X⌋₊ ≤ ⌊z⌋₊`, so the consumer's `k ≥ ⌊X⌋₊` — not `k ≥ X` — suffices).  This is
`supF_pret_majorant_sigma`'s `hMt` antecedent byte-for-byte — the residual PretSupply's
docstring names ("a `t`-uniform `supF` needs a floor valid on the WHOLE line"), closed by
the minimizer.

`hmin` is stated on the WHOLE line (`∀ v : ℝ`) — stronger than the ⟦TWO-M⟧ `|t| ≤ X`
minimizer, and forced by `joint_cs_factoring`'s `∀ t : ℝ` sup; see the module docstring §0
for the two honest closures and the non-attainment caveat. -/
theorem center_dist_floor {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {t₀ t₁ X z : ℝ}
    (hXz : ⌊X⌋₊ ≤ ⌊z⌋₊)
    (hmin : ∀ v : ℝ, pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (t : ℝ) :
    pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)))
          (costwist (t - (t₀ + t₁))) z := by
  have hEll : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := ellLin_norm_le_one g hg
  have hcw : ∀ n : ℕ, ‖costwist t n‖ ≤ 1 := fun n => le_of_eq (costwist_norm t n)
  have h1 := twisted_datum_dist_eq g (t₀ + t₁) (t - (t₀ + t₁)) z
  rw [show t - (t₀ + t₁) + (t₀ + t₁) = t from by ring] at h1
  have h2 : pretDistSq (ellLin g) (costwist t) X ≤ pretDistSq (ellLin g) (costwist t) z :=
    pretDistSq_mono_floor hEll hcw hXz
  have h3 : pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist (t - t₀)) X
      = pretDistSq (ellLin g) (costwist t) X := by
    rw [seamCoeff_trivial_dist_eq, show t - t₀ + t₀ = t from by ring]
  have h4 := hmin (t - t₀)
  rw [h1]
  linarith

/-! ## §1 — the pin's concrete `Fbound`, and the `t`-uniform `supF` binder -/

/-- The absolute product constant `C_S·C_F` of `supF_pret_pointwise` (`C_S` the
mixed-argument ratio price, `C_F` the head's). -/
def rhsCSF : ℝ :=
  Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4))) * Real.exp (cpeel + (Real.log 4 + cpeel))

lemma rhsCSF_pos : 0 < rhsCSF := by
  unfold rhsCSF
  exact mul_pos (Real.exp_pos _) (Real.exp_pos _)

/-- **The pin's `Fbound`** — the σ-parametrized majorant of the joint head's `𝒮·𝓛` sup,
at the BALL arm's exponent `c = 1/(2e)` (S-3, route-scoped; **LIVE GUARD**: a §8.3
consumer citing this head is a STOP):

  `Fbound σ = C_S·C_F·(1/σ)·exp(−(1/(2e))·(M − 2·log(σ·L) − 48))`.

This is `supF_pret_majorant_sigma`'s right-hand side verbatim, so `hFb`/`hpret` are
`le_rfl` at every consumer below. -/
def rhsFbound (M L σ : ℝ) : ℝ :=
  rhsCSF * (1 / σ)
    * Real.exp (-(1 / (2 * Real.exp 1)) * (M - 2 * Real.log (σ * L) - 48))

lemma rhsFbound_nonneg (M L : ℝ) {σ : ℝ} (hσ : 0 < σ) : 0 ≤ rhsFbound M L σ :=
  mul_nonneg (mul_nonneg rhsCSF_pos.le (by positivity)) (Real.exp_nonneg _)

/-- **R1 — the `t`-uniform `supF` at the pin (`joint_supF_pin`).**  `joint_cs_factoring`'s
`hsupF` binder, discharged at the corpus pin (`c₀ = 1+1/L`, `y = L⁴`, `η = 1/log y`,
`L = log k`) from `supF_pret_pointwise` and the §0 floor:

  `∀ t, ‖𝒮(s−α−β)·𝓛(s+β)‖ ≤ Fbound(β + 1/L)`,  `s = c₀ + (t−t₀')i`.

The `t`-dependence — the residual `PretSupply` records — is killed by `hMt` alone: the
floor is uniform in `t` (§0's `center_dist_floor` supplies exactly this from the row's
minimality), so the right-hand side is genuinely `t`-free, which is what
`joint_cs_factoring` demands.

Gates, all discharged from `3 ≤ L`: `e ≤ y` (`y = L⁴ ≥ 81`), `σ := β+1/L ≤ 1`
(`1/L ≤ 1/3`, `β ≤ η = 1/(4 log L) < 1/4`), and the scale condition `e^{1/σ} ≤ k`
(`1/σ ≤ L = log k`). -/
theorem joint_supF_pin {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {t₀' M k L c₀ y η : ℝ}
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L)
    (hMt : ∀ t : ℝ, M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαη : α ≤ η) (hβη : β ≤ η) (t : ℝ) :
    ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFbound M L (β + 1 / L) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 3) hk
  have hL3 : (3 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 3]; exact Real.log_le_log (Real.exp_pos 3) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hLinv3 : 1 / L ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hL0 (by norm_num : (0 : ℝ) < 3)]; linarith
  have hσ0 : (0 : ℝ) < β + 1 / L := by linarith
  -- the `y`-gates
  have hy0 : (0 : ℝ) < y := by rw [hy]; positivity
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hylo : Real.exp 1 ≤ y := by
    rw [hy]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL3 4]
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have h3 : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) hL3
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    linarith
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  have hη4 : η ≤ 1 / 4 := by
    rw [hη, hlogy]
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
    linarith
  -- the twisted datum is 1-bounded at primes
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  -- the scale condition `e^{1/σ} ≤ k` on `σ ≥ 1/L`
  have hσL : 1 / (β + 1 / L) ≤ L := by
    rw [div_le_iff₀ hσ0]
    have h1 : L * (1 / L) = 1 := by field_simp
    nlinarith
  have hYX : Real.exp (1 / (c₀ - 1 + β)) ≤ k := by
    rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring]
    calc Real.exp (1 / (β + 1 / L)) ≤ Real.exp L := Real.exp_le_exp.mpr hσL
      _ = k := by rw [hL, Real.exp_log hk0]
  have hP := supF_pret_pointwise (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) (y := y)
    hgtw (c := 1 / (2 * Real.exp 1)) (t₀ := t₀') (t := t) (X := k) (c₀ := c₀)
    (α := α) (β := β) (by positivity)
    (by
      rw [div_le_div_iff₀ (by positivity) (Real.exp_pos 1)]
      nlinarith [Real.exp_pos 1])
    hylo (by rw [hc₀eq]; linarith) hα0 hβ0
    (by rw [← hη]; exact hαη) (by rw [← hη]; exact hβη)
    (by rw [hc₀eq]; linarith) hYX
  rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring, ← hL] at hP
  refine hP.trans ?_
  unfold rhsFbound rhsCSF
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
  · have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (hMt t) hc0.le]
  · have : (0 : ℝ) ≤ 1 / (β + 1 / L) := by positivity
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) this

/-! ## §2 — the SHARP `crossKer` page: `crossKer ≤ Kα·(1/σ)` at the `arsinh` face

`BridgeAdapt.crossKer_sigma_bound` is built on the CRUDE (Lorentzian) kernel face
(`kernel_L1_mass`, the `2(X+h)/h·π/a` amplitude ⇒ the `√L` excess at the pin).  The
`Tsplit`-SHARP face (`crossKer_le_amp_sharp` ∘ `kernel_L1_mass_sharp`) replaces `√L` by
`log L`; the composition with `window_bridge` is re-run here against that face, since the
grade page needs the sharp amplitude (the `4·arsinh` bracket) rather than `2(X+h)/h`. -/

/-- The `X^β` cancellation at the SHARP amplitude (`(X+h)^a`, no `+1`):
`(X+h)^{c₀−α−β}·X^β ≤ (X+h)^{c₀}·(X+h)^{−α}`.  The `BridgeAdapt.amp_beta_cancel` page with
the exponent shifted by one (the sharp face carries its `(X+h)` inside the bracket). -/
private lemma amp_beta_cancel_sharp {X h c₀ α β : ℝ} (hX : 1 ≤ X) (hh : 0 < h)
    (hβ0 : 0 ≤ β) :
    (X + h) ^ (c₀ - α - β) * X ^ β ≤ (X + h) ^ c₀ * (X + h) ^ (-α) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hsplit : (X + h) ^ (c₀ - α - β)
      = (X + h) ^ c₀ * (X + h) ^ (-α) * (X + h) ^ (-β) := by
    rw [← Real.rpow_add hXh0, ← Real.rpow_add hXh0]
    congr 1
  have hXβ : X ^ β ≤ (X + h) ^ β := Real.rpow_le_rpow hX0.le (by linarith) hβ0
  have hneg0 : (0 : ℝ) < (X + h) ^ (-β) := Real.rpow_pos_of_pos hXh0 _
  have hcancel : (X + h) ^ (-β) * X ^ β ≤ 1 := by
    have hkey : (X + h) ^ (-β) * (X + h) ^ β = 1 := by
      rw [← Real.rpow_add hXh0]; simp
    calc (X + h) ^ (-β) * X ^ β ≤ (X + h) ^ (-β) * (X + h) ^ β :=
          mul_le_mul_of_nonneg_left hXβ hneg0.le
      _ = 1 := hkey
  have hbase0 : (0 : ℝ) ≤ (X + h) ^ c₀ * (X + h) ^ (-α) :=
    mul_nonneg (Real.rpow_nonneg hXh0.le _) (Real.rpow_nonneg hXh0.le _)
  calc (X + h) ^ (c₀ - α - β) * X ^ β
      = ((X + h) ^ c₀ * (X + h) ^ (-α)) * ((X + h) ^ (-β) * X ^ β) := by rw [hsplit]; ring
    _ ≤ ((X + h) ^ c₀ * (X + h) ^ (-α)) * 1 := mul_le_mul_of_nonneg_left hcancel hbase0
    _ = (X + h) ^ c₀ * (X + h) ^ (-α) := by ring

/-- **R2 — the SHARP per-`(α,β)` `1/σ` bound (`crossKer_sharp_sigma_bound`).**  The
`crossKer_sigma_bound` page re-run at the `Tsplit`-sharp kernel face: for any split height
`T > 0`, at the pinned home (`c₀ = 1+1/L`, `L = log X`, `σ = β+1/L`),

  `crossKer α β ≤ Kα·(1/σ)`,
  `Kα := 9e(log 4+4)²·L·(X+h)^{c₀}·(4·arsinh(2T) + 4(X+h)/(hT))·(X+h)^{−α}`.

Four absorptions, each exact: `arsinh(T/a) ≤ arsinh(2T)` (from `a = c₀−α−β ≥ 1/2`, `arsinh`
monotone), `amp_beta_cancel_sharp` (the `X^β` cancellation), `y^{−2β} ≤ 1`, and
`min(L,1/σ)² ≤ L·(1/σ)` (the second `min` factor spent on the `L` the σ-cutoff returns —
this is the `L` the grade page cannot recover; see §5). -/
theorem crossKer_sharp_sigma_bound (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X h y c₀ L t₀ α β σ T : ℝ}
    (hL : L = Real.log X) (hL3 : 3 ≤ L) (hy : 1 ≤ y) (hyX : y ≤ X)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h) (hT : 0 < T)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαβ : α + β ≤ 1 / 2) (hσ : σ = β + 1 / L) :
    crossKer g X h y c₀ t₀ α β
      ≤ (9 * Real.exp 1 * (Real.log 4 + 4) ^ 2 * L * (X + h) ^ c₀
          * (4 * Real.arsinh (2 * T) + 4 * (X + h) / (h * T)) * (X + h) ^ (-α)) * (1 / σ) := by
  have hX : (1 : ℝ) ≤ X := le_trans hy hyX
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hc : (0 : ℝ) < c₀ - α - β := by rw [hc₀]; linarith
  have hchalf : (1 : ℝ) / 2 ≤ c₀ - α - β := by rw [hc₀]; linarith
  have hσ0 : (0 : ℝ) < σ := by rw [hσ]; linarith
  -- the two landed legs, BEFORE the abbreviations (so the `set`s fold them)
  have hamp := crossKer_le_amp_sharp (g := g) (y := y) (t₀ := t₀) (T := T) hX hh hc hT
  have hwin := window_bridge g hg hL hL3 hy hyX hc₀ hβ0 (by linarith) hσ
  set A : ℝ := 9 * Real.exp 1 * (Real.log 4 + 4) ^ 2 with hA
  have hA0 : (0 : ℝ) ≤ A := by
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hA]; positivity
  set Ba : ℝ := 4 * Real.arsinh (T / (c₀ - α - β)) + 4 * (X + h) / (h * T) with hBa
  set P : ℝ := (X + h) ^ (c₀ - α - β) with hP
  have hP0 : (0 : ℝ) ≤ P := Real.rpow_nonneg hXh0.le _
  set S : ℝ := (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
      ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - β))
    * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
      ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ + β)) with hS
  have hS0 : (0 : ℝ) ≤ S :=
    mul_nonneg (window_mass_nonneg g X y (c₀ - β)) (window_mass_nonneg g X y (c₀ + β))
  -- the sharp bracket, `α,β`-freed by `arsinh` monotonicity
  have harsinh : Real.arsinh (T / (c₀ - α - β)) ≤ Real.arsinh (2 * T) := by
    refine Real.arsinh_le_arsinh.mpr ?_
    rw [div_le_iff₀ hc]
    nlinarith
  have hars0 : (0 : ℝ) ≤ Real.arsinh (T / (c₀ - α - β)) := by
    have h0 : Real.arsinh 0 ≤ Real.arsinh (T / (c₀ - α - β)) :=
      Real.arsinh_le_arsinh.mpr (by positivity)
    rwa [Real.arsinh_zero] at h0
  set B : ℝ := 4 * Real.arsinh (2 * T) + 4 * (X + h) / (h * T) with hB
  have hBa0 : (0 : ℝ) ≤ Ba := by
    have h4 : (0 : ℝ) ≤ 4 * (X + h) / (h * T) := by positivity
    rw [hBa]; linarith
  have hBaB : Ba ≤ B := by rw [hBa, hB]; linarith
  have hB0 : (0 : ℝ) ≤ B := le_trans hBa0 hBaB
  -- the three remaining absorptions
  have hXβ0 : (0 : ℝ) ≤ X ^ β := Real.rpow_nonneg hX0.le _
  have hyβ : y ^ (-(2 * β)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  have hyβ0 : (0 : ℝ) ≤ y ^ (-(2 * β)) := Real.rpow_nonneg hy0.le _
  have hminL : min L (1 / σ) ≤ L := min_le_left _ _
  have hminσ : min L (1 / σ) ≤ 1 / σ := min_le_right _ _
  have hmin0 : (0 : ℝ) ≤ min L (1 / σ) := le_min hL0.le (by positivity)
  have hminsq : min L (1 / σ) ^ 2 ≤ L * (1 / σ) := by
    calc min L (1 / σ) ^ 2 = min L (1 / σ) * min L (1 / σ) := by ring
      _ ≤ L * (1 / σ) := mul_le_mul hminL hminσ hmin0 hL0.le
  have hminsq0 : (0 : ℝ) ≤ min L (1 / σ) ^ 2 := sq_nonneg _
  have hcancel := amp_beta_cancel_sharp (X := X) (h := h) (c₀ := c₀) (α := α) (β := β)
    hX hh hβ0
  have hAB0 : (0 : ℝ) ≤ A * B := mul_nonneg hA0 hB0
  have hRHS0 : (0 : ℝ) ≤ (X + h) ^ c₀ * (X + h) ^ (-α) :=
    mul_nonneg (Real.rpow_nonneg hXh0.le _) (Real.rpow_nonneg hXh0.le _)
  -- STEP 1: the sharp face and the window product
  have hstep1 : crossKer g X h y c₀ t₀ α β
      ≤ (A * (X ^ β * y ^ (-(2 * β))) * min L (1 / σ) ^ 2) * (P * B) := by
    refine le_trans hamp ?_
    refine mul_le_mul hwin (mul_le_mul_of_nonneg_left hBaB hP0)
      (mul_nonneg hP0 hBa0) ?_
    exact mul_nonneg (mul_nonneg hA0 (mul_nonneg hXβ0 hyβ0)) hminsq0
  refine le_trans hstep1 ?_
  -- STEP 2: the regrouping and the three factor bounds
  have e1 : (A * (X ^ β * y ^ (-(2 * β))) * min L (1 / σ) ^ 2) * (P * B)
      = (A * B) * (P * X ^ β) * y ^ (-(2 * β)) * min L (1 / σ) ^ 2 := by rw [hP]; ring
  have e2 : (A * L * (X + h) ^ c₀ * B * (X + h) ^ (-α)) * (1 / σ)
      = (A * B) * ((X + h) ^ c₀ * (X + h) ^ (-α)) * 1 * (L * (1 / σ)) := by ring
  rw [e1, e2]
  have c1 : (A * B) * (P * X ^ β) ≤ (A * B) * ((X + h) ^ c₀ * (X + h) ^ (-α)) := by
    rw [hP]; exact mul_le_mul_of_nonneg_left hcancel hAB0
  have c1nn : (0 : ℝ) ≤ (A * B) * (P * X ^ β) :=
    mul_nonneg hAB0 (mul_nonneg hP0 hXβ0)
  have c2 : (A * B) * (P * X ^ β) * y ^ (-(2 * β))
      ≤ (A * B) * ((X + h) ^ c₀ * (X + h) ^ (-α)) * 1 :=
    mul_le_mul c1 hyβ hyβ0 (mul_nonneg hAB0 hRHS0)
  refine mul_le_mul c2 hminsq hminsq0 ?_
  exact mul_nonneg (mul_nonneg hAB0 hRHS0) zero_le_one

/-! ## §3 — the α-integral of the kernel scale: `∫₀^η (X+h)^{−α} dα ≤ 1/log(X+h)` -/

/-- **R3 — the `α`-decay integral (`alpha_rpow_integral_le`).**  For `a > 1` and `η ≥ 0`,
`∫₀^η a^{−α} dα = (1 − a^{−η})/log a ≤ 1/log a` — GHS's `x^{−α}` α-decay, the factor `1/L`
that pays back one of the two `L`'s the σ-page spends.  FTC on the antiderivative
`α ↦ e^{−α log a}/(−log a)`. -/
theorem alpha_rpow_integral_le {a η : ℝ} (ha : 1 < a) (_hη : 0 ≤ η) :
    (∫ α in (0 : ℝ)..η, a ^ (-α)) ≤ 1 / Real.log a := by
  have ha0 : (0 : ℝ) < a := by linarith
  set c : ℝ := Real.log a with hc
  have hc0 : (0 : ℝ) < c := Real.log_pos ha
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hfun : (fun α : ℝ => a ^ (-α)) = fun α : ℝ => Real.exp (α * (-c)) := by
    funext α
    rw [Real.rpow_def_of_pos ha0, ← hc]
    congr 1
    ring
  have hderiv : ∀ α ∈ Set.uIcc (0 : ℝ) η,
      HasDerivAt (fun α : ℝ => Real.exp (α * (-c)) / (-c)) (Real.exp (α * (-c))) α := by
    intro α _
    have h1 : HasDerivAt (fun α : ℝ => α * (-c)) (-c) α := by
      simpa using (hasDerivAt_id α).mul_const (-c)
    have h3 := h1.exp.div_const (-c)
    rwa [show Real.exp (α * (-c)) * (-c) / (-c) = Real.exp (α * (-c)) from by
      field_simp] at h3
  have hint : IntervalIntegrable (fun α : ℝ => Real.exp (α * (-c))) volume 0 η := by
    apply Continuous.intervalIntegrable
    exact Real.continuous_exp.comp (by fun_prop)
  have hval : (∫ α in (0 : ℝ)..η, Real.exp (α * (-c)))
      = Real.exp (η * (-c)) / (-c) - Real.exp (0 * (-c)) / (-c) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hfun, hval]
  have hpos : (0 : ℝ) < Real.exp (η * (-c)) := Real.exp_pos _
  rw [show Real.exp (0 * (-c)) = 1 from by norm_num, div_sub_div_same, div_neg, ← neg_div,
    neg_sub, div_le_div_iff₀ hc0 hc0]
  nlinarith

/-- Continuity of `α ↦ a^{−α}` at a positive base (the `exp`-presentation). -/
private lemma continuous_rpow_neg {a : ℝ} (ha : 0 < a) :
    Continuous (fun α : ℝ => a ^ (-α)) := by
  have hrw : (fun α : ℝ => a ^ (-α)) = fun α : ℝ => Real.exp (Real.log a * (-α)) := by
    funext α; rw [Real.rpow_def_of_pos ha]
  rw [hrw]
  exact Real.continuous_exp.comp (by fun_prop)

/-! ## §4 — the assembly: the per-`α` β-integral, the α-integral, and the grade -/

/-- The `α`-free kernel amplitude at the sharp face:
`Kamp = 9e(log 4+4)²·L·(k+h)^{c₀}·(4·arsinh(2T) + 4(k+h)/(hT))`, so that §2's exit reads
`crossKer α β ≤ (Kamp·(k+h)^{−α})·(1/σ)`. -/
def rhsKamp (L k h c₀ T : ℝ) : ℝ :=
  9 * Real.exp 1 * (Real.log 4 + 4) ^ 2 * L * (k + h) ^ c₀
    * (4 * Real.arsinh (2 * T) + 4 * (k + h) / (h * T))

/-- The σ-cutoff's return (`joint_sigma_integral`'s RHS at `c = 1/(2e)`):
`C_S·C_F·(e^{48c}/(1−2c))·e^{−cM}·L`.  **The second `L`** — the one the α-integral cannot
pay back; see §5. -/
def rhsSigmaG (M L : ℝ) : ℝ :=
  rhsCSF * ((Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
    * Real.exp (-(1 / (2 * Real.exp 1) * M)) * L)

/-- **THE ASSEMBLED GRADE** `Agrade = (1/π)·C_S·C_F·(e^{48c}/(1−2c))·Kamp`.  At the pin
(`h = k/√L`, `T = L⁴`) this is `≍ C·k·L·log L` — the honest landing, a full `L·log L` above
the ε-cap; see the module docstring §5. -/
def rhsAgrade (L k h c₀ T : ℝ) : ℝ :=
  (1 / Real.pi) * rhsCSF
    * (Real.exp (1 / (2 * Real.exp 1) * 48) / (1 - 2 * (1 / (2 * Real.exp 1))))
    * rhsKamp L k h c₀ T

/-- The pin's elementary arithmetic (`L ≥ 3`, the `y`-gates, `η ≤ 1/4`). -/
private lemma pin_basic {k L y η : ℝ} (hk : Real.exp 3 ≤ k) (hL : L = Real.log k)
    (hy : y = L ^ 4) (hη : η = 1 / Real.log y) :
    0 < k ∧ 3 ≤ L ∧ 1 ≤ y ∧ Real.exp 1 ≤ y ∧ 0 < Real.log y ∧ 0 < η ∧ η ≤ 1 / 4 := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 3) hk
  have hL3 : (3 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 3]; exact Real.log_le_log (Real.exp_pos 3) hk
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have h81 : (81 : ℝ) ≤ y := by
    rw [hy]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL3 4]
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have h3 : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) hL3
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    linarith
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  refine ⟨hk0, hL3, by linarith, by linarith, hlogy0, by rw [hη]; positivity, ?_⟩
  rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
  linarith

/-- Interval-integrability of the σ-integrand `Fbound σ/σ` (continuity on `[1/L, b]`) — the
local re-derivation of `PretSupply`'s private `sigma_core_integrable_pret` at the concrete
`Fbound`.  DISCHARGED, not carried. -/
private lemma rhs_sigma_div_integrable {M L b : ℝ} (hL0 : 0 < L) (hb : 1 / L ≤ b) :
    IntervalIntegrable (fun σ : ℝ => rhsFbound M L σ / σ) volume (1 / L) b := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ σ ∈ Set.uIcc (1 / L) b, (0 : ℝ) < σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact lt_of_lt_of_le hLinv0 hσ.1
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFbound]
  refine ContinuousOn.div (ContinuousOn.mul ?_ ?_) continuousOn_id
    (fun σ hσ => (hpos σ hσ).ne')
  · exact continuousOn_const.mul
      (continuousOn_const.div continuousOn_id (fun σ hσ => (hpos σ hσ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log
      ((continuous_id.mul continuous_const).continuousOn)
      (fun σ hσ => (mul_pos (hpos σ hσ) hL0).ne'))

/-- Interval-integrability of `bridge_adapter`'s translated integrand.  DISCHARGED at the
concrete `Fbound` (the `BridgeAdapt` note: with any concrete `Fbound` this follows). -/
private lemma rhs_shift_integrable {M L η Kα : ℝ} (hL0 : 0 < L) (hη0 : 0 ≤ η) :
    IntervalIntegrable
      (fun β : ℝ => Kα * (rhsFbound M L (β + 1 / L) / (β + 1 / L))) volume 0 η := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ β ∈ Set.uIcc (0 : ℝ) η, (0 : ℝ) < β + 1 / L := by
    intro β hβ
    rw [Set.uIcc_of_le hη0, Set.mem_Icc] at hβ
    linarith [hβ.1]
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFbound]
  refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.mul ?_ ?_) ?_
    (fun β hβ => (hpos β hβ).ne'))
  · exact continuousOn_const.mul
      (continuousOn_const.div (by fun_prop) (fun β hβ => (hpos β hβ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log (by fun_prop)
      (fun β hβ => (mul_pos (hpos β hβ) hL0).ne'))
  · fun_prop

/-- **R4 — the per-`α` β-integral (`beta_integral_pin`).**  `bridge_adapter` ∘
`joint_sigma_integral` at the pin: for `α ∈ [0,η]`,

  `∫₀^η Fbound(β+1/L)·crossKer α β dβ ≤ (Kamp·(k+h)^{−α})·(C_S·C_F·(e^{48c}/(1−2c))·e^{−cM}·L)`.

The FLAT exit (no `(1+M)`): `joint_sigma_integral`, not `sigma_wiring`.  `hFdom` and the
σ-cutoff's `hFb` are `le_rfl` — the concrete `Fbound` IS the majorant
`supF_pret_majorant_sigma` produces.  The ONE carried socket is `hIβ`. -/
theorem beta_integral_pin (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀' M k L c₀ y η h T α : ℝ}
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h) (hT : 0 < T) (hyk : y ≤ k) (hM0 : 0 ≤ M)
    (hLη : 1 / L ≤ η) (hα0 : 0 ≤ α) (hαη : α ≤ η)
    (hIβ : IntervalIntegrable (fun β => rhsFbound M L (β + 1 / L)
        * crossKer g k h y c₀ t₀' α β) volume 0 η) :
    (∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L) * crossKer g k h y c₀ t₀' α β)
      ≤ (rhsKamp L k h c₀ T * (k + h) ^ (-α)) * rhsSigmaG M L := by
  obtain ⟨hk0, hL3, hy1, _hye, _hlogy0, hη0, hη4⟩ := pin_basic hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hK0 : (0 : ℝ) ≤ rhsKamp L k h c₀ T * (k + h) ^ (-α) := by
    have hars : (0 : ℝ) ≤ Real.arsinh (2 * T) := by
      have h0 : Real.arsinh 0 ≤ Real.arsinh (2 * T) :=
        Real.arsinh_le_arsinh.mpr (by positivity)
      rwa [Real.arsinh_zero] at h0
    have hbr : (0 : ℝ) ≤ 4 * Real.arsinh (2 * T) + 4 * (k + h) / (h * T) := by
      have : (0 : ℝ) ≤ 4 * (k + h) / (h * T) := by positivity
      linarith
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hpow : (0 : ℝ) < (k + h) ^ c₀ := Real.rpow_pos_of_pos hkh0 _
    have hamp : (0 : ℝ) ≤ rhsKamp L k h c₀ T := by
      unfold rhsKamp
      have : (0 : ℝ) ≤ 9 * Real.exp 1 * (Real.log 4 + 4) ^ 2 * L * (k + h) ^ c₀ := by
        positivity
      exact mul_nonneg this hbr
    exact mul_nonneg hamp (Real.rpow_nonneg hkh0.le _)
  -- the pointwise `crossKer` bound (§2) on the β-range
  have hcross : ∀ β ∈ Icc (0 : ℝ) η,
      crossKer g k h y c₀ t₀' α β
        ≤ (rhsKamp L k h c₀ T * (k + h) ^ (-α)) * (1 / (β + 1 / L)) := by
    intro β hβ
    exact crossKer_sharp_sigma_bound g hg hL hL3 hy1 hyk hc₀ hh hT hα0 hβ.1
      (by linarith [hβ.2]) rfl
  have hsup0 : ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ rhsFbound M L (β + 1 / L) := by
    intro β hβ
    exact rhsFbound_nonneg M L (by linarith [hβ.1])
  have hFnn : ∀ σ ∈ Icc (1 / L) (2 * η), 0 ≤ rhsFbound M L σ := by
    intro σ hσ
    exact rhsFbound_nonneg M L (lt_of_lt_of_le hLinv0 hσ.1)
  have hIσ := rhs_sigma_div_integrable (M := M) (L := L) (b := 2 * η) hL0 (by linarith)
  have hBA := bridge_adapter (g := g) (X := k) (h := h) (y := y) (c₀ := c₀) (t₀ := t₀')
    (L := L) (η := η) (Kα := rhsKamp L k h c₀ T * (k + h) ^ (-α)) (α := α)
    (supF := fun _ β => rhsFbound M L (β + 1 / L)) (Fbound := rhsFbound M L)
    hL0 hLη hK0 hsup0 hcross (fun β _ => le_rfl) hFnn hIβ
    (rhs_shift_integrable hL0 hη0.le) hIσ
  refine le_trans hBA ?_
  refine mul_le_mul_of_nonneg_left ?_ hK0
  -- the σ-cutoff, FLAT
  have hlogk3 : (3 : ℝ) ≤ Real.log k := by rw [← hL]; exact hL3
  rw [hL]
  exact joint_sigma_integral (Fbound := rhsFbound M (Real.log k))
    (c := 1 / (2 * Real.exp 1)) (X := k) (b := 2 * η) (M := M) (CSF := rhsCSF)
    (by positivity)
    (by
      rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring,
        div_lt_one (Real.exp_pos 1)]
      linarith [Real.exp_one_gt_d9])
    hlogk3 hM0 rhsCSF_pos.le (by rw [← hL]; linarith) (by rw [← hL]; exact hIσ)
    (fun σ _ => le_rfl)

/-- **R5 — THE GRADE AT SCALE `k` (`rhs_grade_at_scale`).**  `joint_cs_factoring` ∘ (R4 per
`α`) ∘ the α-integral: for the twisted datum `g' = (q ↦ g q·q^{−it₀'})` at the pin,

  `‖prop21RHS g' t₀' k h c₀ y η‖ ≤ Agrade·e^{−(1/(2e))·M}`,
  `Agrade = (1/π)·C_S·C_F·(e^{48c}/(1−2c))·Kamp`,
  `Kamp = 9e(log 4+4)²·L·(k+h)^{c₀}·(4·arsinh(2T) + 4(k+h)/(hT))`.

`M` is FREE (the M-shape): any floor for the joint head's distance at every frequency, which
§0's `center_dist_floor` supplies from the row's minimality.  The `α`-integral contributes
the `1/L` (`alpha_rpow_integral_le`) that cancels ONE of the σ-page's two `L`'s; the other
stays in `Kamp` — the honest deficit (§5 of the module docstring).

Four integrability sockets are carried (the house conditional-assembly form, exactly
`joint_cs_factoring`'s own); everything else is discharged. -/
theorem rhs_grade_at_scale (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀' M k L c₀ y η h T : ℝ}
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h) (hT : 0 < T) (hyk : y ≤ k) (hM0 : 0 ≤ M)
    (hLη : 1 / L ≤ η)
    (hMt : ∀ t : ℝ, M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    (hIβ : ∀ α ∈ Icc (0 : ℝ) η, IntervalIntegrable (fun β => rhsFbound M L (β + 1 / L)
        * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β) volume 0 η)
    (hIβ' : ∀ α ∈ Icc (0 : ℝ) η, IntervalIntegrable
        (fun β => ‖(1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand
          (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y α β t‖) volume 0 η)
    (hIα : IntervalIntegrable (fun α => ∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L)
        * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β) volume 0 η)
    (hIα' : IntervalIntegrable (fun α => ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
        ∫ t, jointIntegrand (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y α β t‖)
        volume 0 η) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' k h c₀ y η‖
      ≤ rhsAgrade L k h c₀ T * Real.exp (-(1 / (2 * Real.exp 1)) * M) := by
  obtain ⟨hk0, hL3, hy1, _hye, _hlogy0, hη0, hη4⟩ := pin_basic hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hk1 : (1 : ℝ) ≤ k := le_trans (Real.one_le_exp (by norm_num)) hk
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  -- the amplitude is nonnegative
  have hars : (0 : ℝ) ≤ Real.arsinh (2 * T) := by
    have h0 : Real.arsinh 0 ≤ Real.arsinh (2 * T) := Real.arsinh_le_arsinh.mpr (by positivity)
    rwa [Real.arsinh_zero] at h0
  have hKamp0 : (0 : ℝ) ≤ rhsKamp L k h c₀ T := by
    have hbr : (0 : ℝ) ≤ 4 * Real.arsinh (2 * T) + 4 * (k + h) / (h * T) := by
      have h4 : (0 : ℝ) ≤ 4 * (k + h) / (h * T) := by positivity
      linarith
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    unfold rhsKamp
    have hfront : (0 : ℝ) ≤ 9 * Real.exp 1 * (Real.log 4 + 4) ^ 2 * L * (k + h) ^ c₀ := by
      positivity
    exact mul_nonneg hfront hbr
  have hG0 : (0 : ℝ) ≤ rhsSigmaG M L := by
    unfold rhsSigmaG
    have hE : (0 : ℝ) ≤ Real.exp (1 / (2 * Real.exp 1) * 48)
        / (1 - 2 * (1 / (2 * Real.exp 1))) := by
      have hd : (0 : ℝ) < 1 - 2 * (1 / (2 * Real.exp 1)) := by
        rw [show 2 * (1 / (2 * Real.exp 1)) = 1 / Real.exp 1 from by ring]
        have h1 : 1 / Real.exp 1 < 1 := by
          rw [div_lt_one (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
        linarith
      positivity
    exact mul_nonneg rhsCSF_pos.le (by positivity)
  -- J1 — the CS factoring with the `t`-uniform `supF`
  have hJ1 := joint_cs_factoring (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
    (t₀ := t₀') (X := k) (h := h) (c₀ := c₀) (y := y) (η := η)
    (supF := fun _ β => rhsFbound M L (β + 1 / L))
    hk1 hh hη0.le (by rw [hc₀]; linarith)
    (fun _ _ β hβ => rhsFbound_nonneg M L (by linarith [hβ.1]))
    (fun α hα β hβ t => joint_supF_pin hg hk hL hy hη hc₀ hMt hα.1 hβ.1 hα.2 hβ.2 t)
    hIβ hIβ' hIα hIα'
  refine hJ1.trans ?_
  -- the per-`α` β-integral
  have hper : ∀ α ∈ Icc (0 : ℝ) η,
      (∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        ≤ (rhsKamp L k h c₀ T * (k + h) ^ (-α)) * rhsSigmaG M L :=
    fun α hα => beta_integral_pin _ hgtw hk hL hy hη hc₀ hh hT hyk hM0 hLη hα.1 hα.2
      (hIβ α hα)
  -- the α-integral: the `1/L` that pays back ONE of the two `L`'s
  have hKcont : Continuous
      (fun α : ℝ => (rhsKamp L k h c₀ T * (k + h) ^ (-α)) * rhsSigmaG M L) :=
    ((continuous_rpow_neg hkh0).const_mul _).mul continuous_const
  have hmono := intervalIntegral.integral_mono_on hη0.le hIα
    (hKcont.intervalIntegrable 0 η) hper
  have hfe : ∀ α : ℝ, (rhsKamp L k h c₀ T * (k + h) ^ (-α)) * rhsSigmaG M L
      = (rhsKamp L k h c₀ T * rhsSigmaG M L) * ((k + h) ^ (-α)) := fun α => by ring
  have hpull : (∫ α in (0 : ℝ)..η, (rhsKamp L k h c₀ T * (k + h) ^ (-α)) * rhsSigmaG M L)
      = (rhsKamp L k h c₀ T * rhsSigmaG M L) * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := by
    simp only [hfe]
    exact intervalIntegral.integral_const_mul _ _
  have hint_le : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / L := by
    have h1 : (∫ α in (0 : ℝ)..η, (k + h) ^ (-α)) ≤ 1 / Real.log (k + h) :=
      alpha_rpow_integral_le (by linarith) hη0.le
    have h2 : L ≤ Real.log (k + h) := by
      rw [hL]; exact Real.log_le_log hk0 (by linarith)
    have h3 : (0 : ℝ) < Real.log (k + h) := by linarith
    have h4 : 1 / Real.log (k + h) ≤ 1 / L := by
      rw [div_le_div_iff₀ h3 hL0]; linarith
    linarith
  have hstep : (1 / Real.pi) * ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η,
        rhsFbound M L (β + 1 / L)
          * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β
      ≤ (1 / Real.pi) * ((rhsKamp L k h c₀ T * rhsSigmaG M L) * (1 / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, rhsFbound M L (β + 1 / L)
              * crossKer (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) k h y c₀ t₀' α β)
        ≤ ∫ α in (0 : ℝ)..η, (rhsKamp L k h c₀ T * (k + h) ^ (-α)) * rhsSigmaG M L := hmono
      _ = (rhsKamp L k h c₀ T * rhsSigmaG M L) * ∫ α in (0 : ℝ)..η, (k + h) ^ (-α) := hpull
      _ ≤ (rhsKamp L k h c₀ T * rhsSigmaG M L) * (1 / L) :=
          mul_le_mul_of_nonneg_left hint_le (mul_nonneg hKamp0 hG0)
  refine hstep.trans (le_of_eq ?_)
  -- the grade algebra: the σ-page's `L` against the α-integral's `1/L`
  have hexpeq : Real.exp (-(1 / (2 * Real.exp 1) * M))
      = Real.exp (-(1 / (2 * Real.exp 1)) * M) := by rw [neg_mul]
  have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold rhsAgrade rhsSigmaG
  rw [← hexpeq]
  field_simp

/-! ## §5 — the exit: the `hRHS` binder shape, and the capstone -/

/-- **The four integrability sockets of the joint route at one scale** — bundled.  These are
`joint_cs_factoring`'s OWN hypotheses (the house conditional-assembly form): the `β`- and
`α`-level interval-integrability of `supF·crossKer` and of the `prop21RHS` integrand.  They
are plumbing over `crossKer`'s `β`-continuity (a dominated-convergence page of its own);
nothing in this file weakens them. -/
def JointIntegrableAt (d : ℕ → ℂ) (t₀' M k L c₀ y η h : ℝ) : Prop :=
  (∀ α ∈ Icc (0 : ℝ) η, IntervalIntegrable
      (fun β => rhsFbound M L (β + 1 / L) * crossKer d k h y c₀ t₀' α β) volume 0 η)
  ∧ (∀ α ∈ Icc (0 : ℝ) η, IntervalIntegrable
      (fun β => ‖(1 / (2 * Real.pi) : ℝ) • ∫ t, jointIntegrand d t₀' k h c₀ y α β t‖)
      volume 0 η)
  ∧ IntervalIntegrable (fun α => ∫ β in (0 : ℝ)..η,
      rhsFbound M L (β + 1 / L) * crossKer d k h y c₀ t₀' α β) volume 0 η
  ∧ IntervalIntegrable (fun α => ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
      ∫ t, jointIntegrand d t₀' k h c₀ y α β t‖) volume 0 η

/-- `4·log L ≤ L` for `L ≥ 64` (`log √L ≤ √L − 1`, then `8√L ≤ L`).  The single
threshold arithmetic behind BOTH remaining pin gates: `1/L ≤ η = 1/(4 log L)` and
`(log k)⁴ ≤ k`. -/
private lemma four_log_le_self {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  nlinarith

/-- **THE EXIT (`hRHS_discharged`).**  `center_halasz_supply`'s `hRHS` binder at one scale
`k`, in its EXACT shape, from the joint-head chain: `§0`'s minimality floor + R5's grade,
against the grade socket `Agrade ≤ C₁·k`.

The single scale gate is `e^{64} ≤ k` (it discharges BOTH remaining pin gates through
`four_log_le_self`: `1/L ≤ η` and `(log k)⁴ ≤ k`); the distance floor comes from the row's
minimality `hmin` at the centre; the four integrability sockets and the grade socket are
carried.  **The grade socket is the honest frontier**: R5 exhibits `Agrade ≍ C·k·L·log L`,
so `hgrade` holds only for `C₁ ≳ L·log L` — a full `L·log L` above the ε-cap.  See the
module docstring §5; per iron rule 1 nothing here forces it. -/
theorem hRHS_discharged {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {t₀ t₁ X C₁ : ℝ} {k : ℕ}
    (hk64 : Real.exp 64 ≤ (k : ℝ)) (hXk : ⌊X⌋₊ ≤ k)
    (hmin : ∀ v : ℝ, pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hInt : JointIntegrableAt (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      (k : ℝ) (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
      (1 / Real.log (Real.log (k : ℝ) ^ 4)) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
    (hgrade : rhsAgrade (Real.log (k : ℝ)) (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
        (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4) ≤ C₁ * (k : ℝ)) :
    ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
        (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
        (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
      ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
  obtain ⟨hIβ, hIβ', hIα, hIα'⟩ := hInt
  set L : ℝ := Real.log (k : ℝ) with hLdef
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk64
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk64
  have hL0 : (0 : ℝ) < L := by linarith
  have h4log := four_log_le_self hL64
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have h3 : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) (by linarith)
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hlogy : Real.log (L ^ 4) = 4 * Real.log L := by rw [Real.log_pow]; norm_num
  -- gate 1: `1/L ≤ η`
  have hLη : 1 / L ≤ 1 / Real.log (L ^ 4) := by
    rw [hlogy, div_le_div_iff₀ hL0 (by linarith)]
    linarith
  -- gate 2: `(log k)⁴ ≤ k`
  have hyk : L ^ 4 ≤ (k : ℝ) := by
    have h1 : Real.log (L ^ 4) ≤ Real.log (k : ℝ) := by rw [hlogy, ← hLdef]; linarith
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity), Real.exp_log hk0] at h2
  -- the distance floor from the row's minimality
  have hM0 : (0 : ℝ) ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X :=
    pretDistSq_nonneg _ _ _
      (fun n => norm_seamCoeff_le (fun m => ellLin_norm_le_one g hg m) (fun _ => by simp) t₀ n)
      (fun n => le_of_eq (costwist_norm t₁ n))
  have hMt := center_dist_floor hg (z := (k : ℝ))
    (by rw [Nat.floor_natCast]; exact hXk) hmin
  have hsq0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  refine le_trans (rhs_grade_at_scale g hg (t₀' := t₀ + t₁) (T := L ^ 4)
    (by linarith [Real.exp_le_exp.mpr (by norm_num : (3 : ℝ) ≤ 64)]) hLdef rfl rfl rfl
    (by positivity) (by positivity) hyk hM0 hLη hMt hIβ hIβ' hIα hIα') ?_
  exact mul_le_mul_of_nonneg_right hgrade (Real.exp_nonneg _)

/-- **THE CAPSTONE (`center_halasz_of_grade`).**  `center_halasz_supply` ∘ `hRHS_discharged`:
the `HCENTER` centre bound with its `hRHS` socket REPLACED by the joint-head chain's own
residuals — the row's minimality `hmin` (the ⟦TWO-M⟧ semantics, honestly carried), the four
integrability sockets, and the grade socket.

  `‖∑_{n≤k} seamCoeff (ellLin g) 1 t₀ n · e^{−it₁ log n}‖
     ≤ (C₁·e^{−(1/(2e))·𝔻²(f, p^{it₁}; X)} + 4·(log X)^{−1/2+1/1000})·k`.

**What this is and is not.**  It IS the `hRHS` socket dissolved into the joint chain: the
`t`-sup, the twist-slot reconciliation, the scale bridge, the σ-cutoff and the α-integral are
all machine-checked here.  It is NOT the ε-cap grade: `rhs_grade_at_scale` exhibits the
concrete `Agrade ≍ C·k·log k·log log k`, so `hgrade` is satisfiable only at
`C₁ ≍ (log X)^{1+o(1)}` — above the `(log X)^{1/1000}` the ball leg needs.  The gap is the
kernel's standalone `L¹` mass times the window-mass `L` (module docstring §5), and it closes
only through the mixed-line Plancherel bridge.  **LIVE GUARD**: `c = 1/(2e)` is the BALL
arm's halved constant; a §8.3 consumer citing this head is a STOP. -/
theorem center_halasz_of_grade {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (C₁ : ℝ), X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ C₁ →
        (∀ v : ℝ, pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
            ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          JointIntegrableAt (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
            (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
            (k : ℝ) (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
            (1 / Real.log (Real.log (k : ℝ) ^ 4))
            ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          rhsAgrade (Real.log (k : ℝ)) (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
              (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4) ≤ C₁ * (k : ℝ)) →
      ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
              + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨X₁, hX₁0, hsupply⟩ := center_halasz_supply hg t₀ t₁
  refine ⟨max X₁ (Real.exp 64 + 1), lt_of_lt_of_le hX₁0 (le_max_left _ _), ?_⟩
  intro X N C₁ hXlb hXN hN2 hC₁0 hmin hInt hgrade
  refine hsupply X N C₁ (le_trans (le_max_left _ _) hXlb) hXN hN2 hC₁0 ?_
  intro k hkfl hkN
  have hXexp : Real.exp 64 + 1 ≤ X := le_trans (le_max_right _ _) hXlb
  have hfl : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hk64 : Real.exp 64 ≤ (k : ℝ) := by
    have h : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkfl
    linarith
  exact hRHS_discharged hg hk64 hkfl hmin (hInt k hkfl hkN) (hgrade k hkfl hkN)

end Salt.MR

