/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.PortAssembly
import Salt.MR.ZetaInvShallow
import Salt.MR.HalaszIntegersChiClose

/-!
# WAVE CLOSE — the two ruled exposures, fired

Wave P-7 stopped with two one-line statement changes owed, both ruled by the maestro at
`b9d1979`.  This file makes the compositions they unlock.  Nothing here is a new estimate:
every line is a composition of landed theorems.

## ⟦R-1⟧ the rate chain's `hxi`, restated at the WIDTH — and DISCHARGED

`PortAssembly.lean` §7 adjudicated the shape: the STRONG carve-out (`Re ρ < 1/2` at every real
zero of `L(·,χ)`) is a GRH fragment and is not Siegel-foldable, while the WIDTH form is.  The
restatement happened in the landed files (`MobiusChiRateClose.XiCarveWidth`,
`mmuChiRate_nonprincipal` and the four wrappers, `ZetaInvShallow.mmuChiRate_of_carve` /
`lambdaChiSummatory_of_carve`); `xiCarveWidth_of_half` records that nothing was lost.

`xiCarveWidth_of_siegel` below then DISCHARGES the restated hypothesis outright, so:

**`mmuChiRate_holds_gated : MmuChiRate` and `lambdaChiSummatory_holds_gated` carry NO
analytic hypothesis: the former has literally zero binders; the latter only the
Prop-family parameter `(A : ℝ) (hA : 0 < A)` — the saving it is stated at.**  The port's centerpiece — the `χ`-twisted, `t`-uniform Möbius rate — is
in the kernel.  ⟦THE ADJUDICATION the brief asked for⟧ the Siegel gate did NOT have to ride as
a hypothesis: it folds into the `∃ x₀` that `MmuChiRate` already carries.  The arithmetic:
Siegel's `∃ K` is INEFFECTIVE, so the threshold `H₀ = max(exp(exp 100)+3, exp(exp(1/K)))` is
ineffective too — and an ineffective threshold inside an `∃ x₀` is exactly what an ineffective
constant is allowed to be.  What is NOT ineffective is the bound's shape: `C` and the decay
`(log y)^{−A}` are effective, uniform in `q ≤ (log y)^{12}`, `|t| ≤ y`, `χ`.

The gate's exponent arithmetic, once more, because it is the whole content: at
`q ≤ (log H)^{12}`, `q^{1/16} ≤ (log H)^{3/4}` — which is EXACTLY `vkShallowWidth`'s leading
denominator factor — so the product `q^{1/16}·vkShallowWidth(10⁻⁶) q H` collapses to
`10⁻⁶/((log q+1)(loglog H)³)`, and only `(loglog H)³ ≥ 10⁻⁶/K` is asked of `H`.  `16 = 12/(3/4)`.

## ⟦R-2⟧ `c_vk = 1/10⁸`, exposed — and §9's socket fired

`twisted_edge_price_strip` is literally `⟨1/10^8, …⟩` and `twisted_window_price_gated_holds`
passes the same constant through, but both packaged it behind `∃ c_vk`, so the kernel could not
see that it matches the region's own literal `1/10⁸`.  Both `∃`s now expose it (the strip by an
added `c_vk = 1/10^8` conjunct, the price by being stated AT the literal), which lets
`halasz_primes_chi_pair_of_gates` fire with its price hypothesis discharged:
`halaszPrimesChi_holds_gated` is `USetChi.HalaszPrimesChi`'s conclusion behind FOUR `q`-vs-`T`
gates PLUS the uniform height floor `T₀ ≤ T` (⟦PORT-AUDIT correction, 2026-07-30⟧: the
honest count is four `q`-dependent gates + one uniform floor — §3's docstring had it
right; this headline undercounted), and nothing else.

⟦THE EXPOSURE WAS TWO CONJUNCTS, NOT ONE — reported as a deviation⟧
`twisted_window_price_gated_holds` also had to expose `exp(exp 100) ≤ T₀` in place of
`3 ≤ T₀`: §9 demands the former and the proof already produced it (`T₀ := T₀e`, the edge's own
floor), so this is the same genre of exposure — a value the proof has, hidden by a weaker `∃`
body.
-/

namespace Salt.MR

open scoped BigOperators
open Complex DirichletCharacter

/-! ## §1 — ⟦R-1⟧ the width-form carve-out, discharged by the Siegel fold -/

/-- **⟦R-1⟧ THE ξ₁ CARVE-OUT, DISCHARGED.**  `siegel_real_carve` (PortAssembly §7, the port's
ONE ineffective constant) delivers the WIDTH form `XiCarveWidth H₀` at the ineffective
threshold `H₀ = max(exp(exp 100)+3, exp(exp(1/K)))`.

The gate `q^{1/16}·W ≤ K` at `W = vkShallowWidth (10⁻⁶) q H`: the modulus gate
`q ≤ (log H)^{12}` gives `q^{1/16} ≤ (log H)^{3/4}`, which cancels the width's `(log H)^{3/4}`
outright, leaving `10⁻⁶/((log q+1)(loglog H)³) ≤ K` — and `loglog H ≥ 1/K` closes it with the
`(log q+1)` and two powers of `loglog H` unspent. -/
theorem xiCarveWidth_of_siegel :
    ∃ H₀ : ℝ, Real.exp (Real.exp 100) + 3 ≤ H₀ ∧ XiCarveWidth H₀ := by
  obtain ⟨K, hK0, hsg⟩ := siegel_real_carve
  refine ⟨max (Real.exp (Real.exp 100) + 3) (Real.exp (Real.exp (1 / K))),
    le_max_left _ _, ?_⟩
  intro q hq χ hχ1 H hH hqH ρ hρ0 hρim
  have hχinv1 : χ⁻¹ ≠ 1 := fun h => hχ1 (by rw [← inv_inv χ, h, inv_one])
  have hH1 : Real.exp (Real.exp 100) + 3 ≤ H := le_trans (le_max_left _ _) hH
  have hH2 : Real.exp (Real.exp (1 / K)) ≤ H := le_trans (le_max_right _ _) hH
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hHpos : (0 : ℝ) < H := by linarith
  have hlogH100 : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log hEpos (by linarith)
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hll100 : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hlogH100
  have hllK : 1 / K ≤ Real.log (Real.log H) := by
    have h1 : Real.exp (1 / K) ≤ Real.log H := by
      rw [← Real.log_exp (Real.exp (1 / K))]
      exact Real.log_le_log (Real.exp_pos _) hH2
    have h2 := Real.log_le_log (Real.exp_pos (1 / K)) h1
    rwa [Real.log_exp] at h2
  have hW0 : 0 < vkShallowWidth (1 / 10 ^ 6) q H :=
    vkShallowWidth_pos (by norm_num) (by linarith)
  refine hsg q χ⁻¹ hχinv1 _ hW0 ?_ ρ hρ0 hρim
  -- ⟦the Siegel gate⟧ `q^{1/16}·W ≤ K`
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log H) := by linarith
  have hR1 : (1 : ℝ) ≤ Real.log H ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hqR : (q : ℝ) ^ ((1 : ℝ) / 16) ≤ Real.log H ^ ((3 : ℝ) / 4) := by
    have h1 : (q : ℝ) ^ ((1 : ℝ) / 16) ≤ (Real.log H ^ (12 : ℕ)) ^ ((1 : ℝ) / 16) :=
      Real.rpow_le_rpow (by linarith) hqH (by norm_num)
    have h2 : (Real.log H ^ (12 : ℕ)) ^ ((1 : ℝ) / 16) = Real.log H ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_natCast (Real.log H) 12, ← Real.rpow_mul hlogH0.le]
      norm_num
    rwa [h2] at h1
  have hℓ3 : Real.log (Real.log H) ≤ Real.log (Real.log H) ^ (3 : ℕ) := by
    have h := pow_le_pow_right₀ hℓ1 (show 1 ≤ 3 by norm_num)
    simpa using h
  have hKℓ : (1 : ℝ) ≤ K * Real.log (Real.log H) := by
    have h1 : K * (1 / K) ≤ K * Real.log (Real.log H) :=
      mul_le_mul_of_nonneg_left hllK hK0.le
    have h0 : K * (1 / K) = 1 := by field_simp
    linarith [h0 ▸ h1]
  have hKℓ3 : (1 : ℝ) ≤ K * Real.log (Real.log H) ^ (3 : ℕ) := by
    nlinarith [hℓ3, hK0.le, hKℓ]
  have hDpos : (0 : ℝ) < (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
      * Real.log (Real.log H) ^ (3 : ℕ) := by
    have h1 : (0 : ℝ) < Real.log (q : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := by linarith
    have h3 : (0 : ℝ) < Real.log (Real.log H) ^ (3 : ℕ) := by positivity
    positivity
  rw [vkShallowWidth, mul_div_assoc', div_le_iff₀ hDpos]
  have ha0 : (0 : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) :=
    Real.rpow_nonneg (by linarith) _
  calc (q : ℝ) ^ ((1 : ℝ) / 16) * (1 / 10 ^ 6)
      ≤ Real.log H ^ ((3 : ℝ) / 4) := by nlinarith [hqR, ha0]
    _ ≤ (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
          * (K * Real.log (Real.log H) ^ (3 : ℕ)) := by
        have h1 : Real.log H ^ ((3 : ℝ) / 4)
            ≤ (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4) := by
          nlinarith [hR1, hlogq]
        nlinarith [h1, hKℓ3, hR1, hlogq]
    _ = K * ((Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (3 : ℕ)) := by ring

/-- **⟦R-1's DELIVERABLE⟧ — the `χ`-twisted `t`-uniform Möbius rate, UNCONDITIONAL.**

`MmuChiRate`: for every saving `A > 0` there are `C > 0` and a threshold `x₀` with
`‖∑_{n ≤ y} μ(n)χ̄(n)n^{it}‖ ≤ C·y/(log y)^A` for all `y ≥ x₀`, uniformly over
`q ≤ (log y)^{12}`, every `χ mod q`, and `|t| ≤ y`.

The whole chain in one line: §1's Siegel discharge → `mmuChiRate_of_carve` (the width-form
hypothesis) → the landed mirror (contour shift + budget + de-smoothing) at the landed χ-VK
shallow edge bound, with the χ₀ row on the landed ζ twin `zetaInvShallowVk_holds`.  The
threshold `x₀` inherits Siegel's ineffectivity; nothing else does. -/
theorem mmuChiRate_holds_gated : MmuChiRate := by
  obtain ⟨H₀, hH₀, hxi⟩ := xiCarveWidth_of_siegel
  exact mmuChiRate_of_carve hH₀ hxi

/-- **⟦R-1's SECOND DELIVERABLE⟧ — O3's bridge, fired.**  `LambdaChiSummatory A` at the fold's
own gates (`q ≤ (log y)^{11}`, `|t| ≤ ⌊√y⌋`), unconditionally, for every saving `A > 0`. -/
theorem lambdaChiSummatory_holds_gated (A : ℝ) (hA : 0 < A) : LambdaChiSummatory A := by
  obtain ⟨H₀, hH₀, hxi⟩ := xiCarveWidth_of_siegel
  exact lambdaChiSummatory_of_carve hH₀ hxi A hA

/-! ## §2 — ⟦R-2⟧ the pair socket, at the four gates and nothing else -/

/-- **⟦R-2's DELIVERABLE⟧ — THE PORT'S `(χ,t)`-PAIR ROW, UNCONDITIONAL AT FOUR GATES.**

`USetChi.HalaszPrimesChi`'s conclusion — the socket with the diagonal term `P`, **not**
`φ(q)·P` — with the twisted window price DISCHARGED (`twisted_window_price_gated_holds`, now
stated at the literal width `1/10⁸`) and the zero-free region DISCHARGED (A2's carve-free
rectangle).  What is left in front of the conclusion is four `q`-vs-`T` gates:

* **G1** the twisted edge's `q`-scale gate;
* **G2** the region's `A`-absorption at `A := 1 + log(20000(Cq+8104))/100`;
* **G3** the below-floor width comparison (constant `Kq`, effective);
* **G4** the Siegel gate (constant `Ks`, the port's one ineffective constant).

⟦WHY THE GATES CANNOT BE ABSORBED — the law, restated as a fact about quantifier order⟧
`HalaszPrimesChi C c T₀` quantifies `∀ q` AFTER `T₀` is fixed, while every one of G1–G4 asks
`T ≥ T₁(q)` with `T₁` growing in `q`.  So the gated row does not imply the gate-free slot, and
no choice of `T₀` repairs that: the slot's own statement is what would have to move (see the
`𝒰`-ladder note in `docs/blueprints/flags.md`).  Consumers instantiate the socket at ONE
`(q, T)`, where the gates are exactly the freeze's own arithmetic. -/
theorem halaszPrimesChi_holds_gated :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C₁, C₂, C₃, T₀e, hC₁, hC₂, hC₃, hT₀e, hprice⟩ := twisted_window_price_gated_holds
  exact halasz_primes_chi_pair_of_gates hC₁ hC₂ hC₃ hT₀e hprice

/-- **⟦THE SLOT-WAVE DELIVERABLE (1/2)⟧ — `USetChi.HalaszPrimesChi`, DISCHARGED POINTWISE.**

The socket is now stated at a PARAMETER pair `(q, T)` (`USetChi.lean`, the amendment of
2026-07-30: the old `HalaszPrimesChi C c T₀` fixed `T₀` before `∀ q`, which no `q`-dependent
gate can ever meet).  In that shape §2's row discharges it outright, and **the four gates
become exactly the per-`(q,T)` floor the slot no longer carries**:

* `T₀ ≤ T` — the uniform part of the floor, still uniform (`3 ≤ T₀`, and `T₀ ≥ exp(exp 100)`
  inside `halasz_primes_chi_pair_of_gates`'s own `max`);
* **G1** the twisted edge's `q`-scale gate; **G2** the region's `A`-absorption at
  `A := 1 + log(20000(Cq+8104))/100`; **G3** the below-floor width comparison (`Kq`,
  effective); **G4** the Siegel gate (`Ks`, the port's one ineffective constant — it rides as
  the `∃` it already was, and `Ks` is the only ineffective datum in this statement).

Every gate stays in-statement, verbatim, at its literal shape (law #253): nothing here is
absorbed into a constant, and the `(5T+1)` scale of the gates is NOT the `(qT)` scale of the
socket's decay denominator — the two log scales are kept apart on purpose. -/
theorem halaszPrimesChi_pointwise_of_gates :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T : ℝ), T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      HalaszPrimesChi C c q T := by
  obtain ⟨C, c, T₀, Kq, Ks, hC, hc, hT₀, hKq, hKs, hrow⟩ := halaszPrimesChi_holds_gated
  refine ⟨C, c, T₀, Kq, Ks, hC, hc, hT₀, hKq, hKs, ?_⟩
  intro q _ T hT hG1 hG2 hG3 hG4 P hP hPT10 ℰ hws hsub S hS a
  exact hrow q T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a

/-! ## §3 — ⟦A3⟧ THE 𝒰-EXIT COMPOSE: the lifted ladder's two branches, joined

`usetChi_integral_to_branches` (the χ-summed eq-(16) composition) with BOTH branch bounds
substituted:

* the **`𝒯_S` branch** at the re-pinned level `ε_Q = (log X)^{−106}`
  (`usetChi_TS_branch_exit_repinned`) — UNCONDITIONAL: `halaszIntegersChiPhi_holds` discharged
  the integers slot at the `φ(q)`-graded row, and the six extra powers of log on the level
  repay the `φ(q)` debit exactly (`phi_debit_level_repin`);
* the **`𝒯_L` branch** (`tLChi_main_sumsq`) at the SAME level, which is where the pair socket
  is spent — `V⁻¹ ≤ ε_Q` is the re-pinning's own `V = (log X)^{106}`, killed by the
  quasi-power (`θ < 1/8`).

⟦THE SOCKET, POINTWISE⟧ the socket enters as `hslot : HalaszPrimesChi Cs cs q T` — at THIS
compose's own `(q, T)`.  The close wave stated it as `HalaszPrimesChi Cs cs T₀` and reported
the obstruction: that shape fixes `T₀` BEFORE quantifying `∀ q`, while each of §2's four gates
asks `T ≥ T₁(q)` with `T₁` increasing in `q`, so no choice of `T₀` lets the gated row fill the
slot.  The slot-wave amendment restated it pointwise, which is what §4 below then discharges:
`usetChi_window_meansq_gated` carries NO socket hypothesis at all.  This theorem keeps the
socket named so the composition stays readable at one `(q, T)`; the gated form is the
deliverable.

Everything else rides in-statement: the `𝒰`-thinness package (`α, η, ε` and the budget), the
per-`j` block gates (uniform in `j ∈ ramI H P Q`, as the ladder demands), the pointwise
co-factor bound `Rbd` on the `𝒯_L` side (not a `𝒰`-property — the landed rung says so), and
the Lemma-12 error row `E`, which `HybridMoments.lemma12_meansq_all_chi` supplies. -/

set_option maxHeartbeats 800000 in
-- The compose threads two branch exits (each with a dozen in-statement gates) through the
-- χ-summed eq-(16) composition; the unifier needs room for the `ramMain`/`spoly` expressions
-- at twisted data, exactly as `usetChi_integral_to_branches` itself does.
/-- **⟦A3⟧ THE 𝒰-EXIT, COMPOSED.**  The `χ`-summed window mean square of the twisted Dirichlet
polynomial on `A ⊆ [−T,T]` (the consumer's `(Ann ∖ ball) ∩ 𝒰`), from the pair socket, the
landed `φ(q)`-graded integers row, the `𝒰`-thinness and the Lemma-12 error row.

The two branch prices are visible in the bound: `5128·(log X)^{−200}·M·(1+log 2T)·(mass)` on
`𝒯_S` — byte-for-byte MR's `q = 1` grade — and `81·Cs·Rbd²·(H/j)²` on `𝒯_L`, the Lemma-11
mass and the prime-window gain each contributing one factor `H/j`. -/
theorem usetChi_window_meansq_of_socket
    {Cs cs : ℝ} (hCs : 0 < Cs) (hcs : 0 < cs)
    (q : ℕ) [NeZero q] (f : ℕ → ℂ) (hf1 : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ) (hJb1 : 1 ≤ Jb) (hJbJ : Jb ≤ J) (hδ0 : 0 < δ)
    (T V L X : ℝ) (hslot : HalaszPrimesChi Cs cs q T)
    (hT1 : 1 ≤ T) (hqT : 1 < (q : ℝ) * T) (hV : 1 ≤ V)
    (hVinv : V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ))
    (hP3 : 3 ≤ Pseq Jb) (hQT : (Qseq Jb : ℝ) ≤ (q : ℝ) * T)
    (hκ30Q : 30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb))
    (hLL5 : 5 ≤ Real.log (Real.log ((q : ℝ) * T)))
    (α η ε : ℝ) (hVα : Real.log V ≤ α * Real.log (Pseq Jb)) (hα : α ≤ 1 / 4 - η)
    (hη2 : 2 * η ≤ 1) (hTX : T ≤ X) (hX0 : 0 < X) (hdebit : (q : ℝ) ^ (2 * α) ≤ X ^ ε)
    (hL0 : 0 < Real.log X) (hqlog : (q : ℝ) ≤ (Real.log X) ^ 12)
    (hVδ : V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ))
    (hlogT1 : 1 ≤ Real.log ((q : ℝ) * T))
    (hTL : Real.log ((q : ℝ) * T) ≤ L) (hLe : Real.exp 1 ≤ L)
    (hlogV : Real.log V ≤ 100 * Real.log L)
    (H : ℝ) (hH2 : 2 ≤ H) (N Xd P Q M : ℕ) (a b cf : ℕ → ℂ) (hcf1 : ∀ n : ℕ, ‖cf n‖ ≤ 1)
    (hM : ∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 M)
    (hbudget : thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η + ε)
      ≤ (M : ℝ))
    (hHj : ∀ j ∈ ramI H P Q, H ≤ (j : ℝ))
    (hB3 : ∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j)
    (hBT : ∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * T)
    (hκ30 : ∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j))
    (hBT10 : ∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ T ^ 10)
    (hWL : ∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L)
    (hgate : ∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
      ≤ cs * (Real.log (ramQbase H P j)) ^ 2)
    (Rbd : ℝ) (hRbd : 0 ≤ Rbd)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (hUA : ∀ r : DirichletCharacter ℂ q × ℝ, r.2 ∈ A →
      r ∈ UsetChi q f Pseq Qseq δ J)
    (hR : ∀ j ∈ ramI H P Q, ∀ r : DirichletCharacter ℂ q × ℝ, r.2 ∈ A →
      ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd)
    (E : ℝ)
    (herr : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
        ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in A, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ 4 * ((ramI H P Q).card : ℝ)
          * (∑ j ∈ ramI H P Q,
              (5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
                  * (∑ m ∈ Finset.Icc 1 M,
                      ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
                + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
        + 2 * E := by
  refine usetChi_integral_to_branches q H N Xd P Q a b cf T E (by linarith) herr
    A hAm hAsub ((Real.log X) ^ (-106 : ℝ))
    (fun j => 5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
      * (∑ m ∈ Finset.Icc 1 M, ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2))
    (fun j => 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2) ?_ ?_
  · -- ⟦the `𝒯_S` branch⟧ the re-pinned exit, unconditional
    intro j hj ℰ hws hsubA
    exact usetChi_TS_branch_exit_repinned q f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V hT1 hqT
      hV hVinv hP3 hQT hκ30Q hLL5 ℰ hws (fun r hr => hAsub (hsubA r hr))
      (fun r hr => hUA r (hsubA r hr)) α η X ε hVα hα hη2 hTX hX0 hdebit hL0 hqlog
      H N Xd P Q j M b cf (hM j hj) hbudget
  · -- ⟦the `𝒯_L` branch⟧ the pair socket, spent once per block
    intro j hj ℰ hws hsubA
    exact tLChi_main_sumsq hCs hcs q hH2 P Q j N Xd cf b hcf1 (hHj j hj) T V L
      ((Real.log X) ^ (-106 : ℝ)) Rbd hslot ℰ hws (fun r hr => hAsub (hsubA r hr)) hT1 hqT
      (hB3 j hj) (hBT j hj) (hκ30 j hj) hLL5 hV hVδ (hBT10 j hj) hTL hlogT1 hLe (hWL j hj)
      hlogV (hgate j hj) hRbd
      (fun r hr => hR j hj r
        (hsubA r (tLsetChi_subset q H P Q j cf ((Real.log X) ^ (-106 : ℝ)) ℰ hr)))

/-! ## §4 — ⟦THE SLOT-WAVE DELIVERABLE (2/2)⟧ the `𝒰`-exit with the SOCKET GONE

§3's compose at §2's discharged socket.  `hslot` leaves the hypothesis list; what replaces it
is the per-`(q,T)` floor — `T₀ ≤ T` and the four gates — carried in-statement, verbatim.

⟦THE HONEST RESIDUE, restated⟧ what `usetChi_window_meansq_gated` still asks for, all named
and all in-statement:

1. **the `𝒰`-package** — `f`, `hf1`, `Pseq/Qseq`, `δ`, `J`, `Jb`, the level data `V` with
   `hVinv`/`hVδ`, the thinness exponents `α, η, ε` with `hVα`/`hα`/`hη2`/`hdebit`, the budget
   `hbudget`, and the membership `hUA : A ⊆ 𝒰`'s fibre form;
2. **the per-`j` block gates**, uniform on `ramI H P Q` (`hHj`, `hB3`, `hBT`, `hκ30`,
   `hBT10`, `hWL`, `hgate`) plus the ambient height/scale gates (`hT1`, `hqT`, `hV`, `hP3`,
   `hQT`, `hκ30Q`, `hLL5`, `hlogT1`, `hTL`, `hLe`, `hlogV`, `hTX`, `hX0`, `hL0`, `hqlog`);
3. **`Rbd`** — the pointwise co-factor bound on `𝒯_L` (NOT a `𝒰`-property: the landed rung
   says so, and the ladder cannot supply it);
4. **the Lemma-12 error row `E`** (`HybridMoments.lemma12_meansq_all_chi` supplies it);
5. **the per-`(q,T)` floor** — `T₀ ≤ T` and G1–G4, the price of the socket's discharge;

plus the WELL-FORMEDNESS binders the five groups do not enumerate (⟦PORT-AUDIT,
2026-07-30⟧): `hJb1`, `hJbJ`, `hδ0`, `hH2`, `hcf1`, `hM`, `hAm`, `hAsub` —
normalization, range and measurability conditions, no analytic content.

⟦THE FOUR LOG SCALES, kept apart⟧ the gates read `log(5T+1)`, the socket's decay denominator
reads `log(qT)`, the count and the kill read `L ≥ log(qT)`, and the `𝒯_S` level reads
`log X`.  None of the four is substituted for another anywhere in this statement. -/

set_option maxHeartbeats 800000 in
-- Same cause as §3: the composed statement carries the ladder's full gate list.
/-- **⟦A3, GATED⟧ THE `𝒰`-EXIT, UNCONDITIONAL IN THE SOCKET.**  The `χ`-summed window mean
square of the twisted Dirichlet polynomial on `A ⊆ [−T,T]`, with `HalaszPrimesChi` DISCHARGED
by §2's pair row: the constants `Cs, cs, T₀, Kq, Ks` are the port's own (`Ks` ineffective,
Siegel; the rest effective), and the socket's cost appears as the four `q`-vs-`T` gates. -/
theorem usetChi_window_meansq_gated :
    ∃ Cs cs T₀ Kq Ks : ℝ, 0 < Cs ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (f : ℕ → ℂ), (∀ n : ℕ, ‖f n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (δ : ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J → 0 < δ →
      ∀ (T V L X : ℝ), 1 ≤ T → 1 < (q : ℝ) * T → 1 ≤ V →
        V⁻¹ ≤ δ / ((Nat.log 2 (Qseq Jb + 1) + 1 : ℕ) : ℝ) →
        3 ≤ Pseq Jb → (Qseq Jb : ℝ) ≤ (q : ℝ) * T →
        30 ≤ Real.log ((q : ℝ) * T) / Real.log (Qseq Jb) →
        5 ≤ Real.log (Real.log ((q : ℝ) * T)) →
      ∀ α η ε : ℝ, Real.log V ≤ α * Real.log (Pseq Jb) → α ≤ 1 / 4 - η → 2 * η ≤ 1 →
        T ≤ X → 0 < X → (q : ℝ) ^ (2 * α) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        -- ⟦THE PER-`(q,T)` FLOOR — what the socket's discharge costs⟧
        T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * T) → Real.log ((q : ℝ) * T) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q M : ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 M) →
        thinBundleChi ((q : ℝ) * T) V (Pseq Jb) (Qseq Jb) * X ^ (1 - 2 * η + ε) ≤ (M : ℝ) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * T) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ T ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (-T) T →
        (∀ r : DirichletCharacter ℂ q × ℝ, r.2 ∈ A → r ∈ UsetChi q f Pseq Qseq δ J) →
        (∀ j ∈ ramI H P Q, ∀ r : DirichletCharacter ℂ q × ℝ, r.2 ∈ A →
          ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        (∑ χ : DirichletCharacter ℂ q, ∫ t in A, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (∑ j ∈ ramI H P Q,
                  (5128 * (Real.log X) ^ (-200 : ℝ) * (M : ℝ) * (1 + Real.log (2 * T))
                      * (∑ m ∈ Finset.Icc 1 M,
                          ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
                    + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
            + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKs, hpt⟩ := halaszPrimesChi_pointwise_of_gates
  refine ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hT₀, hKq, hKs, ?_⟩
  intro q _ f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0 T V L X hT1 hqT hV hVinv hP3 hQT hκ30Q hLL5
    α η ε hVα hα hη2 hTX hX0 hdebit hL0 hqlog hVδ hT₀T hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV
    H hH2 N Xd P Q M a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd
    A hAm hAsub hUA hR E herr
  exact usetChi_window_meansq_of_socket hCs hcs q f hf1 Pseq Qseq δ J Jb hJb1 hJbJ hδ0
    T V L X (hpt q T hT₀T hG1 hG2 hG3 hG4) hT1 hqT hV hVinv hP3 hQT hκ30Q hLL5
    α η ε hVα hα hη2 hTX hX0 hdebit hL0 hqlog hVδ hlogT1 hTL hLe hlogV
    H hH2 N Xd P Q M a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd
    A hAm hAsub hUA hR E herr

end Salt.MR
