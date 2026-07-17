/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The tower-numeric discharge of the log-Chowla-2 spine, node W3E-TOWER

`log_chowla_two_conditional` (`Salt/Entropy/Chowla/SpineClose.lean`, node
W3E-FINAL) closes the log-Chowla-2 contradiction, but threads TEN inputs through
its `∀`-block: the window range (`R.Hlo ≤ H`, `H ≤ R.Hhi`), the combined
producer floor (`H₀ ≤ H`), the coupling `hepsc`, the four decrement budgets
(`ht`/`hg`/`hgle`/`hI`), and the two numeric closures (`hbudget1`/`hbudget2`).

This node discharges everything the LANDED regime witness can honestly discharge,
producing the cleanest citation surface.  Concretely:

* **The `H`-selection + `hI`** are discharged TOGETHER by `entropy_decrement`
  (Tao 1509.05422 Lemma 3.1): the tower produces an admissible `H ∈ [H₋, H₊]` at
  which the mutual information is below `H/(log H · logloglog H)`.  That value is
  the discharged `κ`; the `residue : liouville` order of `hI` is the decrement's
  `liouville : residue` order swapped by `mutualInfo_window_comm`.
* **`hbudget2`** (`K·δ < c₀·ε`) is folded into the door-smallness threshold
  `δ₀ = ε/(2K)` at the choice `c₀ = 1`: any door level `δ ≤ δ₀` clears it.

What CANNOT be discharged for the fixed witness is exactly the **opaque-constant
genre** — three inputs that are TRUE-but-undecidable because the witness pins
`ε = 1/2` while the producer constants (`cE`, `c₁ = cD3/4`, `C`) are
`∃`-extracted (opaque):

1. `H₀ ≤ H` — the combined floor sits below the decrement level.  Opaque:
   `H₀` is a `max` of "H sufficiently large" thresholds and the decrement's `H`
   is `∃`-bound in `[4·10⁶, chowlaTower ..]`; both are opaque, so this needs the
   hypothesis.  (Believed trivially true — the tower endpoint dwarfs any fixed
   floor — but opaque-vs-opaque cannot be proved for the landed witness, which is
   NOT `Hlo`-parametric: `RegimeInst`'s builder pins `Hlo = 4·10⁶` and the
   divergence input `dropSum_exceeds_log_two` is stated at that base.)
2. `hepsc : ε ≤ cE/(32·log 4)` — Tao's "ε small enough".  Opaque: `cE` is the
   `∃`-output of `hreduce_holds_final`; the witness's `ε = 1/2` is not
   `eps`-parametric (the builder pins it), so this stays as a hypothesis.
3. `hbudget1` — the tower error is beaten by the `c₁·εH/log H` margin.  Opaque:
   after dividing by `(H/log H)·ε`, it reduces to `c₁ ≳ (C+1)·ε`, i.e.
   `cD3 ≳ 2(C+1)` at `ε = 1/2` — an inequality between the opaque Mertens
   constant `cD3` and the opaque circle-method constant `C`.

These three stay as explicit hypotheses INSIDE the `∀`/`→` structure (each
flagged above).  Because they reference the SAME `∃`-extracted constants used
elsewhere in the proof, the MRT door is taken as a PARAMETER (a single
`log_chowla_two_conditional` invocation) rather than `∀`-quantified with a
door-free `δ₀`; the two shapes are equivalent in strength, and `δ₀ = ε/(2K)` is
door-free in content.  The `t`/`g` decrement parameters stay `∀`-quantified with
their constraints (`0 < t`, `0 < g`, `hgle`) — honest, since the shell fires for
ANY admissible pair, and `hgle`'s `RHS > 0` is itself `ε`-dependent and hence not
provable for the `ε`-opaque witness.
-/
import Salt.Entropy.Chowla.SpineClose
import Salt.Entropy.Chowla.Decrement

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-- **Mutual-information order swap at the window pair.**  `entropy_decrement`
produces `I[liouvilleWindow : residueWindow]`, while `log_chowla_two_shell`'s
`hI` binder consumes `I[residueWindow : liouvilleWindow]`.  Mutual information is
symmetric (`mutualInfo_def` + `entropy_comm` on the pair), so the two coincide. -/
private lemma mutualInfo_window_comm (R : ChowlaRegime) (H : ℕ) :
    I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      = I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] := by
  simp only [mutualInfo_def]
  rw [entropy_comm (measurable_residueWindow R.eps H) (measurable_liouvilleWindow H)
    (logMeasure R.x R.ω)]
  ring

/-- **W3E-TOWER, the tower-discharged citation surface.**  For the witnessed
Chowla regime `R`, GIVEN the MRT uniformity door at level `δ` (Tao 1509.05422
Prop 2.4, PROVEN in Matomäki–Radziwiłł–Tao arXiv:1503.05121), there is an
admissible decrement level `H ∈ [H₋, H₊]` — produced by `entropy_decrement`,
Lemma 3.1 — at which the Liouville/residue mutual information is below the
discharged budget `κ`, and a door-smallness threshold `δ₀ = ε/(2K) > 0`, such
that log-Chowla-2 does NOT fail as soon as three opaque-constant residuals hold
and the door is small (`δ ≤ δ₀`):

* `H₀ ≤ H`  — the combined producer floor is below the decrement level
  [OPAQUE floor; believed trivially true, not provable for the `Hlo`-rigid
  witness];
* `ε ≤ cE/(32·log 4)`  — the fixed `ε = 1/2` clears the reduce coupling
  [OPAQUE `ε`-smallness];
* the `hbudget1` inequality  — the tower error is beaten by the `c₁·εH/log H`
  margin [OPAQUE `ε`-smallness, `≈ cD3 ≳ 2(C+1)` at `ε = 1/2`].

Discharged here (no longer inputs): the window range `H₋ ≤ H ≤ H₊`, the mutual
information budget `hI` (with `κ = H/(log H · logloglog H)`), and `hbudget2`
(folded into `δ ≤ δ₀ = ε/(2K)`).  The `t`/`g` decrement parameters remain free,
under their constraints `0 < t`, `0 < g`, `hgle`. -/
theorem log_chowla_two_of_door (R : ChowlaRegime) {δ : ℝ}
    (hdoor : MRTUniformity R δ) :
    ∃ (c₁ C K cE κ δ₀ : ℝ) (H₀ H : ℕ),
      0 < c₁ ∧ 0 < C ∧ 0 < K ∧ 0 < cE ∧ 0 < δ₀ ∧
      R.Hlo ≤ H ∧ H ≤ R.Hhi ∧
      I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω] ≤ κ ∧
      ∀ (t g : ℝ), 0 < t → 0 < g →
        g ≤ (R.eps : ℝ) ^ 6 * (H : ℝ)
            / (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2 →
        H₀ ≤ H →
        (R.eps : ℝ) ≤ cE / (32 * Real.log 4) →
        C * ((H : ℝ) / Real.log (H : ℝ)) * (1 * (R.eps : ℝ))
            + C * ((H : ℝ) / Real.log (H : ℝ)) * (R.eps : ℝ) ^ 2
            + shellError R H t g κ
          ≤ c₁ * ((R.eps : ℝ) * (H : ℝ) / Real.log (H : ℝ)) →
        δ ≤ δ₀ →
        ¬ logChowla2Fails R.eps R.x R.ω := by
  classical
  obtain ⟨c₁, C, K, cE, H₀, hc₁, hC, hK, hcE, hblock⟩ :=
    log_chowla_two_conditional R hdoor
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrement R
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hepsRpos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hI : I[residueWindow R.eps H : liouvilleWindow H ; logMeasure R.x R.ω]
      ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
    rw [mutualInfo_window_comm]; exact hMI
  refine ⟨c₁, C, K, cE, (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))),
      (R.eps : ℝ) / (2 * K), H₀, H, hc₁, hC, hK, hcE,
      div_pos hepsRpos (by positivity), hlo, hhi, hI, ?_⟩
  intro t g ht hg hgle hH₀ hepsc hbudget1 hδ hfail
  have hbudget2 : K * δ < 1 * (R.eps : ℝ) := by
    have hle : K * δ ≤ K * ((R.eps : ℝ) / (2 * K)) :=
      mul_le_mul_of_nonneg_left hδ (le_of_lt hK)
    have heq : K * ((R.eps : ℝ) / (2 * K)) = (R.eps : ℝ) / 2 := by
      field_simp
    rw [heq] at hle
    rw [one_mul]
    linarith
  exact hblock H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))) 1
    ht hg hgle hI hbudget1 hbudget2 hfail

end Salt.Entropy.Chowla
