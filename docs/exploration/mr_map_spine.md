# MR consumption map — what the log-Chowla spine actually needs from "MR"

All claims GROUNDED (file:line) unless marked MEMORY. MR is the longest-parked
campaign: nothing below is from memory; every statement was re-read this session.

## 1. The spine's terminal surface and its exact conditionality

`log_chowla_two_final` — Salt/Entropy/Chowla/SpineFinal.lean:260-272:

```
∃ (δ₀ : ℝ) (R : ChowlaRegime) (H : ℕ) (c₁ C : ℝ),
  0 < δ₀ ∧ 0 < c₁ ∧ 0 < C ∧ R.Hlo ≤ H ∧ H ≤ R.Hhi ∧
  ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ → MRTUniformity R δ →
    ∀ (t g : ℝ), 0 < t → 0 < g →
      g ≤ (R.eps)^6 * H / (18 * (2*log 4) * log H) - log 2 →
      C*(H/log H)*(1*R.eps) + C*(H/log H)*R.eps^2
          + shellError R H t g (H/(log H * logloglog H))
        ≤ c₁ * (R.eps * H / log H) →
      ¬ logChowla2Fails R.eps R.x R.ω
```

Conditional on exactly TWO things:
1. **`MRTUniformity R δ` at any `0 < δ ≤ δ₀`** — the MR side. δ₀ is witnessed
   as `(R.eps)/(2*K)` (SpineFinal.lean:309), a FIXED positive constant once ε
   is chosen (`exists_rat_btwn` below `cE/(32·log 4)`, SpineFinal.lean:278-291).
   MR does NOT need o(1) decay — fixed-δ₀ grade suffices.
2. **The `t`/`g`/`hbudget1` residual** — the entropy-decrement AM–GM balance
   (docstring SpineFinal.lean:254-258: "the honest analytic core... Tao's
   Lemma-3.x quantitative close"). This is SPINE-internal, NOT an MR
   obligation; it is the registered node **SPINE-BUDGET** (pilot.md:5255-5259,
   "the node for the unqualified form"). Everything else — hepsc, H₀, hI
   (κ = H/(log H·logloglog H)), hbudget2 — is DISCHARGED in the final surface
   (SpineFinal.lean:247-253).

`logChowla2Fails eps x ω` — Salt/Entropy/Chowla/ChowlaFailure.lean:59-64:
`ε·log ω < |Σ_{n ∈ Ioc(x/ω, x]} λ(n)λ(n+1)/n|` (Tao (2.4), model
`a=1,b=0,h=1,g₁=g₂=λ`, unnormalized RHS).

So: **discharging MRTUniformity at the witnessed R for one δ ∈ (0, δ₀] makes
log-Chowla-2 unconditional modulo SPINE-BUDGET; discharging both makes it
unconditional, full stop.** Axiom base of everything landed:
[propext, Classical.choice, Quot.sound] (build-time audit, All.lean:92-241;
`log_chowla_two_final` on the audit list at All.lean:201).

## 2. THE INTERFACE — the exact Prop the spine wants from MR

### 2a. The full door (what the terminal surface consumes today)

`MRTUniformity` — Salt/Entropy/Chowla/MRTDoor.lean:48-50:

```lean
noncomputable def MRTUniformity (R : ChowlaRegime) (δ : ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
    (∫ n, ‖windowExpSum H n α‖ ∂(logMeasure R.x R.ω)) ≤ δ * (H : ℝ)
```

with `windowExpSum H n α = ∑_{i : Fin H} λ(n+i+1) · e(α(i+1))`
(MRTDoor.lean:37-39; `liouvilleWindow H n i = λ(n+i+1)`, Windows.lean:27-29)
and `logMeasure x ω` = the normalized 1/n measure on `Ioc (x/ω) x`
(LogMeasure.lean:26-28).

**Quantifier-position invariant (load-bearing, kernel cannot police):** the
`∀ α` is OUTSIDE the L¹ integral — Tao 1509.05422 Prop 2.4, a THEOREM proven
from MRT arXiv:1503.05121. The sup-INSIDE variant is Tao (4.1), OPEN
(MRTDoor.lean:41-47 warning block; same warning at :95-108).

**Regime scale (what makes it hard):** `R` is the witnessed regime from
`chowlaRegime_exists_param` (SpineFinal.lean:295-296); H ranges over
`[Hlo, Hhi]` with `Hlo ≥ 4·10⁶` and `Hhi ≥ chowlaTower C0 a Hlo J`
(tower-sized; Regime.lean:56-110 fields `hHlo_floor`, `hfit`, `hJcon`), and x
sits further above via `hheadroom'`. So the door is the DEEP `H = x^{o(1)}`
regime: internal Dirichlet-polynomial heights reach T ≈ x/H, polynomial in the
scale (POLE-2 memo, s3-a3-design.md:933-971).

### 2b. The registered CHEAPER honest target (Xi door)

`MRTUniformityXi` — MRTDoor.lean:109-111:

```lean
∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ ξ ∈ bigXi R.eps H,
  (∫ n, ‖windowExpSum H n (-(ξ.val : ℝ)/(H : ℝ))‖ ∂(logMeasure R.x R.ω)) ≤ δ * H
```

Only the major-arc frequencies `α = −ξ/H`, `ξ ∈ Ξ_H = bigXi R.eps H` =
`{ξ ∈ ZMod H : ε²/log H ≤ ‖S_H(−ξ/H)‖}` with `S_H(α) = Σ_{p∈𝒫_H}(1/p)e(αp)`
(CircleMethod.lean:35-45). `|Ξ_H| ≤ K` is landed (`bigXi_bounded`,
consumed at SpineFinal.lean:231/293). Extra explicit hypothesis `0 ≤ δ`
(no longer derivable — the derivation fired the door at α = 0;
MRTDoor.lean:121-128). The trivial weakening `mrtUniformity_implies_xi` is
MRTDoor.lean:116-119; the Xi seam `contradiction_of_mrtDoorXi` SHIPS
(MRTDoor.lean:127-157). CAVEAT (W4-MAJOR-R0 RED, s3-a3-design.md:608-635):
ξ = 0 ∈ Ξ_H always, and its instance is already full MR short-interval
strength — the weakening shrinks the SURFACE (drops the ~2M minor-arc
Kátai/BSZ package, s3-a3-design.md:922-926), not the DEPTH.

**GAP:** no Xi-form terminal surface exists. `log_chowla_two_final` consumes
the FULL door only; rewiring it to `MRTUniformityXi` is the registered
Fable spine-rewire, coupled with SPINE-BUDGET ("same surface",
s3-a3-design.md:924-926; pilot.md:5541-5545). MR-RESHAPE's open design
question: whether the ξ/H major-arc restriction propagates into the internal
Plancherel height range is UNRESOLVED — do not assume (s3-a3-design.md:962-968).

### 2c. What the seam needs vs what the spine supplies

`contradiction_of_mrtDoor` (MRTDoor.lean:57-93): door + `|Ξ_H| ≤ K` +
`K·δ < c₀·ε` + the mass lower bound `hlower`. Only the DOOR is external;
`hXi`, `hsmall`, `hlower` are all produced spine-internally
(bigXi_bounded, δ₀ = ε/(2K), outer_combine/circle-method chain).

### 2d. Full consumer enumeration (grep MRTUniformity, Salt/**/*.lean)

- Theorem23Shell.lean:159 (`log_chowla_two_shell`, hdoor + hbudget2)
- SpineClose.lean:29, :178 (`log_chowla_two_conditional`, `_regime`)
- TowerDischarge.lean:95-96 (`log_chowla_two_of_door` — δ₀ = ε/(2K) form)
- SpineFinal.lean:47, :203, :263 (`spine_False_core`, `_hoisted`, `_final`)
- MRTDoor.lean:59, :117, :129 (seam, weakening, Xi seam)

## 3. The registered MR infrastructure + adjudications (docs)

- **MR-R0** (s3-a3-design.md:896-931; pilot.md ledger "MR-R0 ADJUDICATED"):
  campaign registered at central 12–16M (band 8–25M+), larger than HB-ENGINE.
  Landed corpus then: large-sieve stack, classical dVP region, smoothed
  Perron/contour, λ long-sum rates, Mertens. Absent: Halász–Montgomery
  (POLE 1, 2–5M), vertical-line L², Saffari–Vaughan, Turán–Kubilius, and
  VK (POLE 2).
- **Registered openers** (s3-a3-design.md:928-931): **MR-C** = Turán–Kubilius
  (B/C, self-contained; no Lean file exists yet — grep TuranKubilius over
  Salt/ is empty) and **MR-A** = vertical-line L² from `analytic_LS` via
  `gallagher_pointwise` (C; suppliers exist in Salt/LS/Gallagher.lean,
  Salt/LS/ArithmeticLS.lean). Both "unconditionally useful either way"
  (s3-a3-design.md:969-971). First registered milestone: ξ=0 untwisted
  log-averaged cheap-MR for λ (Tao Suppl. 6 route: Turán–Kubilius +
  Plancherel + Halász-type + ZFR + Mertens; s3-a3-design.md:926-928).
- **POLE-2 memo** (s3-a3-design.md:933-971): MR is VK-GATED. The ZFR enters at
  exactly one step — `−ζ′/ζ(1 + 1/log Q + it) = o((log|t|)^{0.98})` consumed
  uniformly at heights |t| ≍ x (polynomial in scale). dVP gives only
  O(log|t|): short by a full power of log; fixed-δ₀ does NOT rescue
  (Plancherel needs `|μ̂(ξ)| ≤ 1 − δ₀` uniformly over polynomial-height
  support). Any θ < 0.98 power region suffices; VK's 2/3 sufficient not
  necessary.
- **Option-C RED** (s3-a3-design.md:1076-1095) — why θ < 1 STRICTLY:
  `D(λ, n^{it}; x)² = loglog x + log|ζ(1+it)| + O(1)`; width `(log t)^{−θ}`
  gives `log|ζ(1+it)| ≥ −θ·loglog t`, so `D² ≥ (1−θ)·loglog x` — diverges for
  ANY θ < 1. Littlewood's coefficient is EXACTLY 1 (width loglog t/log t ⟹
  D² ≥ logloglog x + O(1), bounded). Invariant under Tao's P₋/P₊ cutoff
  choices. So: MR gate = any power region θ < 1 strictly; by VK-R0's
  quantization θ ∈ {1, ≤ 3/4} (s3-a3-design.md:973-1012) that means
  Vinogradov machinery, full stop.
- **THE GATE IS NOW CLEARED IN-CORPUS:** `zeta_zero_free_region_pow` —
  Salt/Vk/GrowthPow.lean:1044-1048, on the Vk audit list (Salt/Vk/All.lean:133):
  `∃ c T₀, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ, ζ(ρ) = 0 → T₀ ≤ |ρ.im| → ρ.re ≤ 1 −
  c/((log|ρ.im|)^{3/4}·(loglog|ρ.im|)³)` — θ = 3/4 < 1, exactly the
  vk-freeze.md:34 target ("MR gate satisfied"). CONSUMPTION WARNING
  (vk-freeze.md:10): constants are existential and astronomically lazy
  (fires only for log t ≳ 1.5e26); the MR gate must consume the width SHAPE
  θ = 3/4 < 1 — consumers needing dominance at accessible heights must min
  with the landed classical region. Salt/Vmvt/ (18 files) backs it.
  gold-window-report.md:113 queues "close the VK region → the MR gate design
  block" — the region is now closed; the MR gate DESIGN BLOCK is the next
  Fable-tier step.

## 4. The transport wall — what is FORBIDDEN vs what stays OPEN

`TransportWall.lean` (node TD-R2b):
- **Forbidden:** `orthogonality_wall` (:143-147) — the slots (PmNormalized :71
  + PairCollapse :77) cannot force TwinDetecting (:91); and
  `no_slot_derived_twin_linkage` (:155-159) — NO linkage L can be both
  slot-derivable and detection-sufficient (witness: constant weight w ≡ 1,
  slot-passing + twin-blind, :116-133). The entropy mechanism's
  pair-collapse structure CANNOT be composed into twin-relevant weights along
  any slot-derived route. boundary-map.md:91-99: a real transport door must
  supply (1) an entropy budget for an unbounded weight system AND (2) a
  dilation-invariant correlation structure outside the CM±1 class — neither
  weakenable.
- **Honest scope** (TransportWall.lean:51-60): only slot-satisfaction-ALONE is
  ruled out; a door whose linkage pins w beyond the slots is not excluded —
  that strong wall is the parity/twin-correlation open problem, prose-only.
- **Stays open:** log-Chowla-2 ITSELF as the unconditional target. The wall
  says MR discharge buys log-Chowla-2, NOT twins; it does not obstruct the MR
  campaign one bit. Related exhibit: `dilation_forces_log` (BoundaryMap,
  audit All.lean:193) — logarithmic averaging is forced by dilation
  covariance, so natural-Chowla needs a different change of variables
  (boundary-map.md:105-110).

## 5. THE INTERFACE, stated as precisely as the corpus allows

MR must prove, for the ONE witnessed regime R (∃-bound inside
log_chowla_two_final; parametric builder `chowlaRegime_exists_param`,
RegimeParam.lean, lets MR pick its own R at any admissible ε and floor):

> **∃ δ ∈ (0, ε/(2K)] : ∀ H ∈ [R.Hlo, R.Hhi], ∀ α ∈ ℝ,
> ∫ ‖Σ_{i<H} λ(n+i+1)·e(α(i+1))‖ d(logMeasure R.x R.ω)(n) ≤ δ·H**
> — i.e. `MRTUniformity R δ` (MRTDoor.lean:48) with δ ≤ δ₀
> (δ₀ = R.eps/(2K), SpineFinal.lean:309), quantifier ∀α OUTSIDE the integral.

Weakened admissible form after the registered Fable spine-rewire (couples with
SPINE-BUDGET): `MRTUniformityXi R δ` + `0 ≤ δ` (MRTDoor.lean:109) — α
restricted to the ≤ K major-arc points −ξ/H, ξ ∈ bigXi R.eps H; seam already
ships (contradiction_of_mrtDoorXi). Whether the restriction helps INTERNALLY
is MR-RESHAPE's open question (s3-a3-design.md:962-968).

What MR does NOT owe the spine: |Ξ_H| ≤ K, the budgets hbudget1/2, the mass
lower bound, t/g — all spine-internal (SPINE-BUDGET's node). What the corpus
now holds toward MR that it did not at MR-R0 pricing: the θ = 3/4 power
zero-free region (Salt/Vk/GrowthPow.lean:1044) + VMVT track + LS suppliers
for MR-A. The re-pricing of the 12–16M central under a landed VK is exactly
the queued "MR gate design block" (gold-window-report.md:113).
