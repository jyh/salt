# CMU-HUNT — the band-lane constant traced to its leaves (2026-08-02)

**VERDICT: EFFECTIVE, not opaque — and the rider as stated is unsatisfiable
by the corpus's own witness.** The honest ceiling on the constant the chain
actually produces is `log Cband ≈ 22 661`, not 40. Siegel never enters the
constant (only the threshold x₀, via PortClose.lean:77). Discharge is by
A-WINDOWING, exactly the dissolving-class move the council named.

## 1. The mint census (every ∃-hop walked)

`C_mu = max C₁ C₂` (MobiusChiRateClose.lean:1339), both rows A-free;
`Cband = 2·C_mu·4³ + 1` (LambdaRateTwisted.lean:715 at s13Aexp = 3),
passed through unchanged to the rider.

- **Row 1 (χ≠1): 100% closed form** — every leaf a literal
  (ZeroFree 1/50456, ZeroFreeReal c₀ = 1/126848, LFunctionInvShallow's
  c₄ = x²/16, Kp = 169K at m = 4, Ctot, C₁ = 5·Ctot + 2).
  Probe: **log C₁ = 384.37**.
- **Row 2 (χ₀): the dominant row** — driven by the LITERAL double-exp
  tower T₀ (Vk/PowRegion.lean:354, "astronomically lazy" by its own
  docstring): log log(T₁+2) = A_pow = 1251.23; the shallow gate spends
  9·A_pow, squared ⇒ **log C₂ = 22 655.7**.
- **The structural law: log Cband ≈ 18·A_pow + 139.**

## 2. The two genuine opacity leaves (both ζ-row, both denominators)

1. SW/ZetaZeroFree.lean:180 — ε₀ = infDist to the zeta zeros via
   `IsCompact.exists_isMinOn` (feeds c₃ = min(1/75712, ε₀·log2)).
2. SW/ZetaInvShallow.lean:53 — δ = ‖Zc z₀‖ via the same compactness
   (feeds C = max(1/c, 4/(δ·log2⁷), ...)).

Neither is Siegel. Both are non-binding but blocking: floors
ε₀ ≥ 1.9e-5 and δ ≥ 7.7e-16 make them vanish into existing literals —
but without floors, no numeric discharge at any A (they sit under
division).

## 3. The A-window (the consumer's honest tolerance)

`log Cband ≤ 40` is spent at exactly ONE site (S11HoistGrade.lean:468 →
Mfl ≤ 2³⁵⁵ → FlatFloorBump.lean:124's `flatDoorM_ge_pow355`). Solving
against flatDoorM A = ⌊e^{1.6A}/310301⌋:

> **log Cband ≤ 0.64·A₀ − 4.2** — at the design floor A₀ = 162 the true
> tolerance is already 99.5 (the corpus asks 40, wasting 59 nats); the
> traced ceiling 22 661 needs **A₀ ≈ 35 414** (Mfl ≤ 2^{81 728}).
> Raising A₀ is free: A is symbolic in the terminal and every A-consumer
> loosens as A grows.

## 4. The ratified repair (council v5 #3, the recommendation)

- **(b) BAND-WINDOW — cheap, class A/B, one wave**: generalize
  `flatDoorM_ge_pow355` → `flatDoorM_ge_pow n` under
  A ≥ (n·log2 + log 310301 + 1)/1.6; thread 2³⁵⁵ → 2ⁿ and 162 → A₀(n)
  through the six consumer hops (S16Budget:1430/1655/1760/2618,
  S16BudgetFlat, S16FlatTerminal(-Linear)); restate the rider as
  **log Cband ≤ 0.64·A₀ − 4.2 with A₀ := 36 000** (~586 nats of margin
  over the traced ceiling). KEY CONSEQUENCE: C_mu is a FIXED real
  (A-free), so the A-windowed rider dissolves in the classical limit —
  **hband leaves the ineffective-limit corollary's hypothesis list.**
- **(a) the effective discharge — ~4-5 waves, later**: floor the two
  compactness leaves (δ easy — explicit |(s−1)ζ| floor on a box; ε₀ the
  low-height zero-free strip, class C, mind circularity), then ~12
  `_bounded` conjunct-carry twins down the chain (the EPSPIN genre, no
  new analysis). This makes the EFFECTIVE regime's hband actually
  satisfied by the corpus's own witness.
- **NOT viable**: shrinking the constant to fit 40 (needs A_pow ≲ 5
  against PowRegion's hard-coded +1100 — a sharper VK region,
  research-tier).

Probes: scratchpad cmu/probe.py, cmu/window.py (mpmath 60 dps, all
inputs the corpus's own closed forms).
