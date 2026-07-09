# Endgame design — C4 (EH over compat) + C5 (ratio + pigeonhole) [Fable, 2026-07-09]

Hand-verified at Fable tier. With `s2-inner-design.md` (Waves 1–2), this
specifies EVERYTHING remaining to `BoundedGapsFromEH`. Implementation is
mechanical from here. Parameters throughout: `K₀=64`, `T = k^{1/8}/log k`,
`R = ⌊N^{1/5}⌋` (or `N^{1/5}` as convenient), `W = W k`, `y = yTensor k R T`,
`f₀ = fTilde k R T` (note: fTilde is automatically zero-patched — fTilde(0)=0
since 0∉sqfCop; hf01 from fWt_nonneg/fWt_le_one; hfmono = fTilde_anti, landed
in VAbs.lean).

## FIFTH FRAGILITY (caught at design time; MUST fix before C5)
The committed `s2main_lower` (S2MainLower.lean) has error term
`(2C·logR/D₀)·Σ_u |contraction u|/∏φ(uᵢ)`. Its natural bound is
`(2C·logR/D₀)·B₁·B₁^{k−1} = (2ClogR/D₀)B₁^k` — and `B₁^k/(B₁²A₁^{k−1})
= (B₁/A₁)^{k−2}/A₁ ~ (logk/2)^{k−2}·klogk/logR`, so error/main
~ `(logk/2)^k/k³ → ∞`. **The committed bound is true but USELESS downstream.**
Root cause: lemma53's error is ABSOLUTE (`C·logR/D₀`), not relative to
`∏f₀(vᵢ)`.

### Fix P1 — `lemma53_rel` (mechanical rework of the landed lemma53)
For tensor `y`, `v` with `vₘ=1`, `v ∈ 𝒟`:
`|yM(v) − contraction(v)| ≤ (∏_{i≠m} fTilde(vᵢ)) · C·logR/D₀`, C R-free.
**Why the landed proof supports it:** every term of the htail sum (Lemma53.lean,
`htail_bound`) has `vᵢ | aᵢ (i≠m)`, so `|y_a| ≤ ∏_{i≠m}f₀(aᵢ) ≤ ∏_{i≠m}f₀(vᵢ)`
(fTilde antitone) — factor `∏f₀(vᵢ)` out of Step-1's strip (was `|y_a| ≤ 1`)
and carry through; identically for the `(G−1)·S` piece (`|contraction(v)| =
∏f₀(vᵢ)·Bv(v) ≤ ∏f₀(vᵢ)·B₁ ≤ ∏f₀(vᵢ)·C₁logR` replaces `abs_mainSum_le`).
Re-run `htail_bound` → `htail_bound_rel`, `lemma53` → `lemma53_rel`.

### Fix P2 — `s2main_lower_rel` (re-thread S2MainLower with P1)
`Qdiag_gv ≥ Σ_{u:uₘ=1}(contraction u)²/∏φ(uᵢ) − (2C·logR/D₀)·B₁·A₁^{k−1}·2`
(the error sum now: `Σ_u ∏f₀(uᵢ)·|contraction u|/∏φ ≤ B₁·Σ_u∏f₀(uᵢ)²/∏φ ≤
B₁·(A₁-type box)^{k−1} ≤ 2B₁A₁^{k−1}` — A-type, NOT B-type; the `≤ 2` from
the coordinate relaxation as in Gdiag_le). Combined with the committed
`s2_tensor_lower_cheb` (`Σ(contraction)²/∏φ ≥ (1/4)B₁²A₁^{k−1}`):
**`Qdiag_gv ≥ (1/8)·B₁²·A₁^{k−1}`** for k in the regime — needs
`(2ClogR/D₀)·2·A₁^{k−1}·B₁ ≤ (1/8)B₁²A₁^{k−1}` ⟺ `32C·logR/D₀ ≤ B₁`
⟸ `B₁ ≥ (φW/W)logR/(16k)` (B1_lower_sharp) and `D₀ = k³ ≥ 512Ck(W/φW)`
(true, W/φW ~ 3logk). [Qdiag_gv = s2FullFormM by s2FullFormM_eq_Qdiag;
that equals the (d,e)-form via s2_diag_lam_restricted = s2main_lower's LHS.]

## C4 — S2m over COMPAT pairs (fixes the herr collision-leak correctly)
File suggestion: extend `Salt/Maynard/S2Eh.lean`.
1. **`s2PrimeCount_collision`**: colliding `(d,e)` (∃i≠j, prime p | dᵢ, p | eⱼ,
   p > D₀) ⟹ `s2PrimeCount = 0`. Proof = `congCountTuple_collision`'s
   (CongCount.lean): counted `n` has `p | n+hᵢ` and `p | n+hⱼ` ⟹ `p | hᵢ−hⱼ`,
   contra `p > D₀ ≥ (H k).sup ≥ |hᵢ−hⱼ| > 0` (hSeq_injective). So
   `S2m = Σ_compat λλ·count` (from the committed `S2m_eq_guarded`).
2. **Main identity**: `(Δπ(m)/φW)·s2CompatFormM = Σ_compat λλ·density`
   (density = `Δπ(m)/(φW·phiLcmProd)`; `Δπ(m) := deltaPi k K₀ N m`,
   committed def). Direct from s2CompatFormM's def (Möbius-free algebra).
3. **Error**: `|S2m − (Δπ/φW)·s2CompatFormM| ≤ Σ_compat |λλ|·|count−density|`,
   per-pair by the committed **`s2PrimeCount_approx'`** (hbij discharged;
   its hyps hold for compat pairs: hcoplcm = pairwise-coprime lcms needs
   exactly NOT-collision + 𝒟-structure; hcopW, hlcmpos from 𝒟; hν₀ from
   exists_nu0). `|λ| ≤ λmax = Cλ(1+logR)^{k+1}` (lam_abs_le_sharp; |yTensor|≤1).
4. **Fiber count** (the (3k)^ω regrouping, COMPAT ONLY — now sound):
   compat ⟹ `qMod = W·∏lcm` is SQUAREFREE (pairwise-coprime squarefree lcms,
   coprime to squarefree W) and `< W·R²`. Fiber
   `#{(d,e) compat, dₘ=eₘ=1 : qMod = q} ≤ (3(k−1))^{ω(q/W)} ≤ (3k)^{ω(q)}`:
   each prime of `q/W` sits in exactly one lcm (pairwise coprime) — assign
   (coordinate i≠m) × (d-only | e-only | both); recover `(d,e)` from
   `(q, assignment)`. Mirror CollisionQuant's assignments/slotProd or
   VAbs's vAssignSet/coord_recover pattern.
5. **EH**: regrouped error ≤ `λmax²·Σ_{q<WR², sqf}(3k)^{ω(q)}(maxDisc(64N+hₘ,q)
   + maxDisc(N+hₘ,q))`; extend ranges to `⌊√x⌋+1` (needs `W·R² ≤ √(N+hₘ)`,
   i.e. `W ≤ N^{1/10}`, N large) and apply **eh_error_pow k (2k+4)** at both
   endpoints (the reverted-but-sound endpoint machinery: le_floor_sqrt,
   xdivlog_le, endpoint_eh_bound — re-create from the design here, they were
   genuine). Result:
   **`S2m ≥ (Δπ(m)/φW)·s2CompatFormM − C·N·(1+logR)^{2k+2}/(logN)^{2k+4}`**
   for N ≥ N₀, C N-free. (errEH·k ≪ main since main ~ N·(logN)^k-order for
   fixed k; the 2k+4 exponent was chosen for exactly this.)
6. **Chain to the diagonal** (Wave-2 output + P2):
   `s2CompatFormM ≥ s2FullFormM − (24k²/D₀)·Ndiag` [Wave 2's s2Compat_ge_N]
   `≥ (1/8)B₁²A₁^{k−1} − (24k²/D₀)·8B₁²A₁^{k−1}` [P2 + Ndiag ≤ 4B₁²·2A₁^{k−1}
   via Gdiag_le] `≥ (1/16)B₁²A₁^{k−1}` for `k ≥ 3072` (192/k ≤ 1/16).

## C5 — the ratio, k₀ selection, pigeonhole (file `Salt/Maynard/Endgame.lean`)
1. **P3 — S1 wiring**: `S1_upper` (S1Bound.lean) takes `hsol`; discharge via
   the committed `cong_solvable` (5-line corollary `S1_upper'` if not already
   done). Then with C1: `S1 ≤ 2·(63N/W)·A₁^k + errS1`,
   `errS1 = C·R²(1+logR)^{4k+2} = o(N/logN)`.
2. **P4 — Δπ shift**: `Δπ(m) = π(64N+hₘ) − π(N+hₘ) ≥ π(64N) − π(N) − hₘ ≥
   (c/2)·N/logN` for N ≥ N₁ (primes_in_interval_ge + `π(N+h) ≤ π(N) + h` +
   hₘ ≤ D₀ fixed). Also `Δπ ≥ 0` trivially where needed.
3. **The counting identity + pigeonhole**:
   `Σ_m S2m = Σ_{n∈window} P(n)·w(n)` with `P(n) = #{m : (n+hₘ).Prime}`,
   `S1 = Σ_n w(n)`, `w = weightSq ≥ 0` (trivial sum swaps). If
   `Σ_m S2m > S1` then ∃n∈window with `P(n) ≥ 2` ⟹ primes
   `p = n+hᵢ ≠ q = n+hⱼ`, both `> N`, `|q−p| = |hᵢ−hⱼ| ≤ (H k).sup id =: C`.
4. **The final inequality** (fixed k, N → ∞): need
   `k·(Δπ/φW)·(1/16)B₁²A₁^{k−1} > 2·63·(N/W)·A₁^k + (o-terms)`, i.e.
   `(k/16)(c/2)(N/(logN·φW))·B₁² > 126(N/W)A₁(1+ε)` ⟺
   **`k·B₁²/A₁ > (4032/c)·(φW/W)·logN·(1+ε)`**.
   Sharp bounds (landed): `B₁ ≥ (φW/W)b⁻¹·log(1+b·log(R₀−1)) − errB1` with
   `b·logR₀ = T·logk = k^{1/8}` ⟹ `B₁ ≥ (φW/W)b⁻¹·(1/9)logk` (log(1+k^{1/8})
   ≥ (1/8)logk·(1−ε), errB1 absorbed for R large); `A₁ ≤ 4(φW/W)b⁻¹(1+ε)`
   (A1_upper_sharp; the s⁻²-boundary term small). So
   `k·B₁²/A₁ ≥ k·(φW/W)b⁻¹(logk)²/(4·81) = (φW/W)·logR·(logk)/324`
   (b⁻¹ = logR/(klogk)). With `logR = logN/5`:
   need `(logk)/1620 > (4032/c)(1+ε)` ⟺ **`logk > 6.6M/c`** — pick
   `k₀ := max(exp(⌈7·10⁶/c⌉), regime floor)` where the regime floor covers:
   k ≥ 3072, logk ≥ 300, `1 ≤ T = k^{1/8}/logk` (⟸ k^{1/8} ≥ logk ✓ at this
   size), `5T ≤ k`, `hEA/hEB/hb4/hX` are N-large (all satisfied for N ≥ N₀(k)).
   The φW/W cancels exactly ✓. `c` = the primes_in_interval_ge constant
   (existential — obtain it first, then choose k₀; the ∃-form is fine).
5. **`BoundedGapsFromEH`**: given `hEH : EH(1/2)`, take `C := (H k₀).sup id`.
   For arbitrary `N`: apply the large-N result at `N' := max(N, N₀(k₀))` —
   primes `p, q > N' ≥ N`, `|q−p| ≤ C`, `p ≠ q`. Convert to the
   `(q:ℤ)−(p:ℤ) ∈ Icc (−C) C` form. ∎ **This is the theorem.**

## Node order (all C-tier, from this doc + s2-inner-design.md)
Wave 3: P1 (lemma53_rel) ∥ C4-items 1,2,4 (collision-zero, main identity,
  fiber count). Wave 4: P2 ∥ C4-items 3,5 (EH assembly). Wave 5: C4-item 6 +
  P3 + P4. Wave 6: C5 (Endgame.lean). Verify each adversarially; the known
  traps: B-vs-A dimensional mismatches (check every error term's f₀-weight),
  per-u vs sum-level bounds, and (p−1) vs (p−2) conversions.
