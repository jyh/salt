# S2 inner bound — complete Fable design (2026-07-09)

The verified design for the LAST open piece: the S2 collision per-assignment
inner bound. Supersedes the `S2InnerBoundQ` atom (RHS `Qdiag_gv` — has a
hidden per-u `Bv ≥ cB₁` issue, do NOT pursue). Every inequality below was
hand-verified at Fable tier. Implementation is now mechanical (C-tier with
this recipe). Context: `Salt/Maynard/S2Collision.lean` (committed 5700181)
has the collision assembly conditional on the atom; re-thread to the new
RHS `Ndiag` below.

## Definitions
- `V := lamPhiContractM k R (W k) m y` (S2DiagRestricted). `f₀ := fTilde k R T`
  (TensorA1, the R₀-cutoff of fWt), tensor `y = ∏f₀·1_𝒟` (hy).
- `B₁ := B1 k R (W k) T = Σ_{r∈sqfCop(R₀,W)} fWt(r)/φ(r)`.
- `G-diag := Σ_{u∈𝒟, uₘ=1} ∏_{i≠m} f₀(uᵢ)²/g(uᵢ)`   (g = gMult).
- `Ndiag := 4·B₁²·G-diag`  (the CORRECT collision-bound RHS).

## Node A — V_abs (direct, NO lemma53 needed)
**Statement.** For `v` with `vₘ = 1`, coords squarefree (else `V(v)=0`,
separate trivial lemmas: `vₘ≠1 ⟹ V=0` since `vₘ|dₘ=1`; non-squarefree or
pairwise-incompatible or ∏≥R coords ⟹ empty d-filter ⟹ V=0):
`|V(v)| ≤ 2·B₁·∏_{i≠m} f₀(vᵢ)·vᵢ/φ(vᵢ)²  ≤  2·B₁·∏_{i≠m} f₀(vᵢ)/g(vᵢ)`.
**Proof.** `lamPhiContractM_collapse` (Lemma53.lean, needs only vₘ=1):
`V(v) = Σ_{a∈𝒟, vᵢ|aᵢ} (y_a/∏φ(aᵢ))·∏_{i≠m}(μ(aᵢ)vᵢ/φ(aᵢ))`. Take abs
(|μ|≤1, y_a ≤ ∏f₀(aᵢ) pointwise). Relax `a∈𝒟` to independent coordinate
ranges (terms ≥0; guarded_sum_le_prod pattern, LamBoundSharp). Coordinate m:
`Σ_{aₘ} f₀(aₘ)/φ(aₘ) = B₁` (fTilde vanishes off sqfCop(R₀); R₀ ≤ R).
Coordinate i≠m: `Σ_{aᵢ: vᵢ|aᵢ} f₀(aᵢ)·vᵢ/φ(aᵢ)²`: f₀(aᵢ) ≤ f₀(vᵢ)
(fTilde divisor-antitone — small lemma fTilde_anti from fWt_anti, HOmit.lean:
d|m, m∈sqfCop ⟹ d∈sqfCop); reindex `aᵢ = vᵢ·c` (aᵢ squarefree ⟹ gcd(vᵢ,c)=1,
φ multiplicative): `≤ f₀(vᵢ)·(vᵢ/φ(vᵢ)²)·Σ_c μ²(c)/φ(c)²`, and `Σ_c ≤ 1 +
12k²/D₀ ≤ 2` by **phiSq_tail_bound** (Lemma53.lean, landed) since c's primes
> D₀ (coprime W). Total: `2B₁·∏f₀(vᵢ)vᵢ/φ(vᵢ)²`. Final step per prime:
`p(p−2) ≤ (p−1)²` ⟹ `vᵢ/φ(vᵢ)² ≤ 1/g(vᵢ)`.

## Node B — the per-assignment bound (erasure on f₀²/g weight)
**Statement.** For squarefree `s` (primes > D₀), `α ∈ assignments k s`,
`σ = slotProd s α fst`, `τ = slotProd s α snd`:
`|Σ_{u∈𝒟} ∏g(uᵢ)·V(u∨σ)·V(u∨τ)| ≤ 3^{ω(s)}·∏_{p|s}(p−2)⁻²·Ndiag`.
**Proof.** Terms with `σₘ≠1 ∨ τₘ≠1 ∨ uₘ≠1` vanish (V=0). Termwise abs +
Node A at `v = u∨σ, u∨τ` (coords squarefree = lcm of squarefrees ✓):
summand `≤ 4B₁²·∏g(uᵢ)·∏_{i≠m}[f₀((u∨σ)ᵢ)/g((u∨σ)ᵢ)]·[f₀((u∨τ)ᵢ)/g((u∨τ)ᵢ)]`.
g-cofactor split: `g((u∨σ)ᵢ) = g(uᵢ)·∏_{p|σᵢ, p∤uᵢ}(p−2)` (g mult on
coprimes; gMult_mul_coprime exists in S2Collision). f₀(u∨σ) ≤ f₀(u)
(antitone). So summand `≤ 4B₁²·[∏_{i≠m}f₀(uᵢ)²/g(uᵢ)]·∏_{p|s}(p−2)^{−εₚ(u)}`
with `εₚ(u) = [p∤u_{iₚ}] + [p∤u_{jₚ}] ≥ 1` ALWAYS (u pairwise coprime ⟹ p
divides ≤ 1 coordinate; iₚ≠jₚ). Partition u by `Q = {p|s : p|u_{iₚ} ∨ p|u_{jₚ}}`
(2 exclusive slot-choices per p∈Q): for p∉Q factor `(p−2)⁻²` direct; for
p∈Q factor `(p−2)⁻¹` + ERASURE at the occupied slot: `u ↦ update u l (u_l/p)`
injective, weight `f₀(u_l)²/g(u_l) ≤ (p−2)⁻¹·f₀(u_l/p)²/g(u_l/p)` (f₀
antitone + g(u_l) = (p−2)g(u_l/p)). [This is s2_erase_branch's structure
with weight f₀²/g instead of g·(∏f₀)²/φ — fresh small lemma, same proof
shape.] Sum: `Σ_Q 2^{|Q|}·∏_{p∈Q}(p−2)⁻¹(erasure)·∏_{p∈Q}(p−2)⁻¹(cofactor)
·∏_{p∉Q}(p−2)⁻² = 3^{ω}∏(p−2)⁻²` times G-diag. ∎

## Node C — mechanical pieces
1. **euler_tail_L** (generalize euler_tail to arbitrary L≥1, bound 4L/D₀
   for 4L ≤ D₀; same Rankin/powerset proof). Use at `L = 6k²`:
   assignments count (k²−k)^ω × 3^ω × [per-prime (p−2)⁻² ≤ 2(p−1)⁻², p≥5]
   2^ω folds to (6k²)^ω·∏(p−1)⁻². Gives Σ_{t>1} ≤ 24k²/D₀ (needs 24k²≤D₀ ✓ k≥24).
2. **Re-thread the collision assembly** (S2Collision.lean committed
   structure): |s2CollisionForm| ≤ (24k²/D₀)·Ndiag = (96k²/D₀)·B₁²·G-diag.
   Replace the S2InnerBoundQ hypothesis by the proven Node-B bound.
3. **Gdiag_le**: `G-diag ≤ 2·A₁^{k−1}`. Via box relaxation (G-diag ≤ A_g^{k−1},
   A_g := Σ_{r∈sqfCop(R₀,W)}f₀(r)²/g(r)) + the sum-level φ/g average:
   `A_g ≤ A₁·(1 + c/D₀)` (expand ∏(p−1)/(p−2) = Σ_{d|r}h(d), h(d)=∏1/(p−2);
   swap; d>1 tail Σh(d)/φ(d) ≤ c/D₀ via primes>D₀ convergent tail), then
   `(1+c/D₀)^{k−1} ≤ e^{ck/D₀} ≤ 2` (D₀=k³). NO C^k.
4. **s2Compat_ge_N**: compat ≥ s2FullFormM − (96k²/D₀)B₁²G-diag.

## Downstream check (verified): C5 closes with room
Qdiag = s2FullFormM ≥ (1/4)B₁²A₁^{k−1} − o(1) (s2main_lower +
s2_tensor_lower_cheb, committed). Collision ≤ (96k²/D₀)·B₁²·2A₁^{k−1} =
(192/k)B₁²A₁^{k−1} (D₀=k³). Ratio collision/main ≤ 768/k → 0. Then C4 over
compat pairs (EH machinery in S2Eh.lean: s2PrimeCount_approx', eh_error_pow,
the endpoint bounds — reusable from the reverted-but-designed herr work,
with the (3k)^ω fiber count) and C5 (ratio via ratio_prize/exists_k0_ratio_gt
+ pigeonhole → BoundedGapsFromEH).

## Remaining after this: herr fiber count ((3k)^ω, compat pairs only now —
collisions handled by the signed bound), C4 assembly, C5. All designed.
