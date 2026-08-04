# TAU-EXT — the scope verdict, and the price of the tall box

**Date** 2026-08-03 (night). **Node** TAU-EXT (the β-supplier). **Status** verdict landed,
packaging + interface landed (`Salt/SW/TauExt.lean`, 366 ln, 9 decls + 1 def, 3-axiom audited,
`lake build` exit 0). Residual named ⟦TAU-EXT-2⟧ and priced below.

## The question

`dh_repulsion_ordered` (`Salt/SW/TBalR8.lean:1752`) — the landed Deuring–Heilbronn repulsion —
hypothesizes `|Im ρ| ≤ 1`. N2's exit lemma `efZeroSumM_spend_at_efHeight` wants a real-part
ceiling `β` at the campaign box `|Im ρ| ≤ efHeight q + 2 = (log q + 2)⁴ + 2`. Is the height-1
restriction *packaging* (a compactness box chosen for convenience) or *analysis* (the engine
reads the height structurally)?

## The verdict: (a) — PACKAGING

Traced at the bytes. `|ρ.im| ≤ 1` is consumed in the proof at exactly these sites:

| site | what it feeds |
|---|---|
| `DHExtractRho.lean:59` (`norm_zeta_rho_le`) | `hZ ρ …` — `‖zetaHol ρ‖ ≤ Z₀` **at the point ρ** |
| `DHExtractRho.lean:283` | `hZ ρ …`, only to extract `0 ≤ Z₀` |
| `DHExtractRho.lean:412` | `norm_zeta_rho_le` again |
| `DHExtractRho.lean:169` (`emrho_perterm`) | `zeta_partial_em`'s height slot — **which that lemma ignores** (`ZetaEM.lean:123`, binder `_him`) |
| `TBalR8.lean:1591` (`C2Rho_le`) | the crude `‖ρ‖ ≤ 2` |

and nowhere else. Every `β₀`-side use of `hZ` is at a **real** point (`hZ (β₀ : ℂ)`,
`DHCore.lean:352,713`; `DHExtractW.lean:319,1187`; `CrushE.lean:225`) — height 0, already
height-free. There is no contour at height 1, no strip integral, no compactness box in the
engine: the detector floor, the R1 shift, the row caps and the exponent balance never see
`Im ρ` except through `Q = q(|Im ρ| + 2)`, which is the contract's **own** base and is already
height-adaptive.

So the two things the tall box actually costs are:

1. **`Z₀`** — the `zetaHol` bound. `zetaHol_bound` (`ZetaEM.lean:152`) is compactness on
   `[1/2,1] × [−1,1]`: opaque constant, and no way to raise the height without making `Z₀`
   depend on `q` (which would destroy the uniformity of the repulsion constant `c`, quantified
   *outside* `q`). **Removed.** `zetaHol_norm_le` gives `‖zetaHol s‖ ≤ 3 + 2|Im s|` on the whole
   closed strip — height-free and explicit. The mechanism: take the landed height-free EM
   estimate `norm_zeta_sub_approx_le_strip` at `N = 1`, where the tail term `N^{1−s}/(s−1)` is
   *exactly* the Laurent pole `zetaHol` subtracts, so they cancel and `zetaHol s = 1 + O(‖s‖/σ)`.
   Corollaries: `zetaHol_bound_tall T` (`Z₀ = 3 + 2T`, the drop-in `hZ` shape at any height) and
   `zetaHol_bound_five` (the current height-1 shape with the opaque compactness constant replaced
   by the numeral **5**).
2. **`‖ρ‖ ≤ 2`** in `C2Rho_le` → `‖ρ‖ ≤ 1 + T`. Linear in the height, i.e. `≤ Q`.

Both ride polynomially in `Q`, and the ⟦N0 CLEAR⟧ audit already priced that rescale at **0.095%**
of the clearance (3.28 of 3465 decimal orders).

## What landed (additive, `Salt/SW/TauExt.lean`)

* `zetaHol_norm_le_of_lt`, `zetaHol_norm_le` — the strip bound (open edge; closed edge by
  continuity in the real direction).
* `zetaHol_bound_tall`, `zetaHol_bound_five` — the packaging.
* `repulsionCeiling b c k Q u = 1 − (log(1/u) − log(1/c) − k·log(log Q + 2))/(b·log Q)` — HB's
  `σ₀ = 1 − A·L⁻¹·log η` written in the contract's own letters.
* `repulsion_ceiling_of_contract` — the inversion (contract ⇒ ceiling), one zero.
* `repulsionCeiling_mono` — the ceiling is monotone in the base, so a box-uniform `β` is the
  ceiling at the box **top**, `Q = q(T+2)`.
* `boxZeros_re_le_of_repulsion` — **the `hβ` of `efZeroSumM_spend_at_efHeight`, verbatim.**
* `efZeroSumM_spend_at_repulsion` — the composite: the campaign box's zero sum
  `≤ 4110(log q + 2)⁵ · y^{repulsionCeiling …}`.
* `boxZeros_re_le_unit_box` — the same, fired off the **landed** `dh_repulsion_ordered` at
  `T = 1`. Unconditional. This is the seam test: the artillery's emitted contract shape is
  exactly the shape the inversion consumes, so ⟦TAU-EXT-2⟧ has nothing left to discover there.

Three side hypotheses are carried explicitly because each names a real obligation, not a gap
being hidden: `hord` (the contract's named `T-BAL-UNORDERED` deviation `Re ρ ≤ β₀`); `hreal`
(zeros on the real axis — **the exceptional zero β₀ itself does not satisfy the ceiling and must
be split off first**, exactly as HB (4.11) splits off the `−y^{β₀}/β₀` term of ψ); `hceil` (the
ceiling exceeds the contract's window floor 16/17, so the discarded strip `Re ρ < 16/17` is free).

## ⟦TAU-EXT-2⟧ — the residual, priced

`dh_repulsion_tall`: `dh_repulsion_ordered` with `|Im ρ| ≤ 1` replaced by `|Im ρ| ≤ T`. NOT
landed here because it is **not additive** — it is an edit of existing statements, and this
executor's charter was additive-only (`TBalR8.lean` untouched). The edit is mechanical and fully
enumerated:

1. Height binder `|ρ.im| ≤ 1 ⇝ |ρ.im| ≤ T` in ten statements, in dependency order:
   `norm_zeta_rho_le`, `emrho_perterm` (its `_him` is unused — free), `dhAbel_leg1_rho`
   (`DHExtractRho.lean`), `unmoll_extraction_rho`, `dh_extraction_per_m_rho`,
   `dh_extraction_upper_rho` (`TBalCompose.lean`), `dhAbel_inner_rho` (`TBalFinal.lean`),
   `dh_master_ray`, `dh_repulsion_inst`, `dh_repulsion_ordered` (`TBalR8.lean`).
2. The `hZ` binder's gate `|s.im| ≤ 1 ⇝ |s.im| ≤ T` in the same statements, discharged at the
   call site by `zetaHol_bound_tall` with `Z₀ = 3 + 2T`.
3. `C2Rho_le`: `‖ρ‖ ≤ 2 ⇝ ‖ρ‖ ≤ 1 + T`, and the two constants it emits
   (`hB : 2(9 + 8‖ρ‖) ≤ 50`, `hρσ : ‖ρ‖/σ ≤ 3`) re-priced in `T`. Since `1 + T ≤ Q`, the clean
   move is to charge the whole growth to `Q` and bump the `Q`-exponent of `C2Rho_le`'s conclusion
   from `Q^{1/2}` to `Q^{3/2}`.
4. `dh_repulsion_ordered`'s `c`: the three `Z₀`-carrying numerals `KEβ = 16(328+48Z₀)627⁹`,
   `KEρ = 16(564+72Z₀)627⁹`, `A₀ = log 2 + 4 log(256(82+12Z₀))` take `Z₀ ⇝ 3 + 2T ≤ 3Q`, so the
   thresholds `c ≤ (1/KEβ)⁸`, `c ≤ (c₀/KEρ)⁸`, `c ≤ 1/(Z₀+1)` become `Q`-graded and are absorbed
   by the `Q`-exponent slack (`b = 680` against the `104` actually spent in `row_Eρ_cap` /
   `rho_row_power_bound`).

The only genuine *fights* in that list are (3) and (4) — the `nlinarith` exponent-balance
re-checks of `row_Eρ_cap` and `row_Eβ_cap`. Everything else is binder plumbing. Estimated one
executor wave at Opus tier, plus one refuter on the re-priced numerals (verify-posture law).

## Caveat carried forward

Nothing here reopens ⟦N0 CLEAR⟧'s truncation ruling. The whole design is valid because the
demanded height is **polylog** `(log q)⁴`, not the disc `q²`; at `q²` the `Z₀ = 3 + 2T` growth
would enter as `q²` and the exponent slack would have to be re-audited from scratch. If the
height ruling ever reopens, this file's constants are the first thing to re-price — and N2 would
simultaneously need re-doing as a genuine density theorem (its own recorded caveat).
