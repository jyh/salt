Everything traced. Here is the design page.

---

```
TAU-SHARP — THE CONSTANT-STACK PROVENANCE PAGE
scout: read-only Opus, 2026-08-05, HEAD = bcefe3f (working tree clean w.r.t. Salt/)
target: Salt/SW/TBalTall.lean `dh_repulsion_tall` (:2081), Salt/SW/TauExt.lean
        `repulsionCeiling` (:177), against n4b-design-0805.md §D2 (:205-220)

Legend:  [B] = byte-verified at the cited file:line
         [A] = arithmetic done by this scout from [B] facts (all logs natural;
               recomputed in python, numbers below are exact to 2 dp)

========================================================================
0. THE HEADLINE, FIRST
========================================================================

(i)  §D2's `log(1/c) ≥ 631.6` is CONFIRMED at the bytes [B]+[A], and the arm
     ranking is confirmed: (c₀/KErho)^8 = 631.58, then (1/KEbeta)^8 = 536.67,
     then 2^{-250} = 173.29, then (c₀/32)^{17/3} = 86.23, then
     (1/(8·1610·e))^8 = 83.71, then six arms ≤ 6.9.

(ii) §D2's target "k must go to 0, not merely shrink" is, I believe, ONE STEP
     TOO STRONG, and the correction is the most valuable thing on this page.
     The doc's own numbers prove the law: the recorded binder grade is
     `η ≳ e^{1264+26 log L}` = c²·L^{26}, and 1264 = 2·631.6 = 2·log(1/c),
     26 = 2·13 = 2·(k−1) at k = 14.  So

         the L-power of the regime binder is  (1+ξ)·(k − 1),   ξ = the hN+ margin

     (ξ = 1 is §D2's factor 2).  The door does NOT need k = 0.  **k = 1 makes
     the threshold ABSOLUTE** — η ≤ c^{1+ξ}, no L at all — for any ξ.

(iii) And k = 1 is EXACTLY the structural floor of this skeleton (three
     independent proofs below, §4).  k = 0 is unreachable here, and is
     unreachable in Jutila 1977 Thm 2 as well (his (1.10) carries `1/(8 log D)`
     — k = 1 with constant 8; flags.md:19717 records the statement).  So the
     right TAU-SHARP scope is **k: 14 → 1**, not k → 0, and it closes the N11
     door as stated.

(iv) log(1/c): the honest floor of this SKELETON is ≈ 52 at the present window
     (≈ 36 if the window narrows to 1−1/34), and the first ~545 of the landed
     631.6 come off with TWO stones that change no parameter numeral at all.

========================================================================
1. WHERE THE CONSTANT LIVES (the map)
========================================================================

`c` is a 10-fold `min`, set at TBalTall.lean:2105-2108 [B], projected out by
hc_t1..hc_t10 at :2124-2156 [B], consumed by `dh_repulsion_inst_tall`
(:1673-1691 [B]) which discharges the five row caps' `hg`-hypotheses at
:1978-2014 [B].  The witnesses land at :2162 [B]: `refine ⟨680, c, 14, …⟩`.

The whole engine is ONE lemma: `ray_pow_bound` (TBalR8.lean:368-399 [B]) —

    on the ray  u ≤ c·Q^{-680w}/L₂^{14},   Q^α·u^γ·L₂^ε ≤ c^γ
    provided    γ > 0,  α ≤ 680·w·γ  (hα, :371),  ε ≤ 14·γ  (hε, :371)

Every row is "massage into Q^α u^γ L₂^ε, then apply" (flags.md:11240, catch
R8b-A).  So every constant in the stack is one of:
  (a) the row's leading coefficient K  →  arm `c ≤ (1/(8K))^{1/γ}`;
  (b) the row's u-power γ               →  the EXPONENT of that arm;
  (c) the scale exponents (a,m,g,n) of Y = Q^a u^{-m}, z = Q^g u^{-n};
  (d) b and k, fixed by hα/hε.

========================================================================
2. FACTOR-BY-FACTOR PROVENANCE  (per task: created-where / slack-or-structural /
   what the same skeleton supports)
========================================================================

--- 2.1  THE 8th POWER  (the single biggest slack; ~24× on two arms) --------

CREATED: not by any estimate.  It is a PROOF-CONVENIENCE COLLAPSE.  Each row
proves a bound `K·c^{γ_row}` with its own γ_row, then throws γ_row away:

  Eρ row  TBalTall.lean:1644-1645 [B]
          `hcγ : c ^ (−3 + −9/100 + −(14(1/2−σ))) ≤ c ^ (1/8)`
          via Real.rpow_le_rpow_of_exponent_ge, i.e. it only uses γ ≥ 1/8.
          TRUE γ on the window σ ≥ 16/17:  γ_Eρ ≥ 3.0865  [A]
  Eβ row  TBalR8.lean:816-817 [B]      TRUE γ_Eβ ≥ 2.0865  [A]
  A row   TBalR8.lean:542-543 [B]      TRUE γ_A  ≥ 0.15647 [A]

The arm is then `c ≤ (1/(8K))^{1/γ}` (the `hcollapse` helper, TBalTall:1973
[B]) — with 1/γ read as 8 instead of 1/3.0865 = 0.324.

  VERDICT: SLACK, and it is the dominant one.  flags.md:11245 (catch R8b-C)
  records the reason in the open: "use Real.pow_rpow_inv_natCast when 1/γ is a
  nat-reciprocal" — a *nat* exponent was wanted, so γ was floored to 1/8.

  WHAT THE SAME SKELETON SUPPORTS, unchanged otherwise [A]:
      (c₀/KEρ)^8   631.58  →  log(KEρ/c₀)/3.0865 =  25.58
      (1/KEβ)^8    536.67  →  log(KEβ)/2.0865    =  32.16
      (1/(8·1610e))^8 83.71 → log(8·1610e)/0.15647 = 66.86
  Two of the three arms drop by a factor 20-24.  The A-row barely moves
  (its γ really is ≈ 0.156) — good news: that arm was nearly honest.

--- 2.2  627^9  (the polylog factor) ---------------------------------------

CREATED: `logz_factor_le`, TBalR8.lean:681-709 [B].  At z ≤ 2Q^{12}u^{−3},
    1 + log z² ≤ 3 + 24·log Q + 600·u^{−1/100} ≤ 627·u^{−1/100}·L₂
  627 = 3 + 24 + 600 exactly [B, the three folds e1/e2/e4 at :702,:703,:707]:
      3   = 1 + 2·log 2 rounded up (:698)             — structural, negligible
      24  = 2·g,  g = 12 the z-exponent (:693)        — structural (see 2.5)
      600 = 2·n/δ = 6·100,  n = 3, δ = 1/100 (:700,:706) — SLACK, twice over
Raised to the 9th by `logz_factor_pow9_le` (:712-731 [B]).

  The 9 itself: `sum_gcW_pairkernel_le` (DHExtractW.lean:923-930 [B]) —
  |gcW| ≤ 3^ω (:946) times the exact pair-count 3^ω (:921, `paircount`), so
  9^ω, closed by `tau6W_le` (Sharp.lean:248 [B]): Σ_{d≤L sqfree} k^{ω}/d ≤
  (1+log L)^k.  **The 9 is STRUCTURAL and tau6W_le is essentially sharp** —
  the Euler-product truth is exp(9·Σ_{p≤L}1/p) = e^{9M}(log L)^9, M = 0.2615,
  so at most e^{2.35} sits between the landed bound and the truth [A].  Do not
  hunt here.

  SLACK 1 (class A): `neg_log_le_rpow` (TBalR8:250-254 [B]) is
  `−log u ≤ u^{−δ}/δ`, from mathlib's `Real.log_le_rpow_div`.  The sharp form
  is `u^{−δ}/(e·δ)` (log y ≤ y/e).  Nine factors ⇒ e^9 = 8103, i.e. **−9.0 on
  the numerator of both the Eβ and Eρ arms** [A].
  SLACK 2 (class A): δ = 1/100 is a free knob; the constant is 3+2g+2n/(eδ)
  and the γ-cost is 9δ.  Optimum near δ ≈ 0.015-0.03: 627 → ≈ 137-174 [A],
  another ≈ −4.5 on those numerators.

--- 2.3  THE 636, THE 16, THE 328/568 --------------------------------------

636:  `C2Rho_le_tall`, TBalTall.lean:1450-1467 [B], fold at :1545 [B]:
      102·Q + 54·MQ·Z₀ + 162·MQ + 198·M ≤ 636·B₂ with the four pieces bounded
      by B₂ and the Z₀-piece by 108·B₂ (Z₀ ≤ 2Q, :1541-1544).
      102 + 108 + 162 + 198 = 570 — the docstring says so itself (:1458 [B]:
      "the honest total is 570").  636 is a leftover from the pre-tall count.
      VERDICT: SLACK, but worth only log(636/570) = 0.11 in the numerator.
      Take it while in the file; it is not a stone.
      The 6-term source is `CwRho`/`C2Rho`, TBalFinal.lean:415-426 [B]; the
      Q^{5/2} (was Q^{1/2}) is the tall re-pricing of ‖ρ‖ ≤ Q and Z₀ ≤ 2Q
      (:1451-1457 [B]) — STRUCTURAL to the tall box, and free (§2.6).

16:   TBalTall:2097-2098 [B] KEβ = 16·(328+48·5)·627^9, KEρ = 16·636·627^9.
      16 = 8 × 2 exactly [B, hgEρ at :2006-2014]:
        8 = the row budget 1/8 (five rows must sum < 3/4; the assembly is
            :2057-2062 [B]: 5·(1/8) + 1/4 = 7/8 vs the master's 1 − 1/Y).
            Relaxable to ≈ 3/20: worth log(1.2) = 0.18.  Not a stone.
        2 = the ceil doubling `ceil_dbl` z ≤ 2Q^{12}u^{−3} (:1663, :1797 [B]).
            Removable only by a floor/ceil re-cut; worth 0.69.  Not a stone.

328/568: `row_Eβ_cap` :746-747, :766-767 [B].  328 = 136 + 48 + 144, the three
      M-coefficients of K after folding u ≤ 1; 568 = 328 + 48·Z₀ at Z₀ = 5,
      the β₀-side numeral from `zetaHol_bound_five` (TauExt.lean:162 [B]).
      VERDICT: STRUCTURAL (they are the extraction's own constants).

--- 2.4  THE 250·log 2 ARM  (pure legacy) ----------------------------------

`hc_t1 : c ≤ 2^{−250}` is consumed at EXACTLY ONE site: the trivial branch,
TBalTall.lean:1730-1733 [B], feeding `tbal_tau_le_split` (TBalR8:44-46 [B]).
That lemma is STATED at the literal numeral 2^{−250}, and its proof needs only
`40·c ≤ L₂^{13}` with L₂ ≥ 2 ⇒ L₂^{13} ≥ 8192 (:58-63 [B]) — i.e. **c ≤ 204.8
suffices**.  The 2^{−250} is the freeze's legacy witness (flags.md:11013,
:11080: "the freeze's 2^{−250} was the c₀-independent grade").
  VERDICT: 100% SLACK.  Generalising the lemma to `(hc : c ≤ 1)` deletes an
  arm worth 173.29 [A].  Class A, ~10 lines.

--- 2.5  THE SCALE EXPONENTS  a = 104, m = 14, g = 12, n = 3 ---------------

Set at TBalTall.lean:1776-1777 [B]: z := ⌈Q^{12}u^{−3}⌉, Y := ⌈Q^{104}u^{−14}⌉.

g = 12, n = 3 — **STRUCTURAL**, and I checked the crux:
  `tbal_hcov` (TBalR8:1082-1092 [B]) runs on D = √(z·⌈1/u⌉) ≈ Q^{g/2}u^{−(n+1)/2}.
   * hT1 (:1233-1240 [B]) needs Q^{g/2} ≥ 3400-ish; at the floor Q ≥ 4 this is
     4^6 = 4096 (:1211 [B]).  g < 12 fails at q = 2, |Im ρ| = 0. [A]
   * hkey12 (:1241-1252 [B]) needs u²·D to be u-FREE, i.e. (n+1)/2 = 2, n = 3.
     At n = 1 the bound carries a stray u and dies. [A]
  Do not touch g, n.

m = 14 — SLACK, floor 12.  The only lower constraint is `hY_nat : 2z^4 ≤ Y`
  (TBalTall:1925-1938 [B], hypothesis of `dh_master_ray_tall`, itself forced by
  the extraction's Y/(mk) ≥ 2 with mk ≤ z^4), which needs m ≥ 4n = 12 and
  a ≥ 4g + 3 = 51 (the code spends the surplus as Q^{56}u^{−2} ≥ 32, :1909-1936
  [B]).  m = 12 is admissible.
  m is a TWO-SIDED knob: γ_ρmain = 1 − m·w₀ and γ_A want m SMALL; γ_Eβ, γ_Eρ =
  m(σ−1/2) − … want m LARGE.  Optimum m = 12 (see §3).

a = 104 — SLACK, floor 51.  a does NOT enter the c-arms at all except through
  the A-row's 805 = 1 + a + m/δ_A (TBalR8:475-497 [B]: 805 = 1 + 104 + 14·50,
  exact).  What a DOES set is b (next).

--- 2.6  b = 680  (and the "680 vs 104" framing needs correcting) ----------

b is fixed by hα of `ray_pow_bound` on the ρ-main row alone:
  `rho_row_power_bound` :307-308 [B] — Q^{104w − 680w(1−14w)} ≤ 1 ⟺
  104 ≤ 680(1 − 14w) on w ≤ 1/17, i.e. **b ≥ a/(1 − m·w₀) = 104·17/3 = 589.33** [A].
  So the landed slack is 680/589.33 = **1.154, not 6.5**.  The tau-ext-scope /
  N0-CLEAR line "b = 680 against the 104 actually spent" (TauExt.lean:76 [B],
  flags.md:19727) describes the *Eρ* row (whose α is ≈ −31 with 37 of margin —
  there the slack is real and is what paid for the tall re-pricing,
  TBalTall:1564-1568 [B]) and must NOT be read as slack in b itself.
  VERDICT: b is SLACK only through a and m: b_min = (a + o(1))/(1 − m w₀);
  at (a,m) = (51,12) this is 173.4, i.e. **b: 680 → 174** [A].
  b does not enter log(1/c); it enters the CONSUMER as θ = s·ξ/((1+ξ)·b)
  (§D2's θ ≥ 0.18 is exactly 250·(1/2)/680 [A] — the model checks out), so
  b: 680 → 174 multiplies the road's θ by 3.9.

--- 2.7  k = 14 ------------------------------------------------------------

k is fixed by hε (`ray_pow_bound` :371 [B]): ε ≤ 14γ per row, ε = the row's
L₂-power (1 for ρ-main and A, 10 for Eβ, 11 for Eρ).  With the landed γ's the
worst is 11/3.086 = 3.6, so 14 is not even tight against its own rows [A].
Full treatment in §4.

--- 2.8  c₀ = 1/126848  ----------------------------------------------------

`zero_free_region_all`, ZeroFreeReal.lean:604-605 [B], obtained at
TBalTall:2089 [B], entering through the pole floors 1/‖1−ρ‖, 1/(1−σ) ≤ L₂/c₀
(TBalTall:1893-1896 [B]).  log(1/c₀) = 11.75.
  VERDICT: STRUCTURAL for this wave (a better ZFR constant is its own
  campaign).  But note where it lands: after every stone below, the BINDING
  arm is (c₀/32)^{1/γ₁} and log(1/c₀) is 11.75 of its 15.22 numerator.  c₀ is
  the floor under the floor.

========================================================================
3. (1) THE HONEST FLOOR THIS PROOF STRUCTURE SUPPORTS
========================================================================

All numbers [A], from the [B] facts above; each entry is
max over the five row arms + the four guard arms.

  state                                        log(1/c)      b       k
  ------------------------------------------------------------------------
  LANDED (TBalTall:2105-2108)                    631.58     680      14
  + S1 (kill 2^{-250}) + S2 (γ-honest arms)       86.23     680      14
      binding arm: (c₀/32)^{17/3}, the ρ-main/ZFR row
  + S3 (a,m,b) = (51,12,174)                      55.71     174      14
  + S5 (sharp neg_log, δ ≈ 0.02)                  51.74     174      14
      binding arm: (c₀/32)^{17/5}  = (17/5)·log(32/c₀)
  + S4 (k → 1)                                    51.74     174       1
  + S7 (window 16/17 → 1−1/34, consumer-gated)    36.41      79       1

  THE FLOOR OF THE SKELETON:  log(1/c) ≈ 52  at the present window,
                              ≈ 36  at a 1/34 window.
  It cannot go below ≈ 40 (resp. ≈ 18) without a better c₀, because the
  binding arm is (17/5)·log(32/c₀) and log(1/c₀) = 11.75 of that.

  THE FLOOR OF k:  k = 1  EXACTLY (§4).  Not 0.
  THE FLOOR OF b:  b = (a + δ'm)/(1 − m w₀) ≈ 174 at (a,m,w₀)=(51,12,1/17).

  Consumer read (using §D2's own law, verified against its own numbers):
      binder   η ≤ c^{1+ξ}·L^{(1+ξ)(k−1)}
      landed   e^{−1264}·L^{−26}          (ξ=1, k=14, log(1/c)=631.6)  ← §D2
      after    e^{−104}                   (ξ=1, k=1,  log(1/c)=52)  ABSOLUTE
      θ        s·ξ/((1+ξ)b):  0.18 → 0.72 at ξ=1, s=250, b=174

========================================================================
4. (3) IS AN ABSOLUTE THRESHOLD REACHABLE IN THIS SKELETON?
========================================================================

YES — and it needs k = 1, which is reachable; k = 0 is NOT reachable, and it
is not needed.

WHY k ≥ 1 IS STRUCTURAL (three independent walls, all [B]-grounded):

 (W1) The trivial-branch split.  `tbal_tau_le_split` must give τ ≤ 1/(40 L₂)
      (TBalTall:1725-1733 [B]).  With τ = c·Q^{−bw}/L₂^k and w ≥ c₀/log Q (the
      ZFR floor, :1882 [B]), Q^{−bw} ≥ e^{−b c₀} = a CONSTANT (b c₀ = 0.0054
      at the landed values [A]).  So τ ≥ c·e^{−bc₀}/L₂^k, and τ ≤ 1/(40L₂)
      uniformly in Q forces k ≥ 1.
 (W2) The residue row's ZFR pole.  `row_rho_main_cap` (TBalR8:598-676 [B])
      spends 1/‖1−ρ‖ ≤ L₂/c₀ — one genuine log Q, and the worst case is
      exactly the ZFR boundary w = c₀/log Q where sup(Q^{−bw}/w) = (L/c₀)e^{−bc₀}.
      That log Q can only be paid by the contract's own L₂^{−k}.
 (W3) hε: ε = 1 ≤ k·γ_ρmain with γ_ρmain = 1 − m w₀ < 1 forces k > 1 naively;
      the SHORTFALL is 1 − γ = m·w, which is ∝ w and therefore convertible
      into a Q-power (L₂ ≤ (1/δ'+2)Q^{δ'}, matched by the ray's b·w·γ), so
      k = 1 exactly suffices.  At k < 1 the shortfall acquires a CONSTANT term
      γ_a(1−k) that is not ∝ w, and hα fails for small w — this is precisely
      catch R8b-B, flags.md:11257-11259 [B].

WHY k = 1 IS ENOUGH FOR THE OTHER FOUR ROWS:
  * Eβ (ε=10) and Eρ (ε=11): their α carries a large NEGATIVE constant
    (α_Eρ = 5/2 + 12 + 104(1/2−σ) ≤ −31.4 on the window [A], TBalTall:1600 [B]),
    so 10δ'/11δ' of Q-exponent is free: convert L₂^{10}, L₂^{11} to Q-powers at
    cost (1/δ'+2)^{11} — at δ' = 1/2 that is 4^{11}, worth +4.9 on that arm [A].
    Their ε then imposes NOTHING on k.
  * A-row (ε=1): split `log Y ≤ log 2 + a·log Q + m·log(1/u)`
    (TBalR8:478-481 [B]) into its two pieces instead of folding them into one
    u^{−δ_A}L₂ product (:485-496 [B]).  Piece 1 (a·log Q) has ε=1, γ = 1 − m(w−u):
    same shortfall-∝-w situation as W3, fine at k=1.  Piece 2 (m·log(1/u)) has
    ε = 0 — no L₂ at all.  The δ_A that currently pollutes γ_A disappears.
  * 1/x row: ε = 0 already (TBalR8:426 [B]).
  * Guards: `huL2g : u·L₂ ≤ 1/18` (TBalTall:1769 [B]) is presently derived from
    u·L₂^{14} ≤ c (:1747-1754 [B]).  At k=1 it comes from the ray directly; and
    in any case **the deep branch already has htriv : u < 1/(40 L₂)** (:1735 [B])
    which gives it for free — hc_t9 (c ≤ 1/18) is redundant TODAY.

WHY NOT k = 0: W1 and W2 both break irreparably.  The only k=0 restatement is
the disjunctive `1−β₀ ≥ min(1/(40L₂), c·Q^{−b(1−σ)})`, which merely moves the
log into the other branch.

WHY THE DOOR DOESN'T NEED k = 0: the binder's L-power is (1+ξ)(k−1), because
log(1/u) = log(1/η) + log L already carries one log L against k·log(log Q + 2)
≈ k·log L (log Q ≈ L at the campaign box, TauExt:315 [B] Q = q(efHeight q + 4),
efHeight q = (log q + 2)^4; and ≈ L + 6 log L at D4's Y₁ — either way log log Q
≈ log L).  §D2's own recorded numbers confirm the law exactly: 26 = 2(14−1).

A DIFFERENT ROUTE IS NOT INDICATED.  Jutila 1977 Thm 2 (1.10) — the natural
alternative, staged at docs/sources/jutila1977-notes.md, crosswalked at
flags.md:19717 [B] — is `δ₁ ≥ (1−6δ)·D^{−(2+ε)δ/(1−6δ)}/(8 log D)`: k = 1 with
constant 8 and b ≈ 3.09 at δ = 1/17.  I.e. Jutila is (k=1, b=3.09, c=1/8·(1−6δ))
against our post-TAU-SHARP (k=1, b=174, c=e^{−52}).  **Same k.**  Jutila buys b
and c, not k — and pays with an ineffective D₀(ε) that our contract does not
have.  So: take k = 1 in-house; keep N2-DENSITY/Jutila as the b-and-c play, not
the k play.

========================================================================
5. (2) THE TIGHTENING STONES
========================================================================

Each: what re-derives / class / gain in log(1/c) / files touched.

 S1  RETIRE THE 2^{−250} ARM.                                     class A
     Restate `tbal_tau_le_split` (TBalR8:44-46) with hypothesis `hc : c ≤ 1`
     (its proof already only needs 40c ≤ 8192, :71-82).  Delete hc_t1
     (TBalTall:1684, :2109, :2124) and the :1730-1733 block's numeral.
     GAIN: removes an arm at 173.29.  ~15 ln.  No statement outside TBalR8/Tall.

 S2  THE γ-HONEST ARMS (THE BIG ONE).                             class B
     In each of the three `rpow_le_rpow_of_exponent_ge … (1/8)` steps
     (TBalTall:1644-1645; TBalR8:816-817, :542-543) replace 1/8 by the row's
     own γ-floor (3.0865 / 2.0865 / 0.15647), restate the row's `hg` as
     `K·c^{γ₀} ≤ 1/8`, and change the corresponding `c`-arm to
     `c ≤ (1/(8K))^{1/γ₀}` — `hcollapse` (TBalTall:1973) already takes an
     arbitrary rational pinv, so the assembly needs only new `pinv` numerals.
     GAIN: 631.58 → 86.23 (the two 8th-power arms fall to 25.58 and 32.16;
     the A-arm to 66.86).  ~80 ln, no new mathematics.
     RISK: the γ-floors are σ-dependent; each needs the same
     `nlinarith [hσlo]` window check the code already performs.

 S3  THE SCALE RE-CUT (a, m, b) : (104, 14, 680) → (51, 12, 174). class B/C
     Touches the numerals in `rho_row_power_bound`, `ray_pow_bound`(680),
     `row_1x_cap`, `row_A_cap`, `row_rho_main_cap`, `row_Eβ_cap`,
     `row_Eρ_cap(_tall)`, `dh_repulsion_inst(_tall)`, and the two contracts —
     mechanical but wide (~12 statements).  Re-checks needed:
       2z^4 ≤ Y at (51,12,12,3): 32 ≤ Q^3, true at Q ≥ 4 [A]
       α_Eρ = 5/2+12+51(1/2−σ) ≤ −8 on the window [A]
       hα: 51 ≤ 174(1 − 12w) on w ≤ 1/17 [A]
       805 → 1 + 51 + 12/δ_A
     GAIN: 86.23 → 55.71, and b: 680 → 174 (θ ×3.9).
     NOTE the trade: m ↓ helps the ρ-main/A arms, hurts Eβ/Eρ; m = 12 is the
     optimum and is also the floor forced by 2z^4 ≤ Y.

 S4  k : 14 → 1  (THE DOOR STONE).                                class B/C
     Four moves, all named in §4: (i) the A-row log Y piece-split;
     (ii) the ρ-main / A-row shortfall conversion L₂^{mw} ≤ (1/δ'+2)^{mw}Q^{δ'mw};
     (iii) the Eβ/Eρ L₂^{10}, L₂^{11} → Q^{10δ'}, Q^{11δ'} conversion;
     (iv) the trivial branch at c ≤ 1/40.
     `ray_pow_bound` needs a companion admitting a w-proportional L₂ residue
     (α ≤ bwγ with α already carrying δ'·(ε − kγ)).
     GAIN in log(1/c): +5 (the δ' constants) — this stone COSTS a little.
     GAIN at the door: the binder's L-power (1+ξ)(k−1) → 0.  ABSOLUTE.

 S5  SHARPEN THE CRUDE-δ + TUNE δ.                                class A
     `neg_log_le_rpow` (TBalR8:250-254): `−log u ≤ u^{−δ}/(e·δ)`, two lines
     from `log y ≤ y/e`.  Then re-tune δ = 1/100 → ≈ 1/50 in `logz_factor_le`
     (627 → ≈ 137) and δ_A in row_A_cap.
     GAIN: −9.0 then −4.5 on the Eβ/Eρ numerators; 55.71 → 51.74 after S3.

 S6  636 → 570.                                                   class A
     `C2Rho_le_tall`:1545 already proves 570; the docstring says so (:1458).
     GAIN: 0.11/γ.  Cosmetic — bundle into whichever wave opens the file.

 S7  THE WINDOW 16/17 → 1 − 1/34.                        class B, CONSUMER-GATED
     Every γ improves (γ_ρmain 5/17 → 0.647).  GAIN: 51.74 → 36.41, b → 79.
     COST: the contract's window numeral appears in the statement
     (TBalTall:2086) and in the consumer's `hceil` (TauExt:262,:269,:283,:316),
     which must then hold at 1−1/34 rather than 16/17.  DO NOT fire without
     the road's ruling.

 S8  A BETTER c₀.                                     class C/D — NOT this wave
     After S1-S5 the binding arm is (17/5)·log(32/c₀) and log(1/c₀) = 11.75 of
     its 15.22.  c₀ = 1/1000 would give 51.74 → 35.3 [A].  Separate campaign.

 NOT STONES (verified, do not spend on these):
   * the 9 in (1+log z²)^9 — sharp within e^{2.35} (§2.2)
   * g = 12, n = 3 — structural in `tbal_hcov` (§2.5)
   * the 328/568/136/48/144 — the extraction's own constants
   * the 1/8 row budget → 3/20 — worth 0.18
   * the ceil doubling 2 — worth 0.69

========================================================================
6. (4) THE RECOMMENDED TAU-SHARP WAVE PLAN
========================================================================

Design ruling to bank first (Fable, before any executor):
   **TAU-SHARP's target is (k, b, log(1/c)) = (1, ~174, ~52), NOT k = 0.**
   The N11 door closes at k = 1 because the binder's L-power is (1+ξ)(k−1).
   Re-scope §D2:215 accordingly and correct §D2:212's "the KErho arm is the
   target" — after S2 the KErho arm is 25.6 and the BINDING arm is the ZFR
   residue row (c₀/32)^{1/γ}.

Wave TS-0 (scout+refuter, 0 Lean):  put §4's k=1 argument and §3's arm table
   through one refuter pass with these kill-checks:
     K1  does htriv really survive every use of the ray in the deep branch?
     K2  is the shortfall-∝-w conversion legitimate at ALL w ∈ (c₀/log Q, 1/17]?
     K3  does the consumer's Range-A ledger really carry L^{(1+ξ)(k−1)} and
         nothing else? (this is a ROAD-side check, and it is the one that
         decides whether the whole wave is worth firing)
     K4  the γ-floors: is γ_Eρ ≥ 3.0865 uniform in σ on [16/17,1)?

Wave TS-1 (one Opus executor, additive, ~120 ln):  S1 + S5 + S6.
   All class A, all inside TBalR8/TBalTall, no statement outside the two files.
   Lands `tbal_tau_le_split'`, the sharpened `neg_log_le_rpow'`,
   `logz_factor_le'` at the tuned δ, `C2Rho_le_tall` at 570.
   Exit test: `dh_repulsion_tall` still builds with the same witnesses.

Wave TS-2 (one Opus executor, ~120 ln):  S2 alone.
   The three γ-honest arms + the four new `c`-min numerals.
   Exit test: `#print axioms dh_repulsion_tall` = 3 axioms; and a new
   `dh_repulsion_tall_grade : log(1/c) ≤ 90`-style ledger comment recording
   the arm table so the next wave cannot lose it.
   AFTER TS-2 the honest grade is 86.2 with NO parameter changed — this alone
   takes §D2's e^{1264} to e^{172}.

Wave TS-3 (Fable design block + one executor, ~300 ln):  S3 + S4 together.
   They must go together: S4's shortfall conversion changes hα, and S3 changes
   b, so the two hα re-checks are the same re-check.  This is the wave that
   produces the door: (b, c, k) = (174, e^{−52}, 1).
   Deliverable statement (drop-in for TauExt/N4 — the consumer shape is
   UNCHANGED, only the witnesses move):
     dh_repulsion_tall : ∃ b c k, … with k = 1
   and TauExt.lean:177's `repulsionCeiling` needs no edit at all.

Wave TS-4 (gated): S7, only on the road's ruling about `hceil`.

Sequencing note: TS-1 and TS-2 are independent and could run in parallel, but
they touch the same `c`-min block (TBalTall:2105-2156) — run them sequentially,
TS-1 first (it deletes an arm, which shortens TS-2's min-tower projections).

WHAT I DID NOT VERIFY (honest gaps in this page):
  * The road-side claim K3 (the Range-A ledger's L-power).  I derived
    (1+ξ)(k−1) from §D2's own two recorded numbers (1264 = 2·631.6 and
    26 = 2·13) and from the ceiling's algebra (TauExt:177-178), NOT from the
    consumer's Lean text — no consumer exists yet.  If the road's ledger has
    an additional L^5-type polylog prefactor (efZeroSumM_spend_at_repulsion's
    4110·(log q + 2)^5, TauExt:320 [B]), that prefactor is k-independent and
    survives every stone here; it is the road's problem, not the artillery's.
  * §D2:216's "hN+ ∧ hηq is empty below q ≈ e^{250}" — I did not re-derive it;
    after TS-3 the corresponding floor should drop by the same factor as
    log(1/c) and should be re-stated in the same commit.
```

Key corrections for the record: (a) the 631.6 is confirmed, but ~545 of it is a **proof-convenience collapse** (three `c^γ ≤ c^{1/8}` steps that throw away γ ≈ 3.09/2.09) plus a legacy `2^{-250}` arm used at one site that needs only `c ≤ 1`; (b) the "680 vs 104 slack" is really 680 vs **589.3** — b is 15% slack, not 550%, and it is `a`, not `b`, that carries the slack; (c) **k = 0 is not needed** — the binder's L-power is `(1+ξ)(k−1)` (confirmed against §D2's own 26 = 2·13), so k = 1 is absolute, and k = 1 is exactly the skeleton's structural floor (three walls: the trivial-branch split, the residue row's ZFR pole, and the hα shortfall law of catch R8b-B).
