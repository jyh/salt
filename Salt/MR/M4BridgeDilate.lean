/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Dyadic
import Salt.MR.M4Sieve
import Salt.MR.M4BridgeResidue

/-!
# ⟦BRIDGE 3⟧ — the `d₀`-dilation transport into the door window (`M4BridgeDilate`)

Source: `M4Close`'s module header, ⟦THE FIVE OPEN BRIDGES⟧ item 3 — "`M4Residue.
residue_split_dilate_door` + `M4Dyadic.sum_window_dilate` are landed; the bridge is the door
window's image under `n ↦ n/d₀` and the trivial branch below `trivThresh H d₀ W` as a case
split"; the campaign freeze `docs/exploration/s9-freeze-0726.md` ⟦AMENDMENT B⟧ row `M4-5`
(:280), whose trivial branch is "below `H·d₀/W³`".

MRT §4 step (b)+(c) at the DOOR's own carrier.  The door window is `Finset.Ioc n (n+H)`
(`M4Window.absWindowSum`, half-open — `{n+1,…,n+H}`); the residue split fixes a class `r`
mod `q`, sets `d₀ := (r,q)`, and re-indexes `m = d₀·k`.  What this file lands is the
transport of that re-indexing *into the door's own window shape*, so that the dilated object
is again an `absWindowSum` — at the dilated base `n/d₀`, the dilated length `dilLen H n d₀`,
and the DILATED FREQUENCY `d₀·α`.

## ⟦THE HEADLINE⟧ (`classWindowSum_dilate`)

```
   ∑_{n<m≤n+H, m ≡ r (q)} a(m) e(αm)
     =  ∑_{n/d₀ < k ≤ (n+H)/d₀} [k ≡ r₀ (q₀)]·a(d₀k)·e((d₀α)k)
     =  absWindowSum (dilCoeff a d₀ q₀ r₀) (dilLen H n d₀) (n/d₀) (d₀·α)
```

with `q₀ = q/d₀`, `r₀ = r/d₀` COPRIME (`M4Residue.coprime_reduced_of_gcd`), the class test
transported by `M4Residue.modEq_dilate_iff`, and the re-indexing itself
`M4Residue.sum_reindex_dilate` — CITED, never re-proved.  No hypothesis on `a`: the
identity is a change of variables, not an estimate.

## ⟦THE ENDPOINTS ARE THE CONTENT⟧ (§1)

The two ℕ-divisions `n/d₀` and `(n+H)/d₀` round INDEPENDENTLY, so the dilated length is
`dilLen H n d₀ = (n+H)/d₀ − n/d₀` and NOT `H/d₀`.  Both sides are derived, never waved:

```
      H/d₀  ≤  dilLen H n d₀  ≤  H/d₀ + 1        (ℕ, §1: `le_dilLen`, `dilLen_le`)
   (H:ℝ)/d₀ − 1 ≤ dilLen H n d₀ ≤ (H:ℝ)/d₀ + 1   (ℝ, §1: the two casts)
      dilLen H n d₀ ≤ H                          (§1, via the `k ↦ d₀k` injection)
```

The MEMBERSHIP correspondence, by contrast, is EXACT — no `±1` anywhere: `n/d₀ < k` iff
`n < d₀k` (`Nat.div_lt_iff_lt_mul`) and `k ≤ (n+H)/d₀` iff `d₀k ≤ n+H`
(`Nat.le_div_iff_mul_le`).  The slack lives in the *length*, and only there.

## ⟦THE λ-LEG⟧ (§5) — no coprimality, and the gate is a hypothesis

`liouvilleC_mul` factors `λ(d₀k) = λ(d₀)λ(k)` at NO coprimality (complete multiplicativity),
and `memS_dilate_door` transfers the block indicator on the nose under the door gate
`d₀ ≤ q ≤ (log H)^{12} < P₁` (`M4Residue` §5 — STRICT, and carried as a hypothesis at every
statement that uses it).  Together: `dilCoeff (1_𝒮·λ) d₀ q₀ r₀ = λ(d₀)·(1_𝒮·λ restricted to
the class)`, so the dilation is invisible to the modulus (`‖λ(d₀)‖ = 1`).

## ⟦THE DILATED FREQUENCY⟧ (§7) — where `q` and `d₀` meet

`e(α·d₀k) = e((d₀α)·k)`: the transported sum is a window sum at the frequency `d₀α`, and its
major-arc status must be re-read at the DILATED window.  The honest bookkeeping
(`nearRatTight_dilate`): if `α` is `(Q,H)`-tight-major with witness `a/q'`, then `d₀α` is
tight-major at the dilated window `H₀` with witness denominator `q'/(d₀,q')` and cap

```
      Q · (H + d₀)/H       (NOT `Q`, and NOT `arcDen 12 (dilLen H n d₀)`)
```

The cap moves UP by `1 + d₀/H` while the dilated window's own `arcDen 12 (dilLen H n d₀)`
moves DOWN (`arcDen_dilLen_le`): the transport does not preserve the arc datum on the nose,
and `arcDen_le_dilate_cap` states the resulting one-way comparison exactly.  At door scales
`d₀ ≤ q ≤ W = (log H)^{12}`, so the factor is `≤ 1 + (log H)^{12}/H` — but it is carried
SYMBOLICALLY here and never evaluated.

## ⟦THE TRIVIAL BRANCH⟧ (§6) — a case split, not a threshold choice

The freeze's M4-5 branch (`trivThresh H d₀ W = H·d₀/W³`, `M4Dyadic` §6) is consumed as a
DICHOTOMY (`classWindow_trivial_or_long`): either the dilated window is below the threshold
and `M4Dyadic.norm_absWindowSum_le_thresh` closes the class outright (through the `±1` of
§1 — the `+1` is why the branch is stated at `H/d₀ + 1 ≤ thr`), or it is not and the
transport identity hands the class to the analytic road.  The threshold is a parameter: this
file never evaluates `trivThresh`.

## ⟦SEAM A⟧ — the plug into ⟦BRIDGE 1⟧ (§9)

`M4BridgeResidue.norm_absWindowSum_split_coprime_add` cuts the class sum into its coprime
and non-coprime halves and names the second as this bridge's.  §9 makes the plug literal:
`classPhaseSum` (⟦BRIDGE 1⟧'s carrier) is `classWindowSum` on the nose, so the transport
fires on it unchanged, and `norm_absWindowSum_split_dilate_trivial` discharges the whole
non-coprime half against the DILATED window's length (`d₀ = (r,q) > 1` there).

## Conventions

* **Four log scales** (M4-8's pin): this file speaks `H` only.  `W = (log H)^{12}`
  enters exclusively through `M4Residue`'s door gate hypothesis `(q:ℝ) ≤ (log H)^{12}`; no
  `log X`, no `log x`, no `log ω` appears.
* **Half-open, everywhere**: `Ioc n (n+H)`, matching `absWindowSum` and `logMeasure`'s own
  `Ioc (x/ω) x`.
* **`d₀ = (r,q)` is never assumed nonzero** — it is DERIVED from `0 < q`
  (`Nat.gcd_pos_of_pos_right`), which is the only positivity hypothesis the transport needs.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE ENDPOINT BOOKKEEPING (ℕ-division, both sides derived)

The door window `(n, n+H]` maps to `(n/d, (n+H)/d]` under `m ↦ m/d`.  The two divisions
round independently, so the dilated length is a *difference of floors*: `H/d ± 1`, and this
section derives both signs. -/

/-- **The dilated window's length**: `(n+H)/d − n/d`.  NOT `H/d` — see §1's two-sided
bound.  (`d = 0` is admissible as a formal input; every statement below carries `0 < d`.) -/
def dilLen (H n d : ℕ) : ℕ := (n + H) / d - n / d

/-- Floors add downward: `⌊n/d⌋ + ⌊H/d⌋ ≤ ⌊(n+H)/d⌋`. -/
theorem div_add_div_le_add_div (n H : ℕ) {d : ℕ} (hd : 0 < d) :
    n / d + H / d ≤ (n + H) / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have h1 := Nat.div_mul_le_self n d
  have h2 := Nat.div_mul_le_self H d
  have hexp : (n / d + H / d) * d = n / d * d + H / d * d := by ring
  omega

/-- …and they lose at most one unit: `⌊(n+H)/d⌋ ≤ ⌊n/d⌋ + ⌊H/d⌋ + 1`.  The `+1` is the two
residues meeting (`Nat.add_div`'s carry bit), and it is the whole `±1` of this file. -/
theorem add_div_le_div_add_div_succ (n H : ℕ) {d : ℕ} (hd : 0 < d) :
    (n + H) / d ≤ n / d + H / d + 1 := by
  rw [Nat.add_div hd]
  split <;> omega

/-- **The lower endpoint bound**: `H/d ≤ dilLen H n d` (ℕ-division on both sides). -/
theorem le_dilLen (H n : ℕ) {d : ℕ} (hd : 0 < d) : H / d ≤ dilLen H n d := by
  have h : H / d + n / d ≤ (n + H) / d := by
    rw [Nat.add_comm (H / d)]
    exact div_add_div_le_add_div n H hd
  exact Nat.le_sub_of_add_le h

/-- **The upper endpoint bound**: `dilLen H n d ≤ H/d + 1`. -/
theorem dilLen_le (H n : ℕ) {d : ℕ} (hd : 0 < d) : dilLen H n d ≤ H / d + 1 := by
  unfold dilLen
  refine Nat.sub_le_iff_le_add.mpr ?_
  calc (n + H) / d ≤ n / d + H / d + 1 := add_div_le_div_add_div_succ n H hd
    _ = H / d + 1 + n / d := by ring

/-- The dilated window, rebased: `(n/d, (n+H)/d] = (n/d, n/d + dilLen H n d]` — the shape
`absWindowSum` reads (`Ioc n₀ (n₀ + H₀)`). -/
theorem Ioc_dilate_eq (H n : ℕ) {d : ℕ} :
    Finset.Ioc (n / d) ((n + H) / d) = Finset.Ioc (n / d) (n / d + dilLen H n d) := by
  have hkey : n / d + dilLen H n d = (n + H) / d :=
    Nat.add_sub_cancel' (Nat.div_le_div_right (Nat.le_add_right n H))
  rw [hkey]

/-- **THE EXACT MEMBERSHIP CORRESPONDENCE** (no `±1`): `k` in the dilated window implies
`d·k` in the door window.  Both endpoints transport exactly — `Nat.div_lt_iff_lt_mul` at the
open end, `Nat.le_div_iff_mul_le` at the closed end. -/
theorem Ioc_dilate_maps {H n d : ℕ} (hd : 0 < d) {k : ℕ}
    (hk : k ∈ Finset.Ioc (n / d) ((n + H) / d)) : d * k ∈ Finset.Ioc n (n + H) := by
  rw [Finset.mem_Ioc] at hk ⊢
  refine ⟨?_, ?_⟩
  · have h := (Nat.div_lt_iff_lt_mul hd).mp hk.1
    rwa [Nat.mul_comm] at h
  · have h := (Nat.le_div_iff_mul_le hd).mp hk.2
    rwa [Nat.mul_comm] at h

/-- **The dilated window never grows**: `dilLen H n d ≤ H` for `d ≥ 1`, proved by the
`k ↦ d·k` injection into the door window (so it is exact at `d = 1`, where the two windows
coincide, and the `H/d + 1` bound of `dilLen_le` would be off by one). -/
theorem dilLen_le_window (H n : ℕ) {d : ℕ} (hd : 0 < d) : dilLen H n d ≤ H := by
  have hcard : (Finset.Ioc (n / d) ((n + H) / d)).card ≤ (Finset.Ioc n (n + H)).card := by
    refine Finset.card_le_card_of_injOn (fun k => d * k) (fun k hk => Ioc_dilate_maps hd hk) ?_
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hd hxy
  rw [Nat.card_Ioc, Nat.card_Ioc] at hcard
  simpa [dilLen] using hcard

/-- **The endpoint bound, ℝ-side (upper)**: `dilLen H n d ≤ (H:ℝ)/d + 1`.  This is the form
the trivial branch consumes. -/
theorem dilLen_le_real (H n : ℕ) {d : ℕ} (hd : 0 < d) :
    (dilLen H n d : ℝ) ≤ (H : ℝ) / (d : ℝ) + 1 := by
  have h : (dilLen H n d : ℝ) ≤ ((H / d : ℕ) : ℝ) + 1 := by
    exact_mod_cast dilLen_le H n hd
  have hcast : ((H / d : ℕ) : ℝ) ≤ (H : ℝ) / (d : ℝ) := Nat.cast_div_le
  linarith

/-- **The endpoint bound, ℝ-side (lower)**: `(H:ℝ)/d − 1 ≤ dilLen H n d`.  Together with
`dilLen_le_real` this is the freeze's "`H/d₀ ± 1`", with both signs derived. -/
theorem le_dilLen_real (H n : ℕ) {d : ℕ} (hd : 0 < d) :
    (H : ℝ) / (d : ℝ) - 1 ≤ (dilLen H n d : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcast : ((H / d : ℕ) : ℝ) ≤ (dilLen H n d : ℝ) := by exact_mod_cast le_dilLen H n hd
  have hdm : (H : ℝ) = (d : ℝ) * ((H / d : ℕ) : ℝ) + ((H % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod H d).symm
  have hlt : ((H % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt H hd
  have hmul : (d : ℝ) * ((H / d : ℕ) : ℝ) ≤ (d : ℝ) * (dilLen H n d : ℝ) :=
    mul_le_mul_of_nonneg_left hcast hd0.le
  rw [sub_le_iff_le_add, div_le_iff₀ hd0]
  nlinarith

/-- **The length gate the frequency transport consumes**: `d·dilLen H n d ≤ H + d`.  (The
`+d` is `d` times the `+1` of `dilLen_le`.) -/
theorem d_mul_dilLen_le (H n : ℕ) {d : ℕ} (hd : 0 < d) : d * dilLen H n d ≤ H + d := by
  have h2 := Nat.div_mul_le_self H d
  calc d * dilLen H n d ≤ d * (H / d + 1) := Nat.mul_le_mul_left d (dilLen_le H n hd)
    _ = H / d * d + d := by ring
    _ ≤ H + d := by omega

/-! ## §2 — THE WINDOW'S IMAGE UNDER `m ↦ m/d₀`

The set identity behind the transport: the class-restricted door window, divided by
`d₀ = (r,q)`, is the dilated window restricted to the reduced class `r₀ mod q₀`.  Both
inclusions are the exact endpoint correspondences of §1 plus `M4Residue.modEq_dilate_iff`. -/

/-- **THE IMAGE OF THE CLASS-RESTRICTED DOOR WINDOW.**

```
   {n < m ≤ n+H : m ≡ r (q)} / d₀  =  {n/d₀ < k ≤ (n+H)/d₀ : k ≡ r₀ (q₀)}
```

with `d₀ = (r,q)`, `r₀ = r/d₀`, `q₀ = q/d₀`.  Every `m` in the class is divisible by `d₀`
(`M4Residue.gcd_dvd_of_modEq`), which is what makes the division lossless. -/
theorem image_div_class_window {q : ℕ} (hq : 0 < q) (r H n : ℕ) :
    ((Finset.Ioc n (n + H)).filter (fun m => m ≡ r [MOD q])).image
        (fun m => m / Nat.gcd r q)
      = (Finset.Ioc (n / Nat.gcd r q) ((n + H) / Nat.gcd r q)).filter
          (fun k => k ≡ r / Nat.gcd r q [MOD q / Nat.gcd r q]) := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  ext k
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨m, ⟨⟨hlo, hhi⟩, hmod⟩, rfl⟩
    have hdvd : Nat.gcd r q ∣ m := gcd_dvd_of_modEq hmod
    have hm : Nat.gcd r q * (m / Nat.gcd r q) = m := Nat.mul_div_cancel' hdvd
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (Nat.div_lt_iff_lt_mul hd).mpr ?_
      rw [Nat.mul_comm, hm]
      exact hlo
    · refine (Nat.le_div_iff_mul_le hd).mpr ?_
      rw [Nat.mul_comm, hm]
      exact hhi
    · refine (modEq_dilate_iff hq).mp ?_
      rw [hm]
      exact hmod
  · rintro ⟨⟨hlo, hhi⟩, hmod⟩
    refine ⟨Nat.gcd r q * k, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · have h := (Nat.div_lt_iff_lt_mul hd).mp hlo
      rwa [Nat.mul_comm] at h
    · have h := (Nat.le_div_iff_mul_le hd).mp hhi
      rwa [Nat.mul_comm] at h
    · exact (modEq_dilate_iff hq).mpr hmod
    · exact Nat.mul_div_cancel_left k hd

/-! ## §3 — THE DILATED FREQUENCY, pointwise

`e(α·(d k)) = e((dα)·k)`: the dilation is absorbed into the frequency.  This is the single
place the phase is touched; §7 reads off what it costs on the arc side. -/

/-- **The phase transport**: `e(α·(d k)) = e((d·α)·k)`.  Pure `ℕ → ℂ` cast algebra. -/
theorem exp_phase_dilate (α : ℝ) (d k : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((d * k : ℕ) : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((d : ℝ) * α : ℝ) : ℂ)
          * ((k : ℕ) : ℂ)) := by
  congr 1
  push_cast
  ring

/-! ## §4 — THE TRANSPORT

The class-restricted door-window sum, its coefficient-side spellings, and the headline
identity. -/

/-- **The class-restricted coefficient sequence** `1_{· ≡ r (q)}·a`. -/
def classCoeff (a : ℕ → ℂ) (q r : ℕ) : ℕ → ℂ :=
  fun m => if m ≡ r [MOD q] then a m else 0

/-- **The dilated coefficient sequence** `k ↦ 1_{k ≡ r₀ (q₀)}·a(d·k)` — the datum the
transported window sum carries. -/
def dilCoeff (a : ℕ → ℂ) (d q₀ r₀ : ℕ) : ℕ → ℂ :=
  fun k => if k ≡ r₀ [MOD q₀] then a (d * k) else 0

/-- **The class-restricted door-window sum**: `∑_{n<m≤n+H, m ≡ r (q)} a(m) e(αm)`.  This is
the object the residue split (⟦BRIDGE 1⟧) produces, one per class. -/
def classWindowSum (a : ℕ → ℂ) (H n q r : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ (Finset.Ioc n (n + H)).filter (fun m => m ≡ r [MOD q]),
    a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ))

/-- Both restrictions are 1-bounded when `a` is (the indicator only deletes terms). -/
theorem norm_classCoeff_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (q r m : ℕ) :
    ‖classCoeff a q r m‖ ≤ 1 := by
  unfold classCoeff
  split_ifs
  · exact ha m
  · simp

theorem norm_dilCoeff_le_one {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (d q₀ r₀ k : ℕ) :
    ‖dilCoeff a d q₀ r₀ k‖ ≤ 1 := by
  unfold dilCoeff
  split_ifs
  · exact ha _
  · simp

/-- The class-restricted window sum IS an `absWindowSum` at the restricted datum — the
spelling `M4Window`'s trivial bound and `M4Door`'s glue both read. -/
theorem classWindowSum_eq_absWindowSum (a : ℕ → ℂ) (H n q r : ℕ) (α : ℝ) :
    classWindowSum a H n q r α = absWindowSum (classCoeff a q r) H n α := by
  unfold classWindowSum absWindowSum classCoeff
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs
  · rfl
  · rw [zero_mul]

/-- **THE HEADLINE — the `d₀`-dilation transported into the door window.**

```
   ∑_{n<m≤n+H, m ≡ r (q)} a(m)e(αm)
     =  absWindowSum (dilCoeff a d₀ q₀ r₀) (dilLen H n d₀) (n/d₀) (d₀·α)
```

`d₀ = (r,q)`, `q₀ = q/d₀`, `r₀ = r/d₀`.  A change of variables, so there is no hypothesis on
`a` and no estimate: the reindexing is `M4Residue.sum_reindex_dilate`, the window's image is
§2, the class test is `M4Residue.modEq_dilate_iff`, and the frequency is §3's `d₀α`. -/
theorem classWindowSum_dilate (a : ℕ → ℂ) {q : ℕ} (hq : 0 < q) (r H n : ℕ) (α : ℝ) :
    classWindowSum a H n q r α
      = absWindowSum (dilCoeff a (Nat.gcd r q) (q / Nat.gcd r q) (r / Nat.gcd r q))
          (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) ((Nat.gcd r q : ℝ) * α) := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have hdvd : ∀ m ∈ (Finset.Ioc n (n + H)).filter (fun m => m ≡ r [MOD q]),
      Nat.gcd r q ∣ m := fun m hm => gcd_dvd_of_modEq (Finset.mem_filter.mp hm).2
  unfold classWindowSum absWindowSum dilCoeff
  rw [sum_reindex_dilate hdvd
      (fun m => a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * ((m : ℕ) : ℂ))),
    image_div_class_window hq r H n, ← Ioc_dilate_eq H n, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [exp_phase_dilate]
  · rw [zero_mul]

/-! ## §5 — THE λ-LEG: the factorisation and the `1_𝒮` transfer at the door

`λ` is completely multiplicative — `liouvilleC_mul` carries NO coprimality hypothesis — and
under the door gate `d₀ ≤ q ≤ W < P₁` the block indicator does not see `d₀`
(`M4Residue.memS_dilate_door`).  Both are consumed here; neither is re-proved. -/

/-- **The door gate at every block index.**  `M4Residue.door_dilation_gate'` gives `d < P₁`;
`calP_door_mono` lifts it to `d < P_j` for all `j ∈ [1,J]` — the exact hypothesis
`indicator_mul_dilate_liouville` demands.  STRICT throughout (`d₀ ≤ q ≤ W < P₁`).

⟦THE CAP IS `M`-RELATIVE⟧ the ceiling is the door's own bottom block `P₁`, not the numeral
`2^{262144}` reached through `log H ≤ 2^{21845}` — see `M4Residue.door_dilation_gate'`.  A
consumer at `W = (log H)^{12}` supplies `hW` from the old numeral route unchanged; a consumer
at `W = arcDen 12 H` supplies it from ⟦gate 12⟧'s re-cut line. -/
theorem door_gate_blocks {M J d q : ℕ} {W : ℝ} (hM : 1 ≤ M) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) :
    ∀ j ∈ Finset.Icc 1 J, d < calP (Adoor M) (3072 * M) j := fun _ hj =>
  lt_of_lt_of_le (door_dilation_gate_calP (M := M) hdq hqW hW)
    (calP_door_mono hM (Finset.mem_Icc.mp hj).1)

/-- **THE DILATED DATUM FACTORS** (MRT step (b) at the door, pointwise):

```
      dilCoeff (1_𝒮·λ) d₀ q₀ r₀ (k)  =  λ(d₀) · classCoeff (1_𝒮·λ) q₀ r₀ (k)
```

for `k ≠ 0`.  The λ-half is `liouvilleC_mul` (no coprimality); the `1_𝒮`-half is
`memS_dilate_door` (the strict gate), routed through
`M4Residue.indicator_mul_dilate_liouville`. -/
theorem dilCoeff_memS_door {M J d q q₀ r₀ : ℕ} {W : ℝ} (hM : 1 ≤ M) (hd : d ≠ 0) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
    {k : ℕ} (hk : k ≠ 0) :
    dilCoeff (memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) J
        liouvilleC) d q₀ r₀ k
      = liouvilleC d * classCoeff (memSCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) J liouvilleC) q₀ r₀ k := by
  simp only [dilCoeff, classCoeff, memSCoeff]
  by_cases hmod : k ≡ r₀ [MOD q₀]
  · rw [if_pos hmod, if_pos hmod]
    exact indicator_mul_dilate_liouville hd hk (door_gate_blocks hM hdq hqW hW)
  · rw [if_neg hmod, if_neg hmod, mul_zero]

/-- **The factorisation under the window sum**: `λ(d₀)` comes out of the whole dilated
window sum, because every index of `Ioc n₀ (n₀+H₀)` is `≥ 1`. -/
theorem absWindowSum_dilCoeff_memS_door {M J d q q₀ r₀ H₀ n₀ : ℕ} {W : ℝ} (hM : 1 ≤ M)
    (hd : d ≠ 0) (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) (β : ℝ) :
    absWindowSum (dilCoeff (memSCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) J liouvilleC) d q₀ r₀) H₀ n₀ β
      = liouvilleC d * absWindowSum (classCoeff (memSCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) J liouvilleC) q₀ r₀) H₀ n₀ β := by
  unfold absWindowSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  rw [dilCoeff_memS_door (J := J) hM hd hdq hqW hW hk0]
  ring

/-- **The dilation is invisible to the modulus**: `‖λ(d₀)‖ = 1`, so the transported window
sum's norm is the norm of the *reduced* datum's window sum. -/
theorem norm_absWindowSum_dilCoeff_memS_door {M J d q q₀ r₀ H₀ n₀ : ℕ} {W : ℝ} (hM : 1 ≤ M)
    (hd : d ≠ 0) (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) (β : ℝ) :
    ‖absWindowSum (dilCoeff (memSCoeff (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) J liouvilleC) d q₀ r₀) H₀ n₀ β‖
      = ‖absWindowSum (classCoeff (memSCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) J liouvilleC) q₀ r₀) H₀ n₀ β‖ := by
  rw [absWindowSum_dilCoeff_memS_door (J := J) (H₀ := H₀) (n₀ := n₀) hM hd hdq hqW hW β,
    norm_mul, liouvilleC_norm hd, one_mul]

/-! ## §6 — THE TRIVIAL BRANCH (the case split)

Below the freeze's threshold the class closes with no analysis at all: the dilated window
has at most `H/d₀ + 1` terms of modulus `≤ 1`.  `M4Dyadic.norm_absWindowSum_le_thresh` is
consumed verbatim; the `+1` is §1's, and it is why the branch is stated at `H/d₀ + 1 ≤ thr`
rather than at `H/d₀ ≤ thr`. -/

/-- The trivial bound at the DILATED window, with §1's `+1` paid. -/
theorem norm_absWindowSum_dilLen_le {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (H n : ℕ) {d : ℕ}
    (hd : 0 < d) {thr : ℝ} (hthr : (H : ℝ) / (d : ℝ) + 1 ≤ thr) (n₀ : ℕ) (β : ℝ) :
    ‖absWindowSum a (dilLen H n d) n₀ β‖ ≤ thr :=
  norm_absWindowSum_le_thresh ha (le_trans (dilLen_le_real H n hd) hthr) n₀ β

/-- **THE TRIVIAL BRANCH, at the class window.**  Transport (§4) + the trivial bound: a
class whose dilated window is below the threshold is discharged outright. -/
theorem norm_classWindowSum_le_thresh {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {q : ℕ} (hq : 0 < q)
    (r H n : ℕ) (α : ℝ) {thr : ℝ} (hthr : (H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ thr) :
    ‖classWindowSum a H n q r α‖ ≤ thr := by
  rw [classWindowSum_dilate a hq r H n α]
  exact norm_absWindowSum_dilLen_le (norm_dilCoeff_le_one ha _ _ _) H n
    (Nat.gcd_pos_of_pos_right r hq) hthr _ _

/-- The same at the freeze's own threshold `trivThresh H d₀ W = H·d₀/W³` (M4-5's trivial
branch), carried SYMBOLICALLY — this file never evaluates it. -/
theorem norm_classWindowSum_le_trivThresh {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {q : ℕ}
    (hq : 0 < q) (r H n : ℕ) (α : ℝ) {Hp d₀ W : ℝ}
    (hthr : (H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ trivThresh Hp d₀ W) :
    ‖classWindowSum a H n q r α‖ ≤ trivThresh Hp d₀ W :=
  norm_classWindowSum_le_thresh ha hq r H n α hthr

/-- **The trivial branch in the door's own `L¹` shape** (`logMeasure` is a probability
measure, so the pointwise bound passes under the integral unchanged — `M4Dyadic`'s
`integral_logMeasure_le_of_le`, no integrability side condition). -/
theorem integral_logMeasure_classWindowSum_le_thresh {x ω : ℕ} (hx : 2 ≤ x) (hω : 2 ≤ ω)
    {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {q : ℕ} (hq : 0 < q) (r H : ℕ) (α : ℝ) {thr : ℝ}
    (hthr : (H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ thr) :
    (∫ n, ‖classWindowSum a H n q r α‖ ∂(logMeasure x ω)) ≤ thr :=
  integral_logMeasure_le_of_le hx hω
    (fun n => norm_classWindowSum_le_thresh ha hq r H n α hthr)

/-- **THE CASE SPLIT** (the freeze's M4-5 dichotomy, at the door window).  Either the
dilated window is below the threshold — and the class is discharged by the trivial bound —
or it is not, and the transport identity hands the class to the analytic road at the
dilated datum.  The split is on the window length alone, which is what makes it usable
inside the dyadic cover (`m4_meansq_or_trivial`'s own shape). -/
theorem classWindow_trivial_or_long {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {q : ℕ} (hq : 0 < q)
    (r H n : ℕ) (α thr : ℝ) :
    ((H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ thr ∧ ‖classWindowSum a H n q r α‖ ≤ thr)
      ∨ (thr < (H : ℝ) / (Nat.gcd r q : ℝ) + 1
          ∧ classWindowSum a H n q r α
              = absWindowSum (dilCoeff a (Nat.gcd r q) (q / Nat.gcd r q) (r / Nat.gcd r q))
                  (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) ((Nat.gcd r q : ℝ) * α)) := by
  rcases le_or_gt ((H : ℝ) / (Nat.gcd r q : ℝ) + 1) thr with hshort | hlong
  · exact Or.inl ⟨hshort, norm_classWindowSum_le_thresh ha hq r H n α hshort⟩
  · exact Or.inr ⟨hlong, classWindowSum_dilate a hq r H n α⟩

/-! ## §7 — THE DILATED FREQUENCY'S ARC STATUS (where `q` and `d₀` meet)

The transported sum lives at the frequency `d₀α` on a window of length `dilLen H n d₀`.  Its
tight-major status is NOT inherited on the nose: the witness denominator drops to
`q'/(d₀,q')` (good), while the radius is multiplied by `d₀` and the window shrinks by `d₀`
(exactly cancelling), leaving the honest cost of the `±1` — the factor `(H+d₀)/H`. -/

/-- **THE FREQUENCY TRANSPORT.**  If `α` is `(Q,H)`-tight-major then `d·α` is tight-major on
any window `H₀` with `d·H₀ ≤ H + d`, at the cap `Q·(H+d)/H`.

The witness: `α ≈ a/q'` gives `dα ≈ (d/g)a/(q'/g)` with `g = (d,q')`, so the denominator
DROPS to `q'/g ≤ q' ≤ Q`, and the radius `d·Q/(q'H) = (d/g)·Q/((q'/g)H)` meets the target
`Q(H+d)/(H·(q'/g)·H₀)` exactly through `d·H₀ ≤ H+d`.  Nothing is discarded — and `d > 0` is
not needed: the identity `(d,q')·(d/(d,q')) = d` carries the degenerate case too. -/
theorem nearRatTight_dilate {Q α : ℝ} {H H₀ d : ℕ} (hQ : 0 ≤ Q) (hH : 0 < H)
    (hH₀ : 0 < H₀) (hlen : d * H₀ ≤ H + d) (h : NearRatTight Q H α) :
    NearRatTight (Q * ((H : ℝ) + (d : ℝ)) / (H : ℝ)) H₀ ((d : ℝ) * α) := by
  obtain ⟨a, q, hq, hqQ, hrad⟩ := h
  have hg : 0 < Nat.gcd d q := Nat.gcd_pos_of_pos_right d hq
  have hde : Nat.gcd d q * (d / Nat.gcd d q) = d :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left d q)
  have hqe : Nat.gcd d q * (q / Nat.gcd d q) = q :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right d q)
  have hq₀ : 0 < q / Nat.gcd d q := by
    rcases Nat.eq_zero_or_pos (q / Nat.gcd d q) with h0 | h0
    · rw [h0, Nat.mul_zero] at hqe
      omega
    · exact h0
  -- ⟦the real-side dictionary⟧
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hH₀R : (0 : ℝ) < (H₀ : ℝ) := by exact_mod_cast hH₀
  have hgR : (1 : ℝ) ≤ (Nat.gcd d q : ℝ) := by exact_mod_cast hg
  have hq₀R : (0 : ℝ) < ((q / Nat.gcd d q : ℕ) : ℝ) := by exact_mod_cast hq₀
  have hqR0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdR0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdR : (d : ℝ) = (Nat.gcd d q : ℝ) * ((d / Nat.gcd d q : ℕ) : ℝ) := by
    exact_mod_cast hde.symm
  have hqRe : (q : ℝ) = (Nat.gcd d q : ℝ) * ((q / Nat.gcd d q : ℕ) : ℝ) := by
    exact_mod_cast hqe.symm
  have heR : (0 : ℝ) ≤ ((d / Nat.gcd d q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hgne : (Nat.gcd d q : ℝ) ≠ 0 := by linarith
  have hq₀ne : ((q / Nat.gcd d q : ℕ) : ℝ) ≠ 0 := ne_of_gt hq₀R
  have hHne : (H : ℝ) ≠ 0 := ne_of_gt hHR
  have hEd : ((d / Nat.gcd d q : ℕ) : ℝ) ≤ (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hgR heR
    rw [one_mul] at h
    linarith [hdR]
  have hlenR : (d : ℝ) * (H₀ : ℝ) ≤ (H : ℝ) + (d : ℝ) := by exact_mod_cast hlen
  refine ⟨(d / Nat.gcd d q : ℕ) * a, q / Nat.gcd d q, hq₀, ?_, ?_⟩
  · -- the cap: the denominator DROPS, and `Q ≤ Q(H+d)/H`
    have hq₀q : ((q / Nat.gcd d q : ℕ) : ℝ) ≤ (q : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hgR hq₀R.le
      rw [one_mul] at h
      linarith [hqRe]
    have hQle : Q ≤ Q * ((H : ℝ) + (d : ℝ)) / (H : ℝ) := by
      rw [le_div_iff₀ hHR]
      nlinarith [mul_nonneg hQ hdR0]
    linarith [hq₀q.trans hqQ]
  · -- the radius, exactly
    have hcast : (((d / Nat.gcd d q : ℕ) * a : ℤ) : ℝ)
        = ((d / Nat.gcd d q : ℕ) : ℝ) * (a : ℝ) := by
      simp only [Int.cast_mul, Int.cast_natCast]
    have hkey : (((d / Nat.gcd d q : ℕ) * a : ℤ) : ℝ) / ((q / Nat.gcd d q : ℕ) : ℝ)
        = (d : ℝ) * ((a : ℝ) / (q : ℝ)) := by
      rw [hcast, hdR, hqRe]
      field_simp
    have habs : |(d : ℝ) * α - (((d / Nat.gcd d q : ℕ) * a : ℤ) : ℝ)
          / ((q / Nat.gcd d q : ℕ) : ℝ)|
        = (d : ℝ) * |α - (a : ℝ) / (q : ℝ)| := by
      rw [hkey, ← mul_sub, abs_mul, abs_of_nonneg hdR0]
    rw [habs]
    have hstep1 : (d : ℝ) * |α - (a : ℝ) / (q : ℝ)| ≤ (d : ℝ) * (Q / ((q : ℝ) * (H : ℝ))) :=
      mul_le_mul_of_nonneg_left hrad hdR0
    have hstep2 : (d : ℝ) * (Q / ((q : ℝ) * (H : ℝ)))
        = ((d / Nat.gcd d q : ℕ) : ℝ) * Q / (((q / Nat.gcd d q : ℕ) : ℝ) * (H : ℝ)) := by
      rw [hdR, hqRe]
      field_simp
    have hstep3 : ((d / Nat.gcd d q : ℕ) : ℝ) * Q
          / (((q / Nat.gcd d q : ℕ) : ℝ) * (H : ℝ))
        ≤ Q * ((H : ℝ) + (d : ℝ)) / (H : ℝ)
            / (((q / Nat.gcd d q : ℕ) : ℝ) * (H₀ : ℝ)) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : ((d / Nat.gcd d q : ℕ) : ℝ) * (H₀ : ℝ) ≤ (H : ℝ) + (d : ℝ) := by
        have := mul_le_mul_of_nonneg_right hEd hH₀R.le
        linarith
      have h2 : (0 : ℝ) ≤ Q * (((q / Nat.gcd d q : ℕ) : ℝ) * (H : ℝ)) := by positivity
      calc ((d / Nat.gcd d q : ℕ) : ℝ) * Q * ((H : ℝ) * (((q / Nat.gcd d q : ℕ) : ℝ)
              * (H₀ : ℝ)))
          = Q * (((q / Nat.gcd d q : ℕ) : ℝ) * (H : ℝ))
              * (((d / Nat.gcd d q : ℕ) : ℝ) * (H₀ : ℝ)) := by ring
        _ ≤ Q * (((q / Nat.gcd d q : ℕ) : ℝ) * (H : ℝ)) * ((H : ℝ) + (d : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = Q * ((H : ℝ) + (d : ℝ)) * (((q / Nat.gcd d q : ℕ) : ℝ) * (H : ℝ)) := by ring
    calc (d : ℝ) * |α - (a : ℝ) / (q : ℝ)|
        ≤ (d : ℝ) * (Q / ((q : ℝ) * (H : ℝ))) := hstep1
      _ = ((d / Nat.gcd d q : ℕ) : ℝ) * Q
            / (((q / Nat.gcd d q : ℕ) : ℝ) * (H : ℝ)) := hstep2
      _ ≤ Q * ((H : ℝ) + (d : ℝ)) / (H : ℝ)
            / (((q / Nat.gcd d q : ℕ) : ℝ) * (H₀ : ℝ)) := hstep3

/-- The dilated window's OWN denominator cap is smaller: `arcDen B (dilLen H n d) ≤
arcDen B H` (the window shrinks, and `arcDen` is monotone in `H`). -/
theorem arcDen_dilLen_le {B : ℝ} (hB : 0 ≤ B) {H n d : ℕ} (hd : 0 < d)
    (h1 : 1 ≤ dilLen H n d) : arcDen B (dilLen H n d) ≤ arcDen B H := by
  have hlt : (0 : ℝ) < (dilLen H n d : ℝ) := by exact_mod_cast h1
  have hle : (dilLen H n d : ℝ) ≤ (H : ℝ) := by exact_mod_cast dilLen_le_window H n hd
  unfold arcDen
  exact Real.rpow_le_rpow (Real.log_natCast_nonneg _) (Real.log_le_log hlt hle) hB

/-- **THE HONEST RADIUS BOOKKEEPING, stated as a comparison.**  The transported datum lives
at the cap `arcDen 12 H·(H+d₀)/H`, which is ABOVE the dilated window's own
`arcDen 12 (dilLen H n d₀)`.  So the dilation cannot be absorbed into the arc datum: it costs
the explicit factor `1 + d₀/H` (`≤ 1 + (log H)^{12}/H` at the door's gate `d₀ ≤ q ≤ W`), and
this inequality is the exact place where `q` and `d₀` meet. -/
theorem arcDen_le_dilate_cap {H n d : ℕ} (hd : 0 < d) (h1 : 1 ≤ dilLen H n d) :
    arcDen 12 (dilLen H n d) ≤ arcDen 12 H * ((H : ℝ) + (d : ℝ)) / (H : ℝ) := by
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · exfalso
    have := dilLen_le_window 0 n hd
    omega
  · have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
    have hdR0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hstep := arcDen_dilLen_le (B := 12) (by norm_num) hd h1
    have hcap : arcDen 12 H ≤ arcDen 12 H * ((H : ℝ) + (d : ℝ)) / (H : ℝ) := by
      rw [le_div_iff₀ hHR]
      nlinarith [arcDen_nonneg 12 H]
    linarith

/-- **The frequency transport at the door's arc datum**: a tight-major `α` at cap
`arcDen 12 H` transports to `d₀·α`, tight-major on the dilated window at the cap
`arcDen 12 H·(H+d₀)/H`. -/
theorem nearRatTight_dilate_door {H n d : ℕ} {α : ℝ} (hd : 0 < d) (hH : 0 < H)
    (hlen : 0 < dilLen H n d) (h : NearRatTight (arcDen 12 H) H α) :
    NearRatTight (arcDen 12 H * ((H : ℝ) + (d : ℝ)) / (H : ℝ)) (dilLen H n d)
      ((d : ℝ) * α) :=
  nearRatTight_dilate (arcDen_nonneg 12 H) hH hlen (d_mul_dilLen_le H n hd) h

/-! ## §8 — THE COMPOSED EXIT

The per-class statement ⟦BRIDGE 1⟧/⟦BRIDGE 2⟧'s chain consumes: at the door's sieved λ
datum, each residue class's window sum is — in modulus, exactly — the dilated window sum at
the REDUCED datum `(q₀, r₀)`, with the `d₀`-bookkeeping constants explicit and the trivial
branch available at every threshold. -/

/-- **THE ROW'S EXIT — the per-class dilated statement.**  For the door's sieved Liouville
datum `1_𝒮·λ`, at a class `r` mod `q` with `d₀ = (r,q)` under the door gate
`d₀ ≤ q ≤ W < P₁` (`W` free — the cap is the door's own `P₁`, `M4Residue.door_dilation_gate'`):

1. **the transport** — `‖class sum‖ = ‖dilated window sum at the reduced datum‖`
   (`λ(d₀)` has modulus 1, so the dilation is invisible);
2. **the bookkeeping** — the dilated length is `H/d₀ ± 1`, both signs derived, and `≤ H`;
3. **the trivial branch** — every threshold above `H/d₀ + 1` closes the class outright.

The reduced class is coprime (`M4Residue.coprime_reduced_of_gcd`: `(r₀,q₀) = 1`), which is
what makes the character expansion (⟦BRIDGE 1⟧'s second half, `M4Close.
sum_liou_modEq_residue_eq`) legitimate at the dilated datum. -/
theorem m4_class_dilate_exit {M J q r H n : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) (α : ℝ) :
    ‖classWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) J liouvilleC) H n q r α‖
        = ‖absWindowSum (classCoeff (memSCoeff (calP (Adoor M) (3072 * M))
            (calQK (Adoor M) (3072 * M) M) J liouvilleC)
              (q / Nat.gcd r q) (r / Nat.gcd r q))
            (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) ((Nat.gcd r q : ℝ) * α)‖
      ∧ ((H : ℝ) / (Nat.gcd r q : ℝ) - 1 ≤ (dilLen H n (Nat.gcd r q) : ℝ)
          ∧ (dilLen H n (Nat.gcd r q) : ℝ) ≤ (H : ℝ) / (Nat.gcd r q : ℝ) + 1
          ∧ dilLen H n (Nat.gcd r q) ≤ H)
      ∧ (∀ thr : ℝ, (H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ thr →
          ‖classWindowSum (memSCoeff (calP (Adoor M) (3072 * M))
            (calQK (Adoor M) (3072 * M) M) J liouvilleC) H n q r α‖ ≤ thr) := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  have hdq : Nat.gcd r q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right r q)
  refine ⟨?_, ⟨le_dilLen_real H n hd, dilLen_le_real H n hd, dilLen_le_window H n hd⟩, ?_⟩
  · rw [classWindowSum_dilate _ hq r H n α]
    exact norm_absWindowSum_dilCoeff_memS_door (J := J)
      (H₀ := dilLen H n (Nat.gcd r q)) (n₀ := n / Nat.gcd r q) hM hd.ne' hdq hqW hW _
  · intro thr hthr
    exact norm_classWindowSum_le_thresh
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ J m) hq r H n α hthr

/-- The reduced class of the exit is COPRIME — cited from `M4Residue` so that the exit's
consumer never has to re-derive the hypothesis the character expansion needs. -/
theorem m4_class_dilate_coprime {q : ℕ} (hq : 0 < q) (r : ℕ) :
    Nat.Coprime (r / Nat.gcd r q) (q / Nat.gcd r q) :=
  coprime_reduced_of_gcd hq

/-! ## §9 — ⟦SEAM A⟧: the plug into ⟦BRIDGE 1⟧'s non-coprime half

`M4BridgeResidue.norm_absWindowSum_split_coprime_add` cuts the `r`-sum into its coprime and
non-coprime halves and names the second "`M4Residue`'s `d₀`-dilation (⟦BRIDGE 3⟧), which
plugs in exactly here".  This section makes that plug literal: ⟦BRIDGE 1⟧'s carrier
`classPhaseSum` is byte-identical to §4's `classWindowSum`, so the transport applies to it
unchanged — and on the NON-COPRIME classes (`d₀ = (r,q) > 1`, exactly the dilation's own
regime) it delivers the `H/d₀` saving the trivial branch then spends. -/

/-- ⟦BRIDGE 1⟧'s class carrier IS §4's: `windowClass H n q r` is `(Ioc n (n+H)).filter
(· ≡ r (q))` on the nose, and the summands are the same term. -/
theorem classWindowSum_eq_classPhaseSum (a : ℕ → ℂ) (H n q r : ℕ) (θ : ℝ) :
    classWindowSum a H n q r θ = classPhaseSum a H n q r θ := rfl

/-- **THE TRANSPORT AT ⟦BRIDGE 1⟧'S CARRIER.**  The residual-frequency class sum of
⟦BRIDGE 1⟧ is a door-shaped window sum on the dilated window at the dilated frequency
`d₀·θ`. -/
theorem classPhaseSum_dilate (a : ℕ → ℂ) {q : ℕ} (hq : 0 < q) (r H n : ℕ) (θ : ℝ) :
    classPhaseSum a H n q r θ
      = absWindowSum (dilCoeff a (Nat.gcd r q) (q / Nat.gcd r q) (r / Nat.gcd r q))
          (dilLen H n (Nat.gcd r q)) (n / Nat.gcd r q) ((Nat.gcd r q : ℝ) * θ) := by
  rw [← classWindowSum_eq_classPhaseSum]
  exact classWindowSum_dilate a hq r H n θ

/-- The trivial branch at ⟦BRIDGE 1⟧'s carrier. -/
theorem norm_classPhaseSum_le_thresh {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) {q : ℕ} (hq : 0 < q)
    (r H n : ℕ) (θ : ℝ) {thr : ℝ} (hthr : (H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ thr) :
    ‖classPhaseSum a H n q r θ‖ ≤ thr := by
  rw [← classWindowSum_eq_classPhaseSum]
  exact norm_classWindowSum_le_thresh ha hq r H n θ hthr

/-- **THE COMPOSED EXIT AT ⟦SEAM A⟧.**  ⟦BRIDGE 1⟧'s split, with its non-coprime half
discharged by the dilation's trivial branch:

```
   ‖∑_{n<m≤n+H} a(m)e((a₀/q + θ)m)‖
     ≤  ∑_{r<q, (q,r)=1} ‖class sum‖  +  #{r<q : (q,r)≠1} · thr
```

for any `thr` dominating `H/d₀ + 1` on every non-coprime class — the `d₀`-bookkeeping made
explicit, `d₀ = (r,q) > 1` there, so the branch is bought by the DILATED window's length and
not by `H`.  The coprime half is left untouched: it is the character expansion's half
(`M4Close` §6, `M4BridgeResidue` §4). -/
theorem norm_absWindowSum_split_dilate_trivial {a : ℕ → ℂ} (ha : ∀ m, ‖a m‖ ≤ 1) (H n : ℕ)
    {q : ℕ} (hq : 0 < q) (a₀ : ℤ) (θ : ℝ) {thr : ℝ}
    (hthr : ∀ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
      (H : ℝ) / (Nat.gcd r q : ℝ) + 1 ≤ thr) :
    ‖absWindowSum a H n ((a₀ : ℝ) / (q : ℝ) + θ)‖
      ≤ (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
            ‖classPhaseSum a H n q r θ‖)
        + (((Finset.range q).filter (fun r => ¬ Nat.Coprime q r)).card : ℝ) * thr := by
  refine le_trans (norm_absWindowSum_split_coprime_add a H n hq a₀ θ) ?_
  have hnc : ∑ r ∈ (Finset.range q).filter (fun r => ¬ Nat.Coprime q r),
      ‖classPhaseSum a H n q r θ‖
      ≤ (((Finset.range q).filter (fun r => ¬ Nat.Coprime q r)).card : ℝ) * thr := by
    have h := Finset.sum_le_card_nsmul
      ((Finset.range q).filter (fun r => ¬ Nat.Coprime q r))
      (fun r => ‖classPhaseSum a H n q r θ‖) thr
      (fun r hr => norm_classPhaseSum_le_thresh ha hq r H n θ (hthr r hr))
    simpa [nsmul_eq_mul] using h
  linarith

end Salt.MR

end
