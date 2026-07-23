# Cloud shift — afternoon-1 (L11-FINISHER)

**Mission:** land A-2 `dual_assembly` and A-3 `halasz_primes_pow` — the last two
stones of node **L11** — by extending `Salt/MR/HalaszPrimesCore.lean`.
**Branch:** `cloud-shift/afternoon-1` (from `origin/main`). All commits `[skip ci]`,
single Lean file (append-only; landed region byte-identical), plus this report.

---

## Setup (the per-session cost)

The mission's `elan-init.sh` path is **blocked** in this environment, but not by a
network wall — by GitHub **repo-scoping**. Verbatim:

```
$ curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
info: downloading installer
curl: (22) The requested URL returned error: 403
elan: command failed: curl -sSfL https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz
```

The 403 body (captured directly) is **not** an egress denial:

```
{"message":"GitHub access to this repository is not enabled for this session.
 Use add_repo to request access.","documentation_url":"..."}
```

`leanprover/elan` is **out of this session's GitHub scope** (scope = `jyh/salt`,
`leanprover/lean4`); the elan binary download is refused. The proxy itself is
healthy (`recentRelayFailures: []`, TLS fine, CONNECT tunnels establish).

**Workaround (no network fight):** the toolchain repo `leanprover/lean4` **is** in
scope, so I downloaded the pinned toolchain tarball directly and put its `bin/` on
PATH, bypassing elan entirely:

```
curl -sSL https://github.com/leanprover/lean4/releases/download/v4.32.0-rc1/lean-4.32.0-rc1-linux.tar.zst
  -> 200, 564 MB (in-scope repo -> CDN redirect works)
tar --zstd -xf ...   (apt-get install -y zstd first; zstd not preinstalled)
export PATH=/home/user/toolchain/lean-4.32.0-rc1-linux/bin:$PATH
lean --version -> 4.32.0-rc1  ✓
```

Timings (UTC): elan attempt 21:31 (fail); toolchain download+extract 21:34–21:35
(~1 min, 564 MB); `lake exe cache get` 21:35–21:37 (8564 files, exit 0);
`lake build` corpus 21:38 → green (8800 jobs). **Module gate builds cost ~18–22 min
each** — the 3170→3400-line `HalaszPrimesCore.lean` fully re-elaborates
`per_pair_contour` (12.8M-heartbeat tactics) on every edit; budget for it.

**Freshness:** commit `ebf4d67` reachable from `HEAD` (`git merge-base
--is-ancestor` → true). No stale proxy.

---

## Per-stone results

### A-2 `dual_assembly` — **LANDED** (commit chain below)

The dual bound, assembled exactly per the freeze's A-2 card:

- `window_dominates` opens `log P · Σ_{p∈S} g(p) ≤ Σ_n Λ(n)·w(n)·g(n)`
  (g(n) = ‖Σ_t η_t n^{it}‖², nonneg; full Λ-window sum on the right);
- `(RHSr : ℂ)` is expanded pairwise: `= Σ_{t,t'} η_t·conj(η_{t'})·inner(t−t')`,
  where `inner(u)` is exactly `per_pair_contour`'s tsum (the cast + normSq
  expansion + a double `Summable.tsum_finsetSum` swap + `tsum_mul_left`);
- `inner(t−t') = windowKernel P 1 (t−t') + δ`, `‖δ‖ ≤ ε` from `per_pair_contour`
  (u-uniform; `|t−t'| ≤ 2T` from the `[-T,T]` bracket);
- **pole row** `pole_double_row` (Cauchy `|η_t η_{t'}| ≤ ½(|η_t|²+|η_{t'}|²)` +
  `pole_row_sum` in both orientations) → `≤ 44π·P·Σ‖η‖²`;
- **error row** `error_double_row` → `≤ ε·|𝒯|·Σ‖η‖²`;
- divide by `log P`.

Exit: `Σ_{p∈S} ‖Σ_t conj(p^{−it})·η_t‖² ≤ (44π·P + ε·|𝒯|)/log P · Σ_t‖η_t‖²`,
with `ε` = `per_pair_contour`'s concrete `5T+1`-height decay (verbatim, the six
`T₀` thresholds auto-inherited by destructuring `per_pair_contour`).

Helpers landed (all in the new `L11Assembly` section, after `per_pair_contour`):
`hatMellin_conj`, `windowKernel_neg`, `norm_windowKernel_neg`, `pole_double_row`,
`error_double_row`, `conj_ncast_cpow`, `summable_window_pair`, `dual_core`,
`dual_assembly`.

### A-3 `halasz_primes_primal_raw` — **LANDED**

The **primal** Halász bound, via `primes_dual_iff` off `dual_assembly`
(`.mpr`, with `0 ≤ Δ`):

`Σ_t ‖Σ_p p^{−it}·a_p‖² ≤ (44π·P + ε·|𝒯|)/log P · Σ_p‖a_p‖²`

— the frozen conclusion shape **at the raw `5T+1`-height decay** `ε`. This is the
honest primal L11 bound; only the pure-`(log T)` repackaging remains (see residual).

### A-3 `halasz_primes_pow` (frozen header) — **absorption MACHINERY LANDED; final constant-assembly is the RESIDUAL**

The frozen header wants the decay in pure-`T` form
`exp(−c·log P / ((log T)^{3/4}(loglog T)⁴))·(log T)²` with `∃ C c T₀`, `P ≤ T^10`.
`primal_raw` already gives the primal at `ε` (the `5T+1`, `D₃`/`D₄` form). The
remaining step is the **absorption** to that shape. Its hard analytic core is now
**landed** (sorry-free, axiom-clean) — the `A-3 absorption machinery` section:

- `log_le_rpow_div : log u ≤ u^ε/ε` (`u,ε>0`) — the key polylog-vs-power tool
  (apply `log_le_sub_one` to `u^ε`; no `isLittleO`/threshold needed).
- `loglog4_le : (loglog T)⁴ ≤ (16/5)⁴·(log T)^{5/4}` (`log T ≥ 1`).
- `log5T1_le_two_logT : log(5T+1) ≤ 2 log T` (`T ≥ 6`, via `5T+1 ≤ T²`).
- `loglog5T1_le : loglog(5T+1) ≤ 2 loglog T`.
- `D3_5T1_le : D₃(5T+1) ≤ Cκ·D₄(T)` with `Cκ = 2^{3/4}·8` — prices the exp-match.
- `D4_5T1_le : D₄(5T+1) ≤ K₂·(log T)²` with `K₂ = 2^{3/4}·16·(16/5)⁴` — prices
  the `(log T)²` factor.

With these, the final `halasz_primes_pow` is a bounded constant-assembly: pick
`C = 44π + 3C₁K₂ + 30C₂ + 3C₃K₂`, `c = min(c_vk/(2Cκ), 1/20)`,
`T₀ = max(max T₀_raw (exp(exp 1))) 6`, then show
`44π·P + ε·|𝒯| ≤ C·(P + |𝒯|·P·exp(−c·log P/D₄(T))·(log T)²)` via three term-bounds:

1. **`εA`** (leading): `exp(−(c_vk/2)L/D₃(5T+1)) ≤ exp(−cL/D₄(T))` [from `c·D₃(5T+1)
   ≤ (c_vk/2)·D₄(T)`, i.e. `D3_5T1_le` + `c ≤ c_vk/(2Cκ)`] and `D₄(5T+1) ≤
   K₂(log T)²` [`D4_5T1_le`] ⟹ `εA ≤ C₁K₂·P·exp(−cL/D₄(T))(log T)² ≤ (C/3)·(…)`.
   **This term is verified working in scratch.**
2. **`εB`** = `C₂·P·L/T`: uses `expc ≥ exp(−10c·log T) ≥ 1/T` (since `10c ≤ ½`)
   and `L ≤ 10 log T` (`P ≤ T^10`), giving `εB ≤ (C/3)·P·expc·(log T)²` once
   `C ≥ 30C₂`, `log T ≥ 1` — **the T-threshold collapses to `T^{1−10c}·log T ≥ 1`,
   trivial for `T ≥ e`** (choosing `C` large normalizes the constants away).
3. **`εC`** = `C₃·D₄(5T+1)·P/T²`: `1/T²` dominates a fortiori; `C ≥ 3C₃K₂`.

RESIDUAL: only the mechanical `εB`/`εC` term-bounds and the `star`+division chain
remain. In scratch these ran into `nlinarith` heartbeat timeouts and
product-atom-associativity friction in the constant juggling (not mathematical
gaps) — a `set_option maxHeartbeats` bump + `calc`-structured (nlinarith-free)
term bounds is the path. Stopped here per the "give up early, loudly" discipline
rather than grind the 20-min-rebuild loop; the machinery is banked so a successor
closes the assembly directly. `primal_raw` remains the faithful primal exit — the
absorption is repackaging only, no new mathematics.

---

## The discard-redundancy ruling (the freeze's open question)

`prime_power_discard` is **NOT needed** in this assembly, and I subtracted nothing.
`window_dominates` lower-bounds the prime sum by `log P·Σ_p g(p) ≤ Σ_n Λ(n)·w(n)·g(n)`
over **all** `n` (primes *and* proper prime powers), and `per_pair_contour` prices
that **full** Λ-window sum. The prime-power terms are already inside the priced
tsum (they only add, all summands `≥ 0`), so no separate discard subtraction
arises. `prime_power_discard` / `prime_power_count_le` / `inner_sum_sq_le` remain in
the file untouched (per instructions) — they are simply unused by the closed route.

---

## Axiom audits

All landed lemmas: `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.
Verified per increment via a scratch file **outside** the repo
(`lake env lean scratch.lean`). No `sorry`, no `native_decide`, no new axioms.

## New traps banked

- **`lake env lean` needs the project CWD** — run from `/home/user/salt`, else
  `unknown module prefix 'Salt'` (search path lacks the build dir).
- **`RCLike.mul_conj` vs `Complex.mul_conj'`:** the RCLike form's `‖z‖^2` coercion
  (algebraMap) does not syntactically match `push_cast`'s `Complex.ofReal`; use
  `Complex.mul_conj'` (ℂ-native) for `← rw` after `ofReal_pow`.
- **`push_cast` splits `↑(t−t')` → `↑t − ↑t'`**, breaking a match against a lemma
  stated with `↑(t−t')`. Use targeted `Complex.ofReal_mul`/`ofReal_pow` rewrites on
  the LHS only, not a blanket `push_cast`.
- **`Σ (f+g)/2·h` distribution:** `rw [eq_div_iff two_ne_zero, Finset.sum_mul,
  ← Finset.sum_add_distrib]` + nested `sum_congr` + `ring` is bulletproof;
  `add_div, ← Finset.sum_div` fails because the summand is `(…/2)·h`, not `…/2`.
- **char-vs-byte long lines:** the `linter.style.longLine` counts **characters**
  (ℂ, ∑, ↑ = 1 char); a `grep .{101,}` (bytes) over-reports. Check with Python
  `len(str)`.
- **Setup: `elan` 403 is repo-scoping, not egress** — download the in-scope
  `leanprover/lean4` toolchain tarball directly and skip elan.

## Appended line count

`Salt/MR/HalaszPrimesCore.lean`: 3040 → 3547 lines (the `L11Assembly` section:
A-2 helpers + `dual_core` + `dual_assembly` + `halasz_primes_primal_raw` + the
A-3 absorption machinery). Landed region (`≤ 3040`) byte-identical to baseline.

Landing sequence (branch `cloud-shift/afternoon-1`, all `[skip ci]`):
`21dc9fc` kernel conj-symmetry + double rows · `37aef62` dual_core ·
`8c53c56` dual_assembly + primal_raw + report · (+ absorption machinery).
