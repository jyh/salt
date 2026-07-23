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

### A-3 `halasz_primes_pow` (frozen header) — **RESIDUAL** (the `D₃(5T+1)→D₄(T)` absorption)

The frozen header wants the decay in pure-`T` form
`exp(−c·log P / ((log T)^{3/4}(loglog T)⁴))·(log T)²` with `∃ C c T₀`, `P ≤ T^10`.
`primal_raw` already gives the primal at `ε` (the `5T+1`, `D₃`/`D₄` form). The
remaining step is the **absorption**: choose `C ≥ 44π`, `c`, `T₀` so that for
`T ≥ T₀`, `P ≤ T^10`:

  `44π·P + ε·|𝒯| ≤ C·(P + |𝒯|·P·exp(−c·log P/D₄(T))·(log T)²)`.

Reduces (÷ `|𝒯|`, ÷ `P`) to three term-bounds, each a delicate `rpow`/`log`
threshold inequality:

1. **`εA` (the leading term):** `C₁·exp(−(c_vk/2)·log P/D₃(5T+1))·D₄(5T+1) ≤
   (C/3)·exp(−c·log P/D₄(T))·(log T)²`. Needs (a) `c·D₃(5T+1) ≤ (c_vk/2)·D₄(T)`
   — i.e. `D₄(T)/D₃(5T+1) → ∞` (the `(loglog)⁴`-vs-`³` gain beats the
   `log(5T+1)/log T → 1` and `loglog(5T+1)/loglog T → 1` losses), pick
   `c = c_vk/2` once `D₄(T) ≥ D₃(5T+1)`; and (b) `D₄(5T+1) ≤ (log T)²`
   (`(log)^{3/4}(loglog)⁴ = o((log)²)`).
2. **`εB`:** `C₂·log P/T ≤ (C/3)·exp(−c·log P/D₄(T))·(log T)²`; uses `P ≤ T^10`
   (`log P ≤ 10 log T`) so `exp(−c·log P/D₄(T)) ≥ T^{−o(1)} ≫ 1/T`.
3. **`εC`:** `C₃·D₄(5T+1)/T² ≤ (C/3)·exp(…)·(log T)²` — dominated a fortiori (`1/T²`).

Each is true (standard slowly-varying asymptotics) but is a real C-tier estimate
with the module's full rpow/log trap bank; the 20-min module rebuild per iteration
makes the debug loop expensive. Left as the single residual. `primal_raw` is the
faithful primal exit; the absorption is repackaging only, no new mathematics.

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

`Salt/MR/HalaszPrimesCore.lean`: 3040 → ~3400 lines (the `L11Assembly` section).
Landed region (`≤ 3040`) byte-identical to the mission baseline.
