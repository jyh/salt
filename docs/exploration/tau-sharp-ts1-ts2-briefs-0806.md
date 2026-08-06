# TAU-SHARP — THE TS-1 AND TS-2 EXECUTOR BRIEFS, BANKED

**Status:** both waves HELD until **20:00 tonight** by the fleet's third-OOM standing order
(`FLEET.md`, 8/6 09:22 — the math seat pauses all Lean building; TBalTall/TBalR8 are the 8+GB
elaborations). These briefs are complete and pre-derived so the waves fire tonight with no
re-work. Written by the salt MATHEMATICS seat, 2026-08-06.

**Governing documents, in precedence order:**
1. `docs/exploration/tau-sharp-refuter-0806.md` — the TS-0 verdicts. **BINDING; overrides the
   dossier wherever they differ.**
2. `docs/exploration/tau-sharp-scout-dossier-0805.md` — the design freeze (§5 stones, §6 plan).
3. `CLAUDE.md` — the iron rules.

---

## ⛔ THE BUILD RULE — GOES VERBATIM IN EVERY EXECUTOR BRIEF ⛔

THREE OOM incidents on 8/6 (single Lean elaborations reach 6–9 GB on salt's heavy files; five
seats at default parallelism exhausted 64 GB + 8 GB swap; 49 bare `lean` processes bypassed the
lock). **EVERY Lean invocation — builds AND audit runs — goes through the fleet wrapper. NEVER
bare `lake build`, NEVER bare `lake env lean`, NEVER bare `lean`.**

```
/Users/jyh/projects/claude/saltbuild.sh                    # full build
/Users/jyh/projects/claude/saltbuild.sh Salt.SW.TBalR8     # targeted build
/Users/jyh/projects/claude/saltbuild.sh ScratchTS1.lean    # audit run (replaces `lake env lean`)
```

Atomic cross-seat lock (one heavy job fleet-wide, stale-reaped), `LEAN_NUM_THREADS=4`. It prints
**`saltbuild EXIT=N` — judge THAT number, not a pipe's exit status.** Exit 75 is a lock-wait
timeout and is safe to retry; killed builds resume incrementally, so no work is lost.
**Prefer TARGETED builds while iterating**; full build only at wave exit.

## ⛔ THE SHARED-TREE RULE ⛔

`/Users/jyh/projects/claude/salt` is a **shared working tree**: other seats commit into it
concurrently (observed 8/6 at 09:04, 09:18, and a seat's `git add -A` swept another seat's staged
file into commit `b406014`). Therefore: **commit ONLY explicit pathspecs. Never `git add -A`,
never `git commit -a`.** Before standing down, leave no unverified edits in the tree.

---

## WAVE TS-1 — S1 + S5 + S6

### Work already done and BANKED (unverified — never completed a build)

A killed pre-rule executor got partway. Its output is preserved and **verified to re-apply
cleanly** (`git apply --check`):

- `~/.claude/salt-ts1-wip/ts1-partial.patch` — 701-line diff against
  `Salt/SW/{TBalR8,TBalTall,All}.lean`, containing **S6 propagated (636 → 570)** and
  **S5(a) propagated (627 → 248)** through `C2Rho_le_tall` → `row_Eρ_cap_tall` → `KEρ`, plus the
  `neg_log_le_rpow'` roll-call row in `Salt/SW/All.lean`.
- `~/.claude/salt-ts1-wip/ScratchTS1.lean` — **proved** (elaborated, not yet axiom-audited):
  the S1 generalised `tbal_tau_le_split` at `(hc0 : 0 ≤ c) (hc : c ≤ 1)`, the sharp
  `neg_log_le_rpow' : −log u ≤ u^{−δ}/(e·δ)`, and `logz_factor_le` at **248**.
  The sharp-log route that worked: `Real.log_le_sub_one_of_pos` at `y/e` gives `log y ≤ y/e`;
  then `Real.log_rpow` + `le_div_iff₀`. The `e3` step needs `Real.exp_one_gt_d9` to turn
  `600/e` into the numeral `221` (`3 + 24 + 221 = 248`).

**START BY RE-APPLYING THE PATCH**, then finish S1 (which is proved in scratch but **not yet
threaded into either tower**) and mirror everything into the TBalR8 twin.

### ⛔ THE KILL THAT GOVERNS THE WAVE — BOTH TOWERS, ALWAYS
The dossier's edit lists name only the TALL assembly. **They are wrong.** Two parallel
assemblies; four of five row caps SHARED verbatim (`row_rho_main_cap`, `row_A_cap`, `row_1x_cap`,
`row_Eβ_cap`); only Eρ is forked.
- `dh_repulsion_inst` (`TBalR8:1373`) → **LANDED `dh_repulsion_ordered` (`:1752`)**, **11-fold**
  `c`-min at `TBalR8:1776-1833`. Consumed at `TauExt.lean:353`, audited in `Salt/SW/All.lean:313`.
- `dh_repulsion_inst_tall` (`TBalTall:1673`) → `dh_repulsion_tall` (`:2081`), **10-fold** `c`-min
  at `TBalTall:2105-2156`.

`hc_t1` is consumed at **TWO** sites: `TBalTall:1730-1733` **and `TBalR8:1425-1428`**. Edit only
the tall side and a landed theorem with live consumers goes red.
Note also: TBalR8's KEβ/KEρ arms carry a **free `Z₀`** (`:1387-1388`), so the dossier's §3 arm
table (computed at the tall numerals `Z₀ ⇝ 5`, `636`) does not price that tower at all.

### S1 — **by numeral replacement, NOT arm deletion**
Deleting a `min` head shifts every hand-built `le_trans (min_le_right _ _) …` projection below it
(`hc_t2` two deep, `hc_t10` nine deep) — ~123 lines of churn. Instead:
1. Restate `tbal_tau_le_split` (`TBalR8:44-46`) generalised in `c` — **the proof is already
   written in the banked scratch file**. Keep `b = 680`, `k = 14` hardwired; parametrising them
   is TS-3's job.
2. Replace the head numeral `2 ^ (-(250 : ℝ))` by `1/40` in BOTH towers (`TBalTall:2105`,
   `TBalR8:1776`); `hp1` becomes `by norm_num` (`TBalTall:2109`, `TBalR8:1780`). `hc_t1` then
   reads `c ≤ 1/40` and feeds both trivial branches. **Every other projection keeps its index.**
`log 40 = 3.69` is dominated by the surviving `1/576` arm (6.36), so the arm goes inert and the
**full 173.29 is realised anyway**; and it is S4-shaped, so TS-3 never re-touches this lemma.

### S5(b) — GUARDED, and it is optional
The δ re-tune `1/100 → ≈1/50` (`248 → ≈137`) changes the `u`-exponent `−9/100` at every consumer
of `logz_factor_pow9_le`, hence every γ-floor and every window `nlinarith`. **STOP-RULE: if it
costs more than ~40 lines or breaks any window check, ABANDON it, keep S5(a), and record why in
`flags.md`.** It moves no delivered number (see the arm table below); its value is TS-3's only.

### S6 — done in the patch; still check the twin
Confirm whether TBalR8 has a `C2Rho_le` that also over-counts. If it does not, **say so
explicitly**; do not force a change.

---

## WAVE TS-2 — S2, the γ-honest arms (fires AFTER TS-1; same writer-slot block)

Replace the three `Real.rpow_le_rpow_of_exponent_ge … (1/8)` collapse steps by each row's own
γ-floor, restate that row's `hg` as `K·c^{γ₀} ≤ 1/8`, and change the arm to
`c ≤ (1/(8K))^{1/γ₀}` (`hcollapse`, `TBalTall:1973`, already takes an arbitrary rational `pinv`).

### ⛔ USE EXACT RATIONALS — THE FREEZE'S NUMERALS ARE INADMISSIBLE
Each γ is a function of σ alone (Eρ, Eβ), strictly increasing, so the infimum is at the **closed**
endpoint `hσlo : 16/17 ≤ σ`:

| row | site | exact γ(σ) | **floor to use** | freeze's (WRONG) |
|---|---|---|---|---|
| Eρ | `TBalTall:1644-1645` | `14σ − 1009/100` | **`5247/1700`** | 3.0865 — FALSE at σ=16/17 |
| Eβ | `TBalR8:816-817` | `14σ − 1109/100` | **`3547/1700`** | 2.0865 — FALSE at σ=16/17 |
| A | `TBalR8:542-543` | `49/50 − 14(w−u)` | **`133/850`** | 0.15647 (true, margin 5.9e−7) |

Both wrong numerals exceed their infimum by `2.941e−5`. **Close the side goals with
`linarith [hσlo]` (tight-but-true, equality at the endpoint), NOT `nlinarith`.**
Direction is safe: `rpow_le_rpow_of_exponent_ge (hx0) (hx1 : x ≤ 1) (hyz : z ≤ y) : x^y ≤ x^z` is
applied with the side goal in the FLOOR direction; substituting `γ₀ > 1/8` keeps the shape and
makes `hg` a **weaker** demand on `c`. `hσlo` is already in scope and already load-bearing at all
three lines — no uniformity trap.

**If TS-1 landed S5(b),** recompute the two floors at the new exponent (`−9/50` in place of
`−9/100` ⇒ `5247/1700 − 9/100` and `3547/1700 − 9/100`) before writing any numeral.

### THE ARM TABLE — the ledger the wave must not lose
`c` is a `min` over ten arms; `log(1/c)` is the **MAX**. Record this as a comment beside both
`c`-min blocks.

| arm | landed `log(1/arm)` | after TS-1+TS-2 |
|---|---|---|
| `2^{−250}` → `1/40` | 173.29 | 3.69 |
| **`(c₀/32)^{17/3}`** | 86.23 | **86.23 ← BINDING** |
| `(1/805)^{50/49}` | 6.83 | 6.83 |
| `(1/(8·1610·e))^8` → A-row γ | 83.71 | 66.87 |
| `1/2` | 0.69 | 0.69 |
| `(1/KEβ)^8` → γ_Eβ | 536.67 | 32.15 |
| `(c₀/KEρ)^8` → γ_Eρ | **631.58 ← BINDING** | 25.58 (less, w/ S5+S6) |
| `1/(3A₀)` | 4.85 | 4.85 |
| `1/18` | 2.89 | 2.89 |
| `1/576` | 6.36 | 6.36 |
| **MAX** | **631.58** | **86.23** |

`c₀ = 1/126848` (`ZeroFreeReal.lean:392/:605`), `log(1/c₀) = 11.7507`;
`KEβ = 16·(328+48·5)·627^9`, `KEρ = 16·636·627^9` (`TBalTall:2097-2098`).

**Read this before budgeting effort:** **S1 is the load-bearing stone.** Without it the
`2^{−250}` arm at 173.29 becomes binding after TS-2 and the whole program stalls there instead of
86.23. **S5 and S6 shrink arms that end at 32.15 and 25.58 — far below the binding 86.23 — so
they deliver 0.00 to this program's grade.** Their value is banked for TS-3 (which drops the
`c₀/32` arm). Do them, but do not grind; honour the stop-rule.

### HONEST STATEMENT OF WHAT THE TWO WAVES DELIVER
`log(1/c)`: **631.58 → 86.23**, i.e. §D2's `e^{1264}` → `e^{172}`, with **no parameter changed
and no statement outside the two files**. Per TS-0's K3, this is explicit-constant hygiene and it
moves the `hN+ ∧ hηq` non-emptiness floor — it buys the **N11 door nothing**, because
`imsz_gives_fulcrum_witnesses` accepts every *constant* `C > 0`, so the door is gated on the
L-power, not the size of `log(1/c)`. Say this in the landing commit so no later reader misreads it.

---

## ⚠️ OPEN AT DISPATCH TIME — THE `-M` CAP MAY NOT BIND (check before you trust it)

The wrapper's `*.lean` branch now carries `lean -M 12000`. **Whether that cap actually binds is
UNVERIFIED as of this writing.** `-M` is enforced inside Lean, which is why it survives Darwin's
rlimit gap (`ulimit -v`/`-m` are measured no-ops here) — but a `decide +kernel` runaway lives in
kernel `whnf`, which may not sit on the allocation path Lean's counter checks. If it does not
bind, the cap is cosmetic and this wave's axiom-check step runs unprotected.

**TS-1 executor: make this wave produce the datum.** While your build/audit runs, and once at
wave exit, run

```
python3 /Users/jyh/projects/claude/saltworks/docs/ledger-tools/fleet_hygiene.py --brief
```

The evidence seat's detector parses each live Lean process's own `-M` out of its argv and reports
**cap versus RSS**. A process holding **more RSS than its own cap** is a live proof that `-M` does
not bind that workload — if you see that, **post it to `FLEET.md` with the exact numbers**, it
settles an open fleet ruling. Note the converse is *not* proof: caps present and unbreached only
means this run did not test them. TBal work is elaboration-heavy rather than `decide`-heavy, so it
is unlikely to be the breaching workload — but "unlikely" is not a bound, which is the whole
lesson of 2026-08-06.

## ⭐ MUTATION CHECK — TS-2's REAL EXIT TEST (borrowed from the silicon seat, 8/6)

A green build proves the γ-floors are **sufficient**. It does not prove they are **load-bearing** —
a numeral that is satisfied for an unrelated reason would also build green, and that is precisely
the vacuity failure this campaign has been hunting all day. The silicon seat's netlist work supplies
the missing positive control: **mutate one input and confirm the check FAILS.**

**So TS-2 does not exit on a green build alone. After the γ-honest arms land:**

1. Replace one exact-rational floor with the freeze's **inadmissible** value — e.g. `γ_Eρ`'s
   `5247/1700` → `3.0865` (which exceeds the true infimum by `2.941e−5`).
2. `saltbuild.sh Salt.SW.TBalTall`. **It MUST fail**, and it must fail at that side goal
   (`linarith [hσlo]` unable to close `3.0865 ≤ 14σ − 1009/100` at `σ = 16/17`).
3. Restore the exact rational; green again.
4. **Report both outcomes in the flags entry.** If the mutated build *passes*, the numeral is not
   load-bearing and something else is discharging the goal — **stop and flag it**, because that
   would mean the arm table is not measuring what it claims to measure.

The same check applies to S1: replace `1/40` with something `> 1` and `tbal_tau_le_split` must fail.
**Cost: two builds. Value: it converts "the wave built" into "the wave's numerals are the reason it
built."**

## EXIT TEST (both waves)
1. `saltbuild.sh Salt.SW.TBalR8`, then `saltbuild.sh Salt.SW.TBalTall` while iterating; full
   `saltbuild.sh` at wave exit with **`saltbuild EXIT=0`**, no new warnings.
2. **BOTH** `dh_repulsion_ordered` and `dh_repulsion_tall` build, same witness shape
   `⟨680, c, 14⟩`.
3. `#print axioms` on both = `[propext, Classical.choice, Quot.sound]`, via
   `saltbuild.sh ScratchTS1.lean` (unique name; **do not commit it**; `ScratchW45.lean` and
   `ScratchCT.lean` belong to other waves — do not disturb them).
4. TS-2 additionally: record the post-wave arm table as a comment beside both `c`-min blocks.

## IRON RULES
No `sorry`, no `native_decide`, no new axioms. **Never alter a blueprint statement to make a
proof go through** — flag it in `docs/blueprints/flags.md` instead. ~3 serious attempts per
piece, then flag and move on. **DO NOT TOUCH** any `Salt/HB/Lemma7*.lean` (another seat is wiring
them — `Salt/HB/` saw commits at 09:04 and 09:18 on 8/6), anything under `papers/`, `CLAUDE.md`,
`docs/MODEL_POLICY.md`, or blueprint node tables.
Commit style `play M: TAU-SHARP TS-N — …`, `[skip ci]` on its own line before the trailers,
**explicit pathspecs only**.

## HELD, NOT THIS SEAT'S — do not let an executor drift into these
TS-3 (S3+S4), the dossier §6 design ruling, and the `k → 1` scope are **statement-layer and HELD**
pending the design seat and the Captain (TS-0 K3 CONFIRMED-FATAL on the door claim; K2's new wall
W4 and the b-floor correction to 664.66). An executor that finds itself editing `ray_pow_bound`'s
statement, `a`/`m`/`b`, or `k` has left its wave.
