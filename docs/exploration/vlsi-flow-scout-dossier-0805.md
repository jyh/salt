All experiments are complete. Here is the dossier.

---

# VLSI-FLOW-SCOUT — DOSSIER

Machine-checked findings from this machine (M-series, darwin 25.5, Lean 4.32.0-rc1) plus three parallel research streams. Experiment files live in `/private/tmp/claude-501/-Users-jyh-projects-claude-salt/ea81b992-0821-4192-8f48-c0dcdcbc14c2/scratchpad/bvtest/`.

---

## A. THE KERNEL SIDE — the headline finding

### TRUE — `bv_decide` is present, mature, and arm64-native

`/Users/jyh/projects/claude/salt/lean-toolchain` pins `leanprover/lean4:v4.32.0-rc1`; `lakefile.toml` pins mathlib to the same tag. The toolchain ships:

- `Std/Tactic/BVDecide/` — verified bitblaster, AIG library, LRAT parser + checker **with soundness proofs** (`LRATCheckerSound.lean`, `CompactLRATCheckerSound.lean`).
- `~/.elan/toolchains/leanprover--lean4---v4.32.0-rc1/bin/cadical` — a **native arm64 CaDiCaL**, shipped in-toolchain. No install, no Docker, no PATH surgery.

Provenance: `leanprover/leansat` was archived 2024-08-29 and upstreamed into core; the first `bv_decide` commits in lean4 are 2024-08/09 (v4.12 era). **This is two-year-old, actively-maintained infrastructure, not a new toy.**

### TRUE — but the certificate is **NOT** checked by the kernel. It becomes an axiom.

This is the single most important fact in this dossier, and it contradicts the premise of the question.

`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:39` calls `nativeEqTrue`. `Lean/Meta/Native.lean` states its own purpose verbatim:

> "proofs by native evaluation (`native decide`, `bv_decide`). Such proofs involve a native computation using the Lean kernel, and then asserting the result of that computation as an axiom towards the logic."

It compiles `verifyBVExpr <expr> <cert>` to native code, runs it, and if `true`, **adds a fresh axiom** `<thm>._native.bv_decide.ax_N`. Confirmed by running it:

```
theorem rca8_correct (x y : BitVec 8) : rca8 x y = x + y := by
  unfold rca8 sumb carry; bv_decide
-- depends on axioms: [propext, Classical.choice, Quot.sound,
--                     rca8_correct._native.bv_decide.ax_1_5]
```

There is **no `+kernel` option** — I read the whole `BVDecideConfig` (`Std/Tactic/BVDecide/Syntax.lean:40-97`): `timeout`, `trimProofs`, `binaryProofs`, `acNf`, `andFlattening`, `embeddedConstraintSubst`, `structures`, `fixedInt`, `enums`, `graphviz`, `maxSteps`, `shortCircuit`, `solverMode`. Nothing about kernel checking.

**The easy-to-miss trap:** goals closed by `bv_normalize` preprocessing *alone* never call the solver and come out clean (`x + y = y + x` gave `[propext]`). So a casual axiom check can look clean while every real obligation carries an axiom. My independent prior-art stream reached this same conclusion separately.

**This violates salt Iron Rule 3 ("No `native_decide`, no new axioms") as literally written.**

### The mitigation that saves it — and it is a genuinely strong one

The axiom is not a black box. It is a **specific, concrete, externally re-checkable claim**: "this LRAT string refutes this CNF." Two consequences:

1. **Per-theorem, not blanket.** Upstream RFC [leanprover/lean4#12216](https://github.com/leanprover/lean4/issues/12216) (Breitner, 2026-01-28) deliberately replaced the old global `Lean.ofReduceBool` with these per-theorem axioms. Its stated goal #5: *"It's not quite feasible to write external checkers for some native computation tactic (like bv_decide). We want that to be possible, at least architecturally."* Architecturally intended; not yet delivered.
2. **A verified external checker exists today.** Lammich's Isabelle/HOL-verified `lrat_isa` and CakeML's `cake_lpr` both check LRAT. `bv_check "proof.lrat"` lets you pin certificates on disk. So you can honestly claim: *every SAT step is checked by an independently verified checker from a different prover*, which is arguably a **better** audit story than one kernel.

**Recommended framing:** "kernel-checked except the SAT steps, which are certificate-checked and independently re-validated by an Isabelle-verified LRAT checker." Do not claim "no axioms."

### TRUE — measured capability and scale limits (all measured today)

| Circuit | Scale | Time | Result |
|---|---|---|---|
| Gate-level ripple-carry adder, 8/32/64-bit | 8→64 FA | 1–2.5s | OK (64-bit needs `maxRecDepth`) |
| **RV32I ALU, 10 ops, 32-bit**, structural one-hot mux vs behavioural spec | — | **1.2s** | **OK** |
| **Batcher 8-way sorter, 8-bit keys, full sortedness** (BitVec level) | 19 comparators | **3.5s** | **OK** |
| Batcher 8-way, 16-bit keys | 19 comparators | 2.7s | OK |
| Batcher 16-way, 8-bit keys | 63 comparators | 5m18s | OK (needs `maxHeartbeats 0`) |
| **Gate-level comparator cell ≡ spec** (pure 2-input cells) | **81 gates** | **1.4s** | **OK** |
| Gate-level 4-way sorter, one output pair | 357 gates | 6.9s | OK |
| **Gate-level 8-way sorter, one output pair** | **1299 gates** | **>10 min** | **FAIL** |
| Shift-add multiplier, 8 / 12 / 16-bit | — | 2.7s / **2m17s** / **fail** | **wall at 12–16 bits** |

Four hard-won engineering findings:

1. **Multiplier wall at 12–16 bits.** Expected (bitblasting multipliers is the classic SAT-hard case). Any RISC-V M-extension work must avoid proving a multiplier monolithically.
2. **The gate-level wall is ELABORATION, not SAT.** Monolithic `unfold` of ~1300 gates blows up the term before CaDiCaL sees it. The 16-way sorter failure was `whnf` heartbeats, not solver timeout.
3. **Compositional proof completely dissolves this.** Prove the 81-gate comparator ≡ spec once (1.4s), then the fabric at BitVec level (3.5s) → gate-level correctness for the whole fabric in ~5s instead of >10 min. **This is the architecture, and it is empirically confirmed.**
4. **`Prod`-valued `if` defeats reification** (`sorryAx` with a confusing dump). Write designs in flattened scalar style — which is what a netlist is anyway. Structures in *hypotheses* are fine (`structures := true`).

**Sequential logic:** `bv_decide` is combinational-only. The working pattern (verified): `bv_decide` discharges the one-cycle obligation, plain Lean induction lifts to arbitrarily many cycles. This is a real advantage over riscv-formal, which is bounded-depth BMC. **Counterexamples work** — a deliberately broken carry chain returned `x = 1#4, y = 15#4` instantly, giving a usable debug loop.

### UNCERTAIN
- Whether kernel-run certificate checking lands upstream on any timeline (RFC open, no target).
- Whether `lrat_isa`/`cake_lpr` ingest Lean's *binary* LRAT format without conversion (`binaryProofs := true` by default; set false).

---

## B. THE FLOW

### TRUE
- **OpenLane 2 is now LibreLane, under the FOSSi Foundation.** Efabless was wound up; FOSSi adopted the project. Current release **3.0.6 (2026-08-02)**. Use [`librelane/librelane`](https://github.com/librelane/librelane), **not** `efabless/openlane2` (dead, redirects to `chipfoundry/openlane2`). OpenLane 1 README: *"not recommended for new projects."*
- **macOS ARM is a first-class, CI-tested target — this is the surprise.** LibreLane's CI has a `build-darwin` job on `macos-15` / `aarch64-darwin` that runs tests and **pushes binaries to a shared Nix cache**. Docs recommend Nix on macOS *because* it's native: *"built natively for both Intel and Apple Silicon-based Macs, unlike the AppImage or Docker which would use a Virtual Machine."* Realistic: **~15–25 min, ~8–10 GB**. Docker images are genuine multi-arch (`linux/arm64` + `linux/amd64`), no qemu.
- **ORFS is the bad path on macOS.** Supported-OS list has no macOS; `openroad/orfs` Docker images are **amd64-only** (qemu emulation). Native M-series builds are a documented grind.
- **Artifacts for equivalence checking** (`librelane/state/design_format.py`):
  - `runs/RUN_*/final/nl/<design>.logical_nl.v` — **post-route, logical cells only, no fills/decaps/taps. This is the one to import.**
  - `runs/RUN_*/*-yosys-synthesis/<design>.nl.v` — post-synthesis (glob the numeric prefix; it shifts between versions)
  - `final/spef/*.spef`, `final/gds/<design>.gds`
- **Cell semantics are machine-readable**, two ways: Liberty `function` attributes (`sky130_fd_sc_hd__tt_025C_1v80.lib`, `sg13g2_stdcell_typ_1p20V_25C.lib`) and Verilog models (`sky130_fd_sc_hd.v`, `sg13g2_stdcell.v` + `sg13g2_udp.v`).
- **Yosys alone:** `brew install yosys` (0.68, arm64 bottle) works, but for `eqy`/`sby` use the **OSS CAD Suite darwin-arm64** tarball.

### The macOS caveat you must state in any writeup
LibreLane issue [#522 "Cross-OS Determinism"](https://github.com/librelane/librelane/issues/522) is **open since July 2024**: identical inputs give different results on macOS vs Linux, maintainers pointing at synthesis. Issue #825 (2025-11-27) is a concrete instance — **1170 KLayout DRC errors on Mac, DRC-clean on Linux**. Develop on Mac; **run the final pass on Linux before claiming any number or taping out.**

### UNCERTAIN
- `Yosys.EQY` is in the Classic flow but self-described *"Experimental… you are expected to provide your own EQY script"*, and it **silently skips on any non-sky130A PDK** (so IHP gets nothing). Don't count on it. Note it checks RTL-vs-netlist, not the seam we care about.

---

## C. REAL SILICON

### TRUE
- **Efabless ceased operations late Feb / early Mar 2025.** Your recollection is correct. It killed chipIgnite mid-flight and stranded TT08/TT09. Assets → **ChipFoundry** (Umbralogic Technologies, ex-Efabless staff, announced 2025-09-03). OpenLane → **LibreLane / FOSSi**. Caravel survives as `chipfoundry/caravel`.
- **TinyTapeout is alive and is the cheap path. Two windows open:**

| Shuttle | Process | **Deadline** | Est. delivery |
|---|---|---|---|
| **TTSKY26c** | sky130A | **2026-09-07 20:00 UTC** | 2027-05-12 |
| **TTIHP26b** | IHP SG13G2 | **2026-09-21 20:00 UTC** | 2027-08-16 |

  **€70/tile**, DevKit €300 (one subsidized at €100 per submission). **Minimum viable submission ≈ €185 (~$200).** Tile ≈ 160×100 µm ≈ **1000 gates**; fixed I/O (clk, rst_n, 8 in / 8 out / 8 bidir); up to **8×2 tiles**… actually up to **8×4 = 32 tiles ≈ 0.6 mm², ~32k gates, €2,240**. Accepts either RTL (they harden it via LibreLane) **or your own precompiled GDS** (analog/custom-GDS template; no metal5 on sky130). Caveat: TTSKY26c DevKit PCBs are **sold out (0/80)**.
- **Best area-per-dollar: wafer.space Run 3** — GF180MCU 180nm, **$2,000** for 1.73 mm² core + **1,000 bare dies** (early bird by **2026-09-30**), GDS due **2026-12-16**, parts Q2 2027. +$1,500 chip-on-board. You bring your own pad ring. No NDA.
- **ChipFoundry chipIgnite: $14,950**, next commitment gate **2026-10-08** (CI2612), delivery 2027-05-25. GDSII-only submission, 100 QFN parts.
- **Google/SkyWater OpenMPW is dead** (wound down Nov 2023; PDKs to CHIPS Alliance). MOSIS 2.0, Europractice, and Muse are institutional/NDA — not individual routes.

**Sizing check:** my Batcher 8×8-bit fabric measures **1299 gates** ≈ 1–2 TT tiles. A comfortable fit. An RV32I-subset core (~5–15k gates) is 8–16 tiles (€560–1,120).

### UNCERTAIN
- Whether a private individual (no institution) can sign IHP's Open Silicon Participation Agreement.
- **"A GDSII" is not portable between programs** — each wants its own frame. Budget rework.

---

## D. PRIOR ART — the gap is real

### TRUE — nobody has done this

**No one has ever kernel-checked an equivalence between a proof-assistant design and a gate-level netlist from a real synthesis+P&R flow, let alone to GDSII.** The frontier and exactly where each chain breaks:

| Chain | Verified floor | First unverified link |
|---|---|---|
| **Lutsig** (Lööw, HOL4, CPP'21) — *the frontier* | **tech-mapped FPGA LUT netlist** | Verilog pretty-printer, then Vivado P&R + bitstream |
| Kôika (PLDI'20) | mini-RTL netlist *inside Coq*; compiler proved | *"thin unverified pretty-printing layer"* to Verilog |
| Kami (ICFP'17) | module refinement; designs proved | Coq extraction → `bsc` → Vivado (*"the entire synthesis process is part of Kami's trusted base"*) |
| Silver Oak / Cava (Google) | Coq circuit designs (AES/HMAC for OpenTitan) | the Coq→SystemVerilog generator. **Archived 2021; never landed upstream in OpenTitan** |
| VAMP/Verisoft | PVS gate-level design (Tomasulo + IEEE-754 FPU, 8 person-years) | `pvs2hdl` unverified; **hand-substituted Xilinx macros** replaced verified adders |
| Centaur/ACL2 (shipping x86) | RTL via SVEX; symbolic simulator itself proved (GL) | **VL Verilog front end trusted**; RTL→gates by commercial EQ checker |
| Intel Forte/STE | gate/transistor netlist *models* | C-coded STE engine, deliberately never verified |

**The only formally verified processor ever fabricated is FM9001** (Hunt & Brock, Nqthm → LSI Logic, ~1990–92) — and its DE→NDL translator was never verified.

Three findings that should shape the plan:

1. **Kôika proves the compiler but leaves designs unproved; Kami proves designs but trusts the compiler. Nobody has both halves in one system.**
2. **`bv_decide`'s AIG/CNF infrastructure descends from the ACL2/Centaur AIGNET lineage** — the verified-AIG technology built for x86 verification is now in Lean's stdlib. The missing step is exactly making the certificate check kernel-run.
3. **HWMCC 2024 made certificates mandatory** (Froleyks et al., CAV'25) and **44 of 1536 certificates were invalid** — *"Initially, all model checkers produced invalid certificates."* Certification catches real bugs. And Intel's own DVCon 2007 "FEV's Greatest Bloopers" records **two CPUs that taped out equivalence-check-clean and would not boot.** The seam you'd be attacking is the one with a documented dead-silicon record.

### TRUE — Lean 4 hardware work exists but is embryonic (all 2025–26)
- **Sail→Lean backend is official and in-tree** (first commit 2024-09-23; shipped in Sail 0.19, 2025-03-11, marked *"HIGHLY EXPERIMENTAL"*). [`opencompl/sail-riscv-lean`](https://github.com/opencompl/sail-riscv-lean) regenerates daily: **175,877 lines, 4,779 defs, 0 errors**. The official `riscv/sail-riscv` repo added an **executable Lean emulator** (PR #1777, **2026-07-16**) passing riscv-tests. **This is a large, free asset for week 2.**
- **Verilean/sparkle** — a Lean 4 HDL → SystemVerilog, created 2026-01-16, ~102★, uses `bv_decide` via `#verify_eq`. **Its emitter is unverified. No GDSII, no tapeout.** This is the nearest neighbour; check it before writing your own emitter.
- **AWS**: ~500k lines of Lean for a verified Trainium compiler (de Moura, FLoC 2026) — verified compiler *to* a chip, not verification *of* one.
- Lean Zulip's hardware thread (2020) concluded there were no active Lean hardware projects. That is no longer quite true, but nearly.

### What would genuinely be first
Kernel-checked (or certificate-checked) equivalence **between a Lean design and the actual post-P&R gate netlist**, carried to GDSII and fabricated. Nobody has done it. **The claim is real and defensible** — provided the trust boundary is stated honestly (see A).

---

## E. THE VERILOG EXTRACTION QUESTION — recommendation

**Do not choose between (i) and (ii). The right move makes the emitter untrusted.**

Option (i) as posed is a trap: `bv_decide` cannot read Verilog, so "prove hand-written Verilog equivalent to the Lean model" still requires a Verilog→Lean importer. Same parsing problem, more hand-written RTL.

**RECOMMENDED ARCHITECTURE — emit untrusted, import trusted:**

1. **Lean → Verilog emitter: UNTRUSTED, ~200–300 lines.** Walk the Lean structural design, print `assign` statements. A bug here cannot produce a false theorem — it produces a netlist that *fails* step 3.
2. **Run LibreLane** (untrusted, millions of lines — Yosys, ABC, OpenROAD) → `final/nl/<design>.logical_nl.v` + GDS.
3. **Gate netlist → Lean importer: TRUSTED, ~300 lines.** Parse flat structural Verilog into a Lean definition over Bool wires. Then `bv_decide` proves it equals the Lean spec.
4. **Cell semantics: TRUSTED, ~30 one-line Lean defs.** Print the cell set actually used; hand-model each (`sky130_fd_sc_hd__nand2_1 ⟹ fun a b => !(a && b)`). Far more auditable than parsing Liberty.

**Why this wins:** synthesis and P&R fall *out* of the TCB entirely — a Yosys bug is caught, not trusted. The TCB shrinks to a ~300-line parser plus ~30 one-line cell models, both reviewable in an afternoon. **This is strictly stronger than Kami, Kôika, Cava, and VAMP**, all of which trust their emitter.

Empirically confirmed today: the compositional discipline (§A finding 3) is what makes step 3 scale — prove per-module, compose at BitVec level.

**Check `Verilean/sparkle` first** for the emitter; borrowing an untrusted emitter costs nothing.

---

## FEASIBILITY VERDICT

### (1) Switch vertical slice in ~1 week — **FEASIBLE, good confidence**

The Lean side is already substantially done. I proved the 19-comparator Batcher fabric sorted in 3.5s and the 81-gate gate-level comparator ≡ spec in 1.4s, today, on this machine, with zero installation. Realistic split: LibreLane/Nix bring-up ~0.5 day (CI-tested path); emitter ~1 day; **importer ~2–3 days (the real work)**; proofs ~0.5 day; GDS + DRC ~1 day. Fits, with the importer as the only genuine unknown.

### (2) RISC-V-subset core in the following week — **NOT FEASIBLE as stated; feasible if scoped down**

The ALU is a solved problem (1.2s, measured). What does *not* fit in a week: sequential decomposition across a whole datapath, the register file, instruction decode, hazard logic, integrating the 176k-line `sail-riscv-lean` model, and gate-level import at 5–15k gates. The multiplier wall (12–16 bits) rules out M-extension. **Scope to: ALU + register file + a 3–5 instruction single-cycle datapath, spec written by hand in Lean (not Sail-derived).** Call it "a verified RISC-V *datapath*," not "a verified RISC-V core." Budget 3–4 weeks for anything deserving the word "core."

---

## TOP 5 RISKS

| # | Risk | Mitigation |
|---|---|---|
| 1 | **The native axiom breaks the headline claim** and violates Iron Rule 3 as written. | Reframe as certificate-checked; pin LRAT files via `bv_check`; re-validate with Isabelle-verified `lrat_isa`. Set `binaryProofs := false`. **Decide this before any code.** |
| 2 | **Gate-level import doesn't scale** — monolithic proofs die at ~1300 gates (measured, elaboration not SAT). | Compositional discipline: per-module cell lemmas + BitVec-level composition. **Confirmed working (81 gates in 1.4s).** Design the importer to emit per-module lemmas from day one. |
| 3 | **macOS cross-OS non-determinism** ([#522](https://github.com/librelane/librelane/issues/522), open 2 yrs) — DRC-clean on Linux, 1170 errors on Mac. | Develop on Mac; run the final/publishable pass on Linux. Never tape out from a Mac run. |
| 4 | **Importer is trusted and could be wrong** — a bug makes the whole chain vacuous. | Keep it ≤300 lines; hand-model only cells actually used; cross-validate by round-tripping through Yosys `eqy` and by mutation-testing (inject netlist faults, confirm `bv_decide` produces counterexamples — the mechanism works, verified today). |
| 5 | **Shuttle deadline is a hard wall** — TTSKY26c **Sept 7**, TTIHP26b **Sept 21**, ~4–6 weeks out. Miss it and silicon slips ~4 months. | Decide silicon intent in week 1, not week 3. TT accepts precompiled GDS, so the flow needn't be perfect — only DRC-clean and tile-shaped. |

---

## THE SINGLE DECISION THAT MOST CHANGES THE PLAN

**Whether a per-theorem `_native.bv_decide.ax` axiom is acceptable in the trust story.**

Everything hangs on it:

- **If YES** (recommended — reframed as "certificate-checked, independently re-validated by an Isabelle-verified LRAT checker"): the plan above runs, week 1 is comfortable, and the result is still genuinely first-of-its-kind, because *no existing system* — Kami, Kôika, Cava, VAMP, Centaur, Intel — has a smaller TCB at the RTL↔gates seam than the one proposed here.
- **If NO** (Iron Rule 3 enforced literally, zero new axioms): `bv_decide` is unusable, and with it the entire approach. You would need a kernel-run LRAT checker — an open upstream problem ([RFC #12216](https://github.com/leanprover/lean4/issues/12216) goal 5, explicitly unachieved). That is a research project, D-tier, not a 2-week demo.

This is a Fable/JYH-tier call, and it should be made before a single line is written. Secondary decision, needed within days: whether real silicon is in scope — because that converts the Sept 7 / Sept 21 deadlines into the schedule's forcing function.

**Sources:** [librelane/librelane](https://github.com/librelane/librelane) · [LibreLane macOS Nix install](https://librelane.readthedocs.io/en/latest/installation/nix_installation/installation_macos.html) · [LibreLane #522](https://github.com/librelane/librelane/issues/522) · [FOSSi — LibreLane 3.0](https://fossi-foundation.org/librelane/blog/2026-03-25-website_release_3-0) · [TinyTapeout](https://tinytapeout.com/chips/) · [wafer.space pricing](https://wafer.space/price.html) · [ChipFoundry](https://chipfoundry.io/) · [ChipFoundry acquires Efabless assets](https://finance.yahoo.com/news/chipfoundry-acquires-efabless-assets-propel-171500837.html) · [IHP-Open-PDK](https://github.com/IHP-GmbH/IHP-Open-PDK) · [Lean RFC #12216](https://github.com/leanprover/lean4/issues/12216) · [opencompl/sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean) · [mit-plv/koika](https://github.com/mit-plv/koika) · [mit-plv/kami](https://github.com/mit-plv/kami) · [project-oak/silveroak](https://github.com/project-oak/silveroak) · [riscv-formal](https://github.com/YosysHQ/riscv-formal) · [oss-cad-suite-build](https://github.com/YosysHQ/oss-cad-suite-build) · [fossi-foundation/open-pdks](https://github.com/fossi-foundation/open-pdks)
