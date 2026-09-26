# THE FULCRUM-SHAPE CENSUS — by machine (O13 item 3, first cut)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/fulcrum_census.py` · staleness gate: `python3 scripts/fulcrum_census.py --check` · self-test: `python3 scripts/fulcrum_census.py --self-test`.
> Base: last commit touching `Salt/` = `ddc2511d` · source digest `7459fcd147e4efa5` (item 1's digest: sha256 over every `Salt/**/*.lean`, sorted by path). Built on `scripts/results_catalogue.py` + `scripts/methods_catalogue.py` (imported).

⚠️ **Nothing here bears on twin primes until it does.** This is a CENSUS of candidates for the fulcrum sweep (QUEUE item 15 lane (a)); the seat prices each by class (A–D) before any Lean. A shape is not a result.

## LIMITS — read these before any count below

- **Source-level parse, no elaboration** (item 1's limits all apply: macros, `alias`, `to_additive`, notation are invisible; implicit `{}`/`⦃⦄` binders are NOT walked; section `variable`s count only when named in the statement or `include`d).
- **Polarity is SYNTACTIC.** `¬`, `Not`, and `… → False` flip; nothing else does. A P reached only through an unfolded definition, `↔`, `≠`-style sugar, `∨` inside a binder, or a `∃` is NOT counted. `P x → False` in a BINDER is a ¬F-consumer; a declaration whose CONCLUSION is `False` is a refutation (¬F-producer `via False`) of the conjunction of its corpus premises, and its premises are not F-consumers.
- **Arrows under an `∃` are split as item 1 splits them:** a conclusion `∃ c, 0 < c ∧ ∀ x, A x → ¬ P x` is cut at its depth-0 `→`, so `A` counts as a premise (of the inner `∀`, which it is) and `¬ P` as the conclusion. Such a ¬F-producer is `conditional` whenever `A` is a corpus Prop, though the result proves the `∃` outright.
- **`engine` occurrences** are premises of a hypothesised implication (`hEngine : P → Q`), recorded at the binder's polarity. Nested implications deeper than one level are walked with the same rule and are imprecise (the polarity of `((P → Q) → R)` is not flipped).
- **Consumers are counted over EVERY declaration in `Salt/`** (theorem/lemma/def/abbrev/instance/opaque, not Prop-valued definitions themselves), not only audited results. Item 2's `hang` column (audited conditional results only) is carried beside it.
- **F-producers are item 2's, verbatim** (unconditional = DISCHARGED, `!g` guarded; conditional; ∃-witness). ¬F-producers are this script's: `¬ P` conclusions (one level of `∧` under the `¬`), unconditional unless another corpus Prop sits as a direct positive binder.
- **Disjunction sites are VISIBLE ONLY:** a theorem conclusion that is a top-level `∨`, or a Prop-def body that is one. A theorem concluding a NAMED disjunction (e.g. `HeathBrownDichotomy`) is not unfolded — the Prop-def row carries it.
- **Case splits are a TOKEN SCAN** of proof bodies: `by_cases [h :] P`, `em P`, `Classical.em P`, `Decidable.em P`, `Classical.byCases P`, with P's head resolved against the corpus Prop set in the declaration's namespace/open context. A split on an unfolded or `have`-named proposition is invisible.
- **The classes are SHAPES, not verdicts.** FULCRUM-SHAPED says both polarities are consumed somewhere; it does not say the two horns are the SAME instance of P (arguments are not compared) nor that either horn is unconditional.
- **A finding about item 1, surfaced by this census:** 73 declarations see a corpus Prop ONLY under `¬` in their binders; **31 of them are AUDITED results that item 1 classes `unconditional`** (its binder walk reads `¬ P` as head `Not`, not P). Listed at the foot. Item 2's DISCHARGED status inherits this: a producer whose only corpus premise is a `¬ P` binder counts as unconditional.

## Population receipt

| declarations indexed | corpus Prop-valued names | consumer declarations scanned | audited results | FULCRUM-SHAPED | HALF-SHAPED | neither | disjunction/case-split sites |
|---|---|---|---|---|---|---|---|
| 22703 | 668 | 22025 | 9087 | 13 | 318 | 337 | 86 |

Per-polarity totals over the 668 Props: with F-consumers 519 · with ¬F-consumers 21 · with F-producers (any kind) 438 · with ¬F-producers (any kind) 59.

## FULCRUM-SHAPED (13) — both polarities consumed

Counts: F-cons = F-consumers (direct/engine) · ¬F-cons = ¬F-consumers (direct/engine) · F-prod = unconditional/conditional/∃-witness · ¬F-prod = unconditional/conditional/via False · sites = disjunction/case-split.

| P | defined at | status | F-cons | ¬F-cons | F-prod | ¬F-prod | sites | ¬F-consumer examples | F-consumer examples |
|---|---|---|---|---|---|---|---|---|---|
| `Salt.MR.NearRatTight` | Salt/MR/BigXiArc.lean:566 | DISCHARGED | 54 (50/15) | 4 (4/0) | 2/9/0 | 0/0/0 | 0/0 | `Salt.MR.approx_reduced` (Salt/MR/MinorArcExit.lean:333), `Salt.MR.exists_large_den_of_minorTight` (Salt/MR/BigXiArc.lean:712), `Salt.MR.exists_large_den_of_not_nearRatTight` (Salt/MR/BigXiArc.lean:684) +1 | `Salt.MR.G2Scaffold.m4_hbd_of_live_L` (Salt/MR/M4RowLinear.lean:2335), `Salt.MR.G2Scaffold.m4_hbd_of_live_L_gk` (Salt/MR/M4RowLinear.lean:2445), `Salt.MR.G2Scaffold.m4_hbd_of_live_split_L` (Salt/MR/M4RowLinear.lean:1616) +51 |
| `Salt.MR.CapFreeFloor` | Salt/MR/CapFreeArm.lean:111 | DISCHARGED | 9 (9/0) | 6 (6/0) | 4/2/0 | 0/0/0 | 0/5 | `Salt.MR.a2Rows_of_cap` (Salt/MR/ThmA2Rows.lean:464), `Salt.MR.a2Rows_of_cap_L` (Salt/MR/ThmA2Linear.lean:1251), `Salt.MR.a2Rows_of_cap_L_gk` (Salt/MR/ThmA2Linear.lean:1962) +3 | `Salt.MR.a2Rows_of_capfree` (Salt/MR/ThmA2Rows.lean:305), `Salt.MR.a2Rows_of_capfree_L` (Salt/MR/ThmA2Linear.lean:1098), `Salt.MR.a2Rows_of_capfree_L_gk` (Salt/MR/ThmA2Linear.lean:1834) +6 |
| `Salt.BrunLower.chi` | Salt/BrunLower/Defs.lean:149 | DISCHARGED | 10 (9/1) | 3 (3/0) | 3/2/0 | 0/0/0 | 0/8 | `Salt.BrunLower.forcing` (Salt/BrunLower/Lemma3.lean:468), `Salt.HB.exists_firstFailure` (Salt/HB/RosserDim4FL.lean:557), `Salt.HB.failSet_forced_count` (Salt/HB/RosserDim4FL.lean:710) | `Salt.BrunLower.chi_add_smaller_prime` (Salt/BrunLower/Defs.lean:235), `Salt.BrunLower.chi_dvd_closed` (Salt/BrunLower/Defs.lean:202), `Salt.BrunLower.chi_imp_windowed` (Salt/BrunLower/Defs.lean:177) +7 |
| `Salt.Entropy.Chowla.logChowla2Fails` | Salt/Entropy/Chowla/ChowlaFailure.lean:59 | OPEN | 3 (3/0) | 7 (5/2) | 0/0/0 | 0/199/24 | 0/0 | `Salt.Entropy.Chowla.sign_split_fifth` (Salt/Entropy/Chowla/SignSplit.lean:278), `Salt.Entropy.Chowla.sign_split_of_not_fails` (Salt/Entropy/Chowla/SignSplit.lean:209), `Salt.Entropy.Chowla.sign_split_quarter_log` (Salt/Entropy/Chowla/SignSplit.lean:252) +4 | `Salt.Entropy.Chowla.h211_of_logChowla2Fails` (Salt/Entropy/Chowla/ChowlaFailure.lean:120), `Salt.Entropy.Chowla.singleCorr_of_fails` (Salt/Entropy/Chowla/ChowlaFailure.lean:81), `Salt.Entropy.Chowla.singleCorr_of_fails_h_one` (Salt/Entropy/Chowla/ChowlaFailure.lean:239) |
| `Salt.Entropy.Chowla.logChowlaFailsAff` | Salt/Entropy/Chowla/AffineFork.lean:69 | OPEN | 3 (3/0) | 5 (5/0) | 0/0/0 | 2/10/1 | 0/0 | `Salt.Entropy.Chowla.affWindow_survivorMass_ge` (Salt/Entropy/Chowla/AffineFork.lean:107), `Salt.Entropy.Chowla.exists_affSurvivor_of_not_failsAff` (Salt/Entropy/Chowla/AffineFork.lean:153), `Salt.Entropy.Chowla.gradedAffHeadAt_g12b_of_at_regime` (Salt/Entropy/Chowla/StrideShellBand.lean:369) +2 | `Salt.Entropy.Chowla.h211_aff` (Salt/Entropy/Chowla/StrideBridge.lean:665), `Salt.Entropy.Chowla.singleCorr_of_failsAff` (Salt/Entropy/Chowla/StrideFork.lean:138), `Salt.Entropy.Chowla.singleCorr_of_failsAff'` (Salt/Entropy/Chowla/StrideFork.lean:176) |
| `Salt.Fulcrum.FulcrumQualityMin` | Salt/Fulcrum/Basic.lean:61 | OPEN | 3 (2/1) | 2 (2/0) | 0/2/0 | 0/0/0 | 0/1 | `Salt.Fulcrum.not_fulcrum_implies_noSiegelZeros` (Salt/Fulcrum/Dichotomy.lean:82), `Salt.SW.not_fulcrum_siegelFree_SW` (Salt/SW/StandoffGate.lean:805) | `Salt.Fulcrum.fulcrum_dichotomy` (Salt/Fulcrum/Dichotomy.lean:102), `Salt.HB.crown_handover_k1` (Salt/HB/CrownTheorem1.lean:6577), `Salt.HB.hEngine_of_N7` (Salt/HB/CrownTheorem1.lean:6925) |
| `Salt.HB.FulcrumQualityPoly` | Salt/HB/CrownTheorem1.lean:6338 | OPEN | 4 (3/1) | 1 (1/0) | 0/0/0 | 0/0/0 | 0/1 | `Salt.HB.not_fulcrumPoly_implies_noSiegelZerosPoly` (Salt/HB/CrownTheorem1.lean:6414) | `Salt.HB.crown_handover` (Salt/HB/CrownTheorem1.lean:6902), `Salt.HB.fulcrumQualityMin_of_poly` (Salt/HB/CrownTheorem1.lean:6519), `Salt.HB.fulcrum_dichotomy_poly` (Salt/HB/CrownTheorem1.lean:6463) +1 |
| `Salt.MR.WindowSmooth` | Salt/MR/MobiusChiRamare.lean:175 | DISCHARGED | 3 (3/0) | 2 (2/0) | 4/0/0 | 0/0/0 | 0/1 | `Salt.MR.lamTailWeight_eq_zero_of_not_smooth` (Salt/MR/LambdaChiRamare.lean:192), `Salt.MR.ramTailWeight_eq_zero_of_not_smooth` (Salt/MR/MobiusChiRamare.lean:204) | `Salt.MR.lamTailWeight_apply_of` (Salt/MR/LambdaChiRamare.lean:177), `Salt.MR.ramTailWeight_apply_of` (Salt/MR/MobiusChiRamare.lean:200), `Salt.MR.windowSmooth_dvd_bandPow` (Salt/MR/RamareMassTail.lean:201) |
| `Salt.Chen.IsP2` | Salt/Chen/WeightTrivia.lean:270 | OPEN | 1 (1/0) | 3 (2/1) | 0/1/6 | 1/0/0 | 0/2 | `Salt.Chen.chen_weight_le_indicator` (Salt/Chen/WeightTrivia.lean:373), `Salt.Chen.chen_weight_struct` (Salt/Chen/WeightTrivia.lean:391), `Salt.Chen.not_isP2_cardFactors_ge_three` (Salt/Chen/WeightTrivia.lean:353) | `Salt.Chen.isP2_mono` (Salt/Chen/Assembly.lean:375) |
| `Salt.MR.MaskSmooth` | Salt/MR/MobiusChiRamareUnion.lean:116 | DISCHARGED | 2 (2/0) | 2 (2/0) | 4/0/0 | 0/0/0 | 0/1 | `Salt.MR.lamTailWeightMask_eq_zero_of_not_smooth` (Salt/MR/LambdaChiMask.lean:150), `Salt.MR.maskTailWeight_eq_zero_of_not_smooth` (Salt/MR/MobiusChiRamareUnion.lean:204) | `Salt.MR.lamTailWeightMask_apply_of` (Salt/MR/LambdaChiMask.lean:134), `Salt.MR.maskTailWeight_apply_of` (Salt/MR/MobiusChiRamareUnion.lean:200) |
| `Salt.MR.Squarefull` | Salt/MR/HalaszSeam.lean:154 | DISCHARGED | 3 (3/0) | 1 (1/0) | 3/0/0 | 1/0/0 | 0/0 | `Salt.MR.sPart_eq_zero_of_not_squarefull` (Salt/MR/SPartCore.lean:170) | `Salt.MR.cubePartOf_le` (Salt/MR/SPartCore.lean:714), `Salt.MR.sqPartOf_le` (Salt/MR/SPartCore.lean:706), `Salt.MR.sqPartOf_sq_mul_cubePartOf_cube` (Salt/MR/SPartCore.lean:682) |
| `Salt.MR.NearRat` | Salt/MR/BigXiArc.lean:144 | DISCHARGED | 1 (1/0) | 2 (2/0) | 3/3/0 | 0/0/0 | 0/0 | `Salt.MR.exists_large_den_of_minor` (Salt/MR/BigXiArc.lean:331), `Salt.MR.exists_large_den_of_not_nearRat` (Salt/MR/BigXiArc.lean:274) | `Salt.MR.nearRat_mono` (Salt/MR/BigXiArc.lean:188) |
| `Salt.MR.MemS` | Salt/MR/Sec9Glue.lean:118 | OPEN | 1 (1/0) | 1 (1/0) | 0/0/0 | 4/0/0 | 0/6 | `Salt.MR.memSCoeff_eq_zero_of_not_memS` (Salt/MR/M4Band.lean:359) | `Salt.MR.memSPunct_of_memS` (Salt/MR/M4Puncture.lean:69) |

## HALF-SHAPED — top 40 of 318 by F-consumer count (status OPEN, no ¬F-consumer: *what would ¬P give?*)

| # | P | defined at | status | F-cons (direct/engine) | audited hang (item 2) | ∃-witness producers | cond. producers | ¬F-prod | sites | F-consumer examples |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `Salt.MR.ShortIntervalDatum` | Salt/MR/GradeConst.lean:52 | OPEN | 128 (128/4) | 97 | `Salt.MR.exists_shortIntervalDatum` (Salt/MR/GradeConst.lean:57) | 0 | 0 | 0 | `Salt.MR.TLG_feed_of_supply_local` (Salt/MR/USetGradedBalance.lean:363), `Salt.MR.TL_feed_of_supply` (Salt/MR/USetBalance.lean:283), `Salt.MR.a2Rows_of_cap` (Salt/MR/ThmA2Rows.lean:464) +125 |
| 2 | `Salt.MR.DoorBaseFrame` | Salt/MR/M4ArithPrime.lean:109 | OPEN | 93 (93/0) | 41 | - | 3 | 0 | 0 | `Salt.MR.doorFuseFrame_pool'_of_gates` (Salt/MR/M4ArithPrime.lean:148), `Salt.MR.doorFuseFrame_pool'_of_gates_L` (Salt/MR/M4ArithZeroLinear.lean:709), `Salt.MR.doorFuseFrame_pool'_of_gates_L_gk` (Salt/MR/M4ArithZeroLinear.lean:1311) +90 |
| 3 | `Salt.MR.DoorArithFrameRho_L` | Salt/MR/ArithPageLinear.lean:315 | OPEN | 92 (92/0) | 71 | - | 5 | 0 | 0 | `Salt.MR.DoorArithFrameRho_L.armWeak` (Salt/MR/ArithPageLinear.lean:356), `Salt.MR.DoorArithFrameRho_L.logInvRho_nonneg` (Salt/MR/ArithPageLinear.lean:349), `Salt.MR.DoorArithFrameRho_L.loglogX_ge` (Salt/MR/ArithPageLinear.lean:363) +89 |
| 4 | `Salt.MR.DoorArithFrameRho` | Salt/MR/M4ArithRho.lean:176 | OPEN | 91 (91/0) | 16 | - | 6 | 0 | 0 | `Salt.MR.DoorArithFrameRho.armWeak` (Salt/MR/M4ArithRho.lean:217), `Salt.MR.DoorArithFrameRho.logInvRho_nonneg` (Salt/MR/M4ArithRho.lean:210), `Salt.MR.DoorArithFrameRho.loglogX_ge` (Salt/MR/M4ArithRho.lean:224) +88 |
| 5 | `Salt.MR.CofactorSocket` | Salt/MR/CapFreeArm3.lean:258 | OPEN | 79 (79/0) | 47 | - | 21 | 0 | 0 | `Salt.MR.CofactorSocket.mono` (Salt/MR/CapFreeArm3.lean:264), `Salt.MR.a2Rows_of_capfree3` (Salt/MR/ThmA2Rows.lean:892), `Salt.MR.a2Rows_of_capfree3'` (Salt/MR/A3Middle.lean:804) +76 |
| 6 | `Salt.MR.DoorArithFrame` | Salt/MR/M4ArithPage.lean:291 | OPEN | 45 (45/0) | 26 | - | 0 | 0 | 0 | `Salt.MR.DoorArithFrame.armWeak` (Salt/MR/M4ArithPage.lean:323), `Salt.MR.DoorArithFrame.loglogX_ge` (Salt/MR/M4ArithPage.lean:329), `Salt.MR.DoorArithFrame.one_lt_logH` (Salt/MR/M4ArithPage.lean:320) +42 |
| 7 | `Salt.MR.DoorRowZeroBase_L_gk` | Salt/MR/M4RowSpineLinear.lean:1433 | OPEN | 44 (44/0) | 35 | - | 0 | 0 | 0 | `Salt.MR.m4_chiSummedFreeRow_of_doorArith_zero_L_gk` (Salt/MR/M4ArithZeroLinear.lean:1033), `Salt.MR.m4_chiSummedFreeRow_of_doorArith_zero_L_gk_kwide` (Salt/MR/M4ArithZeroLinear.lean:1481), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L_gk` (Salt/MR/M4RowsChiPrimeLinear.lean:724) +41 |
| 8 | `Salt.HB.N9Regime` | Salt/HB/CrownTheorem1.lean:442 | OPEN | 39 (39/0) | 19 | - | 0 | 0 | 0 | `Salt.HB.chiOne_kill_at_hb_point` (Salt/HB/CrownTheorem1.lean:2196), `Salt.HB.dh_ceiling_box` (Salt/HB/CrownTheorem1.lean:1151), `Salt.HB.dh_floor_ball` (Salt/HB/CrownTheorem1.lean:1284) +36 |
| 9 | `Salt.MR.DoorFuseFrame` | Salt/MR/M4Assembly.lean:440 | OPEN | 30 (30/0) | 21 | - | 1 | 0 | 0 | `Salt.MR.doorFuseFrame_reEps` (Salt/MR/S12Compose.lean:696), `Salt.MR.logChowla2_capstone_conditional` (Salt/MR/S12Compose.lean:283), `Salt.MR.logChowla2_capstone_conditional_perBlock` (Salt/MR/S12Compose.lean:471) +27 |
| 10 | `Salt.MR.DoorFuseFrame_gk` | Salt/MR/M4Assembly.lean:656 | OPEN | 30 (30/0) | 0 | - | 1 | 0 | 0 | `Salt.MR.doorFuseFrame_reEps_gk` (Salt/MR/S12Compose.lean:971), `Salt.MR.logChowla2_capstone_conditional_gk` (Salt/MR/S12Compose.lean:983), `Salt.MR.logChowla2_capstone_conditional_perBlock_gk` (Salt/MR/S12Compose.lean:1143) +27 |
| 11 | `Salt.MR.M4DoorGates_L` | Salt/MR/M4LadderLinear.lean:939 | OPEN | 30 (30/0) | 8 | - | 0 | 2 | 0 | `Salt.MR.G2Scaffold.m4_cover_assembly_L` (Salt/MR/M4RowLinear.lean:1527), `Salt.MR.G2Scaffold.m4_cover_assembly_blk_L` (Salt/MR/M4RowLinear.lean:1549), `Salt.MR.G2Scaffold.m4_cover_assembly_supQ_L` (Salt/MR/M4RowLinear.lean:2163) +27 |
| 12 | `Salt.MR.DoorFuseFrame_L_gk` | Salt/MR/M4RowAssemblyLinear.lean:280 | OPEN | 28 (28/0) | 18 | - | 0 | 0 | 0 | `Salt.MR.m4_arith_door_exit_of_delta_L_gk` (Salt/MR/M4ArithRhoLinear.lean:255), `Salt.MR.m4_arith_door_exit_rho_L_gk` (Salt/MR/M4ArithRhoLinear.lean:219), `Salt.MR.m4_chiSummedFreeRow_of_doorArithRho_L_gk` (Salt/MR/M4ArithRhoLinear.lean:186) +25 |
| 13 | `Salt.MR.DoorBandBase_L_gk` | Salt/MR/M4SocketLinear.lean:450 | OPEN | 27 (27/0) | 25 | - | 4 | 0 | 0 | `Salt.MR.flat_capstone_uniform` (Salt/MR/S16Uniform.lean:567), `Salt.MR.flat_capstone_uniform_kwide` (Salt/MR/S16Uniform.lean:1823), `Salt.MR.flat_capstone_uniform_win` (Salt/MR/S16Uniform.lean:1239) +24 |
| 14 | `Salt.MR.DoorBandBase_gk` | Salt/MR/M4SocketDischarge.lean:545 | OPEN | 27 (27/0) | 3 | - | 2 | 0 | 0 | `Salt.MR.logChowla2_capstone_conditional_gk` (Salt/MR/S12Compose.lean:983), `Salt.MR.logChowla2_capstone_conditional_perBlock_gk` (Salt/MR/S12Compose.lean:1143), `Salt.MR.logChowla2_capstone_final'_gk` (Salt/MR/S12FuseCompose.lean:880) +24 |
| 15 | `Salt.MR.S16BandLaneCBoundedLH_winU` | Salt/MR/S16UniformLH.lean:142 | OPEN | 27 (22/5) | 22 | `Salt.MR.s16_bandLaneWinLH_holdsU` (Salt/MR/S16UniformLH.lean:342) | 0 | 0 | 0 | `Salt.MR.flat_capstone_generic_h` (Salt/MR/StridePairReceipt.lean:1189), `Salt.MR.flat_capstone_generic_h_14` (Salt/MR/StridePairReceipt.lean:2411), `Salt.MR.flat_capstone_generic_h_Z` (Salt/MR/StrideDoorAllGrades.lean:1269) +24 |
| 16 | `Salt.MR.A2Frame3` | Salt/MR/CapFreeArm3.lean:1059 | OPEN | 26 (26/0) | 14 | - | 3 | 0 | 0 | `Salt.MR.A2Frame3.box_at` (Salt/MR/CapFreeArm3.lean:1102), `Salt.MR.A2Frame3.ksGate_at` (Salt/MR/CapFreeArm3.lean:1110), `Salt.MR.a2Rows_of_capfree3` (Salt/MR/ThmA2Rows.lean:892) +23 |
| 17 | `Salt.MR.GRowsZeroGate'''_gk` | Salt/MR/M4ClosureRepair.lean:1174 | OPEN | 26 (26/0) | 3 | - | 3 | 2 | 0 | `Salt.MR.doorFuseFrame_pool'_of_gates_cc_decay_gk` (Salt/MR/M4ClosureRepair.lean:1256), `Salt.MR.doorFuseFrame_pool'_of_gates_cc_gk` (Salt/MR/M4ClosureRepair.lean:1212), `Salt.MR.doorFuseFrame_pool'_of_gates_const_gk` (Salt/MR/M4ClosureRepair.lean:1580) +23 |
| 18 | `Salt.MR.DoorRowZeroBase` | Salt/MR/M4RowsChiZero.lean:723 | OPEN | 25 (25/0) | 12 | - | 3 | 0 | 0 | `Salt.MR.m4_chiSummedFreeRow_of_doorArith_zero` (Salt/MR/M4ArithZero.lean:140), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'` (Salt/MR/M4RowsChiZeroPrime.lean:744), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated` (Salt/MR/M4ClosureRepair.lean:544) +22 |
| 19 | `Salt.MR.DoorRowZeroBase_gk` | Salt/MR/M4RowsChiZero.lean:934 | OPEN | 25 (25/0) | 0 | - | 3 | 0 | 0 | `Salt.MR.m4_chiSummedFreeRow_of_doorArith_zero_gk` (Salt/MR/M4ArithZero.lean:983), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_gk` (Salt/MR/M4ClosureRepair.lean:1406), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gk` (Salt/MR/M4RowsChiZeroPrime.lean:911) +22 |
| 20 | `Salt.MR.DoorBandBase` | Salt/MR/M4SocketDischarge.lean:262 | OPEN | 21 (21/0) | 11 | - | 2 | 0 | 0 | `Salt.MR.logChowla2_capstone_conditional` (Salt/MR/S12Compose.lean:283), `Salt.MR.logChowla2_capstone_conditional_perBlock` (Salt/MR/S12Compose.lean:471), `Salt.MR.logChowla2_capstone_final` (Salt/MR/S12Compose.lean:710) +18 |
| 21 | `Salt.MR.DoorRowEndBase_L_gk` | Salt/MR/M4RowAssemblyLinear.lean:5278 | OPEN | 20 (20/0) | 13 | - | 0 | 0 | 0 | `Salt.MR.m4_chiSummedFreeRow_of_doorArith_end_L_gk` (Salt/MR/M4SocketLinear.lean:537), `Salt.MR.m4_chiSummedFreeRow_of_doorArith_end_L_gk_kwide` (Salt/MR/M4SocketLinear.lean:727), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_end_L_gk` (Salt/MR/M4RowAssemblyLinear.lean:5356) +17 |
| 22 | `Salt.MR.GRowsZeroGate'''` | Salt/MR/M4ClosureRepair.lean:278 | OPEN | 20 (20/0) | 0 | - | 3 | 2 | 0 | `Salt.MR.doorFuseFrame_pool'_of_gates_cc` (Salt/MR/M4ClosureRepair.lean:324), `Salt.MR.doorFuseFrame_pool'_of_gates_cc_decay` (Salt/MR/M4ClosureRepair.lean:371), `Salt.MR.doorFuseFrame_pool'_of_gates_const` (Salt/MR/M4ClosureRepair.lean:964) +17 |
| 23 | `Salt.MR.S16BandLaneCBoundedL_winU` | Salt/MR/S16ComposeV4.lean:74 | OPEN | 19 (14/5) | 14 | `Salt.MR.s16_bandLaneWinL_holdsU` (Salt/MR/S16ComposeV4.lean:93) | 0 | 0 | 0 | `Salt.MR.flat_capstone_generic` (Salt/MR/DoorReceipt.lean:433), `Salt.MR.flat_capstone_generic_U` (Salt/MR/FlatDoorUniform.lean:985), `Salt.MR.flat_capstone_generic_eps` (Salt/MR/FlatDoorEpsChain.lean:845) +16 |
| 24 | `Salt.MR.A2Frame` | Salt/MR/ThmA2.lean:713 | OPEN | 17 (17/0) | 9 | - | 1 | 0 | 0 | `Salt.MR.A2Frame.box_at` (Salt/MR/ThmA2.lean:754), `Salt.MR.A2Frame.ksGate_at` (Salt/MR/ThmA2.lean:762), `Salt.MR.a2Rows_of_cap` (Salt/MR/ThmA2Rows.lean:464) +14 |
| 25 | `Salt.MR.DoorFuseFrame_L` | Salt/MR/M4RowLinear.lean:198 | OPEN | 16 (16/0) | 8 | - | 0 | 0 | 0 | `Salt.MR.m4_arith_door_exit_of_delta_L` (Salt/MR/M4ArithRhoLinear.lean:132), `Salt.MR.m4_arith_door_exit_rho_L` (Salt/MR/M4ArithRhoLinear.lean:94), `Salt.MR.m4_chiSummedFreeRow_of_doorArithRho_L` (Salt/MR/M4ArithRhoLinear.lean:57) +13 |
| 26 | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` | Salt/Entropy/Chowla/StridePair.lean:361 | OPEN | 14 (13/2) | 17 | `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride` (Salt/MR/StridePairReceipt.lean:2121), `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride_g` (Salt/MR/StridePairReceiptG.lean:1173) +4 | 5 | 4 | 0 | `Salt.Entropy.Chowla.gradedAffHeadAt_g12b_of_at_regime` (Salt/Entropy/Chowla/StrideShellBand.lean:369), `Salt.Entropy.Chowla.log_chowla_aff_of_door` (Salt/Entropy/Chowla/StrideShell.lean:433), `Salt.Entropy.Chowla.log_chowla_aff_of_door_at_regime_g12b` (Salt/Entropy/Chowla/StrideShellBand.lean:90) +11 |
| 27 | `Salt.MR.DoorRowZeroBase_L` | Salt/MR/M4RowLinear.lean:383 | OPEN | 14 (14/0) | 7 | - | 0 | 0 | 0 | `Salt.MR.m4_chiSummedFreeRow_of_doorArith_zero_L` (Salt/MR/M4ArithZeroLinear.lean:437), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L` (Salt/MR/M4RowsChiPrimeLinear.lean:368), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L` (Salt/MR/M4ClosureRepairLinear.lean:338) +11 |
| 28 | `Salt.HB.IsTsw` | Salt/HB/L2cELTsw.lean:82 | OPEN | 13 (13/0) | 0 | - | 0 | 0 | 0 | `Salt.HB.tsw_P_gt` (Salt/HB/L2cELTsw.lean:379), `Salt.HB.tsw_P_rough` (Salt/HB/L2cELTsw.lean:464), `Salt.HB.tsw_U_ge` (Salt/HB/L2cELTsw.lean:406) +10 |
| 29 | `Salt.MR.CaseASocket2` | Salt/MR/USetGradedPrice.lean:122 | OPEN | 13 (13/0) | 10 | - | 1 | 0 | 0 | `Salt.MR.cofactorSocket_of_ellLin` (Salt/MR/CapFreeArm3.lean:311), `Salt.MR.cofactor_Rbd34_local_nocap` (Salt/MR/CapFreeArm.lean:281), `Salt.MR.cofactor_Rbd34_local_nocap3` (Salt/MR/CapFreeArm3.lean:175) +10 |
| 30 | `Salt.MR.S16BandLaneCBoundedL` | Salt/MR/S16FlatTerminalLinear.lean:50 | OPEN | 13 (13/0) | 13 | - | 0 | 0 | 0 | `Salt.MR.flat_capstone_uniform` (Salt/MR/S16Uniform.lean:567), `Salt.MR.flat_capstone_uniform_kwide` (Salt/MR/S16Uniform.lean:1823), `Salt.MR.flat_conditional_uniform` (Salt/MR/S16Uniform.lean:802) +10 |
| 31 | `Salt.Entropy.Chowla.XCeilRider` | Salt/MR/XThread.lean:75 | OPEN | 12 (12/0) | 12 | - | 1 | 0 | 0 | `Salt.Entropy.Chowla.chowlaRegimeFlat_exists_param_head_xceil` (Salt/MR/XThread.lean:96), `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_mul` (Salt/MR/StridePairReceipt.lean:386), `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_mul_b9` (Salt/MR/StridePairReceipt.lean:2749) +9 |
| 32 | `Salt.MR.DoorRowEndBase` | Salt/MR/M4RowsChiEnd.lean:779 | OPEN | 12 (12/0) | 5 | - | 2 | 0 | 0 | `Salt.MR.doorRowZeroBase_of_doorRowEndBase` (Salt/MR/M4RowsChiZero.lean:742), `Salt.MR.m4_chiSummedFreeRow_of_doorArith_end` (Salt/MR/M4SocketDischarge.lean:196), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_end` (Salt/MR/M4RowsChiEnd.lean:885) +9 |
| 33 | `Salt.MR.DoorRowEndBase_gk` | Salt/MR/M4RowsChiEnd.lean:1080 | OPEN | 12 (12/0) | 0 | - | 2 | 0 | 0 | `Salt.MR.doorRowZeroBase_of_doorRowEndBase_gk` (Salt/MR/M4RowsChiZero.lean:952), `Salt.MR.m4_chiSummedFreeRow_of_doorArith_end_gk` (Salt/MR/M4SocketDischarge.lean:647), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_end_gk` (Salt/MR/M4RowsChiEnd.lean:1169) +9 |
| 34 | `Salt.HB.IsAdditiveOn` | Salt/HB/CrownAssembly.lean:175 | OPEN | 11 (11/0) | 8 | - | 0 | 0 | 0 | `Salt.HB.abs_A_sub_sum_ratio_le` (Salt/HB/CrownAssembly.lean:724), `Salt.HB.additive_prod` (Salt/HB/CrownAssembly.lean:299), `Salt.HB.deltaSum_nuG_mul_additive` (Salt/HB/CrownAssembly.lean:381) +8 |
| 35 | `Salt.MR.DoorFuseFrame_pool'_L_gk` | Salt/MR/M4RowSpineLinear.lean:1146 | OPEN | 11 (11/0) | 7 | - | 6 | 0 | 0 | `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool'_L_gk` (Salt/MR/M4RowSpineLinear.lean:1221), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool'_gatedH_L_gk` (Salt/MR/S16ProducersH.lean:1275), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool'_gated_L_gk` (Salt/MR/M4ClosureRepairLinear.lean:866) +8 |
| 36 | `Salt.MR.S16BandLaneCBounded` | Salt/MR/S16Budget.lean:1381 | OPEN | 11 (11/0) | 3 | - | 1 | 0 | 0 | `Salt.MR.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl` (Salt/MR/S16Budget.lean:1494), `Salt.MR.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flat` (Salt/MR/S16BudgetFlat.lean:51), `Salt.MR.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot` (Salt/MR/S16FlatTerminal.lean:305) +8 |
| 37 | `GEH_min` | Salt/Maynard/GehDoor.lean:160 | OPEN | 10 (10/0) | 2 | - | 1 | 0 | 0 | `GEH_min_antitone` (Salt/Maynard/GehDoor.lean:193), `GEH_min_implies_pointwise` (Salt/Maynard/GehDoor.lean:221), `GehAnchor.pieceObligationU_of_anchored_multiblock` (Salt/Maynard/GehAnchor.lean:505) +7 |
| 38 | `HasLevel` | Salt/Maynard/Level.lean:28 | OPEN | 10 (10/0) | 0 | - | 7 | 0 | 0 | `HasLevel_antitone` (Salt/Maynard/Level.lean:44), `Salt.Maynard.S2m_ge_compatMain_lod_uniform` (Salt/Maynard/LevelConsume.lean:326), `Salt.Maynard.analyticFrontier_lod` (Salt/Maynard/LevelConsume.lean:488) +7 |
| 39 | `Salt.MR.DoorCapBasePerBlock_gk` | Salt/MR/M4CapWire.lean:1312 | OPEN | 10 (10/0) | 2 | - | 1 | 0 | 0 | `Salt.MR.logChowla2_capstone_conditional_perBlock_gk` (Salt/MR/S12Compose.lean:1143), `Salt.MR.logChowla2_capstone_final'_gk` (Salt/MR/S12FuseCompose.lean:880), `Salt.MR.logChowla2_capstone_final_gk` (Salt/MR/S12Compose.lean:1303) +7 |
| 40 | `Salt.MR.DoorRowEndBase_L` | Salt/MR/M4RowLinear.lean:336 | OPEN | 10 (10/0) | 5 | - | 0 | 0 | 0 | `Salt.MR.m4_chiSummedFreeRow_of_doorArith_end_L` (Salt/MR/M4SocketLinear.lean:155), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_end_L` (Salt/MR/M4RowAssemblyLinear.lean:5113), `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L` (Salt/MR/M4RowsChiPrimeLinear.lean:220) +7 |

## ¬F-PRODUCED, NOT FULCRUM-SHAPED (54; first 54) — a ¬P is proved somewhere but nothing consumes it as a binder

| P | status | class | F-cons | ¬F-prod (u/c/via False) | examples |
|---|---|---|---|---|---|
| `Salt.Entropy.Chowla.logChowlaFails` | OPEN | HALF | 1 | 0/17/1 | `Salt.Entropy.Chowla.flat_head_uniform_h` (Salt/Entropy/Chowla/HloExportFlatH.lean:410), `Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat_h` (Salt/Entropy/Chowla/HloExportFlatH.lean:220) +16 |
| `Salt.Entropy.Chowla.MRTUniformity` | OPEN | HALF | 6 | 0/0/6 | `Salt.Entropy.Chowla.contradiction_of_mrtDoor` (Salt/Entropy/Chowla/MRTDoor.lean:62), `Salt.Entropy.Chowla.log_chowla_two_conditional` (Salt/Entropy/Chowla/SpineClose.lean:28) +4 |
| `Salt.Entropy.Chowla.MRTUniformityXiL2` | DISCHARGED | - | 27 | 0/0/6 | `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2` (Salt/Entropy/Chowla/MRTDoor.lean:205), `Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq` (Salt/Entropy/Chowla/Theorem23Shell.lean:362) +4 |
| `Salt.MR.M4DoorGates` | DISCHARGED | - | 68 | 0/0/6 | `Salt.MR.m4_door_False_of_blockMeanSq` (Salt/MR/M4BridgeCover.lean:506), `Salt.MR.m4_door_False_of_live` (Salt/MR/M4Close.lean:555) +4 |
| `Salt.MR.M4DoorGates_gk` | DISCHARGED | - | 57 | 0/0/5 | `Salt.MR.m4_door_False_of_blockMeanSq_gk` (Salt/MR/M4BridgeCover.lean:669), `Salt.MR.m4_door_False_of_live_gk` (Salt/MR/M4Close.lean:957) +3 |
| `Salt.Entropy.Chowla.MRTUniformityXi` | DISCHARGED | - | 14 | 0/0/4 | `Salt.Entropy.Chowla.contradiction_of_mrtDoorXi` (Salt/Entropy/Chowla/MRTDoor.lean:132), `Salt.Entropy.Chowla.log_chowla_two_shell_xi` (Salt/Entropy/Chowla/Theorem23Shell.lean:243) +2 |
| `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` | OPEN | HALF | 14 | 0/0/4 | `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2AffW` (Salt/Entropy/Chowla/StridePair.lean:390), `Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq_aff` (Salt/Entropy/Chowla/StrideShell.lean:125) +2 |
| `Salt.Entropy.Chowla.TwinDetecting` | DISCHARGED | - | 0 | 3/0/1 | `Salt.Entropy.Chowla.const_twin_blind` (Salt/Entropy/Chowla/TransportWall.lean:131), `Salt.Entropy.Chowla.corr_zero_blind` (Salt/Entropy/Chowla/PinDichotomy.lean:303) +2 |
| `Salt.MR.M4GradeGate` | DISCHARGED | - | 15 | 0/0/4 | `Salt.MR.m4_door_False_of_blockMeanSq` (Salt/MR/M4BridgeCover.lean:506), `Salt.MR.m4_door_False_of_blockMeanSq_gk` (Salt/MR/M4BridgeCover.lean:669) +2 |
| `Salt.MR.SocketBase` | DISCHARGED | - | 273 | 0/2/2 | `Salt.MR.s14_socket_empty_of_gRows` (Salt/MR/S14Compose.lean:288), `Salt.MR.s14_socket_empty_of_gRows_gk` (Salt/MR/S14Compose.lean:562) +2 |
| `Salt.Chen.TripleP` | OPEN | HALF | 3 | 3/0/0 | `Salt.Chen.not_tripleP_30` (Salt/Chen/WeightFamily.lean:155), `Salt.Chen.not_tripleP_of_heavy` (Salt/Chen/TwinDeficit.lean:214) +1 |
| `Salt.Entropy.Chowla.MRTUniformityXiL2H` | OPEN | HALF | 4 | 0/0/3 | `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2H` (Salt/Entropy/Chowla/ShiftFork.lean:579), `Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq_h` (Salt/Entropy/Chowla/Theorem23Shell.lean:627) +1 |
| `Salt.MR.CofactorBulkL` | OPEN | HALF | 3 | 2/1/0 | `Salt.MR.cofkL_bulk_infeasible` (Salt/MR/RegisterInhabit.lean:209), `Salt.MR.cofkL_bulk_infeasible_loglog` (Salt/MR/RegisterInhabit.lean:229) +1 |
| `Salt.MR.TannGate` | DISCHARGED | - | 481 | 3/0/0 | `Salt.MR.TannGate_fails_polylog` (Salt/MR/USetPins.lean:380), `Salt.MR.TannGate_fails_polylog_deg` (Salt/MR/USetPins.lean:394) +1 |
| `Salt.Parity.ParityInv` | DISCHARGED | - | 0 | 1/2/0 | `Salt.Certs.cert_parity_gap_witness` (Salt/Certs/ParityGap.lean:97), `Salt.Certs.cert_parity_gap` (Salt/Certs/ParityGap.lean:74) +1 |
| `Salt.Chen.ProductInWindow` | DISCHARGED | - | 0 | 2/0/0 | `Salt.Chen.not_productInWindow_of_above` (Salt/Chen/SwitchStrip.lean:272), `Salt.Chen.not_productInWindow_of_below` (Salt/Chen/SwitchStrip.lean:268) |
| `Salt.Entropy.Chowla.MRTUniformityXiH` | OPEN | - | 0 | 0/0/2 | `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiH` (Salt/Entropy/Chowla/ShiftFork.lean:345), `Salt.Entropy.Chowla.log_chowla_two_shell_xi_h` (Salt/Entropy/Chowla/Theorem23Shell.lean:488) |
| `Salt.MR.BlockSmallG` | DISCHARGED | - | 0 | 2/0/0 | `Salt.MR.mem_UsetGChi` (Salt/MR/USetGChi.lean:110), `Salt.MR.not_blockSmallG_pred_of_mem_TsetG` (Salt/MR/TLegCover.lean:99) |
| `Salt.MR.DoorRowCarriedT0` | OPEN | HALF | 7 | 0/0/2 | `Salt.MR.m4_wave_closed_coprime_discharged_False` (Salt/MR/M4Collapse.lean:254), `Salt.MR.m4_wave_collapsed_False` (Salt/MR/M4BaseNarrow.lean:1192) |
| `Salt.MR.DoorRowCarriedT0_L` | OPEN | HALF | 7 | 0/0/2 | `Salt.MR.m4_wave_closed_coprime_discharged_False_L` (Salt/MR/M4RowAssemblyLinear.lean:513), `Salt.MR.m4_wave_collapsed_False_L` (Salt/MR/M4RowAssemblyLinear.lean:4196) |
| `Salt.MR.DoorRowCarriedT0_L_gk` | OPEN | HALF | 9 | 0/0/2 | `Salt.MR.m4_wave_closed_coprime_discharged_False_L_gk` (Salt/MR/M4RowAssemblyLinear.lean:645), `Salt.MR.m4_wave_closed_coprime_discharged_False_L_gk_kwide` (Salt/MR/M4RowAssemblyLinear.lean:5498) |
| `Salt.MR.GRowsZeroGate'''` | OPEN | HALF | 20 | 0/0/2 | `Salt.MR.s14_compose_stops_of_MSelect'` (Salt/MR/S14Compose.lean:393), `Salt.MR.s14_gRows_kill` (Salt/MR/S14Compose.lean:230) |
| `Salt.MR.GRowsZeroGate'''_gk` | OPEN | HALF | 26 | 0/0/2 | `Salt.MR.s14_compose_stops_of_MSelect'_gk` (Salt/MR/S14Compose.lean:577), `Salt.MR.s14_gRows_kill_gk` (Salt/MR/S14Compose.lean:509) |
| `Salt.MR.M4ChiFreeRowMeanSq_L_gk` | OPEN | HALF | 4 | 0/0/2 | `Salt.MR.m4_wave_closed_coprime_discharged_False_L_gk` (Salt/MR/M4RowAssemblyLinear.lean:645), `Salt.MR.m4_wave_closed_coprime_discharged_False_L_gk_kwide` (Salt/MR/M4RowAssemblyLinear.lean:5498) |
| `Salt.MR.M4DoorGates_L` | OPEN | HALF | 30 | 0/0/2 | `Salt.MR.m4_wave_closed_coprime_discharged_False_L` (Salt/MR/M4RowAssemblyLinear.lean:513), `Salt.MR.m4_wave_collapsed_False_L` (Salt/MR/M4RowAssemblyLinear.lean:4196) |
| `Salt.MR.M4DoorGates_L_gk` | DISCHARGED | - | 57 | 0/0/2 | `Salt.MR.m4_wave_closed_coprime_discharged_False_L_gk` (Salt/MR/M4RowAssemblyLinear.lean:645), `Salt.MR.m4_wave_closed_coprime_discharged_False_L_gk_kwide` (Salt/MR/M4RowAssemblyLinear.lean:5498) |
| `Salt.Chen.windowDisjoint` | STRUCTURAL | - | 2 | 0/0/1 | `Salt.Chen.tripleSet_box_windowDisjoint` (Salt/Chen/SwitchDyadic.lean:206) |
| `Salt.Entropy.Chowla.MRTUniformityXiAff` | OPEN | - | 0 | 0/0/1 | `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiAff` (Salt/Entropy/Chowla/StrideFork.lean:725) |
| `Salt.Entropy.Chowla.MRTUniformityXiL2Aff` | OPEN | HALF | 1 | 0/0/1 | `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2Aff` (Salt/Entropy/Chowla/StrideFork.lean:759) |
| `Salt.Entropy.Chowla.PmNormalized` | DISCHARGED | - | 9 | 1/0/0 | `Salt.Entropy.Chowla.delta1w_not_pmNormalized` (Salt/Entropy/Chowla/PinDichotomy.lean:333) |
| `Salt.Entropy.Chowla.TwinDetecting'` | DISCHARGED | - | 2 | 1/0/0 | `Salt.Entropy.Chowla.slack_witness_not_twinDetecting'` (Salt/Entropy/Chowla/PinDichotomy.lean:110) |
| `Salt.MR.BlockSmallAt` | OPEN | - | 0 | 1/0/0 | `Salt.MR.mem_UsetChi` (Salt/MR/USetChi.lean:282) |
| `Salt.MR.DoorRowCarriedT0_gk` | OPEN | HALF | 6 | 0/0/1 | `Salt.MR.m4_wave_closed_coprime_discharged_False_gk` (Salt/MR/M4Collapse.lean:432) |
| `Salt.MR.M4BlockMeanSq` | DISCHARGED | - | 3 | 0/0/1 | `Salt.MR.m4_door_False_of_blockMeanSq` (Salt/MR/M4BridgeCover.lean:506) |
| `Salt.MR.M4BlockMeanSq_gk` | DISCHARGED | - | 3 | 0/0/1 | `Salt.MR.m4_door_False_of_blockMeanSq_gk` (Salt/MR/M4BridgeCover.lean:669) |
| `Salt.MR.M4ChiFreeRowMeanSq` | OPEN | HALF | 3 | 0/0/1 | `Salt.MR.m4_wave_closed_coprime_discharged_False` (Salt/MR/M4Collapse.lean:254) |
| `Salt.MR.M4ChiFreeRowMeanSq_L` | OPEN | HALF | 3 | 0/0/1 | `Salt.MR.m4_wave_closed_coprime_discharged_False_L` (Salt/MR/M4RowAssemblyLinear.lean:513) |
| `Salt.MR.M4ChiFreeRowMeanSq_gk` | OPEN | HALF | 3 | 0/0/1 | `Salt.MR.m4_wave_closed_coprime_discharged_False_gk` (Salt/MR/M4Collapse.lean:432) |
| `Salt.MR.M4ClassBlockMeanSq` | DISCHARGED | - | 4 | 0/0/1 | `Salt.MR.m4_wave_closed_False` (Salt/MR/M4WaveClosed.lean:552) |
| `Salt.MR.M4ClassBlockMeanSq_gk` | DISCHARGED | - | 4 | 0/0/1 | `Salt.MR.m4_wave_closed_False_gk` (Salt/MR/M4WaveClosed.lean:1122) |
| `Salt.MR.M4RowMeanSq` | OPEN | HALF | 3 | 0/0/1 | `Salt.MR.m4_wave_False` (Salt/MR/M4Join.lean:463) |
| `Salt.MR.M4RowMeanSq_gk` | OPEN | HALF | 3 | 0/0/1 | `Salt.MR.m4_wave_False_gk` (Salt/MR/M4Join.lean:765) |
| `Salt.MR.M4SievedDoorSq` | DISCHARGED | - | 16 | 0/0/1 | `Salt.MR.m4_door_False_of_live` (Salt/MR/M4Close.lean:555) |
| `Salt.MR.M4SievedDoorSq_gk` | DISCHARGED | - | 14 | 0/0/1 | `Salt.MR.m4_door_False_of_live_gk` (Salt/MR/M4Close.lean:957) |
| `Salt.MR.MRTBandCount` | OPEN | HALF | 2 | 0/0/1 | `Salt.MR.mrtBands_bandCount_incompatible_at_one` (Salt/MR/MRTPropA3.lean:598) |
| `Salt.MR.MRTBands` | OPEN | HALF | 7 | 0/0/1 | `Salt.MR.mrtBands_bandCount_incompatible_at_one` (Salt/MR/MRTPropA3.lean:598) |
| `Salt.MR.MRTLargeRangeEquidistribution` | OPEN | - | 0 | 1/0/0 | `Salt.MR.not_mrtLargeRangeEquidistribution` (Salt/MR/MRTPropA3.lean:4614) |
| `Salt.MR.MRTLemmaA4ii` | OPEN | - | 0 | 1/0/0 | `Salt.MR.not_mrtLemmaA4ii` (Salt/MR/MRTPropA3.lean:1476) |
| `Salt.MR.MRTLemmaA7Statement` | OPEN | - | 0 | 1/0/0 | `Salt.MR.not_mrtLemmaA7Statement` (Salt/MR/MRTPropA3.lean:4158) |
| `Salt.MR.MSelect'` | DISCHARGED | - | 4 | 0/0/1 | `Salt.MR.s14_compose_stops_of_MSelect'` (Salt/MR/S14Compose.lean:393) |
| `Salt.MR.MSelect'_gk` | DISCHARGED | - | 4 | 0/0/1 | `Salt.MR.s14_compose_stops_of_MSelect'_gk` (Salt/MR/S14Compose.lean:577) |
| `Salt.MR.S15Sel'` | DISCHARGED | - | 7 | 0/0/1 | `Salt.MR.s15_sel'_empty_at_closed_forms` (Salt/MR/S15Witness.lean:736) |
| `Salt.MR.SocketBaseLH` | DISCHARGED | - | 240 | 1/0/0 | `Salt.MR.socketBaseLH_at_zero_false` (Salt/MR/TierSSocket.lean:149) |
| `Salt.TwinBar.BadHyp` | OPEN | - | 0 | 1/0/0 | `Salt.TwinBar.badHyp_false` (Salt/TwinBar/SiegelTwin.lean:153) |

## DISJUNCTION AND CASE-SPLIT SITES (86; first 86, ordered by path)

By kind: case split `by_cases` 83 · prop-def body 2 · theorem conclusion 1.

| kind | declaration | file:line | P (polarity) |
|---|---|---|---|
| case split `by_cases` | `Salt.BrunLower.peel_term_eq` | Salt/BrunLower/Lemma3.lean:280 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.BrunLower.peel_term_eq` | Salt/BrunLower/Lemma3.lean:285 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.BrunLower.overcount` | Salt/BrunLower/Lemma3.lean:581 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.BrunLower.overcount` | Salt/BrunLower/Lemma3.lean:582 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.BrunLower.errSum_le_remainder_prod` | Salt/BrunLower/Pair.lean:84 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.BrunLower.peel_term_nonneg` | Salt/BrunLower/Pointwise.lean:116 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.BrunLower.peel_term_nonneg` | Salt/BrunLower/Pointwise.lean:122 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.BrunLower.remainder_prod_bound_of_R` | Salt/BrunLower/Remainder.lean:580 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.Chen.triplePrimeSum_le` | Salt/Chen/Assembly.lean:328 | `Salt.Chen.TripleP` |
| case split `by_cases` | `Salt.Chen.diagSum_le_bandDiagCount` | Salt/Chen/BandClose.lean:260 | `Salt.Chen.cwin` |
| case split `by_cases` | `Salt.Chen.symRectCount_eq_card` | Salt/Chen/BandIdent.lean:414 | `Salt.Chen.cwin` |
| case split `by_cases` | `Salt.Chen.diagSum_eq_card` | Salt/Chen/PDiag.lean:97 | `Salt.Chen.cwin` |
| case split `by_cases` | `Salt.Chen.diagSum_le_diagSum_true` | Salt/Chen/PDiag.lean:106 | `Salt.Chen.cwin` |
| case split `by_cases` | `Salt.Chen.diagAggW_le_honest` | Salt/Chen/PDiag.lean:447 | `Salt.Chen.cwin` |
| case split `by_cases` | `Salt.Chen.triplePrimeSum_le_sifted` | Salt/Chen/SwitchSieve.lean:240 | `Salt.Chen.TripleP` |
| case split `by_cases` | `Salt.Chen.triplePrimeSumW_le_sifted` | Salt/Chen/SwitchW.lean:234 | `Salt.Chen.TripleP` |
| case split `by_cases` | `Salt.Chen.buchstab_defect` | Salt/Chen/TnInduction.lean:597 | `Salt.Chen.rosserCond` |
| case split `by_cases` | `Salt.Chen.p2Ind_split` | Salt/Chen/TwinDeficit.lean:162 | `Salt.Chen.IsE2` |
| case split `by_cases` | `Salt.Chen.chenWeightA_le_indicator_of_sifted` | Salt/Chen/WeightFamily.lean:123 | `Salt.Chen.IsP2` |
| case split `by_cases` | `Salt.Chen.chen_weight_le_indicator` | Salt/Chen/WeightTrivia.lean:378 | `Salt.Chen.IsP2` |
| case split `by_cases` | `Salt.Fulcrum.fulcrum_dichotomy` | Salt/Fulcrum/Dichotomy.lean:105 | `Salt.Fulcrum.FulcrumQualityMin` |
| case split `by_cases` | `Salt.Goldbach.goldTriplePrimeSumW_le_sifted` | Salt/Goldbach/Asm5.lean:64 | `Salt.Chen.TripleP` |
| case split `by_cases` | `Salt.Goldbach.goldSymRectCount_eq_card` | Salt/Goldbach/BandIdent.lean:720 | `Salt.Goldbach.goldCwin` |
| case split `by_cases` | `Salt.Goldbach.gold_diagSum_eq_card` | Salt/Goldbach/PDiag.lean:70 | `Salt.Goldbach.goldCwin` |
| case split `by_cases` | `Salt.Goldbach.gold_diagSum_le_diagSum_true` | Salt/Goldbach/PDiag.lean:79 | `Salt.Goldbach.goldCwin` |
| case split `by_cases` | `Salt.Goldbach.gold_diagAggW_le_honest` | Salt/Goldbach/PDiag.lean:283 | `Salt.Goldbach.goldCwin` |
| case split `by_cases` | `Salt.HB.lamSum_S_decomp` | Salt/HB/CrownAssembly.lean:1342 | `Salt.BrunLower.chi` |
| prop-def body | `Salt.HB.HeathBrownDichotomyPoly` | Salt/HB/CrownTheorem1.lean:6361 | `TwinPrimeConjecture`, `Salt.HB.NoSiegelZerosPoly` |
| case split `by_cases` | `Salt.HB.fulcrum_dichotomy_poly` | Salt/HB/CrownTheorem1.lean:6466 | `Salt.HB.FulcrumQualityPoly` |
| case split `by_cases` | `Salt.HB.uncov_mem_cover` | Salt/HB/L2cMop.lean:399 | `Salt.HB.T2JunkBlock` |
| case split `by_cases` | `Salt.HB.uncov_mem_cover` | Salt/HB/L2cMop.lean:425 | `Salt.HB.T3FJunkBlock` |
| case split `by_cases` | `Salt.HB.uncov_mem_cover` | Salt/HB/L2cMop.lean:469 | `Salt.HB.TswJunkV` |
| case split `by_cases` | `Salt.N7.moebius_step` | Salt/HB/Lemma5Bilinear.lean:673 | `Salt.HB.Admissible` |
| case split `by_cases` | `Salt.N7.LamStar_eq_moebius_hbQ` | Salt/HB/Lemma5Bilinear.lean:717 | `Salt.HB.Admissible` |
| case split `by_cases` | `Salt.HB.exists_firstFailure` | Salt/HB/RosserDim4FL.lean:583 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.HB.firstFailure_decomposition` | Salt/HB/RosserDim4FL.lean:638 | `Salt.BrunLower.chi` |
| case split `by_cases` | `Salt.HB.LamStar_sub_LamTilde_eq_starDiff` | Salt/HB/StarStep.lean:100 | `Salt.HB.Admissible` |
| case split `by_cases` | `Salt.HB.starErrBound_nonneg` | Salt/HB/StarStep.lean:197 | `Salt.HB.HasExcSq` |
| case split `by_cases` | `Salt.HB.abs_starDiff_le_starErrBound` | Salt/HB/StarStep.lean:207 | `Salt.HB.HasExcSq` |
| case split `by_cases` | `Salt.HB.hChiArith_mult` | Salt/HB/TwistChain.lean:201 | `Salt.HB.Admissible` |
| case split `by_cases` | `Salt.MR.indicator_mul_shift_up` | Salt/MR/M4Band.lean:126 | `Salt.MR.MemS` |
| case split `by_cases` | `Salt.MR.errC_normSq_le` | Salt/MR/M4ParsevalStone.lean:75 | `Salt.MR.MemS` |
| case split `by_cases` | `Salt.MR.indicator_mul_punct` | Salt/MR/M4Puncture.lean:141 | `Salt.MR.MemSPunct` |
| case split `by_cases` | `Salt.MR.indicator_mul_dilate` | Salt/MR/M4Residue.lean:217 | `Salt.MR.MemS` |
| case split `by_cases` | `Salt.MR.sum_memS_dilate` | Salt/MR/M4Residue.lean:239 | `Salt.MR.MemS` |
| case split `by_cases` | `Salt.MR.ramTailWeight_isMultiplicative` | Salt/MR/MobiusChiRamare.lean:267 | `Salt.MR.WindowSmooth` |
| case split `by_cases` | `Salt.MR.ramTailWeight_isMultiplicative` | Salt/MR/MobiusChiRamare.lean:268 | `Salt.MR.WindowSmooth` |
| case split `by_cases` | `Salt.MR.maskTailWeight_isMultiplicative` | Salt/MR/MobiusChiRamareUnion.lean:257 | `Salt.MR.MaskSmooth` |
| case split `by_cases` | `Salt.MR.maskTailWeight_isMultiplicative` | Salt/MR/MobiusChiRamareUnion.lean:258 | `Salt.MR.MaskSmooth` |
| case split `by_cases` | `Salt.MR.prod_one_sub_gJ` | Salt/MR/Sec9Glue.lean:243 | `Salt.MR.MemS` |
| case split `by_cases` | `Salt.MR.lemma5_middle` | Salt/MR/Sec9Glue.lean:265 | `Salt.MR.MemS` |
| case split `by_cases` | `Salt.MR.wt_mul` | Salt/MR/ShiuMoment.lean:176 | `Salt.MR.BlockSmooth` |
| case split `by_cases` | `Salt.MR.thm_a2'_L` | Salt/MR/ThmA2Linear.lean:1514 | `Salt.MR.CapFreeFloor` |
| case split `by_cases` | `Salt.MR.thm_a2'_L_gk` | Salt/MR/ThmA2Linear.lean:2202 | `Salt.MR.CapFreeFloor` |
| case split `by_cases` | `Salt.MR.thm_a2'_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:3848 | `Salt.MR.CapFreeFloor` |
| case split `by_cases` | `Salt.MR.thm_a2'` | Salt/MR/ThmA2Rows.lean:736 | `Salt.MR.CapFreeFloor` |
| case split `by_cases` | `Salt.MR.thm_a2'_gk` | Salt/MR/ThmA2Rows.lean:1615 | `Salt.MR.CapFreeFloor` |
| case split `by_cases` | `Salt.Maynard.compat_moebius_expansion` | Salt/Maynard/CollisionQuant.lean:1647 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2m_sub_compatMain_le_disc_R_uniform` | Salt/Maynard/FrontierDischarge.lean:253 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.S2m_ge_compatMain_eh_uniform` | Salt/Maynard/FrontierDischarge.lean:397 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.S2m_ge_compatMain_lod_uniform` | Salt/Maynard/LevelConsume.lean:446 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.classSum_pp2_le` | Salt/Maynard/PpFold.lean:233 | `Salt.Maynard.isPrimeSq` |
| case split `by_cases` | `Salt.Maynard.pp2Term_le_ppTerm` | Salt/Maynard/PpFold.lean:338 | `Salt.Maynard.isPrimeSq` |
| case split `by_cases` | `Salt.Maynard.S1_le_main_add_error` | Salt/Maynard/S1Bound.lean:167 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.S1_le_main_add_errorW` | Salt/Maynard/S1Bound.lean:466 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.compat_moebius_expansion_M` | Salt/Maynard/S2Collision.lean:297 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2m_sub_compatMain_le` | Salt/Maynard/S2CompatEH.lean:107 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2m_sub_compatMain_le` | Salt/Maynard/S2CompatEH.lean:129 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2m_sub_compatMain_le` | Salt/Maynard/S2CompatEH.lean:136 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2m_sub_compatMain_le_disc` | Salt/Maynard/S2CompatEH.lean:171 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2m_sub_compatMain_le_disc_uniform` | Salt/Maynard/S2CompatEHFinal.lean:82 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.S2m_ge_compatMain_eh` | Salt/Maynard/S2CompatEHFinal.lean:232 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2mW_sub_compatMainW_le` | Salt/Maynard/S2CompatEHW.lean:71 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2mW_sub_compatMainW_le` | Salt/Maynard/S2CompatEHW.lean:93 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2mW_sub_compatMainW_le` | Salt/Maynard/S2CompatEHW.lean:100 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.compat_pair_fiber_leW` | Salt/Maynard/S2CompatEHW.lean:467 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.abs_S2mW_sub_compatMainW_le_disc_R_uniform` | Salt/Maynard/S2CompatEHW.lean:540 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.s2CompatMain_eq` | Salt/Maynard/S2Eh.lean:237 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.s2CompatMainW_eq` | Salt/Maynard/S2Eh.lean:817 | `Salt.Maynard.IsCollisionPair` |
| case split `by_cases` | `Salt.Maynard.compat_pair_fiber_le` | Salt/Maynard/S2FiberCount.lean:427 | `Salt.Maynard.IsCollisionPair` |
| theorem conclusion | `Salt.Maynard.shiu_class_cover` | Salt/Maynard/ShiuDecomp.lean:387 | `Salt.Maynard.shiuClassDeg`, `Salt.Maynard.shiuClassI`, `Salt.Maynard.shiuClassII`, `Salt.Maynard.shiuClassIIIIV` |
| case split `by_cases` | `Salt.Twelve.powerful_sum_bounded` | Salt/Twelve/PhiUpper.lean:432 | `Salt.Twelve.IsPowerful` |
| case split `by_cases` | `Salt.Twelve.windowWeight_col_le` | Salt/Twelve/PhiUpperReindex.lean:220 | `Salt.Twelve.IsPowerful` |
| case split `by_cases` | `Salt.Twelve.S2mW_ge_compatMain_theta_uniform` | Salt/Twelve/WinCore.lean:364 | `Salt.Maynard.IsCollisionPair` |
| prop-def body | `Salt.TwinBar.HeathBrownDichotomy` | Salt/TwinBar/SiegelTwin.lean:97 | `TwinPrimeConjecture`, `Salt.TwinBar.NoSiegelZeros` |
| case split `by_cases` | `Salt.TwinBar.heathBrown_iff_dichotomy` | Salt/TwinBar/SiegelTwin.lean:142 | `Salt.TwinBar.NoSiegelZeros` |

## Audited results item 1 classes `unconditional` whose only corpus-Prop binder is under ¬ (31)

- `Salt.Chen.chen_weight_le_indicator` (Salt/Chen/WeightTrivia.lean:373)
- `Salt.Chen.chen_weight_struct` (Salt/Chen/WeightTrivia.lean:391)
- `Salt.Entropy.Chowla.affWindow_survivorMass_ge` (Salt/Entropy/Chowla/AffineFork.lean:107)
- `Salt.Entropy.Chowla.decrement_exists_of_tower` (Salt/Entropy/Chowla/Endpoints.lean:98)
- `Salt.Entropy.Chowla.decrement_exists_of_tower_aff` (Salt/Entropy/Chowla/StrideDecrement.lean:688)
- `Salt.Entropy.Chowla.exists_affSurvivor_of_not_failsAff` (Salt/Entropy/Chowla/AffineFork.lean:153)
- `Salt.Entropy.Chowla.sign_split_fifth` (Salt/Entropy/Chowla/SignSplit.lean:278)
- `Salt.Entropy.Chowla.sign_split_of_not_fails` (Salt/Entropy/Chowla/SignSplit.lean:209)
- `Salt.Entropy.Chowla.sign_split_quarter_log` (Salt/Entropy/Chowla/SignSplit.lean:252)
- `Salt.Fulcrum.not_fulcrum_implies_noSiegelZeros` (Salt/Fulcrum/Dichotomy.lean:82)
- `Salt.HB.exists_firstFailure` (Salt/HB/RosserDim4FL.lean:557)
- `Salt.HB.not_fulcrumPoly_implies_noSiegelZerosPoly` (Salt/HB/CrownTheorem1.lean:6414)
- `Salt.MR.a2_row_cap_of_not_capFreeFloor` (Salt/MR/ThmA2.lean:686)
- `Salt.MR.affFullRangeAt_band_of_not_fails` (Salt/MR/TierSBridge.lean:135)
- `Salt.MR.approx_reduced` (Salt/MR/MinorArcExit.lean:333)
- `Salt.MR.exists_large_den_of_minor` (Salt/MR/BigXiArc.lean:331)
- `Salt.MR.exists_large_den_of_minorTight` (Salt/MR/BigXiArc.lean:712)
- `Salt.MR.exists_large_den_of_not_nearRat` (Salt/MR/BigXiArc.lean:274)
- `Salt.MR.exists_large_den_of_not_nearRatTight` (Salt/MR/BigXiArc.lean:684)
- `Salt.MR.exists_q_expSum_le` (Salt/MR/MinorArcExit.lean:895)
- `Salt.MR.flat_head_uniform_xceil_eps` (Salt/MR/FlatDoorEpsChain.lean:552)
- `Salt.MR.flat_head_uniform_xceil_epsW` (Salt/MR/FlatDoorEpsRung2.lean:4783)
- `Salt.MR.gradedAffHeadAt_g12b_of_at_regime_crowned` (Salt/MR/TierSBridge.lean:61)
- `Salt.MR.lamTailWeightMask_eq_zero_of_not_smooth` (Salt/MR/LambdaChiMask.lean:150)
- `Salt.MR.memSCoeff_eq_zero_of_not_memS` (Salt/MR/M4Band.lean:359)
- `Salt.MR.not_blockSmallG_witness` (Salt/MR/USetGradedThin.lean:140)
- `Salt.MR.ramI_nonempty_of_not_blockSmallG` (Salt/MR/USetGradedThin.lean:152)
- `Salt.MR.ramTailWeight_eq_zero_of_not_smooth` (Salt/MR/MobiusChiRamare.lean:204)
- `Salt.MR.sPart_eq_zero_of_not_squarefull` (Salt/MR/SPartCore.lean:170)
- `Salt.Parity.Z_trivial_of_not_completion` (Salt/Parity/Z.lean:125)
- `Salt.SW.not_fulcrum_siegelFree_SW` (Salt/SW/StandoffGate.lean:805)

