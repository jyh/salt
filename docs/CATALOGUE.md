# THE RESULTS CATALOGUE — by machine (O13 item 1)

> **GENERATED — do not edit by hand.** Regenerate: `python3 scripts/results_catalogue.py` · staleness gate: `python3 scripts/results_catalogue.py --check`.
> Base: last commit touching `Salt/` = `ddc2511d` · source digest `7459fcd147e4efa5` (sha256 over every `Salt/**/*.lean`, sorted by path).

## Population receipt

| ledgers read | ledgers with audit commands | names parsed | distinct names | resolved | unresolved | audited in 2+ ledgers | repeat mentions folded |
|---|---|---|---|---|---|---|---|
| 24 | 22 | 9143 | 9088 | 9087 | 1 | 0 | 55 |

Declarations indexed across the tree: 22703 · corpus Prop-valued names (the hypothesis universe): 668.

## KIND × OBJECT (counts; a name with several objects counts once in each object column)

| kind | total | zeros | sieves | characters | entropy | exponential sums | other |
|---|---|---|---|---|---|---|---|
| unconditional | 6790 | 294 | 2072 | 4640 | 379 | 425 | 29 |
| conditional | 1605 | 25 | 196 | 1417 | 95 | 24 | 4 |
| statement-only | 211 | 0 | 4 | 198 | 10 | 0 | 0 |
| infrastructure | 481 | 0 | 68 | 366 | 55 | 17 | 0 |
| unresolved | 1 | 0 | 0 | 0 | 1 | 0 | 0 |
| **all** | 9088 | 319 | 2340 | 6621 | 540 | 466 | 33 |

## LIMITS — read these beside every count above

- **Source-level parse, no elaboration.** Names, binders and types are read from comment-stripped source text. Anything produced by macros, `alias`, `to_additive`, `@[simps]`, or elaboration-time notation is invisible; section `variable`s are attached only when their name occurs in the statement or is `include`d; implicit `{}`/`⦃⦄` binders are NOT walked.
- **Unresolved: 1.** A name the parser cannot find a declaration site for is listed in its own section, never dropped. Unresolved ≠ absent from Lean.
- **The conditional test** is the binder's HEAD SYMBOL (walked through leading `∀`/`→` and through `∧`) resolved against the corpus Prop-valued set; premises `A → …` at the top of the conclusion count as binders. A binder `¬ P …` or `P … → False` is a hypothesis on P at NEGATIVE polarity, listed as `¬P` (since 2026-09-26; before, 31 such results read as unconditional); a `¬ P` in a binder's own ANTECEDENT (`¬ P → Q`) is not walked — the hypothesis there is Q. A hypothesis whose head is a mathlib or infix Prop (`2 ≤ x`, `Tendsto …`, `Squarefree P`) does not make a result conditional. The Prop-valued set is itself heuristic: `: Prop` / `: … → Prop` ascriptions, structures/classes all of whose fields look Prop-shaped, and untyped defs whose body is `∀`/`∃`/relational.
- **Mixed data+Prop bundles are DATA.** A corpus structure carrying both data and Prop fields (e.g. `ChowlaRegime`, `HBForms`, `TruncSieve`) is not Prop-valued, so a binder of that type does NOT make a result conditional — the constraints inside a regime bundle are invisible to this column.
- **The infrastructure split for theorems is a HEURISTIC:** a theorem/lemma whose conclusion is `=`/`↔` and whose proof is `rfl`, `Iff.rfl`, `Eq.refl …`, `by rfl`, `by unfold …`, `by delta …` or `by exact rfl`. Every other identity lemma is classed by its binders.
- **A `def` whose type is a proposition** (not `Prop` itself) is classed as a theorem, by its binders.
- **The object map is a CHOICE**, reproduced verbatim below. `characters` includes multiplicative twists (`liouville`, `moebius`); symbol tags are plain substrings of the statement.

<details><summary>Object map (data in the script)</summary>

| rule | matches | objects |
|---|---|---|
| path prefix | `Salt/Entropy/` | entropy |
| path prefix | `Salt/ExpSum/` | exponential sums |
| path prefix | `Salt/Vk/` | exponential sums, zeros |
| path prefix | `Salt/Vmvt/` | exponential sums |
| path prefix | `Salt/Weil/` | exponential sums |
| path prefix | `Salt/Brun/` | sieves |
| path prefix | `Salt/BrunLower/` | sieves |
| path prefix | `Salt/Chen/` | sieves |
| path prefix | `Salt/Maynard/` | sieves |
| path prefix | `Salt/Parity/` | sieves |
| path prefix | `Salt/LS/` | sieves |
| path prefix | `Salt/BV/` | sieves |
| path prefix | `Salt/SW/` | sieves |
| path prefix | `Salt/Goldbach/` | sieves |
| path prefix | `Salt/HardyLittlewood/` | sieves |
| path prefix | `Salt/Twelve/` | sieves |
| path prefix | `Salt/TwinBar/` | sieves |
| path prefix | `Salt/Mertens/` | sieves |
| path prefix | `Salt/HB/` | characters |
| path prefix | `Salt/MR/` | characters |
| file-name substring | `Zero` | zeros |
| file-name substring | `Zeta` | zeros |
| file-name substring | `ZFR` | zeros |
| file-name substring | `Littlewood` | zeros |
| file-name substring | `Sieve` | sieves |
| file-name substring | `Selberg` | sieves |
| file-name substring | `Char` | characters |
| file-name substring | `Dirichlet` | characters |
| file-name substring | `Liouville` | characters |
| file-name substring | `ExpSum` | exponential sums |
| file-name substring | `Weyl` | exponential sums |
| file-name substring | `VdC` | exponential sums |
| file-name substring | `Entropy` | entropy |
| statement symbol | `riemannZeta` | zeros |
| statement symbol | `LSeries` | zeros |
| statement symbol | `zeroFree` | zeros |
| statement symbol | `ZeroFree` | zeros |
| statement symbol | `zeroCount` | zeros |
| statement symbol | `DirichletCharacter` | characters |
| statement symbol | `MulChar` | characters |
| statement symbol | `legendreSym` | characters |
| statement symbol | `jacobiSym` | characters |
| statement symbol | `liouville` | characters |
| statement symbol | `moebius` | characters |
| statement symbol | `gaussSum` | characters, exponential sums |
| statement symbol | `vonMangoldt` | sieves |
| statement symbol | `primeCounting` | sieves |
| statement symbol | `twinPrimeCounting` | sieves |
| statement symbol | `Sieve` | sieves |
| statement symbol | `sieve` | sieves |
| statement symbol | `Selberg` | sieves |
| statement symbol | `Complex.exp (2 * π * I` | exponential sums |
| statement symbol | `Complex.exp (2 * ↑π * I` | exponential sums |
| statement symbol | `Complex.exp (2 * Real.pi * Complex.I` | exponential sums |
| statement symbol | `AddChar` | exponential sums |
| statement symbol | `toCircle` | exponential sums |
| statement symbol | `fourier` | exponential sums |
| statement symbol | `expSum` | exponential sums |
| statement symbol | `ExpSum` | exponential sums |
| statement symbol | `entropy` | entropy |
| statement symbol | `Entropy` | entropy |
| statement symbol | `negMulLog` | entropy |
| statement symbol | `klFun` | entropy |
| (none matched) | | other |

</details>

## Named hypotheses — how many conditional results hang on each (the O2 payoff table)

| hypothesis | conditional results |
|---|---|
| `Salt.MR.SocketBaseLH` | 228 |
| `Salt.MR.TannGate` | 161 |
| `Salt.MR.ShortIntervalDatum` | 97 |
| `Salt.MR.DoorArithFrameRho_L` | 71 |
| `Salt.MR.M4DoorGates` | 55 |
| `Salt.MR.WellSpaced` | 53 |
| `Salt.MR.MmuChiRate` | 51 |
| `Salt.MR.SocketBaseL` | 48 |
| `Salt.MR.CofactorSocket` | 47 |
| `Salt.MR.M4DoorGates_L_gk` | 44 |
| `Salt.MR.NearRatTight` | 44 |
| `Salt.MR.DoorBaseFrame` | 41 |
| `Salt.MR.TLBlockGates34` | 37 |
| `Salt.MR.DoorRowZeroBase_L_gk` | 35 |
| `Salt.MR.FibreWellSpaced` | 34 |
| `Salt.MR.GRowsZeroGate'''_L_gk` | 31 |
| `Salt.MR.SeamCoefW` | 31 |
| `Salt.MR.collisionGate` | 29 |
| `Salt.MR.XiFamily` | 28 |
| `Salt.MR.SocketBase` | 27 |
| `Salt.MR.DoorArithFrame` | 26 |
| `Salt.MR.SeamCoefWS` | 26 |
| `Salt.MR.DoorBandBase_L_gk` | 25 |
| `Salt.Entropy.Chowla.MRTUniformityXiL2` | 23 |
| `Salt.MR.CalFrameK` | 22 |
| `Salt.MR.S16BandLaneCBoundedLH_winU` | 22 |
| `Salt.MR.DoorFuseFrame` | 21 |
| `Salt.MR.JointIntegrableAt` | 21 |
| `Salt.MR.m4SmallGradeFits` | 21 |
| `Salt.HB.N9Regime` | 19 |
| `Salt.MR.S15Sel''_L_gk` | 19 |
| `Salt.MR.DoorFuseFrame_L_gk` | 18 |
| `Salt.Entropy.Chowla.MRTUniformityXi` | 17 |
| `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` | 17 |
| `Salt.MR.DoorArithFrameRho` | 16 |
| `Salt.Entropy.Chowla.logChowla2Fails` | 15 |
| `Salt.Chen.StepHypWPC` | 14 |
| `Salt.MR.A2Frame3` | 14 |
| `Salt.MR.S16BandLaneCBoundedL_winU` | 14 |
| `Salt.MR.CapFreeFloor3` | 13 |
| `Salt.MR.DoorRowEndBase_L_gk` | 13 |
| `Salt.MR.S16BandLaneCBoundedL` | 13 |
| `Salt.Entropy.Chowla.XCeilRider` | 12 |
| `Salt.Entropy.Chowla.XCeilRiderStrict` | 12 |
| `Salt.MR.DoorRowZeroBase` | 12 |
| `Salt.MR.M4GradeGateSplit` | 12 |
| `Salt.MR.M4SievedDoorSq` | 12 |
| `Salt.MR.DoorBandBase` | 11 |
| `Salt.MR.LevelGates` | 11 |
| `Salt.Entropy.Chowla.MRTUniformity` | 10 |
| `Salt.Entropy.Chowla.StrideScale` | 10 |
| `Salt.MR.CaseASocket2` | 10 |
| `Salt.MR.M4ChiSummedFreeRowH_L_gk` | 10 |
| `Salt.MR.S15CrossingBound_L_gk` | 10 |
| `Salt.MR.S16BandLaneCBoundedL_win` | 10 |
| `Salt.BV.SiegelWalfisz` | 9 |
| `Salt.HB.N7Exit` | 9 |
| `Salt.MR.A2Frame` | 9 |
| `Salt.MR.DoorCapBasePerBlock_L_gk` | 9 |
| `Salt.MR.DoorRowCarriedT0` | 9 |
| `Salt.BrunLower.chi` | 8 |
| `Salt.Chen.StepHypWP` | 8 |
| `Salt.Entropy.Chowla.PairCollapse` | 8 |
| `Salt.HB.IsAdditiveOn` | 8 |
| `Salt.MR.DoorFuseFrame_L` | 8 |
| `Salt.MR.M4DoorGates_L` | 8 |
| `Salt.MR.MRTBands` | 8 |
| `Salt.MR.PocketSocket` | 8 |
| `FiniteRange` | 7 |
| `Salt.Entropy.Chowla.PmNormalized` | 7 |
| `Salt.HB.CoprimeSupport` | 7 |
| `Salt.MR.BigXiArcTight` | 7 |
| `Salt.MR.DoorFuseFrame_pool'_L_gk` | 7 |
| `Salt.MR.DoorRowZeroBase_L` | 7 |
| `Salt.MR.MSelect'_L_gk` | 7 |
| `Salt.MR.VkTwistUB` | 7 |
| `Salt.MR.XiCarveWidth` | 7 |
| `Salt.Entropy.Chowla.MRTUniformityXiL2H` | 6 |
| `Salt.MR.CapFreeFloor` | 6 |
| `Salt.MR.CaseASocketGen` | 6 |
| `Salt.MR.DoorRowCarriedT0_L` | 6 |
| `Salt.MR.M4ChiSummedFreeRow` | 6 |
| `Salt.MR.M4ChiSummedFreeRow_L_gk` | 6 |
| `Salt.MR.M4GradeGate` | 6 |
| `Salt.MR.S15Sel''_L` | 6 |
| `Salt.MR.S16BaseScaleCap96_LH_gk` | 6 |
| `Salt.MR.S16CofactorSupply_LH_gk` | 6 |
| `Salt.MR.SawtoothOdd` | 6 |
| `Salt.MR.SieveBlockGate` | 6 |
| `Salt.MR.TLBlockGates` | 6 |
| `ProbabilityTheory.FiniteSupport` | 5 |
| `Salt.Entropy.Chowla.MRTUniformityXiL2Set` | 5 |
| `Salt.MR.DoorRowCarriedT0_L_gk` | 5 |
| `Salt.MR.DoorRowCarried_L_gk` | 5 |
| `Salt.MR.DoorRowEndBase` | 5 |
| `Salt.MR.DoorRowEndBase_L` | 5 |
| `Salt.MR.GRowsZeroGate'''_L` | 5 |
| `Salt.MR.JointIntegrableAtC` | 5 |
| `Salt.MR.L1LowerEffective` | 5 |
| `Salt.MR.Lemma4Comparison` | 5 |
| `Salt.MR.M4ChiBlockMeanSqH` | 5 |
| `Salt.MR.M4ClassBlockMeanSq` | 5 |
| `Salt.MR.M4SievedDoorSqH_L_gk` | 5 |
| `Salt.MR.M4SievedDoorSq_L_gk` | 5 |
| `Salt.MR.S15CrossingBound_LH_gk` | 5 |
| `Salt.MR.S16BandLaneCBoundedLH_win` | 5 |
| `Salt.MR.S16CofactorSupply_L_gk` | 5 |
| `Salt.TwinBar.AffFullRangeAt` | 5 |
| `Salt.TwinBar.LambdaSummatory` | 5 |
| `¬Salt.Entropy.Chowla.logChowlaFailsAff` | 5 |
| `Salt.BrunLower.IsLowerMoebius` | 4 |
| `Salt.Chen.Feasible` | 4 |
| `Salt.Chen.StepHyp` | 4 |
| `Salt.Chen.rosserCond` | 4 |
| `Salt.Entropy.Chowla.logChowlaFailsAff` | 4 |
| `Salt.MR.CalFrame` | 4 |
| `Salt.MR.DoorBandBase_L` | 4 |
| `Salt.MR.DoorFuseFrame_pool` | 4 |
| `Salt.MR.FlatDoorEpsFamilyW` | 4 |
| `Salt.MR.HalaszPrimesChi` | 4 |
| `Salt.MR.M4BlockMeanSq` | 4 |
| `Salt.MR.M4ChiDyadicRowMeanSq` | 4 |
| `Salt.MR.M4ChiFreeRowMeanSq` | 4 |
| `Salt.MR.M4CoprimeBlockMeanSq` | 4 |
| `Salt.MR.M4CoprimeBlockMeanSq_L_gk` | 4 |
| `Salt.MR.M4DoorGates_gk` | 4 |
| `Salt.MR.M4RowMeanSq` | 4 |
| `Salt.MR.TwistedWindowPriceGated` | 4 |
| `Salt.MR.XCeilRiderAt` | 4 |
| `Salt.Twelve.PhiUpperAtom` | 4 |
| `Salt.TwinBar.LiouvilleTwinDisp` | 4 |
| `¬Salt.MR.NearRatTight` | 4 |
| `EHall` | 3 |
| `ProbabilityTheory.Kernel.AEFiniteKernelSupport` | 3 |
| `Salt.Entropy.Chowla.LogChowlaAffSupply` | 3 |
| `Salt.HB.FulcrumQualityPoly` | 3 |
| `Salt.HB.Lemma5Eval` | 3 |
| `Salt.MR.CofactorBulkL` | 3 |
| `Salt.MR.DoorBandBase_gk` | 3 |
| `Salt.MR.DoorCapBase` | 3 |
| `Salt.MR.DoorFuseFrame_pool'_L` | 3 |
| `Salt.MR.DoorRowCarried` | 3 |
| `Salt.MR.ExitClose` | 3 |
| `Salt.MR.FlatDoorAllGradesW` | 3 |
| `Salt.MR.FlatHeadFormEpsW` | 3 |
| `Salt.MR.FlatHeadFormEpsW_band` | 3 |
| `Salt.MR.FlatHeadFormH` | 3 |
| `Salt.MR.FlatHeadFormHG` | 3 |
| `Salt.MR.FlatHeadFormHG_Z` | 3 |
| `Salt.MR.FlatHeadFormHG_g12b_band` | 3 |
| `Salt.MR.FlatHeadFormU` | 3 |
| `Salt.MR.GRowsZeroGate''` | 3 |
| `Salt.MR.GRowsZeroGate'''_gk` | 3 |
| `Salt.MR.HalaszIntegersChi` | 3 |
| `Salt.MR.M4BlockMeanSqSup` | 3 |
| `Salt.MR.M4BlockMeanSqSupQH` | 3 |
| `Salt.MR.M4ChiBlockMeanSq` | 3 |
| `Salt.MR.M4ChiRowMeanSq` | 3 |
| `Salt.MR.M4RowDatumAt` | 3 |
| `Salt.MR.MRTBandCount` | 3 |
| `Salt.MR.MRTLemmaA6` | 3 |
| `Salt.MR.MSelect` | 3 |
| `Salt.MR.MSelect'_L` | 3 |
| `Salt.MR.MVHilbertUniform` | 3 |
| `Salt.MR.MmuChiRatePrincipal` | 3 |
| `Salt.MR.PocketSocket3Gen` | 3 |
| `Salt.MR.PrimeTailShiftBounded` | 3 |
| `Salt.MR.S13CapGate` | 3 |
| `Salt.MR.S13CapGatePerBlock_L_gk` | 3 |
| `Salt.MR.S15Sel''_L_gk_T` | 3 |
| `Salt.MR.S16BandLaneCBounded` | 3 |
| `Salt.MR.S16BandLaneCBoundedLH` | 3 |
| `Salt.MR.S16BaseScaleCap96_L_gk` | 3 |
| `Salt.MR.Squarefull` | 3 |
| `Salt.MR.TLBlockGatesLoc` | 3 |
| `Salt.MR.WindowSmooth` | 3 |
| `Salt.MR.ZetaInvShallowVk` | 3 |
| `Salt.TwinBar.CorrWindow` | 3 |
| `Salt.TwinBar.LiouvilleTwinDispLog` | 3 |
| `Salt.TwinBar.SiegelSequence` | 3 |
| `TwinPrimeConjecture` | 3 |
| `WindowPNT` | 3 |
| `¬Salt.Entropy.Chowla.logChowla2Fails` | 3 |
| `¬Salt.MR.CapFreeFloor` | 3 |
| `CoeffAt` | 2 |
| `GEH_min` | 2 |
| `Salt.BV.PsiToPiTransfer` | 2 |
| `Salt.Entropy.Chowla.GradedAffHeadAt` | 2 |
| `Salt.Entropy.Chowla.LogChowlaAffSupplyW` | 2 |
| `Salt.Entropy.Chowla.MRTUniformityXiH` | 2 |
| `Salt.Entropy.Chowla.MRTUniformityXiL2Aff` | 2 |
| `Salt.Entropy.Chowla.TwinDetecting'` | 2 |
| `Salt.Fulcrum.FulcrumQualityMin` | 2 |
| `Salt.HB.HasTwoFormGcdBound` | 2 |
| `Salt.HB.IsSignFunction` | 2 |
| `Salt.MR.BlockLive` | 2 |
| `Salt.MR.CellGates` | 2 |
| `Salt.MR.DoorCapBasePerBlock` | 2 |
| `Salt.MR.DoorCapBasePerBlock_gk` | 2 |
| `Salt.MR.DoorFuseFrame_pool'` | 2 |
| `Salt.MR.DoorFuseFrame_pool_L` | 2 |
| `Salt.MR.DoorRowCarriedJoin_L_gk` | 2 |
| `Salt.MR.DoorRowCarriedPool_L_gk` | 2 |
| `Salt.MR.DoorRowCarried_L` | 2 |
| `Salt.MR.FlatCapstoneFormHG_g12b_band` | 2 |
| `Salt.MR.FlatConditionalFormHG_g12b_band` | 2 |
| `Salt.MR.FlatHeadForm` | 2 |
| `Salt.MR.FlatHeadFormEps` | 2 |
| `Salt.MR.FlatHeadFormHG_g12b` | 2 |
| `Salt.MR.FlatKswinFormHG_g12b_band` | 2 |
| `Salt.MR.FlatRoadExitFormH` | 2 |
| `Salt.MR.FlatRoadExitFormHG_g12b_band` | 2 |
| `Salt.MR.M4ChiFreeRowMeanSqN` | 2 |
| `Salt.MR.M4ChiFreeRowMeanSq_L` | 2 |
| `Salt.MR.M4ChiFreeRowMeanSq_L_gk` | 2 |
| `Salt.MR.M4ChiMaximalStep` | 2 |
| `Salt.MR.M4ChiSummedBlockMeanSqN` | 2 |
| `Salt.MR.M4ChiSummedBlockMeanSqNH_L_gk` | 2 |
| `Salt.MR.M4ChiSummedFreeRow_L` | 2 |
| `Salt.MR.M4ClassBlockMeanSqH` | 2 |
| `Salt.MR.M4CoprimeBlockMeanSq_L` | 2 |
| `Salt.MR.M4DoorL2HeadDemand` | 2 |
| `Salt.MR.M4GradeGateL2` | 2 |
| `Salt.MR.M4SievedDoorSqH` | 2 |
| `Salt.MR.M4SievedDoorSqSup` | 2 |
| `Salt.MR.M4SievedDoorSqSupH` | 2 |
| `Salt.MR.MRTDoorAllGrades` | 2 |
| `Salt.MR.MRTLargeRangeEquidistributionFixed` | 2 |
| `Salt.MR.MRTPropA3Ambient` | 2 |
| `Salt.MR.MRTThmA1` | 2 |
| `Salt.MR.MSelect_L` | 2 |
| `Salt.MR.MSelect_L_gk` | 2 |
| `Salt.MR.MaskSmooth` | 2 |
| `Salt.MR.MinorArcBoundTight` | 2 |
| `Salt.MR.PocketSocket3` | 2 |
| `Salt.MR.S15Sel''_L_T` | 2 |
| `Salt.MR.S16BaseScaleCapEnd_L_gk` | 2 |
| `Salt.MR.StrideDoorAllGradesW` | 2 |
| `Salt.MR.XCeilRiderStrictAt` | 2 |
| `Salt.Parity.TwinSufficient` | 2 |
| `Salt.SW.EstermannPositivity` | 2 |
| `Salt.SW.NoSiegelZerosAt` | 2 |
| `Salt.SW.WellSpacedAt` | 2 |
| `Salt.Twelve.PiAsymp` | 2 |
| `Salt.TwinBar.InfinitelyManySiegelZeros` | 2 |
| `Salt.TwinBar.MmuRate` | 2 |
| `Salt.TwinBar.TwinB_min` | 2 |
| `¬Salt.BrunLower.chi` | 2 |
| `¬Salt.Fulcrum.FulcrumQualityMin` | 2 |
| `¬Salt.MR.BlockSmallG` | 2 |
| `¬Salt.MR.NearRat` | 2 |
| `PieceObligationU` | 1 |
| `SWAt` | 1 |
| `SWAtData` | 1 |
| `Salt.BV.PsiToPiCore` | 1 |
| `Salt.Chen.StepHypW` | 1 |
| `Salt.Chen.TripleP` | 1 |
| `Salt.Chen.windowDisjoint` | 1 |
| `Salt.Entropy.Chowla.GradedAffHeadAt_g12b` | 1 |
| `Salt.Entropy.Chowla.MRTUniformityXiAff` | 1 |
| `Salt.Entropy.Chowla.TwinDetecting` | 1 |
| `Salt.Entropy.Chowla.logChowlaFails` | 1 |
| `Salt.ExpSum.IsVdCBound` | 1 |
| `Salt.Fulcrum.SiegelModulusUnbounded` | 1 |
| `Salt.HB.NoSiegelZerosPoly` | 1 |
| `Salt.LS.Spaced` | 1 |
| `Salt.MR.BigXiArc` | 1 |
| `Salt.MR.DoorCapErrWS` | 1 |
| `Salt.MR.FlatCapstoneForm` | 1 |
| `Salt.MR.FlatCapstoneFormEps` | 1 |
| `Salt.MR.FlatCapstoneFormEpsW` | 1 |
| `Salt.MR.FlatCapstoneFormEpsW_band` | 1 |
| `Salt.MR.FlatCapstoneFormH` | 1 |
| `Salt.MR.FlatCapstoneFormHG` | 1 |
| `Salt.MR.FlatCapstoneFormHG_Z` | 1 |
| `Salt.MR.FlatCapstoneFormHG_g12b` | 1 |
| `Salt.MR.FlatCapstoneFormU` | 1 |
| `Salt.MR.FlatConditionalForm` | 1 |
| `Salt.MR.FlatConditionalFormEps` | 1 |
| `Salt.MR.FlatConditionalFormEpsW` | 1 |
| `Salt.MR.FlatConditionalFormEpsW_band` | 1 |
| `Salt.MR.FlatConditionalFormH` | 1 |
| `Salt.MR.FlatConditionalFormHG` | 1 |
| `Salt.MR.FlatConditionalFormHG_Z` | 1 |
| `Salt.MR.FlatConditionalFormHG_g12b` | 1 |
| `Salt.MR.FlatConditionalFormU` | 1 |
| `Salt.MR.FlatDoorAllGradesBandW` | 1 |
| `Salt.MR.FlatDoorL2Form` | 1 |
| `Salt.MR.FlatDoorL2FormEps` | 1 |
| `Salt.MR.FlatDoorL2FormEpsW` | 1 |
| `Salt.MR.FlatDoorL2FormEpsW_band` | 1 |
| `Salt.MR.FlatDoorL2FormU` | 1 |
| `Salt.MR.FlatDoorPayload` | 1 |
| `Salt.MR.FlatDoorUniformW` | 1 |
| `Salt.MR.FlatKswinForm` | 1 |
| `Salt.MR.FlatKswinFormEps` | 1 |
| `Salt.MR.FlatKswinFormEpsW` | 1 |
| `Salt.MR.FlatKswinFormEpsW_band` | 1 |
| `Salt.MR.FlatKswinFormH` | 1 |
| `Salt.MR.FlatKswinFormHG` | 1 |
| `Salt.MR.FlatKswinFormHG_Z` | 1 |
| `Salt.MR.FlatKswinFormHG_g12b` | 1 |
| `Salt.MR.FlatKswinFormU` | 1 |
| `Salt.MR.FlatRoadExitFormHG` | 1 |
| `Salt.MR.FlatRoadExitFormHG_Z` | 1 |
| `Salt.MR.FlatRoadExitFormHG_g12b` | 1 |
| `Salt.MR.FlatRoadForm` | 1 |
| `Salt.MR.FlatRoadFormEps` | 1 |
| `Salt.MR.FlatRoadFormEpsW` | 1 |
| `Salt.MR.FlatRoadFormEpsW_band` | 1 |
| `Salt.MR.FlatRoadFormU` | 1 |
| `Salt.MR.FlatSocketForm` | 1 |
| `Salt.MR.FlatSocketFormEps` | 1 |
| `Salt.MR.FlatSocketFormEpsW` | 1 |
| `Salt.MR.FlatSocketFormEpsW_band` | 1 |
| `Salt.MR.FlatSocketFormU` | 1 |
| `Salt.MR.GRowsZeroGate` | 1 |
| `Salt.MR.GRowsZeroGate''_L` | 1 |
| `Salt.MR.L2KernelUniform` | 1 |
| `Salt.MR.Lemma4Datum` | 1 |
| `Salt.MR.M4BlockMeanSqBlk` | 1 |
| `Salt.MR.M4BlockMeanSqBlk2` | 1 |
| `Salt.MR.M4BlockMeanSqBlk2H_L_gk` | 1 |
| `Salt.MR.M4BlockMeanSqSupQ` | 1 |
| `Salt.MR.M4ChiFreeShiftBlockMeanSq` | 1 |
| `Salt.MR.M4ChiShiftBlockMeanSq` | 1 |
| `Salt.MR.M4ChiSummedBlockMeanSqN_L` | 1 |
| `Salt.MR.M4ChiSummedBlockMeanSqN_L_gk` | 1 |
| `Salt.MR.M4ChiSummedFreeRowBigH_L_gk` | 1 |
| `Salt.MR.M4ChiSummedFreeRow_gk` | 1 |
| `Salt.MR.M4ChiSummedFreeShiftBlock` | 1 |
| `Salt.MR.M4ChiSummedFreeShiftBlockH_L_gk` | 1 |
| `Salt.MR.M4CoprimeBlockMeanSqN` | 1 |
| `Salt.MR.M4CoprimeBlockMeanSqN_L` | 1 |
| `Salt.MR.M4CoprimeChiBlockMeanSqN` | 1 |
| `Salt.MR.M4RowMeanSqLam` | 1 |
| `Salt.MR.M4SievedDoorSqBlk` | 1 |
| `Salt.MR.M4SievedDoorSqBlk2` | 1 |
| `Salt.MR.M4SievedDoorSqBlk2H_L_gk` | 1 |
| `Salt.MR.MRTLemmaA4iiFixed34T` | 1 |
| `Salt.MR.MRTParsevalConstantMatch` | 1 |
| `Salt.MR.MRTParsevalConstantMatch_34` | 1 |
| `Salt.MR.MRTPropA3` | 1 |
| `Salt.MR.MRTShortSegmentSplitting` | 1 |
| `Salt.MR.MRTThmA1GJ` | 1 |
| `Salt.MR.MRTThmA1GJ_34` | 1 |
| `Salt.MR.MinorArcBound` | 1 |
| `Salt.MR.NearRat` | 1 |
| `Salt.MR.S13BandGate'_L_gk` | 1 |
| `Salt.MR.S15CrossingBound_gk` | 1 |
| `Salt.MR.S15Sel''_gk` | 1 |
| `Salt.MR.S16BaseScaleCap96_gk` | 1 |
| `Salt.MR.S16BaseScaleCapEnd_LH_gk` | 1 |
| `Salt.MR.S16BaseScaleCapL_gk` | 1 |
| `Salt.MR.S16BaseScaleCap_gk` | 1 |
| `Salt.MR.S4ArrowUncapped` | 1 |
| `Salt.MR.StrideSupplyAllStridesW` | 1 |
| `Salt.MR.V7RatedFormHG_g12b_band` | 1 |
| `Salt.MR.XCeilGateAt` | 1 |
| `Salt.MR.mrtGate` | 1 |
| `Salt.Parity.Z` | 1 |
| `Salt.SW.EstermannInterface` | 1 |
| `Salt.Twelve.WinFrontierM` | 1 |
| `Salt.TwinBar.Admissible` | 1 |
| `Salt.TwinBar.CorrWindowStrong` | 1 |
| `Salt.TwinBar.FourBar` | 1 |
| `Salt.TwinBar.SieveAgree` | 1 |
| `Salt.TwinBar.SieveAgreeCorr` | 1 |
| `Salt.TwinBar.TripleBar` | 1 |
| `Salt.TwinBar.TwinTypeII` | 1 |
| `Salt.Vk.VkSpaced` | 1 |
| `Salt.Vk.ZetaGrowthPow` | 1 |
| `Salt.Vmvt.PairEqFracBound` | 1 |
| `Salt.Vmvt.VmvtBound` | 1 |
| `¬Salt.Chen.IsP2` | 1 |
| `¬Salt.HB.FulcrumQualityPoly` | 1 |
| `¬Salt.MR.MaskSmooth` | 1 |
| `¬Salt.MR.MemS` | 1 |
| `¬Salt.MR.Squarefull` | 1 |
| `¬Salt.MR.WindowSmooth` | 1 |
| `¬Salt.Parity.Completion` | 1 |

## unconditional (6790)

| name | file:line | objects |
|---|---|---|
| `Salt.BV.psiToPiTransfer_holds` | Salt/BV/AbelCore.lean:750 | sieves |
| `Salt.BV.bilinear_LS_shell` | Salt/BV/BilinearLS.lean:279 | sieves, characters |
| `Salt.BV.cs_over_finset_chi` | Salt/BV/BilinearLSDvd.lean:119 | sieves |
| `Salt.BV.bilinear_LS_shell_dvd` | Salt/BV/BilinearLSDvd.lean:252 | sieves, characters |
| `Salt.BV.fourierCutoff_indicator` | Salt/BV/Completion.lean:141 | sieves, exponential sums |
| `Salt.BV.sum_norm_fourierCutoff_le` | Salt/BV/Completion.lean:237 | sieves, exponential sums |
| `Salt.BV.bilinear_factorization` | Salt/BV/Completion.lean:291 | sieves, characters, exponential sums |
| `Salt.BV.sum_card_divisors_le` | Salt/BV/DivisorSum.lean:48 | sieves |
| `Salt.BV.char_LS_max` | Salt/BV/MaxLS.lean:208 | sieves, characters |
| `Salt.BV.psiAP_discrepancy_le` | Salt/BV/MaxReduction.lean:54 | sieves, characters |
| `Salt.BV.psiAP_discrepancy_sup'_le` | Salt/BV/MaxReduction.lean:139 | sieves, characters |
| `Salt.BV.polya_vinogradov` | Salt/BV/PolyaVinogradov.lean:234 | sieves, characters |
| `Salt.BV.norm_psiChi_one_sub_psiTot_le` | Salt/BV/SWChar.lean:196 | sieves, characters |
| `Salt.BV.sup_div_log_pow_le` | Salt/BV/SWMaxY.lean:111 | sieves |
| `Salt.BV.typeI_one_maxdisc_le` | Salt/BV/TypeI.lean:381 | sieves, characters |
| `Salt.BV.typeI_two_maxdisc_le` | Salt/BV/TypeI.lean:463 | sieves, characters |
| `Salt.BV.typeII_block_le` | Salt/BV/TypeII.lean:248 | sieves, characters |
| `Salt.BV.typeII_disc_reduce` | Salt/BV/TypeII.lean:428 | sieves, characters |
| `Salt.BV.typeII_disc_le` | Salt/BV/TypeIIClose.lean:606 | sieves, characters |
| `Salt.BrunLower.esymm_le` | Salt/BrunLower/BlockDecomp.lean:96 | sieves |
| `Salt.BrunLower.block_esymm_le` | Salt/BrunLower/BlockDecomp.lean:161 | sieves |
| `Salt.BrunLower.mainSum_le_blockForm` | Salt/BrunLower/BlockDecomp.lean:173 | sieves |
| `Salt.BrunLower.mainSum_ge_blockForm` | Salt/BrunLower/BlockDecomp.lean:199 | sieves |
| `Salt.BrunLower.mainSum_le_of_upper'` | Salt/BrunLower/BlockDecomp.lean:228 | sieves |
| `Salt.BrunLower.mainSum_ge_of_lower'` | Salt/BrunLower/BlockDecomp.lean:246 | sieves |
| `Salt.BrunLower.zLev_antitone` | Salt/BrunLower/Defs.lean:75 | sieves |
| `Salt.BrunLower.zLev_le_two_iff` | Salt/BrunLower/Defs.lean:85 | sieves |
| `Salt.BrunLower.exists_zLev_le_two` | Salt/BrunLower/Defs.lean:95 | sieves |
| `Salt.BrunLower.zLev_minLevel_le_two` | Salt/BrunLower/Defs.lean:125 | sieves |
| `Salt.BrunLower.exp_minLevel_ge` | Salt/BrunLower/Defs.lean:129 | sieves |
| `Salt.BrunLower.chi_one` | Salt/BrunLower/Defs.lean:187 | sieves |
| `Salt.BrunLower.chi_prime` | Salt/BrunLower/Defs.lean:214 | sieves |
| `Salt.BrunLower.W_pos` | Salt/BrunLower/Defs.lean:278 | sieves |
| `Salt.BrunLower.master_signed` | Salt/BrunLower/Lemma3.lean:388 | sieves |
| `Salt.BrunLower.hcorr_upper` | Salt/BrunLower/Lemma3.lean:860 | sieves |
| `Salt.BrunLower.hcorr_lower` | Salt/BrunLower/Lemma3.lean:873 | sieves |
| `Salt.BrunLower.mainSum_le_blockForm'` | Salt/BrunLower/Lemma3.lean:890 | sieves |
| `Salt.BrunLower.mainSum_ge_blockForm'` | Salt/BrunLower/Lemma3.lean:901 | sieves |
| `Salt.BrunLower.blockTail_le` | Salt/BrunLower/MainTerm.lean:207 | sieves |
| `Salt.BrunLower.mainSum_le_of_upper` | Salt/BrunLower/MainTerm.lean:254 | sieves |
| `Salt.BrunLower.mainSum_ge_of_lower` | Salt/BrunLower/MainTerm.lean:291 | sieves |
| `Salt.BrunLower.LamTwin_pos` | Salt/BrunLower/MertensDischarge.lean:124 | sieves |
| `Salt.BrunLower.LamTwin_le_lam` | Salt/BrunLower/MertensDischarge.lean:134 | sieves |
| `Salt.BrunLower.LamTwin_le_one` | Salt/BrunLower/MertensDischarge.lean:142 | sieves |
| `Salt.BrunLower.log_Wratio_le_ladder` | Salt/BrunLower/MertensDischarge.lean:263 | sieves |
| `Salt.BrunLower.hMert_twin` | Salt/BrunLower/MertensDischarge.lean:602 | sieves |
| `Salt.BrunLower.hMert_twinSieve` | Salt/BrunLower/MertensDischarge.lean:660 | sieves |
| `Salt.BrunLower.sum_vonMangoldt_div_ge` | Salt/BrunLower/MertensWindow.lean:53 | sieves |
| `Salt.BrunLower.abs_Sfun_sub_log_le` | Salt/BrunLower/MertensWindow.lean:340 | sieves |
| `Salt.BrunLower.sum_inv_le_of_prime_window` | Salt/BrunLower/MertensWindow.lean:595 | sieves |
| `Salt.BrunLower.sum_inv_prime_window_le` | Salt/BrunLower/MertensWindow.lean:656 | sieves |
| `Salt.BrunLower.sum_inv_le_of_subset_window` | Salt/BrunLower/MertensWindow.lean:665 | sieves |
| `Salt.BrunLower.errSum_le_remainder_prod` | Salt/BrunLower/Pair.lean:65 | sieves |
| `Salt.BrunLower.brun_lower` | Salt/BrunLower/Pair.lean:97 | sieves |
| `Salt.BrunLower.brun_upper` | Salt/BrunLower/Pair.lean:136 | sieves |
| `Salt.BrunLower.sum_moebius_chi_upper` | Salt/BrunLower/Pointwise.lean:200 | sieves |
| `Salt.BrunLower.sum_moebius_chi_lower` | Salt/BrunLower/Pointwise.lean:218 | sieves |
| `Salt.BrunLower.isUpperMoebius_moebius_chiOne` | Salt/BrunLower/Pointwise.lean:288 | sieves |
| `Salt.BrunLower.isLowerMoebius_moebius_chiTwo` | Salt/BrunLower/Pointwise.lean:305 | sieves |
| `Salt.BrunLower.capSum_le` | Salt/BrunLower/Remainder.lean:51 | sieves |
| `Salt.BrunLower.capSum_master` | Salt/BrunLower/Remainder.lean:192 | sieves |
| `Salt.BrunLower.remainder_prod_bound` | Salt/BrunLower/Remainder.lean:499 | sieves |
| `Salt.BrunLower.remainder_prod_bound_of_R` | Salt/BrunLower/Remainder.lean:568 | sieves |
| `Salt.BrunLower.margin_ge` | Salt/BrunLower/TwinInstance.lean:359 | sieves |
| `Salt.BrunLower.margin_ge_b1` | Salt/BrunLower/TwinInstance.lean:387 | sieves |
| `Salt.BrunLower.twin_almost_prime` | Salt/BrunLower/TwinInstance.lean:798 | sieves |
| `Salt.BrunLower.Wratio_pos` | Salt/BrunLower/WRatio.lean:109 | sieves |
| `Salt.BrunLower.windowSum_nonneg` | Salt/BrunLower/WRatio.lean:115 | sieves |
| `Salt.BrunLower.windowSum_le_log_Wratio` | Salt/BrunLower/WRatio.lean:135 | sieves |
| `Salt.BrunLower.Wratio_le_exp` | Salt/BrunLower/WRatio.lean:156 | sieves |
| `Salt.BrunLower.windowSum_le` | Salt/BrunLower/WRatio.lean:173 | sieves |
| `Salt.Certs.cert_bounded_gaps_iff` | Salt/Certs/BoundedGaps.lean:94 | other |
| `Salt.Certs.cert_bounded_gaps` | Salt/Certs/BoundedGaps.lean:115 | other |
| `Salt.Certs.cert_bounded_gaps_infinitely_many_iff` | Salt/Certs/BoundedGaps.lean:125 | other |
| `Salt.Certs.cert_bounded_gaps_infinitely_many` | Salt/Certs/BoundedGaps.lean:140 | other |
| `Salt.Certs.cert_chen` | Salt/Certs/Chen.lean:168 | other |
| `Salt.Certs.cert_chen_omega` | Salt/Certs/Chen.lean:193 | other |
| `Salt.Certs.cert_chen_goldbach_isP2_iff` | Salt/Certs/ChenGoldbach.lean:73 | other |
| `Salt.Certs.cert_chen_goldbach` | Salt/Certs/ChenGoldbach.lean:89 | other |
| `Salt.Certs.cert_log_chowla_door_only` | Salt/Certs/ChowlaSpine.lean:74 | characters, exponential sums |
| `Salt.Certs.cert_log_chowla_budget_head` | Salt/Certs/ChowlaSpine.lean:107 | characters, exponential sums |
| `Salt.Certs.cert_kloosterman_estermann` | Salt/Certs/Kloosterman.lean:83 | other |
| `Salt.Certs.cert_weil_bound_prime` | Salt/Certs/Kloosterman.lean:97 | other |
| `Salt.Certs.cert_weil_bound_prime_witness` | Salt/Certs/Kloosterman.lean:127 | other |
| `Salt.Certs.cert_analytic_large_sieve` | Salt/Certs/LargeSieve.lean:63 | sieves |
| `Salt.Certs.cert_analytic_large_sieve_witness` | Salt/Certs/LargeSieve.lean:82 | sieves |
| `Salt.Certs.cert_char_large_sieve` | Salt/Certs/LargeSieve.lean:96 | sieves, characters |
| `Salt.Certs.cert_char_large_sieve_witness` | Salt/Certs/LargeSieve.lean:140 | sieves |
| `Salt.Certs.cert_char_large_sieve_level_one_primitive` | Salt/Certs/LargeSieve.lean:144 | sieves, characters |
| `Salt.Certs.cert_char_large_sieve_level_two_not_primitive` | Salt/Certs/LargeSieve.lean:152 | sieves, characters |
| `Salt.Certs.cert_parity_gap_witness` | Salt/Certs/ParityGap.lean:97 | other |
| `Salt.Certs.cert_siegel_walfisz` | Salt/Certs/SiegelWalfisz.lean:73 | other |
| `Salt.Certs.cert_twin_bar` | Salt/Certs/TwinBar.lean:103 | other |
| `Salt.Certs.cert_no_twin_weight` | Salt/Certs/TwinBar.lean:120 | other |
| `Salt.Certs.cert_least_k` | Salt/Certs/TwinBar.lean:140 | other |
| `Salt.Certs.cert_twin_bar_witness` | Salt/Certs/TwinBar.lean:183 | other |
| `Salt.Certs.cert_vaughan` | Salt/Certs/Vaughan.lean:80 | sieves |
| `Salt.Certs.cert_vaughan_witness` | Salt/Certs/Vaughan.lean:93 | sieves |
| `Salt.Certs.cert_vmvt_iff` | Salt/Certs/Vmvt.lean:96 | other |
| `Salt.Certs.cert_vmvt` | Salt/Certs/Vmvt.lean:145 | other |
| `Salt.Certs.cert_vmvt_witness` | Salt/Certs/Vmvt.lean:157 | other |
| `Salt.Certs.cert_zeta_zero_free_pow` | Salt/Certs/ZetaPowRegion.lean:70 | zeros |
| `Salt.Chen.massSum_le_A2_sharp` | Salt/Chen/A2Weighted.lean:102 | sieves |
| `Salt.Chen.A2grid_sharp_le` | Salt/Chen/A2Weighted.lean:461 | sieves |
| `Salt.Chen.A2grid_window_le` | Salt/Chen/A2Window.lean:232 | sieves |
| `Salt.Chen.A2grid_window_additive` | Salt/Chen/A2Window.lean:310 | sieves |
| `Salt.Chen.razor_window_cost` | Salt/Chen/A2Window.lean:343 | sieves |
| `Salt.Chen.logRatio_A2_window_mem` | Salt/Chen/A2Window.lean:377 | sieves |
| `Salt.Chen.prime_sum_abel_antitone` | Salt/Chen/AbelPass.lean:262 | sieves |
| `Salt.Chen.prime_sum_abel_monotone` | Salt/Chen/AbelPass.lean:401 | sieves |
| `Salt.Chen.applicationA` | Salt/Chen/AbelPass.lean:554 | sieves |
| `Salt.Chen.Ifun_closed_form` | Salt/Chen/AbelPass2.lean:129 | sieves |
| `Salt.Chen.Ifun_hasDerivAt` | Salt/Chen/AbelPass2.lean:241 | sieves |
| `Salt.Chen.Ifun_deriv_nonpos` | Salt/Chen/AbelPass2.lean:260 | sieves |
| `Salt.Chen.applicationB` | Salt/Chen/AbelPass2.lean:365 | sieves |
| `Salt.Chen.Ifun_integral_eq_cbar` | Salt/Chen/AbelPass2.lean:404 | sieves |
| `Salt.Chen.weightedPairSum_fibered` | Salt/Chen/AbelPass2.lean:466 | sieves |
| `Salt.Chen.telescope_ge` | Salt/Chen/AbelStep.lean:109 | sieves |
| `Salt.Chen.stepHyp_lhs_eq` | Salt/Chen/AbelStep.lean:157 | sieves |
| `Salt.Chen.telescope_window_upper` | Salt/Chen/AbelStep.lean:173 | sieves |
| `Salt.Chen.telescope_window_lower` | Salt/Chen/AbelStep.lean:209 | sieves |
| `Salt.Chen.ledger_collect` | Salt/Chen/AbelStep.lean:235 | sieves |
| `Salt.Chen.stepHyp_of_comparisons` | Salt/Chen/AbelStep.lean:266 | sieves |
| `Salt.Chen.nonunit_forces_fst_dvd` | Salt/Chen/AggCE.lean:75 | sieves |
| `Salt.Chen.nuChen_sum_dvd_le` | Salt/Chen/AggCE.lean:130 | sieves |
| `Salt.Chen.hCE_at_op` | Salt/Chen/AggCE.lean:212 | sieves |
| `Salt.Chen.crumb_le_rpow_at_op` | Salt/Chen/AggDiag.lean:58 | sieves |
| `Salt.Chen.opPdiag_compat` | Salt/Chen/AggDiag.lean:192 | sieves |
| `Salt.Chen.hdiag_slot_at_op` | Salt/Chen/AggDiag.lean:288 | sieves |
| `Salt.Chen.kerr_ratio_term_le` | Salt/Chen/AggSum.lean:77 | sieves |
| `Salt.Chen.boxPriceKerr_worst_le` | Salt/Chen/AggSum.lean:135 | sieves |
| `Salt.Chen.hSum_at_op` | Salt/Chen/AggSum.lean:278 | sieves |
| `Salt.Chen.sum_totient_div_sqrt_le` | Salt/Chen/AlphaClose.lean:82 | sieves |
| `Salt.Chen.efold_large_fibered` | Salt/Chen/AlphaClose.lean:119 | sieves |
| `Salt.Chen.efold_large_reduce` | Salt/Chen/AlphaClose.lean:239 | sieves |
| `Salt.Chen.efold_large_discharge` | Salt/Chen/AlphaClose.lean:390 | sieves |
| `Salt.Chen.general_BV_alpha_final` | Salt/Chen/AlphaClose.lean:735 | sieves |
| `Salt.Chen.efold_alpha_reduce_dense` | Salt/Chen/AlphaSide.lean:230 | sieves |
| `Salt.Chen.efold_small_le` | Salt/Chen/AlphaSide.lean:311 | sieves, characters |
| `Salt.Chen.efold_large_fourterm` | Salt/Chen/AlphaSide.lean:336 | sieves |
| `Salt.Chen.efold_alpha_le` | Salt/Chen/AlphaSide.lean:374 | sieves |
| `Salt.Chen.efold_small_discharge` | Salt/Chen/AlphaSide.lean:419 | sieves, characters |
| `Salt.Chen.general_BV_alpha_discharged` | Salt/Chen/AlphaSide.lean:547 | sieves |
| `Salt.Chen.box_price_at_op` | Salt/Chen/AssembleA3.lean:142 | sieves |
| `Salt.Chen.low_price_at_op` | Salt/Chen/AssembleA3b.lean:147 | sieves |
| `Salt.Chen.sym_price_at_op` | Salt/Chen/AssembleA3b.lean:380 | sieves |
| `Salt.Chen.razor_reduction` | Salt/Chen/Assembly.lean:191 | sieves |
| `Salt.Chen.triplePrimeSum_le` | Salt/Chen/Assembly.lean:305 | sieves |
| `Salt.Chen.chen_positivity` | Salt/Chen/Assembly.lean:358 | sieves |
| `Salt.Chen.chen_survivor` | Salt/Chen/Assembly.lean:383 | sieves |
| `Salt.Chen.chen_of_hypotheses` | Salt/Chen/Assembly.lean:425 | sieves |
| `Salt.Chen.factors_ge_z_of_sift_W` | Salt/Chen/Assembly.lean:502 | sieves |
| `Salt.Chen.razor_reduction_W` | Salt/Chen/Assembly.lean:540 | sieves |
| `Salt.Chen.stripPrimeSum_le_W` | Salt/Chen/Assembly.lean:584 | sieves |
| `Salt.Chen.chen_positivity_W` | Salt/Chen/Assembly.lean:657 | sieves |
| `Salt.Chen.chen_survivor_W` | Salt/Chen/Assembly.lean:673 | sieves |
| `Salt.Chen.chen_of_hypotheses_W` | Salt/Chen/Assembly.lean:715 | sieves |
| `Salt.Chen.residue_witness` | Salt/Chen/Assembly.lean:739 | sieves |
| `Salt.Chen.sum_inv_totient_le_Winv` | Salt/Chen/BVSum.lean:116 | sieves |
| `Salt.Chen.rosserRemainder_le_split` | Salt/Chen/BVSum.lean:203 | sieves |
| `Salt.Chen.convSum_le` | Salt/Chen/BVSum.lean:251 | sieves |
| `Salt.Chen.twinA1_hBV` | Salt/Chen/BVSum.lean:314 | sieves |
| `Salt.Chen.symCard_two_mul` | Salt/Chen/BandClose.lean:151 | sieves |
| `Salt.Chen.bandCard_split` | Salt/Chen/BandClose.lean:208 | sieves |
| `Salt.Chen.bandDisc_eq_three` | Salt/Chen/BandClose.lean:337 | sieves |
| `Salt.Chen.bandDisc_le_three_pieces` | Salt/Chen/BandClose.lean:357 | sieves |
| `Salt.Chen.Plo_discharge` | Salt/Chen/BandClose.lean:389 | sieves |
| `Salt.Chen.norm_blockAlphaLow_le_one` | Salt/Chen/BandIdent.lean:79 | sieves |
| `Salt.Chen.lowRect_eq_apDiscBilinCutoff` | Salt/Chen/BandIdent.lean:232 | sieves |
| `Salt.Chen.norm_blockAlphaSym_le_one` | Salt/Chen/BandIdent.lean:358 | sieves |
| `Salt.Chen.symRect_eq_apDiscBilinCutoff` | Salt/Chen/BandIdent.lean:524 | sieves |
| `Salt.Chen.Plo_discharge_priced` | Salt/Chen/BandIdent.lean:613 | sieves |
| `Salt.Chen.sum_symm_ordered_split` | Salt/Chen/BandSplit.lean:97 | sieves |
| `Salt.Chen.bandDiagCount_le` | Salt/Chen/BandSplit.lean:185 | sieves |
| `Salt.Chen.thetaAP_SW` | Salt/Chen/BetaSW.lean:266 | sieves |
| `Salt.Chen.prime_indicator_SW` | Salt/Chen/BetaSW.lean:368 | sieves |
| `Salt.Chen.prime_indicator_coprime_SW` | Salt/Chen/BetaSW.lean:582 | sieves |
| `Salt.Chen.regroup_bilin` | Salt/Chen/BilinearDescent.lean:139 | sieves, characters |
| `Salt.Chen.swapPhi_generic` | Salt/Chen/BilinearDescent.lean:204 | sieves |
| `Salt.Chen.perd_energy_le` | Salt/Chen/BilinearDescent.lean:240 | sieves, characters |
| `Salt.Chen.bilinear_hLargeDisc` | Salt/Chen/BilinearDescent.lean:329 | sieves, characters |
| `Salt.Chen.blockSwitchSieve_rem_split` | Salt/Chen/BlockPricing.lean:246 | sieves |
| `Salt.Chen.blockRem_rosserRemainder_split_le` | Salt/Chen/BlockPricing.lean:295 | sieves |
| `Salt.Chen.sum_blockRem_split_le` | Salt/Chen/BlockPricing.lean:314 | sieves |
| `Salt.Chen.norm_blockPieceAlpha_le_one` | Salt/Chen/BlockPricing.lean:344 | sieves |
| `Salt.Chen.hHDblocks_of_perBlock` | Salt/Chen/BlockPricing.lean:356 | sieves |
| `Salt.Chen.hBVblocks_of_generalBV` | Salt/Chen/BlockPricing.lean:377 | sieves |
| `Salt.Chen.brun_lower_ell1` | Salt/Chen/BrunEll1.lean:191 | sieves |
| `Salt.Chen.mainSum_moebius_eq_W` | Salt/Chen/Buchstab.lean:205 | sieves |
| `Salt.Chen.mainSum_lam_defect` | Salt/Chen/Buchstab.lean:214 | sieves |
| `Salt.Chen.linear_sieve_upper_rosser` | Salt/Chen/Buchstab.lean:265 | sieves |
| `Salt.Chen.linear_sieve_lower_rosser` | Salt/Chen/Buchstab.lean:327 | sieves |
| `Salt.Chen.cbar_lt` | Salt/Chen/CbarCert.lean:21117 | sieves |
| `Salt.Chen.one_le_Fchain` | Salt/Chen/ChainValues.lean:86 | sieves |
| `Salt.Chen.fchain_lower_of_evenSum_le` | Salt/Chen/ChainValues.lean:124 | sieves |
| `Salt.Chen.Fchain_upper_of_oddSum_le` | Salt/Chen/ChainValues.lean:132 | sieves |
| `Salt.Chen.fseq_two_le_sq` | Salt/Chen/ChainValues.lean:152 | sieves |
| `Salt.Chen.fchain_two_lower` | Salt/Chen/ChainValues.lean:200 | sieves |
| `Salt.Chen.fchain_trunc_close` | Salt/Chen/ChainValues.lean:215 | sieves |
| `Salt.Chen.chen_ledger_line` | Salt/Chen/ChainValues.lean:257 | sieves |
| `Salt.Chen.boundary_XM_raw` | Salt/Chen/ChenFinal.lean:66 | sieves |
| `Salt.Chen.boundary_log_bounds` | Salt/Chen/ChenFinal.lean:135 | sieves |
| `Salt.Chen.xm_sqrt_bounds` | Salt/Chen/ChenFinal.lean:145 | sieves |
| `Salt.Chen.d0_window_of_XM_band` | Salt/Chen/ChenFinal2.lean:68 | sieves |
| `Salt.Chen.band_kfloor_of_live` | Salt/Chen/ChenFinal2.lean:283 | sieves |
| `Salt.Chen.medium_box_price_at_op_band` | Salt/Chen/ChenFinal2.lean:327 | sieves |
| `Salt.Chen.sym_box_hprice_at_2pow_band` | Salt/Chen/ChenFinal2.lean:409 | sieves |
| `Salt.Chen.low_box_hprice_at_2pow_band` | Salt/Chen/ChenFinal2.lean:489 | sieves |
| `Salt.Chen.kfloor_of_live_box` | Salt/Chen/ChenHeadline.lean:48 | sieves |
| `Salt.Chen.box_hprice_at_2pow_lo` | Salt/Chen/ChenHeadline.lean:119 | sieves |
| `Salt.Chen.box_rows_at_op` | Salt/Chen/ChenRows1.lean:573 | sieves |
| `Salt.Chen.blockAlphaSym_eq_blockAlphaLow_of_le` | Salt/Chen/ChenRows2.lean:112 | sieves |
| `Salt.Chen.middle_k_band_floor` | Salt/Chen/ChenRows2.lean:136 | sieves |
| `Salt.Chen.band_price_rows_at_op` | Salt/Chen/ChenRows2.lean:443 | sieves |
| `Salt.Chen.low_rows_at_op` | Salt/Chen/ChenRows2.lean:563 | sieves |
| `Salt.Chen.sym_rows_at_op` | Salt/Chen/ChenRows2.lean:676 | sieves |
| `Salt.Chen.chen_headline` | Salt/Chen/ChenTheorem.lean:32 | sieves |
| `Salt.Chen.bilinTwist_eq_sum_class` | Salt/Chen/ConductorDescent.lean:75 | sieves, characters |
| `Salt.Chen.bilinTwist_le_of_classDisc` | Salt/Chen/ConductorDescent.lean:98 | sieves, characters |
| `Salt.Chen.hβSW_of_prime_indicator` | Salt/Chen/ConductorDescent.lean:175 | sieves, characters |
| `Salt.Chen.general_BV_closed` | Salt/Chen/ConductorDescent.lean:231 | sieves, characters |
| `Salt.Chen.hcount_massBridge` | Salt/Chen/CountAtOp.lean:111 | sieves |
| `Salt.Chen.hcount_op_geometry` | Salt/Chen/CountAtOp.lean:140 | sieves |
| `Salt.Chen.hcount_at_op` | Salt/Chen/CountAtOp.lean:213 | sieves |
| `Salt.Chen.hcount_Lval_rows` | Salt/Chen/CountAtOp2.lean:169 | sieves |
| `Salt.Chen.Ifun_op_le` | Salt/Chen/CountAtOp2.lean:243 | sieves |
| `Salt.Chen.S1set_mertens` | Salt/Chen/CountAtOp2.lean:298 | sieves |
| `Salt.Chen.slack_collapse` | Salt/Chen/CountAtOp2.lean:321 | sieves |
| `Salt.Chen.ESW_main_fold` | Salt/Chen/CountAtOp2.lean:354 | sieves |
| `Salt.Chen.count_bound_uniformK` | Salt/Chen/CountAtOp3.lean:65 | sieves |
| `Salt.Chen.corr_le_at_op` | Salt/Chen/CountAtOp3.lean:401 | sieves |
| `Salt.Chen.hcount_star_at_op` | Salt/Chen/CountAtOp3.lean:732 | sieves |
| `Salt.Chen.hcount_slot_closed` | Salt/Chen/CountAtOp3.lean:1017 | sieves |
| `Salt.Chen.S2set_subset_primesInWindow` | Salt/Chen/CountClose.lean:66 | sieves |
| `Salt.Chen.S1set_subset_insert` | Salt/Chen/CountClose.lean:91 | sieves |
| `Salt.Chen.tail187_integral_le` | Salt/Chen/CountClose.lean:129 | sieves |
| `Salt.Chen.tripleSum_le_weighted_pairSum'` | Salt/Chen/CountFinal.lean:172 | sieves |
| `Salt.Chen.weightedPairSum'_le_cbar` | Salt/Chen/CountFinal.lean:399 | sieves |
| `Salt.Chen.tripleSum_le_cbar_final` | Salt/Chen/CountFinal.lean:555 | sieves |
| `Salt.Chen.tripleSumW_equidist` | Salt/Chen/CountW.lean:604 | sieves |
| `Salt.Chen.tripleSum_le_cbar_final_W` | Salt/Chen/CountW.lean:679 | sieves |
| `Salt.Chen.hBJS_antitone` | Salt/Chen/DecayMass.lean:51 | sieves |
| `Salt.Chen.prime_tail_mass_le` | Salt/Chen/DecayMass.lean:135 | sieves |
| `Salt.Chen.decay_mass_le` | Salt/Chen/DecayMass.lean:269 | sieves |
| `Salt.Chen.hh_of_window` | Salt/Chen/DecayMass.lean:441 | sieves |
| `Salt.Chen.stepHyp_pointwise` | Salt/Chen/DecayMass.lean:532 | sieves |
| `Salt.Chen.card_divisors_subpoly` | Salt/Chen/DivisorBound.lean:188 | sieves |
| `Salt.Chen.card_divisors_cube_root` | Salt/Chen/DivisorBound.lean:218 | sieves |
| `Salt.Chen.hdiv_discharge` | Salt/Chen/DivisorBound.lean:239 | sieves |
| `Salt.Chen.block_energy_le_dvd` | Salt/Chen/DyadicDvd.lean:103 | sieves |
| `Salt.Chen.dyadic_large_reduction_dvd` | Salt/Chen/DyadicDvd.lean:150 | sieves |
| `Salt.Chen.geom_shell_sum_le_dvd` | Salt/Chen/DyadicDvd.lean:208 | sieves |
| `Salt.Chen.dyadic_energy_le_dvd` | Salt/Chen/DyadicDvd.lean:328 | sieves |
| `Salt.Chen.smallConductor_energy_le` | Salt/Chen/EnergyClose.lean:400 | sieves, characters |
| `Salt.Chen.hMainEnergy_discharge` | Salt/Chen/EnergyClose.lean:768 | sieves, characters |
| `Salt.Chen.bilinTwist_sub_primitive_eq` | Salt/Chen/EnergyClose.lean:864 | sieves, characters |
| `Salt.Chen.bilinTwist_energy_le_dvd` | Salt/Chen/EnergyShellDvd.lean:87 | sieves, characters |
| `Salt.Chen.energy_shell_dvd` | Salt/Chen/EnergyShellDvd.lean:177 | sieves |
| `Salt.Chen.bilinTwist_efold` | Salt/Chen/ErrFold.lean:181 | sieves, characters |
| `Salt.Chen.hErrSum_reorg` | Salt/Chen/ErrFold.lean:316 | sieves, characters |
| `Salt.Chen.hErrSum_discharge` | Salt/Chen/ErrFold.lean:437 | sieves, characters |
| `Salt.Chen.Fchain_switch_le` | Salt/Chen/FchainPoint.lean:64 | sieves |
| `Salt.Chen.tripleSum_le_16x_at_op` | Salt/Chen/FinA3.lean:180 | sieves |
| `Salt.Chen.box_price_indep` | Salt/Chen/FinA3.lean:227 | sieves |
| `Salt.Chen.low_price_indep` | Salt/Chen/FinA3b.lean:34 | sieves |
| `Salt.Chen.sym_price_indep` | Salt/Chen/FinA3b.lean:260 | sieves |
| `Salt.Chen.priceBoxOp_le` | Salt/Chen/FinA3c.lean:57 | sieves |
| `Salt.Chen.priceLowOp_le` | Salt/Chen/FinA3c.lean:78 | sieves |
| `Salt.Chen.hA3_bundle` | Salt/Chen/FinA3c.lean:99 | sieves |
| `Salt.Chen.two_le_maxDepth_A1` | Salt/Chen/FinLed.lean:75 | sieves |
| `Salt.Chen.hcertA1_at_op` | Salt/Chen/FinLed.lean:104 | sieves |
| `Salt.Chen.hcertA3_at_op` | Salt/Chen/FinLed.lean:118 | sieves |
| `Salt.Chen.hcount_seam` | Salt/Chen/FinLed.lean:151 | sieves |
| `Salt.Chen.XW_lower_at_op` | Salt/Chen/FinLed.lean:311 | sieves |
| `Salt.Chen.A2grid_topwindow_le` | Salt/Chen/FinLed2.lean:337 | sieves |
| `Salt.Chen.razor_topwindow_cost` | Salt/Chen/FinLed2.lean:421 | sieves |
| `Salt.Chen.logRatio_A2_topwindow_mem` | Salt/Chen/FinLed2.lean:440 | sieves |
| `Salt.Chen.hcertA2_at_op` | Salt/Chen/FinLed2.lean:624 | sieves |
| `Salt.Chen.hL_bundle` | Salt/Chen/FinLed3.lean:646 | sieves |
| `Salt.Chen.hBJS_window_min` | Salt/Chen/FlatFuncbound.lean:47 | sieves |
| `Salt.Chen.hBJS_funcbound_flat` | Salt/Chen/FlatFuncbound.lean:73 | sieves |
| `Salt.Chen.flat_h_contract` | Salt/Chen/FlatFuncbound.lean:96 | sieves |
| `Salt.Chen.antitone_integral_lower` | Salt/Chen/FseqAntitone.lean:41 | sieves |
| `Salt.Chen.fseq_one_antitoneOn_Ici` | Salt/Chen/FseqAntitone.lean:54 | sieves |
| `Salt.Chen.fseq_antitoneOn_odd` | Salt/Chen/FseqAntitone.lean:74 | sieves |
| `Salt.Chen.fseq_antitoneOn_even` | Salt/Chen/FseqAntitone.lean:127 | sieves |
| `Salt.Chen.apDiscBilin_orthogonality` | Salt/Chen/GeneralBV.lean:125 | sieves, characters |
| `Salt.Chen.norm_apDiscBilin_le` | Salt/Chen/GeneralBV.lean:196 | sieves, characters |
| `Salt.Chen.bilinTwist_energy_le` | Salt/Chen/GeneralBV.lean:255 | sieves, characters |
| `Salt.Chen.general_BV_weak` | Salt/Chen/GeneralBV.lean:403 | sieves, characters |
| `Salt.Chen.cutoff_BV_at_op` | Salt/Chen/GlueBV.lean:184 | sieves |
| `Salt.Chen.hCE_discharge` | Salt/Chen/GlueBV.lean:258 | sieves |
| `Salt.Chen.diag_nu_crumb` | Salt/Chen/GlueBV.lean:281 | sieves |
| `Salt.Chen.catch64_D0_window_empty` | Salt/Chen/GlueFinal.lean:165 | sieves |
| `Salt.Chen.catch64_op_boundary_infeasible` | Salt/Chen/GlueFinal.lean:323 | sieves |
| `Salt.Chen.hyx_at_op` | Salt/Chen/GlueFinal.lean:353 | sieves |
| `Salt.Chen.sievePrimorial_dvd` | Salt/Chen/GlueFinal.lean:373 | sieves |
| `Salt.Chen.hDsq_row` | Salt/Chen/GlueFinal.lean:381 | sieves |
| `Salt.Chen.hfloor_row` | Salt/Chen/GlueFinal.lean:420 | sieves |
| `Salt.Chen.habs_row` | Salt/Chen/GlueFinal.lean:512 | sieves |
| `Salt.Chen.logRatio_A3_mem_range` | Salt/Chen/GlueFinal.lean:668 | sieves |
| `Salt.Chen.hmA1_normalized` | Salt/Chen/GlueNormalized.lean:101 | sieves |
| `Salt.Chen.hmA2_normalized` | Salt/Chen/GlueNormalized.lean:118 | sieves |
| `Salt.Chen.hmA3_normalized` | Salt/Chen/GlueNormalized.lean:145 | sieves |
| `Salt.Chen.errorBundle_le` | Salt/Chen/GlueNormalized.lean:210 | sieves |
| `Salt.Chen.normalized_package` | Salt/Chen/GlueNormalized.lean:232 | sieves |
| `Salt.Chen.h4_cond_of_base` | Salt/Chen/H4Cond.lean:55 | sieves |
| `Salt.Chen.catch65_slot_torn` | Salt/Chen/Headline.lean:128 | sieves |
| `Salt.Chen.catch65_no_H_at_odd_P` | Salt/Chen/Headline.lean:172 | sieves |
| `Salt.Chen.band_habs_row` | Salt/Chen/Headline3.lean:48 | sieves |
| `Salt.Chen.middle_k_M_le_two_y` | Salt/Chen/Headline3.lean:169 | sieves |
| `Salt.Chen.chen_headline_of_ops` | Salt/Chen/Headline4.lean:84 | sieves |
| `Salt.Chen.hA1_bundle` | Salt/Chen/Headline4.lean:163 | sieves |
| `Salt.Chen.hA2_bundle` | Salt/Chen/Headline4.lean:189 | sieves |
| `Salt.Chen.chen_headline_of_A3_ledger` | Salt/Chen/Headline4.lean:237 | sieves |
| `Salt.Chen.catch68_price_rows_nonneg` | Salt/Chen/HeadlineW.lean:130 | sieves |
| `Salt.Chen.catch68_hSum_hNum_infeasible` | Salt/Chen/HeadlineW.lean:166 | sieves |
| `Salt.Chen.neg_log_nu_le` | Salt/Chen/Hyp4.lean:69 | sieves |
| `Salt.Chen.vratio_prod_le` | Salt/Chen/Hyp4.lean:124 | sieves |
| `Salt.Chen.w0R_threshold` | Salt/Chen/Hyp4.lean:230 | sieves |
| `Salt.Chen.thresh_mono` | Salt/Chen/Hyp4.lean:253 | sieves |
| `Salt.Chen.vratio_window_le` | Salt/Chen/Hyp4.lean:283 | sieves |
| `Salt.Chen.h4_base` | Salt/Chen/Hyp4.lean:300 | sieves |
| `Salt.Chen.prod_telescope` | Salt/Chen/Lemma11.lean:73 | sieves |
| `Salt.Chen.T_one_upper` | Salt/Chen/Lemma11.lean:195 | sieves |
| `Salt.Chen.T_two_one_zero` | Salt/Chen/Lemma11.lean:218 | sieves |
| `Salt.Chen.hlevel_one_upper` | Salt/Chen/Lemma11.lean:277 | sieves |
| `Salt.Chen.tau_sum_le_of_recursion` | Salt/Chen/Lemma11.lean:316 | sieves |
| `Salt.Chen.hTbound_upper_of_levels` | Salt/Chen/Lemma11.lean:386 | sieves |
| `Salt.Chen.hTbound_lower_of_levels` | Salt/Chen/Lemma11.lean:421 | sieves |
| `Salt.Chen.linear_sieve_upper_rosser_assembled_final` | Salt/Chen/Lemma11.lean:484 | sieves |
| `Salt.Chen.linear_sieve_lower_rosser_assembled_final` | Salt/Chen/Lemma11.lean:498 | sieves |
| `Salt.Chen.TruncSieve.isUpperMoebius` | Salt/Chen/LinearSieve.lean:264 | sieves |
| `Salt.Chen.TruncSieve.isLowerMoebius` | Salt/Chen/LinearSieve.lean:282 | sieves |
| `Salt.Chen.linear_sieve_upper` | Salt/Chen/LinearSieve.lean:333 | sieves |
| `Salt.Chen.linear_sieve_lower` | Salt/Chen/LinearSieve.lean:349 | sieves |
| `Salt.Chen.linear_sieve_upper_chain` | Salt/Chen/LinearSieve.lean:377 | sieves |
| `Salt.Chen.linear_sieve_lower_chain` | Salt/Chen/LinearSieve.lean:389 | sieves |
| `Salt.Chen.rosserCond_one` | Salt/Chen/LinearSieve.lean:497 | sieves |
| `Salt.Chen.rosserSieve_isUpperMoebius` | Salt/Chen/LinearSieve.lean:579 | sieves |
| `Salt.Chen.rosserSieve_isLowerMoebius` | Salt/Chen/LinearSieve.lean:584 | sieves |
| `Salt.Chen.log_half_le_tangent` | Salt/Chen/LogToolkit.lean:98 | sieves |
| `Salt.Chen.log_half_ge_chord` | Salt/Chen/LogToolkit.lean:110 | sieves |
| `Salt.Chen.integral_quad` | Salt/Chen/LogToolkit.lean:141 | sieves |
| `Salt.Chen.panel_le` | Salt/Chen/LogToolkit.lean:159 | sieves |
| `Salt.Chen.panel_ge` | Salt/Chen/LogToolkit.lean:171 | sieves |
| `Salt.Chen.log_two_le` | Salt/Chen/LogToolkit.lean:184 | sieves |
| `Salt.Chen.le_log_two` | Salt/Chen/LogToolkit.lean:189 | sieves |
| `Salt.Chen.log_three_le` | Salt/Chen/LogToolkit.lean:204 | sieves |
| `Salt.Chen.le_log_three` | Salt/Chen/LogToolkit.lean:210 | sieves |
| `Salt.Chen.cflatI_tight` | Salt/Chen/LogToolkit.lean:1025 | sieves |
| `Salt.Chen.cflatI_lower` | Salt/Chen/LogToolkit.lean:1075 | sieves |
| `Salt.Chen.massE_two_tight` | Salt/Chen/LogToolkit.lean:1797 | sieves |
| `Salt.Chen.massE_two_lower` | Salt/Chen/LogToolkit.lean:1847 | sieves |
| `Salt.Chen.Cphi2_tight` | Salt/Chen/LogToolkit.lean:2198 | sieves |
| `Salt.Chen.fseq_odd_continuousOn` | Salt/Chen/MassCert.lean:88 | sieves |
| `Salt.Chen.massE_recursion` | Salt/Chen/MassCert.lean:154 | sieves |
| `Salt.Chen.cflatI_le_half` | Salt/Chen/MassCert.lean:266 | sieves |
| `Salt.Chen.massE_flat_split` | Salt/Chen/MassCert.lean:329 | sieves |
| `Salt.Chen.massE_two_le` | Salt/Chen/MassCert.lean:366 | sieves |
| `Salt.Chen.massE_two_le_half` | Salt/Chen/MassCert.lean:417 | sieves |
| `Salt.Chen.massSum_reindex` | Salt/Chen/MassCert.lean:432 | sieves |
| `Salt.Chen.massEvenSum_tail_le` | Salt/Chen/MassCert.lean:455 | sieves |
| `Salt.Chen.massSum_le_head_add_geomtail` | Salt/Chen/MassCert.lean:464 | sieves |
| `Salt.Chen.fseq_odd_le_massE_div` | Salt/Chen/MassCert2.lean:102 | sieves |
| `Salt.Chen.fseq_even_le_massO_div` | Salt/Chen/MassCert2.lean:132 | sieves |
| `Salt.Chen.fseq_even_continuousOn` | Salt/Chen/MassCert2.lean:167 | sieves |
| `Salt.Chen.massTail_eq_phiMoment` | Salt/Chen/MassCert2.lean:213 | sieves |
| `Salt.Chen.massE_eq_flat_phiMoment` | Salt/Chen/MassCert2.lean:350 | sieves |
| `Salt.Chen.Cphi2_le` | Salt/Chen/MassCert2.lean:441 | sieves |
| `Salt.Chen.Cphi1_le` | Salt/Chen/MassCert2.lean:462 | sieves |
| `Salt.Chen.massE_nonneg` | Salt/Chen/MassLedger.lean:56 | sieves |
| `Salt.Chen.fseq_odd_eq_massE` | Salt/Chen/MassLedger.lean:68 | sieves |
| `Salt.Chen.Fchain_mass_ledger` | Salt/Chen/MassLedger.lean:93 | sieves |
| `Salt.Chen.Fchain_le_A2_of_massSum` | Salt/Chen/MassLedger.lean:143 | sieves |
| `Salt.Chen.massE_le_crude` | Salt/Chen/MassLedger.lean:166 | sieves |
| `Salt.Chen.massO_nonneg` | Salt/Chen/MassLedgerA1.lean:60 | sieves |
| `Salt.Chen.fseq_even_eq_masses` | Salt/Chen/MassLedgerA1.lean:75 | sieves |
| `Salt.Chen.evenSum_le_of_massSums` | Salt/Chen/MassLedgerA1.lean:136 | sieves |
| `Salt.Chen.fchain_ge_A1_of_massSums` | Salt/Chen/MassLedgerA1.lean:249 | sieves |
| `Salt.Chen.massO_le_crude` | Salt/Chen/MassLedgerA1.lean:288 | sieves |
| `Salt.Chen.medium_support_floor_high` | Salt/Chen/MediumFloor.lean:176 | sieves |
| `Salt.Chen.medium_support_floor_low` | Salt/Chen/MediumFloor.lean:183 | sieves |
| `Salt.Chen.medium_support_floor_sym` | Salt/Chen/MediumFloor.lean:190 | sieves |
| `Salt.Chen.carrier_eq_zero_below_floor` | Salt/Chen/MediumFloor.lean:206 | sieves |
| `Salt.Chen.apDiscBilinCutoff_eq_of_under` | Salt/Chen/MediumFloor.lean:226 | sieves |
| `Salt.Chen.hdiv_direct` | Salt/Chen/MediumFloor.lean:271 | sieves |
| `Salt.Chen.dyadicBoundary_card_le_three` | Salt/Chen/MediumFloor.lean:344 | sieves |
| `Salt.Chen.box_disc_three_way` | Salt/Chen/MediumFloor.lean:394 | sieves |
| `Salt.Chen.medium_survivor_price` | Salt/Chen/MediumFloor.lean:507 | sieves |
| `Salt.Chen.hHD_of_box_disc` | Salt/Chen/MediumFloor.lean:578 | sieves |
| `Salt.Chen.Plo_sym_of_box_disc` | Salt/Chen/MediumFloor.lean:601 | sieves |
| `Salt.Chen.Plo_low_of_box_disc` | Salt/Chen/MediumFloor.lean:624 | sieves |
| `Salt.Chen.hNum_at_op` | Salt/Chen/MediumFloor.lean:659 | sieves |
| `Salt.Chen.sum_inv_prime_window_ge` | Salt/Chen/MertensPNT.lean:159 | sieves |
| `Salt.Chen.twinWindow_mass_eq` | Salt/Chen/MertensPNT.lean:248 | sieves |
| `Salt.Chen.lambda_mass_lower` | Salt/Chen/MertensPNT.lean:261 | sieves |
| `Salt.Chen.lambda_mass_upper` | Salt/Chen/MertensPNT.lean:310 | sieves |
| `Salt.Chen.middle_medium_box_price_at_y` | Salt/Chen/MiddleK.lean:138 | sieves |
| `Salt.Chen.middle_k_price` | Salt/Chen/MiddleK.lean:284 | sieves |
| `Salt.Chen.rough_divisor_crumb` | Salt/Chen/PDiag.lean:243 | sieves |
| `Salt.Chen.nuChen_sum_divisors_le` | Salt/Chen/PDiag.lean:299 | sieves |
| `Salt.Chen.diagAggW_le_honest` | Salt/Chen/PDiag.lean:344 | sieves |
| `Salt.Chen.PloW_honest` | Salt/Chen/PDiag.lean:592 | sieves |
| `Salt.Chen.hBVblocksW_discharge'` | Salt/Chen/PDiag.lean:682 | sieves |
| `Salt.Chen.geom_decay_pointwise` | Salt/Chen/PLCascade.lean:102 | sieves |
| `Salt.Chen.geom_tail_ratio` | Salt/Chen/PLCascade.lean:122 | sieves |
| `Salt.Chen.geom_tail_majorant` | Salt/Chen/PLCascade.lean:155 | sieves |
| `Salt.Chen.fseq_le_leftEndpoint` | Salt/Chen/PLCascade.lean:190 | sieves |
| `Salt.Chen.fseq_next_le_const` | Salt/Chen/PLCascade.lean:216 | sieves |
| `Salt.Chen.evenSum_reindex` | Salt/Chen/PLCascade.lean:237 | sieves |
| `Salt.Chen.fseq_evensum_tail_le` | Salt/Chen/PLCascade.lean:262 | sieves |
| `Salt.Chen.evenSum_le_head_add_geomtail` | Salt/Chen/PLCascade.lean:272 | sieves |
| `Salt.Chen.fseq_even_le_crude` | Salt/Chen/PLCascade.lean:295 | sieves |
| `Salt.Chen.fseq_evensum_tail_crude` | Salt/Chen/PLCascade.lean:306 | sieves |
| `Salt.Chen.fseq_two_le_const_demo` | Salt/Chen/PLCascade.lean:325 | sieves |
| `Salt.Chen.ratio_le_of_floor` | Salt/Chen/PackA.lean:83 | sieves |
| `Salt.Chen.boxPriceKerrY_worst_le` | Salt/Chen/PackA.lean:129 | sieves |
| `Salt.Chen.symPriceK_worst_le` | Salt/Chen/PackA.lean:241 | sieves |
| `Salt.Chen.lowPriceK_worst_le` | Salt/Chen/PackA.lean:321 | sieves |
| `Salt.Chen.hRCE_at_op` | Salt/Chen/PackA.lean:374 | sieves |
| `Salt.Chen.XW_pos_at_op` | Salt/Chen/PackB.lean:71 | sieves |
| `Salt.Chen.hWy_at_op` | Salt/Chen/PackB.lean:144 | sieves |
| `Salt.Chen.blockBox_pair_card` | Salt/Chen/PairBijection.lean:151 | sieves |
| `Salt.Chen.blockBox_apDiscBilin_eq` | Salt/Chen/PairBijection.lean:278 | sieves |
| `Salt.Chen.norm_blockBox_apDiscBilin_eq` | Salt/Chen/PairBijection.lean:313 | sieves |
| `Salt.Chen.W_sieveBelow` | Salt/Chen/Peeling.lean:143 | sieves |
| `Salt.Chen.isViolPrefix_peel_iff` | Salt/Chen/Peeling.lean:223 | sieves |
| `Salt.Chen.T_peel` | Salt/Chen/Peeling.lean:320 | sieves |
| `Salt.Chen.T_le_of_peel_step` | Salt/Chen/Peeling.lean:461 | sieves |
| `Salt.Chen.hlevel_upper_of_step` | Salt/Chen/Peeling.lean:504 | sieves |
| `Salt.Chen.hlevel_lower_of_step` | Salt/Chen/Peeling.lean:531 | sieves |
| `Salt.Chen.hmain_upper_of_step` | Salt/Chen/Peeling.lean:557 | sieves |
| `Salt.Chen.hmain_lower_of_step` | Salt/Chen/Peeling.lean:573 | sieves |
| `Salt.Chen.efold_density_fold` | Salt/Chen/PerEEngine.lean:85 | sieves |
| `Salt.Chen.hErrSum_final` | Salt/Chen/PerEEngine.lean:123 | sieves, characters |
| `Salt.Chen.hLargeDisc_of_perE` | Salt/Chen/PerEEngine.lean:160 | sieves, characters |
| `Salt.Chen.general_BV_final` | Salt/Chen/PerEEngine.lean:190 | sieves |
| `Salt.Chen.sum_inv_Icc_le_log` | Salt/Chen/PerEEngine2.lean:168 | sieves |
| `Salt.Chen.hErrSum_final'` | Salt/Chen/PerEEngine2.lean:204 | sieves, characters |
| `Salt.Chen.hLargeDisc_of_perE'` | Salt/Chen/PerEEngine2.lean:251 | sieves, characters |
| `Salt.Chen.general_BV_final'` | Salt/Chen/PerEEngine2.lean:281 | sieves |
| `Salt.Chen.hPerE_reduces_to_alpha` | Salt/Chen/PerEEngine2.lean:331 | sieves |
| `Salt.Chen.abs_blockHonestDisc_le_sum_pieces` | Salt/Chen/PieceDecomp.lean:214 | sieves |
| `Salt.Chen.card_pieces` | Salt/Chen/PieceDecomp.lean:225 | sieves |
| `Salt.Chen.hBlock_of_window_prices` | Salt/Chen/PieceDecomp.lean:383 | sieves |
| `Salt.Chen.box_carrier_eq_zero_above_cap` | Salt/Chen/PriceClose.lean:69 | sieves |
| `Salt.Chen.y_lt_two_pow_succ_of_carrier` | Salt/Chen/PriceClose.lean:97 | sieves |
| `Salt.Chen.hDsq_piece_of_kfloor` | Salt/Chen/PriceClose.lean:127 | sieves |
| `Salt.Chen.hDsmall_at_op` | Salt/Chen/PriceClose.lean:147 | sieves |
| `Salt.Chen.tower_budget` | Salt/Chen/PriceClose.lean:205 | sieves |
| `Salt.Chen.hNum_close_of_tower` | Salt/Chen/PriceClose.lean:219 | sieves |
| `Salt.Chen.bridge_scale` | Salt/Chen/PriceOne.lean:137 | sieves |
| `Salt.Chen.medium_box_price_at_op` | Salt/Chen/PriceOne.lean:492 | sieves |
| `Salt.Chen.crtClassW_coprime_of_mem` | Salt/Chen/PriceThree.lean:101 | sieves |
| `Salt.Chen.box_hprice_at_2pow` | Salt/Chen/PriceThree.lean:228 | sieves |
| `Salt.Chen.sym_box_hprice_at_2pow` | Salt/Chen/PriceThree.lean:313 | sieves |
| `Salt.Chen.low_box_hprice_at_2pow` | Salt/Chen/PriceThree.lean:393 | sieves |
| `Salt.Chen.d0_window_nonempty_lo` | Salt/Chen/PriceTwo.lean:86 | sieves |
| `Salt.Chen.medium_box_price_at_op_lo` | Salt/Chen/PriceTwo.lean:652 | sieves |
| `Salt.Chen.sym_box_price_at_op` | Salt/Chen/PriceTwo.lean:803 | sieves |
| `Salt.Chen.low_box_price_at_op` | Salt/Chen/PriceTwo.lean:840 | sieves |
| `Salt.Chen.razor_scalar_margin` | Salt/Chen/RazorClose.lean:94 | sieves |
| `Salt.Chen.razor_of_normalized` | Salt/Chen/RazorClose.lean:116 | sieves |
| `Salt.Chen.hledger_at_certs` | Salt/Chen/RazorClose.lean:156 | sieves |
| `Salt.Chen.fseq_one_window` | Salt/Chen/RosserChain.lean:81 | sieves |
| `Salt.Chen.fseq_eq_zero_of_ge` | Salt/Chen/RosserChain.lean:126 | sieves |
| `Salt.Chen.fseq_nonneg` | Salt/Chen/RosserChain.lean:162 | sieves |
| `Salt.Chen.fseq_two_window` | Salt/Chen/RosserChain.lean:208 | sieves |
| `Salt.Chen.fseq_intervalIntegrable` | Salt/Chen/RosserChain.lean:424 | sieves |
| `Salt.Chen.fseq_shift_intervalIntegrable` | Salt/Chen/RosserChain.lean:429 | sieves |
| `Salt.Chen.Fchain_add_fchain` | Salt/Chen/RosserChain.lean:452 | sieves |
| `Salt.Chen.Fchain_add_fchain_one_ne_two` | Salt/Chen/RosserChain.lean:461 | sieves |
| `Salt.Chen.stepHyp_sharpB_pointwise` | Salt/Chen/SharpClose.lean:52 | sieves |
| `Salt.Chen.stepHypWPC_sharpB` | Salt/Chen/SharpClose.lean:125 | sieves |
| `Salt.Chen.bjs_theorem6_sharpB_final_upper` | Salt/Chen/SharpClose.lean:138 | sieves |
| `Salt.Chen.bjs_theorem6_sharpB_final_lower` | Salt/Chen/SharpClose.lean:161 | sieves |
| `Salt.Chen.abel_pushforward` | Salt/Chen/SharpF.lean:73 | sieves |
| `Salt.Chen.hf_cell_ge2` | Salt/Chen/SharpF.lean:173 | sieves |
| `Salt.Chen.hBJS_flat_lb` | Salt/Chen/SharpF.lean:323 | sieves |
| `Salt.Chen.vlow_le_of_guard` | Salt/Chen/SharpF.lean:355 | sieves |
| `Salt.Chen.hf_sharp_flat` | Salt/Chen/SharpF.lean:451 | sieves |
| `Salt.Chen.hf_sharp_of_window` | Salt/Chen/SharpF.lean:718 | sieves |
| `Salt.Chen.tail_parts_bound` | Salt/Chen/SharpFuncbound.lean:99 | sieves |
| `Salt.Chen.hBJS_funcbound_sharp` | Salt/Chen/SharpFuncbound.lean:220 | sieves |
| `Salt.Chen.hBJS_shift_le` | Salt/Chen/SharpH.lean:83 | sieves |
| `Salt.Chen.upset_mass_le` | Salt/Chen/SharpH.lean:139 | sieves |
| `Salt.Chen.hh_antitone_majorize` | Salt/Chen/SharpH.lean:271 | sieves |
| `Salt.Chen.hh_sharp_ge2_of_pushforward` | Salt/Chen/SharpH.lean:294 | sieves |
| `Salt.Chen.layer_cake_pushforward` | Salt/Chen/SharpH2.lean:262 | sieves |
| `Salt.Chen.hpush_core` | Salt/Chen/SharpH2.lean:362 | sieves |
| `Salt.Chen.upset_mass_window_le` | Salt/Chen/SharpH2.lean:440 | sieves |
| `Salt.Chen.hh_sharp_flat` | Salt/Chen/SharpH2.lean:636 | sieves |
| `Salt.Chen.hh_sharp_ge2` | Salt/Chen/SharpH2.lean:780 | sieves |
| `Salt.Chen.hh_sharp_of_window` | Salt/Chen/SharpH2.lean:852 | sieves |
| `Salt.Chen.Vbelow_le_ratio` | Salt/Chen/SharpStep.lean:102 | sieves |
| `Salt.Chen.prime_support_mass_le` | Salt/Chen/SharpStep.lean:148 | sieves |
| `Salt.Chen.hf_of_window` | Salt/Chen/SharpStep.lean:359 | sieves |
| `Salt.Chen.hh_reduced` | Salt/Chen/SharpStep.lean:506 | sieves |
| `Salt.Chen.fseq_geom_uniform` | Salt/Chen/SharpTau.lean:97 | sieves |
| `Salt.Chen.ch_const_geom_ge` | Salt/Chen/SharpTau.lean:168 | sieves |
| `Salt.Chen.tauDecSum_odd_ge` | Salt/Chen/SharpTau.lean:241 | sieves |
| `Salt.Chen.two_sqrt_primes_not_both_dvd` | Salt/Chen/SqrtDFold.lean:106 | sieves |
| `Salt.Chen.efold_beta_le_single` | Salt/Chen/SqrtDFold.lean:323 | sieves, characters |
| `Salt.Chen.card_conductor_not_dvd_le` | Salt/Chen/SqrtDFold.lean:443 | sieves, characters |
| `Salt.Chen.general_BV_cutoff_sqrtD` | Salt/Chen/SqrtDFold.lean:818 | sieves |
| `Salt.Chen.medium_survivor_price_sqrtD` | Salt/Chen/SqrtDFold.lean:956 | sieves |
| `Salt.Chen.hNum_at_op_sqrtD` | Salt/Chen/SqrtDFold.lean:1089 | sieves |
| `Salt.Chen.d0_window_nonempty` | Salt/Chen/SqrtDFold.lean:1296 | sieves |
| `Salt.Chen.hBJS_funcbound` | Salt/Chen/StepBound.lean:187 | sieves |
| `Salt.Chen.tauSum_odd_le` | Salt/Chen/StepBound.lean:239 | sieves |
| `Salt.Chen.tauSum_even_le` | Salt/Chen/StepBound.lean:248 | sieves |
| `Salt.Chen.hbase_of` | Salt/Chen/StepBound.lean:266 | sieves |
| `Salt.Chen.bjs_theorem6_upper` | Salt/Chen/StepBound.lean:312 | sieves |
| `Salt.Chen.bjs_theorem6_lower` | Salt/Chen/StepBound.lean:331 | sieves |
| `Salt.Chen.bjs_theorem6_upper_sifted` | Salt/Chen/StepBound.lean:350 | sieves |
| `Salt.Chen.bjs_theorem6_lower_sifted` | Salt/Chen/StepBound.lean:371 | sieves |
| `Salt.Chen.T_le_of_peel_step'` | Salt/Chen/StepBound2.lean:92 | sieves |
| `Salt.Chen.hbase'_of` | Salt/Chen/StepBound2.lean:168 | sieves |
| `Salt.Chen.apDiscBilinCutoff_sum_alpha` | Salt/Chen/SubBlocked.lean:153 | sieves |
| `Salt.Chen.apDiscBilinCutoff_eq_zero_of_over` | Salt/Chen/SubBlocked.lean:216 | sieves |
| `Salt.Chen.subblocked_box_price` | Salt/Chen/SubBlocked.lean:341 | sieves |
| `Salt.Chen.massSum_le_A2_final` | Salt/Chen/SuperClose.lean:42 | sieves |
| `Salt.Chen.massOSum_le_A1_final` | Salt/Chen/SuperClose.lean:48 | sieves |
| `Salt.Chen.Fchain_A2_final` | Salt/Chen/SuperClose.lean:55 | sieves |
| `Salt.Chen.fchain_A1_final` | Salt/Chen/SuperClose.lean:61 | sieves |
| `Salt.Chen.hSE_holds` | Salt/Chen/SuperPanelsE.lean:7914 | sieves |
| `Salt.Chen.hSO_holds` | Salt/Chen/SuperPanelsO.lean:3418 | sieves |
| `Salt.Chen.budE_le` | Salt/Chen/SuperProfile.lean:92 | sieves |
| `Salt.Chen.budO_le` | Salt/Chen/SuperProfile.lean:96 | sieves |
| `Salt.Chen.hSE_reduce` | Salt/Chen/SuperProfile.lean:106 | sieves |
| `Salt.Chen.hSO_reduce` | Salt/Chen/SuperProfile.lean:118 | sieves |
| `Salt.Chen.fseq2_upper_of_log_lower` | Salt/Chen/SuperProfile.lean:138 | sieves |
| `Salt.Chen.tail_integral_le` | Salt/Chen/SuperProfile.lean:154 | sieves |
| `Salt.Chen.Ebar_panel_eq` | Salt/Chen/SuperProfileDef.lean:123 | sieves |
| `Salt.Chen.Ebar_nonneg` | Salt/Chen/SuperProfileDef.lean:141 | sieves |
| `Salt.Chen.Ebar_intervalIntegrable` | Salt/Chen/SuperProfileDef.lean:210 | sieves |
| `Salt.Chen.Ebar_integral_le` | Salt/Chen/SuperProfileDef.lean:273 | sieves |
| `Salt.Chen.Obar_panel_eq` | Salt/Chen/SuperProfileDef.lean:356 | sieves |
| `Salt.Chen.Obar_nonneg` | Salt/Chen/SuperProfileDef.lean:374 | sieves |
| `Salt.Chen.Obar_intervalIntegrable` | Salt/Chen/SuperProfileDef.lean:443 | sieves |
| `Salt.Chen.Obar_integral_le` | Salt/Chen/SuperProfileDef.lean:532 | sieves |
| `Salt.Chen.even_step` | Salt/Chen/SuperSolution.lean:189 | sieves |
| `Salt.Chen.Xe_recursion` | Salt/Chen/SuperSolution.lean:229 | sieves |
| `Salt.Chen.odd_step` | Salt/Chen/SuperSolution.lean:247 | sieves |
| `Salt.Chen.superSol_dominates` | Salt/Chen/SuperSolution.lean:298 | sieves |
| `Salt.Chen.massE_sum_eq` | Salt/Chen/SuperSolution.lean:374 | sieves |
| `Salt.Chen.massO_sum_eq` | Salt/Chen/SuperSolution.lean:405 | sieves |
| `Salt.Chen.massSum_le_A2_of_superSolution` | Salt/Chen/SuperSolution.lean:444 | sieves |
| `Salt.Chen.massOSum_le_A1_of_superSolution` | Salt/Chen/SuperSolution.lean:474 | sieves |
| `Salt.Chen.switch_dvd_coprime_two` | Salt/Chen/SwitchBV.lean:88 | sieves |
| `Salt.Chen.switchSieve_multSum_eq_apCount` | Salt/Chen/SwitchBV.lean:155 | sieves |
| `Salt.Chen.norm_semiprimeBlockInd_le_one` | Salt/Chen/SwitchBV.lean:210 | sieves |
| `Salt.Chen.switchSieve_rem_split` | Salt/Chen/SwitchBV.lean:263 | sieves |
| `Salt.Chen.switchSieve_abs_rem_le` | Salt/Chen/SwitchBV.lean:280 | sieves |
| `Salt.Chen.switchSieve_rosserRemainder_split_le` | Salt/Chen/SwitchBV.lean:316 | sieves |
| `Salt.Chen.hBVswitch_of_generalBV` | Salt/Chen/SwitchBV.lean:344 | sieves |
| `Salt.Chen.block_switch_upper_B` | Salt/Chen/SwitchBlocks.lean:278 | sieves |
| `Salt.Chen.triplePrimeSum_le_sum_blocks` | Salt/Chen/SwitchBlocks.lean:338 | sieves |
| `Salt.Chen.norm_blockAlpha_le_one` | Salt/Chen/SwitchBlocks.lean:369 | sieves |
| `Salt.Chen.mainA3_of_block_remainders` | Salt/Chen/SwitchBlocks.lean:387 | sieves |
| `Salt.Chen.cbar_pos` | Salt/Chen/SwitchConstant.lean:93 | sieves |
| `Salt.Chen.two_log_three_sub_log_six_sub_cbar_pos` | Salt/Chen/SwitchConstant.lean:111 | sieves |
| `Salt.Chen.abs_switchHonestDisc_le_sum_relevant` | Salt/Chen/SwitchDyadic.lean:266 | sieves |
| `Salt.Chen.hHD_of_generalBV_inputs` | Salt/Chen/SwitchDyadic.lean:291 | sieves |
| `Salt.Chen.abs_boxHonestDisc_le_boxCount` | Salt/Chen/SwitchPricing.lean:137 | sieves |
| `Salt.Chen.card_relevantBoxes_le` | Salt/Chen/SwitchPricing.lean:160 | sieves |
| `Salt.Chen.hHD_of_uniform_price` | Salt/Chen/SwitchPricing.lean:221 | sieves |
| `Salt.Chen.norm_boxAlpha_le_one` | Salt/Chen/SwitchPricing.lean:249 | sieves |
| `Salt.Chen.box_price_of_apDiscBilin` | Salt/Chen/SwitchPricing.lean:270 | sieves |
| `Salt.Chen.switch_hnu` | Salt/Chen/SwitchSieve.lean:156 | sieves |
| `Salt.Chen.switch_hguard` | Salt/Chen/SwitchSieve.lean:162 | sieves |
| `Salt.Chen.switch_upper_B` | Salt/Chen/SwitchSieve.lean:182 | sieves |
| `Salt.Chen.triplePrimeSum_le_sifted` | Salt/Chen/SwitchSieve.lean:228 | sieves |
| `Salt.Chen.mainA3_of_hBVswitch` | Salt/Chen/SwitchSieve.lean:297 | sieves |
| `Salt.Chen.apDiscBilin_sum_alpha` | Salt/Chen/SwitchStrip.lean:151 | sieves |
| `Salt.Chen.norm_restrictAlpha_le_one` | Salt/Chen/SwitchStrip.lean:181 | sieves |
| `Salt.Chen.apDiscBilin_split_threshold` | Salt/Chen/SwitchStrip.lean:189 | sieves |
| `Salt.Chen.apDiscBilin_singleton_collapse` | Salt/Chen/SwitchStrip.lean:208 | sieves |
| `Salt.Chen.productInWindow_of_corners` | Salt/Chen/SwitchStrip.lean:247 | sieves |
| `Salt.Chen.triplePrimeSumW_le_sifted` | Salt/Chen/SwitchW.lean:213 | sieves |
| `Salt.Chen.switchSieveW_siftedSum_eq_sum_blocks` | Salt/Chen/SwitchW.lean:271 | sieves |
| `Salt.Chen.block_switch_upper_B_W` | Salt/Chen/SwitchW.lean:295 | sieves |
| `Salt.Chen.mainA3_of_block_remainders_W` | Salt/Chen/SwitchW.lean:340 | sieves |
| `Salt.Chen.crtClassW_coprime` | Salt/Chen/SwitchW.lean:435 | sieves |
| `Salt.Chen.memClassW_iff` | Salt/Chen/SwitchW.lean:457 | sieves |
| `Salt.Chen.blockUnitM_add_blockNonUnitM` | Salt/Chen/SwitchW.lean:495 | sieves |
| `Salt.Chen.blockMultSumW_eq_apCount` | Salt/Chen/SwitchW.lean:520 | sieves |
| `Salt.Chen.blockSwitchSieveW_rem_split` | Salt/Chen/SwitchW.lean:610 | sieves |
| `Salt.Chen.blockSwitchSieveW_abs_rem_le` | Salt/Chen/SwitchW.lean:626 | sieves |
| `Salt.Chen.blockRemW_rosserRemainder_split_le` | Salt/Chen/SwitchW.lean:645 | sieves |
| `Salt.Chen.sum_blockRemW_split_le` | Salt/Chen/SwitchW.lean:663 | sieves |
| `Salt.Chen.hBVblocksW_of_generalBV` | Salt/Chen/SwitchW.lean:684 | sieves |
| `Salt.Chen.hBlockW_of_window_prices` | Salt/Chen/SwitchW2.lean:332 | sieves |
| `Salt.Chen.blockBoxW_windowDisc_eq` | Salt/Chen/SwitchW2.lean:406 | sieves |
| `Salt.Chen.hNum_at_opW` | Salt/Chen/SwitchW2.lean:455 | sieves |
| `Salt.Chen.bandDiscW_le_three_pieces` | Salt/Chen/SwitchW2.lean:597 | sieves |
| `Salt.Chen.PloW_discharge` | Salt/Chen/SwitchW2.lean:623 | sieves |
| `Salt.Chen.hrW_discharge` | Salt/Chen/SwitchW2.lean:846 | sieves |
| `Salt.Chen.hBVblocksW_discharge` | Salt/Chen/SwitchW2.lean:894 | sieves |
| `Salt.Chen.fseq_le` | Salt/Chen/Tail.lean:320 | sieves |
| `Salt.Chen.fseq_tail_sum_le` | Salt/Chen/Tail.lean:416 | sieves |
| `Salt.Chen.fseq_tail_le` | Salt/Chen/Tail.lean:463 | sieves |
| `Salt.Chen.fchain_close` | Salt/Chen/Tail.lean:493 | sieves |
| `Salt.Chen.Fchain_close` | Salt/Chen/Tail.lean:517 | sieves |
| `Salt.Chen.tauChen_rec` | Salt/Chen/TauNumeric.lean:134 | sieves |
| `Salt.Chen.hτrec_zero_impossible` | Salt/Chen/TauNumeric.lean:189 | sieves |
| `Salt.Chen.tauSum_odd_ge` | Salt/Chen/TauNumeric.lean:275 | sieves |
| `Salt.Chen.chSharp_lt_one` | Salt/Chen/TauSharp.lean:146 | sieves |
| `Salt.Chen.sharp_h_contract` | Salt/Chen/TauSharp.lean:156 | sieves |
| `Salt.Chen.chSharp_h_contract` | Salt/Chen/TauSharp.lean:170 | sieves |
| `Salt.Chen.tauSharp_nonneg` | Salt/Chen/TauSharp.lean:195 | sieves |
| `Salt.Chen.tauSharp_hτrec` | Salt/Chen/TauSharp.lean:207 | sieves |
| `Salt.Chen.tauSharp_sum_le` | Salt/Chen/TauSharp.lean:225 | sieves |
| `Salt.Chen.tauSharp_sum_odd_le` | Salt/Chen/TauSharp.lean:235 | sieves |
| `Salt.Chen.tauSharp_sum_even_le` | Salt/Chen/TauSharp.lean:241 | sieves |
| `Salt.Chen.Csharp_frozen` | Salt/Chen/TauSharp.lean:249 | sieves |
| `Salt.Chen.stepHyp_sharp_of_comparisons` | Salt/Chen/TauSharp.lean:261 | sieves |
| `Salt.Chen.bjs_theorem6_sharp_upper` | Salt/Chen/TauSharp.lean:282 | sieves |
| `Salt.Chen.bjs_theorem6_sharp_lower` | Salt/Chen/TauSharp.lean:310 | sieves |
| `Salt.Chen.op_floors` | Salt/Chen/TheHeadline.lean:55 | sieves |
| `Salt.Chen.buchstab_defect` | Salt/Chen/TnInduction.lean:584 | sieves |
| `Salt.Chen.T_nonneg` | Salt/Chen/TnInduction.lean:636 | sieves |
| `Salt.Chen.buchstab_upper` | Salt/Chen/TnInduction.lean:658 | sieves |
| `Salt.Chen.buchstab_lower` | Salt/Chen/TnInduction.lean:684 | sieves |
| `Salt.Chen.hmain_upper` | Salt/Chen/TnInduction.lean:723 | sieves |
| `Salt.Chen.hmain_lower` | Salt/Chen/TnInduction.lean:740 | sieves |
| `Salt.Chen.linear_sieve_upper_rosser_assembled` | Salt/Chen/TnInduction.lean:756 | sieves |
| `Salt.Chen.linear_sieve_lower_rosser_assembled` | Salt/Chen/TnInduction.lean:770 | sieves |
| `Salt.Chen.hbar_le_hBJS` | Salt/Chen/TnInduction.lean:794 | sieves |
| `Salt.Chen.prod_ratio_le_card_succ` | Salt/Chen/TotientHelpers.lean:34 | sieves |
| `Salt.Chen.totient_ratio_le_log` | Salt/Chen/TotientHelpers.lean:69 | sieves |
| `Salt.Chen.totient_lcm_mul_totient_gcd` | Salt/Chen/TotientHelpers.lean:146 | sieves |
| `Salt.Chen.card_divisors_le_two_sqrt` | Salt/Chen/TotientHelpers.lean:173 | sieves |
| `Salt.Chen.apDiscBilinCutoff_transpose` | Salt/Chen/TransposedBV.lean:156 | sieves |
| `Salt.Chen.medium_smallconductor_prime_side` | Salt/Chen/TransposedBV.lean:202 | sieves |
| `Salt.Chen.medium_band_price` | Salt/Chen/TransposedBV.lean:239 | sieves |
| `Salt.Chen.subblocked_box_price_reduced` | Salt/Chen/TransposedBV.lean:258 | sieves |
| `Salt.Chen.prime_count_Ioc_le` | Salt/Chen/TripleCount.lean:118 | sieves |
| `Salt.Chen.chen_switch_const_lt` | Salt/Chen/TripleCount.lean:146 | sieves |
| `Salt.Chen.triple_count_le` | Salt/Chen/TripleCount.lean:505 | sieves |
| `Salt.Chen.twinA1_hnu` | Salt/Chen/TwinA1.lean:186 | sieves |
| `Salt.Chen.twinA1_hguard` | Salt/Chen/TwinA1.lean:193 | sieves |
| `Salt.Chen.twinA1_rem_eq` | Salt/Chen/TwinA1.lean:320 | sieves |
| `Salt.Chen.twinA1_abs_rem_le` | Salt/Chen/TwinA1.lean:336 | sieves |
| `Salt.Chen.twin_A1_lower` | Salt/Chen/TwinA1.lean:372 | sieves |
| `Salt.Chen.crt_class_coprime` | Salt/Chen/TwinA1W.lean:208 | sieves |
| `Salt.Chen.twinA1W_rem_eq` | Salt/Chen/TwinA1W.lean:292 | sieves |
| `Salt.Chen.twinA1_hBV_W` | Salt/Chen/TwinA1W.lean:620 | sieves |
| `Salt.Chen.A1primeSumW_bridge` | Salt/Chen/TwinA1W.lean:792 | sieves |
| `Salt.Chen.twin_A2_per_prime` | Salt/Chen/TwinA2.lean:97 | sieves |
| `Salt.Chen.A2grid_le_envelope` | Salt/Chen/TwinA2.lean:146 | sieves |
| `Salt.Chen.twin_A2_upper` | Salt/Chen/TwinA2.lean:218 | sieves |
| `Salt.Chen.twinA2W_rem_eq` | Salt/Chen/TwinA2W.lean:218 | sieves |
| `Salt.Chen.twinA2W_hcoef` | Salt/Chen/TwinA2W.lean:403 | sieves |
| `Salt.Chen.twinA2_hBVagg_W` | Salt/Chen/TwinA2W.lean:700 | sieves |
| `Salt.Chen.p2PrimeSum_split` | Salt/Chen/TwinDeficit.lean:175 | sieves |
| `Salt.Chen.heavy_semiprime_obstruction` | Salt/Chen/TwinDeficit.lean:234 | sieves |
| `Salt.Chen.p1_razor_reduction` | Salt/Chen/TwinDeficit.lean:280 | sieves |
| `Salt.Chen.p1RazorValue_eq` | Salt/Chen/TwinDeficit.lean:293 | sieves |
| `Salt.Chen.e2_carrier_inhabited` | Salt/Chen/TwinDeficit.lean:309 | sieves |
| `Salt.Chen.p1_carrier_inhabited` | Salt/Chen/TwinDeficit.lean:331 | sieves |
| `Salt.Chen.twin_razor_deficit` | Salt/Chen/TwinDeficit.lean:369 | sieves |
| `Salt.Chen.twin_razor_deficit'` | Salt/Chen/TwinDeficit.lean:385 | sieves |
| `Salt.Chen.deficit_quant_ledger` | Salt/Chen/TwinDeficit.lean:405 | sieves |
| `Salt.Chen.p2RazorLHS_ge_of_certs` | Salt/Chen/TwinDeficit.lean:431 | sieves |
| `Salt.Chen.e2_lower_of_certs_twinup` | Salt/Chen/TwinDeficit.lean:455 | sieves |
| `Salt.Chen.deficit_floor_of_certs` | Salt/Chen/TwinDeficit.lean:480 | sieves |
| `Salt.Chen.p2PrimeSumW_split` | Salt/Chen/TwinDeficit.lean:527 | sieves |
| `Salt.Chen.p1_razor_reduction_W` | Salt/Chen/TwinDeficit.lean:556 | sieves |
| `Salt.Chen.twin_razor_deficit_W` | Salt/Chen/TwinDeficit.lean:569 | sieves |
| `Salt.Chen.e2W_carrier_inhabited` | Salt/Chen/TwinDeficit.lean:598 | sieves |
| `Salt.Chen.fseq_next_le_of_shift_majorant` | Salt/Chen/ValueCascade.lean:80 | sieves |
| `Salt.Chen.integral_M3` | Salt/Chen/ValueCascade.lean:101 | sieves |
| `Salt.Chen.fseq2_shift_le_M3` | Salt/Chen/ValueCascade.lean:139 | sieves |
| `Salt.Chen.M3_intble` | Salt/Chen/ValueCascade.lean:146 | sieves |
| `Salt.Chen.fseq_three_tail_le` | Salt/Chen/ValueCascade.lean:170 | sieves |
| `Salt.Chen.fseq_three_flat_le` | Salt/Chen/ValueCascade.lean:191 | sieves |
| `Salt.Chen.W_twinA1_ge` | Salt/Chen/WLower.lean:51 | sieves |
| `Salt.Chen.window_prod_lower` | Salt/Chen/WRatioSharp.lean:200 | sieves |
| `Salt.Chen.window_prod_upper` | Salt/Chen/WRatioSharp.lean:238 | sieves |
| `Salt.Chen.W_switch_factor` | Salt/Chen/WRatioSharp.lean:293 | sieves |
| `Salt.Chen.W_ratio_upper` | Salt/Chen/WRatioSharp.lean:315 | sieves |
| `Salt.Chen.W_ratio_lower` | Salt/Chen/WRatioSharp.lean:329 | sieves |
| `Salt.Chen.omegaLe_eq_zero_of_prime_gt` | Salt/Chen/WeightEscape.lean:59 | sieves |
| `Salt.Chen.sqStrip_eq_zero_of_prime_gt` | Salt/Chen/WeightEscape.lean:68 | sieves |
| `Salt.Chen.not_tripleP_of_prime` | Salt/Chen/WeightEscape.lean:77 | sieves |
| `Salt.Chen.readableWeight_heavy` | Salt/Chen/WeightEscape.lean:95 | sieves |
| `Salt.Chen.readableWeight_window_prime` | Salt/Chen/WeightEscape.lean:105 | sieves |
| `Salt.Chen.readableWeight_blind` | Salt/Chen/WeightEscape.lean:117 | sieves |
| `Salt.Chen.bigOmegaGt_prime` | Salt/Chen/WeightEscape.lean:145 | sieves |
| `Salt.Chen.bigOmegaGt_heavy` | Salt/Chen/WeightEscape.lean:160 | sieves |
| `Salt.Chen.chenWeightA_le_indicator_of_sifted` | Salt/Chen/WeightFamily.lean:115 | sieves |
| `Salt.Chen.admissible_worst_case` | Salt/Chen/WeightFamily.lean:135 | sieves |
| `Salt.Chen.admissible_necessary` | Salt/Chen/WeightFamily.lean:191 | sieves |
| `Salt.Chen.marginFn_half_ge` | Salt/Chen/WeightFamily.lean:211 | sieves |
| `Salt.Chen.marginFn_antitone` | Salt/Chen/WeightFamily.lean:233 | sieves |
| `Salt.Chen.alpha_half_optimal` | Salt/Chen/WeightFamily.lean:247 | sieves |
| `Salt.Chen.alpha_half_strict` | Salt/Chen/WeightFamily.lean:251 | sieves |
| `Salt.Chen.chenWeightA_eq_one_of_heavy` | Salt/Chen/WeightFamily.lean:266 | sieves |
| `Salt.Chen.retune_invisible_at_heavy` | Salt/Chen/WeightFamily.lean:281 | sieves |
| `Salt.Chen.p2PrimeSum_le_A1primeSum` | Salt/Chen/WeightNoGo.lean:106 | sieves |
| `Salt.Chen.corpus_feasible` | Salt/Chen/WeightNoGo.lean:126 | sieves |
| `Salt.Chen.affine_carrier_identity` | Salt/Chen/WeightNoGo.lean:163 | sieves |
| `Salt.Chen.window_two_thirds_lt` | Salt/Chen/WeightTrivia.lean:93 | sieves |
| `Salt.Chen.switch_loss_le` | Salt/Chen/WeightTrivia.lean:119 | sieves |
| `Salt.Chen.stripSum_le` | Salt/Chen/WeightTrivia.lean:188 | sieves |
| `Salt.Chen.chen_weight_le_indicator` | Salt/Chen/WeightTrivia.lean:373 | sieves |
| `Salt.Chen.per_pair_weighted_le` | Salt/Chen/WeightedCount.lean:121 | sieves |
| `Salt.Chen.tripleSum_le_weighted_pairSum` | Salt/Chen/WeightedCount.lean:325 | sieves |
| `Salt.Chen.cbar_inner_integral` | Salt/Chen/WeightedCount.lean:377 | sieves |
| `Salt.Chen.cbar_eq_double_integral` | Salt/Chen/WeightedCount.lean:441 | sieves |
| `Salt.Chen.apDiscBilinCutoff_orthogonality` | Salt/Chen/WindowBV.lean:106 | sieves, characters |
| `Salt.Chen.norm_apDiscBilinCutoff_le` | Salt/Chen/WindowBV.lean:184 | sieves, characters |
| `Salt.Chen.cutoffTwist_energy_le` | Salt/Chen/WindowBV.lean:218 | sieves, characters |
| `Salt.Chen.energy_shell_cutoff` | Salt/Chen/WindowBV.lean:270 | sieves |
| `Salt.Chen.block_energy_le_cutoff` | Salt/Chen/WindowBVDescent.lean:86 | sieves |
| `Salt.Chen.dyadic_large_reduction_cutoff` | Salt/Chen/WindowBVDescent.lean:127 | sieves |
| `Salt.Chen.dyadic_energy_le_cutoff` | Salt/Chen/WindowBVDescent.lean:208 | sieves |
| `Salt.Chen.dyadic_energy_le_cutoff_dvd` | Salt/Chen/WindowBVDescent.lean:378 | sieves |
| `Salt.Chen.cutoffTwist_coprimeRestrict_primitive` | Salt/Chen/WindowClose.lean:85 | sieves, characters |
| `Salt.Chen.regroup_cutoff` | Salt/Chen/WindowClose.lean:112 | sieves, characters |
| `Salt.Chen.cutoff_hLargeDisc` | Salt/Chen/WindowClose.lean:183 | sieves, characters |
| `Salt.Chen.general_BV_cutoff_final` | Salt/Chen/WindowClose.lean:283 | sieves, characters |
| `Salt.Chen.hHD_of_generalBV_window` | Salt/Chen/WindowClose.lean:386 | sieves |
| `Salt.Chen.hMainEnergy_cutoff_discharge` | Salt/Chen/WindowErrFold.lean:76 | sieves |
| `Salt.Chen.cutoffEfoldTerm_eq_zero_of_gt` | Salt/Chen/WindowErrFold.lean:328 | sieves |
| `Salt.Chen.cutoffEfoldTerm_reorg` | Salt/Chen/WindowErrFold.lean:346 | sieves, characters |
| `Salt.Chen.cutoffEfold_alpha_le` | Salt/Chen/WindowErrFold.lean:1129 | sieves |
| `Salt.Chen.hErrSum_cutoff_of_thresholds` | Salt/Chen/WindowErrFold.lean:1218 | sieves, characters |
| `Salt.Chen.general_BV_cutoff_closed` | Salt/Chen/WindowErrFold.lean:1278 | sieves |
| `Salt.Chen.logRatio_A1_mem` | Salt/Chen/WindowMembership.lean:113 | sieves |
| `Salt.Chen.logRatio_A3_mem` | Salt/Chen/WindowMembership.lean:135 | sieves |
| `Salt.Chen.smallconductor_window_perd` | Salt/Chen/WindowSW.lean:104 | sieves |
| `Salt.Chen.smallconductor_window_sum` | Salt/Chen/WindowSW.lean:302 | sieves |
| `Salt.Chen.blockBox_windowed_pair_card` | Salt/Chen/WindowSW.lean:453 | sieves |
| `Salt.Chen.blockBox_windowDisc_eq_res` | Salt/Chen/WindowSW.lean:565 | sieves |
| `Salt.Chen.blockBox_windowDisc_eq` | Salt/Chen/WindowSW.lean:682 | sieves |
| `Salt.Chen.cutoffTwist_le_sum_interval_twists` | Salt/Chen/WindowSmallChi.lean:57 | sieves, characters |
| `Salt.Chen.interval_prime_twist_SW` | Salt/Chen/WindowSmallChi.lean:105 | sieves, characters |
| `Salt.Chen.hSmallCut_discharge` | Salt/Chen/WindowSmallChi.lean:171 | sieves |
| `Salt.Chen.hsmall_pere_discharge` | Salt/Chen/WindowSmallChi.lean:297 | sieves |
| `Salt.Chen.general_BV_cutoff_unconditional` | Salt/Chen/WindowSmallChi.lean:458 | sieves |
| `Salt.Chen.windowed_bilinear_BV_sqrtD` | Salt/Chen/WindowedBVStatement.lean:110 | sieves |
| `Salt.Chen.windowed_bilinear_BV_below_N` | Salt/Chen/WindowedBVStatement.lean:163 | sieves |
| `Salt.Chen.T_vanish` | Salt/Chen/WindowedStep.lean:96 | sieves |
| `Salt.Chen.stepHypW_holds` | Salt/Chen/WindowedStep.lean:244 | sieves |
| `Salt.Chen.bjs_theorem6_windowed_upper` | Salt/Chen/WindowedStep.lean:402 | sieves |
| `Salt.Chen.bjs_theorem6_windowed_lower` | Salt/Chen/WindowedStep.lean:427 | sieves |
| `Salt.Chen.stepHypWPC_const` | Salt/Chen/WindowedStepC.lean:79 | sieves |
| `Salt.Chen.chSharpB_lt_one` | Salt/Chen/WindowedStepC.lean:331 | sieves |
| `Salt.Chen.tauSharpB_hτrec` | Salt/Chen/WindowedStepC.lean:371 | sieves |
| `Salt.Chen.tauSharpB_sum_le` | Salt/Chen/WindowedStepC.lean:388 | sieves |
| `Salt.Chen.tauSharpB_sum_odd_le` | Salt/Chen/WindowedStepC.lean:403 | sieves |
| `Salt.Chen.tauSharpB_sum_even_le` | Salt/Chen/WindowedStepC.lean:409 | sieves |
| `Salt.Chen.CsharpB_frozen` | Salt/Chen/WindowedStepC.lean:416 | sieves |
| `Salt.Chen.stepHypWP_const` | Salt/Chen/WindowedStepP.lean:78 | sieves |
| `Salt.Chen.bjs_theorem6_windowed_upper_via_p` | Salt/Chen/WindowedStepP.lean:293 | sieves |
| `Salt.Chen.bjs_theorem6_windowed_lower_via_p` | Salt/Chen/WindowedStepP.lean:319 | sieves |
| `ProbabilityTheory.entropy_le_log_card` | Salt/Entropy/Basic.lean:116 | entropy |
| `Salt.Entropy.Chowla.liouville_shift_two_eq_neg_one_iff` | Salt/Entropy/Chowla/AffineFork.lean:198 | characters, entropy |
| `Salt.Entropy.Chowla.coprime_twinProd_of_affine` | Salt/Entropy/Chowla/AffineFork.lean:225 | entropy |
| `Salt.Entropy.Chowla.exists_admissible_class` | Salt/Entropy/Chowla/AffineFork.lean:242 | entropy |
| `Salt.Entropy.Chowla.rough_of_coprime_primorial` | Salt/Entropy/Chowla/AffineFork.lean:260 | entropy |
| `Salt.Entropy.Chowla.flatDesignBase_unbounded` | Salt/Entropy/Chowla/AffineFork.lean:278 | entropy |
| `Salt.Entropy.Chowla.dilation_forces_log` | Salt/Entropy/Chowla/BoundaryMap.lean:51 | entropy |
| `Salt.Entropy.Chowla.approx_covariance_not_unique` | Salt/Entropy/Chowla/BoundaryMap.lean:71 | entropy |
| `Salt.Entropy.Chowla.completelyMult_pm_one_collapse` | Salt/Entropy/Chowla/BoundaryMap.lean:103 | entropy |
| `Salt.Entropy.Chowla.collapse_forces_completelyMult` | Salt/Entropy/Chowla/BoundaryMap.lean:168 | entropy |
| `Salt.Entropy.Chowla.collapse_iff_completelyMult` | Salt/Entropy/Chowla/BoundaryMap.lean:214 | entropy |
| `Salt.Entropy.Chowla.liouville_mul` | Salt/Entropy/Chowla/ChowlaFailure.lean:67 | characters, entropy |
| `Salt.Entropy.Chowla.liouville_prime` | Salt/Entropy/Chowla/ChowlaFailure.lean:73 | characters, entropy |
| `Salt.Entropy.Chowla.singleCorr_of_fails_h` | Salt/Entropy/Chowla/ChowlaFailure.lean:197 | characters, entropy |
| `Salt.Entropy.Chowla.h211_of_logChowla2Fails_h` | Salt/Entropy/Chowla/ChowlaFailure.lean:254 | characters, entropy |
| `Salt.Entropy.Chowla.dft_is_fourier_coeff` | Salt/Entropy/Chowla/CircleMethod.lean:51 | entropy, exponential sums |
| `Salt.Entropy.Chowla.dft_parseval` | Salt/Entropy/Chowla/CircleMethod.lean:126 | entropy |
| `Salt.Entropy.Chowla.dft_l1_bound` | Salt/Entropy/Chowla/CircleMethod.lean:155 | entropy |
| `Salt.Entropy.Chowla.circle_method_estimate` | Salt/Entropy/Chowla/CircleMethod.lean:574 | entropy |
| `Salt.Entropy.Chowla.fourier_split_h` | Salt/Entropy/Chowla/CircleMethod.lean:1043 | entropy, exponential sums |
| `Salt.Entropy.Chowla.fourier_split_sq_h` | Salt/Entropy/Chowla/CircleMethod.lean:1133 | entropy, exponential sums |
| `Salt.Entropy.Chowla.circle_method_estimate_h_core` | Salt/Entropy/Chowla/CircleMethod.lean:1214 | entropy |
| `Salt.Entropy.Chowla.circle_method_estimate_sq_h_core` | Salt/Entropy/Chowla/CircleMethod.lean:1366 | entropy |
| `Salt.Entropy.Chowla.iIndepFun_residueProj` | Salt/Entropy/Chowla/Concentration.lean:102 | entropy |
| `Salt.Entropy.Chowla.hoeffding_residueProj` | Salt/Entropy/Chowla/Concentration.lean:218 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_mean` | Salt/Entropy/Chowla/Decoupled.lean:38 | entropy |
| `Salt.Entropy.Chowla.fBridge_concentration_decoupled` | Salt/Entropy/Chowla/Decoupled.lean:53 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_h_mean` | Salt/Entropy/Chowla/Decoupled.lean:84 | entropy |
| `Salt.Entropy.Chowla.fBridge_h_concentration_decoupled` | Salt/Entropy/Chowla/Decoupled.lean:101 | entropy |
| `Salt.Entropy.Chowla.entropy_decrement` | Salt/Entropy/Chowla/Decrement.lean:49 | characters, entropy |
| `Salt.Entropy.Chowla.dilation_error` | Salt/Entropy/Chowla/Dilation.lean:108 | entropy |
| `Salt.Entropy.Chowla.perPair_collapse` | Salt/Entropy/Chowla/DilationStability.lean:70 | entropy |
| `Salt.Entropy.Chowla.dilated_window_stability` | Salt/Entropy/Chowla/DilationStability.lean:178 | entropy |
| `Salt.Entropy.Chowla.not_summable_one_div_nat_loglog` | Salt/Entropy/Chowla/Diverge.lean:230 | entropy |
| `Salt.Entropy.Chowla.dropSum_exceeds_log_two` | Salt/Entropy/Chowla/Diverge.lean:397 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists` | Salt/Entropy/Chowla/Diverge.lean:449 | entropy |
| `Salt.Entropy.Chowla.entropy_per_symbol_le` | Salt/Entropy/Chowla/Endpoints.lean:41 | characters, entropy |
| `Salt.Entropy.Chowla.decrement_exists_of_tower` | Salt/Entropy/Chowla/Endpoints.lean:98 | characters, entropy |
| `Salt.Entropy.Chowla.fBridge_concentration` | Salt/Entropy/Chowla/FBridge.lean:298 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_mean` | Salt/Entropy/Chowla/FBridge.lean:353 | entropy |
| `Salt.Entropy.Chowla.fBridge_concentration_sharp` | Salt/Entropy/Chowla/FBridge.lean:434 | entropy |
| `Salt.Entropy.Chowla.fBridge_concentration_decoupled_sharp` | Salt/Entropy/Chowla/FBridge.lean:482 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_h_one` | Salt/Entropy/Chowla/FBridge.lean:555 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_h_one` | Salt/Entropy/Chowla/FBridge.lean:562 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_h_abs_le` | Salt/Entropy/Chowla/FBridge.lean:572 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_h_mem_Icc` | Salt/Entropy/Chowla/FBridge.lean:607 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_h_sum_over_residues` | Salt/Entropy/Chowla/FBridge.lean:648 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_h_mean` | Salt/Entropy/Chowla/FBridge.lean:671 | entropy |
| `Salt.Entropy.Chowla.fBridge_h_concentration_raw` | Salt/Entropy/Chowla/FBridge.lean:711 | entropy |
| `Salt.Entropy.Chowla.fBridge_h_concentration` | Salt/Entropy/Chowla/FBridge.lean:726 | entropy |
| `Salt.Entropy.Chowla.fBridge_h_concentration_sharp` | Salt/Entropy/Chowla/FBridge.lean:752 | entropy |
| `Salt.Entropy.Chowla.fBridge_h_concentration_decoupled_sharp` | Salt/Entropy/Chowla/FBridge.lean:801 | entropy |
| `Salt.Entropy.Chowla.entropy_sub_le_of_l1` | Salt/Entropy/Chowla/Fannes.lean:190 | entropy |
| `Salt.Entropy.Chowla.hsq_holds_gen'` | Salt/Entropy/Chowla/GoldbachEnergyFinal.lean:135 | entropy |
| `Salt.Entropy.Chowla.hsq_holds3` | Salt/Entropy/Chowla/GoldbachEnergyFinal.lean:176 | entropy |
| `Salt.Entropy.Chowla.hpt_holds` | Salt/Entropy/Chowla/GoldbachEnergyFinal.lean:396 | entropy |
| `Salt.Entropy.Chowla.bigXi_bounded` | Salt/Entropy/Chowla/GoldbachEnergyFinal.lean:502 | entropy |
| `Salt.Entropy.Chowla.goldSelbergTerms_prime_dvd` | Salt/Entropy/Chowla/GoldbachEnergyG.lean:62 | sieves, entropy |
| `Salt.Entropy.Chowla.goldSelbergTerms_prime_not_dvd` | Salt/Entropy/Chowla/GoldbachEnergyG.lean:75 | sieves, entropy |
| `Salt.Entropy.Chowla.gTwin_le_sCorr_mul_selbergTerms` | Salt/Entropy/Chowla/GoldbachEnergyG.lean:125 | sieves, entropy |
| `Salt.Entropy.Chowla.goldSelbergBoundingSum_ge_log_sq` | Salt/Entropy/Chowla/GoldbachEnergyG.lean:288 | sieves, entropy |
| `Salt.Entropy.Chowla.sTrunc2_pos` | Salt/Entropy/Chowla/GoldbachEnergyGc.lean:81 | entropy |
| `Salt.Entropy.Chowla.selbergTerms_eq_gTwin_of_coprime` | Salt/Entropy/Chowla/GoldbachEnergyGc.lean:126 | sieves, entropy |
| `Salt.Entropy.Chowla.goldCarrierSum_ge_log_sq_div_sTrunc2` | Salt/Entropy/Chowla/GoldbachEnergyGc.lean:245 | sieves, entropy |
| `Salt.Entropy.Chowla.goldSelbergBoundingSum_ge_log_sq_div_sTrunc2` | Salt/Entropy/Chowla/GoldbachEnergyGc.lean:287 | sieves, entropy |
| `Salt.Entropy.Chowla.repCount_eq_zero_of_window_odd` | Salt/Entropy/Chowla/GoldbachEnergyHpt.lean:54 | entropy |
| `Salt.Entropy.Chowla.goldSiftedSum_le_main_add_err` | Salt/Entropy/Chowla/GoldbachEnergyHpt.lean:138 | sieves, entropy |
| `Salt.Entropy.Chowla.goldBoundingSum_ge_uniform` | Salt/Entropy/Chowla/GoldbachEnergyHpt.lean:187 | sieves, entropy |
| `Salt.Entropy.Chowla.repCount_even_le_primorial` | Salt/Entropy/Chowla/GoldbachEnergyHpt.lean:240 | entropy |
| `Salt.Entropy.Chowla.hFac_mul_of_coprime` | Salt/Entropy/Chowla/GoldbachEnergyHsq.lean:77 | entropy |
| `Salt.Entropy.Chowla.sTrunc_le_prod` | Salt/Entropy/Chowla/GoldbachEnergyHsq.lean:129 | entropy |
| `Salt.Entropy.Chowla.hFac_lcm_sum_le` | Salt/Entropy/Chowla/GoldbachEnergyHsq.lean:359 | entropy |
| `Salt.Entropy.Chowla.hFac2_mul_of_coprime` | Salt/Entropy/Chowla/GoldbachEnergyHsq2.lean:53 | entropy |
| `Salt.Entropy.Chowla.hFac2_lcm_sum_le` | Salt/Entropy/Chowla/GoldbachEnergyHsq2.lean:257 | entropy |
| `Salt.Entropy.Chowla.hsq_holds2` | Salt/Entropy/Chowla/GoldbachEnergyHsq2.lean:369 | entropy |
| `Salt.Entropy.Chowla.sum_sTruncW_sq_le` | Salt/Entropy/Chowla/GoldbachEnergyHsqAsm.lean:90 | entropy |
| `Salt.Entropy.Chowla.hsq_holds_gen` | Salt/Entropy/Chowla/GoldbachEnergyHsqAsm.lean:152 | entropy |
| `Salt.Entropy.Chowla.hsq_holds` | Salt/Entropy/Chowla/GoldbachEnergyHsqAsm.lean:199 | entropy |
| `Salt.Entropy.Chowla.hFac2_lcm_sum_le_exp40` | Salt/Entropy/Chowla/GoldbachEnergyKc.lean:68 | entropy |
| `Salt.Entropy.Chowla.hFac2_lcm_sum_le_bounded` | Salt/Entropy/Chowla/GoldbachEnergyKc.lean:178 | entropy |
| `Salt.Entropy.Chowla.exp_forty_le_pow40` | Salt/Entropy/Chowla/GoldbachEnergyKc.lean:190 | entropy |
| `Salt.Entropy.Chowla.bigXi_bounded_500_explicit40` | Salt/Entropy/Chowla/GoldbachEnergyKc.lean:200 | entropy |
| `Salt.Entropy.Chowla.bigXi_bounded_500_ceiling` | Salt/Entropy/Chowla/GoldbachEnergyKc.lean:213 | entropy |
| `Salt.Entropy.Chowla.bigXi_bounded_ceiling_of_pin` | Salt/Entropy/Chowla/GoldbachEnergyKc.lean:231 | entropy |
| `Salt.Entropy.Chowla.hpt_const_le_pow35_h` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:52 | entropy |
| `Salt.Entropy.Chowla.h_le_1096_of_log_le_seven` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:107 | entropy |
| `Salt.Entropy.Chowla.h_le_1202604_of_log_le_fourteen` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:129 | entropy |
| `Salt.Entropy.Chowla.hpt_holds_500h` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:155 | entropy |
| `Salt.Entropy.Chowla.bigXiH_bounded_ceiling_of_pin` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:246 | entropy |
| `Salt.Entropy.Chowla.eps_line_h` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:323 | entropy |
| `Salt.Entropy.Chowla.h_le_8103_of_log_le_nine` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:340 | entropy |
| `Salt.Entropy.Chowla.hpt_const_le_pow35_h_b9` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:359 | entropy |
| `Salt.Entropy.Chowla.hpt_holds_500h_b9` | Salt/Entropy/Chowla/GoldbachEnergyKcH.lean:412 | entropy |
| `Salt.Entropy.Chowla.rhoG_prime_dvd` | Salt/Entropy/Chowla/GoldbachEnergyM2.lean:86 | entropy |
| `Salt.Entropy.Chowla.rhoG_prime_not_dvd` | Salt/Entropy/Chowla/GoldbachEnergyM2.lean:95 | entropy |
| `Salt.Entropy.Chowla.rhoG_mul_of_coprime` | Salt/Entropy/Chowla/GoldbachEnergyM2.lean:171 | entropy |
| `Salt.Entropy.Chowla.rhoG_squarefree_le` | Salt/Entropy/Chowla/GoldbachEnergyM2.lean:222 | entropy |
| `Salt.Entropy.Chowla.goldProgression_count_bound` | Salt/Entropy/Chowla/GoldbachEnergyM2.lean:253 | entropy |
| `Salt.Entropy.Chowla.mainTermSum_ge_of_sixteen` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:139 | entropy |
| `Salt.Entropy.Chowla.logZ_ge_twenty` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:181 | entropy |
| `Salt.Entropy.Chowla.repCount_even_le_primorial_param` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:289 | entropy |
| `Salt.Entropy.Chowla.hpt_large_thr` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:340 | sieves, entropy |
| `Salt.Entropy.Chowla.hpt_holds_thr` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:544 | sieves, entropy |
| `Salt.Entropy.Chowla.hsq_explicit` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:672 | entropy |
| `Salt.Entropy.Chowla.bigXi_bounded_explicit` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:718 | entropy |
| `Salt.Entropy.Chowla.hpt_const_le_pow35` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:809 | entropy |
| `Salt.Entropy.Chowla.hpt_holds_500` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:829 | entropy |
| `Salt.Entropy.Chowla.bigXi_bounded_500` | Salt/Entropy/Chowla/GoldbachEnergyN0.lean:866 | entropy |
| `Salt.Entropy.Chowla.nuG_mult` | Salt/Entropy/Chowla/GoldbachEnergySieve.lean:52 | sieves, entropy |
| `Salt.Entropy.Chowla.nuG_lt_one_of_prime` | Salt/Entropy/Chowla/GoldbachEnergySieve.lean:77 | sieves, entropy |
| `Salt.Entropy.Chowla.goldEnergySieve_siftedSum` | Salt/Entropy/Chowla/GoldbachEnergySieve.lean:156 | sieves, entropy |
| `Salt.Entropy.Chowla.goldEnergySieve_abs_rem_le` | Salt/Entropy/Chowla/GoldbachEnergySieve.lean:174 | sieves, entropy |
| `Salt.Entropy.Chowla.repCount_le_siftedSum` | Salt/Entropy/Chowla/GoldbachEnergySieve.lean:191 | sieves, entropy |
| `Salt.Entropy.Chowla.epsh_gate_implies_epssq_h` | Salt/Entropy/Chowla/HBudget.lean:450 | entropy |
| `Salt.Entropy.Chowla.hbudget_holds` | Salt/Entropy/Chowla/HBudget.lean:475 | entropy |
| `Salt.Entropy.Chowla.hreduce_holds_final` | Salt/Entropy/Chowla/HBudget.lean:732 | characters, entropy |
| `Salt.Entropy.Chowla.hbudget_holds_h` | Salt/Entropy/Chowla/HBudget.lean:1182 | entropy |
| `Salt.Entropy.Chowla.hbudget_h_gate_implies_epssq_h` | Salt/Entropy/Chowla/HBudget.lean:1471 | entropy |
| `Salt.Entropy.Chowla.hbudget_holds_h_one` | Salt/Entropy/Chowla/HBudget.lean:1489 | entropy |
| `Salt.Entropy.Chowla.hreduce_holds_final_h` | Salt/Entropy/Chowla/HBudget.lean:1514 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_holds` | Salt/Entropy/Chowla/HMainAssembly.lean:103 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_holds_h` | Salt/Entropy/Chowla/HMainAssembly.lean:165 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_holds_h_one` | Salt/Entropy/Chowla/HMainAssembly.lean:210 | characters, entropy |
| `Salt.Entropy.Chowla.consumability_probe` | Salt/Entropy/Chowla/HReduce.lean:76 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_close` | Salt/Entropy/Chowla/HReduce.lean:103 | characters, entropy |
| `Salt.Entropy.Chowla.consumability_probe_h` | Salt/Entropy/Chowla/HReduce.lean:140 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_close_h` | Salt/Entropy/Chowla/HReduce.lean:167 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_close_h_one` | Salt/Entropy/Chowla/HReduce.lean:197 | characters, entropy |
| `Salt.Entropy.Chowla.hbudget_holds_h_bounded` | Salt/Entropy/Chowla/HeadPinLeavesH.lean:56 | entropy |
| `Salt.Entropy.Chowla.hreduce_holds_final_h_bounded` | Salt/Entropy/Chowla/HeadPinLeavesH.lean:344 | characters, entropy |
| `Salt.Entropy.Chowla.circle_method_estimate_sq_bounded_h_core` | Salt/Entropy/Chowla/HeadPinLeavesH.lean:375 | entropy |
| `Salt.Entropy.Chowla.circle_method_estimate_sq_bounded_h` | Salt/Entropy/Chowla/HeadPinLeavesH.lean:511 | entropy |
| `Salt.Entropy.Chowla.harmonic_shift_l1_le` | Salt/Entropy/Chowla/Invariance.lean:68 | entropy |
| `Salt.Entropy.Chowla.condEntropy_shift_reduction` | Salt/Entropy/Chowla/InvarianceHead.lean:108 | characters, entropy |
| `Salt.Entropy.Chowla.condEntropy_shift_le_of_l1` | Salt/Entropy/Chowla/InvarianceHead.lean:150 | characters, entropy |
| `Salt.Entropy.Chowla.windowPhi_norm_le` | Salt/Entropy/Chowla/LargeSpectrum.lean:48 | entropy |
| `Salt.Entropy.Chowla.expSum_eq_dft_windowPhi` | Salt/Entropy/Chowla/LargeSpectrum.lean:73 | entropy, exponential sums |
| `Salt.Entropy.Chowla.card_bigXi_mul_thresh_le` | Salt/Entropy/Chowla/LargeSpectrum.lean:122 | entropy, exponential sums |
| `Salt.Entropy.Chowla.dft_windowPhi_l4_le` | Salt/Entropy/Chowla/LargeSpectrum.lean:174 | entropy |
| `Salt.Entropy.Chowla.large_spectrum_energy` | Salt/Entropy/Chowla/LargeSpectrum.lean:297 | entropy |
| `Salt.Entropy.Chowla.bigXi_bounded_of_sieve` | Salt/Entropy/Chowla/LargeSpectrumBound.lean:48 | entropy |
| `Salt.Entropy.Chowla.isProbabilityMeasure_logMeasure` | Salt/Entropy/Chowla/LogMeasure.lean:70 | entropy |
| `Salt.Entropy.Chowla.logMeasure_apply_singleton` | Salt/Entropy/Chowla/LogMeasure.lean:90 | entropy |
| `Salt.Entropy.Chowla.harmonic_window_bounds` | Salt/Entropy/Chowla/LogMeasure.lean:115 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_abs_le_box` | Salt/Entropy/Chowla/OuterCombine.lean:111 | entropy |
| `Salt.Entropy.Chowla.decoupledMean_abs_le_box` | Salt/Entropy/Chowla/OuterCombine.lean:118 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_h_abs_le_boxSum` | Salt/Entropy/Chowla/OuterCombine.lean:134 | entropy |
| `Salt.Entropy.Chowla.decoupledMean_h_abs_le_boxSum` | Salt/Entropy/Chowla/OuterCombine.lean:147 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_h_abs_le_box` | Salt/Entropy/Chowla/OuterCombine.lean:172 | entropy |
| `Salt.Entropy.Chowla.decoupledMean_h_abs_le_box` | Salt/Entropy/Chowla/OuterCombine.lean:179 | entropy |
| `Salt.Entropy.Chowla.outer_badMass_eq` | Salt/Entropy/Chowla/OuterCombine.lean:193 | characters, entropy |
| `Salt.Entropy.Chowla.outer_badMass_le` | Salt/Entropy/Chowla/OuterCombine.lean:242 | characters, entropy |
| `Salt.Entropy.Chowla.outer_combine` | Salt/Entropy/Chowla/OuterCombine.lean:346 | characters, entropy |
| `Salt.Entropy.Chowla.outer_badMass_h_eq` | Salt/Entropy/Chowla/OuterCombine.lean:482 | characters, entropy |
| `Salt.Entropy.Chowla.outer_badMass_h_le` | Salt/Entropy/Chowla/OuterCombine.lean:526 | characters, entropy |
| `Salt.Entropy.Chowla.outer_combine_h` | Salt/Entropy/Chowla/OuterCombine.lean:620 | characters, entropy |
| `Salt.Entropy.Chowla.slack_witness_twinDetecting` | Salt/Entropy/Chowla/PinDichotomy.lean:98 | entropy |
| `Salt.Entropy.Chowla.slack_witness_not_twinDetecting'` | Salt/Entropy/Chowla/PinDichotomy.lean:110 | entropy |
| `Salt.Entropy.Chowla.liouville_pinned` | Salt/Entropy/Chowla/PinDichotomy.lean:260 | characters, entropy |
| `Salt.Entropy.Chowla.chi4w_detecting'` | Salt/Entropy/Chowla/PinDichotomy.lean:293 | entropy |
| `Salt.Entropy.Chowla.chi4w_detecting` | Salt/Entropy/Chowla/PinDichotomy.lean:297 | entropy |
| `Salt.Entropy.Chowla.corr_zero_blind` | Salt/Entropy/Chowla/PinDichotomy.lean:303 | entropy |
| `Salt.Entropy.Chowla.delta1w_corr` | Salt/Entropy/Chowla/PinDichotomy.lean:311 | entropy |
| `Salt.Entropy.Chowla.delta1w_blind` | Salt/Entropy/Chowla/PinDichotomy.lean:316 | entropy |
| `Salt.Entropy.Chowla.delta1w_pairCollapse` | Salt/Entropy/Chowla/PinDichotomy.lean:320 | entropy |
| `Salt.Entropy.Chowla.delta1w_not_pmNormalized` | Salt/Entropy/Chowla/PinDichotomy.lean:333 | entropy |
| `Salt.Entropy.Chowla.chi4w_pairCollapse` | Salt/Entropy/Chowla/PinDichotomy.lean:346 | entropy |
| `Salt.Entropy.Chowla.door_criterion_needs_zero_blindness` | Salt/Entropy/Chowla/PinDichotomy.lean:402 | entropy |
| `Salt.Entropy.Chowla.entropy_residueWindow_le_log_PH` | Salt/Entropy/Chowla/PrimeWindow.lean:65 | entropy |
| `Salt.Entropy.Chowla.log_PH_le` | Salt/Entropy/Chowla/PrimeWindow.lean:91 | entropy |
| `Salt.Entropy.Chowla.coprime_PH_of_le` | Salt/Entropy/Chowla/PrimeWindow.lean:145 | entropy |
| `Salt.Entropy.Chowla.perPair_dilation` | Salt/Entropy/Chowla/Prop26.lean:130 | entropy |
| `Salt.Entropy.Chowla.fBridge_of_singleCorr` | Salt/Entropy/Chowla/Prop26.lean:160 | characters, entropy |
| `Salt.Entropy.Chowla.fBridgeF_h_liouville_apply_one` | Salt/Entropy/Chowla/Prop26.lean:243 | characters, entropy |
| `Salt.Entropy.Chowla.perPair_dilation_h` | Salt/Entropy/Chowla/Prop26.lean:257 | entropy |
| `Salt.Entropy.Chowla.fBridge_of_singleCorr_h` | Salt/Entropy/Chowla/Prop26.lean:286 | characters, entropy |
| `Salt.Entropy.Chowla.addEnergy_eq_sum_repCount_sq` | Salt/Entropy/Chowla/QuadrupleCount.lean:48 | entropy |
| `Salt.Entropy.Chowla.addEnergy_le_of_r_bound` | Salt/Entropy/Chowla/QuadrupleCount.lean:60 | entropy |
| `Salt.Entropy.Chowla.W3_AE_d_of_sieve` | Salt/Entropy/Chowla/QuadrupleCount.lean:83 | entropy |
| `Salt.Entropy.Chowla.dvd_chowlaTower` | Salt/Entropy/Chowla/Regime.lean:148 | entropy |
| `Salt.Entropy.Chowla.omega_big_at` | Salt/Entropy/Chowla/Regime.lean:241 | entropy |
| `Salt.Entropy.Chowla.x_big_at` | Salt/Entropy/Chowla/Regime.lean:261 | entropy |
| `Salt.Entropy.Chowla.regime_outer` | Salt/Entropy/Chowla/RegimeInst.lean:88 | entropy |
| `Salt.Entropy.Chowla.regime_exists_of_dropSum_exists` | Salt/Entropy/Chowla/RegimeInst.lean:201 | entropy |
| `Salt.Entropy.Chowla.dropSum_exceeds_log_two_base` | Salt/Entropy/Chowla/RegimeParam.lean:219 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists_param_gen` | Salt/Entropy/Chowla/RegimeParam.lean:386 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists_param` | Salt/Entropy/Chowla/RegimeParam.lean:474 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists_param_head'` | Salt/Entropy/Chowla/RegimeParam.lean:543 | entropy |
| `Salt.Entropy.Chowla.entropy_ge_of_mass_ub` | Salt/Entropy/Chowla/ResidueUniform.lean:65 | entropy |
| `Salt.Entropy.Chowla.entropy_residueWindow_ge` | Salt/Entropy/Chowla/ResidueUniform.lean:536 | entropy |
| `Salt.Entropy.Chowla.integral_logMeasure_eq` | Salt/Entropy/Chowla/ShiftCorr.lean:42 | entropy |
| `Salt.Entropy.Chowla.integral_shift_le` | Salt/Entropy/Chowla/ShiftCorr.lean:235 | entropy |
| `Salt.Entropy.Chowla.corr_shift_le` | Salt/Entropy/Chowla/ShiftCorr.lean:276 | entropy |
| `Salt.Entropy.Chowla.bigXi_eq_bigXiH_one` | Salt/Entropy/Chowla/ShiftFork.lean:105 | entropy |
| `Salt.Entropy.Chowla.mem_bigXiH_iff` | Salt/Entropy/Chowla/ShiftFork.lean:118 | entropy |
| `Salt.Entropy.Chowla.bigXiH_card_le_gcd_mul` | Salt/Entropy/Chowla/ShiftFork.lean:224 | entropy |
| `Salt.Entropy.Chowla.bigXiH_card_le_mul` | Salt/Entropy/Chowla/ShiftFork.lean:239 | entropy |
| `Salt.Entropy.Chowla.bigXiH_bounded` | Salt/Entropy/Chowla/ShiftFork.lean:253 | entropy |
| `Salt.Entropy.Chowla.mrtUniformityXi_eq_xiH_one` | Salt/Entropy/Chowla/ShiftFork.lean:314 | entropy |
| `Salt.Entropy.Chowla.bigXiH_eq_twistFilter` | Salt/Entropy/Chowla/ShiftFork.lean:386 | entropy |
| `Salt.Entropy.Chowla.circle_method_estimate_h` | Salt/Entropy/Chowla/ShiftFork.lean:404 | entropy |
| `Salt.Entropy.Chowla.circle_method_estimate_sq_h` | Salt/Entropy/Chowla/ShiftFork.lean:442 | entropy |
| `Salt.Entropy.Chowla.liouville_collapse_h` | Salt/Entropy/Chowla/ShiftFork.lean:479 | characters, entropy |
| `Salt.Entropy.Chowla.mrtUniformityXiL2_eq_xiL2H_one` | Salt/Entropy/Chowla/ShiftFork.lean:555 | entropy |
| `Salt.Entropy.Chowla.agreeMass_sub_disagreeMass` | Salt/Entropy/Chowla/SignSplit.lean:122 | characters, entropy |
| `Salt.Entropy.Chowla.regime_logOmega_ge` | Salt/Entropy/Chowla/SignSplit.lean:174 | entropy |
| `Salt.Entropy.Chowla.sign_split_pos` | Salt/Entropy/Chowla/SignSplit.lean:269 | entropy |
| `Salt.Entropy.Chowla.margin_fails_vanishing_demand` | Salt/Entropy/Chowla/SpineEpsFence.lean:67 | entropy |
| `Salt.Entropy.Chowla.margin_not_forall_of_vanishing_demand` | Salt/Entropy/Chowla/SpineEpsFence.lean:76 | entropy |
| `Salt.Entropy.Chowla.spine_eps_constant_floor` | Salt/Entropy/Chowla/SpineEpsFence.lean:102 | entropy |
| `Salt.Entropy.Chowla.joint_l1_le` | Salt/Entropy/Chowla/Step.lean:255 | entropy |
| `Salt.Entropy.Chowla.condEntropy_shift_le` | Salt/Entropy/Chowla/Step.lean:417 | characters, entropy |
| `Salt.Entropy.Chowla.step_ineq_3_11` | Salt/Entropy/Chowla/Step.lean:696 | characters, entropy |
| `Salt.Entropy.Chowla.fBridgeG_aff_one_zero` | Salt/Entropy/Chowla/StrideBridge.lean:107 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_aff_one_zero` | Salt/Entropy/Chowla/StrideBridge.lean:117 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_aff_abs_le` | Salt/Entropy/Chowla/StrideBridge.lean:131 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_aff_mem_Icc` | Salt/Entropy/Chowla/StrideBridge.lean:179 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_aff_sum_over_residues` | Salt/Entropy/Chowla/StrideBridge.lean:195 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_aff_mean` | Salt/Entropy/Chowla/StrideBridge.lean:233 | entropy |
| `Salt.Entropy.Chowla.fBridge_aff_concentration_raw` | Salt/Entropy/Chowla/StrideBridge.lean:275 | entropy |
| `Salt.Entropy.Chowla.fBridge_aff_concentration` | Salt/Entropy/Chowla/StrideBridge.lean:289 | entropy |
| `Salt.Entropy.Chowla.fBridge_aff_concentration_sharp` | Salt/Entropy/Chowla/StrideBridge.lean:314 | entropy |
| `Salt.Entropy.Chowla.fBridge_aff_concentration_decoupled_sharp` | Salt/Entropy/Chowla/StrideBridge.lean:363 | entropy |
| `Salt.Entropy.Chowla.affFilter_spec_three` | Salt/Entropy/Chowla/StrideBridge.lean:397 | entropy |
| `Salt.Entropy.Chowla.affFilter_spec_two` | Salt/Entropy/Chowla/StrideBridge.lean:405 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_aff_two_one` | Salt/Entropy/Chowla/StrideBridge.lean:418 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_aff_liouville_apply_one_zero` | Salt/Entropy/Chowla/StrideBridge.lean:491 | characters, entropy |
| `Salt.Entropy.Chowla.affGate_index_eq` | Salt/Entropy/Chowla/StrideBridge.lean:508 | entropy |
| `Salt.Entropy.Chowla.liouville_collapse_aff` | Salt/Entropy/Chowla/StrideBridge.lean:522 | characters, entropy |
| `Salt.Entropy.Chowla.perPair_collapse_aff` | Salt/Entropy/Chowla/StrideBridge.lean:540 | entropy |
| `Salt.Entropy.Chowla.affCollapse_base_point` | Salt/Entropy/Chowla/StrideBridge.lean:567 | entropy |
| `Salt.Entropy.Chowla.fBridge_of_singleCorr_aff` | Salt/Entropy/Chowla/StrideBridge.lean:588 | characters, entropy |
| `Salt.Entropy.Chowla.fBridge_of_singleCorr_aff'` | Salt/Entropy/Chowla/StrideBridge.lean:639 | characters, entropy |
| `Salt.Entropy.Chowla.dft_twist` | Salt/Entropy/Chowla/StrideCircle.lean:116 | entropy, exponential sums |
| `Salt.Entropy.Chowla.norm_twist_mul` | Salt/Entropy/Chowla/StrideCircle.lean:128 | entropy, exponential sums |
| `Salt.Entropy.Chowla.stdAddChar_lift_of_dvd` | Salt/Entropy/Chowla/StrideCircle.lean:141 | entropy, exponential sums |
| `Salt.Entropy.Chowla.classFilter_expand` | Salt/Entropy/Chowla/StrideCircle.lean:185 | entropy, exponential sums |
| `Salt.Entropy.Chowla.filteredCorr_eq_twistSum` | Salt/Entropy/Chowla/StrideCircle.lean:264 | entropy, exponential sums |
| `Salt.Entropy.Chowla.periodization_total_twist` | Salt/Entropy/Chowla/StrideCircle.lean:373 | entropy, exponential sums |
| `Salt.Entropy.Chowla.T_collapse_twist` | Salt/Entropy/Chowla/StrideCircle.lean:485 | entropy, exponential sums |
| `Salt.Entropy.Chowla.fourier_split_sq_twist` | Salt/Entropy/Chowla/StrideCircle.lean:547 | entropy, exponential sums |
| `Salt.Entropy.Chowla.xiEta_subset_bigXiAff` | Salt/Entropy/Chowla/StrideCircle.lean:647 | entropy |
| `Salt.Entropy.Chowla.xiEta_translate_mem_bigXiAff` | Salt/Entropy/Chowla/StrideCircle.lean:667 | entropy |
| `Salt.Entropy.Chowla.sum_xiEta_le` | Salt/Entropy/Chowla/StrideCircle.lean:736 | entropy |
| `Salt.Entropy.Chowla.sum_xiEta_translate_le` | Salt/Entropy/Chowla/StrideCircle.lean:751 | entropy |
| `Salt.Entropy.Chowla.circle_method_estimate_sq_bounded_aff` | Salt/Entropy/Chowla/StrideCircle.lean:802 | entropy |
| `Salt.Entropy.Chowla.circle_method_estimate_sq_aff_core` | Salt/Entropy/Chowla/StrideCircle.lean:1066 | entropy |
| `Salt.Entropy.Chowla.entropy_residueWindow_aff_eq` | Salt/Entropy/Chowla/StrideCombine.lean:64 | entropy |
| `Salt.Entropy.Chowla.entropy_residueWindow_ge_aff` | Salt/Entropy/Chowla/StrideCombine.lean:88 | entropy |
| `Salt.Entropy.Chowla.weakUniform_spine_aff` | Salt/Entropy/Chowla/StrideCombine.lean:98 | characters, entropy |
| `Salt.Entropy.Chowla.badSet_aff_one_zero` | Salt/Entropy/Chowla/StrideCombine.lean:138 | entropy |
| `Salt.Entropy.Chowla.badSet_transport_aff` | Salt/Entropy/Chowla/StrideCombine.lean:152 | characters, entropy |
| `Salt.Entropy.Chowla.badSet_transport_at_calibration_aff` | Salt/Entropy/Chowla/StrideCombine.lean:213 | characters, entropy |
| `Salt.Entropy.Chowla.fBridgeF_aff_abs_le_boxSum` | Salt/Entropy/Chowla/StrideCombine.lean:269 | entropy |
| `Salt.Entropy.Chowla.decoupledMean_aff_abs_le_boxSum` | Salt/Entropy/Chowla/StrideCombine.lean:282 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_aff_abs_le_box` | Salt/Entropy/Chowla/StrideCombine.lean:313 | entropy |
| `Salt.Entropy.Chowla.decoupledMean_aff_abs_le_box` | Salt/Entropy/Chowla/StrideCombine.lean:322 | entropy |
| `Salt.Entropy.Chowla.outer_badMass_aff_eq` | Salt/Entropy/Chowla/StrideCombine.lean:337 | characters, entropy |
| `Salt.Entropy.Chowla.outer_badMass_aff_le` | Salt/Entropy/Chowla/StrideCombine.lean:381 | characters, entropy |
| `Salt.Entropy.Chowla.outer_combine_aff` | Salt/Entropy/Chowla/StrideCombine.lean:468 | characters, entropy |
| `Salt.Entropy.Chowla.outer_combine_aff_one_zero` | Salt/Entropy/Chowla/StrideCombine.lean:580 | characters, entropy |
| `Salt.Entropy.Chowla.finiteSupport_logMeasureAff` | Salt/Entropy/Chowla/StrideDecrement.lean:62 | entropy |
| `Salt.Entropy.Chowla.joint_l1_le_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:98 | entropy |
| `Salt.Entropy.Chowla.condEntropy_shift_reduction_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:177 | characters, entropy |
| `Salt.Entropy.Chowla.condEntropy_shift_le_of_l1_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:218 | characters, entropy |
| `Salt.Entropy.Chowla.condEntropy_shift_le_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:267 | characters, entropy |
| `Salt.Entropy.Chowla.condEntropy_kwindow_le_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:362 | characters, entropy |
| `Salt.Entropy.Chowla.step_ineq_3_11_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:418 | characters, entropy |
| `Salt.Entropy.Chowla.tower_step_of_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:526 | characters, entropy |
| `Salt.Entropy.Chowla.tower_step_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:581 | entropy |
| `Salt.Entropy.Chowla.tower_telescope_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:613 | entropy |
| `Salt.Entropy.Chowla.entropy_per_symbol_le_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:640 | characters, entropy |
| `Salt.Entropy.Chowla.entropy_nonneg_per_symbol_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:648 | characters, entropy |
| `Salt.Entropy.Chowla.mutualInfo_window_nonneg_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:654 | characters, entropy |
| `Salt.Entropy.Chowla.mutualInfo_window_comm_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:664 | characters, entropy |
| `Salt.Entropy.Chowla.decrement_exists_of_tower_aff` | Salt/Entropy/Chowla/StrideDecrement.lean:688 | characters, entropy |
| `Salt.Entropy.Chowla.entropy_decrementAff` | Salt/Entropy/Chowla/StrideDecrement.lean:729 | characters, entropy |
| `Salt.Entropy.Chowla.entropy_decrementAff_one` | Salt/Entropy/Chowla/StrideDecrement.lean:749 | characters, entropy |
| `Salt.Entropy.Chowla.mem_bigXiAff_iff` | Salt/Entropy/Chowla/StrideFork.lean:218 | entropy |
| `Salt.Entropy.Chowla.bigXiAff_one_zero` | Salt/Entropy/Chowla/StrideFork.lean:229 | entropy |
| `Salt.Entropy.Chowla.affOffset_spec` | Salt/Entropy/Chowla/StrideFork.lean:249 | entropy |
| `Salt.Entropy.Chowla.card_affPreimage_le` | Salt/Entropy/Chowla/StrideFork.lean:336 | entropy |
| `Salt.Entropy.Chowla.bigXiAff_card_le` | Salt/Entropy/Chowla/StrideFork.lean:356 | entropy |
| `Salt.Entropy.Chowla.bigXiAff_card_le_mul` | Salt/Entropy/Chowla/StrideFork.lean:379 | entropy |
| `Salt.Entropy.Chowla.bigXiAff_bounded` | Salt/Entropy/Chowla/StrideFork.lean:391 | entropy |
| `Salt.Entropy.Chowla.bigXiAff_bounded_ceiling_of_pin` | Salt/Entropy/Chowla/StrideFork.lean:413 | entropy |
| `Salt.Entropy.Chowla.chowlaTower_eq_base_one` | Salt/Entropy/Chowla/StrideFork.lean:515 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists_flat_stride` | Salt/Entropy/Chowla/StrideFork.lean:549 | entropy |
| `Salt.Entropy.Chowla.mrtUniformityXiH_eq_xiAff_one_zero` | Salt/Entropy/Chowla/StrideFork.lean:667 | entropy |
| `Salt.Entropy.Chowla.mrtUniformityXiL2H_eq_xiL2Aff_one_zero` | Salt/Entropy/Chowla/StrideFork.lean:692 | entropy |
| `Salt.Entropy.Chowla.sum_window_aff_eq` | Salt/Entropy/Chowla/StrideFork.lean:782 | entropy |
| `Salt.Entropy.Chowla.bigXiAff_bounded_ceiling_of_pin_b9` | Salt/Entropy/Chowla/StrideFork.lean:807 | entropy |
| `Salt.Entropy.Chowla.strideScale_one` | Salt/Entropy/Chowla/StridePair.lean:84 | entropy |
| `Salt.Entropy.Chowla.chowlaTower_ge_base` | Salt/Entropy/Chowla/StridePair.lean:101 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_tower` | Salt/Entropy/Chowla/StridePair.lean:282 | entropy |
| `Salt.Entropy.Chowla.bigXiAffD_card_le` | Salt/Entropy/Chowla/StridePair.lean:320 | entropy |
| `Salt.Entropy.Chowla.mrtUniformityXiL2AffW_one_zero_eq` | Salt/Entropy/Chowla/StridePair.lean:408 | entropy |
| `Salt.Entropy.Chowla.sum_window_image_le` | Salt/Entropy/Chowla/StridePair.lean:473 | entropy |
| `Salt.Entropy.Chowla.integral_logMeasureAff_le_plain` | Salt/Entropy/Chowla/StridePair.lean:514 | entropy |
| `Salt.Entropy.Chowla.strideZRatio_le` | Salt/Entropy/Chowla/StridePair.lean:715 | entropy |
| `Salt.Entropy.Chowla.strideEndpoint_le` | Salt/Entropy/Chowla/StridePair.lean:732 | entropy |
| `Salt.Entropy.Chowla.loglog_mul_flatDesignBase_le` | Salt/Entropy/Chowla/StridePair.lean:757 | entropy |
| `Salt.Entropy.Chowla.flatDesignBase_clears_stride_floors` | Salt/Entropy/Chowla/StridePair.lean:803 | entropy |
| `Salt.Entropy.Chowla.loglog_mul_flatDesignBase_le_b9` | Salt/Entropy/Chowla/StridePair.lean:842 | entropy |
| `Salt.Entropy.Chowla.flatDesignBase_clears_stride_floors_b9` | Salt/Entropy/Chowla/StridePair.lean:885 | entropy |
| `Salt.Entropy.Chowla.flatDesignBase_ge_pow600` | Salt/Entropy/Chowla/StridePrize.lean:60 | entropy |
| `Salt.Entropy.Chowla.gcd_dvd_two_of_coprime` | Salt/Entropy/Chowla/StridePrize.lean:106 | entropy |
| `Salt.Entropy.Chowla.strideWindow_Z_pos` | Salt/Entropy/Chowla/StrideReduce.lean:73 | entropy |
| `Salt.Entropy.Chowla.strideWindow_sum_inv_sq` | Salt/Entropy/Chowla/StrideReduce.lean:88 | entropy |
| `Salt.Entropy.Chowla.strideBoundary_card_le` | Salt/Entropy/Chowla/StrideReduce.lean:113 | entropy |
| `Salt.Entropy.Chowla.gate_residue_aff` | Salt/Entropy/Chowla/StrideReduce.lean:136 | entropy |
| `Salt.Entropy.Chowla.card_class_range_le` | Salt/Entropy/Chowla/StrideReduce.lean:187 | entropy |
| `Salt.Entropy.Chowla.card_class_range_ge` | Salt/Entropy/Chowla/StrideReduce.lean:214 | entropy |
| `Salt.Entropy.Chowla.card_class_boundary_le` | Salt/Entropy/Chowla/StrideReduce.lean:256 | entropy |
| `Salt.Entropy.Chowla.shiftCorrAff_le` | Salt/Entropy/Chowla/StrideReduce.lean:292 | entropy |
| `Salt.Entropy.Chowla.absXaff_le_one` | Salt/Entropy/Chowla/StrideReduce.lean:331 | entropy |
| `Salt.Entropy.Chowla.perPair_collapse_aff_collapsed` | Salt/Entropy/Chowla/StrideReduce.lean:371 | entropy |
| `Salt.Entropy.Chowla.perPair_bound_aff` | Salt/Entropy/Chowla/StrideReduce.lean:419 | entropy |
| `Salt.Entropy.Chowla.IF_unfold_aff` | Salt/Entropy/Chowla/StrideReduce.lean:573 | characters, entropy |
| `Salt.Entropy.Chowla.per_term_aff` | Salt/Entropy/Chowla/StrideReduce.lean:629 | entropy |
| `Salt.Entropy.Chowla.hbudget_holds_aff` | Salt/Entropy/Chowla/StrideReduce.lean:759 | entropy |
| `Salt.Entropy.Chowla.hreduce_holds_aff` | Salt/Entropy/Chowla/StrideReduce.lean:1244 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_close_aff` | Salt/Entropy/Chowla/StrideReduce.lean:1288 | characters, entropy |
| `Salt.Entropy.Chowla.consumability_probe_aff` | Salt/Entropy/Chowla/StrideReduce.lean:1316 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_holds_final_aff` | Salt/Entropy/Chowla/StrideReduce.lean:1340 | characters, entropy |
| `Salt.Entropy.Chowla.hreduce_holds_aff_one_zero` | Salt/Entropy/Chowla/StrideReduce.lean:1378 | characters, entropy |
| `Salt.Entropy.Chowla.budgetFloor_le_flatDesignBase` | Salt/Entropy/Chowla/StrideShell.lean:75 | entropy |
| `Salt.Entropy.Chowla.nat_le_flatDesignBase` | Salt/Entropy/Chowla/StrideShell.lean:83 | entropy |
| `Salt.Entropy.Chowla.flatDesignBase_mono` | Salt/Entropy/Chowla/StrideShellBand.lean:61 | entropy |
| `Salt.Entropy.Chowla.affGrade_composes_g12b` | Salt/Entropy/Chowla/StrideShellBand.lean:287 | entropy |
| `Salt.Entropy.Chowla.tower_step` | Salt/Entropy/Chowla/Tower.lean:210 | entropy |
| `Salt.Entropy.Chowla.tower_telescope` | Salt/Entropy/Chowla/Tower.lean:246 | entropy |
| `Salt.Entropy.Chowla.towerDropSum_ge_half_log_ratio` | Salt/Entropy/Chowla/TowerExport.lean:502 | entropy |
| `Salt.Entropy.Chowla.towerDropSum_le_half_log_ratio_mul` | Salt/Entropy/Chowla/TowerExport.lean:539 | entropy |
| `Salt.Entropy.Chowla.towerJmin_spec` | Salt/Entropy/Chowla/TowerExport.lean:582 | entropy |
| `Salt.Entropy.Chowla.towerDropSum_le_log_two_of_lt_towerJmin` | Salt/Entropy/Chowla/TowerExport.lean:587 | entropy |
| `Salt.Entropy.Chowla.tower_loglog_le` | Salt/Entropy/Chowla/TowerExport.lean:617 | entropy |
| `Salt.Entropy.Chowla.tower_loglog_ge` | Salt/Entropy/Chowla/TowerExport.lean:673 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists_param_tower` | Salt/Entropy/Chowla/TowerExport.lean:733 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists_param_head_tower'` | Salt/Entropy/Chowla/TowerExport.lean:755 | entropy |
| `Salt.Entropy.Chowla.three_halves_lt_log_nine_halves` | Salt/Entropy/Chowla/TowerExport.lean:792 | entropy |
| `Salt.Entropy.Chowla.rpow_nine_halves_le_pow_five` | Salt/Entropy/Chowla/TowerExport.lean:809 | entropy |
| `Salt.Entropy.Chowla.tower_loglog_le_45` | Salt/Entropy/Chowla/TowerExport.lean:822 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists_param_tower_45` | Salt/Entropy/Chowla/TowerExport.lean:876 | entropy |
| `Salt.Entropy.Chowla.chowlaRegime_exists_param_head_tower45'` | Salt/Entropy/Chowla/TowerExport.lean:892 | entropy |
| `Salt.Entropy.Chowla.towerDropSumFlat_ge_log_ratio` | Salt/Entropy/Chowla/TowerFlat.lean:419 | entropy |
| `Salt.Entropy.Chowla.towerDropSumFlat_le_log_ratio_mul` | Salt/Entropy/Chowla/TowerFlat.lean:443 | entropy |
| `Salt.Entropy.Chowla.towerFlat_width_ge` | Salt/Entropy/Chowla/TowerFlat.lean:585 | entropy |
| `Salt.Entropy.Chowla.towerFlat_width_le` | Salt/Entropy/Chowla/TowerFlat.lean:625 | entropy |
| `Salt.Entropy.Chowla.towerShape_width_ge` | Salt/Entropy/Chowla/TowerShape.lean:362 | entropy |
| `Salt.Entropy.Chowla.chowlaTowerShape_const` | Salt/Entropy/Chowla/TowerShape.lean:398 | entropy |
| `Salt.Entropy.Chowla.towerLS_const` | Salt/Entropy/Chowla/TowerShape.lean:404 | entropy |
| `Salt.Entropy.Chowla.towerLamS_const` | Salt/Entropy/Chowla/TowerShape.lean:407 | entropy |
| `Salt.Entropy.Chowla.towerWS_const` | Salt/Entropy/Chowla/TowerShape.lean:410 | entropy |
| `Salt.Entropy.Chowla.towerDropSumShape_const` | Salt/Entropy/Chowla/TowerShape.lean:413 | entropy |
| `Salt.Entropy.Chowla.towerShape_flat_le` | Salt/Entropy/Chowla/TowerShape.lean:429 | entropy |
| `Salt.Entropy.Chowla.badSet_transport` | Salt/Entropy/Chowla/Transport.lean:69 | characters, entropy |
| `Salt.Entropy.Chowla.badSet_transport_at_calibration` | Salt/Entropy/Chowla/Transport.lean:128 | characters, entropy |
| `Salt.Entropy.Chowla.badSet_h_one` | Salt/Entropy/Chowla/Transport.lean:211 | entropy |
| `Salt.Entropy.Chowla.badSet_transport_h` | Salt/Entropy/Chowla/Transport.lean:243 | characters, entropy |
| `Salt.Entropy.Chowla.badSet_transport_at_calibration_h` | Salt/Entropy/Chowla/Transport.lean:302 | characters, entropy |
| `Salt.Entropy.Chowla.weakUniform_generic` | Salt/Entropy/Chowla/WeakUniform.lean:139 | entropy |
| `Salt.Entropy.Chowla.weakUniform_spine` | Salt/Entropy/Chowla/WeakUniform.lean:184 | characters, entropy |
| `Salt.Entropy.Chowla.primeWindow_card_le_of_regime` | Salt/Entropy/Chowla/WindowCount.lean:47 | entropy |
| `Salt.Entropy.Chowla.regime_nonvacuous` | Salt/Entropy/Chowla/WindowCount.lean:122 | entropy |
| `Salt.Entropy.Chowla.primeWindow_sum_inv_ge` | Salt/Entropy/Chowla/WindowMertensLower.lean:56 | entropy |
| `entropy_liouvilleWindow_le` | Salt/Entropy/Chowla/Windows.lean:62 | characters, entropy |
| `liouvilleWindow_block` | Salt/Entropy/Chowla/Windows.lean:87 | characters, entropy |
| `ProbabilityTheory.cond_real_apply` | Salt/Entropy/Mathlib/ConditionalProbability.lean:33 | entropy |
| `ProbabilityTheory.Kernel.disintegration` | Salt/Entropy/Mathlib/KernelDisintegration.lean:101 | entropy |
| `ProbabilityTheory.Kernel.condKernel_prod_ae_eq` | Salt/Entropy/Mathlib/KernelDisintegration.lean:160 | entropy |
| `MeasureTheory.Measure.dirac_real_apply'` | Salt/Entropy/Mathlib/MeasureDirac.lean:27 | entropy |
| `MeasureTheory.Measure.prod_real_singleton` | Salt/Entropy/Mathlib/MeasureReal.lean:49 | entropy |
| `Set.ncard_singleton_inter'` | Salt/Entropy/Mathlib/SetCard.lean:30 | entropy |
| `Set.ncard_inter_singleton` | Salt/Entropy/Mathlib/SetCard.lean:34 | entropy |
| `ProbabilityTheory.uniformOn_real_singleton` | Salt/Entropy/Mathlib/UniformOn.lean:68 | entropy |
| `ProbabilityTheory.measureEntropy_dirac` | Salt/Entropy/Measure.lean:272 | entropy |
| `ProbabilityTheory.measureEntropy_le_log_card` | Salt/Entropy/Measure.lean:406 | entropy |
| `Salt.ExpSum.norm_eR` | Salt/ExpSum/Basic.lean:45 | exponential sums |
| `Salt.ExpSum.eR_mul_conj` | Salt/ExpSum/Basic.lean:60 | exponential sums |
| `Salt.ExpSum.weyl_vdC_sq` | Salt/ExpSum/Basic.lean:131 | exponential sums |
| `Salt.ExpSum.weyl_vdC_expSum` | Salt/ExpSum/Basic.lean:258 | exponential sums |
| `Salt.ExpSum.vdC_2nd_ZR` | Salt/ExpSum/DerivTest.lean:63 | exponential sums |
| `Salt.ExpSum.vdC_third_derivative` | Salt/ExpSum/DerivTest.lean:536 | exponential sums |
| `Salt.ExpSum.vdC_kth_derivative` | Salt/ExpSum/DerivTestK.lean:667 | exponential sums |
| `Salt.ExpSum.kusmin_landau` | Salt/ExpSum/Kusmin.lean:186 | exponential sums |
| `Salt.ExpSum.zeta_block_kusmin_prefix` | Salt/ExpSum/Strip.lean:48 | exponential sums |
| `Salt.ExpSum.isVdCBound_16` | Salt/ExpSum/Strip.lean:182 | exponential sums |
| `Salt.ExpSum.zeta_block_vdC_prefix` | Salt/ExpSum/Strip.lean:198 | exponential sums |
| `Salt.ExpSum.zeta_block_prefix_collapse` | Salt/ExpSum/Strip.lean:304 | exponential sums |
| `Salt.ExpSum.zeta_window_prefix` | Salt/ExpSum/Strip.lean:359 | exponential sums |
| `Salt.ExpSum.zeta_seam_prefix` | Salt/ExpSum/Strip.lean:497 | exponential sums |
| `Salt.ExpSum.zeta_patch_prefix` | Salt/ExpSum/Strip.lean:589 | exponential sums |
| `Salt.ExpSum.cpow_weight_split` | Salt/ExpSum/Strip.lean:679 | exponential sums |
| `Salt.ExpSum.abel_antitone_prefix` | Salt/ExpSum/Strip.lean:698 | exponential sums |
| `Salt.ExpSum.zeta_weighted_block` | Salt/ExpSum/Strip.lean:762 | exponential sums |
| `Salt.ExpSum.window_coverage` | Salt/ExpSum/Strip.lean:809 | exponential sums |
| `Salt.ExpSum.zeta_block_dispatch` | Salt/ExpSum/Strip.lean:839 | exponential sums |
| `Salt.ExpSum.dyadic_sum_split_gen` | Salt/ExpSum/Strip.lean:979 | exponential sums |
| `Salt.ExpSum.sum_Icc_rpow_neg_le'` | Salt/ExpSum/Strip.lean:994 | exponential sums |
| `Salt.ExpSum.sq_le_two_pow` | Salt/ExpSum/Strip.lean:1007 | exponential sums |
| `Salt.ExpSum.head_coeff_le` | Salt/ExpSum/Strip.lean:1020 | exponential sums |
| `Salt.ExpSum.zeta_ladder_bound` | Salt/ExpSum/Strip.lean:1068 | exponential sums |
| `Salt.ExpSum.m0_guard` | Salt/ExpSum/Strip.lean:1171 | exponential sums |
| `Salt.ExpSum.zeta_head_bound` | Salt/ExpSum/Strip.lean:1213 | exponential sums |
| `Salt.ExpSum.zeta_strip_family` | Salt/ExpSum/Strip.lean:1301 | zeros, exponential sums |
| `Salt.ExpSum.dk_eq_zero_of_diff_const` | Salt/ExpSum/Twist.lean:64 | exponential sums |
| `Salt.ExpSum.dk_affine` | Salt/ExpSum/Twist.lean:81 | exponential sums |
| `Salt.ExpSum.dk_add_linear` | Salt/ExpSum/Twist.lean:89 | exponential sums |
| `Salt.ExpSum.dk_add_affine` | Salt/ExpSum/Twist.lean:98 | exponential sums |
| `Salt.ExpSum.dk_signed_add_linear` | Salt/ExpSum/Twist.lean:118 | exponential sums |
| `Salt.ExpSum.dk_window_affine_iff` | Salt/ExpSum/Twist.lean:131 | exponential sums |
| `Salt.ExpSum.isVdCBound_16_affine` | Salt/ExpSum/Twist.lean:158 | exponential sums |
| `Salt.ExpSum.zeta_dk_window_twist` | Salt/ExpSum/Twist.lean:175 | exponential sums |
| `Salt.ExpSum.zeta_block_vdC_prefix_twist` | Salt/ExpSum/TwistStrip.lean:72 | exponential sums |
| `Salt.ExpSum.zeta_block_prefix_collapse_twist` | Salt/ExpSum/TwistStrip.lean:180 | exponential sums |
| `Salt.ExpSum.zeta_window_prefix_twist` | Salt/ExpSum/TwistStrip.lean:235 | exponential sums |
| `Salt.ExpSum.zeta_seam_prefix_twist` | Salt/ExpSum/TwistStrip.lean:372 | exponential sums |
| `Salt.ExpSum.zeta_patch_prefix_twist` | Salt/ExpSum/TwistStrip.lean:462 | exponential sums |
| `Salt.ExpSum.zeta_lowt_prefix_twist` | Salt/ExpSum/TwistStrip.lean:555 | exponential sums |
| `Salt.ExpSum.vdC_second_derivative` | Salt/ExpSum/VdCorput2.lean:145 | exponential sums |
| `Salt.ExpSum.zeta_block_window` | Salt/ExpSum/Window.lean:53 | exponential sums |
| `Salt.ExpSum.zeta_block_window_meet` | Salt/ExpSum/Window.lean:201 | exponential sums |
| `Salt.ExpSum.zeta_block_window_three` | Salt/ExpSum/Window.lean:218 | exponential sums |
| `Salt.ExpSum.norm_zeta_sub_approx_le` | Salt/ExpSum/ZetaApprox.lean:542 | zeros, exponential sums |
| `Salt.ExpSum.zeta_growth_strip` | Salt/ExpSum/ZetaApprox.lean:562 | zeros, exponential sums |
| `Salt.ExpSum.zeta_block_vdC` | Salt/ExpSum/ZetaBlock.lean:291 | zeros, exponential sums |
| `Salt.ExpSum.zeta_block_bound` | Salt/ExpSum/ZetaBlock.lean:367 | zeros, exponential sums |
| `Salt.ExpSum.zeta_dyadic_assembly` | Salt/ExpSum/ZetaGrowth.lean:141 | zeros, exponential sums |
| `Salt.ExpSum.zeta_partial_growth` | Salt/ExpSum/ZetaGrowth.lean:199 | zeros, exponential sums |
| `Salt.ExpSum.zeta_block_kusmin` | Salt/ExpSum/ZetaGrowth.lean:278 | zeros, exponential sums |
| `Salt.Fulcrum.fulcrum_zero_real` | Salt/Fulcrum/Basic.lean:93 | characters |
| `Salt.Fulcrum.fulcrum_zero_real_zfr` | Salt/Fulcrum/Basic.lean:170 | characters |
| `Salt.Fulcrum.zero_free_region_all_numeral` | Salt/Fulcrum/CZeroNumeral.lean:387 | zeros, characters |
| `Salt.Fulcrum.fulcrum_zero_real_numeral` | Salt/Fulcrum/CZeroNumeral.lean:427 | zeros, characters |
| `Salt.Fulcrum.chen_omega_prod_le_three` | Salt/Fulcrum/ChenCorollary.lean:34 | other |
| `Salt.Fulcrum.siegel_zeros_isolated_below` | Salt/Fulcrum/Gadget.lean:93 | characters |
| `Salt.Goldbach.gold_A1_lower` | Salt/Goldbach/A1.lean:191 | sieves |
| `Salt.Goldbach.goldBVSum` | Salt/Goldbach/A1.lean:314 | sieves |
| `Salt.Goldbach.W_goldA1_ge` | Salt/Goldbach/A1.lean:365 | sieves |
| `Salt.Goldbach.gold_A1_lower_W` | Salt/Goldbach/A1W.lean:216 | sieves |
| `Salt.Goldbach.goldRosserRemainderW_le_split` | Salt/Goldbach/A1W.lean:318 | sieves |
| `Salt.Goldbach.goldBVSum_W` | Salt/Goldbach/A1W.lean:354 | sieves |
| `Salt.Goldbach.goldApSumW_eq_psiAP` | Salt/Goldbach/A2W.lean:95 | sieves |
| `Salt.Goldbach.goldA2W_rem_eq` | Salt/Goldbach/A2W.lean:215 | sieves |
| `Salt.Goldbach.goldRosserRemainderW2_le_split` | Salt/Goldbach/A2W.lean:351 | sieves |
| `Salt.Goldbach.goldA2_hBVagg_W` | Salt/Goldbach/A2W.lean:407 | sieves |
| `Salt.Goldbach.gold_log_absorb` | Salt/Goldbach/Agg.lean:52 | sieves |
| `Salt.Goldbach.gold_hSum_at_op` | Salt/Goldbach/Agg.lean:77 | sieves |
| `Salt.Goldbach.gold_mainA3_of_block_remainders_W` | Salt/Goldbach/Agg2.lean:53 | sieves |
| `Salt.Goldbach.gold_band_hsym_slot_full` | Salt/Goldbach/Asm.lean:133 | sieves |
| `Salt.Goldbach.gold_hBVblocksW_final` | Salt/Goldbach/Asm2.lean:33 | sieves |
| `Salt.Goldbach.gold_hBVblocksW_at_op_closed` | Salt/Goldbach/Asm3.lean:466 | sieves |
| `Salt.Goldbach.goldbach_of_hypotheses_W` | Salt/Goldbach/Asm4.lean:355 | sieves |
| `Salt.Goldbach.goldTriplePrimeSumW_le_sifted` | Salt/Goldbach/Asm5.lean:34 | sieves |
| `Salt.Goldbach.gold_hA2_bundle` | Salt/Goldbach/Asm5.lean:159 | sieves |
| `Salt.Goldbach.gold_hA3_bundle` | Salt/Goldbach/Asm5.lean:188 | sieves |
| `Salt.Goldbach.gold_hA1_bundle` | Salt/Goldbach/Asm6.lean:86 | sieves |
| `Salt.Goldbach.chen_goldbach_of_ledger` | Salt/Goldbach/Asm6.lean:123 | sieves |
| `Salt.Goldbach.gold_dvd_sub_of_resG` | Salt/Goldbach/Band.lean:61 | sieves |
| `Salt.Goldbach.gold_diag_residue_crumb` | Salt/Goldbach/Band.lean:78 | sieves |
| `Salt.Goldbach.gold_band_low_vanish` | Salt/Goldbach/BandClose.lean:83 | sieves |
| `Salt.Goldbach.gold_band_sym_vanish` | Salt/Goldbach/BandClose.lean:100 | sieves |
| `Salt.Goldbach.gold_band_low_kp_floor` | Salt/Goldbach/BandClose.lean:115 | sieves |
| `Salt.Goldbach.gold_band_sym_kp_floor` | Salt/Goldbach/BandClose.lean:123 | sieves |
| `Salt.Goldbach.gold_band_geoN_inputs` | Salt/Goldbach/BandClose.lean:151 | sieves |
| `Salt.Goldbach.gold_band_survsum_geoN_floored` | Salt/Goldbach/BandClose.lean:266 | sieves |
| `Salt.Goldbach.gold_hSum_geo_band` | Salt/Goldbach/BandClose2.lean:51 | sieves |
| `Salt.Goldbach.gold_band_price_sym` | Salt/Goldbach/BandEng.lean:67 | sieves |
| `Salt.Goldbach.gold_band_price_low` | Salt/Goldbach/BandEng.lean:98 | sieves |
| `Salt.Goldbach.gold_hdiffK_sym_discharge` | Salt/Goldbach/BandEng.lean:134 | sieves |
| `Salt.Goldbach.gold_hdiffK_low_discharge` | Salt/Goldbach/BandEng.lean:158 | sieves |
| `Salt.Goldbach.gold_band_annulus_absorb` | Salt/Goldbach/BandEng.lean:188 | sieves |
| `Salt.Goldbach.gold_band_hsym_slot` | Salt/Goldbach/BandEng.lean:229 | sieves |
| `Salt.Goldbach.goldLowRect_windowDisc_eq` | Salt/Goldbach/BandIdent.lean:220 | sieves |
| `Salt.Goldbach.goldLowRect_eq` | Salt/Goldbach/BandIdent.lean:323 | sieves |
| `Salt.Goldbach.goldBandLowDisc_eq_carrier` | Salt/Goldbach/BandIdent.lean:347 | sieves |
| `Salt.Goldbach.goldBandLowDisc_le_annulus_sum` | Salt/Goldbach/BandIdent.lean:394 | sieves |
| `Salt.Goldbach.goldBandDiagCount_le` | Salt/Goldbach/BandIdent.lean:494 | sieves |
| `Salt.Goldbach.goldSymCard_two_mul` | Salt/Goldbach/BandIdent.lean:546 | sieves |
| `Salt.Goldbach.goldBandCard_split` | Salt/Goldbach/BandIdent.lean:589 | sieves |
| `Salt.Goldbach.goldBandDiscW_eq_three` | Salt/Goldbach/BandIdent.lean:653 | sieves |
| `Salt.Goldbach.goldSymRect_windowDisc_eq` | Salt/Goldbach/BandIdent.lean:833 | sieves |
| `Salt.Goldbach.goldSymRect_eq` | Salt/Goldbach/BandIdent.lean:900 | sieves |
| `Salt.Goldbach.goldBandSymRectDisc_le_annulus_sum` | Salt/Goldbach/BandIdent.lean:933 | sieves |
| `Salt.Goldbach.gold_band_geo_absorb` | Salt/Goldbach/BandPrice.lean:47 | sieves |
| `Salt.Goldbach.gold_band_hpriceLow` | Salt/Goldbach/BandPrice.lean:134 | sieves |
| `Salt.Goldbach.gold_band_hlow` | Salt/Goldbach/BandPrice.lean:162 | sieves |
| `Salt.Goldbach.gold_band_sym_hiX` | Salt/Goldbach/BandPrice.lean:193 | sieves |
| `Salt.Goldbach.gold_band_hpriceSym` | Salt/Goldbach/BandPrice.lean:235 | sieves |
| `Salt.Goldbach.gold_band_hsym` | Salt/Goldbach/BandPrice.lean:263 | sieves |
| `Salt.Goldbach.gold_hBVblocksW_at_op_band` | Salt/Goldbach/BandPrice2.lean:41 | sieves |
| `Salt.Goldbach.gold_btail_slot_firing_le` | Salt/Goldbach/BandPrice2.lean:123 | sieves |
| `Salt.Goldbach.gold_band_wide_price_at_op` | Salt/Goldbach/BandRows.lean:98 | sieves |
| `Salt.Goldbach.gold_crumb_triple_tower` | Salt/Goldbach/BandRows2.lean:52 | sieves |
| `Salt.Goldbach.gold_box_crumb_tower` | Salt/Goldbach/BandRows2.lean:314 | sieves |
| `Salt.Goldbach.gold_band_crumb_tower` | Salt/Goldbach/BandRows2.lean:335 | sieves |
| `Salt.Goldbach.gold_crumb_tower_close` | Salt/Goldbach/BandRows2.lean:379 | sieves |
| `Salt.Goldbach.gold_d0_window_band` | Salt/Goldbach/BandWin.lean:56 | sieves |
| `Salt.Goldbach.gold_box_price_engine_at_band` | Salt/Goldbach/BandWin.lean:274 | sieves |
| `Salt.Goldbach.gold_band_box_kerr` | Salt/Goldbach/BandWin.lean:362 | sieves |
| `Salt.Goldbach.gold_band_survsum_geoN` | Salt/Goldbach/BandWin.lean:451 | sieves |
| `Salt.Goldbach.gold_band_geo_absorb_tail` | Salt/Goldbach/BandWin2.lean:148 | sieves |
| `Salt.Goldbach.gold_band_hlow_tail` | Salt/Goldbach/BandWin2.lean:207 | sieves |
| `Salt.Goldbach.gold_band_hsym_tail` | Salt/Goldbach/BandWin2.lean:232 | sieves |
| `Salt.Goldbach.gold_box_hcoupG` | Salt/Goldbach/BoxRows.lean:86 | sieves |
| `Salt.Goldbach.gold_box_carrier_vanish` | Salt/Goldbach/BoxRows.lean:132 | sieves |
| `Salt.Goldbach.gold_box_price_vanish` | Salt/Goldbach/BoxRows.lean:147 | sieves |
| `Salt.Goldbach.gold_box_XM_scale` | Salt/Goldbach/BoxRows.lean:182 | sieves |
| `Salt.Goldbach.gold_box_XMhi` | Salt/Goldbach/BoxRows.lean:212 | sieves |
| `Salt.Goldbach.gold_box_price_row_dead` | Salt/Goldbach/BoxRows2.lean:64 | sieves |
| `Salt.Goldbach.gold_box_price_live_kerr` | Salt/Goldbach/BoxRows3.lean:48 | sieves |
| `Salt.Goldbach.gold_box_price_dead_kerr` | Salt/Goldbach/BoxRows3.lean:143 | sieves |
| `Salt.Goldbach.gold_hSum_discharged` | Salt/Goldbach/BoxRows3.lean:172 | sieves |
| `Salt.Goldbach.chen_goldbach` | Salt/Goldbach/ChenGoldbach.lean:41 | sieves |
| `Salt.Goldbach.gold_band_hlow_wide_at_op` | Salt/Goldbach/Close.lean:54 | sieves |
| `Salt.Goldbach.gold_band_hsym_wide_at_op` | Salt/Goldbach/Close.lean:131 | sieves |
| `Salt.Goldbach.gold_band_hlow_slot_at_op` | Salt/Goldbach/Close.lean:217 | sieves |
| `Salt.Goldbach.goldCard_le_pairSum` | Salt/Goldbach/Count.lean:94 | sieves |
| `Salt.Goldbach.goldTripleSum_le_pairSum` | Salt/Goldbach/Count.lean:144 | sieves |
| `Salt.Goldbach.goldCount_bound_uniformK` | Salt/Goldbach/CountFinal.lean:67 | sieves |
| `Salt.Goldbach.goldTripleSum_le_cbar_final` | Salt/Goldbach/CountFinal.lean:147 | sieves |
| `Salt.Goldbach.gold_d0_window_annulus` | Salt/Goldbach/D0Win.lean:63 | sieves |
| `Salt.Goldbach.gold_kfloor_live_annulus` | Salt/Goldbach/D0Win.lean:283 | sieves |
| `Salt.Goldbach.gold_box_price_engine_at_live_annulus` | Salt/Goldbach/D0Win.lean:354 | sieves |
| `Salt.Goldbach.gold_live_annulus_lower` | Salt/Goldbach/D0Win2.lean:59 | sieves |
| `Salt.Goldbach.gold_kfloor_live_z` | Salt/Goldbach/D0Win2.lean:114 | sieves |
| `Salt.Goldbach.gold_d0_window_z` | Salt/Goldbach/D0Win2.lean:186 | sieves |
| `Salt.Goldbach.gold_box_price_engine_at_live_z` | Salt/Goldbach/D0Win2.lean:398 | sieves |
| `Salt.Goldbach.gold_dsplit_head_cap_below_conductor` | Salt/Goldbach/DSplit.lean:101 | sieves |
| `Salt.Goldbach.goldPs_squarefree` | Salt/Goldbach/Density.lean:74 | sieves |
| `Salt.Goldbach.goldPs_primeFactors` | Salt/Goldbach/Density.lean:80 | sieves |
| `Salt.Goldbach.goldPs_coprime_N` | Salt/Goldbach/Density.lean:88 | sieves |
| `Salt.Goldbach.coprime_of_dvd_goldPs` | Salt/Goldbach/Density.lean:98 | sieves |
| `Salt.Goldbach.goldPs_odd` | Salt/Goldbach/Density.lean:104 | sieves |
| `Salt.Goldbach.goldPs_primeFactors_facts` | Salt/Goldbach/Density.lean:113 | sieves |
| `Salt.Goldbach.coprime_mod_of_coprime` | Salt/Goldbach/Density.lean:126 | sieves |
| `Salt.Goldbach.crtClass_coprime_gold` | Salt/Goldbach/Density.lean:135 | sieves |
| `Salt.Goldbach.card_primesInWindow_dvd_le` | Salt/Goldbach/Density.lean:157 | sieves |
| `Salt.Goldbach.punctured_correction_le` | Salt/Goldbach/Density.lean:191 | sieves |
| `Salt.Goldbach.window_prod_upper_punctured` | Salt/Goldbach/Density.lean:238 | sieves |
| `Salt.Goldbach.exp_correction_le` | Salt/Goldbach/Density.lean:296 | sieves |
| `Salt.Goldbach.exp_correction_le_op` | Salt/Goldbach/Density.lean:320 | sieves |
| `Salt.Goldbach.window_prod_upper_punctured_folded` | Salt/Goldbach/Density.lean:334 | sieves |
| `Salt.Goldbach.goldPs_hnu` | Salt/Goldbach/Density.lean:357 | sieves |
| `Salt.Goldbach.apDiscBilinCutoff_symm` | Salt/Goldbach/Final.lean:56 | sieves |
| `Salt.Goldbach.gold_box_disc_trivial_min` | Salt/Goldbach/Final.lean:94 | sieves |
| `Salt.Goldbach.gold_box_tail_min` | Salt/Goldbach/Final.lean:117 | sieves |
| `Salt.Goldbach.gold_box_price_tail_min` | Salt/Goldbach/Final.lean:204 | sieves |
| `Salt.Goldbach.min_le_sqrt_mul` | Salt/Goldbach/Final.lean:231 | sieves |
| `Salt.Goldbach.gold_box_hprice_at_min` | Salt/Goldbach/Final.lean:267 | sieves |
| `Salt.Goldbach.gold_box_hbox_at_min` | Salt/Goldbach/Final.lean:325 | sieves |
| `Salt.Goldbach.gold_hBVblocksW_at_op` | Salt/Goldbach/Final2.lean:55 | sieves |
| `Salt.Goldbach.gold_boxPriceKerr_geo` | Salt/Goldbach/GeoSum.lean:63 | sieves |
| `Salt.Goldbach.gold_goldCut_geosum` | Salt/Goldbach/GeoSum.lean:173 | sieves |
| `Salt.Goldbach.gold_hSum_geo` | Salt/Goldbach/GeoSum.lean:203 | sieves |
| `Salt.Goldbach.gold_boxPriceKerr_geoN` | Salt/Goldbach/GeoSum2.lean:52 | sieves |
| `Salt.Goldbach.gold_box_hprice_at` | Salt/Goldbach/Glue.lean:69 | sieves |
| `Salt.Goldbach.gold_box_hbox_at` | Salt/Goldbach/Glue.lean:131 | sieves |
| `Salt.Goldbach.gold_boxPriceKerrY_geoN` | Salt/Goldbach/KerrY.lean:216 | sieves |
| `Salt.Goldbach.gold_kerrY_hbox_geoN` | Salt/Goldbach/KerrY.lean:253 | sieves |
| `Salt.Goldbach.gold_kerrY_engine` | Salt/Goldbach/KerrY.lean:293 | sieves |
| `Salt.Goldbach.gold_kerrY2_engine` | Salt/Goldbach/KerrY2.lean:133 | sieves |
| `Salt.Goldbach.gold_kerrY2_geoN` | Salt/Goldbach/KerrY2.lean:635 | sieves |
| `Salt.Goldbach.gold_hmid_discharge` | Salt/Goldbach/KerrY2.lean:765 | sieves |
| `Salt.Goldbach.gold_W_ge_twin` | Salt/Goldbach/Ledger.lean:234 | sieves |
| `Salt.Goldbach.gold_hWy_at_op` | Salt/Goldbach/Ledger.lean:400 | sieves |
| `Salt.Goldbach.gold_hcertA1_at_op` | Salt/Goldbach/Ledger2.lean:34 | sieves |
| `Salt.Goldbach.gold_hcertA3_at_op` | Salt/Goldbach/Ledger2.lean:50 | sieves |
| `Salt.Goldbach.gold_hcertA2_at_op` | Salt/Goldbach/Ledger2.lean:64 | sieves |
| `Salt.Goldbach.gold_hL_bundle` | Salt/Goldbach/Ledger3.lean:36 | sieves |
| `Salt.Goldbach.gold_factors_ge_z_of_sift` | Salt/Goldbach/Omega.lean:72 | sieves |
| `Salt.Goldbach.goldA2W_hcoef` | Salt/Goldbach/Omega.lean:170 | sieves |
| `Salt.Goldbach.gold_a12_hBV_A2` | Salt/Goldbach/Omega.lean:188 | sieves |
| `Salt.Goldbach.gold_op_Yhalf` | Salt/Goldbach/Omega.lean:357 | sieves |
| `Salt.Goldbach.goldOpP_pfull` | Salt/Goldbach/Omega.lean:391 | sieves |
| `Salt.Goldbach.gold_a12_hA2` | Salt/Goldbach/Omega.lean:405 | sieves |
| `Salt.Goldbach.gold_opQ_squarefree` | Salt/Goldbach/Op.lean:65 | sieves |
| `Salt.Goldbach.gold_opQ_even` | Salt/Goldbach/Op.lean:71 | sieves |
| `Salt.Goldbach.gold_opQ_coprime_P` | Salt/Goldbach/Op.lean:122 | sieves |
| `Salt.Goldbach.gold_op_Zpow9` | Salt/Goldbach/Op.lean:151 | sieves |
| `Salt.Goldbach.gold_op_residue` | Salt/Goldbach/Op.lean:186 | sieves |
| `Salt.Goldbach.gold_a12_hBV_A1` | Salt/Goldbach/Op.lean:200 | sieves |
| `Salt.Goldbach.gold_a12_hA1` | Salt/Goldbach/Op.lean:270 | sieves |
| `Salt.Goldbach.gold_op_count_rows` | Salt/Goldbach/Op.lean:315 | sieves |
| `Salt.Goldbach.gold_op_hCE` | Salt/Goldbach/Op.lean:377 | sieves |
| `Salt.Goldbach.gold_hcount_seam` | Salt/Goldbach/Op2.lean:60 | sieves |
| `Salt.Goldbach.gold_box_live_ratios` | Salt/Goldbach/OpPlumb.lean:45 | sieves |
| `Salt.Goldbach.gold_box_hbox_geoN` | Salt/Goldbach/OpPlumb.lean:148 | sieves |
| `Salt.Goldbach.gold_box_price_wide_or_dead` | Salt/Goldbach/OpPlumb.lean:174 | sieves |
| `Salt.Goldbach.gold_box_hprice_op` | Salt/Goldbach/OpPlumb.lean:220 | sieves |
| `Salt.Goldbach.sum_goldDiagTotal_le_goldDiagPairSet` | Salt/Goldbach/PDiag.lean:97 | sieves |
| `Salt.Goldbach.goldDiagPairSet_card_le` | Salt/Goldbach/PDiag.lean:139 | sieves |
| `Salt.Goldbach.gold_diagAggW_le_honest` | Salt/Goldbach/PDiag.lean:178 | sieves |
| `Salt.Goldbach.gold_PloW_honest` | Salt/Goldbach/PDiag.lean:399 | sieves |
| `Salt.Goldbach.gold_hBVblocksW_discharge'` | Salt/Goldbach/PDiag.lean:502 | sieves |
| `Salt.Goldbach.goldPerPair_pi_upper` | Salt/Goldbach/PiUpper.lean:373 | sieves |
| `Salt.Goldbach.gold_crtClassG_coprime_of_mem` | Salt/Goldbach/Price.lean:60 | sieves |
| `Salt.Goldbach.gold_box_price_engine` | Salt/Goldbach/Price.lean:96 | sieves |
| `Salt.Goldbach.gold_tower_budget` | Salt/Goldbach/PriceClose.lean:50 | sieves |
| `Salt.Goldbach.gold_hNum_close_of_tower` | Salt/Goldbach/PriceClose.lean:58 | sieves |
| `Salt.Goldbach.gold_mainA3_at_op` | Salt/Goldbach/PriceClose.lean:78 | sieves |
| `Salt.Goldbach.exists_crt_finset` | Salt/Goldbach/Residue.lean:42 | sieves |
| `Salt.Goldbach.goldbach_residue_witness` | Salt/Goldbach/Residue.lean:77 | sieves |
| `Salt.Goldbach.crtClassG_modEq_left` | Salt/Goldbach/Residue.lean:129 | sieves |
| `Salt.Goldbach.crtClassG_modEq_right` | Salt/Goldbach/Residue.lean:135 | sieves |
| `Salt.Goldbach.crtClassG_coprime` | Salt/Goldbach/Residue.lean:144 | sieves |
| `Salt.Goldbach.crt_class_coprimeG` | Salt/Goldbach/Residue.lean:170 | sieves |
| `Salt.Goldbach.gold_op_scales` | Salt/Goldbach/RowsLive.lean:71 | sieves |
| `Salt.Goldbach.gold_box_zx_rows` | Salt/Goldbach/RowsLive.lean:143 | sieves |
| `Salt.Goldbach.gold_box_Xfloor` | Salt/Goldbach/RowsLive.lean:265 | sieves |
| `Salt.Goldbach.gold_box_wge` | Salt/Goldbach/RowsLive.lean:280 | sieves |
| `Salt.Goldbach.gold_box_Mfloor` | Salt/Goldbach/RowsLive.lean:313 | sieves |
| `Salt.Goldbach.gold_box_rows_at_op` | Salt/Goldbach/RowsLive.lean:348 | sieves |
| `Salt.Goldbach.gold_box_rows_wide` | Salt/Goldbach/RowsWide.lean:108 | sieves |
| `Salt.Goldbach.goldBlockResCountM_eq_sum_pieces` | Salt/Goldbach/SW2.lean:84 | sieves |
| `Salt.Goldbach.gold_hBlockW_of_window_prices` | Salt/Goldbach/SW2.lean:253 | sieves |
| `Salt.Goldbach.gold_hNum_at_opW` | Salt/Goldbach/SW2.lean:336 | sieves |
| `Salt.Goldbach.gold_PloW_sym_of_box_disc` | Salt/Goldbach/SW2.lean:387 | sieves |
| `Salt.Goldbach.gold_PloW_low_of_box_disc` | Salt/Goldbach/SW2.lean:424 | sieves |
| `Salt.Goldbach.gold_bandDiscW_le_three_pieces_diag` | Salt/Goldbach/SW2.lean:475 | sieves |
| `Salt.Goldbach.gold_band_low_survsum_discharge` | Salt/Goldbach/Surv.lean:61 | sieves |
| `Salt.Goldbach.gold_band_sym_survsum_discharge` | Salt/Goldbach/Surv.lean:85 | sieves |
| `Salt.Goldbach.gold_band_btail_slot_firing_le` | Salt/Goldbach/Surv.lean:158 | sieves |
| `Salt.Goldbach.gold_band_hlow_tail_discharge` | Salt/Goldbach/Surv.lean:232 | sieves |
| `Salt.Goldbach.gold_band_hsym_tail_discharge` | Salt/Goldbach/Surv.lean:259 | sieves |
| `Salt.Goldbach.gold_switch_upper_B` | Salt/Goldbach/Switch.lean:277 | sieves |
| `Salt.Goldbach.gold_block_switch_upper_B_W` | Salt/Goldbach/Switch.lean:520 | sieves |
| `Salt.Goldbach.gold_mainA3_of_hBVswitch` | Salt/Goldbach/Switch.lean:608 | sieves |
| `Salt.Goldbach.gold_switch_coprime_N` | Salt/Goldbach/SwitchBV.lean:49 | sieves |
| `Salt.Goldbach.goldSwitchSieve_multSum_eq_apCount` | Salt/Goldbach/SwitchBV.lean:119 | sieves |
| `Salt.Goldbach.norm_goldSemiprimeBlockInd_le_one` | Salt/Goldbach/SwitchBV.lean:150 | sieves |
| `Salt.Goldbach.goldSwitchSieve_rem_split` | Salt/Goldbach/SwitchBV.lean:184 | sieves |
| `Salt.Goldbach.gold_hBVswitch_of_generalBV` | Salt/Goldbach/SwitchBV.lean:239 | sieves |
| `Salt.Goldbach.gold_nonunit_forces_fst_dvd` | Salt/Goldbach/SwitchBV.lean:257 | sieves |
| `Salt.Goldbach.gold_memClassG` | Salt/Goldbach/SwitchBV.lean:311 | sieves |
| `Salt.Goldbach.goldBlockMultSumW_eq_apCount` | Salt/Goldbach/SwitchBV.lean:385 | sieves |
| `Salt.Goldbach.goldBlockSwitchSieveW_rem_split` | Salt/Goldbach/SwitchBV.lean:473 | sieves |
| `Salt.Goldbach.gold_hBVblocksW_of_generalBV` | Salt/Goldbach/SwitchBV.lean:544 | sieves |
| `Salt.Goldbach.gold_hCE_at_op` | Salt/Goldbach/SwitchBV.lean:568 | sieves |
| `Salt.Goldbach.gold_box_disc_trivial` | Salt/Goldbach/Tail.lean:225 | sieves |
| `Salt.Goldbach.gold_box_tail_le` | Salt/Goldbach/Tail.lean:266 | sieves |
| `Salt.Goldbach.gold_box_carrier_tail` | Salt/Goldbach/Tail2.lean:57 | sieves |
| `Salt.Goldbach.gold_box_price_tail` | Salt/Goldbach/Tail2.lean:92 | sieves |
| `Salt.Goldbach.window_two_thirds_lt` | Salt/Goldbach/WeightWindow.lean:46 | sieves |
| `Salt.Goldbach.card_window_dvd_le` | Salt/Goldbach/WeightWindow.lean:65 | sieves |
| `Salt.Goldbach.stripSum_le` | Salt/Goldbach/WeightWindow.lean:97 | sieves |
| `Salt.Goldbach.goldBlockBox_windowed_pair_card` | Salt/Goldbach/WindowSW.lean:146 | sieves |
| `Salt.Goldbach.goldBlockBox_windowDisc_eq_res` | Salt/Goldbach/WindowSW.lean:267 | sieves |
| `Salt.Goldbach.goldBlockBox_windowDisc_eq_res_annulus` | Salt/Goldbach/WindowSW.lean:359 | sieves |
| `Salt.Goldbach.goldWindowDisc_le_annulus_sum` | Salt/Goldbach/WindowSW.lean:384 | sieves |
| `Salt.Goldbach.goldBlockBoxHonestDisc_eq_carrier` | Salt/Goldbach/WindowSW.lean:427 | sieves |
| `Salt.Goldbach.goldBoxHonestDisc_le_annulus_sum` | Salt/Goldbach/WindowSW.lean:477 | sieves |
| `Salt.HB.chiRe_eq_one_or_neg_one_or_zero` | Salt/HB/CharTrio.lean:72 | characters |
| `Salt.HB.chiRe_eq_zero_iff_map_eq_zero` | Salt/HB/CharTrio.lean:81 | characters |
| `Salt.HB.chiRe_eq_zero_iff_not_coprime` | Salt/HB/CharTrio.lean:95 | characters |
| `Salt.HB.chiRe_prime_eq_zero_iff_dvd` | Salt/HB/CharTrio.lean:101 | characters |
| `Salt.HB.hb_hchi01` | Salt/HB/CharTrio.lean:109 | characters |
| `Salt.HB.hb_hchi0` | Salt/HB/CharTrio.lean:115 | characters |
| `Salt.HB.prod_one_sub_chiRe_div_Pz_pos` | Salt/HB/CharTrio.lean:132 | characters |
| `Salt.HB.hbL1_pos` | Salt/HB/CharTrio.lean:136 | characters |
| `Salt.HB.Pz_eq_union_windowPrimes` | Salt/HB/CharTrio.lean:145 | characters |
| `Salt.HB.Pz_disjoint_windowPrimes` | Salt/HB/CharTrio.lean:158 | characters |
| `Salt.HB.hbEulerProdBelow_split` | Salt/HB/CharTrio.lean:169 | characters |
| `Salt.HB.tendsto_hbEulerProdBelow_hbL1` | Salt/HB/CharTrio.lean:181 | characters |
| `Salt.HB.hbL1_eq_of_tendsto` | Salt/HB/CharTrio.lean:196 | characters |
| `Salt.HB.hbL1_split_indep` | Salt/HB/CharTrio.lean:204 | characters |
| `Salt.HB.hb_L2_at_split_point_char` | Salt/HB/CharTrio.lean:215 | characters |
| `Salt.HB.hb_L2_at_split_point_charTrio` | Salt/HB/CharTrio.lean:248 | characters |
| `Salt.HB.l2cWindow_coprime_hbP` | Salt/HB/CrownAssembly.lean:99 | characters |
| `Salt.HB.hbDataN8_S3_eq` | Salt/HB/CrownAssembly.lean:136 | characters |
| `Salt.HB.hbDataN8_sandwich` | Salt/HB/CrownAssembly.lean:149 | characters |
| `Salt.HB.deltaSum_nuG_eq` | Salt/HB/CrownAssembly.lean:233 | characters |
| `Salt.HB.deltaSum_nuG_nonneg` | Salt/HB/CrownAssembly.lean:265 | characters |
| `Salt.HB.lamSum_nuG_sub_W_bounds` | Salt/HB/CrownAssembly.lean:283 | sieves, characters |
| `Salt.HB.failSet_log_le` | Salt/HB/CrownAssembly.lean:1103 | characters |
| `Salt.HB.hbG_div_eq_nuG` | Salt/HB/CrownAssembly.lean:1208 | characters |
| `Salt.HB.n8ErrSum_le` | Salt/HB/CrownAssembly.lean:1232 | characters |
| `Salt.HB.hbS1_eq_W` | Salt/HB/CrownAssembly.lean:1732 | sieves, characters |
| `Salt.HB.l2cWindow_subset_honestWindow` | Salt/HB/CrownChain.lean:102 | characters |
| `Salt.HB.S1_l2cWindow_le_S1_Ioc` | Salt/HB/CrownChain.lean:115 | characters |
| `Salt.HB.S1_Ioc_sub_S1_l2cWindow_le` | Salt/HB/CrownChain.lean:182 | characters |
| `Salt.HB.S2_sub_S3_window_of_tau` | Salt/HB/CrownChain.lean:322 | characters |
| `Salt.HB.S2_sub_S3_l2cWindow` | Salt/HB/CrownChain.lean:420 | characters |
| `Salt.HB.hb_lemma4_l2cWindow` | Salt/HB/CrownChain.lean:461 | characters |
| `Salt.HB.pretenseSum_at_repulsion_floor` | Salt/HB/CrownChain.lean:519 | characters |
| `Salt.HB.dh_repulsion_tall_at` | Salt/HB/CrownTheorem1.lean:191 | characters |
| `Salt.HB.dh_spec` | Salt/HB/CrownTheorem1.lean:261 | characters |
| `Salt.HB.invSqC_spec` | Salt/HB/CrownTheorem1.lean:283 | characters |
| `Salt.HB.merC_spec` | Salt/HB/CrownTheorem1.lean:302 | characters |
| `Salt.HB.segC_spec` | Salt/HB/CrownTheorem1.lean:312 | characters |
| `Salt.HB.n9EllAt_two` | Salt/HB/CrownTheorem1.lean:340 | characters |
| `Salt.HB.n9E0B3_nonneg` | Salt/HB/CrownTheorem1.lean:413 | characters |
| `Salt.HB.hbZ_bounds` | Salt/HB/CrownTheorem1.lean:535 | characters |
| `Salt.HB.three_le_of_ne_one` | Salt/HB/CrownTheorem1.lean:890 | characters |
| `Salt.HB.dh_repulsion_tall_real` | Salt/HB/CrownTheorem1.lean:1047 | characters |
| `Salt.HB.neg_re_logDeriv_LFunction_ge` | Salt/HB/CrownTheorem1.lean:1804 | characters |
| `Salt.HB.neg_re_logDeriv_differenced_mult_ge` | Salt/HB/CrownTheorem1.lean:1816 | characters |
| `Salt.HB.card_divisors_le_rpow_explicit` | Salt/HB/CrownTheorem1.lean:4539 | characters |
| `Salt.HB.fulcrumQualityPoly_one_iff` | Salt/HB/CrownTheorem1.lean:6365 | characters |
| `Salt.HB.noSiegelZerosPoly_one_iff` | Salt/HB/CrownTheorem1.lean:6369 | characters |
| `Salt.HB.heathBrownDichotomyPoly_one_iff` | Salt/HB/CrownTheorem1.lean:6375 | characters |
| `Salt.HB.beta0_max_of_zero` | Salt/HB/CrownTheorem1.lean:6475 | characters |
| `Salt.HB.hbDataN8_S_eq_zero` | Salt/HB/CrownWireHB.lean:51 | characters |
| `Salt.HB.lamSum_S_eq_S3` | Salt/HB/CrownWireHB.lean:77 | characters |
| `Salt.HB.four_mul_add_one_mem_Ioc` | Salt/HB/CrownWireHB.lean:157 | characters |
| `Salt.HB.coprime_excPrimorial_of_odd` | Salt/HB/CrownWireHB.lean:169 | characters |
| `Salt.HB.hbDataHB_S3_le_S3_window` | Salt/HB/CrownWireHB.lean:204 | characters |
| `Salt.HB.hbS1_eq_W_HB` | Salt/HB/CrownWireHB.lean:245 | sieves, characters |
| `Salt.HB.twinPrimeConjecture_of_frequently_pos` | Salt/HB/DoorBridge.lean:67 | characters |
| `Salt.HB.twinWindow_two_mul_add_two` | Salt/HB/DoorBridge.lean:78 | characters |
| `Salt.HB.ppTail_le` | Salt/HB/DoorBridge.lean:175 | characters |
| `Salt.HB.S1_Ioc_le_p1PrimeSum_add_ppTail` | Salt/HB/DoorBridge.lean:264 | characters |
| `Salt.HB.twin_of_ppTail_lt_S1` | Salt/HB/DoorBridge.lean:310 | characters |
| `Salt.HB.twinPrimeConjecture_of_frequently_S1` | Salt/HB/DoorBridge.lean:329 | characters |
| `Salt.HB.factorization_two_le_three_of_isPrimitive` | Salt/HB/EstermannRoad.lean:46 | characters |
| `Salt.HB.norm_kloosterman_estermann_road_of_isPrimitive` | Salt/HB/EstermannRoad.lean:63 | characters |
| `Salt.HB.two_pow_totient_exceeds_estermann_at_nine` | Salt/HB/EstermannRoad.lean:85 | characters |
| `Salt.HB.sqrt_quad_of_threshold` | Salt/HB/HSigmaComp.lean:67 | characters |
| `Salt.HB.repulsion_floor_gives_hsigma` | Salt/HB/HSigmaComp.lean:104 | characters |
| `Salt.HB.hb_L1_one_sided_at_repulsion_floor` | Salt/HB/HSigmaComp.lean:170 | characters |
| `Salt.HB.hsigma_largeness_satisfiable` | Salt/HB/HSigmaComp.lean:213 | characters |
| `Salt.HB.EL_cJunk_bound` | Salt/HB/L2cELJunk.lean:336 | characters |
| `Salt.HB.ER_wJunk_bound` | Salt/HB/L2cELJunk.lean:385 | characters |
| `Salt.HB.EL_corners_bound` | Salt/HB/L2cELJunk.lean:647 | characters |
| `Salt.HB.EL_T1_bound` | Salt/HB/L2cELT1.lean:801 | characters |
| `Salt.HB.EL_T2_bound` | Salt/HB/L2cELT2.lean:1336 | characters |
| `Salt.HB.EL_T3F_bound` | Salt/HB/L2cELT3F.lean:672 | characters |
| `Salt.HB.pretenseSum_nonneg` | Salt/HB/L2cELTsw.lean:191 | characters |
| `Salt.HB.EL_Tsw_bound` | Salt/HB/L2cELTsw.lean:1021 | characters |
| `Salt.HB.ER_squarefull_junk` | Salt/HB/L2cER.lean:154 | characters |
| `Salt.HB.ER_T1'_bound_mixed` | Salt/HB/L2cERT1.lean:738 | characters |
| `Salt.HB.ER_T2'_bound` | Salt/HB/L2cERT2.lean:1054 | characters |
| `Salt.HB.ER_T3'_bound` | Salt/HB/L2cERT3.lean:481 | characters |
| `Salt.HB.ER_Tsw'_bound_of_count` | Salt/HB/L2cERTsw.lean:380 | characters |
| `Salt.HB.engineRoute_card_right` | Salt/HB/L2cEngineRoute.lean:189 | characters |
| `Salt.HB.ER_Tsw'_bound_unconditional` | Salt/HB/L2cEngineRoute.lean:409 | characters |
| `Salt.HB.cPairSum_bound_unconditional` | Salt/HB/L2cEngineRoute.lean:613 | characters |
| `Salt.HB.EL_evenCorner_bound` | Salt/HB/L2cEven.lean:677 | characters |
| `Salt.HB.hb_l2c_master_of_count` | Salt/HB/L2cMaster.lean:371 | characters |
| `Salt.HB.EL_uncov_bound_unconditional` | Salt/HB/L2cMasterUncond.lean:48 | characters |
| `Salt.HB.hb_l2c_master_unconditional` | Salt/HB/L2cMasterUncond.lean:85 | characters |
| `Salt.N7.norm_lem10ExpSum_le_card` | Salt/HB/Lemma10.lean:52 | characters, exponential sums |
| `Salt.N7.lem10ExpSum_attains_card` | Salt/HB/Lemma10.lean:65 | characters, exponential sums |
| `Salt.N7.card_le_of_mem_Ioc` | Salt/HB/Lemma10.lean:78 | characters |
| `Salt.N7.card_divisors_le_of_dvd` | Salt/HB/Lemma10.lean:114 | characters |
| `Salt.N7.divisor_triple_le_cube` | Salt/HB/Lemma10.lean:124 | characters |
| `Salt.N7.divisor_triple_attains_cube` | Salt/HB/Lemma10.lean:154 | characters |
| `Salt.N7.e_add_intCast` | Salt/HB/Lemma10Chain.lean:72 | characters |
| `Salt.N7.norm_e_sub_le` | Salt/HB/Lemma10Chain.lean:92 | characters |
| `Salt.N7.sum_Ioc_succ_top_int` | Salt/HB/Lemma10Chain.lean:115 | characters |
| `Salt.N7.sum_Ico_succ_top_int` | Salt/HB/Lemma10Chain.lean:125 | characters |
| `Salt.N7.sum_Ioc_abel_int_ico` | Salt/HB/Lemma10Chain.lean:136 | characters |
| `Salt.N7.sum_Ico_eq_sum_Ioc_pred` | Salt/HB/Lemma10Chain.lean:153 | characters |
| `Salt.N7.sum_Ioc_abel_int` | Salt/HB/Lemma10Chain.lean:169 | characters |
| `Salt.N7.lem10_abel_transfer` | Salt/HB/Lemma10Chain.lean:204 | characters, exponential sums |
| `Salt.N7.var_const` | Salt/HB/Lemma10Chain.lean:281 | characters |
| `Salt.N7.var_inv` | Salt/HB/Lemma10Chain.lean:300 | characters |
| `Salt.N7.stdAddChar_intCast_eq_e` | Salt/HB/Lemma10Chain.lean:371 | characters, exponential sums |
| `Salt.N7.isUnit_intCast_iff` | Salt/HB/Lemma10Chain.lean:382 | characters |
| `Salt.N7.klPhaseSum_eq_kloosterman` | Salt/HB/Lemma10Chain.lean:421 | characters, exponential sums |
| `Salt.N7.sum_zmod_val_eq_sum_range` | Salt/HB/Lemma10Chain.lean:545 | characters |
| `Salt.N7.sum_range_mul_mod` | Salt/HB/Lemma10Chain.lean:562 | characters |
| `Salt.N7.sum_Ico_reflect` | Salt/HB/Lemma10Chain.lean:578 | characters |
| `Salt.N7.gcd_natAbs_eq_of_dvd_sub` | Salt/HB/Lemma10Chain.lean:588 | characters |
| `Salt.N7.sqrt_gcd_mul_le` | Salt/HB/Lemma10Chain.lean:606 | characters |
| `Salt.N7.dist₁_shift_lower` | Salt/HB/Lemma10Chain.lean:631 | characters |
| `Salt.N7.sum_sqrt_gcd_min_le` | Salt/HB/Lemma10Chain.lean:675 | characters |
| `Salt.N7.klPhaseSum_bound` | Salt/HB/Lemma10Chain.lean:730 | characters |
| `Salt.N7.lem10_dyadic_bound` | Salt/HB/Lemma10Chain.lean:1012 | characters, exponential sums |
| `Salt.N7.e_neg_eq_conj` | Salt/HB/Lemma10Chain.lean:1259 | characters |
| `Salt.N7.norm_lem10ExpSumZ` | Salt/HB/Lemma10Seal.lean:92 | characters, exponential sums |
| `Salt.N7.head_reindex` | Salt/HB/Lemma10Seal.lean:110 | characters, exponential sums |
| `Salt.N7.sealK_ge_two` | Salt/HB/Lemma10Seal.lean:137 | characters |
| `Salt.N7.sealK_ge_rpow` | Salt/HB/Lemma10Seal.lean:141 | characters |
| `Salt.N7.sealK_le` | Salt/HB/Lemma10Seal.lean:150 | characters |
| `Salt.N7.log_Kk_le` | Salt/HB/Lemma10Seal.lean:179 | characters |
| `Salt.N7.t4_log_sealK_le` | Salt/HB/Lemma10Seal.lean:229 | characters |
| `Salt.N7.lem10PsiSum_le_fourier_split` | Salt/HB/Lemma10Seal.lean:367 | characters |
| `Salt.N7.lem10_m1_bound` | Salt/HB/Lemma10Seal.lean:415 | characters, exponential sums |
| `Salt.N7.klPhaseSum_bound_road` | Salt/HB/Lemma10Seal.lean:624 | characters |
| `Salt.N7.lem10_dyadic_bound_road` | Salt/HB/Lemma10Seal.lean:651 | characters, exponential sums |
| `Salt.N7.lem10_m1_bound_road` | Salt/HB/Lemma10Seal.lean:694 | characters, exponential sums |
| `Salt.N7.majorant_tail_le` | Salt/HB/Lemma10Seal.lean:849 | characters, exponential sums |
| `Salt.N7.weighted_dyadic_block_sum_le` | Salt/HB/Lemma10Seal.lean:877 | characters, exponential sums |
| `Salt.N7.majorant_m1_le` | Salt/HB/Lemma10Seal.lean:956 | characters, exponential sums |
| `Salt.N7.fourier_column_le` | Salt/HB/Lemma10Seal.lean:1060 | characters, exponential sums |
| `Salt.N7.majorant_head_le` | Salt/HB/Lemma10Seal.lean:1226 | characters, exponential sums |
| `Salt.N7.majorant_rangeA_le` | Salt/HB/Lemma10Seal.lean:1336 | characters, exponential sums |
| `Salt.N7.norm_majorantCoeff_neg` | Salt/HB/Lemma10Seal.lean:1409 | characters |
| `Salt.N7.majorant_tsum_split` | Salt/HB/Lemma10Seal.lean:1485 | characters, exponential sums |
| `Salt.N7.hb_lemma10` | Salt/HB/Lemma10Seal.lean:1559 | characters |
| `Salt.HB.repulsion_floor_gives_lemma3_binders` | Salt/HB/Lemma3Floor.lean:83 | characters |
| `Salt.N7.HBForms.alpha₁_ne_zero` | Salt/HB/Lemma5Bilinear.lean:86 | characters |
| `Salt.N7.HBForms.alpha₂_ne_zero` | Salt/HB/Lemma5Bilinear.lean:99 | characters |
| `Salt.N7.HBForms.two_le_α₁` | Salt/HB/Lemma5Bilinear.lean:112 | characters |
| `Salt.N7.HBForms.two_le_α₂` | Salt/HB/Lemma5Bilinear.lean:115 | characters |
| `Salt.N7.HBForms.one_le_β₁` | Salt/HB/Lemma5Bilinear.lean:119 | characters |
| `Salt.N7.HBForms.one_le_β₂` | Salt/HB/Lemma5Bilinear.lean:131 | characters |
| `Salt.N7.HBForms.one_le_l₁` | Salt/HB/Lemma5Bilinear.lean:146 | characters |
| `Salt.N7.HBForms.one_le_l₂` | Salt/HB/Lemma5Bilinear.lean:151 | characters |
| `Salt.N7.HBForms.odd_β₁` | Salt/HB/Lemma5Bilinear.lean:157 | characters |
| `Salt.N7.HBForms.odd_β₂` | Salt/HB/Lemma5Bilinear.lean:166 | characters |
| `Salt.N7.HBForms.odd_l₁` | Salt/HB/Lemma5Bilinear.lean:176 | characters |
| `Salt.N7.HBForms.odd_l₂` | Salt/HB/Lemma5Bilinear.lean:183 | characters |
| `Salt.N7.HBForms.coprime_l₁_α₁` | Salt/HB/Lemma5Bilinear.lean:191 | characters |
| `Salt.N7.HBForms.coprime_l₂_α₂` | Salt/HB/Lemma5Bilinear.lean:196 | characters |
| `Salt.N7.HBForms.l₁_mono` | Salt/HB/Lemma5Bilinear.lean:202 | characters |
| `Salt.N7.HBForms.l₂_mono` | Salt/HB/Lemma5Bilinear.lean:206 | characters |
| `Salt.N7.HBForms.coprime_l` | Salt/HB/Lemma5Bilinear.lean:215 | characters |
| `Salt.N7.HBForms.coprime_α_iff` | Salt/HB/Lemma5Bilinear.lean:238 | characters |
| `Salt.N7.bilinearS_eq_zero_of_not_coprime_q₁` | Salt/HB/Lemma5Bilinear.lean:318 | characters |
| `Salt.N7.bilinearS_eq_zero_of_not_coprime_q₂` | Salt/HB/Lemma5Bilinear.lean:325 | characters |
| `Salt.N7.bilinearS_eq_zero_of_not_coprime_α₁` | Salt/HB/Lemma5Bilinear.lean:334 | characters |
| `Salt.N7.bilinearS_eq_zero_of_not_coprime_α₂` | Salt/HB/Lemma5Bilinear.lean:343 | characters |
| `Salt.N7.bilinearS_eq_zero_of_not_coprime_δ` | Salt/HB/Lemma5Bilinear.lean:353 | characters |
| `Salt.N7.truncChiSum_eq_zero_of_le` | Salt/HB/Lemma5Bilinear.lean:365 | characters |
| `Salt.N7.bilinearS_eq_zero_of_le₁` | Salt/HB/Lemma5Bilinear.lean:373 | characters |
| `Salt.N7.bilinearS_eq_zero_of_le₂` | Salt/HB/Lemma5Bilinear.lean:382 | characters |
| `Salt.N7.coprime_hbQ_hbP` | Salt/HB/Lemma5Bilinear.lean:431 | characters |
| `Salt.N7.chiRe_finset_prod` | Salt/HB/Lemma5Bilinear.lean:445 | characters |
| `Salt.N7.chiRe_eq_one_of_dvd_hbP` | Salt/HB/Lemma5Bilinear.lean:454 | characters |
| `Salt.N7.integral_Ioi_ite_inv` | Salt/HB/Lemma5Bilinear.lean:469 | characters |
| `Salt.N7.integrable_term` | Salt/HB/Lemma5Bilinear.lean:489 | characters |
| `Salt.N7.integrableOn_truncChiSum_div` | Salt/HB/Lemma5Bilinear.lean:512 | characters |
| `Salt.N7.integral_Ioi_truncChiSum` | Salt/HB/Lemma5Bilinear.lean:527 | characters |
| `Salt.N7.hbQ_squarefree` | Salt/HB/Lemma5Bilinear.lean:561 | characters |
| `Salt.N7.hbQRad_squarefree` | Salt/HB/Lemma5Bilinear.lean:565 | characters |
| `Salt.N7.hbQRad_dvd_hbQ` | Salt/HB/Lemma5Bilinear.lean:569 | characters |
| `Salt.N7.prime_dvd_hbQ_iff` | Salt/HB/Lemma5Bilinear.lean:576 | characters |
| `Salt.N7.prime_dvd_hbQRad_iff` | Salt/HB/Lemma5Bilinear.lean:589 | characters |
| `Salt.N7.hbQRad_sq_dvd` | Salt/HB/Lemma5Bilinear.lean:605 | characters |
| `Salt.N7.filter_divisors_hbQ` | Salt/HB/Lemma5Bilinear.lean:629 | characters |
| `Salt.N7.hbQRad_eq_one_iff` | Salt/HB/Lemma5Bilinear.lean:652 | characters |
| `Salt.N7.moebius_step` | Salt/HB/Lemma5Bilinear.lean:669 | characters |
| `Salt.N7.chiRe_sq_of_dvd_hbQ` | Salt/HB/Lemma5Bilinear.lean:680 | characters |
| `Salt.N7.chiRe_sq_mul` | Salt/HB/Lemma5Bilinear.lean:694 | characters |
| `Salt.N7.LamStar_eq_moebius_hbQ` | Salt/HB/Lemma5Bilinear.lean:703 | characters |
| `Salt.N7.nested_antidiag` | Salt/HB/Lemma5Bilinear.lean:773 | characters |
| `Salt.N7.fiber_facts` | Salt/HB/Lemma5Bilinear.lean:785 | characters |
| `Salt.N7.second_reindex` | Salt/HB/Lemma5Bilinear.lean:825 | characters |
| `Salt.N7.fiber_reindex` | Salt/HB/Lemma5Bilinear.lean:849 | characters |
| `Salt.N7.hyperbola_fiber` | Salt/HB/Lemma5Bilinear.lean:922 | characters |
| `Salt.N7.LamPrime_eq_hyperbola` | Salt/HB/Lemma5Bilinear.lean:985 | characters |
| `Salt.N7.bilinear_double_integral` | Salt/HB/Lemma5Bilinear.lean:1028 | characters |
| `Salt.N7.inner_split` | Salt/HB/Lemma5Bilinear.lean:1068 | characters |
| `Salt.N7.hb_lemma9_inner` | Salt/HB/Lemma5Bilinear.lean:1105 | characters |
| `Salt.N7.hb_lemma9_general` | Salt/HB/Lemma5Bilinear.lean:1321 | characters |
| `Salt.N7.hb_lemma9_trunc` | Salt/HB/Lemma5Bilinear.lean:1362 | characters |
| `Salt.N7.hb_lemma9` | Salt/HB/Lemma5Bilinear.lean:1412 | characters |
| `Salt.N7.hb_lemma9_trunc_P` | Salt/HB/Lemma5Bilinear.lean:1454 | characters |
| `Salt.N7.cellCount_ne_zero_extract` | Salt/HB/Lemma5Bilinear.lean:1525 | characters |
| `Salt.N7.exists_unique_dyadic` | Salt/HB/Lemma5Bilinear.lean:1552 | characters |
| `Salt.N7.unitRep_modEq` | Salt/HB/Lemma5Bilinear.lean:1592 | characters |
| `Salt.N7.unitRep_mem_Icc` | Salt/HB/Lemma5Bilinear.lean:1600 | characters |
| `Salt.N7.unitRep_coprime` | Salt/HB/Lemma5Bilinear.lean:1608 | characters |
| `Salt.N7.unitRep_unique` | Salt/HB/Lemma5Bilinear.lean:1619 | characters |
| `Salt.N7.truncChiSum_eq_sum_cells` | Salt/HB/Lemma5Bilinear.lean:1650 | characters |
| `Salt.N7.coprime_of_modEq` | Salt/HB/Lemma5Bilinear.lean:1775 | characters |
| `Salt.N7.cell_card_eq_zero_of_not_coprime` | Salt/HB/Lemma5Bilinear.lean:1790 | characters |
| `Salt.N7.not_coprime_of_not_mem_window` | Salt/HB/Lemma5Bilinear.lean:1808 | characters |
| `Salt.N7.sum_pull₈` | Salt/HB/Lemma5Bilinear.lean:1823 | characters |
| `Salt.N7.sum_swap_two_two` | Salt/HB/Lemma5Bilinear.lean:1873 | characters |
| `Salt.N7.sum_cells_mul` | Salt/HB/Lemma5Bilinear.lean:1887 | characters |
| `Salt.N7.bilinearS_eq_sum_cells` | Salt/HB/Lemma5Bilinear.lean:1912 | characters |
| `Salt.N7.cellCount_ne_zero_bounds` | Salt/HB/Lemma5Bilinear.lean:2062 | characters |
| `Salt.N7.cellCount_swap₁` | Salt/HB/Lemma5Bilinear.lean:2132 | characters |
| `Salt.N7.cellCount_swap₂` | Salt/HB/Lemma5Bilinear.lean:2149 | characters |
| `Salt.N7.gcd_lcm_distrib` | Salt/HB/Lemma5Bilinear.lean:2175 | characters |
| `Salt.N7.cellCount_eq_zero_of_not_congr` | Salt/HB/Lemma5Bilinear.lean:2203 | characters |
| `Salt.N7.crt_four` | Salt/HB/Lemma5Bilinear.lean:2277 | characters |
| `Salt.N7.crt_collapse` | Salt/HB/Lemma5Bilinear.lean:2322 | characters |
| `Salt.N7.nested` | Salt/HB/Lemma5Bilinear.lean:2629 | characters |
| `Salt.N7.card_Ioc_filter_modEq_eq_sawtooth` | Salt/HB/Lemma5Bilinear.lean:2635 | characters |
| `Salt.N7.modEq_mul_iff_modEq_invMod` | Salt/HB/Lemma5Bilinear.lean:2662 | characters |
| `Salt.N7.card_count_eq_sawtooth` | Salt/HB/Lemma5Bilinear.lean:2682 | characters |
| `Salt.N7.count_eq_zero_of_not_coprime` | Salt/HB/Lemma5Bilinear.lean:2704 | characters |
| `Salt.N7.R₂_le_hbT₁` | Salt/HB/Lemma5Bilinear.lean:2723 | characters |
| `Salt.N7.hbT₁_pos` | Salt/HB/Lemma5Bilinear.lean:2726 | characters |
| `Salt.N7.hbT₂_le_two_R₂` | Salt/HB/Lemma5Bilinear.lean:2729 | characters |
| `Salt.N7.mem_Ioc_floor_iff` | Salt/HB/Lemma5Bilinear.lean:2733 | characters |
| `Salt.N7.Ioc_floor_eq_empty_of_neg` | Salt/HB/Lemma5Bilinear.lean:2753 | characters |
| `Salt.N7.five_eight_iff` | Salt/HB/Lemma5Bilinear.lean:2763 | characters |
| `Salt.N7.hbT_mem_iff` | Salt/HB/Lemma5Bilinear.lean:2795 | characters |
| `Salt.N7.cellCount_eq_sum_w` | Salt/HB/Lemma5Bilinear.lean:2889 | characters |
| `Salt.N7.coprime_w₁_of_count_ne_zero` | Salt/HB/Lemma5Bilinear.lean:3066 | characters |
| `Salt.N7.kb5f_C_coprime` | Salt/HB/Lemma5Bilinear.lean:3150 | characters |
| `Salt.N7.kb5f_C_iff` | Salt/HB/Lemma5Bilinear.lean:3173 | characters |
| `Salt.N7.kb5f_k_pos` | Salt/HB/Lemma5Bilinear.lean:3197 | characters |
| `Salt.N7.kb5f_k_two` | Salt/HB/Lemma5Bilinear.lean:3207 | characters |
| `Salt.N7.kb5f_two_dvd_alpha` | Salt/HB/Lemma5Bilinear.lean:3222 | characters |
| `Salt.N7.cellCount_eq_sum_sawtooth` | Salt/HB/Lemma5Bilinear.lean:3235 | characters |
| `Salt.HB.exp_two_mul_log` | Salt/HB/Lemma7.lean:68 | characters |
| `Salt.HB.sq_eq_exp_mul_one_add` | Salt/HB/Lemma7.lean:78 | characters |
| `Salt.HB.abs_one_add_mul_sub_one_le` | Salt/HB/Lemma7.lean:94 | characters |
| `Salt.HB.primeProdBelow_pos` | Salt/HB/Lemma7.lean:108 | characters |
| `Salt.HB.hb_mertens_third_real` | Salt/HB/Lemma7.lean:122 | characters |
| `Salt.HB.hb_L2_core` | Salt/HB/Lemma7.lean:194 | characters |
| `Salt.HB.hb_L2_at_split_point` | Salt/HB/Lemma7.lean:267 | characters |
| `Salt.HB.hasDerivAt_wLog` | Salt/HB/Lemma7EF.lean:61 | characters |
| `Salt.HB.wLog_nonneg` | Salt/HB/Lemma7EF.lean:80 | characters |
| `Salt.HB.wLog'_nonpos` | Salt/HB/Lemma7EF.lean:84 | characters |
| `Salt.HB.sum_Icc_zero_eq_psiChiR` | Salt/HB/Lemma7EF.lean:114 | sieves, characters |
| `Salt.HB.abel_logChiSum` | Salt/HB/Lemma7EF.lean:140 | characters |
| `Salt.HB.mainTerm_ibp` | Salt/HB/Lemma7EF.lean:172 | characters |
| `Salt.HB.logChiSum_add_mainTerm_norm_le` | Salt/HB/Lemma7EF.lean:228 | characters |
| `Salt.HB.psiDefect_norm_le_of_ef` | Salt/HB/Lemma7EF.lean:384 | characters |
| `Salt.HB.rpow_c_add_one` | Salt/HB/Lemma7EF.lean:496 | characters |
| `Salt.HB.efShiftError_le_efShiftBound` | Salt/HB/Lemma7EF.lean:530 | characters |
| `Salt.HB.re_le_repulsionCeiling_of_ne` | Salt/HB/Lemma7EF.lean:661 | characters |
| `Salt.HB.exists_repulsion_ceiling_of_ne` | Salt/HB/Lemma7EF.lean:696 | characters |
| `Salt.HB.re_le_of_zeroFree_of_ne` | Salt/HB/Lemma7EF.lean:722 | characters |
| `Salt.HB.psiDefect_norm_le_rangeA` | Salt/HB/Lemma7EF.lean:748 | characters |
| `Salt.HB.two_le_efT0` | Salt/HB/Lemma7EF.lean:799 | characters |
| `Salt.HB.efH_pos` | Salt/HB/Lemma7EF.lean:810 | characters |
| `Salt.HB.psiDefect_norm_le_envelope` | Salt/HB/Lemma7EF.lean:838 | characters |
| `Salt.HB.continuousOn_efEnvelope` | Salt/HB/Lemma7EF.lean:1007 | characters |
| `Salt.HB.efShiftB_nonneg` | Salt/HB/Lemma7EF.lean:1050 | characters |
| `Salt.HB.efShiftBound_nonneg` | Salt/HB/Lemma7EF.lean:1075 | characters |
| `Salt.HB.efEnvelope_nonneg` | Salt/HB/Lemma7EF.lean:1093 | characters |
| `Salt.HB.logChiSum_composite_of_ceiling` | Salt/HB/Lemma7EF.lean:1128 | characters |
| `Salt.HB.logChiSum_add` | Salt/HB/Lemma7EF.lean:1155 | characters |
| `Salt.HB.intervalIntegrable_rpow_div_log` | Salt/HB/Lemma7EF.lean:1168 | characters |
| `Salt.HB.integrableOn_rpow_div_log` | Salt/HB/Lemma7EF.lean:1181 | characters |
| `Salt.HB.logChiSum_tendsto_of_envelope` | Salt/HB/Lemma7EF.lean:1214 | characters |
| `Salt.HB.efShiftB_le_scale_sharp` | Salt/HB/Lemma7EF.lean:2469 | characters |
| `Salt.HB.efEnvelope_le_ledger_sharp` | Salt/HB/Lemma7EF.lean:2624 | characters |
| `Salt.HB.ledger_const_le_of_window` | Salt/HB/Lemma7EF.lean:2842 | characters |
| `Salt.HB.efEnvelope_zfr_eventually_le_sharp` | Salt/HB/Lemma7EF.lean:2904 | characters |
| `Salt.HB.integral_inv_mul_log_sq` | Salt/HB/Lemma7EF.lean:3056 | characters |
| `Salt.HB.tail_le_of_pointwise` | Salt/HB/Lemma7EF.lean:3084 | characters |
| `Salt.HB.logChiSum_tendsto_zfr_hundred` | Salt/HB/Lemma7EF.lean:3136 | characters |
| `Salt.HB.integrableOn_expNeg_div_Ioi` | Salt/HB/Lemma7F.lean:92 | characters |
| `Salt.HB.integrableOn_expNeg_mul_log_Ioi_zero` | Salt/HB/Lemma7F.lean:118 | characters |
| `Salt.HB.hasDerivAt_expNeg_mul_log` | Salt/HB/Lemma7F.lean:165 | characters |
| `Salt.HB.expIntegral_ibp` | Salt/HB/Lemma7F.lean:181 | characters |
| `Salt.HB.expIntegral_eq_sub` | Salt/HB/Lemma7F.lean:223 | characters |
| `Salt.HB.abs_integral_expNeg_mul_log_Ioc_le` | Salt/HB/Lemma7F.lean:244 | characters |
| `Salt.HB.expIntegral_sub_log_gamma_abs_le` | Salt/HB/Lemma7F.lean:278 | characters |
| `Salt.HB.integral_rpow_div_log_Ioi_eq_expIntegral` | Salt/HB/Lemma7F.lean:332 | characters |
| `Salt.HB.hb_F_tail_integral` | Salt/HB/Lemma7F.lean:435 | characters |
| `Salt.HB.chi_eq_ofReal_chiRe` | Salt/HB/Lemma7F.lean:504 | characters |
| `Salt.HB.chiRe_eq_two_mul_ind_sub` | Salt/HB/Lemma7F.lean:514 | characters |
| `Salt.HB.logChiSum_re_eq` | Salt/HB/Lemma7F.lean:536 | sieves, characters |
| `Salt.HB.chiOne_prime_logWeighted_le` | Salt/HB/Lemma7F.lean:570 | sieves, characters |
| `Salt.HB.rankin_floor_le` | Salt/HB/Lemma7F.lean:623 | characters |
| `Salt.HB.two_mul_pretenseSum_le_at_window` | Salt/HB/Lemma7F.lean:644 | characters |
| `Salt.HB.hb_chiOne_kill_at_window` | Salt/HB/Lemma7F.lean:722 | sieves, characters |
| `Salt.HB.hb_logF_at_split_point` | Salt/HB/Lemma7F.lean:779 | characters |
| `Salt.HB.mem_Pz` | Salt/HB/Lemma7Kappa.lean:74 | characters |
| `Salt.HB.hbG_prime` | Salt/HB/Lemma7Kappa.lean:92 | characters |
| `Salt.HB.hbG_prime_dvd` | Salt/HB/Lemma7Kappa.lean:98 | characters |
| `Salt.HB.hbG_le_four` | Salt/HB/Lemma7Kappa.lean:103 | characters |
| `Salt.HB.one_sub_hbG_div_eq` | Salt/HB/Lemma7Kappa.lean:114 | characters |
| `Salt.HB.hbSfac_le_one` | Salt/HB/Lemma7Kappa.lean:142 | characters |
| `Salt.HB.one_sub_four_div_sq_le_hbSfac` | Salt/HB/Lemma7Kappa.lean:155 | characters |
| `Salt.HB.hbSfac_pos` | Salt/HB/Lemma7Kappa.lean:176 | characters |
| `Salt.HB.abs_log_hbSfac_le` | Salt/HB/Lemma7Kappa.lean:185 | characters |
| `Salt.HB.tsum_tail_inv_sq_le` | Salt/HB/Lemma7Kappa.lean:223 | characters |
| `Salt.HB.three_le_of_primesGt2` | Salt/HB/Lemma7Kappa.lean:263 | characters |
| `Salt.HB.summable_eight_div_sq` | Salt/HB/Lemma7Kappa.lean:268 | characters |
| `Salt.HB.abs_log_twinFactor_le` | Salt/HB/Lemma7Kappa.lean:276 | characters |
| `Salt.HB.hbSfac_log_summable` | Salt/HB/Lemma7Kappa.lean:302 | characters |
| `Salt.HB.hbWfac_pos` | Salt/HB/Lemma7Kappa.lean:307 | characters |
| `Salt.HB.abs_log_hbWfac_le` | Salt/HB/Lemma7Kappa.lean:314 | characters |
| `Salt.HB.hbWfac_log_summable` | Salt/HB/Lemma7Kappa.lean:322 | characters |
| `Salt.HB.hbWfac_multipliable` | Salt/HB/Lemma7Kappa.lean:329 | characters |
| `Salt.HB.hb_hsing` | Salt/HB/Lemma7Kappa.lean:371 | characters |
| `Salt.HB.hb_rear_factor` | Salt/HB/Lemma7Kappa.lean:539 | characters |
| `Salt.HB.hb_rear_factor_two` | Salt/HB/Lemma7Kappa.lean:607 | characters |
| `Salt.HB.gt2Primes_eq_filter` | Salt/HB/Lemma7Kappa.lean:621 | characters |
| `Salt.HB.hb_rear_prod_identity` | Salt/HB/Lemma7Kappa.lean:631 | characters |
| `Salt.HB.hbCalpha_eq` | Salt/HB/Lemma7Kappa.lean:661 | characters |
| `Salt.HB.alpha_primeFactors_prod_eq` | Salt/HB/Lemma7Kappa.lean:676 | characters |
| `Salt.HB.qFactors_low_prod_eq` | Salt/HB/Lemma7Kappa.lean:692 | characters |
| `Salt.HB.hbS1_eq` | Salt/HB/Lemma7Kappa.lean:708 | characters |
| `Salt.HB.hbKappaTail_split` | Salt/HB/Lemma7Kappa.lean:721 | characters |
| `Salt.HB.one_sub_sum_le_prod_one_sub` | Salt/HB/Lemma7Kappa.lean:797 | characters |
| `Salt.HB.abs_prod_one_sub_two_div_sub_one_le` | Salt/HB/Lemma7Kappa.lean:823 | characters |
| `Salt.HB.hb_hrear` | Salt/HB/Lemma7Kappa.lean:858 | characters |
| `Salt.HB.hb_L2_at_split_point_concrete` | Salt/HB/Lemma7Kappa.lean:938 | characters |
| `Salt.HB.chiReTB_abs_le_one` | Salt/HB/Lemma7Prod.lean:79 | characters |
| `Salt.HB.one_lt_log_three` | Salt/HB/Lemma7Prod.lean:95 | characters |
| `Salt.HB.abs_log_log_floor_sub_le` | Salt/HB/Lemma7Prod.lean:103 | characters |
| `Salt.HB.log_le_two_mul_log_floor` | Salt/HB/Lemma7Prod.lean:157 | characters |
| `Salt.HB.hbEulerProd_pos` | Salt/HB/Lemma7Prod.lean:187 | characters |
| `Salt.HB.log_hbEulerProd` | Salt/HB/Lemma7Prod.lean:192 | characters |
| `Salt.HB.hbLogF_eq_of_tendsto` | Salt/HB/Lemma7Prod.lean:215 | characters |
| `Salt.HB.tendsto_hbEulerProd_hbF` | Salt/HB/Lemma7Prod.lean:222 | characters |
| `Salt.HB.abs_neg_log_one_sub_sub_self_le` | Salt/HB/Lemma7Prod.lean:238 | characters |
| `Salt.HB.hbEulerLog_sub_primeSum_termwise` | Salt/HB/Lemma7Prod.lean:257 | characters |
| `Salt.HB.sum_two_div_sq_windowPrimes_le` | Salt/HB/Lemma7Prod.lean:280 | characters |
| `Salt.HB.ppDefect_nonneg` | Salt/HB/Lemma7Prod.lean:314 | characters |
| `Salt.HB.logChiSum_re_eq_sum` | Salt/HB/Lemma7Prod.lean:323 | sieves, characters |
| `Salt.HB.logChiSum_re_sub_primeSum_le` | Salt/HB/Lemma7Prod.lean:334 | characters |
| `Salt.HB.sum_recip_windowPrimes_eq` | Salt/HB/Lemma7Prod.lean:373 | characters |
| `Salt.HB.sum_recip_largePrimeFactors_le` | Salt/HB/Lemma7Prod.lean:401 | characters |
| `Salt.HB.hb_coprime_segment` | Salt/HB/Lemma7Prod.lean:450 | characters |
| `Salt.HB.hb_hseg` | Salt/HB/Lemma7Prod.lean:587 | sieves, characters |
| `Salt.HB.hb_hcorr_finite` | Salt/HB/Lemma7Prod.lean:653 | characters |
| `Salt.HB.hb_hcorr_at_limit` | Salt/HB/Lemma7Prod.lean:669 | characters |
| `Salt.HB.sum_ppCoef_eq` | Salt/HB/Lemma7Prod.lean:694 | characters |
| `Salt.HB.sum_ppCoef_nat_eq` | Salt/HB/Lemma7Prod.lean:709 | characters |
| `Salt.HB.psi_sub_theta_nonneg` | Salt/HB/Lemma7Prod.lean:715 | characters |
| `Salt.HB.abs_wLog'_mul_psi_sub_theta_le` | Salt/HB/Lemma7Prod.lean:720 | characters |
| `Salt.HB.ppDefect_le` | Salt/HB/Lemma7Prod.lean:756 | characters |
| `Salt.HB.ppDefect_le'` | Salt/HB/Lemma7Prod.lean:869 | characters |
| `Salt.HB.hb_hcorr_closed` | Salt/HB/Lemma7Prod.lean:885 | characters |
| `Salt.HB.hb_hseg_closed` | Salt/HB/Lemma7Prod.lean:895 | sieves, characters |
| `Salt.HB.zeroMult_eq_one_of_window` | Salt/HB/MOne.lean:78 | characters |
| `Salt.HB.zeroMult_eq_one_of_gap` | Salt/HB/MOne.lean:99 | characters |
| `Salt.HB.zeroMult_eq_one_of_eta` | Salt/HB/MOne.lean:142 | characters |
| `Salt.HB.rhoK_prime` | Salt/HB/MixedCount.lean:201 | characters |
| `Salt.HB.card_mixResidues` | Salt/HB/MixedCount.lean:323 | characters |
| `Salt.HB.mixPairSieve_rem_abs_le` | Salt/HB/MixedCount.lean:479 | characters |
| `Salt.HB.mixPairSieve_errSum_le` | Salt/HB/MixedCount.lean:525 | sieves, characters |
| `Salt.HB.hb_lemma8'_unconditional` | Salt/HB/MixedCount.lean:609 | characters |
| `Salt.HB.card_apResidues` | Salt/HB/PairInstance.lean:136 | characters |
| `Salt.HB.hbPairSieve_rem_abs_le` | Salt/HB/PairInstance.lean:268 | characters |
| `Salt.HB.hbPairSieve_errSum_le` | Salt/HB/PairInstance.lean:324 | sieves, characters |
| `Salt.HB.hb_lemma8` | Salt/HB/PairInstance.lean:414 | characters |
| `Salt.HB.boundingSum_ge_log_sq_of_twinDensity` | Salt/HB/PairSieve.lean:192 | sieves, characters |
| `Salt.HB.pairSieve_lemma8` | Salt/HB/PairSieve.lean:224 | sieves, characters |
| `Salt.HB.boundingSum_ge_phi_log_sq` | Salt/HB/PairSieveMixed.lean:253 | sieves, characters |
| `Salt.HB.pairSieveMixed_lemma8` | Salt/HB/PairSieveMixed.lean:301 | sieves, characters |
| `Salt.HB.two_mul_pretenseSum_le_vmPairW` | Salt/HB/PretenseSumProof.lean:152 | characters |
| `Salt.HB.two_mul_pretenseSum_le_mertens` | Salt/HB/PretenseSumProof.lean:196 | characters |
| `Salt.HB.inv_le_rpow_mul_rpow_neg` | Salt/HB/PretenseSumProof.lean:205 | characters |
| `Salt.HB.two_mul_pretenseSum_le_vmPairS` | Salt/HB/PretenseSumProof.lean:225 | characters |
| `Salt.HB.pole_cancel_le` | Salt/HB/PretenseSumProof.lean:247 | characters |
| `Salt.HB.hb_rate_at_optimal_a` | Salt/HB/PretenseSumProof.lean:264 | characters |
| `Salt.HB.hb_rate_optimal` | Salt/HB/PretenseSumProof.lean:276 | characters |
| `Salt.HB.one_sub_ceiling_le_dist_one` | Salt/HB/PretenseSumProof.lean:312 | characters |
| `Salt.HB.nearOne_multTotal_le` | Salt/HB/PretenseSumProof.lean:341 | characters |
| `Salt.HB.nearOne_invSq_sum_le` | Salt/HB/PretenseSumProof.lean:381 | characters |
| `Salt.HB.pretenseSum_le` | Salt/HB/PretenseSumProof.lean:538 | characters |
| `Salt.HB.pretenseSum_le_series` | Salt/HB/PretenseSumProof.lean:550 | characters |
| `Salt.HB.pretenseSum_le_hb_rate` | Salt/HB/PretenseSumProof.lean:566 | characters |
| `Salt.HB.pretenseSum_le_hb_rate_rpow` | Salt/HB/PretenseSumProof.lean:579 | characters |
| `Salt.HB.pretenseSum_le_quarter_rate` | Salt/HB/PretenseSumProof.lean:590 | characters |
| `Salt.HB.quadraticChar_sum_mul_shift` | Salt/HB/QuadCharSum.lean:68 | characters |
| `Salt.HB.quadraticChar_sum_two_forms_trivial` | Salt/HB/QuadCharSum.lean:123 | characters |
| `Salt.HB.quadraticChar_sum_two_forms_bound` | Salt/HB/QuadCharSum.lean:143 | characters |
| `Salt.HB.quadraticChar_sum_two_forms_eq` | Salt/HB/QuadCharSum.lean:200 | characters |
| `Salt.HB.quadraticChar_sum_two_forms_bound_one` | Salt/HB/QuadCharSum.lean:253 | characters |
| `Salt.HB.legendre_sum_mul_shift` | Salt/HB/QuadCharSum.lean:274 | characters |
| `Salt.HB.legendre_sum_two_forms_bound` | Salt/HB/QuadCharSum.lean:281 | characters |
| `Salt.HB.legendre_sum_two_forms_bound_one` | Salt/HB/QuadCharSum.lean:290 | characters |
| `Salt.HB.legendre_sum_two_forms_trivial` | Salt/HB/QuadCharSum.lean:298 | characters |
| `Salt.HB.isQuadratic_of_int` | Salt/HB/RealPrimStructure.lean:63 | characters |
| `Salt.HB.int_apply_unit` | Salt/HB/RealPrimStructure.lean:74 | characters |
| `Salt.HB.chineseRemainder_apply` | Salt/HB/RealPrimStructure.lean:92 | characters |
| `Salt.HB.crtFactor_apply` | Salt/HB/RealPrimStructure.lean:175 | characters |
| `Salt.HB.crtFactor₁_unique` | Salt/HB/RealPrimStructure.lean:187 | characters |
| `Salt.HB.crtFactor₂_unique` | Salt/HB/RealPrimStructure.lean:200 | characters |
| `Salt.HB.crtFactor₁_isPrimitive` | Salt/HB/RealPrimStructure.lean:224 | characters |
| `Salt.HB.crtFactor₂_isPrimitive` | Salt/HB/RealPrimStructure.lean:268 | characters |
| `Salt.HB.not_isPrimitive_of_odd_prime_pow` | Salt/HB/RealPrimStructure.lean:323 | characters |
| `Salt.HB.eq_quadraticChar_of_isPrimitive` | Salt/HB/RealPrimStructure.lean:371 | characters |
| `Salt.HB.not_isPrimitive_two` | Salt/HB/RealPrimStructure.lean:403 | characters |
| `Salt.HB.exists_odd_sq_sub_dvd` | Salt/HB/RealPrimStructure.lean:415 | characters |
| `Salt.HB.not_isPrimitive_two_pow` | Salt/HB/RealPrimStructure.lean:439 | characters |
| `Salt.HB.isPrimitive_two_pow_of_not_factorsThrough` | Salt/HB/RealPrimStructure.lean:485 | characters |
| `Salt.HB.isPrimitive_chi4` | Salt/HB/RealPrimStructure.lean:504 | characters |
| `Salt.HB.isPrimitive_chi8` | Salt/HB/RealPrimStructure.lean:521 | characters |
| `Salt.HB.isPrimitive_chi8'` | Salt/HB/RealPrimStructure.lean:538 | characters |
| `Salt.HB.eq_chi4_of_isPrimitive` | Salt/HB/RealPrimStructure.lean:555 | characters |
| `Salt.HB.eq_chi8_or_chi8'_of_isPrimitive` | Salt/HB/RealPrimStructure.lean:579 | characters |
| `Salt.HB.squarefree_and_eq_jacobiChar_of_isPrimitive` | Salt/HB/RealPrimStructure.lean:691 | characters |
| `Salt.HB.exists_split_of_isPrimitive` | Salt/HB/RealPrimStructure.lean:699 | characters |
| `Salt.HB.structure_of_isPrimitive` | Salt/HB/RealPrimStructure.lean:737 | characters |
| `Salt.HB.sum_two_forms_le_gcd_of_isPrimitive` | Salt/HB/RealPrimStructure.lean:763 | characters |
| `Salt.HB.exists_split_of_isPrimitive_enumerated` | Salt/HB/RealPrimStructure.lean:779 | characters |
| `Salt.HB.chi4_sum_two_forms_le_gcd` | Salt/HB/RealPrimitive.lean:73 | characters |
| `Salt.HB.chi8_sum_two_forms_le_gcd` | Salt/HB/RealPrimitive.lean:82 | characters |
| `Salt.HB.chi8'_sum_two_forms_le_gcd` | Salt/HB/RealPrimitive.lean:90 | characters |
| `Salt.HB.sum_range_nsmul_of_periodic` | Salt/HB/RealPrimitive.lean:106 | characters |
| `Salt.HB.sum_range_eq_nsmul_of_dvd_of_periodic` | Salt/HB/RealPrimitive.lean:129 | characters |
| `Salt.HB.sum_range_natCast_eq_sum_univ` | Salt/HB/RealPrimitive.lean:160 | characters |
| `Salt.HB.sum_two_forms_range_eq_univ` | Salt/HB/RealPrimitive.lean:174 | characters |
| `Salt.HB.gcd_val_castHom` | Salt/HB/RealPrimitive.lean:180 | characters |
| `Salt.HB.hasTwoFormGcdBound_of_modulus_one` | Salt/HB/RealPrimitive.lean:261 | characters |
| `Salt.HB.hasTwoFormGcdBound_chi4` | Salt/HB/RealPrimitive.lean:270 | characters |
| `Salt.HB.hasTwoFormGcdBound_chi8` | Salt/HB/RealPrimitive.lean:276 | characters |
| `Salt.HB.hasTwoFormGcdBound_chi8'` | Salt/HB/RealPrimitive.lean:282 | characters |
| `Salt.HB.jacobiChar_prime` | Salt/HB/RealPrimitive.lean:295 | characters |
| `Salt.HB.hasTwoFormGcdBound_jacobiChar_prime` | Salt/HB/RealPrimitive.lean:304 | characters |
| `Salt.HB.hasTwoFormGcdBound_jacobiChar` | Salt/HB/RealPrimitive.lean:330 | characters |
| `Salt.HB.sum_class_eq_zero_of_isPrimitive` | Salt/HB/RealPrimitive.lean:415 | characters |
| `Salt.HB.Gdens_le_four` | Salt/HB/RosserDim4.lean:317 | characters |
| `Salt.HB.log_Wratio_le_ladder_dim4` | Salt/HB/RosserDim4.lean:404 | sieves, characters |
| `Salt.HB.M_bound_gen` | Salt/HB/RosserDim4.lean:539 | characters |
| `Salt.HB.hMert_dim4` | Salt/HB/RosserDim4.lean:687 | sieves, characters |
| `Salt.HB.brun_lower_dim4` | Salt/HB/RosserDim4.lean:764 | sieves, characters |
| `Salt.HB.brun_upper_dim4` | Salt/HB/RosserDim4.lean:785 | sieves, characters |
| `Salt.HB.fl_defect_le` | Salt/HB/RosserDim4FL.lean:219 | characters |
| `Salt.HB.fl_defect_le_upper` | Salt/HB/RosserDim4FL.lean:259 | characters |
| `Salt.HB.flConst_quarter_le` | Salt/HB/RosserDim4FL.lean:315 | characters |
| `Salt.HB.fl_dim4_lower` | Salt/HB/RosserDim4FL.lean:364 | sieves, characters |
| `Salt.HB.fl_dim4_upper` | Salt/HB/RosserDim4FL.lean:388 | sieves, characters |
| `Salt.HB.failSet_unique` | Salt/HB/RosserDim4FL.lean:526 | characters |
| `Salt.HB.firstFailure_decomposition` | Salt/HB/RosserDim4FL.lean:628 | characters |
| `Salt.HB.failSet_le_rpow` | Salt/HB/RosserDim4FL.lean:670 | characters |
| `Salt.HB.failSet_moebius` | Salt/HB/RosserDim4FL.lean:773 | characters |
| `Salt.HB.firstFailure_decomposition_signed` | Salt/HB/RosserDim4FL.lean:810 | characters |
| `Salt.HB.perDelta_transfer` | Salt/HB/RosserDim4FL.lean:843 | characters |
| `Salt.HB.transfer_of_decomposition` | Salt/HB/RosserDim4FL.lean:856 | characters |
| `Salt.HB.hb_perDelta_transfer` | Salt/HB/RosserDim4FL.lean:874 | characters |
| `Salt.HB.nuG_isMultiplicative` | Salt/HB/RosserDim4Instance.lean:125 | characters |
| `Salt.HB.hbP_squarefree` | Salt/HB/RosserDim4Instance.lean:224 | characters |
| `Salt.HB.hbP_chi` | Salt/HB/RosserDim4Instance.lean:244 | characters |
| `Salt.HB.hb_sandwich_upper` | Salt/HB/RosserDim4Instance.lean:407 | sieves, characters |
| `Salt.HB.hb_sandwich_lower` | Salt/HB/RosserDim4Instance.lean:419 | sieves, characters |
| `Salt.HB.moebSum_nu_eq_W` | Salt/HB/RosserDim4Instance.lean:436 | sieves, characters |
| `Salt.HB.mainSum_chi_eq_W_sub_correction` | Salt/HB/RosserDim4Instance.lean:451 | sieves, characters |
| `Salt.HB.hb_levelRatio_eq` | Salt/HB/RosserDim4Instance.lean:470 | characters |
| `Salt.HB.hb_fl_lower` | Salt/HB/RosserDim4Instance.lean:483 | sieves, characters |
| `Salt.HB.hb_fl_upper` | Salt/HB/RosserDim4Instance.lean:506 | sieves, characters |
| `Salt.HB.hb_transfer` | Salt/HB/RosserDim4Instance.lean:531 | characters |
| `Salt.HB.hbSieve_fl_sandwich` | Salt/HB/RosserDim4Instance.lean:564 | sieves, characters |
| `Salt.HB.chiReChar_apply` | Salt/HB/SieveWire.lean:87 | sieves, characters |
| `Salt.HB.chiReChar_prime` | Salt/HB/SieveWire.lean:99 | sieves, characters |
| `Salt.HB.hbSiftSet_chiReChar` | Salt/HB/SieveWire.lean:106 | sieves, characters |
| `Salt.HB.hbData_fl_sandwich` | Salt/HB/SieveWire.lean:155 | sieves, characters |
| `Salt.HB.LamTildeGen_lamR_eq_vonMangoldt` | Salt/HB/SignLiouville.lean:93 | characters |
| `Salt.HB.hstar_window` | Salt/HB/StarWindow.lean:288 | characters |
| `Salt.HB.S2_sub_S3_honestWindow` | Salt/HB/StarWindow.lean:429 | characters |
| `Salt.HB.n9B2_spec` | Salt/HB/TailShells.lean:50 | zeros, characters |
| `Salt.HB.efZeroSumM_norm_le_termwise` | Salt/HB/TailShells.lean:57 | characters |
| `Salt.HB.zeroSum_shells_le` | Salt/HB/TailShells.lean:137 | characters |
| `Salt.HB.psiDefect_norm_le_raw` | Salt/HB/TailShells.lean:300 | characters |
| `Salt.HB.psiDefect_norm_le_envelopeB3` | Salt/HB/TailShells.lean:379 | characters |
| `Salt.HB.efEnvelopeB3_nonneg` | Salt/HB/TailShells.lean:447 | characters |
| `Salt.HB.continuousOn_efEnvelopeB3_ceilFun` | Salt/HB/TailShells.lean:583 | characters |
| `Salt.HB.efEnvelopeB3_le_ledger` | Salt/HB/TailShells.lean:622 | characters |
| `Salt.HB.integral_rpow_div_log_tail_le` | Salt/HB/TailShells.lean:709 | characters |
| `Salt.HB.twin_termwise_le` | Salt/HB/Transfer.lean:158 | characters |
| `Salt.HB.S1_le_S2` | Salt/HB/Transfer.lean:189 | characters |
| `Salt.HB.overshoot_sum_nonneg` | Salt/HB/Transfer.lean:211 | characters |
| `Salt.HB.coprimeSupport_window` | Salt/HB/Transfer.lean:223 | characters |
| `Salt.HB.LamTilde_eq_fChi_conv` | Salt/HB/TwistChain.lean:351 | characters |
| `Salt.HB.LamStar_eq_fStar_conv` | Salt/HB/TwistChain.lean:355 | characters |
| `Salt.HB.LamStar_nonneg` | Salt/HB/TwistChain.lean:359 | characters |
| `Salt.HB.vonMangoldt_le_LamTilde` | Salt/HB/TwistChain.lean:368 | characters |
| `Salt.HB.eq_nPlus_mul_nMinus` | Salt/HB/TwistChain.lean:408 | characters |
| `Salt.HB.coprime_nPlus_nMinus` | Salt/HB/TwistChain.lean:424 | characters |
| `Salt.HB.LamTilde_eq_sum_nPlus` | Salt/HB/TwistChainC.lean:121 | characters |
| `Salt.HB.LamTilde_sub_vonMangoldt_le` | Salt/HB/TwistChainC.lean:317 | characters |
| `Salt.HB.logDeriv_LFunction_eq_LSeries` | Salt/HB/TwistedMertens.lean:136 | zeros, characters |
| `Salt.HB.neg_re_logDeriv_LFunction_eq_tsum` | Salt/HB/TwistedMertens.lean:197 | characters |
| `Salt.HB.neg_re_logDeriv_zeta_eq_tsum` | Salt/HB/TwistedMertens.lean:215 | zeros, characters |
| `Salt.HB.neg_re_logDeriv_LFunction_le` | Salt/HB/TwistedMertens.lean:229 | characters |
| `Salt.HB.vmPairS_le_pole` | Salt/HB/TwistedMertens.lean:252 | characters |
| `Salt.HB.norm_inv_sub_inv` | Salt/HB/TwistedMertens.lean:283 | characters |
| `Salt.HB.dist_one_lower_of_floor` | Salt/HB/TwistedMertens.lean:293 | characters |
| `Salt.HB.per_zero_inv_diff_le` | Salt/HB/TwistedMertens.lean:315 | characters |
| `Salt.HB.neg_re_logDeriv_differenced` | Salt/HB/TwistedMertens.lean:362 | characters |
| `Salt.HB.invSq_sum_split_le` | Salt/HB/TwistedMertens.lean:597 | characters |
| `Salt.HB.hbCoreRate_at_operating_point` | Salt/HB/TwistedMertens.lean:664 | characters |
| `Salt.HB.hbCoreRate_at_hb_optimum` | Salt/HB/TwistedMertens.lean:698 | characters |
| `Salt.HB.vmPairS_le_hb_core` | Salt/HB/TwistedMertens.lean:730 | characters |
| `Salt.HB.pretenseSum_le_differenced` | Salt/HB/TwistedMertens.lean:759 | characters |
| `Salt.HardyLittlewood.pi2_multipliable` | Salt/HardyLittlewood/Frame.lean:68 | sieves |
| `Salt.HardyLittlewood.pi2_pos` | Salt/HardyLittlewood/Frame.lean:75 | sieves |
| `Salt.HardyLittlewood.pi2_lt_one` | Salt/HardyLittlewood/Frame.lean:80 | sieves |
| `Salt.HardyLittlewood.twinSingularSeries_pos` | Salt/HardyLittlewood/Frame.lean:113 | sieves |
| `Salt.HardyLittlewood.twinSingularSeries_lt_two` | Salt/HardyLittlewood/Frame.lean:117 | sieves |
| `Salt.HardyLittlewood.twinCounting_upper_order` | Salt/HardyLittlewood/Frame.lean:131 | sieves |
| `Salt.HardyLittlewood.Sel.twinCounting_upper_selberg` | Salt/HardyLittlewood/Selberg16/Crown.lean:21 | sieves |
| `Salt.HardyLittlewood.Sel.twin_le_sel` | Salt/HardyLittlewood/Selberg16/Lev.lean:294 | sieves |
| `Salt.HardyLittlewood.Sel.selbergBoundingSum_sel_ge` | Salt/HardyLittlewood/Selberg16/Lev.lean:307 | sieves |
| `Salt.HardyLittlewood.Sel.mainTermSum_lower` | Salt/HardyLittlewood/Selberg16/M5.lean:134 | sieves |
| `Salt.HardyLittlewood.sum_six_pow_omega_le` | Salt/HardyLittlewood/Sharp.lean:264 | sieves |
| `Salt.HardyLittlewood.twinCounting_upper_sharp` | Salt/HardyLittlewood/Sharp.lean:790 | sieves |
| `Keller.jacobian_det` | Salt/Keller/Counterexample.lean:84 | other |
| `Keller.eval_point0` | Salt/Keller/Counterexample.lean:115 | other |
| `Keller.eval_point1` | Salt/Keller/Counterexample.lean:120 | other |
| `Keller.eval_point2` | Salt/Keller/Counterexample.lean:125 | other |
| `Keller.points_pairwise_distinct` | Salt/Keller/Counterexample.lean:131 | other |
| `Keller.keller_not_injective` | Salt/Keller/Counterexample.lean:142 | other |
| `Keller.jacobian_conjecture_counterexample` | Salt/Keller/Counterexample.lean:159 | other |
| `Keller.keller_not_injective_C` | Salt/Keller/Counterexample.lean:185 | other |
| `Salt.LS.arithmetic_LS` | Salt/LS/ArithmeticLS.lean:91 | sieves, exponential sums |
| `Salt.LS.arithmetic_LS_one` | Salt/LS/ArithmeticLS.lean:147 | sieves, exponential sums |
| `Salt.LS.bdh` | Salt/LS/BDH.lean:360 | sieves, characters |
| `Salt.LS.char_LS_perQ` | Salt/LS/CharLS.lean:74 | sieves, characters, exponential sums |
| `Salt.LS.char_LS` | Salt/LS/CharLS.lean:277 | sieves, characters |
| `Salt.LS.farey_spacing_core` | Salt/LS/Farey.lean:36 | sieves |
| `Salt.LS.farey_spacing` | Salt/LS/Farey.lean:85 | sieves |
| `Salt.LS.gallagher_pointwise` | Salt/LS/Gallagher.lean:38 | sieves |
| `Salt.LS.parseval` | Salt/LS/Parseval.lean:76 | sieves, exponential sums |
| `Salt.LS.vaughan` | Salt/LS/Vaughan.lean:91 | sieves |
| `Salt.LS.vaughan_sum` | Salt/LS/Vaughan.lean:156 | sieves |
| `Salt.MR.a2wall_gate_general` | Salt/MR/A2Wall.lean:84 | characters |
| `Salt.MR.a2wall_gate_45` | Salt/MR/A2Wall.lean:107 | characters |
| `Salt.MR.a2wall_box_clears_45` | Salt/MR/A2Wall.lean:119 | characters |
| `Salt.MR.a2wall_box_floor_clears_gate_45` | Salt/MR/A2Wall.lean:133 | characters |
| `Salt.MR.a2wall_exponent_neg_45` | Salt/MR/A2Wall.lean:152 | characters |
| `Salt.MR.a2wall_critical_n` | Salt/MR/A2Wall.lean:162 | characters |
| `Salt.MR.a2wall_floor_44` | Salt/MR/A2Wall.lean:170 | characters |
| `Salt.MR.a2wall_floor_43_fails` | Salt/MR/A2Wall.lean:181 | characters |
| `Salt.MR.a2wall_floor_48_at_500` | Salt/MR/A2Wall.lean:194 | characters |
| `Salt.MR.a2wall_floor_47_fails_at_500` | Salt/MR/A2Wall.lean:204 | characters |
| `Salt.MR.a2wall_floor32_89` | Salt/MR/A2Wall.lean:218 | characters |
| `Salt.MR.a2wall_floor64_65` | Salt/MR/A2Wall.lean:267 | characters |
| `Salt.MR.a2wall_floor64_64_fails` | Salt/MR/A2Wall.lean:272 | characters |
| `Salt.MR.a2wall_floor32_88_fails` | Salt/MR/A2Wall.lean:275 | characters |
| `Salt.MR.a2wall_box_fails_gate_15` | Salt/MR/A2Wall.lean:292 | characters |
| `Salt.MR.a2wall_ballrad_forced` | Salt/MR/A2Wall.lean:302 | characters |
| `Salt.MR.a2wall_ballrad_pin_exponent` | Salt/MR/A2Wall.lean:325 | characters |
| `Salt.MR.a2wall_ceiling_97` | Salt/MR/A2Wall.lean:340 | characters |
| `Salt.MR.a2wall_ceiling_98_fails` | Salt/MR/A2Wall.lean:351 | characters |
| `Salt.MR.a2wall_ballrad_46_clears` | Salt/MR/A2Wall.lean:363 | characters |
| `Salt.MR.a2wall_window_45_46` | Salt/MR/A2Wall.lean:375 | characters |
| `Salt.MR.mrt_large_range_parametric` | Salt/MR/A4FLargeRange.lean:136 | characters |
| `Salt.MR.mrtLargeRangeEquidistributionFixedEps_holds` | Salt/MR/A4FLargeRange.lean:461 | characters |
| `Salt.MR.mrtLemmaA4iiFixed34E_holds` | Salt/MR/A4FLargeRange.lean:540 | characters |
| `Salt.MR.prime_sum_filter_gt_sub` | Salt/MR/A4FMidBridge.lean:57 | characters |
| `Salt.MR.zeta_near_bridge_lower` | Salt/MR/A4FMidBridge.lean:88 | zeros, characters |
| `Salt.MR.abs_log_zeta_near_one_bounded_height` | Salt/MR/A4FMidBridge.lean:155 | characters |
| `Salt.MR.harmonic_prime_sum_abs_le_bounded_height` | Salt/MR/A4FMidBridge.lean:197 | characters |
| `Salt.MR.harmonic_prime_sum_abs_le_vk` | Salt/MR/A4FMidBridge.lean:221 | characters |
| `Salt.MR.div_seven_pow_seven_le_exp` | Salt/MR/A4FMidRange.lean:48 | characters |
| `Salt.MR.prime_recip_window_bounds` | Salt/MR/A4FMidRange.lean:59 | characters |
| `Salt.MR.mrt_mid_range_parametric` | Salt/MR/A4FMidRange.lean:97 | characters |
| `Salt.MR.mrtShortSegmentSplitting_holds` | Salt/MR/A4FMidRange.lean:416 | characters |
| `Salt.MR.mrt_mid_range_34` | Salt/MR/A4FMidRange.lean:431 | characters |
| `Salt.MR.mrtA4ii_far_mid_unconditional` | Salt/MR/A4FMidRange.lean:457 | characters |
| `Salt.MR.mrtA4ii_far_mid34_unconditional` | Salt/MR/A4FMidRange.lean:473 | characters |
| `Salt.MR.mrtA4ii_far34_C` | Salt/MR/A4FThreshold.lean:42 | characters |
| `Salt.MR.far34_threshold_close` | Salt/MR/A4FThreshold.lean:75 | characters |
| `Salt.MR.mrtLemmaA4iiFixed34T_mid` | Salt/MR/A4FThreshold.lean:165 | characters |
| `Salt.MR.fourierCoeff_absCosCircle` | Salt/MR/AbsCosFourier.lean:105 | characters, exponential sums |
| `Salt.MR.summable_fourierCoeff_absCosCircle` | Salt/MR/AbsCosFourier.lean:191 | characters, exponential sums |
| `Salt.MR.hasSum_absCos_harmonics` | Salt/MR/AbsCosFourier.lean:236 | characters |
| `Salt.MR.hasSum_absCos_tail_weights` | Salt/MR/AbsCosFourier.lean:322 | characters |
| `Salt.MR.absCos_weight_partial_sum` | Salt/MR/AbsCosFourier.lean:370 | characters |
| `Salt.MR.abs_cos_partial_fourier_bound` | Salt/MR/AbsCosFourier.lean:390 | characters |
| `Salt.MR.one_sided_majorant_head_floor` | Salt/MR/AbsCosFourier.lean:470 | characters |
| `Salt.MR.logChowlaAffSupply_one_zero` | Salt/MR/AffineSupplyH.lean:37 | characters |
| `Salt.MR.oddOmega_twinProd_infinite` | Salt/MR/AffineSupplyH.lean:50 | characters |
| `Salt.MR.annHead_le_measure_sup` | Salt/MR/AnnHead.lean:71 | characters |
| `Salt.MR.annHead_grade` | Salt/MR/AnnHead.lean:143 | characters |
| `Salt.MR.annHead_le_socket` | Salt/MR/AnnHead.lean:201 | characters |
| `Salt.MR.T1_decay_annular` | Salt/MR/AnnHead.lean:302 | characters |
| `Salt.MR.prop_A3_T1_row_annular` | Salt/MR/AnnHead.lean:339 | characters |
| `Salt.MR.T1_decay_annular_tailed` | Salt/MR/AnnHead.lean:398 | characters |
| `Salt.MR.annHead_le_socket_T` | Salt/MR/AnnHead.lean:590 | characters |
| `Salt.MR.annHead_le_socket_polyT` | Salt/MR/AnnHead.lean:895 | characters |
| `Salt.MR.T1_decay_annular_polyT` | Salt/MR/AnnHead.lean:958 | characters |
| `Salt.MR.T1_decay_annular_tailed_polyT` | Salt/MR/AnnHead.lean:982 | characters |
| `Salt.MR.prop_A3_T1_row_annular_polyT` | Salt/MR/AnnHead.lean:1008 | characters |
| `Salt.MR.prop_A3_T1_row_annular_le` | Salt/MR/AnnHead.lean:1054 | characters |
| `Salt.MR.s15_log_calQK_L_one` | Salt/MR/ArithPageLinear.lean:67 | characters |
| `Salt.MR.s15_doorRowFloorL_ge` | Salt/MR/ArithPageLinear.lean:74 | characters |
| `Salt.MR.s15_log_calQK_L_one_pos` | Salt/MR/ArithPageLinear.lean:80 | characters |
| `Salt.MR.s15_loglogQ1_L_nonneg` | Salt/MR/ArithPageLinear.lean:88 | characters |
| `Salt.MR.s15_calP_L_one_pos` | Salt/MR/ArithPageLinear.lean:97 | characters |
| `Salt.MR.s15_calP_L_one_le_two` | Salt/MR/ArithPageLinear.lean:102 | characters |
| `Salt.MR.a2Level1_L_pos` | Salt/MR/ArithPageLinear.lean:130 | characters |
| `Salt.MR.a2Level1_L_nonneg` | Salt/MR/ArithPageLinear.lean:135 | characters |
| `Salt.MR.a2Level1_L_gk_eq` | Salt/MR/ArithPageLinear.lean:139 | characters |
| `Salt.MR.s15_a2Level1_L_exp` | Salt/MR/ArithPageLinear.lean:147 | characters |
| `Salt.MR.a2RowsSum'_L_le_a2RowsSum_L` | Salt/MR/ArithPageLinear.lean:179 | characters |
| `Salt.MR.a2RowsSum_L_gk_le` | Salt/MR/ArithPageLinear.lean:228 | characters |
| `Salt.MR.a2RowsSum'_L_gk_le` | Salt/MR/ArithPageLinear.lean:255 | characters |
| `Salt.MR.a2Mrow_L_gk_le` | Salt/MR/ArithPageLinear.lean:282 | characters |
| `Salt.MR.anchorL_of_anchor` | Salt/MR/ArithPageLinear.lean:296 | characters |
| `Salt.MR.m4_arith_anchor_of_C1_rho_L` | Salt/MR/ArithPageLinear.lean:397 | characters |
| `Salt.MR.m4_arith_jfloorL_of_row` | Salt/MR/ArithPageLinear.lean:413 | characters |
| `Salt.MR.doorGrade_summand2_priced_rho_L` | Salt/MR/ArithPageLinear.lean:443 | characters |
| `Salt.MR.a2DoorGrade_L_nonneg` | Salt/MR/ArithPageLinear.lean:510 | characters |
| `Salt.MR.log_calP_one_gen` | Salt/MR/ArithPageLinear.lean:576 | characters |
| `Salt.MR.s15_gP1_of_budget_gen` | Salt/MR/ArithPageLinear.lean:584 | characters |
| `Salt.MR.s15_p2_of_budget_gen` | Salt/MR/ArithPageLinear.lean:617 | characters |
| `Salt.MR.s15_level1_L_of_budget` | Salt/MR/ArithPageLinear.lean:651 | characters |
| `Salt.MR.doorRowFloor_le_doorRowFloorL` | Salt/MR/ArithPageLinear.lean:688 | characters |
| `Salt.MR.a2DoorGrade_pool_L_nonneg` | Salt/MR/ArithPageLinear.lean:806 | characters |
| `Salt.MR.gRowsZeroGate'''_L_of_budget` | Salt/MR/ArithPageLinear.lean:897 | characters |
| `Salt.MR.exp_budget_le` | Salt/MR/BallSup.lean:165 | characters |
| `Salt.MR.center_to_ball_transfer` | Salt/MR/BallSup.lean:207 | characters |
| `Salt.MR.transfer_at_scale` | Salt/MR/BallSup.lean:307 | characters |
| `Salt.MR.spolyA_datum_split` | Salt/MR/BallSup.lean:359 | characters |
| `Salt.MR.ball_sup_of_center` | Salt/MR/BallSup.lean:473 | characters |
| `Salt.MR.halasz_direct_ball_window_free` | Salt/MR/BallSup.lean:635 | zeros, characters |
| `Salt.MR.log_golden_le_one` | Salt/MR/BandRated.lean:74 | characters |
| `Salt.MR.goldenL1_pos` | Salt/MR/BandRated.lean:85 | characters |
| `Salt.MR.goldenL1_le_one` | Salt/MR/BandRated.lean:91 | characters |
| `Salt.MR.goldenL1_le_LFunction_one` | Salt/MR/BandRated.lean:100 | characters |
| `Salt.MR.chi_Llower_band_real_rated` | Salt/MR/BandRated.lean:124 | characters |
| `Salt.MR.chi_Llower_band_real_rated'` | Salt/MR/BandRated.lean:150 | characters |
| `Salt.MR.LFunction_band_lower_principal_uniform` | Salt/MR/BandRated.lean:174 | characters |
| `Salt.MR.chi_Llower_band_realclass_rated` | Salt/MR/BandRated.lean:230 | characters |
| `Salt.MR.chi_floor_band_realclass_rated` | Salt/MR/BandRated.lean:288 | characters |
| `Salt.MR.chi_floor_band_realclass_quarter` | Salt/MR/BandRated.lean:341 | characters |
| `Salt.MR.margin_band_threshold_rated` | Salt/MR/BandRated.lean:405 | characters |
| `Salt.MR.diskConst_ge_head` | Salt/MR/BandRatedAssembly.lean:51 | characters |
| `Salt.MR.bandConstQ_nonneg` | Salt/MR/BandRatedAssembly.lean:71 | characters |
| `Salt.MR.capFreeFloor3_margin_all_chi_vt_rated` | Salt/MR/BandRatedAssembly.lean:108 | characters |
| `Salt.MR.bandConstQ_le_of_le_arcDen` | Salt/MR/BandRatedAssembly.lean:189 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum_vt_rated` | Salt/MR/BandRatedAssembly.lean:271 | characters |
| `Salt.MR.pieceFloor_vt_threshold_of_loglog_rated` | Salt/MR/BandRatedAssembly.lean:309 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum_arcDen_rated` | Salt/MR/BandRatedAssembly.lean:343 | characters |
| `Salt.MR.log_golden_ge_log_two` | Salt/MR/BandRatedSocket.lean:49 | characters |
| `Salt.MR.scaleGate_le_quintic` | Salt/MR/BandRatedSocket.lean:61 | characters |
| `Salt.MR.nearRat_neg` | Salt/MR/BigXiArc.lean:196 | characters |
| `Salt.MR.exists_dirichlet_approx` | Salt/MR/BigXiArc.lean:229 | characters |
| `Salt.MR.nearRat_of_pos` | Salt/MR/BigXiArc.lean:254 | characters |
| `Salt.MR.one_le_arcDen` | Salt/MR/BigXiArc.lean:300 | characters |
| `Salt.MR.arcRadius_pos` | Salt/MR/BigXiArc.lean:305 | characters |
| `Salt.MR.arcDen_mono` | Salt/MR/BigXiArc.lean:312 | characters |
| `Salt.MR.arcRadius_mono` | Salt/MR/BigXiArc.lean:317 | characters |
| `Salt.MR.not_mem_bigXi_of_norm_lt` | Salt/MR/BigXiArc.lean:382 | characters, exponential sums |
| `Salt.MR.norm_expSum_le_sum` | Salt/MR/BigXiArc.lean:388 | characters, exponential sums |
| `Salt.MR.threshold_le_sum_inv_of_mem` | Salt/MR/BigXiArc.lean:405 | characters |
| `Salt.MR.primeWindow_bounds` | Salt/MR/BigXiArc.lean:419 | characters |
| `Salt.MR.inv_p_le_of_mem` | Salt/MR/BigXiArc.lean:439 | characters |
| `Salt.MR.le_inv_p_of_mem` | Salt/MR/BigXiArc.lean:450 | characters |
| `Salt.MR.norm_expSum_le_card` | Salt/MR/BigXiArc.lean:458 | characters, exponential sums |
| `Salt.MR.nearRat_arc_zero` | Salt/MR/BigXiArc.lean:494 | characters |
| `Salt.MR.arcDen_nonneg` | Salt/MR/BigXiArc.lean:574 | characters |
| `Salt.MR.nearRatTight_neg` | Salt/MR/BigXiArc.lean:614 | characters |
| `Salt.MR.nearRatTight_zero` | Salt/MR/BigXiArc.lean:634 | characters |
| `Salt.MR.nearRatTight_arc_zero` | Salt/MR/BigXiArc.lean:773 | characters |
| `Salt.MR.crossKer_sigma_bound` | Salt/MR/BridgeAdapt.lean:262 | characters |
| `Salt.MR.bridge_adapter` | Salt/MR/BridgeAdapt.lean:378 | characters |
| `Salt.MR.sigma_wiring_of_crossKer` | Salt/MR/BridgeAdapt.lean:425 | characters |
| `Salt.MR.loglog_absorb` | Salt/MR/BridgeAdapt.lean:494 | characters |
| `Salt.MR.loglog_absorb_pow` | Salt/MR/BridgeAdapt.lean:548 | characters |
| `Salt.MR.pretDistSq_ellLin_eq` | Salt/MR/CapFreeArm.lean:97 | characters |
| `Salt.MR.capFreeFloor_of_row_floor` | Salt/MR/CapFreeArm.lean:119 | characters |
| `Salt.MR.box_gate_le_X` | Salt/MR/CapFreeArm.lean:166 | characters |
| `Salt.MR.ball_leg_vacuous_at_zero` | Salt/MR/CapFreeArm.lean:250 | characters |
| `Salt.MR.capFreeFloor3_of_row_floor` | Salt/MR/CapFreeArm3.lean:89 | characters |
| `Salt.MR.box_gate_le_3X` | Salt/MR/CapFreeArm3.lean:126 | characters |
| `Salt.MR.ramR_sum_fin` | Salt/MR/CapFreeArm3.lean:273 | characters |
| `Salt.MR.cff_scale_facts` | Salt/MR/CapFreeAssembly.lean:133 | characters |
| `Salt.MR.cff_box_loglog` | Salt/MR/CapFreeAssembly.lean:168 | characters |
| `Salt.MR.cff_box_logloglog` | Salt/MR/CapFreeAssembly.lean:193 | characters |
| `Salt.MR.primeDivSum_le_modulus` | Salt/MR/CapFreeAssembly.lean:235 | characters |
| `Salt.MR.chi_floor_real_bulk` | Salt/MR/CapFreeAssembly.lean:284 | characters |
| `Salt.MR.chi_floor_band_arm` | Salt/MR/CapFreeAssembly.lean:319 | characters |
| `Salt.MR.capFreeFloor3_all_chi` | Salt/MR/CapFreeAssembly.lean:360 | characters |
| `Salt.MR.capFreeFloor_all_chi` | Salt/MR/CapFreeAssembly.lean:408 | characters |
| `Salt.MR.cffK_nonneg` | Salt/MR/CapFreeAssembly.lean:428 | characters |
| `Salt.MR.cffK_spec` | Salt/MR/CapFreeAssembly.lean:433 | characters |
| `Salt.MR.pretDistSq_liouChi_eq` | Salt/MR/CapFreeAssembly.lean:465 | characters |
| `Salt.MR.norm_liouChi_le_one` | Salt/MR/CapFreeAssembly.lean:470 | characters |
| `Salt.MR.capFreeFloor3_liouChi_all` | Salt/MR/CapFreeAssembly.lean:488 | characters |
| `Salt.MR.primeDivSum_le_loglog` | Salt/MR/CapFreeSharp.lean:86 | characters |
| `Salt.MR.primeDivSum_max_le_mertensCap` | Salt/MR/CapFreeSharp.lean:116 | characters |
| `Salt.MR.mertensCap_nonneg` | Salt/MR/CapFreeSharp.lean:121 | characters |
| `Salt.MR.primeDivSum_le_mertensCap` | Salt/MR/CapFreeSharp.lean:130 | characters |
| `Salt.MR.mertensCap_le_of_le` | Salt/MR/CapFreeSharp.lean:153 | characters |
| `Salt.MR.chi_floor_real_bulk_sharp` | Salt/MR/CapFreeSharp.lean:178 | characters |
| `Salt.MR.capFreeFloor3_all_chi_sharp` | Salt/MR/CapFreeSharp.lean:217 | characters |
| `Salt.MR.capFreeFloor_all_chi_sharp` | Salt/MR/CapFreeSharp.lean:260 | characters |
| `Salt.MR.cffKSharp_nonneg` | Salt/MR/CapFreeSharp.lean:278 | characters |
| `Salt.MR.cffKSharp_spec` | Salt/MR/CapFreeSharp.lean:283 | characters |
| `Salt.MR.capFreeFloor3_liouChi_all_sharp` | Salt/MR/CapFreeSharp.lean:296 | characters |
| `Salt.MR.capFreeFloor3_margin_all_chi_sharp` | Salt/MR/CapFreeSharp.lean:313 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum_sharp` | Salt/MR/CapFreeSharp.lean:368 | characters |
| `Salt.MR.center_halasz_supply_YA` | Salt/MR/CaseASocket.lean:251 | characters |
| `Salt.MR.joint_supF_pin_at2C` | Salt/MR/CaseASocket.lean:466 | characters |
| `Salt.MR.joint_supF_pin_window2C` | Salt/MR/CaseASocket.lean:524 | characters |
| `Salt.MR.jointIntegrableAtC_pin2_free` | Salt/MR/CaseASocket.lean:595 | characters |
| `Salt.MR.center_halasz_supply_wideA` | Salt/MR/CaseAWide.lean:238 | characters |
| `Salt.MR.caseASwide_nonneg` | Salt/MR/CaseAWide.lean:387 | characters |
| `Salt.MR.window_sup_decay_center` | Salt/MR/CenterCore.lean:147 | zeros, characters |
| `Salt.MR.halasz_direct_center` | Salt/MR/CenterCore.lean:302 | zeros, characters |
| `Salt.MR.halasz_direct_center_gen` | Salt/MR/CenterCore.lean:371 | zeros, characters |
| `Salt.MR.ball_center_dichotomy` | Salt/MR/CenterCore.lean:531 | characters |
| `Salt.MR.ball_leg_empty_of_le` | Salt/MR/CenterCore.lean:547 | characters |
| `Salt.MR.ball_leg_of_center_small` | Salt/MR/CenterCore.lean:557 | characters |
| `Salt.MR.center_halasz_supply` | Salt/MR/CenterSupply.lean:296 | characters |
| `Salt.MR.ball_sup_supplied` | Salt/MR/CenterSupply.lean:471 | characters |
| `Salt.MR.char_plancherel` | Salt/MR/CharFold.lean:138 | characters |
| `Salt.MR.dpolyChi_eq_class_sum` | Salt/MR/CharFold.lean:192 | characters |
| `Salt.MR.sum_chi_meanSq_pointwise` | Salt/MR/CharFold.lean:209 | characters |
| `Salt.MR.sum_chi_meanSq_fold` | Salt/MR/CharFold.lean:224 | characters |
| `Salt.MR.log_norm_L_eq_re_tsum` | Salt/MR/ChiEuler.lean:107 | characters |
| `Salt.MR.chi_peel_sum_bound` | Salt/MR/ChiEuler.lean:180 | characters |
| `Salt.MR.chi_euler_osc_bridge_unconditional` | Salt/MR/ChiEuler.lean:296 | characters |
| `Salt.MR.chi_dist_bridge` | Salt/MR/ChiEuler.lean:339 | characters |
| `Salt.MR.pretDistSq_pow_le` | Salt/MR/ChiFloor.lean:137 | characters |
| `Salt.MR.pretDist_pow_le` | Salt/MR/ChiFloor.lean:169 | characters |
| `Salt.MR.pretDistSq_chiPrin_ge` | Salt/MR/ChiFloor.lean:260 | characters |
| `Salt.MR.chi_floor_of_order` | Salt/MR/ChiFloor.lean:313 | characters |
| `Salt.MR.chi_floor_orderOf` | Salt/MR/ChiFloor.lean:356 | characters |
| `Salt.MR.chi_floor_orderOf_twisted` | Salt/MR/ChiFloor.lean:377 | characters |
| `Salt.MR.chi_floor_low_of_Llower` | Salt/MR/ChiFloorLow.lean:94 | characters |
| `Salt.MR.chi_floor_low_principal` | Salt/MR/ChiFloorLow.lean:161 | characters |
| `Salt.MR.chi_floor_all_principal` | Salt/MR/ChiFloorLow.lean:201 | characters |
| `Salt.MR.chi_floor_all_principal_twisted` | Salt/MR/ChiFloorLow.lean:230 | characters |
| `Salt.MR.chi_floor_all_of_Llower` | Salt/MR/ChiFloorLow.lean:262 | characters |
| `Salt.MR.chi_floor_all_of_Llower_twisted` | Salt/MR/ChiFloorLow.lean:286 | characters |
| `Salt.MR.chi_Llower_trivial` | Salt/MR/ChiLLower.lean:314 | characters |
| `Salt.MR.chi_floor_all_unconditional` | Salt/MR/ChiLLower.lean:550 | characters |
| `Salt.MR.chi_Llower_341` | Salt/MR/ChiLLower.lean:580 | characters |
| `Salt.MR.chi_floor_all_nonreal` | Salt/MR/ChiLLower.lean:686 | characters |
| `Salt.MR.chi_floor_all_nonreal_twisted` | Salt/MR/ChiLLower.lean:737 | characters |
| `Salt.MR.center_trivial_bound` | Salt/MR/CofactorBall.lean:97 | characters |
| `Salt.MR.damped_partial_trivial` | Salt/MR/CofactorBall.lean:114 | characters |
| `Salt.MR.spolyA_window_split` | Salt/MR/CofactorBall.lean:131 | characters |
| `Salt.MR.far_transfer_sup` | Salt/MR/CofactorBall.lean:217 | characters |
| `Salt.MR.spolyA_ramRcoeff_eq_integral` | Salt/MR/CofactorBall.lean:389 | characters |
| `Salt.MR.spolyA_ramRcoeff_le_of_damp` | Salt/MR/CofactorBall.lean:421 | characters |
| `Salt.MR.damped_partial_transfer` | Salt/MR/CofactorBall.lean:461 | characters |
| `Salt.MR.caseB_window_geometry` | Salt/MR/CofactorBall.lean:517 | characters |
| `Salt.MR.caseB_ramR_of_collided` | Salt/MR/CofactorBall.lean:538 | characters |
| `Salt.MR.log_le_two_sqrt` | Salt/MR/CofactorBall.lean:635 | characters |
| `Salt.MR.collisionGate_discharged` | Salt/MR/CofactorBall.lean:677 | characters |
| `Salt.MR.cofk_two_le_exp_31_32` | Salt/MR/CofactorBulk.lean:103 | characters |
| `Salt.MR.cofkL_ramRbot_le_kk` | Salt/MR/CofactorBulk.lean:114 | characters |
| `Salt.MR.cofkL_one_le_kk` | Salt/MR/CofactorBulk.lean:120 | characters |
| `Salt.MR.cofkL_sqrt_le_kk` | Salt/MR/CofactorBulk.lean:127 | characters |
| `Salt.MR.cofkL_pin2_le_kk` | Salt/MR/CofactorBulk.lean:137 | characters |
| `Salt.MR.cofkL_Mt_le_two_ramRbot` | Salt/MR/CofactorBulk.lean:145 | characters |
| `Salt.MR.four_le_ballQuarterThreshold` | Salt/MR/CofactorBulk.lean:153 | characters |
| `Salt.MR.cofkL_five_le_ramRbot` | Salt/MR/CofactorBulk.lean:161 | characters |
| `Salt.MR.cofkL_two_ramRbot_le` | Salt/MR/CofactorBulk.lean:170 | characters |
| `Salt.MR.blockWindow_mertens_pin` | Salt/MR/CofactorDist.lean:178 | characters |
| `Salt.MR.theta293_self_consistent` | Salt/MR/CofactorDist.lean:257 | characters |
| `Salt.MR.exit_margin_293` | Salt/MR/CofactorDist.lean:277 | characters |
| `Salt.MR.exit_margin_293_sharp` | Salt/MR/CofactorDist.lean:284 | characters |
| `Salt.MR.exit_beats_c0_293` | Salt/MR/CofactorDist.lean:299 | characters |
| `Salt.MR.loglog_absorb_293` | Salt/MR/CofactorDist.lean:323 | characters |
| `Salt.MR.pin_P83_le_Q83_293` | Salt/MR/CofactorDist.lean:329 | characters |
| `Salt.MR.dist_one_shift_le_of_two_caps_asym` | Salt/MR/CofactorDist.lean:357 | characters |
| `Salt.MR.pocket_collision_abstract` | Salt/MR/CofactorDist.lean:388 | characters |
| `Salt.MR.pocket_collision` | Salt/MR/CofactorDist.lean:438 | characters |
| `Salt.MR.pocket_collision_pin` | Salt/MR/CofactorDist.lean:530 | characters |
| `Salt.MR.collisionGate_of_five` | Salt/MR/CofactorDist.lean:602 | characters |
| `Salt.MR.pocket_collision_window` | Salt/MR/CofactorDist.lean:619 | characters |
| `Salt.MR.pocket_far_from_ball` | Salt/MR/CofactorDist.lean:646 | characters |
| `Salt.MR.pocket_ball_shrink` | Salt/MR/CofactorDist.lean:656 | characters |
| `Salt.MR.center_halasz_supply_A` | Salt/MR/CofactorGrade.lean:265 | characters |
| `Salt.MR.caseA_damped_partial` | Salt/MR/CofactorGrade.lean:579 | characters |
| `Salt.MR.caseA_ramR_of_supplied` | Salt/MR/CofactorGrade.lean:642 | characters |
| `Salt.MR.caseA_grade_numeral` | Salt/MR/CofactorGrade.lean:755 | characters |
| `Salt.MR.Tstar_window_mono` | Salt/MR/CofactorLocal.lean:77 | characters |
| `Salt.MR.contour_gate_local_iff` | Salt/MR/CofactorLocal.lean:92 | characters |
| `Salt.MR.pocket_transport_local` | Salt/MR/CofactorLocal.lean:128 | characters |
| `Salt.MR.log_Tstar_self` | Salt/MR/CofactorLocal.lean:436 | characters |
| `Salt.MR.farErr_local_le` | Salt/MR/CofactorLocal.lean:464 | characters |
| `Salt.MR.farErr_local_of_gate` | Salt/MR/CofactorLocal.lean:520 | characters |
| `Salt.MR.farErr_local_window_ge` | Salt/MR/CofactorLocal.lean:540 | characters |
| `Salt.MR.prod_one_sub_gJ_expand` | Salt/MR/CofactorSupplier.lean:136 | characters |
| `Salt.MR.doorCofactor0_split` | Salt/MR/CofactorSupplier.lean:160 | characters |
| `Salt.MR.ramR_sum_finset` | Salt/MR/CofactorSupplier.lean:190 | characters |
| `Salt.MR.doorCofactor0_at_one` | Salt/MR/CofactorSupplier.lean:219 | characters |
| `Salt.MR.pretDistSq_pieceDatum_ge` | Salt/MR/CofactorSupplier.lean:307 | characters |
| `Salt.MR.capFreeFloor3_margin_all_chi` | Salt/MR/CofactorSupplier.lean:347 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum` | Salt/MR/CofactorSupplier.lean:405 | characters |
| `Salt.MR.pretDistSq_dampDatum_eq` | Salt/MR/CofactorSupplier.lean:456 | characters |
| `Salt.MR.box_gate_le_3X_gen` | Salt/MR/CofactorSupplier.lean:513 | characters |
| `Salt.MR.caseA_damped_partial_gen` | Salt/MR/CofactorSupplier.lean:567 | characters |
| `Salt.MR.damped_partial_transfer_34_gen` | Salt/MR/CofactorSupplier.lean:623 | characters |
| `Salt.MR.blockWindow_calibrated_debit` | Salt/MR/CofactorSupplier.lean:829 | characters |
| `Salt.MR.blockWindow_calibrated_debit_sum` | Salt/MR/CofactorSupplier.lean:871 | characters |
| `Salt.MR.dampDatum_isMultiplicative` | Salt/MR/CofactorSupplier.lean:936 | characters |
| `Salt.MR.ellLin_dampDatum` | Salt/MR/CofactorSupplier.lean:945 | characters |
| `Salt.MR.caseA_dissect_gen` | Salt/MR/CofactorSupplier.lean:953 | characters |
| `Salt.MR.caseASocketGen_of_inner` | Salt/MR/CofactorSupplier.lean:979 | characters |
| `Salt.MR.pretDistSq_tail_le` | Salt/MR/CofactorSupply.lean:140 | characters |
| `Salt.MR.caseA_floor_slot` | Salt/MR/CofactorSupply.lean:187 | characters |
| `Salt.MR.gxDatum_trivial_window` | Salt/MR/CofactorSupply.lean:200 | characters |
| `Salt.MR.cofactorRbd_nonneg` | Salt/MR/CofactorSupply.lean:267 | characters |
| `Salt.MR.pocket_transport` | Salt/MR/CofactorSupply.lean:293 | characters |
| `Salt.MR.descent_tail_le` | Salt/MR/CofactorSupply.lean:518 | characters |
| `Salt.MR.cofactorMfl_nonneg_of_descent` | Salt/MR/CofactorSupply.lean:579 | characters |
| `Salt.MR.cofactorMfl_grade_293` | Salt/MR/CofactorSupply.lean:605 | characters |
| `Salt.MR.exists_min_dist_on_Icc` | Salt/MR/CompactMin.lean:123 | characters |
| `Salt.MR.exists_min_dist_abs` | Salt/MR/CompactMin.lean:133 | characters |
| `Salt.MR.pretDistSq_freq_lipschitz` | Salt/MR/CompactMin.lean:177 | characters |
| `Salt.MR.dist_one_shift_le_of_two_caps` | Salt/MR/CompactMin.lean:244 | characters |
| `Salt.MR.overhang_no_undercut` | Salt/MR/CompactMin.lean:281 | characters |
| `Salt.MR.compact_min_package` | Salt/MR/CompactMin.lean:342 | characters |
| `Salt.MR.Cg_le` | Salt/MR/ConstantsExposed.lean:126 | characters |
| `Salt.MR.typical_density_le_bounded` | Salt/MR/ConstantsExposed.lean:138 | characters |
| `Salt.MR.eps_admissible` | Salt/MR/ConstantsExposed.lean:211 | characters |
| `Salt.MR.Klcm_le` | Salt/MR/ConstantsExposed.lean:255 | characters |
| `Salt.MR.KExpr_le` | Salt/MR/ConstantsExposed.lean:356 | characters |
| `Salt.MR.delta0_ge` | Salt/MR/ConstantsExposed.lean:393 | characters |
| `Salt.MR.b_floor_cert` | Salt/MR/ConstantsExposed.lean:410 | characters |
| `Salt.MR.ramare_weight_sum` | Salt/MR/Decomp.lean:119 | characters |
| `Salt.MR.ramare_decomp` | Salt/MR/Decomp.lean:190 | characters |
| `Salt.MR.pretDistSq_principal_eval` | Salt/MR/Dist.lean:95 | characters |
| `Salt.MR.prime_power_tail_le` | Salt/MR/Dist.lean:129 | characters |
| `Salt.MR.dist_one_floor_pow` | Salt/MR/DistHalasz.lean:179 | characters |
| `Salt.MR.Mrange_one_floor` | Salt/MR/DistHalasz.lean:276 | characters |
| `Salt.MR.dist_recenter` | Salt/MR/DistSplit.lean:126 | characters |
| `Salt.MR.dist_split_A4` | Salt/MR/DistSplit.lean:174 | characters |
| `Salt.MR.dist_split_fgJ` | Salt/MR/DistSplit.lean:201 | characters |
| `Salt.MR.dist_window_restrict` | Salt/MR/DistWindow.lean:92 | characters |
| `Salt.MR.out_of_window_mass_le` | Salt/MR/DistWindow.lean:266 | characters |
| `Salt.MR.dist_split_A4_N2` | Salt/MR/DistWindow.lean:329 | characters |
| `Salt.MR.dist_split_A4_N2_windowed` | Salt/MR/DistWindow.lean:357 | characters |
| `Salt.MR.upper_tail_le` | Salt/MR/DistWindow.lean:492 | characters |
| `Salt.MR.dist_split_A4_N2_final` | Salt/MR/DistWindow.lean:596 | characters |
| `Salt.MR.regime_W_headroom_of_floor` | Salt/MR/DoorDischarge.lean:42 | characters |
| `Salt.MR.regime_W_cap_of_floor` | Salt/MR/DoorDischarge.lean:189 | characters |
| `Salt.MR.rpow_neg_anti` | Salt/MR/DoorFloor.lean:115 | characters |
| `Salt.MR.H0door_pos` | Salt/MR/DoorFloor.lean:126 | characters |
| `Salt.MR.exp_le_H0door` | Salt/MR/DoorFloor.lean:130 | characters |
| `Salt.MR.H0door_anti` | Salt/MR/DoorFloor.lean:135 | characters |
| `Salt.MR.doorGrade_pos` | Salt/MR/DoorFloor.lean:140 | characters |
| `Salt.MR.doorGrade_anti` | Salt/MR/DoorFloor.lean:145 | characters |
| `Salt.MR.log_ge_of_H0door_le` | Salt/MR/DoorFloor.lean:156 | characters |
| `Salt.MR.doorGrade_le_of_H0door_le` | Salt/MR/DoorFloor.lean:166 | characters |
| `Salt.MR.le_log_of_H0door_le` | Salt/MR/DoorFloor.lean:185 | characters |
| `Salt.MR.log_scale_threshold` | Salt/MR/DoorFloor.lean:200 | characters |
| `Salt.MR.regime_hthr_of_scale` | Salt/MR/DoorFloor.lean:220 | characters |
| `Salt.MR.regime_W_headroom_of_H0door` | Salt/MR/DoorFloor.lean:234 | characters |
| `Salt.MR.H0mrt_pos` | Salt/MR/DoorFloor.lean:359 | characters |
| `Salt.MR.HplusStar_pos` | Salt/MR/DoorFloor.lean:361 | characters |
| `Salt.MR.mrt_middle_le_of_H0mrt` | Salt/MR/DoorFloor.lean:378 | characters |
| `Salt.MR.mrt_tail_le_of_HplusStar70` | Salt/MR/DoorFloor.lean:420 | characters |
| `Salt.MR.mrt_tail_le_of_HplusStar` | Salt/MR/DoorFloor.lean:445 | characters |
| `Salt.MR.log_scale_threshold_1500` | Salt/MR/DoorFloor1500.lean:55 | characters |
| `Salt.MR.regime_hthr_of_scale_1500` | Salt/MR/DoorFloor1500.lean:75 | characters |
| `Salt.MR.regime_W_headroom_of_floor_1500` | Salt/MR/DoorFloor1500.lean:90 | characters |
| `Salt.MR.regime_W_headroom_of_H0door_1500` | Salt/MR/DoorFloor1500.lean:201 | characters |
| `Salt.MR.regime_head_W_headroom_1500` | Salt/MR/DoorFloor1500.lean:221 | characters |
| `Salt.MR.W_second_arm` | Salt/MR/DoorFloor1500.lean:250 | characters |
| `Salt.MR.W_second_arm_of_scale` | Salt/MR/DoorFloor1500.lean:273 | characters |
| `Salt.MR.door_L1_absorbed_w` | Salt/MR/DoorFloor1500.lean:291 | characters |
| `Salt.MR.door_L1_absorbed_12` | Salt/MR/DoorFloor1500.lean:309 | characters |
| `Salt.MR.door_L1_debit_absorbed_w` | Salt/MR/DoorFloor1500.lean:320 | characters |
| `Salt.MR.door_L1_debit_absorbed_12` | Salt/MR/DoorFloor1500.lean:338 | characters |
| `Salt.MR.Adoor_ge` | Salt/MR/DoorFrame.lean:86 | characters |
| `Salt.MR.Adoor_ge_old` | Salt/MR/DoorFrame.lean:91 | characters |
| `Salt.MR.one_le_Adoor` | Salt/MR/DoorFrame.lean:93 | characters |
| `Salt.MR.Adoor_cast` | Salt/MR/DoorFrame.lean:96 | characters |
| `Salt.MR.calE_door_two` | Salt/MR/DoorFrame.lean:106 | characters |
| `Salt.MR.log_four_M_door` | Salt/MR/DoorFrame.lean:123 | characters |
| `Salt.MR.log_calE_door_two` | Salt/MR/DoorFrame.lean:141 | characters |
| `Salt.MR.calFrameK_satisfiable_door` | Salt/MR/DoorFrame.lean:190 | characters |
| `Salt.MR.levelGates_calibrated_door` | Salt/MR/DoorFrame.lean:241 | characters |
| `Salt.MR.eq28_door_clears` | Salt/MR/DoorFrame.lean:252 | characters |
| `Salt.MR.log_calQK_door_one` | Salt/MR/DoorFrame.lean:264 | characters |
| `Salt.MR.Adoor_eq_four_mul` | Salt/MR/DoorFrameH1.lean:114 | characters |
| `Salt.MR.calP_door_one_ge` | Salt/MR/DoorFrameH1.lean:129 | characters |
| `Salt.MR.calP_door_one_rpow_quarter` | Salt/MR/DoorFrameH1.lean:141 | characters |
| `Salt.MR.one_le_log_calQK_door_one` | Salt/MR/DoorFrameH1.lean:170 | characters |
| `Salt.MR.H1door_two` | Salt/MR/DoorFrameH1.lean:189 | characters |
| `Salt.MR.H1door_cube` | Salt/MR/DoorFrameH1.lean:226 | characters |
| `Salt.MR.H1door_pin` | Salt/MR/DoorFrameH1.lean:245 | characters |
| `Salt.MR.calFrameK_satisfiable_doorH1` | Salt/MR/DoorFrameH1.lean:273 | characters |
| `Salt.MR.levelGates_calibrated_doorH1` | Salt/MR/DoorFrameH1.lean:297 | characters |
| `Salt.MR.mrAlpha_door_one` | Salt/MR/DoorFrameH1.lean:307 | characters |
| `Salt.MR.H1door_level1_identity` | Salt/MR/DoorFrameH1.lean:330 | characters |
| `Salt.MR.H1door_level1_certificate` | Salt/MR/DoorFrameH1.lean:355 | characters |
| `Salt.MR.level1_term_door_decays` | Salt/MR/DoorFrameH1.lean:438 | characters |
| `Salt.MR.calFrameK_satisfiable_doorH1_L` | Salt/MR/DoorLadderLinear.lean:281 | characters |
| `Salt.MR.level1_term_door_decays_L` | Salt/MR/DoorLadderLinear.lean:333 | characters |
| `Salt.MR.calFrameK_satisfiable_doorH1_L_gk` | Salt/MR/DoorLadderLinear.lean:393 | characters |
| `Salt.MR.calFrameK_satisfiable_scaled_L` | Salt/MR/DoorLadderLinear.lean:437 | characters |
| `Salt.MR.calFrameK_satisfiable_Ah_L` | Salt/MR/DoorLadderLinear.lean:554 | characters |
| `Salt.MR.memS_dilate_door_L` | Salt/MR/DoorLadderLinear.lean:738 | characters |
| `Salt.MR.residue_split_dilate_door_L_gk` | Salt/MR/DoorLadderLinear.lean:795 | characters |
| `Salt.MR.AdoorL_ge` | Salt/MR/DoorLinear.lean:84 | characters |
| `Salt.MR.AdoorL_ge_old` | Salt/MR/DoorLinear.lean:89 | characters |
| `Salt.MR.one_le_AdoorL` | Salt/MR/DoorLinear.lean:92 | characters |
| `Salt.MR.Adoor_le_AdoorL` | Salt/MR/DoorLinear.lean:98 | characters |
| `Salt.MR.AdoorL_cast` | Salt/MR/DoorLinear.lean:105 | characters |
| `Salt.MR.calE_doorL_two` | Salt/MR/DoorLinear.lean:115 | characters |
| `Salt.MR.calE_doorL_two_gk` | Salt/MR/DoorLinear.lean:122 | characters |
| `Salt.MR.log_calE_doorL_two` | Salt/MR/DoorLinear.lean:139 | characters |
| `Salt.MR.log_calE_doorL_two_gk` | Salt/MR/DoorLinear.lean:165 | characters |
| `Salt.MR.log_four_M_doorL` | Salt/MR/DoorLinear.lean:193 | characters |
| `Salt.MR.log_gate_doorL` | Salt/MR/DoorLinear.lean:203 | characters |
| `Salt.MR.log_gate_doorL_gk` | Salt/MR/DoorLinear.lean:218 | characters |
| `Salt.MR.calFrameK_satisfiable_doorL` | Salt/MR/DoorLinear.lean:248 | characters |
| `Salt.MR.calFrameK_satisfiable_doorL_gk` | Salt/MR/DoorLinear.lean:300 | characters |
| `Salt.MR.levelGates_calibrated_doorL` | Salt/MR/DoorLinear.lean:360 | characters |
| `Salt.MR.levelGates_calibrated_doorL_gk` | Salt/MR/DoorLinear.lean:368 | characters |
| `Salt.MR.eq28_doorL_clears` | Salt/MR/DoorLinear.lean:378 | characters |
| `Salt.MR.eq28_doorL_clears_gk` | Salt/MR/DoorLinear.lean:387 | characters |
| `Salt.MR.log_calQK_doorL_one` | Salt/MR/DoorLinear.lean:398 | characters |
| `Salt.MR.log_calQK_doorL_one_gk` | Salt/MR/DoorLinear.lean:406 | characters |
| `Salt.MR.calP_doorL_one_gk` | Salt/MR/DoorLinear.lean:413 | characters |
| `Salt.MR.s11_calE_doorL_two` | Salt/MR/DoorLinear.lean:426 | characters |
| `Salt.MR.s11_log_calQK_doorL_two` | Salt/MR/DoorLinear.lean:432 | characters |
| `Salt.MR.s11_log_calP_doorL_one` | Salt/MR/DoorLinear.lean:442 | characters |
| `Salt.MR.s11_calE_doorL_two_gk` | Salt/MR/DoorLinear.lean:449 | characters |
| `Salt.MR.s11_log_calQK_doorL_two_gk` | Salt/MR/DoorLinear.lean:456 | characters |
| `Salt.MR.doorRowFloorL_eq` | Salt/MR/DoorLinear.lean:532 | characters |
| `Salt.MR.s13_calQK_doorL_one` | Salt/MR/DoorLinear.lean:537 | characters |
| `Salt.MR.s13_calQK_doorL_two` | Salt/MR/DoorLinear.lean:543 | characters |
| `Salt.MR.doorL_length_gate` | Salt/MR/DoorLinear.lean:550 | characters |
| `Salt.MR.doorL_length_gate_iff` | Salt/MR/DoorLinear.lean:560 | characters |
| `Salt.MR.flat_door_head_xceil` | Salt/MR/DoorReceipt.lean:1001 | characters |
| `Salt.MR.logChowla2_v7_rated_form` | Salt/MR/DoorReceipt.lean:1086 | characters |
| `Salt.MR.logChowla2_v7_rated_of_generic` | Salt/MR/DoorReceipt.lean:1094 | characters |
| `Salt.MR.mrtDoorReceipt_v7_form` | Salt/MR/DoorReceipt.lean:1100 | characters |
| `Salt.MR.mrtUniformityXiL2_holds_flat` | Salt/MR/DoorReceipt.lean:1110 | characters |
| `Salt.MR.mrtUniformityXi_holds_flat` | Salt/MR/DoorReceipt.lean:1173 | characters |
| `Salt.MR.strataTerm_le_dyadic` | Salt/MR/DoorRoadCompose.lean:119 | characters |
| `Salt.MR.sum_progression_le_sum_Ioc` | Salt/MR/DoorRoadCompose.lean:185 | characters |
| `Salt.MR.strata_modulus_pos` | Salt/MR/DoorRoadCompose.lean:220 | characters |
| `Salt.MR.strata_modulus_within_arc` | Salt/MR/DoorRoadCompose.lean:228 | characters |
| `Salt.MR.strata_capstone_applicable` | Salt/MR/DoorRoadCompose.lean:239 | characters |
| `Salt.MR.progression_mem_Ioc_of_window_in_block` | Salt/MR/DoorRoadCompose.lean:260 | characters |
| `Salt.MR.sum_progression_le_sum_Ioc_of_window` | Salt/MR/DoorRoadCompose.lean:274 | characters |
| `Salt.MR.doorLadder_block_length_ge` | Salt/MR/DoorRoadCompose.lean:320 | characters |
| `Salt.MR.doorLadder_block_length_lt` | Salt/MR/DoorRoadCompose.lean:329 | characters |
| `Salt.MR.sum_swap_dyadic` | Salt/MR/DoorRoadCompose.lean:350 | characters |
| `Salt.MR.sum_swap_dyadic_at_door` | Salt/MR/DoorRoadCompose.lean:366 | sieves, characters |
| `Salt.MR.sum_Ioc_shift_at_door` | Salt/MR/DoorRoadCompose.lean:402 | sieves, characters |
| `Salt.MR.shift_le_cap` | Salt/MR/DoorRoadCompose.lean:414 | characters |
| `Salt.MR.lemma5R` | Salt/MR/Eq26Bridge.lean:123 | characters |
| `Salt.MR.lemma5_budget_diff` | Salt/MR/Eq26Bridge.lean:142 | characters |
| `Salt.MR.one_le_log_of_exp_le` | Salt/MR/Eq26Bridge.lean:175 | characters |
| `Salt.MR.hTwo_pos` | Salt/MR/Eq26Bridge.lean:181 | characters |
| `Salt.MR.hTwo_le_self` | Salt/MR/Eq26Bridge.lean:189 | characters |
| `Salt.MR.hTwo_eq_mul_rpow_neg` | Salt/MR/Eq26Bridge.lean:202 | characters |
| `Salt.MR.gJR_one` | Salt/MR/Eq26Bridge.lean:257 | characters |
| `Salt.MR.gJR_mul` | Salt/MR/Eq26Bridge.lean:266 | characters |
| `Salt.MR.blockOmega_pow_eq_zero_iff` | Salt/MR/Eq26Bridge.lean:275 | characters |
| `Salt.MR.gJR_abs_le_one` | Salt/MR/Eq26Bridge.lean:303 | characters |
| `Salt.MR.window_defect_bound` | Salt/MR/Eq26Bridge.lean:346 | characters |
| `Salt.MR.shortSum_eq26_window` | Salt/MR/Eq26Bridge.lean:380 | characters |
| `Salt.MR.sec9_R_eq_zero_of_card` | Salt/MR/Eq26Bridge.lean:447 | characters |
| `Salt.MR.shortSum_measurable'` | Salt/MR/Eq26Compose.lean:150 | characters |
| `Salt.MR.shortSum_sub_const_sq_intervalIntegrable` | Salt/MR/Eq26Compose.lean:188 | characters |
| `Salt.MR.rpow_inv20_sq` | Salt/MR/Eq26Compose.lean:224 | characters |
| `Salt.MR.one_div_rpow_absorb` | Salt/MR/Eq26Compose.lean:232 | characters |
| `Salt.MR.meansq_shift_of_pointwise` | Salt/MR/Eq26Compose.lean:246 | characters |
| `Salt.MR.hTwo_meets_kernel_binder` | Salt/MR/Eq26Compose.lean:432 | characters |
| `Salt.MR.eq26_carrier_hrange` | Salt/MR/Eq26Compose.lean:439 | characters |
| `Salt.MR.chebyshev_exceptional_set` | Salt/MR/Eq26Compose.lean:513 | characters |
| `Salt.MR.thm3_chebyshev_exceptional` | Salt/MR/Eq26Compose.lean:594 | characters |
| `Salt.MR.thm3_pair_exceptional` | Salt/MR/Eq26Compose.lean:648 | characters |
| `Salt.MR.thm3_pair_nonvacuous` | Salt/MR/Eq26Compose.lean:698 | characters |
| `Salt.MR.calFrameK_satisfiable_scaled` | Salt/MR/Eq26Compose.lean:783 | characters |
| `Salt.MR.Ah_mul_le` | Salt/MR/Eq26Compose.lean:878 | characters |
| `Salt.MR.Ah_one_sided` | Salt/MR/Eq26Compose.lean:891 | characters |
| `Salt.MR.Ah_containment` | Salt/MR/Eq26Compose.lean:909 | characters |
| `Salt.MR.calFrameK_satisfiable_Ah` | Salt/MR/Eq26Compose.lean:929 | characters |
| `Salt.MR.levelGates_calibrated_Ah` | Salt/MR/Eq26Compose.lean:945 | characters |
| `Salt.MR.e4a_zeta_isPrimitiveRoot` | Salt/MR/EvenChiAlgebra.lean:34 | characters |
| `Salt.MR.e4a_fixed_isRational` | Salt/MR/EvenChiAlgebra.lean:47 | characters |
| `Salt.MR.e4a_descent_to_int` | Salt/MR/EvenChiAlgebra.lean:53 | characters |
| `Salt.MR.e4a_fibre_fix` | Salt/MR/EvenChiAlgebra.lean:92 | characters |
| `Salt.MR.e4a_prod_fibre_swap` | Salt/MR/EvenChiAlgebra.lean:133 | characters |
| `Salt.MR.e4a_prod_fibre_fix` | Salt/MR/EvenChiAlgebra.lean:142 | characters |
| `Salt.MR.e4a_fibre_swap'` | Salt/MR/EvenChiAlgebra.lean:163 | characters |
| `Salt.MR.e4a_prod_fibre_swap'` | Salt/MR/EvenChiAlgebra.lean:181 | characters |
| `Salt.MR.e4a_eta_inverts` | Salt/MR/EvenChiAlgebra.lean:192 | characters |
| `Salt.MR.e4a_sum_inv_fixed` | Salt/MR/EvenChiAlgebra.lean:224 | characters |
| `Salt.MR.e4a_sum_inv_fixed_alg` | Salt/MR/EvenChiAlgebra.lean:232 | characters |
| `Salt.MR.e4a_eta_sum_is_integer` | Salt/MR/EvenChiAlgebra.lean:240 | characters |
| `Salt.MR.e4a_sum_isIntegral_of_both` | Salt/MR/EvenChiAlgebra.lean:268 | characters |
| `Salt.MR.e4a_spine` | Salt/MR/EvenChiAlgebra.lean:273 | characters |
| `Salt.MR.e4a_pow_mod_gen` | Salt/MR/EvenChiAlgebra.lean:279 | characters |
| `Salt.MR.e4a_pow_val_mul_gen` | Salt/MR/EvenChiAlgebra.lean:284 | characters |
| `Salt.MR.e4a_fibre_fix'` | Salt/MR/EvenChiAlgebra.lean:303 | characters |
| `Salt.MR.e4a_prod_fibre_fix'` | Salt/MR/EvenChiAlgebra.lean:321 | characters |
| `Salt.MR.e4a_eta_fixed` | Salt/MR/EvenChiAlgebra.lean:347 | characters |
| `Salt.MR.e4a_associated_quotient_eq` | Salt/MR/EvenChiAlgebra.lean:371 | characters |
| `Salt.MR.e4a_prod_associated_gen` | Salt/MR/EvenChiAlgebra.lean:389 | characters |
| `Salt.MR.e4a_assoc_of_card_eq_gen` | Salt/MR/EvenChiAlgebra.lean:406 | characters |
| `Salt.MR.e4a_descent_needs_integrality` | Salt/MR/EvenChiControls.lean:61 | characters |
| `Salt.MR.e4a_descent_holds_when_integral` | Salt/MR/EvenChiControls.lean:72 | characters |
| `Salt.MR.e4a_gaussSum_real_of_primitive` | Salt/MR/EvenChiControls.lean:94 | characters, exponential sums |
| `Salt.MR.e4a_gaussSum_odd_inv_addChar` | Salt/MR/EvenChiControls.lean:109 | characters, exponential sums |
| `Salt.MR.e4a_gaussSum_odd_re_zero` | Salt/MR/EvenChiControls.lean:118 | characters, exponential sums |
| `Salt.MR.e4a_gaussSum_mutant_is_false` | Salt/MR/EvenChiControls.lean:130 | characters, exponential sums |
| `Salt.MR.e4a_toC_vanishes_off_units` | Salt/MR/EvenChiControls.lean:167 | characters |
| `Salt.MR.e4a_toC_signOf_mutant_is_false` | Salt/MR/EvenChiControls.lean:171 | characters |
| `Salt.MR.e4a_ruled_hypothesis_probe` | Salt/MR/EvenChiControls.lean:215 | characters |
| `Salt.MR.e4a_two_cosh_log` | Salt/MR/EvenChiCosh.lean:34 | characters |
| `Salt.MR.e4a_cosh_integer_of_sum` | Salt/MR/EvenChiCosh.lean:43 | characters |
| `Salt.MR.e4a_cosh_sign_free` | Salt/MR/EvenChiCosh.lean:51 | characters |
| `Salt.MR.e4a_golden_sq` | Salt/MR/EvenChiCosh.lean:70 | characters |
| `Salt.MR.e4a_cosh_floor` | Salt/MR/EvenChiCosh.lean:76 | characters |
| `Salt.MR.e4a_two_lt_two_cosh` | Salt/MR/EvenChiCosh.lean:113 | characters |
| `Salt.MR.e4a_int_ge_three_of_two_lt` | Salt/MR/EvenChiCosh.lean:118 | characters |
| `Salt.MR.e4a_E5_floor` | Salt/MR/EvenChiCosh.lean:126 | characters |
| `Salt.MR.e4a_cosh_neg_free` | Salt/MR/EvenChiCosh.lean:147 | characters |
| `Salt.MR.e4a_cosh_of_pm` | Salt/MR/EvenChiCosh.lean:151 | characters |
| `Salt.MR.e4a_cosh_integer_of_pm` | Salt/MR/EvenChiCosh.lean:158 | characters |
| `Salt.MR.e4a_step1_associated` | Salt/MR/EvenChiCyclotomic.lean:57 | characters |
| `Salt.MR.e4a_step2_unit_ratio` | Salt/MR/EvenChiCyclotomic.lean:62 | characters |
| `Salt.MR.e4a_prod_associated` | Salt/MR/EvenChiCyclotomic.lean:71 | characters |
| `Salt.MR.e4a_step4_equal_card_associated` | Salt/MR/EvenChiCyclotomic.lean:88 | characters |
| `Salt.MR.e4a_step5_unit_witness` | Salt/MR/EvenChiCyclotomic.lean:99 | characters |
| `Salt.MR.e4a_pair_mul_one` | Salt/MR/EvenChiCyclotomic.lean:113 | characters |
| `Salt.MR.e4a_conj_eq_pair` | Salt/MR/EvenChiCyclotomic.lean:120 | characters |
| `Salt.MR.e4a_step7_pair_product` | Salt/MR/EvenChiCyclotomic.lean:138 | characters |
| `Salt.MR.e4a_prod_associated_concrete` | Salt/MR/EvenChiCyclotomic.lean:154 | characters |
| `Salt.MR.e4a_prod_one_sub_eq_q` | Salt/MR/EvenChiCyclotomic.lean:161 | characters |
| `Salt.MR.e4a_range_pair_split` | Salt/MR/EvenChiCyclotomic.lean:169 | characters |
| `Salt.MR.e4a_prod_sin_sq_eq_q` | Salt/MR/EvenChiCyclotomic.lean:182 | characters |
| `Salt.MR.e4a_prod_sin_eq_sqrt_q` | Salt/MR/EvenChiCyclotomic.lean:207 | characters |
| `Salt.MR.e4a_eta_associated_of_sum_zero` | Salt/MR/EvenChiCyclotomic.lean:244 | characters |
| `Salt.MR.e4a_zpow_prod_split` | Salt/MR/EvenChiCyclotomic.lean:256 | characters |
| `Salt.MR.e4a_eta_eq_quotient` | Salt/MR/EvenChiCyclotomic.lean:286 | characters |
| `Salt.MR.e4a_eta_associated_in_ring` | Salt/MR/EvenChiCyclotomic.lean:315 | characters |
| `Salt.MR.e4a_real_char_inv` | Salt/MR/EvenChiCyclotomic.lean:325 | characters |
| `Salt.MR.e4a_map_prod_sub_one` | Salt/MR/EvenChiCyclotomic.lean:331 | characters |
| `Salt.MR.e4a_map_prod_sub_one_pow` | Salt/MR/EvenChiCyclotomic.lean:340 | characters |
| `Salt.MR.e4a_map_prod_sub_one_gen` | Salt/MR/EvenChiCyclotomic.lean:351 | characters |
| `Salt.MR.e4a_zeta_pow_mod` | Salt/MR/EvenChiCyclotomic.lean:366 | characters |
| `Salt.MR.e4a_zeta_pow_val_mul` | Salt/MR/EvenChiCyclotomic.lean:374 | characters |
| `Salt.MR.e4a_prod_units_index` | Salt/MR/EvenChiCyclotomic.lean:381 | characters |
| `Salt.MR.e4a_prod_units_galois` | Salt/MR/EvenChiCyclotomic.lean:397 | characters |
| `Salt.MR.e4a_term_bridge` | Salt/MR/EvenChiCyclotomic.lean:434 | characters |
| `Salt.MR.e4a_galois_fibre_swap` | Salt/MR/EvenChiCyclotomic.lean:449 | characters |
| `Salt.MR.e4a_galois_fibre_fix` | Salt/MR/EvenChiCyclotomic.lean:467 | characters |
| `Salt.MR.e4a_galois_eta_swap` | Salt/MR/EvenChiCyclotomic.lean:488 | characters |
| `Salt.MR.e4a_fibres_nonempty` | Salt/MR/EvenChiCyclotomic.lean:509 | characters |
| `Salt.MR.e4a_unit_image_isIntegral_pair` | Salt/MR/EvenChiCyclotomic.lean:523 | characters |
| `Salt.MR.e4a_unit_val_pm` | Salt/MR/EvenChiDescent.lean:56 | characters |
| `Salt.MR.e4a_signRu_coe` | Salt/MR/EvenChiDescent.lean:68 | characters |
| `Salt.MR.e4a_toC_toR` | Salt/MR/EvenChiDescent.lean:106 | characters |
| `Salt.MR.e4a_eInt_spec` | Salt/MR/EvenChiDescent.lean:122 | characters |
| `Salt.MR.e4a_toR_isQuadratic` | Salt/MR/EvenChiDescent.lean:137 | characters |
| `Salt.MR.e4a_toR_even` | Salt/MR/EvenChiDescent.lean:148 | characters |
| `Salt.MR.e4a_toR_ne_one` | Salt/MR/EvenChiDescent.lean:155 | characters |
| `Salt.MR.e4a_toR_isPrimitive` | Salt/MR/EvenChiDescent.lean:164 | characters |
| `Salt.MR.e4a_L1_lower_even_complex` | Salt/MR/EvenChiDescent.lean:175 | characters |
| `Salt.MR.e4a_log_golden_le_pi` | Salt/MR/EvenChiDescent.lean:191 | characters |
| `Salt.MR.e4a_log_golden_pos` | Salt/MR/EvenChiDescent.lean:201 | characters |
| `Salt.MR.e4a_L1_lower_primitive_both` | Salt/MR/EvenChiDescent.lean:209 | characters |
| `Salt.MR.l1LowerEffective_goldenGate` | Salt/MR/EvenChiDescent.lean:248 | characters |
| `Salt.MR.e4a_zeta_pow_q` | Salt/MR/EvenChiEta.lean:46 | characters |
| `Salt.MR.e4a_zeta_isAlgebraic` | Salt/MR/EvenChiEta.lean:59 | characters |
| `Salt.MR.e4a_route_b_isCyclotomicExtension` | Salt/MR/EvenChiEta.lean:73 | characters |
| `Salt.MR.e4aZetaK_isPrimitiveRoot` | Salt/MR/EvenChiEta.lean:108 | characters |
| `Salt.MR.e4aZetaO_isPrimitiveRoot` | Salt/MR/EvenChiEta.lean:119 | characters |
| `Salt.MR.e4a_ringOfIntegers_isIntegral` | Salt/MR/EvenChiEta.lean:129 | characters |
| `Salt.MR.e4a_sigma_to_b` | Salt/MR/EvenChiEta.lean:178 | characters |
| `Salt.MR.e4a_sigma_prod_reindex` | Salt/MR/EvenChiEta.lean:191 | characters |
| `Salt.MR.e4a_eta_gal` | Salt/MR/EvenChiEta.lean:230 | characters |
| `Salt.MR.e4a_eta_sum_is_integer_concrete` | Salt/MR/EvenChiEta.lean:263 | characters |
| `Salt.MR.e4a_eta_isIntegral_of_associated` | Salt/MR/EvenChiEta.lean:283 | characters |
| `Salt.MR.e4a_eta_products_associated` | Salt/MR/EvenChiEta.lean:296 | characters |
| `Salt.MR.e4a_prod_image` | Salt/MR/EvenChiEta.lean:330 | characters |
| `Salt.MR.e4a_eta_is_unit_image` | Salt/MR/EvenChiEta.lean:342 | characters |
| `Salt.MR.e4a_eta_inv_is_unit_image` | Salt/MR/EvenChiEta.lean:365 | characters |
| `Salt.MR.e4a_eta_sum_integer_final` | Salt/MR/EvenChiEta.lean:379 | characters |
| `Salt.MR.e4a_fibre_prod_ne_zero` | Salt/MR/EvenChiEta.lean:414 | characters |
| `Salt.MR.e4a_eta_image` | Salt/MR/EvenChiEta.lean:433 | characters |
| `Salt.MR.e4a_eta_norm` | Salt/MR/EvenChiEta.lean:443 | characters |
| `Salt.MR.e4a_sin_prod_eq_eta_norm_inv` | Salt/MR/EvenChiEta.lean:463 | characters |
| `Salt.MR.e4a_fibre_prod_K_ne_zero` | Salt/MR/EvenChiEta.lean:530 | characters |
| `Salt.MR.e4a_eta_ne_zero` | Salt/MR/EvenChiEta.lean:541 | characters |
| `Salt.MR.exists_int_add_inv_sin_prod` | Salt/MR/EvenChiEta.lean:548 | characters |
| `Salt.MR.e4a_E5a_cosh_integer` | Salt/MR/EvenChiEta.lean:604 | characters, exponential sums |
| `Salt.MR.e4a_E5_floor_at_middle` | Salt/MR/EvenChiEta.lean:625 | characters, exponential sums |
| `Salt.MR.e4a_E5_floor_unconditional` | Salt/MR/EvenChiEta.lean:659 | characters, exponential sums |
| `Salt.MR.e4a_L1_lower_even` | Salt/MR/EvenChiEta.lean:688 | characters |
| `Salt.MR.e4a_norm_add_inv_int` | Salt/MR/EvenChiMiddle.lean:44 | characters |
| `Salt.MR.e4a_prod_units_eq_prod_Ioo` | Salt/MR/EvenChiMiddle.lean:96 | characters |
| `Salt.MR.e4a_ne_one_of_sum_zero` | Salt/MR/EvenChiMiddle.lean:131 | characters |
| `Salt.MR.e4a_fourier_signOf_form` | Salt/MR/EvenChiMiddle.lean:141 | characters, exponential sums |
| `Salt.MR.e4a_fourier_signOf_form_real` | Salt/MR/EvenChiMiddle.lean:171 | characters, exponential sums |
| `Salt.MR.e4a_witness_rhs_re` | Salt/MR/EvenChiMiddle.lean:196 | characters |
| `Salt.MR.e4a_middle_re_join` | Salt/MR/EvenChiMiddle.lean:218 | characters, exponential sums |
| `Salt.MR.e4a_signOf_neg` | Salt/MR/EvenChiMiddle.lean:238 | characters |
| `Salt.MR.e4a_middle_reindex` | Salt/MR/EvenChiMiddle.lean:249 | characters |
| `Salt.MR.e4a_log_eta_units` | Salt/MR/EvenChiMiddle.lean:265 | characters |
| `Salt.MR.e4a_middle_closed` | Salt/MR/EvenChiMiddle.lean:274 | characters, exponential sums |
| `Salt.MR.e4a_P_eq_units_prod_inv` | Salt/MR/EvenChiMiddle.lean:308 | characters |
| `Salt.MR.e4a_log_P_eq_middle` | Salt/MR/EvenChiMiddle.lean:338 | characters, exponential sums |
| `Salt.MR.e4a_middle_ne_zero` | Salt/MR/EvenChiMiddle.lean:348 | characters, exponential sums |
| `Salt.MR.e4a_toC_isQuadratic` | Salt/MR/EvenChiRingBridge.lean:42 | characters |
| `Salt.MR.e4a_toC_even` | Salt/MR/EvenChiRingBridge.lean:46 | characters |
| `Salt.MR.e4a_toC_ne_one` | Salt/MR/EvenChiRingBridge.lean:51 | characters |
| `Salt.MR.e4a_toC_eq_signOf` | Salt/MR/EvenChiRingBridge.lean:58 | characters |
| `Salt.MR.e4a_sum_units_of_vanishing` | Salt/MR/EvenChiRingBridge.lean:67 | characters |
| `Salt.MR.e4a_toC_sum_eq_signOf_sum` | Salt/MR/EvenChiRingBridge.lean:84 | characters |
| `Salt.MR.e4a_toC_toUnitHom_ker` | Salt/MR/EvenChiRingBridge.lean:100 | characters |
| `Salt.MR.e4a_toC_factorsThrough_iff` | Salt/MR/EvenChiRingBridge.lean:108 | characters |
| `Salt.MR.e4a_toC_conductorSet_eq` | Salt/MR/EvenChiRingBridge.lean:115 | characters |
| `Salt.MR.e4a_toC_isPrimitive` | Salt/MR/EvenChiRingBridge.lean:138 | characters |
| `Salt.MR.e4a_card_eq_of_sum_zero` | Salt/MR/EvenChiSign.lean:30 | characters |
| `Salt.MR.e4a_units_reindex` | Salt/MR/EvenChiSign.lean:43 | characters |
| `Salt.MR.e4a_prod_restrict_coprime` | Salt/MR/EvenChiSign.lean:48 | characters |
| `Salt.MR.e4a_char_vanishes_off_units` | Salt/MR/EvenChiSign.lean:63 | characters |
| `Salt.MR.e4a_fibre_swap` | Salt/MR/EvenChiSign.lean:84 | characters |
| `Salt.MR.E4aChiBridge.e4a_signOf_one` | Salt/MR/EvenChiSign.lean:113 | characters |
| `Salt.MR.E4aChiBridge.e4a_signOf_cast` | Salt/MR/EvenChiSign.lean:122 | characters |
| `Salt.MR.E4aChiBridge.e4a_signOf_mul` | Salt/MR/EvenChiSign.lean:139 | characters |
| `Salt.MR.E4aChiBridge.e4a_signOf_trichotomy` | Salt/MR/EvenChiSign.lean:166 | characters |
| `Salt.MR.E4aChiBridge.e4a_dirichletReal_values` | Salt/MR/EvenChiSign.lean:188 | characters |
| `Salt.MR.E4aChiBridge.e4a_signOf_cast'` | Salt/MR/EvenChiSign.lean:204 | characters |
| `Salt.MR.E4aChiBridge.e4a_signOf_mul'` | Salt/MR/EvenChiSign.lean:210 | characters |
| `Salt.MR.e4a_dirichlet_fibre_swap` | Salt/MR/EvenChiSign.lean:231 | characters |
| `Salt.MR.e4a_dirichlet_card_eq` | Salt/MR/EvenChiSign.lean:241 | characters |
| `Salt.MR.e4a_signOf_sum_eq_zero` | Salt/MR/EvenChiSign.lean:269 | characters |
| `Salt.MR.e4a_step3_sin_bridge` | Salt/MR/EvenChiSine.lean:33 | characters |
| `Salt.MR.e4a_norm_zpow_prod` | Salt/MR/EvenChiSine.lean:66 | characters |
| `Salt.MR.e4a_sin_prod_eq_norm` | Salt/MR/EvenChiSine.lean:74 | characters |
| `Salt.MR.e4a_neg_clog_re` | Salt/MR/EvenChiSine.lean:113 | characters |
| `Salt.MR.e4a_sum_clog_re` | Salt/MR/EvenChiSine.lean:118 | characters |
| `Salt.MR.e4a_sum_clog_re_sin` | Salt/MR/EvenChiSine.lean:128 | characters |
| `Salt.MR.e4a_log_zpow_prod` | Salt/MR/EvenChiSine.lean:169 | characters |
| `Salt.MR.e4a_log_eta_eq_sum` | Salt/MR/EvenChiSine.lean:178 | characters |
| `Salt.MR.e4a_exp_pow_eq_exp` | Salt/MR/EvenChiSine.lean:217 | characters |
| `Salt.MR.e4a_unit_ne_zero_aux` | Salt/MR/EvenChiSine.lean:227 | characters |
| `Salt.MR.e4a_unit_neg_ne_zero` | Salt/MR/EvenChiSine.lean:242 | characters |
| `Salt.MR.e4a_unit_val_div_mem` | Salt/MR/EvenChiSine.lean:251 | characters |
| `Salt.MR.e4a_sin_ne_zero_at_unit` | Salt/MR/EvenChiSine.lean:261 | characters |
| `Salt.MR.e4a_sin_bridge_zmod` | Salt/MR/EvenChiSine.lean:267 | characters |
| `Salt.MR.e4a_gaussSum_even_inv_addChar` | Salt/MR/EvenChiTau.lean:28 | characters, exponential sums |
| `Salt.MR.e4a_gaussSum_real` | Salt/MR/EvenChiTau.lean:38 | characters, exponential sums |
| `Salt.MR.e4a_gaussSum_eq_real` | Salt/MR/EvenChiTau.lean:45 | characters, exponential sums |
| `Salt.MR.e4a_gaussSum_re_sq` | Salt/MR/EvenChiTau.lean:54 | characters, exponential sums |
| `Salt.MR.e4a_gaussSum_re_eq_pm_sqrt` | Salt/MR/EvenChiTau.lean:66 | characters, exponential sums |
| `Salt.MR.e4a_gaussSum_re_ne_zero` | Salt/MR/EvenChiTau.lean:96 | characters, exponential sums |
| `Salt.MR.e4a_abs_gaussSum_re` | Salt/MR/EvenChiTau.lean:108 | characters |
| `Salt.MR.sqrt_le_of_sq_le` | Salt/MR/ExitClose.lean:53 | characters |
| `Salt.MR.mul_three_le` | Salt/MR/ExitClose.lean:58 | characters |
| `Salt.MR.pow24_le_exp` | Salt/MR/ExitClose.lean:66 | characters |
| `Salt.MR.exit_collect` | Salt/MR/ExitClose.lean:99 | characters |
| `Salt.MR.exitBd_lt_of_arms` | Salt/MR/ExitClose.lean:373 | characters |
| `Salt.MR.exitClose_twelve` | Salt/MR/ExitClose.lean:742 | characters |
| `Salt.MR.minorArcBoundTight_twelve` | Salt/MR/ExitClose.lean:769 | characters |
| `Salt.MR.bigXiArcTight_twelve` | Salt/MR/ExitClose.lean:773 | characters |
| `Salt.MR.dyadic_SPartial_charge` | Salt/MR/FarArm.lean:109 | characters |
| `Salt.MR.farArm_charge_le` | Salt/MR/FarArm.lean:184 | characters |
| `Salt.MR.cap_fails_floor` | Salt/MR/FarArm.lean:203 | characters |
| `Salt.MR.Mrange_floor_of_center_floor_radius` | Salt/MR/FarArm.lean:240 | characters |
| `Salt.MR.Mrange_floor_of_center_floor` | Salt/MR/FarArm.lean:279 | characters |
| `Salt.MR.far_arm_row` | Salt/MR/FarArm.lean:314 | characters |
| `Salt.MR.far_arm_row_tailed` | Salt/MR/FarArm.lean:352 | characters |
| `Salt.MR.far_arm_row_polyT` | Salt/MR/FarArm.lean:391 | characters |
| `Salt.MR.seam_row_of_inter_empty` | Salt/MR/FarArm.lean:443 | characters |
| `Salt.MR.seam_row_both_arms` | Salt/MR/FarArm.lean:465 | characters |
| `Salt.MR.seam_row_three_arms` | Salt/MR/FarArm.lean:486 | characters |
| `Salt.MR.far_supF_bound` | Salt/MR/FarClose.lean:204 | characters |
| `Salt.MR.far_kernel_bound` | Salt/MR/FarClose.lean:249 | characters |
| `Salt.MR.far_kernel_bound_T` | Salt/MR/FarClose.lean:312 | characters |
| `Salt.MR.far_window_mass_le` | Salt/MR/FarClose.lean:368 | characters |
| `Salt.MR.far_price_floor` | Salt/MR/FarClose.lean:401 | characters |
| `Salt.MR.far_term_priced` | Salt/MR/FarClose.lean:427 | characters |
| `Salt.MR.plog_drift_loglog` | Salt/MR/FarL2.lean:153 | characters |
| `Salt.MR.plog_drift_logloglog` | Salt/MR/FarL2.lean:172 | characters |
| `Salt.MR.plog_floor_real` | Salt/MR/FarL2.lean:212 | characters |
| `Salt.MR.plog_vk_debit` | Salt/MR/FarL2.lean:252 | characters |
| `Salt.MR.polylog_floor_M0` | Salt/MR/FarL2.lean:500 | characters |
| `Salt.MR.plog_floor_clears_gate` | Salt/MR/FarL2.lean:557 | characters |
| `Salt.MR.polylog_floor_M0_liouChi` | Salt/MR/FarL2.lean:574 | characters |
| `Salt.MR.polylog_floor_M0_pieceDatum` | Salt/MR/FarL2.lean:588 | characters |
| `Salt.MR.band_floor_M0_vk` | Salt/MR/FarL2.lean:621 | characters |
| `Salt.MR.box_floor_M0` | Salt/MR/FarL2.lean:665 | characters |
| `Salt.MR.windowSum_l2_mvt` | Salt/MR/FarL2.lean:803 | characters |
| `Salt.MR.crossKerFar_le_weighted_l2` | Salt/MR/FarL2.lean:858 | characters |
| `Salt.MR.box_floor_M0_liouChi` | Salt/MR/FarL2.lean:963 | characters |
| `Salt.MR.box_floor_M0_pieceDatum` | Salt/MR/FarL2.lean:985 | characters |
| `Salt.MR.box_floor_clears_gate_45` | Salt/MR/FarL2.lean:1012 | characters |
| `Salt.MR.dpoly_eq_sum_blocks` | Salt/MR/FarL2Dyadic.lean:155 | characters |
| `Salt.MR.dpoly_block_l2_mvt` | Salt/MR/FarL2Dyadic.lean:213 | characters |
| `Salt.MR.far_weight_le_of_linear_growth` | Salt/MR/FarL2Dyadic.lean:382 | characters |
| `Salt.MR.continuous_windowSum_sq` | Salt/MR/FarL2Dyadic.lean:437 | characters |
| `Salt.MR.windowSum_l2_block_mvt` | Salt/MR/FarL2Dyadic.lean:449 | characters |
| `Salt.MR.winL2Tail_dyadic_le` | Salt/MR/FarL2Dyadic.lean:506 | characters |
| `Salt.MR.farL2_grade_clears_gate` | Salt/MR/FarL2Dyadic.lean:543 | characters |
| `Salt.MR.crossKerFar_polylog` | Salt/MR/FarL2Dyadic.lean:587 | characters |
| `Salt.MR.winL2Coeff_norm_antitone` | Salt/MR/FarL2Dyadic.lean:616 | characters |
| `Salt.MR.winL2Mass_antitone` | Salt/MR/FarL2Dyadic.lean:632 | characters |
| `Salt.MR.winL2Price_antitone` | Salt/MR/FarL2Dyadic.lean:643 | characters |
| `Salt.MR.farL2Grade_antitone` | Salt/MR/FarL2Dyadic.lean:653 | characters |
| `Salt.MR.crossKerFar_polylog_uniform` | Salt/MR/FarL2Dyadic.lean:686 | characters |
| `Salt.MR.Tstar_mono` | Salt/MR/FarStar.lean:273 | characters |
| `Salt.MR.far_kernel_bound_star` | Salt/MR/FarStar.lean:318 | characters |
| `Salt.MR.far_kfar_star_le` | Salt/MR/FarStar.lean:371 | characters |
| `Salt.MR.far_price_floor_16` | Salt/MR/FarStar.lean:518 | characters |
| `Salt.MR.desmooth_under_grade16` | Salt/MR/FarStar.lean:538 | characters |
| `Salt.MR.hfar_star` | Salt/MR/FarStar.lean:565 | characters |
| `Salt.MR.seam_gate_star_of_nonempty` | Salt/MR/FarStar.lean:656 | characters |
| `Salt.MR.exists_min_gate_star` | Salt/MR/FarStar.lean:666 | characters |
| `Salt.MR.seam_gate_star_package` | Salt/MR/FarStar.lean:674 | characters |
| `Salt.MR.crownWd_exists_charge` | Salt/MR/FlatDoorAllGrades.lean:60 | characters |
| `Salt.MR.flatDoorAllGradesW_holds` | Salt/MR/FlatDoorAllGrades.lean:107 | characters |
| `Salt.MR.flat_head_uniform_xceil_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:624 | characters |
| `Salt.MR.crownBand_long_of_tight` | Salt/MR/FlatDoorAllGradesBand.lean:1527 | characters |
| `Salt.MR.crownBand_long_of_tightArm` | Salt/MR/FlatDoorAllGradesBand.lean:1609 | characters |
| `Salt.MR.flatDoorAllGradesBandW_holds` | Salt/MR/FlatDoorAllGradesBand.lean:1706 | characters |
| `Salt.MR.epsChain_log_top_le_nine` | Salt/MR/FlatDoorEpsChain.lean:41 | characters |
| `Salt.MR.epsChain_arm_split_cap` | Salt/MR/FlatDoorEpsChain.lean:79 | characters |
| `Salt.MR.bigXi_bounded_ceiling_of_cap` | Salt/MR/FlatDoorEpsChain.lean:410 | characters |
| `Salt.MR.flat_head_uniform_xceil_eps` | Salt/MR/FlatDoorEpsChain.lean:552 | characters |
| `Salt.MR.flatDoorMint_floor_le_grade` | Salt/MR/FlatDoorEpsFamily.lean:87 | characters |
| `Salt.MR.flatDoorMint_grade_at_pin` | Salt/MR/FlatDoorEpsFamily.lean:98 | characters |
| `Salt.MR.flatDoor_pin_in_cap` | Salt/MR/FlatDoorEpsFamily.lean:257 | characters |
| `Salt.MR.flatDoor_cap_lattice_top` | Salt/MR/FlatDoorEpsFamily.lean:263 | characters |
| `Salt.MR.flatDoor_cap_restated_in_v1` | Salt/MR/FlatDoorEpsFamily.lean:276 | characters |
| `Salt.MR.epsRung2_log500_le` | Salt/MR/FlatDoorEpsRung2.lean:48 | characters |
| `Salt.MR.epsRung2_log_inv_eps_le` | Salt/MR/FlatDoorEpsRung2.lean:58 | characters |
| `Salt.MR.klevF_capNumeral_L` | Salt/MR/FlatDoorEpsRung2.lean:82 | characters |
| `Salt.MR.s16_baseScaleCap96_LH_at_klevF_L` | Salt/MR/FlatDoorEpsRung2.lean:168 | characters |
| `Salt.MR.xt_log_inv_rho_le_L` | Salt/MR/FlatDoorEpsRung2.lean:194 | characters |
| `Salt.MR.flat_arm_eps_le_L` | Salt/MR/FlatDoorEpsRung2.lean:256 | characters |
| `Salt.MR.flat_arm_budget_le_L` | Salt/MR/FlatDoorEpsRung2.lean:314 | characters |
| `Salt.MR.flat_witFloor_eq_designBase_L` | Salt/MR/FlatDoorEpsRung2.lean:426 | characters |
| `Salt.MR.flatDoorM_bfloor_bump_L` | Salt/MR/FlatDoorEpsRung2.lean:461 | characters |
| `Salt.MR.pieceFloor_vt_threshold_of_loglog_rated_L` | Salt/MR/FlatDoorEpsRung2.lean:880 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum_arcDen_rated_L` | Salt/MR/FlatDoorEpsRung2.lean:940 | characters |
| `Salt.MR.cofkR_cofactorSupply_L_gk_rated_L` | Salt/MR/FlatDoorEpsRung2.lean:1498 | characters |
| `Salt.MR.bigXi_bounded_ceiling_eps` | Salt/MR/FlatDoorEpsRung2.lean:2235 | characters |
| `Salt.MR.epsRung2_exp25` | Salt/MR/FlatDoorEpsRung2.lean:2434 | characters |
| `Salt.MR.epsRung2_tower_charge` | Salt/MR/FlatDoorEpsRung2.lean:2452 | characters |
| `Salt.MR.s15Arm_log_le_L` | Salt/MR/FlatDoorEpsRung2.lean:2494 | characters |
| `Salt.MR.s15Arm_log_le_L_cut20` | Salt/MR/FlatDoorEpsRung2.lean:2709 | characters |
| `Salt.MR.epsChain_arm_split_L` | Salt/MR/FlatDoorEpsRung2.lean:2738 | characters |
| `Salt.MR.s16_audit_rho_ge_wide_h_L` | Salt/MR/FlatDoorEpsRung2.lean:3055 | characters |
| `Salt.MR.s16_audit_neglog_rho_le_wide_h_L` | Salt/MR/FlatDoorEpsRung2.lean:3095 | characters |
| `Salt.MR.s16_audit_neglog_rho_le_h_L` | Salt/MR/FlatDoorEpsRung2.lean:3122 | characters |
| `Salt.MR.flat_half_line_L` | Salt/MR/FlatDoorEpsRung2.lean:3142 | characters |
| `Salt.MR.flat_anchor_line_wide_L` | Salt/MR/FlatDoorEpsRung2.lean:3178 | characters |
| `Salt.MR.flat_gP1_line_L` | Salt/MR/FlatDoorEpsRung2.lean:3197 | characters |
| `Salt.MR.flat_lvl_line_L` | Salt/MR/FlatDoorEpsRung2.lean:3231 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_L` | Salt/MR/FlatDoorEpsRung2.lean:3321 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_L` | Salt/MR/FlatDoorEpsRung2.lean:3574 | characters |
| `Salt.MR.flat_blk_line_gk_L` | Salt/MR/FlatDoorEpsRung2.lean:3765 | characters |
| `Salt.MR.flat_lambda_core_T` | Salt/MR/FlatDoorEpsRung2.lean:4016 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_charge_L` | Salt/MR/FlatDoorEpsRung2.lean:4255 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_wide_L` | Salt/MR/FlatDoorEpsRung2.lean:4313 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_wide_L` | Salt/MR/FlatDoorEpsRung2.lean:4336 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_bumped_win_L` | Salt/MR/FlatDoorEpsRung2.lean:4363 | characters |
| `Salt.MR.epsRung2_log_Kb_le` | Salt/MR/FlatDoorEpsRung2.lean:4443 | characters |
| `Salt.MR.epsRung2_one_le_Kb` | Salt/MR/FlatDoorEpsRung2.lean:4456 | characters |
| `Salt.MR.xceilRiderStrictAt_zero` | Salt/MR/FlatDoorEpsRung2.lean:4758 | characters |
| `Salt.MR.flat_head_uniform_xceil_epsW` | Salt/MR/FlatDoorEpsRung2.lean:4783 | characters |
| `Salt.MR.flatDoorEpsFamilyW_holds` | Salt/MR/FlatDoorEpsRung2.lean:5682 | characters |
| `Salt.MR.logChowla2_epsFamily_flatDoor_holds` | Salt/MR/FlatDoorEpsRung2.lean:5738 | characters |
| `Salt.MR.logChowla2_epsFamily_flatDoor_floor_holds` | Salt/MR/FlatDoorEpsRung2.lean:5750 | characters |
| `Salt.MR.crownNV_expSum_zero` | Salt/MR/FlatDoorNonVacuity.lean:50 | characters, entropy, exponential sums |
| `Salt.MR.crownNV_zero_mem_bigXi` | Salt/MR/FlatDoorNonVacuity.lean:64 | characters |
| `Salt.MR.crownNV_above_flat_floor` | Salt/MR/FlatDoorNonVacuity.lean:87 | characters |
| `Salt.MR.crownK6_window_sum_odd` | Salt/MR/FlatDoorParityFloor.lean:60 | characters |
| `Salt.MR.crownK6_one_le_norm_of_odd` | Salt/MR/FlatDoorParityFloor.lean:73 | characters |
| `Salt.MR.crownK6_integral_floor` | Salt/MR/FlatDoorParityFloor.lean:84 | characters, exponential sums |
| `Salt.MR.crownK6_one_le_J` | Salt/MR/FlatDoorParityFloor.lean:101 | characters |
| `Salt.MR.crownK6_Hlo_succ_le_Hhi` | Salt/MR/FlatDoorParityFloor.lean:113 | characters |
| `Salt.MR.crownK6_odd_in_range` | Salt/MR/FlatDoorParityFloor.lean:131 | characters |
| `Salt.MR.crownK6_not_every_grade` | Salt/MR/FlatDoorParityFloor.lean:177 | characters |
| `Salt.MR.crownK6_flat_order_forced` | Salt/MR/FlatDoorParityFloor.lean:189 | characters |
| `Salt.MR.charge_exists` | Salt/MR/FlatDoorUniform.lean:70 | characters |
| `Salt.MR.flatDesignBase_mono'` | Salt/MR/FlatDoorUniform.lean:86 | characters |
| `Salt.MR.le_flatDesignBase_of_loglog` | Salt/MR/FlatDoorUniform.lean:93 | characters |
| `Salt.MR.flatDesignBase_of_loglog_eq` | Salt/MR/FlatDoorUniform.lean:220 | characters |
| `Salt.MR.flatDesignBase_design` | Salt/MR/FlatDoorUniform.lean:232 | characters |
| `Salt.MR.loglogFloor50_le_flatDesignBase` | Salt/MR/FlatDoorUniform.lean:246 | characters |
| `Salt.MR.arcFloor36_le_flatDesignBase` | Salt/MR/FlatDoorUniform.lean:254 | characters |
| `Salt.MR.uArm_log_inv_grade_le` | Salt/MR/FlatDoorUniform.lean:593 | characters |
| `Salt.MR.uArm_exponent_le` | Salt/MR/FlatDoorUniform.lean:655 | characters |
| `Salt.MR.s15Arm_le_of_regime` | Salt/MR/FlatDoorUniform.lean:693 | characters |
| `Salt.MR.flatHeadFormU_trivial` | Salt/MR/FlatDoorUniform.lean:1171 | characters |
| `Salt.MR.flatDoorUniformW_holds` | Salt/MR/FlatDoorUniform.lean:1609 | characters |
| `Salt.MR.flatDoorAllGradesW_of_uniform` | Salt/MR/FlatDoorUniform.lean:1622 | characters |
| `Salt.MR.flatDoorM_ge_bfloorConst` | Salt/MR/FlatFloorBump.lean:97 | characters |
| `Salt.MR.flatDoorM_ge_pow355` | Salt/MR/FlatFloorBump.lean:113 | characters |
| `Salt.MR.flatDoorM_bfloor_bump` | Salt/MR/FlatFloorBump.lean:127 | characters |
| `Salt.MR.flatDoorM_Mfl_bump` | Salt/MR/FlatFloorBump.lean:156 | characters |
| `Salt.MR.flatDoorM_ge_pow` | Salt/MR/FlatFloorBump.lean:252 | characters |
| `Salt.MR.flatDoorM_gradeFloor_win` | Salt/MR/FlatFloorBump.lean:279 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_bumped_win` | Salt/MR/FlatFloorBump.lean:353 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_bumped` | Salt/MR/FlatFloorBump.lean:382 | characters |
| `Salt.MR.dist_one_floor_uniform` | Salt/MR/FloorProvenance.lean:150 | characters |
| `Salt.MR.seam_floor_of_cap_pointwise` | Salt/MR/FloorProvenance.lean:198 | characters |
| `Salt.MR.Mrange_seam_floor_of_cap` | Salt/MR/FloorProvenance.lean:264 | characters |
| `Salt.MR.cap_gate_satisfiable` | Salt/MR/FloorProvenance.lean:328 | characters |
| `Salt.MR.Mrange_seam_floor_column` | Salt/MR/FloorProvenance.lean:358 | characters |
| `Salt.MR.T1_decay_column_cap_supplied` | Salt/MR/FloorProvenance.lean:381 | characters |
| `Salt.MR.Mrange_seam_floor_A10` | Salt/MR/FloorProvenance.lean:422 | characters |
| `Salt.MR.witKk_cut` | Salt/MR/FrameWitness.lean:129 | characters |
| `Salt.MR.witMt_window` | Salt/MR/FrameWitness.lean:145 | characters |
| `Salt.MR.witness_window_geometry` | Salt/MR/FrameWitness.lean:153 | characters |
| `Salt.MR.ramRbot_le_scale` | Salt/MR/FrameWitness.lean:165 | characters |
| `Salt.MR.witMs_range` | Salt/MR/FrameWitness.lean:176 | characters |
| `Salt.MR.witM0_le` | Salt/MR/FrameWitness.lean:187 | characters |
| `Salt.MR.witM0_two_le` | Salt/MR/FrameWitness.lean:191 | characters |
| `Salt.MR.witMs_le_four_mul` | Salt/MR/FrameWitness.lean:198 | characters |
| `Salt.MR.ramI_self` | Salt/MR/FrameWitness.lean:213 | characters |
| `Salt.MR.ramQbase_at_pin` | Salt/MR/FrameWitness.lean:229 | characters |
| `Salt.MR.ramI_self_index_ge` | Salt/MR/FrameWitness.lean:244 | characters |
| `Salt.MR.ramQbase_ge_bot` | Salt/MR/FrameWitness.lean:273 | characters |
| `Salt.MR.ramQbase_le_top` | Salt/MR/FrameWitness.lean:277 | characters |
| `Salt.MR.ramI_index_ge` | Salt/MR/FrameWitness.lean:293 | characters |
| `Salt.MR.h_ceiling_gate` | Salt/MR/FrameWitness.lean:313 | characters |
| `Salt.MR.c4_at_height` | Salt/MR/FrameWitness.lean:326 | characters |
| `Salt.MR.log_le_of_le_Q83` | Salt/MR/FrameWitness.lean:350 | characters |
| `Salt.MR.h_ceiling_gate_band` | Salt/MR/FrameWitness.lean:358 | characters |
| `Salt.MR.c4_at_height_band` | Salt/MR/FrameWitness.lean:372 | characters |
| `Salt.MR.tlBlockGates34_at_witness` | Salt/MR/FrameWitness.lean:415 | characters |
| `Salt.MR.blocks_at_witness` | Salt/MR/FrameWitness.lean:520 | characters |
| `Salt.MR.thinBundleG_mono_T` | Salt/MR/FrameWitness.lean:574 | characters |
| `Salt.MR.thin_at_witness` | Salt/MR/FrameWitness.lean:600 | characters |
| `Salt.MR.ksGate_at_witness` | Salt/MR/FrameWitness.lean:634 | characters |
| `Salt.MR.calibration_at_witness` | Salt/MR/FrameWitness.lean:671 | characters |
| `Salt.MR.Tstar2_le_self` | Salt/MR/FrameWitness.lean:699 | characters |
| `Salt.MR.Tstar2_box_at_witness` | Salt/MR/FrameWitness.lean:719 | characters |
| `Salt.MR.witEP2_nonneg` | Salt/MR/FrameWitness.lean:787 | characters |
| `Salt.MR.witEP2_eval` | Salt/MR/FrameWitness.lean:796 | characters |
| `Salt.MR.witEP2_gate` | Salt/MR/FrameWitness.lean:814 | characters |
| `Salt.MR.err_at_witness` | Salt/MR/FrameWitness.lean:826 | characters |
| `Salt.MR.row_ladder_at_witness` | Salt/MR/FrameWitness.lean:1241 | characters |
| `Salt.MR.exists_shortIntervalDatum` | Salt/MR/GradeConst.lean:57 | characters |
| `Salt.MR.crossKer_width_sigma_bound_uniform` | Salt/MR/GradeConst.lean:686 | characters |
| `Salt.MR.pin_width_gates` | Salt/MR/GradeConst.lean:742 | characters |
| `Salt.MR.width_pin_bracket_le` | Salt/MR/GradeConst.lean:778 | characters |
| `Salt.MR.rhsAgradeConst_le` | Salt/MR/GradeConst.lean:1260 | characters |
| `Salt.MR.intervalIntegrable_beta_legC` | Salt/MR/GradeWindowC.lean:114 | characters |
| `Salt.MR.intervalIntegrable_alpha_legC` | Salt/MR/GradeWindowC.lean:146 | characters |
| `Salt.MR.jointIntegrableAtC_pin_free` | Salt/MR/GradeWindowC.lean:234 | characters |
| `Salt.MR.joint_supF_pin_atC` | Salt/MR/GradeWindowC.lean:353 | characters |
| `Salt.MR.joint_supF_pin_windowC` | Salt/MR/GradeWindowC.lean:430 | characters |
| `Salt.MR.rhsAgradeConstC_le` | Salt/MR/GradeWindowC.lean:539 | characters |
| `Salt.MR.center_halasz_supply_B_uniform` | Salt/MR/GradeWindowC.lean:838 | characters |
| `Salt.MR.center_halasz_supply_B` | Salt/MR/GradeWindowC.lean:956 | characters |
| `Salt.MR.window_mass_eval` | Salt/MR/GrandComp.lean:67 | characters |
| `Salt.MR.window_sup_decay` | Salt/MR/GrandComp.lean:299 | zeros, characters |
| `Salt.MR.window_sup_decay_sq` | Salt/MR/GrandComp.lean:332 | zeros, characters |
| `Salt.MR.sigma_cutoff_seam` | Salt/MR/GrandComp.lean:383 | characters |
| `Salt.MR.nearRatTight_intCast_add` | Salt/MR/HDoorArc.lean:49 | characters |
| `Salt.MR.m4_sievedDoorSqH_trivial` | Salt/MR/HDoorArc.lean:463 | sieves, characters |
| `Salt.MR.m4_classBlockMeanSqH_trivial` | Salt/MR/HDoorClose.lean:323 | characters |
| `Salt.MR.m4_chiBlockMeanSqH_trivial` | Salt/MR/HDoorClose.lean:357 | characters |
| `Salt.MR.arcDen_le_h_mul_arcDen` | Salt/MR/HDoorSupply.lean:66 | characters |
| `Salt.MR.log_le_of_le_arcDen_h` | Salt/MR/HDoorSupply.lean:79 | characters |
| `Salt.MR.log_max_two_le_of_le_arcDen_h` | Salt/MR/HDoorSupply.lean:94 | characters |
| `Salt.MR.mertensCap_le_of_le_arcDen_h` | Salt/MR/HDoorSupply.lean:127 | characters |
| `Salt.MR.vkDebitConst_le_of_le_arcDen_h` | Salt/MR/HDoorSupply.lean:155 | characters |
| `Salt.MR.vkMidDebitSharp_le_of_le_arcDen_h` | Salt/MR/HDoorSupply.lean:174 | characters |
| `Salt.MR.bandConstQ_le_of_le_arcDen_h` | Salt/MR/HDoorSupply.lean:248 | characters |
| `Salt.MR.pieceFloor_vt_threshold_of_loglog_rated_h` | Salt/MR/HDoorSupply.lean:350 | characters |
| `Salt.MR.pieceFloor_vt_threshold_of_loglog_rated_two` | Salt/MR/HDoorSupply.lean:402 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum_arcDen_rated_h` | Salt/MR/HDoorSupply.lean:446 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum_arcDen_rated_two` | Salt/MR/HDoorSupply.lean:478 | characters |
| `Salt.MR.abs_mul_window_le_of_cap` | Salt/MR/HDoorSupply.lean:1146 | characters |
| `Salt.MR.norm_phase_sum_cap_drift` | Salt/MR/HDoorSupply.lean:1162 | characters |
| `Salt.MR.norm_absWindowSum_le_drift_cap` | Salt/MR/HDoorSupply.lean:1179 | characters |
| `Salt.MR.m4_sievedDoorSqSupH_trivial` | Salt/MR/HDoorSupply.lean:1278 | sieves, characters |
| `Salt.MR.m4_blockMeanSqSupQH_of_classPriceH` | Salt/MR/HDoorSupply.lean:1370 | sieves, characters |
| `Salt.MR.m4_blockMeanSqSupQH_trivial` | Salt/MR/HDoorSupply.lean:1425 | characters |
| `Salt.MR.pieceFloor_vt_threshold_of_loglog_rated_h_b9` | Salt/MR/HDoorSupply.lean:1497 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum_arcDen_rated_h_b9` | Salt/MR/HDoorSupply.lean:1549 | characters |
| `Salt.MR.prop21_unconditional_final` | Salt/MR/HExit.lean:620 | characters |
| `Salt.MR.prop21_unconditional_clean` | Salt/MR/HExit.lean:733 | characters |
| `Salt.MR.T1_head_wire` | Salt/MR/HExit.lean:892 | characters |
| `Salt.MR.norm_windowSum_le_mass` | Salt/MR/HExit.lean:957 | characters |
| `Salt.MR.prop21RHS_le_head` | Salt/MR/HExit.lean:984 | characters |
| `Salt.MR.kernel_L1_mass` | Salt/MR/HExit.lean:1120 | characters |
| `Salt.MR.kernel_mass_ledger` | Salt/MR/HExit.lean:1175 | characters |
| `Salt.MR.sigma_cutoff` | Salt/MR/HExit.lean:1226 | characters |
| `Salt.MR.hRHS_discharged_joint` | Salt/MR/HExit.lean:1401 | characters |
| `Salt.MR.T1_head_supplied_joint` | Salt/MR/HExit.lean:1419 | characters |
| `Salt.MR.T1_decay_conditional_final` | Salt/MR/HExit.lean:1458 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_bumped_win_h` | Salt/MR/HSeamCheck.lean:92 | characters |
| `Salt.MR.cos_int_pair` | Salt/MR/HalaszContour.lean:353 | characters |
| `Salt.MR.dirichlet_plancherel` | Salt/MR/HalaszContour.lean:460 | characters |
| `Salt.MR.halasz_cosh_ineq` | Salt/MR/HalaszCore.lean:102 | characters |
| `Salt.MR.halasz_cosh_ineq_complex` | Salt/MR/HalaszCore.lean:180 | characters |
| `Salt.MR.offdiag_int_bound` | Salt/MR/HalaszCore.lean:196 | characters |
| `Salt.MR.grade_EM` | Salt/MR/HalaszCore.lean:245 | characters |
| `Salt.MR.ball_mvt` | Salt/MR/HalaszCore.lean:301 | characters |
| `Salt.MR.log_diff_ge` | Salt/MR/HalaszCore.lean:326 | characters |
| `Salt.MR.halasz_ball_decay` | Salt/MR/HalaszCore.lean:440 | characters |
| `Salt.MR.window_sup_decay_gen` | Salt/MR/HalaszDirect.lean:171 | zeros, characters |
| `Salt.MR.window_sup_decay_theta` | Salt/MR/HalaszDirect.lean:236 | zeros, characters |
| `Salt.MR.halasz_direct_gen` | Salt/MR/HalaszDirect.lean:401 | zeros, characters |
| `Salt.MR.halasz_direct_ball` | Salt/MR/HalaszDirect.lean:461 | zeros, characters |
| `Salt.MR.halasz_direct_ball_window` | Salt/MR/HalaszDirect.lean:527 | zeros, characters |
| `Salt.MR.largeSeries_ftc_double_beta` | Salt/MR/HalaszFactor.lean:109 | zeros, characters |
| `Salt.MR.k4_plan_le_diag_sharp` | Salt/MR/HalaszHead.lean:190 | characters |
| `Salt.MR.contour_A13_A14_head_sharp` | Salt/MR/HalaszHead.lean:236 | characters |
| `Salt.MR.hhead_supplier_fgJ` | Salt/MR/HalaszHead.lean:300 | characters |
| `Salt.MR.T1_decay_fgJ` | Salt/MR/HalaszHead.lean:321 | characters |
| `Salt.MR.hhead_supplier_trivial` | Salt/MR/HalaszHead.lean:419 | characters |
| `Salt.MR.T1_decay_trivial` | Salt/MR/HalaszHead.lean:448 | characters |
| `Salt.MR.smoothPart_ellLin_eq_restrictBelow` | Salt/MR/HalaszIdentity.lean:116 | characters |
| `Salt.MR.seam_centering` | Salt/MR/HalaszIdentity.lean:189 | characters |
| `Salt.MR.seam_alpha_collapse` | Salt/MR/HalaszIdentity.lean:241 | zeros, characters |
| `Salt.MR.seam_double_ftc` | Salt/MR/HalaszIdentity.lean:285 | zeros, characters |
| `Salt.MR.four_factor_hat_rep` | Salt/MR/HalaszIdentity.lean:558 | characters |
| `Salt.MR.hat_contour_rep_mismatch` | Salt/MR/HalaszIdentity.lean:638 | zeros, characters |
| `Salt.MR.four_factor_hat_rep_shifted` | Salt/MR/HalaszIdentity.lean:676 | characters |
| `Salt.MR.prop21RHS_hat_rep` | Salt/MR/HalaszIdentity.lean:745 | characters |
| `Salt.MR.seam_realignment` | Salt/MR/HalaszIdentity.lean:861 | characters |
| `Salt.MR.seam_realignment_hat` | Salt/MR/HalaszIdentity.lean:880 | characters |
| `Salt.MR.prop21RHS_hat_rep_aligned` | Salt/MR/HalaszIdentity.lean:938 | characters |
| `Salt.MR.joint_support_untruncation` | Salt/MR/HalaszIdentity.lean:1110 | characters |
| `Salt.MR.aligned_collapse_assembled` | Salt/MR/HalaszIdentity.lean:1561 | characters |
| `Salt.MR.endpoint_reconciliation_full` | Salt/MR/HalaszIdentity.lean:1705 | characters |
| `Salt.MR.prop21_unconditional` | Salt/MR/HalaszIdentity.lean:2050 | characters |
| `Salt.MR.exp_sum_decay` | Salt/MR/HalaszIntegers.lean:302 | characters |
| `Salt.MR.dualPoly_diagonal` | Salt/MR/HalaszIntegers.lean:394 | characters |
| `Salt.MR.card_chars_totient_real` | Salt/MR/HalaszIntegersChiClose.lean:152 | characters |
| `Salt.MR.halaszIntegersChiPhi_holds` | Salt/MR/HalaszIntegersChiClose.lean:257 | characters |
| `Salt.MR.totient_le_logpow` | Salt/MR/HalaszIntegersChiClose.lean:394 | characters |
| `Salt.MR.phi_debit_level_repin` | Salt/MR/HalaszIntegersChiClose.lean:408 | characters |
| `Salt.MR.mvt_row_carries_T` | Salt/MR/HalaszIntegersChiClose.lean:496 | characters |
| `Salt.MR.phi_row_carries_M` | Salt/MR/HalaszIntegersChiClose.lean:519 | characters |
| `Salt.MR.hat_desmooth` | Salt/MR/HalaszKernel.lean:98 | characters |
| `Salt.MR.hat_contour_rep` | Salt/MR/HalaszKernel.lean:200 | characters |
| `Salt.MR.hat_mellin_bound` | Salt/MR/HalaszKernel.lean:410 | characters |
| `Salt.MR.lambdaLin_norm_le` | Salt/MR/HalaszLambda.lean:68 | sieves, characters |
| `Salt.MR.lambdaLin_convolution` | Salt/MR/HalaszLambda.lean:283 | characters |
| `Salt.MR.ellLin_lseries_deriv` | Salt/MR/HalaszLambda.lean:353 | zeros, characters |
| `Salt.MR.zeta_near_strip_growth` | Salt/MR/HalaszPrimes.lean:120 | zeros, characters |
| `Salt.MR.primes_dual_iff` | Salt/MR/HalaszPrimes.lean:158 | characters |
| `Salt.MR.norm_chi_vonMangoldt_twist_le` | Salt/MR/HalaszPrimesChi.lean:132 | sieves, characters |
| `Salt.MR.lambda_window_rep_chi` | Salt/MR/HalaszPrimesChi.lean:158 | sieves, characters |
| `Salt.MR.loglog_ge_hundred` | Salt/MR/HalaszPrimesChi.lean:531 | characters |
| `Salt.MR.logDn_mono` | Salt/MR/HalaszPrimesChi.lean:542 | characters |
| `Salt.MR.twisted_rect_zero_free_split` | Salt/MR/HalaszPrimesChi.lean:567 | characters |
| `Salt.MR.primeWindow_contour_rep` | Salt/MR/HalaszPrimesCore.lean:237 | characters |
| `Salt.MR.lambda_window_rep` | Salt/MR/HalaszPrimesCore.lean:301 | zeros, sieves, characters |
| `Salt.MR.norm_logDeriv_zeta_cline_le` | Salt/MR/HalaszPrimesCore.lean:364 | zeros, sieves, characters |
| `Salt.MR.rep_truncated` | Salt/MR/HalaszPrimesCore.lean:474 | characters |
| `Salt.MR.rect_zero_free` | Salt/MR/HalaszPrimesCore.lean:698 | characters |
| `Salt.MR.pole_residue_term` | Salt/MR/HalaszPrimesCore.lean:922 | zeros, characters |
| `Salt.MR.shifted_edge_price` | Salt/MR/HalaszPrimesCore.lean:1467 | zeros, characters |
| `Salt.MR.window_dominates` | Salt/MR/HalaszPrimesCore.lean:1643 | sieves, characters |
| `Salt.MR.prime_power_discard` | Salt/MR/HalaszPrimesCore.lean:1753 | sieves, characters |
| `Salt.MR.error_double_row` | Salt/MR/HalaszPrimesCore.lean:3138 | characters |
| `Salt.MR.absorb_arith` | Salt/MR/HalaszPrimesCore.lean:3561 | characters |
| `Salt.MR.shifted_dirichlet_ftc` | Salt/MR/HalaszRep.lean:121 | zeros, characters |
| `Salt.MR.line_integral_tsum_swap` | Salt/MR/HalaszRep.lean:231 | characters |
| `Salt.MR.ellLin_split` | Salt/MR/HalaszRepAsm.lean:142 | characters |
| `Salt.MR.prop21_contour_leg` | Salt/MR/HalaszRepAsm.lean:405 | characters |
| `Salt.MR.prop21_contour_leg_unwindowed` | Salt/MR/HalaszRepAsm.lean:430 | characters |
| `Salt.MR.prop21_analog` | Salt/MR/HalaszRepAsm.lean:520 | characters |
| `Salt.MR.prop21_desmooth_reduction` | Salt/MR/HalaszSeam.lean:238 | characters |
| `Salt.MR.lambdaLin_window_bound` | Salt/MR/HalaszSeam.lean:251 | characters |
| `Salt.MR.fgJ_factorization` | Salt/MR/HalaszSeam.lean:298 | characters |
| `Salt.MR.s2_tail_ledger` | Salt/MR/HalaszSeam.lean:316 | characters |
| `Salt.MR.contour_A13_A14_head_wired` | Salt/MR/HalaszSeam.lean:539 | characters |
| `Salt.MR.exists_unimodular_mul_eq_norm` | Salt/MR/HalaszWeighted.lean:70 | characters |
| `Salt.MR.sum_norm_dirichletPolyChi_eq` | Salt/MR/HalaszWeighted.lean:78 | characters |
| `Salt.MR.sq_sum_norm_dirichletPolyChi_le` | Salt/MR/HalaszWeighted.lean:128 | characters |
| `Salt.MR.sum_mul_norm_sq_eq_halaszB` | Salt/MR/HalaszWeighted.lean:168 | characters |
| `Salt.MR.halasz_weighted` | Salt/MR/HalaszWeighted.lean:188 | characters |
| `Salt.MR.halasz_weighted_tsum` | Salt/MR/HalaszWeighted.lean:204 | characters |
| `Salt.MR.halaszBTsum_eq` | Salt/MR/HalaszWeighted.lean:259 | characters |
| `Salt.MR.widthA_plancherel` | Salt/MR/HeadGrade.lean:178 | characters |
| `Salt.MR.offdiag_widthA_eval` | Salt/MR/HeadGrade.lean:333 | sieves, characters |
| `Salt.MR.offdiag_widthA_sharp` | Salt/MR/HeadGrade.lean:660 | characters |
| `Salt.MR.band_second_moment` | Salt/MR/HeadGrade.lean:742 | characters |
| `Salt.MR.head_split_ledger` | Salt/MR/HeadGrade.lean:806 | characters |
| `Salt.MR.kernel_tail_mass` | Salt/MR/HeadGrade.lean:842 | characters |
| `Salt.MR.tail_band_sum` | Salt/MR/HeadGrade.lean:895 | characters |
| `Salt.MR.hband_discharge` | Salt/MR/HeadGrade.lean:1067 | sieves, characters |
| `Salt.MR.offdiag_widthA_final` | Salt/MR/HeadGrade.lean:1222 | sieves, characters |
| `Salt.MR.head_second_moment_grade` | Salt/MR/HeadGrade.lean:1263 | sieves, characters |
| `Salt.MR.crossKer_head_tail_grade` | Salt/MR/HeadGrade.lean:1417 | characters |
| `Salt.MR.kernel_head_mass` | Salt/MR/HeadGrade.lean:1457 | characters |
| `Salt.MR.head_integral_discharged` | Salt/MR/HeadGrade.lean:1488 | characters |
| `Salt.MR.crossKer_grade_final` | Salt/MR/HeadGrade.lean:1582 | characters |
| `Salt.MR.low_leg_shift` | Salt/MR/HeadGrade.lean:1609 | characters |
| `Salt.MR.sqNorm_cs_band` | Salt/MR/HeadGrade.lean:1655 | characters |
| `Salt.MR.head_sharp_socket` | Salt/MR/HeadGrade.lean:1722 | characters |
| `Salt.MR.crossKer_grade_sharp` | Salt/MR/HeadGrade.lean:1843 | characters |
| `Salt.MR.offdiag_widthA_sharp_low` | Salt/MR/HeadGrade.lean:1991 | characters |
| `Salt.MR.offdiag_widthA_final_low` | Salt/MR/HeadGrade.lean:2067 | sieves, characters |
| `Salt.MR.head_second_moment_grade_low` | Salt/MR/HeadGrade.lean:2101 | sieves, characters |
| `Salt.MR.crossKer_grade_decayed` | Salt/MR/HeadGrade.lean:2245 | characters |
| `Salt.MR.exists_charFibre` | Salt/MR/HybridLargeValues.lean:99 | characters |
| `Salt.MR.hasDerivAt_dpolyChi` | Salt/MR/HybridLargeValues.lean:157 | characters |
| `Salt.MR.deriv_dpolyChi` | Salt/MR/HybridLargeValues.lean:174 | characters |
| `Salt.MR.contDiff_dpolyChi` | Salt/MR/HybridLargeValues.lean:189 | characters |
| `Salt.MR.continuous_deriv_dpolyChi` | Salt/MR/HybridLargeValues.lean:195 | characters |
| `Salt.MR.sum_dtwist_sq_le_subset` | Salt/MR/HybridLargeValues.lean:207 | characters |
| `Salt.MR.hybrid_char_mvt_deriv` | Salt/MR/HybridLargeValues.lean:225 | characters |
| `Salt.MR.hybrid_l2_arith` | Salt/MR/HybridLargeValues.lean:253 | characters |
| `Salt.MR.norm_coeffChiTwist_le` | Salt/MR/HybridLargeValues.lean:488 | characters |
| `Salt.MR.kconv_coeffChiTwist` | Salt/MR/HybridLargeValues.lean:498 | characters |
| `Salt.MR.norm_dpolyChi_pow` | Salt/MR/HybridLargeValues.lean:523 | characters |
| `Salt.MR.card_mul_pow_le_hybrid` | Salt/MR/HybridLargeValues.lean:536 | characters |
| `Salt.MR.classSet_meanSq_le` | Salt/MR/HybridMVT.lean:60 | characters |
| `Salt.MR.sum_unitClass_mass` | Salt/MR/HybridMVT.lean:92 | characters |
| `Salt.MR.hybrid_char_mvt` | Salt/MR/HybridMVT.lean:129 | characters |
| `Salt.MR.hybrid_char_mvt_full` | Salt/MR/HybridMVT.lean:179 | characters |
| `Salt.MR.norm_conj_chi_le_one` | Salt/MR/HybridMoments.lean:120 | characters |
| `Salt.MR.norm_chiBarCoeff_le` | Salt/MR/HybridMoments.lean:126 | characters |
| `Salt.MR.norm_chiBarCoeff_le_one` | Salt/MR/HybridMoments.lean:134 | characters |
| `Salt.MR.sum_chiBar_reindex` | Salt/MR/HybridMoments.lean:142 | characters |
| `Salt.MR.chiBarCoeff_eq_inv` | Salt/MR/HybridMoments.lean:150 | characters |
| `Salt.MR.spoly_chiBarCoeff_eq_dpolyChi` | Salt/MR/HybridMoments.lean:157 | characters |
| `Salt.MR.hybrid_char_spoly_mvt` | Salt/MR/HybridMoments.lean:175 | characters |
| `Salt.MR.chiBarAf_one` | Salt/MR/HybridMoments.lean:218 | characters |
| `Salt.MR.chiBarAf_mul` | Salt/MR/HybridMoments.lean:223 | characters |
| `Salt.MR.pmul_pow_of_chiBarAf` | Salt/MR/HybridMoments.lean:233 | characters |
| `Salt.MR.ramQaf_chiBar` | Salt/MR/HybridMoments.lean:248 | characters |
| `Salt.MR.ramRaf_chiBar` | Salt/MR/HybridMoments.lean:262 | characters |
| `Salt.MR.multShiuCoeff_chiBar` | Salt/MR/HybridMoments.lean:280 | characters |
| `Salt.MR.ramQ_pow_mul_ramR_chiBar_eq_spoly` | Salt/MR/HybridMoments.lean:292 | characters |
| `Salt.MR.multShiuChi_moment` | Salt/MR/HybridMoments.lean:322 | characters |
| `Salt.MR.multShiuChi_moment_KMT` | Salt/MR/HybridMoments.lean:401 | characters |
| `Salt.MR.spoly_chiBar_plancherel_at_zero` | Salt/MR/HybridMoments.lean:441 | characters |
| `Salt.MR.multShiuChi_moment_T1` | Salt/MR/HybridMoments.lean:459 | characters |
| `Salt.MR.card_dirichletChar` | Salt/MR/HybridMoments.lean:492 | characters |
| `Salt.MR.sum_const_dirichletChar` | Salt/MR/HybridMoments.lean:498 | characters |
| `Salt.MR.conj_chi_natCast_mul` | Salt/MR/HybridMoments.lean:504 | characters |
| `Salt.MR.chiBar_hcoef` | Salt/MR/HybridMoments.lean:512 | characters |
| `Salt.MR.windowMassChi_le` | Salt/MR/HybridMoments.lean:524 | characters |
| `Salt.MR.ramP2coeff_chiBar` | Salt/MR/HybridMoments.lean:557 | characters |
| `Salt.MR.ramP2corr_chiBar_eq_spoly` | Salt/MR/HybridMoments.lean:571 | characters |
| `Salt.MR.ramCopTail_chiBar_eq_spoly` | Salt/MR/HybridMoments.lean:582 | characters |
| `Salt.MR.ramErr_meanSq_all_chi` | Salt/MR/HybridMoments.lean:604 | characters |
| `Salt.MR.lemma12_meansq_all_chi` | Salt/MR/HybridMoments.lean:712 | characters |
| `Salt.MR.prod_one_sub_blockAvoid` | Salt/MR/JFactor.lean:130 | characters |
| `Salt.MR.alt_sum_blockAvoid_dirichlet` | Salt/MR/JFactor.lean:155 | characters |
| `Salt.MR.norm_exp_half_sub_le` | Salt/MR/JFactor.lean:226 | characters |
| `Salt.MR.block_factor_le_one` | Salt/MR/JFactor.lean:305 | characters |
| `Salt.MR.jfactor_alt_sum_le` | Salt/MR/JFactor.lean:441 | characters |
| `Salt.MR.jfactor_alt_sum_le_euler` | Salt/MR/JFactor.lean:471 | characters |
| `Salt.MR.joint_cs_factoring` | Salt/MR/JointHead.lean:192 | characters |
| `Salt.MR.sigma_wiring` | Salt/MR/JointHead.lean:271 | characters |
| `Salt.MR.joint_grade_assembly` | Salt/MR/JointHead.lean:294 | characters |
| `Salt.MR.kernel_L1_mass_sharp` | Salt/MR/JointHead.lean:441 | characters |
| `Salt.MR.lorentz_compare` | Salt/MR/JointHead.lean:543 | characters |
| `Salt.MR.mixed_weight_cs` | Salt/MR/JointHead.lean:563 | characters |
| `Salt.MR.offdiag_window_eval` | Salt/MR/JointHead.lean:728 | sieves, characters |
| `Salt.MR.intervalIntegrable_beta_leg` | Salt/MR/JointPlumb.lean:306 | characters |
| `Salt.MR.intervalIntegrable_alpha_leg` | Salt/MR/JointPlumb.lean:342 | characters |
| `Salt.MR.intervalIntegrable_beta_leg'` | Salt/MR/JointPlumb.lean:417 | characters |
| `Salt.MR.intervalIntegrable_alpha_leg'` | Salt/MR/JointPlumb.lean:455 | characters |
| `Salt.MR.jointIntegrableAt_of_gates` | Salt/MR/JointPlumb.lean:513 | characters |
| `Salt.MR.jointIntegrableAt_discharged` | Salt/MR/JointPlumb.lean:533 | characters |
| `Salt.MR.jointIntegrableAt_pin` | Salt/MR/JointPlumb.lean:566 | characters |
| `Salt.Entropy.Chowla.chowlaRegimeFlat_exists_param_head_gceil` | Salt/MR/KLever.lean:106 | characters |
| `Salt.MR.exp_sixteen_eq` | Salt/MR/KLever.lean:150 | characters |
| `Salt.MR.KlevF_ge` | Salt/MR/KLever.lean:155 | characters |
| `Salt.MR.KlevF_lt` | Salt/MR/KLever.lean:160 | characters |
| `Salt.MR.KlevF_le_wideCeiling` | Salt/MR/KLever.lean:172 | characters |
| `Salt.MR.s16_baseScaleCapEnd_L_of_xceil` | Salt/MR/KLever.lean:215 | characters |
| `Salt.MR.klevF_capNumeral` | Salt/MR/KLever.lean:334 | characters |
| `Salt.MR.s16_baseScaleCap96_L_at_klevF` | Salt/MR/KLever.lean:427 | characters |
| `Salt.MR.calFrameK_doorH1_at_L_gk_flat` | Salt/MR/KLever.lean:492 | characters |
| `Salt.MR.dampA_normSq` | Salt/MR/KernelCarry.lean:130 | characters |
| `Salt.MR.vSeg_eq_damp_endpoints` | Salt/MR/KernelCarry.lean:139 | characters |
| `Salt.MR.uKernel_norm_le` | Salt/MR/KernelCarry.lean:184 | characters |
| `Salt.MR.uKernel_wdiff_norm_le` | Salt/MR/KernelCarry.lean:210 | characters |
| `Salt.MR.vtail_meansq_damped` | Salt/MR/KernelCarry.lean:331 | characters |
| `Salt.MR.vtail_meansq_kernel` | Salt/MR/KernelCarry.lean:664 | characters |
| `Salt.MR.vtail_meansq_kernel_neg` | Salt/MR/KernelCarry.lean:733 | characters |
| `Salt.MR.lemma14_contour_kernel` | Salt/MR/KernelCarry.lean:938 | characters |
| `Salt.MR.lemma14_shortInterval_meansq_kernel` | Salt/MR/KernelCarry.lean:1153 | characters |
| `Salt.MR.continuous_dpoly` | Salt/MR/L2MVT.lean:47 | characters |
| `Salt.MR.sq_norm_dpoly_eq` | Salt/MR/L2MVT.lean:55 | characters |
| `Salt.MR.dirichlet_poly_l2_expand` | Salt/MR/L2MVT.lean:97 | characters |
| `Salt.MR.dirichlet_poly_l2_diagonal` | Salt/MR/L2MVT.lean:127 | characters |
| `Salt.MR.norm_LFunction_inv_shallow_of_ball` | Salt/MR/LFunctionInvShallow.lean:111 | characters |
| `Salt.MR.LFunction_ne_zero_of_shallow_ball` | Salt/MR/LFunctionInvShallow.lean:254 | characters |
| `Salt.MR.one_le_shallowGrowth` | Salt/MR/LFunctionInvShallow.lean:300 | characters |
| `Salt.MR.norm_LFunction_le_shallowGrowth` | Salt/MR/LFunctionInvShallow.lean:324 | characters |
| `Salt.MR.vkShallowWidthSharp_le` | Salt/MR/LFunctionInvShallow.lean:462 | characters |
| `Salt.MR.one_le_shallowA` | Salt/MR/LFunctionInvShallow.lean:501 | characters |
| `Salt.MR.shallowA_gate` | Salt/MR/LFunctionInvShallow.lean:507 | characters |
| `Salt.MR.shallowA_lb` | Salt/MR/LFunctionInvShallow.lean:516 | characters |
| `Salt.MR.shallowA_ub` | Salt/MR/LFunctionInvShallow.lean:522 | characters |
| `Salt.MR.boxWidth_shallow_lower` | Salt/MR/LFunctionInvShallow.lean:540 | characters |
| `Salt.MR.log_budget_bound` | Salt/MR/LFunctionInvShallow.lean:672 | characters |
| `Salt.MR.boxWidth_le_carve` | Salt/MR/LFunctionInvShallow.lean:803 | characters |
| `Salt.MR.norm_LFunction_inv_shallow_sharp` | Salt/MR/LFunctionInvShallow.lean:878 | characters |
| `Salt.MR.sq_div_sixteen_log_le` | Salt/MR/LFunctionInvShallow.lean:1174 | characters |
| `Salt.MR.exists_shallowConst` | Salt/MR/LFunctionInvShallow.lean:1199 | characters |
| `Salt.MR.lFunctionInvShallowVkSharp_holds` | Salt/MR/LFunctionInvShallow.lean:1260 | characters |
| `Salt.MR.carve_of_half` | Salt/MR/LFunctionInvShallow.lean:1363 | characters |
| `Salt.MR.lamGrMask_isMultiplicative` | Salt/MR/LambdaChiMask.lean:100 | characters |
| `Salt.MR.lamTailWeightMask_eq_zero_of_not_squarefree` | Salt/MR/LambdaChiMask.lean:145 | characters |
| `Salt.MR.lamTailWeightMask_nonneg` | Salt/MR/LambdaChiMask.lean:155 | characters |
| `Salt.MR.lamTailWeightMask_le_maskTailWeight` | Salt/MR/LambdaChiMask.lean:164 | characters |
| `Salt.MR.lamTailWeightMask_support` | Salt/MR/LambdaChiMask.lean:174 | characters |
| `Salt.MR.lamTailWeightMask_le_zero_param` | Salt/MR/LambdaChiMask.lean:183 | characters |
| `Salt.MR.lamTailWeightMask_isMultiplicative` | Salt/MR/LambdaChiMask.lean:191 | characters |
| `Salt.MR.lamTailWeightMask_prime_pow` | Salt/MR/LambdaChiMask.lean:212 | characters |
| `Salt.MR.lamTailWeightMask_mul_liouville` | Salt/MR/LambdaChiMask.lean:246 | characters |
| `Salt.MR.liouville_mul_lamTailWeightMask` | Salt/MR/LambdaChiMask.lean:304 | characters |
| `Salt.MR.lamGrMask_eq_sum_divisorsAntidiagonal` | Salt/MR/LambdaChiMask.lean:312 | characters |
| `Salt.MR.lamGrMask_twist_eq_sum_divisorsAntidiagonal` | Salt/MR/LambdaChiMask.lean:323 | characters |
| `Salt.MR.MlamGrChiMask_eq_sum` | Salt/MR/LambdaChiMask.lean:366 | characters |
| `Salt.MR.norm_MlamGrChiMask_le_split` | Salt/MR/LambdaChiMask.lean:431 | characters |
| `Salt.MR.lamGrMask_blockMask` | Salt/MR/LambdaChiMask.lean:644 | characters |
| `Salt.MR.lamTailWeightMask_blockMask` | Salt/MR/LambdaChiMask.lean:649 | characters |
| `Salt.MR.MlamGrChiMask_blockMask` | Salt/MR/LambdaChiMask.lean:654 | characters |
| `Salt.MR.lamGr_isMultiplicative` | Salt/MR/LambdaChiRamare.lean:140 | characters |
| `Salt.MR.lamTailWeight_eq_zero_of_not_squarefree` | Salt/MR/LambdaChiRamare.lean:187 | characters |
| `Salt.MR.lamTailWeight_nonneg` | Salt/MR/LambdaChiRamare.lean:198 | characters |
| `Salt.MR.lamTailWeight_le_ramTailWeight` | Salt/MR/LambdaChiRamare.lean:207 | characters |
| `Salt.MR.lamTailWeight_support` | Salt/MR/LambdaChiRamare.lean:218 | characters |
| `Salt.MR.lamTailWeight_le_zero_param` | Salt/MR/LambdaChiRamare.lean:228 | characters |
| `Salt.MR.lamTailWeight_isMultiplicative` | Salt/MR/LambdaChiRamare.lean:236 | characters |
| `Salt.MR.lamTailWeight_prime_pow` | Salt/MR/LambdaChiRamare.lean:259 | characters |
| `Salt.MR.lamTailWeight_mul_liouville` | Salt/MR/LambdaChiRamare.lean:292 | characters |
| `Salt.MR.liouville_mul_lamTailWeight` | Salt/MR/LambdaChiRamare.lean:352 | characters |
| `Salt.MR.lamGr_eq_sum_divisorsAntidiagonal` | Salt/MR/LambdaChiRamare.lean:363 | characters |
| `Salt.MR.lamGr_twist_eq_sum_divisorsAntidiagonal` | Salt/MR/LambdaChiRamare.lean:376 | characters |
| `Salt.MR.sum_filter_dvd_div_eq` | Salt/MR/LambdaChiRamare.lean:411 | characters |
| `Salt.MR.MlambdaChi_inner_dvd` | Salt/MR/LambdaChiRamare.lean:441 | characters |
| `Salt.MR.MlamGrChi_eq_sum` | Salt/MR/LambdaChiRamare.lean:463 | characters |
| `Salt.MR.norm_MlambdaChi_le` | Salt/MR/LambdaChiRamare.lean:524 | characters |
| `Salt.MR.norm_MlamGrChi_le_split` | Salt/MR/LambdaChiRamare.lean:553 | characters |
| `Salt.MR.MlamRamChi_eq_integral` | Salt/MR/LambdaChiRamare.lean:783 | characters |
| `Salt.MR.norm_MlamRamChi_le_of_uniform` | Salt/MR/LambdaChiRamare.lean:808 | characters |
| `Salt.MR.prop21_unconditional_uniform_absC` | Salt/MR/LambdaMass.lean:243 | characters |
| `Salt.MR.prop21_uniform_at_scale_absC` | Salt/MR/LambdaMass.lean:325 | characters |
| `Salt.MR.vonMangoldt_window_damped_min` | Salt/MR/LambdaMass.lean:638 | characters |
| `Salt.MR.vonMangoldt_window_shifted_min` | Salt/MR/LambdaMass.lean:745 | characters |
| `Salt.MR.lambdaLin_window_damped_min` | Salt/MR/LambdaMass.lean:775 | characters |
| `Salt.MR.lambdaLin_window_shifted_min` | Salt/MR/LambdaMass.lean:788 | characters |
| `Salt.MR.mul_apply_mul_twist` | Salt/MR/LambdaRateTwisted.lean:182 | characters |
| `Salt.MR.pmul_mul_of_twist` | Salt/MR/LambdaRateTwisted.lean:205 | characters |
| `Salt.MR.chiBarTwist_mul` | Salt/MR/LambdaRateTwisted.lean:229 | characters |
| `Salt.MR.norm_chiBarTwist_le_one` | Salt/MR/LambdaRateTwisted.lean:250 | characters |
| `Salt.MR.liouville_twist_eq_sum_divisorsAntidiagonal` | Salt/MR/LambdaRateTwisted.lean:274 | characters |
| `Salt.MR.liouville_twist_eq_sum_moebius_twist` | Salt/MR/LambdaRateTwisted.lean:328 | characters |
| `Salt.MR.MmuChi_inner` | Salt/MR/LambdaRateTwisted.lean:359 | characters |
| `Salt.MR.MlambdaChi_eq_sum_MmuChi` | Salt/MR/LambdaRateTwisted.lean:394 | characters |
| `Salt.MR.norm_MmuChi_le` | Salt/MR/LambdaRateTwisted.lean:463 | characters |
| `Salt.MR.norm_one_sub_le_of_one_le_re` | Salt/MR/LandauDescent.lean:72 | characters |
| `Salt.MR.norm_eulerProd_lower` | Salt/MR/LandauDescent.lean:104 | characters |
| `Salt.MR.eulerCorr_prod_lower_real` | Salt/MR/LandauDescent.lean:135 | characters |
| `Salt.MR.eulerCorr_one_lower` | Salt/MR/LandauDescent.lean:141 | characters |
| `Salt.MR.primitiveCharacter_ne_one` | Salt/MR/LandauDescent.lean:150 | characters |
| `Salt.MR.primitiveCharacter_quadratic` | Salt/MR/LandauDescent.lean:157 | characters |
| `Salt.MR.primitiveCharacter_conductor_le` | Salt/MR/LandauDescent.lean:165 | characters |
| `Salt.MR.norm_LFunction_one_eq_re` | Salt/MR/LandauDescent.lean:172 | characters |
| `Salt.MR.L1LowerEffective_descend` | Salt/MR/LandauDescent.lean:197 | characters |
| `Salt.MR.primitiveCharacter_neg_one` | Salt/MR/LandauDescent.lean:241 | characters |
| `Salt.MR.L1LowerEffectiveOdd_descend` | Salt/MR/LandauDescent.lean:268 | characters |
| `Salt.MR.L1LowerEffective_half_iff` | Salt/MR/LandauL1.lean:171 | characters |
| `Salt.MR.log_le_two_mul_sqrt` | Salt/MR/LandauL1.lean:187 | characters |
| `Salt.MR.logq_absorbed` | Salt/MR/LandauL1.lean:197 | characters |
| `Salt.MR.door_L1_absorbed` | Salt/MR/LandauL1.lean:249 | characters |
| `Salt.MR.door_L1_absorbed_subexp` | Salt/MR/LandauL1.lean:274 | characters |
| `Salt.MR.debit_le_affine_log` | Salt/MR/LandauL1.lean:328 | characters |
| `Salt.MR.door_L1_debit_absorbed` | Salt/MR/LandauL1.lean:375 | characters |
| `Salt.MR.dhA_sqrt_weighted_floor` | Salt/MR/LandauL1.lean:481 | characters |
| `Salt.MR.rootNumber_norm_eq_one` | Salt/MR/LandauOdd.lean:101 | characters |
| `Salt.MR.mod_ne_one_of_odd` | Salt/MR/LandauOdd.lean:119 | characters |
| `Salt.MR.odd_inv` | Salt/MR/LandauOdd.lean:126 | characters |
| `Salt.MR.LFunction_apply_zero_eq_completed_odd` | Salt/MR/LandauOdd.lean:133 | characters |
| `Salt.MR.LFunction_apply_one_eq_completed_odd` | Salt/MR/LandauOdd.lean:141 | characters |
| `Salt.MR.LFunction_apply_zero_odd_fe` | Salt/MR/LandauOdd.lean:151 | characters |
| `Salt.MR.norm_LFunction_apply_one_odd` | Salt/MR/LandauOdd.lean:165 | characters |
| `Salt.MR.inv_eq_self_of_sq_eq_one` | Salt/MR/LandauOdd.lean:180 | characters |
| `Salt.MR.LFunction_apply_zero_ne_zero_odd` | Salt/MR/LandauOdd.lean:188 | characters |
| `Salt.MR.norm_LFunction_one_eq_re'` | Salt/MR/LandauOdd.lean:201 | characters |
| `Salt.MR.rpow_three_halves` | Salt/MR/LandauOdd.lean:210 | characters |
| `Salt.MR.L1_lower_odd_of_L0_floor` | Salt/MR/LandauOdd.lean:220 | characters |
| `Salt.MR.val_cases_of_sq_eq_one` | Salt/MR/LandauOdd.lean:280 | characters |
| `Salt.MR.exists_int_sum_val_mul` | Salt/MR/LandauOdd.lean:292 | characters |
| `Salt.MR.primitiveCharacter_ne_one'` | Salt/MR/LandauOdd.lean:351 | characters |
| `Salt.MR.primitiveCharacter_odd` | Salt/MR/LandauOdd.lean:358 | characters |
| `Salt.MR.primitiveCharacter_sq_eq_one` | Salt/MR/LandauOdd.lean:368 | characters |
| `Salt.MR.LFunction_apply_one_descent` | Salt/MR/LandauOdd.lean:376 | characters |
| `Salt.MR.descent_prod_eq_real` | Salt/MR/LandauOdd.lean:389 | characters |
| `Salt.MR.dpoly_pow` | Salt/MR/LargeValueCount.lean:106 | characters |
| `Salt.MR.kconv_l1_le` | Salt/MR/LargeValueCount.lean:182 | characters |
| `Salt.MR.kconv_sup_le_window` | Salt/MR/LargeValueCount.lean:346 | characters |
| `Salt.MR.kconv_l2_le_window` | Salt/MR/LargeValueCount.lean:368 | characters |
| `Salt.MR.lemma14_contour` | Salt/MR/Lemma14.lean:295 | characters |
| `Salt.MR.lemma14_contour_grouped` | Salt/MR/Lemma14.lean:416 | characters |
| `Salt.MR.lemma14_shortInterval_of_perron` | Salt/MR/Lemma14.lean:667 | characters |
| `Salt.MR.Aperron_short_interval` | Salt/MR/Lemma14Bridge.lean:93 | characters |
| `Salt.MR.Aperron_short_interval_collapsed` | Salt/MR/Lemma14Bridge.lean:196 | characters |
| `Salt.MR.dyadic_tail_proper` | Salt/MR/Lemma14Bridge.lean:285 | characters |
| `Salt.MR.taylor2_bound` | Salt/MR/Lemma14Taylor.lean:102 | characters |
| `Salt.MR.uSlab_taylor_main` | Salt/MR/Lemma14Taylor.lean:350 | characters |
| `Salt.MR.uSlab_taylor_main_sq` | Salt/MR/Lemma14Taylor.lean:373 | characters |
| `Salt.MR.xTentT_eq` | Salt/MR/Lemma14Vtail.lean:269 | characters |
| `Salt.MR.tailT_mean_sq_bound` | Salt/MR/Lemma14Vtail.lean:832 | characters |
| `Salt.MR.vtail_mean_sq_bound` | Salt/MR/Lemma14Vtail.lean:1022 | characters |
| `Salt.MR.sum_Ioc_abel_complex` | Salt/MR/M4Abel.lean:92 | characters |
| `Salt.MR.sum_Ioc_abel_complex_const` | Salt/MR/M4Abel.lean:108 | characters |
| `Salt.MR.norm_sum_Ioc_abel_le` | Salt/MR/M4Abel.lean:121 | characters |
| `Salt.MR.norm_sum_Ioc_weighted_le_drift` | Salt/MR/M4Abel.lean:137 | characters |
| `Salt.MR.norm_eR_succ_sub` | Salt/MR/M4Abel.lean:169 | characters |
| `Salt.MR.norm_phase_sum_Ioc_ibp` | Salt/MR/M4Abel.lean:188 | characters |
| `Salt.MR.norm_phase_sum_Ioc_drift` | Salt/MR/M4Abel.lean:203 | characters |
| `Salt.MR.norm_phase_sum_Ioc_drift_sup` | Salt/MR/M4Abel.lean:215 | characters |
| `Salt.MR.abs_mul_window_le_of_arcDen` | Salt/MR/M4Abel.lean:238 | characters |
| `Salt.MR.norm_phase_sum_arcDen_drift` | Salt/MR/M4Abel.lean:259 | characters |
| `Salt.MR.norm_phase_sum_arcDen_drift_sup` | Salt/MR/M4Abel.lean:275 | characters |
| `Salt.MR.le_of_log_le'` | Salt/MR/M4ArithPage.lean:112 | characters |
| `Salt.MR.exp_one_gt_27` | Salt/MR/M4ArithPage.lean:118 | characters |
| `Salt.MR.pow_27_le_exp` | Salt/MR/M4ArithPage.lean:123 | characters |
| `Salt.MR.log_le_of_le_pow27` | Salt/MR/M4ArithPage.lean:129 | characters |
| `Salt.MR.log_le_div_exp_one` | Salt/MR/M4ArithPage.lean:141 | characters |
| `Salt.MR.log_188133_le` | Salt/MR/M4ArithPage.lean:146 | characters |
| `Salt.MR.log_8448_le` | Salt/MR/M4ArithPage.lean:152 | characters |
| `Salt.MR.log_1787702400_le` | Salt/MR/M4ArithPage.lean:158 | characters |
| `Salt.MR.log_304128_le` | Salt/MR/M4ArithPage.lean:164 | characters |
| `Salt.MR.log_6315000_le` | Salt/MR/M4ArithPage.lean:170 | characters |
| `Salt.MR.renormaliseConst_le_exp17` | Salt/MR/M4ArithPage.lean:182 | characters |
| `Salt.MR.renormaliseConst_pos` | Salt/MR/M4ArithPage.lean:203 | characters |
| `Salt.MR.log_ballSupC_le` | Salt/MR/M4ArithPage.lean:210 | characters |
| `Salt.MR.one_lt_log_of_loglog_ge` | Salt/MR/M4ArithPage.lean:228 | characters |
| `Salt.MR.strataResidual_eq_of_pos` | Salt/MR/M4ArithPage.lean:236 | characters |
| `Salt.MR.one_add_twelve_le_exp` | Salt/MR/M4ArithPage.lean:241 | characters |
| `Salt.MR.arcDen_mul_strataResidual_sq_le` | Salt/MR/M4ArithPage.lean:252 | characters |
| `Salt.MR.doorGrade_summand1_priced` | Salt/MR/M4ArithPage.lean:348 | characters |
| `Salt.MR.doorGrade_summand3_priced` | Salt/MR/M4ArithPage.lean:390 | characters |
| `Salt.MR.doorGrade_summand4_priced` | Salt/MR/M4ArithPage.lean:411 | characters |
| `Salt.MR.doorGrade_summand5_priced` | Salt/MR/M4ArithPage.lean:451 | characters |
| `Salt.MR.calP_door_one` | Salt/MR/M4ArithPage.lean:480 | characters |
| `Salt.MR.calQK_door_one` | Salt/MR/M4ArithPage.lean:483 | characters |
| `Salt.MR.doorGrade_summand2_priced` | Salt/MR/M4ArithPage.lean:490 | characters |
| `Salt.MR.doorRho_pos` | Salt/MR/M4ArithPage.lean:594 | characters |
| `Salt.MR.RSanDoor_nonneg` | Salt/MR/M4ArithPage.lean:601 | characters |
| `Salt.MR.m4_chiSummedFreeRowBig_of_doorGradeGated` | Salt/MR/M4ArithPage.lean:662 | characters |
| `Salt.MR.m4_arith_gate4` | Salt/MR/M4ArithPage.lean:701 | characters |
| `Salt.MR.m4_arith_rs_ceiling_met` | Salt/MR/M4ArithPage.lean:716 | characters |
| `Salt.MR.m4_arith_arm_of_gArm` | Salt/MR/M4ArithPage.lean:823 | characters |
| `Salt.MR.m4_arith_arm_of_shift` | Salt/MR/M4ArithPage.lean:847 | characters |
| `Salt.MR.m4_arith_anchor_of_C1` | Salt/MR/M4ArithPage.lean:855 | characters |
| `Salt.MR.m4_arith_jfloor_of_anchor` | Salt/MR/M4ArithPage.lean:865 | characters |
| `Salt.MR.m4_arith_M0_window_lower` | Salt/MR/M4ArithPage.lean:889 | characters |
| `Salt.MR.m4_arith_M0_window_nonempty` | Salt/MR/M4ArithPage.lean:911 | characters |
| `Salt.MR.doorGrade_summand3_priced_pool_of_decay` | Salt/MR/M4ArithPool.lean:71 | characters |
| `Salt.MR.doorGrade_summand3_priced_rho_pool_of_decay` | Salt/MR/M4ArithPool.lean:88 | characters |
| `Salt.MR.m4_chiSummedFreeRowBig_of_doorGradeGated_pool` | Salt/MR/M4ArithPool.lean:214 | characters |
| `Salt.MR.a2RowsSum_door_decomp` | Salt/MR/M4ArithZero.lean:346 | zeros, characters |
| `Salt.MR.m4_hSup_door_at_zero` | Salt/MR/M4Assembly.lean:104 | characters |
| `Salt.MR.m4_hSup_pieceDatum_perChi` | Salt/MR/M4Assembly.lean:125 | characters |
| `Salt.MR.chiBarCoeff_doorCoeffU` | Salt/MR/M4Assembly.lean:175 | characters |
| `Salt.MR.chiBarCoeff_winCutH` | Salt/MR/M4Assembly.lean:184 | characters |
| `Salt.MR.chiBarCoeff_doorRowDatum` | Salt/MR/M4Assembly.lean:195 | characters |
| `Salt.MR.log_natCast_nonneg'` | Salt/MR/M4Assembly.lean:223 | characters |
| `Salt.MR.a2DoorGrade_nonneg` | Salt/MR/M4Assembly.lean:229 | characters |
| `Salt.MR.m4_chiSummedFreeRowBig_of_doorGrade` | Salt/MR/M4Assembly.lean:355 | characters |
| `Salt.MR.m4_chiSummedFreeRow_of_doorGrade` | Salt/MR/M4Assembly.lean:392 | characters |
| `Salt.MR.doorRows_global_hcoef_kills_block` | Salt/MR/M4Assembly.lean:543 | characters |
| `Salt.MR.a2DoorGrade_pool_nonneg` | Salt/MR/M4AssemblyPool.lean:77 | characters |
| `Salt.MR.m4_chiSummedFreeRowBig_of_doorGrade_pool` | Salt/MR/M4AssemblyPool.lean:225 | characters |
| `Salt.MR.m4_chiSummedFreeRow_of_doorGrade_pool` | Salt/MR/M4AssemblyPool.lean:259 | characters |
| `Salt.MR.blockPrimeDivs_eq_empty_of_large` | Salt/MR/M4Band.lean:79 | characters |
| `Salt.MR.blockOmega_shift_up` | Salt/MR/M4Band.lean:95 | characters |
| `Salt.MR.memS_shift_up` | Salt/MR/M4Band.lean:103 | characters |
| `Salt.MR.indicator_mul_shift_up` | Salt/MR/M4Band.lean:121 | characters |
| `Salt.MR.memSCoeff_seamCoefW_band` | Salt/MR/M4Band.lean:138 | characters |
| `Salt.MR.doorChiCoeff_seamCoefW_band` | Salt/MR/M4Band.lean:169 | characters |
| `Salt.MR.door_band_gate` | Salt/MR/M4Band.lean:183 | characters |
| `Salt.MR.door_band_gate_of_log` | Salt/MR/M4Band.lean:195 | characters |
| `Salt.MR.memSCoeff_seamCoefW_band_gen` | Salt/MR/M4Band.lean:235 | characters |
| `Salt.MR.memSCoeff_seamCoefW_band_H` | Salt/MR/M4Band.lean:262 | characters |
| `Salt.MR.memSCoeff_seamCoefWS_band_gen` | Salt/MR/M4Band.lean:284 | characters |
| `Salt.MR.memSCoeff_seamCoefWS_band_H` | Salt/MR/M4Band.lean:307 | characters |
| `Salt.MR.doorChiCoeff_seamCoefWS_band_H` | Salt/MR/M4Band.lean:314 | characters |
| `Salt.MR.doorChiCoeff_seamCoefWS_at_door_H` | Salt/MR/M4Band.lean:325 | characters |
| `Salt.MR.doorChiCoeff_seamCoefW_band_H` | Salt/MR/M4Band.lean:336 | characters |
| `Salt.MR.doorChiCoeff_seamCoefW_at_door_H` | Salt/MR/M4Band.lean:348 | characters |
| `Salt.MR.m4_chiBlock_at` | Salt/MR/M4BaseNarrow.lean:272 | sieves, characters |
| `Salt.MR.m4_classBlock_at` | Salt/MR/M4BaseNarrow.lean:601 | sieves, characters |
| `Salt.MR.narrow_dilate` | Salt/MR/M4BaseNarrow.lean:864 | characters |
| `Salt.MR.arcDen_le_arcDen_Hhi` | Salt/MR/M4BaseNarrow.lean:1016 | characters |
| `Salt.MR.m4_modulusCap_discharged` | Salt/MR/M4BaseNarrow.lean:1046 | characters |
| `Salt.MR.le_numBlocks_mul` | Salt/MR/M4BridgeBlock.lean:128 | characters |
| `Salt.MR.numBlocks_mul_le` | Salt/MR/M4BridgeBlock.lean:136 | characters |
| `Salt.MR.mul_le_of_lt_numBlocks` | Salt/MR/M4BridgeBlock.lean:143 | characters |
| `Salt.MR.blockCut_eq_of_lt` | Salt/MR/M4BridgeBlock.lean:156 | characters |
| `Salt.MR.blockCut_numBlocks` | Salt/MR/M4BridgeBlock.lean:162 | characters |
| `Salt.MR.blockCut_mono` | Salt/MR/M4BridgeBlock.lean:167 | characters |
| `Salt.MR.blockCut_succ_sub_le` | Salt/MR/M4BridgeBlock.lean:174 | characters |
| `Salt.MR.sum_Ioc_chunk` | Salt/MR/M4BridgeBlock.lean:194 | characters |
| `Salt.MR.subWindowSup_mono_length` | Salt/MR/M4BridgeBlock.lean:212 | characters |
| `Salt.MR.abs_mul_window_le_of_arcDen_block` | Salt/MR/M4BridgeBlock.lean:222 | characters |
| `Salt.MR.norm_block_phase_sum_le` | Salt/MR/M4BridgeBlock.lean:243 | characters |
| `Salt.MR.norm_absWindowSum_le_drift_blocked` | Salt/MR/M4BridgeBlock.lean:268 | characters |
| `Salt.MR.norm_absWindowSum_sq_le_drift_blocked` | Salt/MR/M4BridgeBlock.lean:300 | characters |
| `Salt.MR.blockSupSq_nonneg` | Salt/MR/M4BridgeBlock.lean:333 | characters |
| `Salt.MR.blockSupSq_le_of_norm_le_one` | Salt/MR/M4BridgeBlock.lean:337 | characters |
| `Salt.MR.m4_sievedDoorSqBlk_trivial` | Salt/MR/M4BridgeBlock.lean:463 | sieves, characters |
| `Salt.MR.m4_blockMeanSqBlk_trivial` | Salt/MR/M4BridgeBlock.lean:520 | characters |
| `Salt.MR.blockBase_mem_doorLadder_block` | Salt/MR/M4BridgeBlock.lean:562 | characters |
| `Salt.MR.blockBase_le_two_mul` | Salt/MR/M4BridgeBlock.lean:575 | characters |
| `Salt.MR.doorLadder_pos` | Salt/MR/M4BridgeCover.lean:135 | characters |
| `Salt.MR.doorLadder_top_le_two_mul` | Salt/MR/M4BridgeCover.lean:143 | characters |
| `Salt.MR.block_weight_exchange` | Salt/MR/M4BridgeCover.lean:156 | characters |
| `Salt.MR.block_weight_exchange_tight` | Salt/MR/M4BridgeCover.lean:177 | characters |
| `Salt.MR.door_cover_weighted_le` | Salt/MR/M4BridgeCover.lean:211 | characters |
| `Salt.MR.door_weight_absorb` | Salt/MR/M4BridgeCover.lean:280 | characters |
| `Salt.MR.integral_door_cover_le` | Salt/MR/M4BridgeCover.lean:298 | characters |
| `Salt.MR.integral_door_cover_le_clean` | Salt/MR/M4BridgeCover.lean:341 | characters |
| `Salt.MR.norm_doorSievedCoeff_le_one` | Salt/MR/M4BridgeCover.lean:365 | sieves, characters |
| `Salt.MR.regime_window_headroom` | Salt/MR/M4BridgeCover.lean:371 | characters |
| `Salt.MR.m4_blockMeanSq_trivial` | Salt/MR/M4BridgeCover.lean:426 | characters |
| `Salt.MR.m4_gradeGate_of_block_pricing` | Salt/MR/M4BridgeCover.lean:461 | characters |
| `Salt.MR.m4_gradeGate_of_block_pricing_split` | Salt/MR/M4BridgeCover.lean:533 | characters |
| `Salt.MR.div_add_div_le_add_div` | Salt/MR/M4BridgeDilate.lean:127 | characters |
| `Salt.MR.add_div_le_div_add_div_succ` | Salt/MR/M4BridgeDilate.lean:137 | characters |
| `Salt.MR.le_dilLen` | Salt/MR/M4BridgeDilate.lean:143 | characters |
| `Salt.MR.dilLen_le` | Salt/MR/M4BridgeDilate.lean:150 | characters |
| `Salt.MR.Ioc_dilate_eq` | Salt/MR/M4BridgeDilate.lean:158 | characters |
| `Salt.MR.Ioc_dilate_maps` | Salt/MR/M4BridgeDilate.lean:167 | characters |
| `Salt.MR.dilLen_le_window` | Salt/MR/M4BridgeDilate.lean:179 | characters |
| `Salt.MR.dilLen_le_real` | Salt/MR/M4BridgeDilate.lean:189 | characters |
| `Salt.MR.le_dilLen_real` | Salt/MR/M4BridgeDilate.lean:198 | characters |
| `Salt.MR.d_mul_dilLen_le` | Salt/MR/M4BridgeDilate.lean:212 | characters |
| `Salt.MR.image_div_class_window` | Salt/MR/M4BridgeDilate.lean:232 | characters |
| `Salt.MR.exp_phase_dilate` | Salt/MR/M4BridgeDilate.lean:269 | characters |
| `Salt.MR.norm_classCoeff_le_one` | Salt/MR/M4BridgeDilate.lean:298 | characters |
| `Salt.MR.norm_dilCoeff_le_one` | Salt/MR/M4BridgeDilate.lean:305 | characters |
| `Salt.MR.classWindowSum_dilate` | Salt/MR/M4BridgeDilate.lean:333 | characters |
| `Salt.MR.door_gate_blocks` | Salt/MR/M4BridgeDilate.lean:363 | characters |
| `Salt.MR.dilCoeff_memS_door` | Salt/MR/M4BridgeDilate.lean:378 | characters |
| `Salt.MR.norm_absWindowSum_dilCoeff_memS_door` | Salt/MR/M4BridgeDilate.lean:411 | characters |
| `Salt.MR.norm_absWindowSum_dilLen_le` | Salt/MR/M4BridgeDilate.lean:429 | characters |
| `Salt.MR.norm_classWindowSum_le_thresh` | Salt/MR/M4BridgeDilate.lean:436 | characters |
| `Salt.MR.norm_classWindowSum_le_trivThresh` | Salt/MR/M4BridgeDilate.lean:445 | characters |
| `Salt.MR.integral_logMeasure_classWindowSum_le_thresh` | Salt/MR/M4BridgeDilate.lean:454 | characters |
| `Salt.MR.classWindow_trivial_or_long` | Salt/MR/M4BridgeDilate.lean:466 | characters |
| `Salt.MR.arcDen_dilLen_le` | Salt/MR/M4BridgeDilate.lean:579 | characters |
| `Salt.MR.arcDen_le_dilate_cap` | Salt/MR/M4BridgeDilate.lean:591 | characters |
| `Salt.MR.m4_class_dilate_exit` | Salt/MR/M4BridgeDilate.lean:633 | characters |
| `Salt.MR.m4_class_dilate_coprime` | Salt/MR/M4BridgeDilate.lean:659 | characters |
| `Salt.MR.classPhaseSum_dilate` | Salt/MR/M4BridgeDilate.lean:680 | characters |
| `Salt.MR.norm_classPhaseSum_le_thresh` | Salt/MR/M4BridgeDilate.lean:688 | characters |
| `Salt.MR.norm_absWindowSum_split_dilate_trivial` | Salt/MR/M4BridgeDilate.lean:706 | characters |
| `Salt.MR.shortSum_filter_eq_inter_Ioc` | Salt/MR/M4BridgeIntegral.lean:123 | characters |
| `Salt.MR.shortSum_eq_inter_Ioc` | Salt/MR/M4BridgeIntegral.lean:149 | characters |
| `Salt.MR.mem_unit_cell` | Salt/MR/M4BridgeIntegral.lean:156 | characters |
| `Salt.MR.shortSum_const_unit` | Salt/MR/M4BridgeIntegral.lean:161 | characters |
| `Salt.MR.absWindowSum_eq_shortSum` | Salt/MR/M4BridgeIntegral.lean:175 | characters |
| `Salt.MR.norm_shortSum_nat_sq_le_one` | Salt/MR/M4BridgeIntegral.lean:188 | characters |
| `Salt.MR.shortSum_sq_intervalIntegrable` | Salt/MR/M4BridgeIntegral.lean:257 | characters |
| `Salt.MR.integral_unit_shortSum_sq` | Salt/MR/M4BridgeIntegral.lean:281 | characters |
| `Salt.MR.sum_Ico_shortSum_sq_eq_integral` | Salt/MR/M4BridgeIntegral.lean:305 | characters |
| `Salt.MR.integral_shortSum_sq_mono` | Salt/MR/M4BridgeIntegral.lean:330 | characters |
| `Salt.MR.Ioc_eq_Ico_succ` | Salt/MR/M4BridgeIntegral.lean:346 | characters |
| `Salt.MR.meanSq_nonneg` | Salt/MR/M4BridgeIntegral.lean:352 | characters |
| `Salt.MR.sum_Ioc_shortSum_sq_le_meanSq` | Salt/MR/M4BridgeIntegral.lean:362 | characters |
| `Salt.MR.sum_Ico_le_core_add_boundary` | Salt/MR/M4BridgeIntegral.lean:389 | characters |
| `Salt.MR.sum_Ioc_shortSum_sq_le_meanSq_boundary` | Salt/MR/M4BridgeIntegral.lean:411 | characters |
| `Salt.MR.sum_Ioc_absWindowSum_sq_div_le` | Salt/MR/M4BridgeIntegral.lean:448 | characters |
| `Salt.MR.sum_Ioc_absWindowSum_sq_div_le_ladder` | Salt/MR/M4BridgeIntegral.lean:493 | characters |
| `Salt.MR.m4_bridge_door_sq_le` | Salt/MR/M4BridgeIntegral.lean:523 | characters |
| `Salt.MR.mem_seamS0_of_block_window` | Salt/MR/M4BridgeIntegral.lean:557 | characters |
| `Salt.MR.hcov_of_seamS0` | Salt/MR/M4BridgeIntegral.lean:568 | characters |
| `Salt.MR.m4_bridge_door_gates_witness` | Salt/MR/M4BridgeIntegral.lean:577 | characters |
| `Salt.MR.exp_phase_eq_eR` | Salt/MR/M4BridgePhase.lean:150 | characters |
| `Salt.MR.eR_eq_exp_phase` | Salt/MR/M4BridgePhase.lean:160 | characters |
| `Salt.MR.eR_mul_split` | Salt/MR/M4BridgePhase.lean:167 | characters |
| `Salt.MR.sum_Ioc_phaseCoeff_eq_sub` | Salt/MR/M4BridgePhase.lean:204 | characters |
| `Salt.MR.absWindowSum_eq_phaseCoeff_sum` | Salt/MR/M4BridgePhase.lean:210 | characters |
| `Salt.MR.le_subWindowSup` | Salt/MR/M4BridgePhase.lean:222 | characters |
| `Salt.MR.norm_absWindowSum_le_subWindowSup` | Salt/MR/M4BridgePhase.lean:228 | characters |
| `Salt.MR.subWindowSup_nonneg` | Salt/MR/M4BridgePhase.lean:233 | characters |
| `Salt.MR.subWindowSup_le` | Salt/MR/M4BridgePhase.lean:238 | characters |
| `Salt.MR.subWindowSup_le_of_norm_le_one` | Salt/MR/M4BridgePhase.lean:244 | characters |
| `Salt.MR.abel_sup'_eq_subWindowSup` | Salt/MR/M4BridgePhase.lean:253 | characters |
| `Salt.MR.norm_absWindowSum_le_drift` | Salt/MR/M4BridgePhase.lean:291 | characters |
| `Salt.MR.integral_logMeasure_mono` | Salt/MR/M4BridgePhase.lean:353 | characters |
| `Salt.MR.integral_logMeasure_const_mul` | Salt/MR/M4BridgePhase.lean:362 | characters |
| `Salt.MR.qgraded_drift_price_le` | Salt/MR/M4BridgePhase.lean:403 | characters |
| `Salt.MR.m4_sievedDoorSqSup_trivial` | Salt/MR/M4BridgePhase.lean:492 | sieves, characters |
| `Salt.MR.mem_residueClassOn` | Salt/MR/M4BridgeResidue.lean:115 | characters |
| `Salt.MR.mem_windowClass` | Salt/MR/M4BridgeResidue.lean:119 | characters |
| `Salt.MR.windowClass_subset` | Salt/MR/M4BridgeResidue.lean:123 | characters |
| `Salt.MR.sum_window_residue_partition` | Salt/MR/M4BridgeResidue.lean:134 | characters |
| `Salt.MR.sum_card_windowClass` | Salt/MR/M4BridgeResidue.lean:151 | characters |
| `Salt.MR.norm_ratPhase` | Salt/MR/M4BridgeResidue.lean:181 | characters |
| `Salt.MR.exp_phase_split` | Salt/MR/M4BridgeResidue.lean:187 | characters |
| `Salt.MR.exp_eq_ratPhase_of_modEq` | Salt/MR/M4BridgeResidue.lean:207 | characters |
| `Salt.MR.norm_absWindowSum_residue_split_le` | Salt/MR/M4BridgeResidue.lean:257 | characters |
| `Salt.MR.norm_absWindowSum_residue_split_le_of_eq` | Salt/MR/M4BridgeResidue.lean:267 | characters |
| `Salt.MR.norm_absWindowSum_split_coprime_add` | Salt/MR/M4BridgeResidue.lean:295 | characters |
| `Salt.MR.norm_classPhaseSum_le_card` | Salt/MR/M4BridgeResidue.lean:312 | characters |
| `Salt.MR.sum_norm_classPhaseSum_le` | Salt/MR/M4BridgeResidue.lean:325 | characters |
| `Salt.MR.sum_residueClassOn_liou_eq` | Salt/MR/M4BridgeResidue.lean:346 | characters |
| `Salt.MR.sum_windowClass_liou_eq` | Salt/MR/M4BridgeResidue.lean:358 | characters |
| `Salt.MR.norm_sum_residueClassOn_liou_le` | Salt/MR/M4BridgeResidue.lean:367 | characters |
| `Salt.MR.norm_sum_residueClassOn_liou_le_of_uniform` | Salt/MR/M4BridgeResidue.lean:377 | characters |
| `Salt.MR.norm_sum_windowClass_liou_le_of_uniform` | Salt/MR/M4BridgeResidue.lean:384 | characters |
| `Salt.MR.windowClass_partial` | Salt/MR/M4BridgeResidue.lean:395 | characters |
| `Salt.MR.norm_sum_residueClassOn_Ioc_liou_le_of_uniform` | Salt/MR/M4BridgeResidue.lean:408 | characters |
| `Salt.MR.m4_capKS_at_door` | Salt/MR/M4CapWire.lean:450 | characters |
| `Salt.MR.m4_capE_at_door_of_hcoef` | Salt/MR/M4CapWire.lean:494 | characters |
| `Salt.MR.conj_chi_eq_inv` | Salt/MR/M4Chars.lean:89 | characters |
| `Salt.MR.conj_chi_eq_invChar` | Salt/MR/M4Chars.lean:95 | characters |
| `Salt.MR.chi_inv_eq_conj_chi` | Salt/MR/M4Chars.lean:106 | characters |
| `Salt.MR.norm_chi_of_isUnit` | Salt/MR/M4Chars.lean:116 | characters |
| `Salt.MR.totient_cast_ne_zero` | Salt/MR/M4Chars.lean:126 | characters |
| `Salt.MR.totient_cast_pos` | Salt/MR/M4Chars.lean:132 | characters |
| `Salt.MR.sum_conj_chi_mul_chi` | Salt/MR/M4Chars.lean:145 | characters |
| `Salt.MR.sum_chi_mul_conj_chi` | Salt/MR/M4Chars.lean:162 | characters |
| `Salt.MR.indicator_eq_inv_totient_sum` | Salt/MR/M4Chars.lean:184 | characters |
| `Salt.MR.weight_indicator_eq_inv_totient_sum` | Salt/MR/M4Chars.lean:199 | characters |
| `Salt.MR.lam_indicator_eq_lamChi_sum` | Salt/MR/M4Chars.lean:222 | characters |
| `Salt.MR.lam_modEq_indicator_eq_lamChi_sum` | Salt/MR/M4Chars.lean:231 | characters |
| `Salt.MR.sum_weight_residue_eq` | Salt/MR/M4Chars.lean:251 | characters |
| `Salt.MR.sum_lam_residue_eq` | Salt/MR/M4Chars.lean:274 | characters |
| `Salt.MR.norm_sum_lam_residue_le` | Salt/MR/M4Chars.lean:285 | characters |
| `Salt.MR.isUnit_natCast_of_coprime` | Salt/MR/M4Chars.lean:300 | characters |
| `Salt.MR.sum_lam_modEq_residue_eq` | Salt/MR/M4Chars.lean:307 | characters |
| `Salt.MR.norm_sum_lam_modEq_residue_le` | Salt/MR/M4Chars.lean:318 | characters |
| `Salt.MR.chiFreeRowSq_le_four` | Salt/MR/M4ChiSummed.lean:169 | characters |
| `Salt.MR.m4_chiSummedFreeRow_trivial` | Salt/MR/M4ChiSummed.lean:216 | characters |
| `Salt.MR.chiFreeShift_pointwise` | Salt/MR/M4ChiSummed.lean:278 | sieves, characters |
| `Salt.MR.m4_chiSummedShiftBlock_trivial` | Salt/MR/M4ChiSummed.lean:411 | characters |
| `Salt.MR.m4_chiSummedBlockN_trivial` | Salt/MR/M4ChiSummed.lean:546 | characters |
| `Salt.MR.absWindowSum_classCoeff_zero` | Salt/MR/M4ClassPrice.lean:127 | characters |
| `Salt.MR.norm_absWindowSum_rat_le_class_sums` | Salt/MR/M4ClassPrice.lean:137 | characters |
| `Salt.MR.absWindowSum_classCoeff_rat` | Salt/MR/M4ClassPrice.lean:148 | characters |
| `Salt.MR.norm_absWindowSum_classCoeff_rat` | Salt/MR/M4ClassPrice.lean:165 | characters |
| `Salt.MR.mem_sievedWindow` | Salt/MR/M4ClassPrice.lean:184 | sieves, characters |
| `Salt.MR.sum_windowClass_indicator` | Salt/MR/M4ClassPrice.lean:191 | sieves, characters |
| `Salt.MR.sum_windowClass_memSCoeff` | Salt/MR/M4ClassPrice.lean:202 | sieves, characters |
| `Salt.MR.norm_sum_windowClass_memS_le_of_uniform` | Salt/MR/M4ClassPrice.lean:211 | sieves, characters |
| `Salt.MR.norm_sum_windowClass_memS_dilate` | Salt/MR/M4ClassPrice.lean:232 | characters |
| `Salt.MR.m4_class_price` | Salt/MR/M4ClassPrice.lean:265 | sieves, characters |
| `Salt.MR.norm_absWindowSum_rat_le_class_count` | Salt/MR/M4ClassPrice.lean:302 | characters |
| `Salt.MR.subWindowSup_le_class_count` | Salt/MR/M4ClassPrice.lean:315 | characters |
| `Salt.MR.subWindowSup_sq_le_class_count` | Salt/MR/M4ClassPrice.lean:323 | characters |
| `Salt.MR.m4_blockMeanSqSupQ_of_classPrice` | Salt/MR/M4ClassPrice.lean:373 | sieves, characters |
| `Salt.MR.three_mul_div_le` | Salt/MR/M4ClassPrice.lean:436 | characters |
| `Salt.MR.dilBlock_fit_slack` | Salt/MR/M4ClassPrice.lean:458 | characters |
| `Salt.MR.dilBlock_fitted` | Salt/MR/M4ClassPrice.lean:469 | characters |
| `Salt.MR.sum_Ioc_drop_top` | Salt/MR/M4ClassPrice.lean:477 | characters |
| `Salt.MR.sum_Ioc_absWindowSum_sq_div_le_dropped` | Salt/MR/M4ClassPrice.lean:500 | characters |
| `Salt.MR.slack4_fitted` | Salt/MR/M4ClassPrice.lean:555 | characters |
| `Salt.MR.sum_Ioc_drop_top_four` | Salt/MR/M4ClassPrice.lean:563 | characters |
| `Salt.MR.sum_Ioc_absWindowSum_sq_div_le_dropped_four` | Salt/MR/M4ClassPrice.lean:587 | characters |
| `Salt.MR.sum_Ioc_absWindowSum_sq_div_le_slack4` | Salt/MR/M4ClassPrice.lean:641 | characters |
| `Salt.MR.m4_gradeGate_direct` | Salt/MR/M4ClassPrice.lean:704 | characters |
| `Salt.MR.m4_gradeGate_direct_of_sq` | Salt/MR/M4ClassPrice.lean:722 | characters |
| `Salt.MR.m4_gradeGate_direct_split` | Salt/MR/M4ClassPrice.lean:760 | characters |
| `Salt.MR.m4_decay_exponent_neg` | Salt/MR/M4ClassPrice.lean:774 | characters |
| `Salt.MR.m4_decay_summand_eq` | Salt/MR/M4ClassPrice.lean:809 | characters |
| `Salt.MR.m4DecayGrade_factor_le_one` | Salt/MR/M4ClassPrice.lean:846 | characters |
| `Salt.MR.doorCoeffPhase_zero` | Salt/MR/M4ClassPrice.lean:875 | characters |
| `Salt.MR.m4_rowMeanSqUnphased_eq_phased_zero` | Salt/MR/M4ClassPrice.lean:883 | sieves, characters |
| `Salt.MR.sum_harmonic_cauchy_schwarz` | Salt/MR/M4Close.lean:121 | characters |
| `Salt.MR.integral_logMeasure_le_sqrt` | Salt/MR/M4Close.lean:147 | characters |
| `Salt.MR.integral_logMeasure_le_sqrt_of_sq` | Salt/MR/M4Close.lean:191 | characters |
| `Salt.MR.sqrt_m4Saving` | Salt/MR/M4Close.lean:234 | characters |
| `Salt.MR.m4_quality_summand_le` | Salt/MR/M4Close.lean:242 | characters |
| `Salt.MR.m4_rawMS_le` | Salt/MR/M4Close.lean:249 | characters |
| `Salt.MR.m4_rawMS_le_saving` | Salt/MR/M4Close.lean:264 | characters |
| `Salt.MR.exp_one_le_log_regime_Hlo` | Salt/MR/M4Close.lean:285 | characters |
| `Salt.MR.exp_one_le_log_of_regime_le` | Salt/MR/M4Close.lean:300 | characters |
| `Salt.MR.sqrt_m4Saving_le_delivered` | Salt/MR/M4Close.lean:313 | characters |
| `Salt.MR.m4_bandTransport` | Salt/MR/M4Close.lean:359 | characters |
| `Salt.MR.m4_sievedDoorSq_trivial` | Salt/MR/M4Close.lean:384 | sieves, characters |
| `Salt.MR.m4_gradeGate_of_pricing` | Salt/MR/M4Close.lean:434 | characters |
| `Salt.MR.sum_liou_residue_eq` | Salt/MR/M4Close.lean:591 | characters |
| `Salt.MR.sum_liou_modEq_residue_eq` | Salt/MR/M4Close.lean:600 | characters |
| `Salt.MR.norm_sum_liou_modEq_residue_le` | Salt/MR/M4Close.lean:613 | characters |
| `Salt.MR.card_dirichletCharacter_eq_totient` | Salt/MR/M4Close.lean:627 | characters |
| `Salt.MR.inv_totient_sum_le` | Salt/MR/M4Close.lean:641 | characters |
| `Salt.MR.m4_gradeGate_of_pricing_split` | Salt/MR/M4Close.lean:686 | characters |
| `Salt.MR.doorLadder_pow_lower` | Salt/MR/M4Collapse.lean:317 | characters |
| `Salt.MR.norm_sum_doorSievedWindow_le` | Salt/MR/M4CoprimeSupply.lean:105 | sieves, characters |
| `Salt.MR.doorChiSup_le_len` | Salt/MR/M4CoprimeSupply.lean:123 | characters |
| `Salt.MR.m4_coprimeChiBlockMeanSqN_trivial` | Salt/MR/M4CoprimeSupply.lean:152 | characters |
| `Salt.MR.m4_chiFreeShiftBlock_trivial` | Salt/MR/M4CoprimeSupply.lean:262 | characters |
| `Salt.MR.logMeasure_singleton_toReal` | Salt/MR/M4Door.lean:145 | characters |
| `Salt.MR.door_norm_pos` | Salt/MR/M4Door.lean:153 | characters |
| `Salt.MR.door_norm_ge` | Salt/MR/M4Door.lean:161 | characters |
| `Salt.MR.door_norm_one_le` | Salt/MR/M4Door.lean:167 | characters |
| `Salt.MR.integral_logMeasure_le_div` | Salt/MR/M4Door.lean:178 | characters |
| `Salt.MR.sum_div_Ioc_le` | Salt/MR/M4Door.lean:188 | characters |
| `Salt.MR.le_sum_div_Ioc` | Salt/MR/M4Door.lean:196 | characters |
| `Salt.MR.card_shortWindow_ge` | Salt/MR/M4Door.lean:211 | characters |
| `Salt.MR.card_shortWindow_abs_sub_le_one` | Salt/MR/M4Door.lean:237 | characters |
| `Salt.MR.card_shortWindow_band` | Salt/MR/M4Door.lean:255 | characters |
| `Salt.MR.doorLadder_fit` | Salt/MR/M4Door.lean:295 | characters |
| `Salt.MR.doorLadder_floor` | Salt/MR/M4Door.lean:300 | characters |
| `Salt.MR.doorLadder_step_le` | Salt/MR/M4Door.lean:306 | characters |
| `Salt.MR.doorLadder_block_subset` | Salt/MR/M4Door.lean:314 | characters |
| `Salt.MR.doorLadder_upper` | Salt/MR/M4Door.lean:324 | characters |
| `Salt.MR.doorLadder_lower` | Salt/MR/M4Door.lean:352 | characters |
| `Salt.MR.doorLadder_inv_le` | Salt/MR/M4Door.lean:371 | characters |
| `Salt.MR.sum_range_two_pow_shift_le` | Salt/MR/M4Door.lean:399 | characters |
| `Salt.MR.natDiv_gt` | Salt/MR/M4Door.lean:412 | characters |
| `Salt.MR.doorLadder_reaches` | Salt/MR/M4Door.lean:425 | characters |
| `Salt.MR.doorCount_le` | Salt/MR/M4Door.lean:454 | characters |
| `Salt.MR.two_mul_le_two_pow_doorCount` | Salt/MR/M4Door.lean:467 | characters |
| `Salt.MR.sum_Ioc_ladder_split` | Salt/MR/M4Door.lean:494 | characters |
| `Salt.MR.door_cover_sum_le` | Salt/MR/M4Door.lean:534 | characters |
| `Salt.MR.door_count_le_three_mul_norm` | Salt/MR/M4Door.lean:648 | characters |
| `Salt.MR.door_mass_normalised_le` | Salt/MR/M4Door.lean:669 | characters |
| `Salt.MR.doorCount_gates` | Salt/MR/M4Door.lean:802 | characters |
| `Salt.MR.doorRow_trivial_grade` | Salt/MR/M4DoorClose.lean:301 | characters |
| `Salt.MR.m4_doorL2_socket_ceiling_at_sock` | Salt/MR/M4DoorL2.lean:252 | characters |
| `Salt.MR.m4_doorL2_binder_floor_split` | Salt/MR/M4DoorL2.lean:270 | characters |
| `Salt.MR.m4_doorL2_binder_floor_unified` | Salt/MR/M4DoorL2.lean:291 | characters |
| `Salt.MR.m4_doorL2_grade_split` | Salt/MR/M4DoorL2.lean:327 | characters |
| `Salt.MR.m4_gradeGateL2_of_binder_split` | Salt/MR/M4DoorL2.lean:387 | characters |
| `Salt.MR.sum_bigXi_insert_spelling_eq` | Salt/MR/M4DoorL2.lean:545 | characters |
| `Salt.MR.winCutH_supp0` | Salt/MR/M4DoorRow.lean:167 | characters |
| `Salt.MR.winCut_endpoint` | Salt/MR/M4DoorRow.lean:186 | characters |
| `Salt.MR.shortSum_winCutH_seamS0` | Salt/MR/M4DoorRow.lean:208 | characters |
| `Salt.MR.shortSum_winCut_seamS0` | Salt/MR/M4DoorRow.lean:217 | characters |
| `Salt.MR.doorRow_ha1` | Salt/MR/M4DoorRow.lean:235 | characters |
| `Salt.MR.doorRow_hsupp0` | Salt/MR/M4DoorRow.lean:240 | characters |
| `Salt.MR.doorRow_hasupp` | Salt/MR/M4DoorRow.lean:246 | characters |
| `Salt.MR.doorCofactor0_door_eq` | Salt/MR/M4DoorRow.lean:260 | characters |
| `Salt.MR.doorChiCoeff_seamCoefW_at_door` | Salt/MR/M4DoorRow.lean:283 | characters |
| `Salt.MR.m4_door_tail_supply` | Salt/MR/M4DoorRow.lean:300 | characters |
| `Salt.MR.m4_door_tail_supply_end` | Salt/MR/M4DoorRow.lean:332 | characters |
| `Salt.MR.band_window_ratio_lock` | Salt/MR/M4DoorRow.lean:379 | characters |
| `Salt.MR.door_block_one_wide` | Salt/MR/M4DoorRow.lean:407 | characters |
| `Salt.MR.door_length_gate` | Salt/MR/M4DoorRow.lean:432 | characters |
| `Salt.MR.door_length_gate_fails_of_small` | Salt/MR/M4DoorRow.lean:449 | characters |
| `Salt.MR.door_length_gate_iff` | Salt/MR/M4DoorRow.lean:467 | characters |
| `Salt.MR.door_smallGrade_fits` | Salt/MR/M4DoorRow.lean:494 | characters |
| `Salt.MR.two_mul_dyadScale_succ` | Salt/MR/M4Dyadic.lean:108 | characters |
| `Salt.MR.dyadScale_le_self` | Salt/MR/M4Dyadic.lean:123 | characters |
| `Salt.MR.dyadIdx_le` | Salt/MR/M4Dyadic.lean:147 | characters |
| `Salt.MR.dyadCount_le` | Salt/MR/M4Dyadic.lean:156 | characters |
| `Salt.MR.dyadCount_logPow_le` | Salt/MR/M4Dyadic.lean:165 | characters |
| `Salt.MR.dyadCount_logPow_le_numeral` | Salt/MR/M4Dyadic.lean:178 | characters |
| `Salt.MR.pow_ten_le_two_pow_dyadIdx` | Salt/MR/M4Dyadic.lean:191 | characters |
| `Salt.MR.dyadScale_dyadIdx_le` | Salt/MR/M4Dyadic.lean:210 | characters |
| `Salt.MR.dyadPart_window` | Salt/MR/M4Dyadic.lean:237 | characters |
| `Salt.MR.sum_dyadPart` | Salt/MR/M4Dyadic.lean:247 | characters |
| `Salt.MR.sum_dyadCover` | Salt/MR/M4Dyadic.lean:288 | characters |
| `Salt.MR.exists_dyadPart_mem` | Salt/MR/M4Dyadic.lean:305 | characters |
| `Salt.MR.exists_dyadScale_cover` | Salt/MR/M4Dyadic.lean:322 | characters |
| `Salt.MR.dyadScale_floor_of_cover` | Salt/MR/M4Dyadic.lean:335 | characters |
| `Salt.MR.sqrt_le_of_depth` | Salt/MR/M4Dyadic.lean:352 | characters |
| `Salt.MR.two_mul_pow_ten_le_sqrt` | Salt/MR/M4Dyadic.lean:366 | characters |
| `Salt.MR.sqrt_le_dyadScale` | Salt/MR/M4Dyadic.lean:403 | characters |
| `Salt.MR.exp_one_le_of_sqrt_le` | Salt/MR/M4Dyadic.lean:414 | characters |
| `Salt.MR.three_le_of_sqrt_le` | Salt/MR/M4Dyadic.lean:424 | characters |
| `Salt.MR.log_sub_log_le_log_of_floor` | Salt/MR/M4Dyadic.lean:438 | characters |
| `Salt.MR.loglog_sub_log_two_le` | Salt/MR/M4Dyadic.lean:447 | characters |
| `Salt.MR.h_ceiling_transfer` | Salt/MR/M4Dyadic.lean:461 | characters |
| `Salt.MR.five_le_loglog_transfer` | Salt/MR/M4Dyadic.lean:475 | characters |
| `Salt.MR.image_div_window_dilate` | Salt/MR/M4Dyadic.lean:500 | characters |
| `Salt.MR.sum_window_dilate` | Salt/MR/M4Dyadic.lean:532 | characters |
| `Salt.MR.meanSq_scale_invariant` | Salt/MR/M4Dyadic.lean:545 | characters |
| `Salt.MR.meanSq_shortSum_scale` | Salt/MR/M4Dyadic.lean:557 | characters |
| `Salt.MR.sum_div_le_of_window` | Salt/MR/M4Dyadic.lean:574 | characters |
| `Salt.MR.le_sum_div_of_window` | Salt/MR/M4Dyadic.lean:585 | characters |
| `Salt.MR.sum_div_dyadPart_le` | Salt/MR/M4Dyadic.lean:596 | characters |
| `Salt.MR.le_sum_div_dyadPart` | Salt/MR/M4Dyadic.lean:606 | characters |
| `Salt.MR.norm_absWindowSum_le_thresh` | Salt/MR/M4Dyadic.lean:628 | characters |
| `Salt.MR.norm_absWindowSum_le_trivThresh` | Salt/MR/M4Dyadic.lean:633 | characters |
| `Salt.MR.integral_logMeasure_le_of_le` | Salt/MR/M4Dyadic.lean:641 | characters |
| `Salt.MR.integral_logMeasure_absWindowSum_le_thresh` | Salt/MR/M4Dyadic.lean:665 | characters |
| `Salt.MR.card_shortWindow_le` | Salt/MR/M4Dyadic.lean:672 | characters |
| `Salt.MR.norm_shortSum_le` | Salt/MR/M4Dyadic.lean:701 | characters |
| `Salt.MR.sum_range_le_mul` | Salt/MR/M4Dyadic.lean:717 | characters |
| `Salt.MR.sum_range_le_mul_sup'` | Salt/MR/M4Dyadic.lean:723 | characters |
| `Salt.MR.dyadCover_total_le` | Salt/MR/M4Dyadic.lean:730 | characters |
| `Salt.MR.dyadCover_total_le_sup'` | Salt/MR/M4Dyadic.lean:748 | characters |
| `Salt.MR.dyadCover_total_le_logPow` | Salt/MR/M4Dyadic.lean:759 | characters |
| `Salt.MR.endMass_nonneg` | Salt/MR/M4ErrRewire.lean:171 | characters |
| `Salt.MR.err_grade_fit` | Salt/MR/M4ErrRewire.lean:245 | characters |
| `Salt.MR.doorDatum_factorizes` | Salt/MR/M4ErrRewire.lean:314 | characters |
| `Salt.MR.doorDatum_seamCoefW` | Salt/MR/M4ErrRewire.lean:348 | characters |
| `Salt.MR.doorDatum_inhabits_err_binders` | Salt/MR/M4ErrRewire.lean:362 | characters |
| `Salt.MR.absWindowSum_lamCoeff_eq` | Salt/MR/M4Exit.lean:102 | characters |
| `Salt.MR.integral_absWindowSum_lamCoeff_eq` | Salt/MR/M4Exit.lean:108 | characters |
| `Salt.MR.two_le_regime_Hlo` | Salt/MR/M4Exit.lean:117 | characters |
| `Salt.MR.log_pos_of_regime_le` | Salt/MR/M4Exit.lean:122 | characters |
| `Salt.MR.doorGrade_regime_pos` | Salt/MR/M4Exit.lean:130 | characters |
| `Salt.MR.doorGrade_le_regime_floor` | Salt/MR/M4Exit.lean:136 | characters |
| `Salt.MR.doorGrade_regime_pin` | Salt/MR/M4Exit.lean:143 | characters |
| `Salt.MR.mrtGate_of_sq_le` | Salt/MR/M4Exit.lean:173 | characters |
| `Salt.MR.H0scale_pos` | Salt/MR/M4Exit.lean:197 | characters |
| `Salt.MR.sq_le_log_of_H0scale_le` | Salt/MR/M4Exit.lean:202 | characters |
| `Salt.MR.mrtGate_transfer` | Salt/MR/M4Exit.lean:212 | characters |
| `Salt.MR.mrtDeliveredGrade_le_pin` | Salt/MR/M4Exit.lean:242 | characters |
| `Salt.MR.m4_exit_socket` | Salt/MR/M4Exit.lean:337 | characters |
| `Salt.MR.m4_exit_socket_False` | Salt/MR/M4Exit.lean:368 | characters |
| `Salt.MR.m4_exit_socket_split` | Salt/MR/M4Exit.lean:487 | characters |
| `Salt.MR.sum_normSq_chiGaussSum` | Salt/MR/M4Gauss.lean:120 | characters |
| `Salt.MR.coprime_window_expansion` | Salt/MR/M4Gauss.lean:214 | sieves, characters |
| `Salt.MR.norm_sq_inv_totient_gauss_le` | Salt/MR/M4Gauss.lean:269 | characters |
| `Salt.MR.norm_sq_coprime_window_le` | Salt/MR/M4Gauss.lean:302 | sieves, characters |
| `Salt.MR.sum_fibre_eq_coprime` | Salt/MR/M4Gauss.lean:322 | characters |
| `Salt.MR.ratPhase_dilate` | Salt/MR/M4Gauss.lean:368 | characters |
| `Salt.MR.class_rat_dilate` | Salt/MR/M4Gauss.lean:398 | sieves, characters |
| `Salt.MR.stratum_sq_le_chiSummed` | Salt/MR/M4Gauss.lean:448 | sieves, characters |
| `Salt.MR.capL_ledger` | Salt/MR/M4Gauss.lean:538 | characters |
| `Salt.MR.subWindowSup_sq_le_strata` | Salt/MR/M4Gauss.lean:577 | sieves, characters |
| `Salt.MR.sum_inv_divisors_le` | Salt/MR/M4Gauss.lean:652 | characters |
| `Salt.MR.capL_le_dilated_base` | Salt/MR/M4Gauss.lean:691 | characters |
| `Salt.MR.le_mul_div_add` | Salt/MR/M4Gauss.lean:708 | characters |
| `Salt.MR.m4_capstone_window_forces_cf_zero` | Salt/MR/M4Join.lean:173 | characters |
| `Salt.MR.m4_capstone_row_supp_sq` | Salt/MR/M4Join.lean:194 | characters |
| `Salt.MR.m4_blockMeanSqSup_trivial` | Salt/MR/M4Join.lean:274 | characters |
| `Salt.MR.sum_Ioc_le_two_mul_of_harmonic` | Salt/MR/M4Join.lean:316 | characters |
| `Salt.MR.m4_blockGrade_nonneg` | Salt/MR/M4Join.lean:388 | characters |
| `Salt.MR.m4_wave_gradeGate` | Salt/MR/M4Join.lean:401 | characters |
| `Salt.MR.m4_wave_gradeGate_split` | Salt/MR/M4Join.lean:539 | characters |
| `Salt.MR.m4_class_dilate_exit_L_gk` | Salt/MR/M4LadderLinear.lean:2615 | characters |
| `Salt.MR.m4_class_price_L` | Salt/MR/M4LadderLinear.lean:2679 | sieves, characters |
| `Salt.MR.sum_sievedWindow_add` | Salt/MR/M4Maximal.lean:167 | sieves, characters |
| `Salt.MR.dyadic_prefix_shift` | Salt/MR/M4Maximal.lean:189 | characters |
| `Salt.MR.norm_sum_sievedWindow_le_dyadic` | Salt/MR/M4Maximal.lean:207 | sieves, characters |
| `Salt.MR.geom_weight_sum` | Salt/MR/M4Maximal.lean:299 | characters |
| `Salt.MR.geom_weight_sum_pos` | Salt/MR/M4Maximal.lean:305 | characters |
| `Salt.MR.geom_weight_sum_le` | Salt/MR/M4Maximal.lean:309 | characters |
| `Salt.MR.inv_geom_weight` | Salt/MR/M4Maximal.lean:315 | characters |
| `Salt.MR.geom_term_eq` | Salt/MR/M4Maximal.lean:321 | characters |
| `Salt.MR.norm_sum_sievedWindow_sq_le_dyadic` | Salt/MR/M4Maximal.lean:337 | sieves, characters |
| `Salt.MR.doorChiSup_sq_le_dyadic` | Salt/MR/M4Maximal.lean:396 | sieves, characters |
| `Salt.MR.sum_Ioc_shift` | Salt/MR/M4Maximal.lean:421 | characters |
| `Salt.MR.dyadic_count_weight_term_le` | Salt/MR/M4Maximal.lean:429 | characters |
| `Salt.MR.dyadic_count_weight_term_nonneg` | Salt/MR/M4Maximal.lean:456 | characters |
| `Salt.MR.dyadic_count_weight_le` | Salt/MR/M4Maximal.lean:463 | characters |
| `Salt.MR.dyadic_count_weight_small_le` | Salt/MR/M4Maximal.lean:509 | characters |
| `Salt.MR.dyadic_count_weight_geom_le` | Salt/MR/M4Maximal.lean:545 | characters |
| `Salt.MR.dyadic_count_weight_geom_small_le` | Salt/MR/M4Maximal.lean:615 | characters |
| `Salt.MR.m4Cmax_nonneg` | Salt/MR/M4Maximal.lean:676 | characters |
| `Salt.MR.m4BclGraded_nonneg` | Salt/MR/M4Maximal.lean:703 | characters |
| `Salt.MR.m4SmallGradeFits_of_threshold` | Salt/MR/M4Maximal.lean:733 | characters |
| `Salt.MR.m4_chiShiftBlock_trivial` | Salt/MR/M4Maximal.lean:789 | characters |
| `Salt.MR.dpolyA_congr` | Salt/MR/M4MeanSq.lean:226 | characters |
| `Salt.MR.mem_seamS0` | Salt/MR/M4MeanSq.lean:231 | characters |
| `Salt.MR.m4BandDatum_supp` | Salt/MR/M4MeanSq.lean:246 | characters |
| `Salt.MR.m4BandDatum_eq` | Salt/MR/M4MeanSq.lean:249 | characters |
| `Salt.MR.dpolyA_seamS0_bandDatum` | Salt/MR/M4MeanSq.lean:256 | characters |
| `Salt.MR.exp_exp_one_gt_three` | Salt/MR/M4MeanSq.lean:270 | characters |
| `Salt.MR.exp_one_le_exp_exp_one` | Salt/MR/M4MeanSq.lean:275 | characters |
| `Salt.MR.coef_widen_of_window` | Salt/MR/M4MeanSq.lean:311 | characters |
| `Salt.MR.m4_rbar_nonneg` | Salt/MR/M4MeanSq.lean:400 | characters |
| `Salt.MR.m4_t0band_at_datum` | Salt/MR/M4MeanSq.lean:724 | characters |
| `Salt.MR.m4_t0band_of_live` | Salt/MR/M4MeanSq.lean:760 | characters |
| `Salt.MR.m4_trivial_branch` | Salt/MR/M4MeanSq.lean:783 | characters |
| `Salt.MR.card_fibre_div_le` | Salt/MR/M4NonCoprime.lean:131 | characters |
| `Salt.MR.sum_Ioc_comp_div_le` | Salt/MR/M4NonCoprime.lean:152 | characters |
| `Salt.MR.two_mul_div_le` | Salt/MR/M4NonCoprime.lean:181 | characters |
| `Salt.MR.div_mem_reindexed` | Salt/MR/M4NonCoprime.lean:195 | characters |
| `Salt.MR.dilBlock_reindex_fit` | Salt/MR/M4NonCoprime.lean:213 | characters |
| `Salt.MR.d0_ledger` | Salt/MR/M4NonCoprime.lean:229 | characters |
| `Salt.MR.d0_ledger_sharp` | Salt/MR/M4NonCoprime.lean:259 | characters |
| `Salt.MR.classSup_mono_len` | Salt/MR/M4NonCoprime.lean:295 | characters |
| `Salt.MR.classSup_le_dilate` | Salt/MR/M4NonCoprime.lean:304 | sieves, characters |
| `Salt.MR.m4_coprimeBlockMeanSq_trivial` | Salt/MR/M4NonCoprime.lean:350 | characters |
| `Salt.MR.m4_coprimeBlockMeanSqN_trivial` | Salt/MR/M4NonCoprime.lean:526 | characters |
| `Salt.MR.one_le_arcDen_of_regime` | Salt/MR/M4NonCoprime.lean:533 | characters |
| `Salt.MR.mem_ramP2domMR_window` | Salt/MR/M4P2MR.lean:37 | characters |
| `Salt.MR.ramP2domMR_fiber_card_le_omega` | Salt/MR/M4P2MR.lean:56 | characters |
| `Salt.MR.ramP2coeffMR_norm_div_le` | Salt/MR/M4P2MR.lean:88 | characters |
| `Salt.MR.ramP2coeffMR_sum_div_le` | Salt/MR/M4P2MR.lean:250 | characters |
| `Salt.MR.ramP2massMR_direct` | Salt/MR/M4P2MR.lean:301 | characters |
| `Salt.MR.mem_ramP2domEndMR_window` | Salt/MR/M4P2MR.lean:359 | characters |
| `Salt.MR.mem_ramP2domEndMR_prime` | Salt/MR/M4P2MR.lean:369 | characters |
| `Salt.MR.ramP2domEndMR_fiber_card_le_omega` | Salt/MR/M4P2MR.lean:378 | characters |
| `Salt.MR.ramP2coeffEndMR_norm_div_le` | Salt/MR/M4P2MR.lean:396 | characters |
| `Salt.MR.ramP2domEndMR_sum_le` | Salt/MR/M4P2MR.lean:472 | characters |
| `Salt.MR.ramP2coeffEndMR_sum_div_le` | Salt/MR/M4P2MR.lean:531 | characters |
| `Salt.MR.ramP2massEndMR_direct` | Salt/MR/M4P2MR.lean:581 | characters |
| `Salt.MR.errC_normSq_le` | Salt/MR/M4ParsevalStone.lean:73 | characters |
| `Salt.MR.offWindowSum_eq_dft` | Salt/MR/M4ParsevalStone.lean:124 | characters, exponential sums |
| `Salt.MR.norm_absWindowSum_eq_dft` | Salt/MR/M4ParsevalStone.lean:156 | characters |
| `Salt.MR.sum_zmod_window` | Salt/MR/M4ParsevalStone.lean:165 | characters |
| `Salt.MR.parseval_insert_error` | Salt/MR/M4ParsevalStone.lean:188 | characters |
| `Salt.MR.parseval_stone_budget` | Salt/MR/M4ParsevalStone.lean:232 | characters |
| `Salt.MR.sum_integral_logMeasure_le` | Salt/MR/M4ParsevalStone.lean:257 | characters |
| `Salt.MR.blockOmega_prime_in` | Salt/MR/M4Puncture.lean:87 | characters |
| `Salt.MR.blockOmega_prime_out` | Salt/MR/M4Puncture.lean:98 | characters |
| `Salt.MR.memS_mul_prime_punct` | Salt/MR/M4Puncture.lean:110 | characters |
| `Salt.MR.indicator_mul_punct` | Salt/MR/M4Puncture.lean:134 | characters |
| `Salt.MR.calQK_one_lt_calP_two` | Salt/MR/M4Puncture.lean:158 | characters |
| `Salt.MR.door_block_separation` | Salt/MR/M4Puncture.lean:168 | characters |
| `Salt.MR.door_block_sep_at` | Salt/MR/M4Puncture.lean:174 | characters |
| `Salt.MR.memSCoeff_seamCoefW_punct_gen` | Salt/MR/M4Puncture.lean:194 | characters |
| `Salt.MR.memSCoeff_seamCoefW_punct_H` | Salt/MR/M4Puncture.lean:229 | characters |
| `Salt.MR.doorChiCoeff_seamCoefW_punct_H` | Salt/MR/M4Puncture.lean:249 | characters |
| `Salt.MR.memSCoeff_seamCoefWS_punct_gen` | Salt/MR/M4Puncture.lean:270 | characters |
| `Salt.MR.memSCoeff_seamCoefWS_punct_H` | Salt/MR/M4Puncture.lean:294 | characters |
| `Salt.MR.doorChiCoeff_seamCoefWS_punct_H` | Salt/MR/M4Puncture.lean:306 | characters |
| `Salt.MR.norm_doorPunctCoeff_le_one` | Salt/MR/M4Puncture.lean:319 | characters |
| `Salt.MR.one_le_m4W` | Salt/MR/M4Quality.lean:111 | characters |
| `Salt.MR.m4Demand_nonneg` | Salt/MR/M4Quality.lean:115 | characters |
| `Salt.MR.m4_exit_decay_of_quality` | Salt/MR/M4Quality.lean:134 | characters |
| `Salt.MR.cfbM0_antitone_K` | Salt/MR/M4Quality.lean:156 | characters |
| `Salt.MR.m4_quality_of_band` | Salt/MR/M4Quality.lean:170 | characters |
| `Salt.MR.m4_log_le_div_eighty` | Salt/MR/M4Quality.lean:181 | characters |
| `Salt.MR.m4_quality_of_band_hhi` | Salt/MR/M4Quality.lean:207 | characters |
| `Salt.MR.m4_quality_band_coeff_one` | Salt/MR/M4Quality.lean:232 | characters |
| `Salt.MR.m4_quality_band_coeff_one_liouChi` | Salt/MR/M4Quality.lean:244 | characters |
| `Salt.MR.m4_quality_band_door` | Salt/MR/M4Quality.lean:255 | characters |
| `Salt.MR.m4W_mono` | Salt/MR/M4Quality.lean:275 | characters |
| `Salt.MR.m4_modulus_le` | Salt/MR/M4Quality.lean:284 | characters |
| `Salt.MR.m4_modulus_nat_le` | Salt/MR/M4Quality.lean:291 | characters |
| `Salt.MR.m4Wnat_mono` | Salt/MR/M4Quality.lean:299 | characters |
| `Salt.MR.m4_quality_band_window` | Salt/MR/M4Quality.lean:307 | characters |
| `Salt.MR.cfbK_nonneg` | Salt/MR/M4Quality.lean:332 | characters |
| `Salt.MR.cfbK_spec` | Salt/MR/M4Quality.lean:337 | characters |
| `Salt.MR.m4VKdebit_spec` | Salt/MR/M4Quality.lean:350 | characters |
| `Salt.MR.cfbK_le_m4QualityB` | Salt/MR/M4Quality.lean:360 | characters |
| `Salt.MR.siegelBandB_le_m4QualityB` | Salt/MR/M4Quality.lean:362 | characters |
| `Salt.MR.cffK_le_m4QualityB` | Salt/MR/M4Quality.lean:365 | characters |
| `Salt.MR.m4VKdebit_le_m4QualityB` | Salt/MR/M4Quality.lean:368 | characters |
| `Salt.MR.m4QualityB_nonneg` | Salt/MR/M4Quality.lean:371 | characters |
| `Salt.MR.m4JointThr_anchor` | Salt/MR/M4Quality.lean:403 | characters |
| `Salt.MR.m4JointThr_qual` | Salt/MR/M4Quality.lean:406 | characters |
| `Salt.MR.m4JointThr_band` | Salt/MR/M4Quality.lean:410 | characters |
| `Salt.MR.m4JointThr_cff` | Salt/MR/M4Quality.lean:414 | characters |
| `Salt.MR.m4_quality_of_joint` | Salt/MR/M4Quality.lean:423 | characters |
| `Salt.MR.m4_band_of_joint` | Salt/MR/M4Quality.lean:440 | characters |
| `Salt.MR.m4_capfree_of_joint` | Salt/MR/M4Quality.lean:457 | characters |
| `Salt.MR.liouvilleC_mul` | Salt/MR/M4Residue.lean:103 | characters |
| `Salt.MR.liouvilleC_prime` | Salt/MR/M4Residue.lean:109 | characters |
| `Salt.MR.liouvilleC_norm` | Salt/MR/M4Residue.lean:115 | characters |
| `Salt.MR.liouvilleC_norm_le_one` | Salt/MR/M4Residue.lean:121 | characters |
| `Salt.MR.primeFactors_lt_of_lt` | Salt/MR/M4Residue.lean:137 | characters |
| `Salt.MR.blockPrimeDivs_eq_empty_of_small` | Salt/MR/M4Residue.lean:145 | characters |
| `Salt.MR.blockPrimeDivs_dilate` | Salt/MR/M4Residue.lean:157 | characters |
| `Salt.MR.blockOmega_dilate` | Salt/MR/M4Residue.lean:165 | characters |
| `Salt.MR.blockOmega_dilate_of_lt` | Salt/MR/M4Residue.lean:172 | characters |
| `Salt.MR.memS_dilate` | Salt/MR/M4Residue.lean:187 | characters |
| `Salt.MR.memS_dilate_of_lt` | Salt/MR/M4Residue.lean:197 | characters |
| `Salt.MR.memS_dilate_of_lt_bot` | Salt/MR/M4Residue.lean:204 | characters |
| `Salt.MR.indicator_mul_dilate` | Salt/MR/M4Residue.lean:212 | characters |
| `Salt.MR.indicator_mul_dilate_liouville` | Salt/MR/M4Residue.lean:222 | characters |
| `Salt.MR.sum_memS_dilate` | Salt/MR/M4Residue.lean:231 | characters |
| `Salt.MR.gcd_dvd_of_modEq` | Salt/MR/M4Residue.lean:253 | characters |
| `Salt.MR.coprime_reduced_of_gcd` | Salt/MR/M4Residue.lean:263 | characters |
| `Salt.MR.modEq_dilate_iff` | Salt/MR/M4Residue.lean:275 | characters |
| `Salt.MR.sum_reindex_dilate` | Salt/MR/M4Residue.lean:297 | characters |
| `Salt.MR.residue_split_dilate` | Salt/MR/M4Residue.lean:320 | characters |
| `Salt.MR.residue_split_dilate_liouville` | Salt/MR/M4Residue.lean:342 | characters |
| `Salt.MR.calP_door_one_eq` | Salt/MR/M4Residue.lean:359 | characters |
| `Salt.MR.two_pow_le_calP_door_one` | Salt/MR/M4Residue.lean:366 | characters |
| `Salt.MR.lt_calP_door_one` | Salt/MR/M4Residue.lean:380 | characters |
| `Salt.MR.d_lt_calP_door_one` | Salt/MR/M4Residue.lean:386 | characters |
| `Salt.MR.logH_pow_twelve_lt` | Salt/MR/M4Residue.lean:397 | characters |
| `Salt.MR.door_dilation_gate` | Salt/MR/M4Residue.lean:411 | characters |
| `Salt.MR.door_dilation_gate'` | Salt/MR/M4Residue.lean:427 | characters |
| `Salt.MR.door_dilation_gate_calP` | Salt/MR/M4Residue.lean:442 | characters |
| `Salt.MR.calP_door_mono` | Salt/MR/M4Residue.lean:452 | characters |
| `Salt.MR.memS_dilate_door` | Salt/MR/M4Residue.lean:465 | characters |
| `Salt.MR.residue_split_dilate_door` | Salt/MR/M4Residue.lean:475 | characters |
| `Salt.MR.m4_hT0band_at_door_L` | Salt/MR/M4RowLinear.lean:5068 | characters |
| `Salt.MR.m4_hT0band_at_door_L_gk` | Salt/MR/M4RowLinear.lean:5241 | characters |
| `Salt.MR.lemma12RowsMR_pricedK` | Salt/MR/M4RowMR.lean:172 | characters |
| `Salt.MR.lemma12RowsMR_priced_ratioK` | Salt/MR/M4RowMR.lean:234 | characters |
| `Salt.MR.lemma12RowsMR_pricedK_end` | Salt/MR/M4RowMR.lean:436 | characters |
| `Salt.MR.lemma12RowsMR_priced_ratioK_end` | Salt/MR/M4RowMR.lean:520 | characters |
| `Salt.MR.sum_lemma12RowsMR_pricedK_end` | Salt/MR/M4RowMR.lean:574 | characters |
| `Salt.MR.sum_lemma12RowsMR_priced_calibratedK2_end` | Salt/MR/M4RowMR.lean:616 | characters |
| `Salt.MR.sum_lemma12RowsMR_pricedK` | Salt/MR/M4RowMR.lean:673 | characters |
| `Salt.MR.sum_lemma12RowsMR_priced_calibratedK2` | Salt/MR/M4RowMR.lean:719 | characters |
| `Salt.MR.m4_tail_gate_at_pins` | Salt/MR/M4RowSupply.lean:72 | characters |
| `Salt.MR.m4_tail_mass_at_band` | Salt/MR/M4RowSupply.lean:101 | characters |
| `Salt.MR.m4_tail_mass_nonneg` | Salt/MR/M4RowSupply.lean:115 | characters |
| `Salt.MR.m4_tail_grade_at_pins` | Salt/MR/M4RowSupply.lean:137 | characters |
| `Salt.MR.m4_tail_grade_rounded` | Salt/MR/M4RowSupply.lean:185 | characters |
| `Salt.MR.m4_ep2_budget_at_band` | Salt/MR/M4RowSupply.lean:248 | characters |
| `Salt.MR.m4_ep2_budget_at_band_end` | Salt/MR/M4RowSupply.lean:323 | characters |
| `Salt.MR.m4_tail_supply_at_band` | Salt/MR/M4RowSupply.lean:463 | characters |
| `Salt.MR.m4_tail_supply_at_band_end` | Salt/MR/M4RowSupply.lean:499 | characters |
| `Salt.MR.measurableSet_rowPairSetG_fibre` | Salt/MR/M4RowsChi.lean:149 | characters |
| `Salt.MR.rowPairSetG_subset_UsetGChi` | Salt/MR/M4RowsChi.lean:164 | characters |
| `Salt.MR.tL_block_weight_chi` | Salt/MR/M4RowsChi.lean:188 | characters |
| `Salt.MR.usetGChi_block_price` | Salt/MR/M4RowsChi.lean:199 | characters |
| `Salt.MR.usetGChi_row_exit_perChi` | Salt/MR/M4RowsChi.lean:244 | characters |
| `Salt.MR.chiBarCoeff_seam_supp` | Salt/MR/M4RowsChi.lean:345 | characters |
| `Salt.MR.chiBarCoeff_dyadic_supp` | Salt/MR/M4RowsChi.lean:352 | characters |
| `Salt.MR.sum_lemma12Rows_priced_chi` | Salt/MR/M4RowsChi.lean:518 | characters |
| `Salt.MR.m4_rowChi_weighed` | Salt/MR/M4RowsChi.lean:845 | characters |
| `Salt.MR.m4MrowChi_le_a2Mrow` | Salt/MR/M4RowsChi.lean:1102 | characters |
| `Salt.MR.seamCoefWS_levels_of_global` | Salt/MR/M4RowsChiEnd.lean:126 | characters |
| `Salt.MR.sum_lemma12RowsMR_priced_chi_end` | Salt/MR/M4RowsChiEnd.lean:147 | characters |
| `Salt.MR.m4_rowChi_weighed_end` | Salt/MR/M4RowsChiEnd.lean:498 | characters |
| `Salt.MR.m4MrowChiEnd_le_a2Mrow` | Salt/MR/M4RowsChiEnd.lean:652 | characters |
| `Salt.MR.blockfree_row_memS_zero` | Salt/MR/M4RowsChiZero.lean:167 | zeros, characters |
| `Salt.MR.blockLive_winCutH_doorCoeffU` | Salt/MR/M4RowsChiZero.lean:703 | zeros, characters |
| `Salt.MR.cfb_t0band_supply_of_sup` | Salt/MR/M4Seam.lean:119 | characters |
| `Salt.MR.dvd_of_one_le_blockOmega_self` | Salt/MR/M4Seam.lean:179 | characters |
| `Salt.MR.norm_natCast_cpow_it` | Salt/MR/M4Seam.lean:186 | characters |
| `Salt.MR.norm_sum_div_cpow_le_card` | Salt/MR/M4Seam.lean:197 | characters |
| `Salt.MR.card_filter_dvd_Icc` | Salt/MR/M4Seam.lean:211 | characters |
| `Salt.MR.Icc_filter_pexact_image` | Salt/MR/M4Seam.lean:219 | characters |
| `Salt.MR.seamS0_filter_pexact_image` | Salt/MR/M4Seam.lean:240 | characters |
| `Salt.MR.injOn_mul_left` | Salt/MR/M4Seam.lean:265 | characters |
| `Salt.MR.spolyA_dilate_eq` | Salt/MR/M4Seam.lean:280 | characters |
| `Salt.MR.dpolyA_seamS0_dilate` | Salt/MR/M4Seam.lean:337 | characters |
| `Salt.MR.norm_spolyA_dilate_le` | Salt/MR/M4Seam.lean:395 | characters |
| `Salt.MR.m4_row_cf_block_eq_zero` | Salt/MR/M4Seam.lean:461 | characters |
| `Salt.MR.m4_row_supp_sq` | Salt/MR/M4Seam.lean:474 | characters |
| `Salt.MR.m4_hT0band_of_dilated_sup` | Salt/MR/M4Seam.lean:489 | characters |
| `Salt.MR.m4_hT0band_at_row` | Salt/MR/M4Seam.lean:535 | characters |
| `Salt.MR.m4_hT0band_at_row_pins` | Salt/MR/M4Seam.lean:614 | characters |
| `Salt.MR.four_le_arcDen_of_regime` | Salt/MR/M4SecondRoad.lean:154 | characters |
| `Salt.MR.blockLen_drift` | Salt/MR/M4SecondRoad.lean:196 | characters |
| `Salt.MR.blockLen_narrow` | Salt/MR/M4SecondRoad.lean:227 | characters |
| `Salt.MR.blockLen_arc_floor` | Salt/MR/M4SecondRoad.lean:257 | characters |
| `Salt.MR.two_pow_le_four_mul_of_count` | Salt/MR/M4SecondRoad.lean:410 | characters |
| `Salt.MR.doorLadder_ge_x_div_four_omega` | Salt/MR/M4SecondRoad.lean:449 | characters |
| `Salt.MR.truncBudget_pos` | Salt/MR/M4SecondRoad.lean:777 | characters |
| `Salt.MR.truncD_ge` | Salt/MR/M4SecondRoad.lean:793 | characters |
| `Salt.MR.truncD_admissible` | Salt/MR/M4SecondRoad.lean:814 | characters |
| `Salt.MR.stratum_sq_le_chiSummed_at_truncD` | Salt/MR/M4SecondRoad.lean:848 | sieves, characters |
| `Salt.MR.rStrWitness_nonneg` | Salt/MR/M4SecondRoad.lean:872 | characters |
| `Salt.MR.rStrWitness_G1` | Salt/MR/M4SecondRoad.lean:875 | characters |
| `Salt.MR.rSanWitness_nonneg` | Salt/MR/M4SecondRoad.lean:883 | characters |
| `Salt.MR.rSanWitness_envelope` | Salt/MR/M4SecondRoad.lean:886 | characters |
| `Salt.MR.g2_of_j0_floor` | Salt/MR/M4SecondRoad.lean:908 | characters |
| `Salt.MR.memSCoeff_mul` | Salt/MR/M4Sieve.lean:118 | sieves, characters |
| `Salt.MR.norm_memSCoeff_le_one` | Salt/MR/M4Sieve.lean:126 | sieves, characters |
| `Salt.MR.ratioSumK_nonneg` | Salt/MR/M4Sieve.lean:145 | sieves, characters |
| `Salt.MR.card_notMemS_eq_sum` | Salt/MR/M4Sieve.lean:152 | sieves, characters |
| `Salt.MR.sum_memS_split` | Salt/MR/M4Sieve.lean:164 | sieves, characters |
| `Salt.MR.norm_sum_notMemS_le` | Salt/MR/M4Sieve.lean:178 | sieves, characters |
| `Salt.MR.norm_sum_memS_insert` | Salt/MR/M4Sieve.lean:187 | sieves, characters |
| `Salt.MR.norm_absWindowSum_memS_insert` | Salt/MR/M4Sieve.lean:201 | sieves, characters |
| `Salt.MR.norm_shortSum_memS_insert` | Salt/MR/M4Sieve.lean:236 | sieves, characters |
| `Salt.MR.norm_absWindowSum_memS_insert_liouville` | Salt/MR/M4Sieve.lean:247 | sieves, characters |
| `Salt.MR.norm_absWindowSum_memS_insert_liouChi` | Salt/MR/M4Sieve.lean:255 | sieves, characters |
| `Salt.MR.sum_window_double_count` | Salt/MR/M4Sieve.lean:273 | sieves, characters |
| `Salt.MR.sum_notMemSCount_le` | Salt/MR/M4Sieve.lean:318 | sieves, characters |
| `Salt.MR.sum_notMemSCount_weighted_le` | Salt/MR/M4Sieve.lean:342 | sieves, characters |
| `Salt.MR.integral_logMeasure_le_add` | Salt/MR/M4Sieve.lean:372 | sieves, characters |
| `Salt.MR.door_window_not_one_block` | Salt/MR/M4Sieve.lean:393 | sieves, characters |
| `Salt.MR.integral_logMeasure_le_of_weighted` | Salt/MR/M4Sieve.lean:413 | sieves, characters |
| `Salt.MR.card_notMemS_of_subset_Icc` | Salt/MR/M4Sieve.lean:437 | sieves, characters |
| `Salt.MR.notMemS_window_count_le` | Salt/MR/M4Sieve.lean:468 | sieves, characters |
| `Salt.MR.sieve_mass_le_basel` | Salt/MR/M4Sieve.lean:505 | sieves, characters |
| `Salt.MR.sieve_mass_le_quarter` | Salt/MR/M4Sieve.lean:522 | sieves, characters |
| `Salt.MR.sieve_mass_le_eighth` | Salt/MR/M4Sieve.lean:540 | sieves, characters |
| `Salt.MR.m4_sieve_block_mass` | Salt/MR/M4Sieve.lean:588 | sieves, characters |
| `Salt.MR.m4_sieve_insert` | Salt/MR/M4Sieve.lean:641 | sieves, characters |
| `Salt.MR.m4_sieve_insert_liouville` | Salt/MR/M4Sieve.lean:658 | sieves, characters |
| `Salt.MR.m4_sieve_insert_liouChi` | Salt/MR/M4Sieve.lean:670 | sieves, characters |
| `Salt.MR.a2Level1_L_le_a2Level1` | Salt/MR/M4SocketLinear.lean:89 | characters |
| `Salt.MR.doorRowZeroBase_coefWS_witness_L` | Salt/MR/M4SocketLinear.lean:432 | characters |
| `Salt.MR.doorRowZeroBase_coefWS_witness_L_gk` | Salt/MR/M4SocketLinear.lean:701 | characters |
| `Salt.MR.eight_arcDen_le_of_arcFloor` | Salt/MR/M4Spine.lean:165 | characters |
| `Salt.MR.two_arcDen_le_of_arcFloor` | Salt/MR/M4Spine.lean:199 | characters |
| `Salt.MR.mrtDeliveredGrade_le_inv_sq` | Salt/MR/M4Spine.lean:216 | characters |
| `Salt.MR.m4_spine_budget_necessary` | Salt/MR/M4Spine.lean:272 | characters |
| `Salt.MR.m4_budget_forces_C` | Salt/MR/M4Spine.lean:465 | characters |
| `Salt.MR.m4_budget_collision` | Salt/MR/M4Spine.lean:474 | characters |
| `Salt.MR.m4_spine_budget_collision` | Salt/MR/M4Spine.lean:485 | characters |
| `Salt.MR.m4_spine_budget_collision_at_Hlo` | Salt/MR/M4Spine.lean:510 | characters |
| `Salt.MR.m4_spine_budget_collision_perH_at_Hlo` | Salt/MR/M4Spine.lean:533 | characters |
| `Salt.MR.winCutH_sum_finset` | Salt/MR/M4T0Datum.lean:180 | characters |
| `Salt.MR.winCutH_doorChiCoeff_split` | Salt/MR/M4T0Datum.lean:194 | characters |
| `Salt.MR.door_powerset_card` | Salt/MR/M4T0Datum.lean:205 | characters |
| `Salt.MR.spolyA_sum_finset` | Salt/MR/M4T0Datum.lean:214 | characters |
| `Salt.MR.norm_spolyA_of_pieces` | Salt/MR/M4T0Datum.lean:223 | characters |
| `Salt.MR.spolyA_winCutH_split` | Salt/MR/M4T0Datum.lean:255 | characters |
| `Salt.MR.cfb_sup_of_center_cut` | Salt/MR/M4T0Datum.lean:299 | characters |
| `Salt.MR.pieceDatum_isMultiplicative` | Salt/MR/M4T0Datum.lean:335 | characters |
| `Salt.MR.piece_center_of_inner` | Salt/MR/M4T0Datum.lean:351 | characters |
| `Salt.MR.piece_center_of_wide` | Salt/MR/M4T0Datum.lean:393 | characters |
| `Salt.MR.m4_t0datum_sup` | Salt/MR/M4T0Datum.lean:465 | characters |
| `Salt.MR.m4_hT0band_at_door` | Salt/MR/M4T0Datum.lean:505 | characters |
| `Salt.MR.m4_hT0band_at_door_of_wide` | Salt/MR/M4T0Datum.lean:543 | characters |
| `Salt.MR.band_floor_M0_pieceDatum` | Salt/MR/M4T0Datum.lean:631 | characters |
| `Salt.MR.two_le_calE_door` | Salt/MR/M4T0Datum.lean:648 | characters |
| `Salt.MR.band_floor_M0_doorPiece` | Salt/MR/M4T0Datum.lean:666 | characters |
| `Salt.MR.jMask_iff` | Salt/MR/M4T0DatumDischarge.lean:108 | characters |
| `Salt.MR.gJ_eq_jMask_indicator` | Salt/MR/M4T0DatumDischarge.lean:127 | characters |
| `Salt.MR.zero_pow_eq_ite` | Salt/MR/M4T0DatumDischarge.lean:146 | characters |
| `Salt.MR.pieceDatum_twist_eq` | Salt/MR/M4T0DatumDischarge.lean:158 | characters |
| `Salt.MR.piece_partial_sum_eq` | Salt/MR/M4T0DatumDischarge.lean:180 | characters |
| `Salt.MR.maskTailWeight_zero_le_ramTailWeight_zero` | Salt/MR/M4T0DatumDischarge.lean:196 | characters |
| `Salt.MR.jMask_covered` | Salt/MR/M4T0DatumDischarge.lean:208 | characters |
| `Salt.MR.jMask_mass_le` | Salt/MR/M4T0DatumDischarge.lean:217 | characters |
| `Salt.MR.jMask_htail_le` | Salt/MR/M4T0DatumDischarge.lean:229 | characters |
| `Salt.MR.seamT0_le_sqrt_sqrt` | Salt/MR/M4T0DatumDischarge.lean:301 | characters |
| `Salt.MR.t0datum_grade_of_fit` | Salt/MR/M4T0DatumDischarge.lean:378 | characters |
| `Salt.MR.calP_door_ge` | Salt/MR/M4T0DatumDischarge.lean:521 | characters |
| `Salt.MR.calQK_door_le` | Salt/MR/M4T0DatumDischarge.lean:535 | characters |
| `Salt.MR.door_cover` | Salt/MR/M4T0DatumDischarge.lean:552 | characters |
| `Salt.MR.door_window_bounds` | Salt/MR/M4T0DatumDischarge.lean:570 | characters |
| `Salt.MR.t0d_decay_eq` | Salt/MR/M4T0Discharge.lean:110 | characters |
| `Salt.MR.t0d_far_exp_le` | Salt/MR/M4T0Discharge.lean:122 | characters |
| `Salt.MR.t0d_far_le` | Salt/MR/M4T0Discharge.lean:131 | characters |
| `Salt.MR.t0d_P_le` | Salt/MR/M4T0Discharge.lean:157 | characters |
| `Salt.MR.t0d_err_le` | Salt/MR/M4T0Discharge.lean:164 | characters |
| `Salt.MR.t0d_dilGap_le` | Salt/MR/M4T0Discharge.lean:188 | characters |
| `Salt.MR.one_le_t0dC1` | Salt/MR/M4T0Discharge.lean:205 | characters |
| `Salt.MR.t0d_envelope_decay` | Salt/MR/M4T0Discharge.lean:542 | characters |
| `Salt.MR.le_classSup` | Salt/MR/M4WaveClosed.lean:146 | characters |
| `Salt.MR.classSup_nonneg` | Salt/MR/M4WaveClosed.lean:152 | characters |
| `Salt.MR.classSup_le` | Salt/MR/M4WaveClosed.lean:156 | characters |
| `Salt.MR.norm_sum_windowClass_le_of_norm_le_one` | Salt/MR/M4WaveClosed.lean:162 | characters |
| `Salt.MR.classSup_le_of_norm_le_one` | Salt/MR/M4WaveClosed.lean:172 | characters |
| `Salt.MR.subWindowSup_le_sum_classSup` | Salt/MR/M4WaveClosed.lean:180 | characters |
| `Salt.MR.m4_classBlockMeanSq_trivial` | Salt/MR/M4WaveClosed.lean:210 | characters |
| `Salt.MR.sq_inv_totient_sum_le_sum_sq` | Salt/MR/M4WaveClosed.lean:339 | characters |
| `Salt.MR.le_doorChiSup` | Salt/MR/M4WaveClosed.lean:373 | sieves, characters |
| `Salt.MR.doorChiSup_nonneg` | Salt/MR/M4WaveClosed.lean:378 | characters |
| `Salt.MR.classSup_le_inv_totient_sum_doorChiSup` | Salt/MR/M4WaveClosed.lean:395 | sieves, characters |
| `Salt.MR.m4_rawMS_priced_decay` | Salt/MR/M4WaveClosed.lean:464 | characters |
| `Salt.MR.m4DecayGrade_le_debit` | Salt/MR/M4WaveClosed.lean:482 | characters |
| `Salt.MR.absWindowSum_doorChiCoeff_zero` | Salt/MR/M4WaveClosed.lean:712 | sieves, characters |
| `Salt.MR.absWindowSum_doorChiCoeff_zero_L` | Salt/MR/M4WaveLinear.lean:69 | sieves, characters |
| `Salt.MR.doorChiCoeff_seamCoefW_at_door_L` | Salt/MR/M4WaveLinear.lean:884 | characters |
| `Salt.MR.m4_door_tail_supply_end_L` | Salt/MR/M4WaveLinear.lean:929 | characters |
| `Salt.MR.doorChiCoeff_seamCoefW_punct_H_L_gk` | Salt/MR/M4WaveLinear.lean:1243 | characters |
| `Salt.MR.norm_lamCoeff_le_one` | Salt/MR/M4Window.lean:77 | characters |
| `Salt.MR.Ioc_eq_map_rebase` | Salt/MR/M4Window.lean:123 | characters |
| `Salt.MR.windowExpSum_eq_rebase` | Salt/MR/M4Window.lean:164 | characters, exponential sums |
| `Salt.MR.norm_offWindowSum` | Salt/MR/M4Window.lean:182 | characters |
| `Salt.MR.norm_windowExpSum_eq_absWindowSum` | Salt/MR/M4Window.lean:188 | characters, exponential sums |
| `Salt.MR.norm_absWindowSum_le` | Salt/MR/M4Window.lean:195 | characters |
| `Salt.MR.norm_windowExpSum_le` | Salt/MR/M4Window.lean:208 | characters, exponential sums |
| `Salt.MR.mrtUniformityXi_of_absWindowBound_twelve` | Salt/MR/M4Window.lean:268 | characters |
| `Salt.MR.norm_absWindowSum_sq_split` | Salt/MR/M4Window.lean:334 | characters |
| `Salt.MR.integral_norm_absWindowSum_sq_split` | Salt/MR/M4Window.lean:348 | characters |
| `Salt.MR.sum_bigXi_norm_windowExpSum_sq_le_twelve` | Salt/MR/M4Window.lean:567 | sieves, characters, exponential sums |
| `Salt.MR.l2_budget_line` | Salt/MR/M4Window.lean:635 | characters |
| `Salt.MR.norm_absWindowSum_rat_le_coprime_head_add` | Salt/MR/MRTArcRatCoprime.lean:58 | characters |
| `Salt.MR.regime_headroom_at_socket` | Salt/MR/MRTPort.lean:101 | characters |
| `Salt.MR.mrtQuality_lower_of_pointwise` | Salt/MR/MRTPort.lean:194 | characters |
| `Salt.MR.lam_eq_lamCoeff_of_prime` | Salt/MR/MRTPort.lean:243 | characters |
| `Salt.MR.pretDistSq_lam_eq_lamCoeff` | Salt/MR/MRTPort.lean:255 | characters |
| `Salt.MR.mrtCompMultDatum_lamCoeff` | Salt/MR/MRTPort.lean:301 | characters |
| `Salt.MR.W_first_arm` | Salt/MR/MRTPort.lean:398 | characters |
| `Salt.MR.lamCoeff_mul_coprime` | Salt/MR/MRTPortA1.lean:72 | characters |
| `Salt.MR.mul_exp_neg_le_two_div` | Salt/MR/MRTPortA1Tail.lean:35 | characters |
| `Salt.MR.mrtA1_rhs_tail_le` | Salt/MR/MRTPortA1Tail.lean:43 | characters |
| `Salt.MR.exit_lam_tail_absorb` | Salt/MR/MRTPortExitLam.lean:57 | characters |
| `Salt.MR.m4_exit_lam_of_rowMeanSqLam` | Salt/MR/MRTPortExitLam.lean:76 | characters |
| `Salt.MR.m4_exit_lam_of_rowMeanSqLam_gated` | Salt/MR/MRTPortExitLamGated.lean:80 | characters |
| `Salt.MR.m4_ladder_gates_lam` | Salt/MR/MRTPortLadderGates.lean:58 | characters |
| `Salt.MR.log_le_div_add_const_128` | Salt/MR/MRTPortMLower.lean:73 | characters |
| `Salt.MR.log3_shift_le_linear` | Salt/MR/MRTPortMLower.lean:89 | characters |
| `Salt.MR.mrtM_lamCoeff_lower` | Salt/MR/MRTPortMLower.lean:133 | characters |
| `Salt.MR.mrtM_lamCoeff_loglog_floor` | Salt/MR/MRTPortMLower.lean:152 | characters |
| `Salt.MR.mrtM_lamCoeff_ge` | Salt/MR/MRTPortMLower.lean:190 | characters |
| `Salt.MR.m4_exit_socket_split_of_sq` | Salt/MR/MRTPortSocketSq.lean:41 | characters |
| `Salt.MR.m4_exit_socket_split_sq_trivial` | Salt/MR/MRTPortTrivialSplit.lean:48 | characters |
| `Salt.MR.norm_sq_le_two_of_norm_sub_le` | Salt/MR/MRTPortWindow.lean:32 | characters |
| `Salt.MR.norm_mrtShortMean_sq_le_open` | Salt/MR/MRTPortWindow.lean:53 | characters |
| `Salt.MR.mrtS_subset_Icc` | Salt/MR/MRTProp24.lean:145 | characters |
| `Salt.MR.zero_not_mem_mrtS` | Salt/MR/MRTProp24.lean:151 | characters |
| `Salt.MR.mem_mrtWindow` | Salt/MR/MRTProp24.lean:228 | characters |
| `Salt.MR.mrtS_dilate` | Salt/MR/MRTProp24.lean:323 | characters |
| `Salt.MR.mrtS_indicator_mul_dilate` | Salt/MR/MRTProp24.lean:386 | characters |
| `Salt.MR.mrtBandP_base_le` | Salt/MR/MRTProp24.lean:413 | characters |
| `Salt.MR.mrtBand_primeFactors_lt_of_le_W` | Salt/MR/MRTProp24.lean:433 | characters |
| `Salt.MR.mrtS_dilate_of_le_W` | Salt/MR/MRTProp24.lean:453 | characters |
| `Salt.MR.mrtS_indicator_mul_dilate_of_le_W` | Salt/MR/MRTProp24.lean:460 | characters |
| `Salt.MR.mrtS_dilate_of_le_W_witness` | Salt/MR/MRTProp24.lean:473 | characters |
| `Salt.MR.continuous_pretDistSq_costwist` | Salt/MR/MRTPropA3.lean:168 | characters |
| `Salt.MR.exists_min_pretDistSq` | Salt/MR/MRTPropA3.lean:177 | characters |
| `Salt.MR.mrtT0_disjoint_mrtT1` | Salt/MR/MRTPropA3.lean:240 | characters |
| `Salt.MR.mrtA4_constant_pos` | Salt/MR/MRTPropA3.lean:308 | characters |
| `Salt.MR.mrtA5_rho_margin` | Salt/MR/MRTPropA3.lean:341 | characters |
| `Salt.MR.mrtA5_epsilon_ceiling` | Salt/MR/MRTPropA3.lean:358 | characters |
| `Salt.MR.mrtA4i_holds` | Salt/MR/MRTPropA3.lean:428 | characters |
| `Salt.MR.mrtLemmaA4i_holds` | Salt/MR/MRTPropA3.lean:472 | characters |
| `Salt.MR.mrtM_le` | Salt/MR/MRTPropA3.lean:496 | characters |
| `Salt.MR.mrtA4ii_sixteenth_suffices` | Salt/MR/MRTPropA3.lean:510 | characters |
| `Salt.MR.mrtA4ii_high_M` | Salt/MR/MRTPropA3.lean:521 | characters |
| `Salt.MR.mrtA4ii_high_M_target` | Salt/MR/MRTPropA3.lean:540 | characters |
| `Salt.MR.memS_false_of_Qseq_one_le_one` | Salt/MR/MRTPropA3.lean:589 | characters |
| `Salt.MR.integral_dpolyA_eq_zero_of_empty` | Salt/MR/MRTPropA3.lean:627 | characters |
| `Salt.MR.exp_add_exp_neg_eq_two_cos` | Salt/MR/MRTPropA3.lean:644 | characters |
| `Salt.MR.exp_neg_avg` | Salt/MR/MRTPropA3.lean:653 | characters |
| `Salt.MR.mrtA6_inner_eq_sifted` | Salt/MR/MRTPropA3.lean:825 | characters |
| `Salt.MR.mrtA6_F_sifted` | Salt/MR/MRTPropA3.lean:847 | characters |
| `Salt.MR.trivial_cut_needs_delta_ge_one` | Salt/MR/MRTPropA3.lean:1029 | characters |
| `Salt.MR.renormalise_error_logpower_stronger` | Salt/MR/MRTPropA3.lean:1076 | characters |
| `Salt.MR.landed_halasz_exponent_weaker_than_a6` | Salt/MR/MRTPropA3.lean:1140 | characters |
| `Salt.MR.landed_halasz_M_rate_weaker_than_a6` | Salt/MR/MRTPropA3.lean:1151 | characters |
| `Salt.MR.theta_lift_head_rate_at_log_two` | Salt/MR/MRTPropA3.lean:1187 | characters |
| `Salt.MR.b4_grade_cannot_reach_a6_from_head` | Salt/MR/MRTPropA3.lean:1215 | characters |
| `Salt.MR.grade_cannot_reach_fiftieth_under_sigma_wall` | Salt/MR/MRTPropA3.lean:1243 | characters |
| `Salt.MR.theta_lift_grade_at_log_two_still_weaker` | Salt/MR/MRTPropA3.lean:1251 | characters |
| `Salt.MR.mrtA4i_loss_witness` | Salt/MR/MRTPropA3.lean:1380 | characters |
| `Salt.MR.mrtA4i_loss_pos` | Salt/MR/MRTPropA3.lean:1401 | characters |
| `Salt.MR.mrtA7_exact_at_center` | Salt/MR/MRTPropA3.lean:1434 | characters |
| `Salt.MR.not_mrtLemmaA4ii` | Salt/MR/MRTPropA3.lean:1476 | characters |
| `Salt.MR.recenter_then_halve_constant` | Salt/MR/MRTPropA3.lean:1543 | characters |
| `Salt.MR.landed_route_below_a4ii_target` | Salt/MR/MRTPropA3.lean:1554 | characters |
| `Salt.MR.lt_of_mem_mrtT0` | Salt/MR/MRTPropA3.lean:1605 | characters |
| `Salt.MR.abs_sub_le_of_mem_mrtT0` | Salt/MR/MRTPropA3.lean:1613 | characters |
| `Salt.MR.mrtA4iiFixed_high_M` | Salt/MR/MRTPropA3.lean:1658 | characters |
| `Salt.MR.mrtA4ii_far_centre_cap` | Salt/MR/MRTPropA3.lean:1682 | characters |
| `Salt.MR.mrtA7_factor_conj` | Salt/MR/MRTPropA3.lean:1715 | characters |
| `Salt.MR.mrtA7_factors_differ` | Salt/MR/MRTPropA3.lean:1727 | characters |
| `Salt.MR.mrtA8_of_mvt` | Salt/MR/MRTPropA3.lean:1758 | characters |
| `Salt.MR.mrtA8_mvt_step` | Salt/MR/MRTPropA3.lean:1783 | characters |
| `Salt.MR.mrtA8` | Salt/MR/MRTPropA3.lean:1818 | characters |
| `Salt.MR.mrtA3_T0_pointwise_sq` | Salt/MR/MRTPropA3.lean:1911 | characters |
| `Salt.MR.mrtA3_T0_exponent` | Salt/MR/MRTPropA3.lean:1933 | characters |
| `Salt.MR.integral_inv_one_add_sq_le_one` | Salt/MR/MRTPropA3.lean:1939 | characters |
| `Salt.MR.mrtA7_factors_same_norm` | Salt/MR/MRTPropA3.lean:1996 | characters |
| `Salt.MR.mrtT0_subset_Icc` | Salt/MR/MRTPropA3.lean:2039 | characters |
| `Salt.MR.mrtT0_Icc_length` | Salt/MR/MRTPropA3.lean:2051 | characters |
| `Salt.MR.integral_inv_one_sub_sq_le_one` | Salt/MR/MRTPropA3.lean:2059 | characters |
| `Salt.MR.integral_inv_one_add_abs_sq_le_two` | Salt/MR/MRTPropA3.lean:2092 | characters |
| `Salt.MR.integral_inv_one_add_abs_sub_sq_le_two` | Salt/MR/MRTPropA3.lean:2129 | characters |
| `Salt.MR.mrtA3_T0_integral_bound` | Salt/MR/MRTPropA3.lean:2153 | characters |
| `Salt.MR.mrtA3_T0_setIntegral_bound` | Salt/MR/MRTPropA3.lean:2204 | characters |
| `Salt.MR.measurableSet_mrtT1` | Salt/MR/MRTPropA3.lean:2236 | characters |
| `Salt.MR.measurableSet_mrtT0` | Salt/MR/MRTPropA3.lean:2247 | characters |
| `Salt.MR.continuous_a3_majorant` | Salt/MR/MRTPropA3.lean:2259 | characters |
| `Salt.MR.mrtA3_T0_setIntegral_bound_onT0` | Salt/MR/MRTPropA3.lean:2279 | characters |
| `Salt.MR.mrtT0_mono_T` | Salt/MR/MRTPropA3.lean:2325 | characters |
| `Salt.MR.dpolyA_l2_mvt` | Salt/MR/MRTPropA3.lean:2402 | characters |
| `Salt.MR.dpolyA_l2_mvt_Icc` | Salt/MR/MRTPropA3.lean:2419 | characters |
| `Salt.MR.sum_sq_norm_div_le` | Salt/MR/MRTPropA3.lean:2436 | characters |
| `Salt.MR.mrtA3_mvt_branch` | Salt/MR/MRTPropA3.lean:2466 | characters |
| `Salt.MR.memS_false_of_band_inverted` | Salt/MR/MRTPropA3.lean:2530 | characters |
| `Salt.MR.memS_false_of_prime_free_band` | Salt/MR/MRTPropA3.lean:2567 | characters |
| `Salt.MR.band_8_10_prime_free` | Salt/MR/MRTPropA3.lean:2577 | characters |
| `Salt.MR.mrtT1_subset_Icc` | Salt/MR/MRTPropA3.lean:2582 | characters |
| `Salt.MR.integral_sq_le_of_pointwise_on_mrtT1` | Salt/MR/MRTPropA3.lean:2635 | characters |
| `Salt.MR.mrtA3_split_bound` | Salt/MR/MRTPropA3.lean:2666 | characters |
| `Salt.MR.band_eq_Icc` | Salt/MR/MRTPropA3.lean:2682 | characters |
| `Salt.MR.mrtA3_split_bound_interval` | Salt/MR/MRTPropA3.lean:2690 | characters |
| `Salt.MR.mrtM_nonneg` | Salt/MR/MRTPropA3.lean:2718 | characters |
| `Salt.MR.mrtM_one_eq_zero` | Salt/MR/MRTPropA3.lean:2739 | characters |
| `Salt.MR.mrtA3_bracket_nonneg` | Salt/MR/MRTPropA3.lean:2756 | characters |
| `Salt.MR.mrtA3_first_term_of_Pseq1_zero` | Salt/MR/MRTPropA3.lean:2840 | characters |
| `Salt.MR.band_zero_two_has_prime` | Salt/MR/MRTPropA3.lean:2848 | characters |
| `Salt.MR.mrtA3_leading_factor_of_Qseq1_zero` | Salt/MR/MRTPropA3.lean:2874 | characters |
| `Salt.MR.memS_false_of_Qseq1_zero` | Salt/MR/MRTPropA3.lean:2881 | characters |
| `Salt.MR.bridge_side_conditions_of_mrtA3_hyps` | Salt/MR/MRTPropA3.lean:2915 | characters |
| `Salt.MR.mrtT0_subset_band` | Salt/MR/MRTPropA3.lean:2947 | characters |
| `Salt.MR.continuous_a3_twistedSum` | Salt/MR/MRTPropA3.lean:2958 | characters |
| `Salt.MR.integrableOn_sq_mrtT0_of_continuous` | Salt/MR/MRTPropA3.lean:2966 | characters |
| `Salt.MR.integrableOn_sq_mrtT1_of_continuous` | Salt/MR/MRTPropA3.lean:2972 | characters |
| `Salt.MR.renormalise_hyx_of_mrtT0` | Salt/MR/MRTPropA3.lean:3062 | characters |
| `Salt.MR.gJ_f_costwist_mul` | Salt/MR/MRTPropA3.lean:3149 | characters |
| `Salt.MR.gJ_f_costwist_mul_coprime` | Salt/MR/MRTPropA3.lean:3169 | characters |
| `Salt.MR.one_sub_re_le_norm_one_sub` | Salt/MR/MRTPropA3.lean:3212 | characters |
| `Salt.MR.pretDistSq_one_le_sum_norm` | Salt/MR/MRTPropA3.lean:3218 | characters |
| `Salt.MR.norm_one_sub_liouvilleC_prime` | Salt/MR/MRTPropA3.lean:3255 | characters |
| `Salt.MR.sum_norm_one_sub_liouvilleC` | Salt/MR/MRTPropA3.lean:3262 | characters |
| `Salt.MR.recenter_from_unit_floor` | Salt/MR/MRTPropA3.lean:3377 | characters |
| `Salt.MR.unit_floor_route_above_a4ii_target` | Salt/MR/MRTPropA3.lean:3387 | characters |
| `Salt.MR.sieved_primes_floor_le_pretDistSq_sifted` | Salt/MR/MRTPropA3.lean:3413 | characters |
| `Salt.MR.gJ_prime_eq_zero_iff` | Salt/MR/MRTPropA3.lean:3451 | characters |
| `Salt.MR.mertens_block_difference` | Salt/MR/MRTPropA3.lean:3487 | characters |
| `Salt.MR.pretDistSq_ge_cos_average` | Salt/MR/MRTPropA3.lean:3515 | characters |
| `Salt.MR.integral_abs_cos_pi_unit` | Salt/MR/MRTPropA3.lean:3578 | characters |
| `Salt.MR.mrtA4i_halving` | Salt/MR/MRTPropA3.lean:3635 | characters |
| `Salt.MR.mrtA4ii_high_M_sixteenth` | Salt/MR/MRTPropA3.lean:3684 | characters |
| `Salt.MR.mrt_exponent_gap` | Salt/MR/MRTPropA3.lean:3700 | characters |
| `Salt.MR.mrt_exponent_gap_at_Y` | Salt/MR/MRTPropA3.lean:3707 | characters |
| `Salt.MR.mrtA4ii_constant_decomposition` | Salt/MR/MRTPropA3.lean:3726 | characters |
| `Salt.MR.pretDistSq_ge_cos_average_restricted` | Salt/MR/MRTPropA3.lean:3741 | characters |
| `Salt.MR.abs_cos_pi_mul_eq_cos_pi_mul_dist_round` | Salt/MR/MRTPropA3.lean:3763 | characters |
| `Salt.MR.mrtA4_summand_matches_source` | Salt/MR/MRTPropA3.lean:3794 | characters |
| `Salt.MR.mrtA4ii_far_of_cos_average` | Salt/MR/MRTPropA3.lean:3823 | characters |
| `Salt.MR.mrtA4ii_far_of_either_estimate` | Salt/MR/MRTPropA3.lean:3935 | characters |
| `Salt.MR.closed_open_window_card_le_one` | Salt/MR/MRTPropA3.lean:4034 | characters |
| `Salt.MR.shortWindow_closed_sub_open_norm_le` | Salt/MR/MRTPropA3.lean:4052 | characters |
| `Salt.MR.mrtM_costwist_self` | Salt/MR/MRTPropA3.lean:4145 | characters |
| `Salt.MR.not_mrtLemmaA7Statement` | Salt/MR/MRTPropA3.lean:4158 | characters |
| `Salt.MR.mrt_constant_factors` | Salt/MR/MRTPropA3.lean:4316 | characters |
| `Salt.MR.vk34_constant_factors` | Salt/MR/MRTPropA3.lean:4323 | characters |
| `Salt.MR.vk34_constant_fails_rho_margin` | Salt/MR/MRTPropA3.lean:4374 | characters |
| `Salt.MR.vk34_constant_pos` | Salt/MR/MRTPropA3.lean:4385 | characters |
| `Salt.MR.vk34_constant_clears_bar` | Salt/MR/MRTPropA3.lean:4393 | characters |
| `Salt.MR.vk34_constant_lt_mrt` | Salt/MR/MRTPropA3.lean:4402 | characters |
| `Salt.MR.mrtA5_rho_margin34` | Salt/MR/MRTPropA3.lean:4432 | characters |
| `Salt.MR.mrtA5_epsilon_ceiling34` | Salt/MR/MRTPropA3.lean:4443 | characters |
| `Salt.MR.vk34_bar_366_fails` | Salt/MR/MRTPropA3.lean:4451 | characters |
| `Salt.MR.mrtA4ii_high_M_target34` | Salt/MR/MRTPropA3.lean:4468 | characters |
| `Salt.MR.not_mrtLargeRangeEquidistribution` | Salt/MR/MRTPropA3.lean:4614 | characters |
| `Salt.MR.hMsup_of_propA3_shape` | Salt/MR/MRTPropA3Bridge.lean:56 | characters |
| `Salt.MR.one_le_X_div_h` | Salt/MR/MRTPropA3Bridge.lean:126 | characters |
| `Salt.MR.hMsup_of_propA3_shape_parseval` | Salt/MR/MRTPropA3Bridge.lean:140 | characters |
| `Salt.MR.parseval_dpolyA_terms_of_propA3_shape` | Salt/MR/MRTPropA3Bridge.lean:163 | characters |
| `Salt.MR.parseval_bound_of_propA3_shape` | Salt/MR/MRTPropA3Bridge.lean:204 | characters |
| `Salt.MR.log3_shift_mono` | Salt/MR/MRTQualityLam.lean:56 | characters |
| `Salt.MR.mrtM_lam_lower` | Salt/MR/MRTQualityLam.lean:75 | characters |
| `Salt.MR.mrtA2_first_summand_le_of_h` | Salt/MR/MRTSummandSupply.lean:131 | characters |
| `Salt.MR.mrtBands_A1_vacuous_at_Pseq_one_two` | Salt/MR/MRTSummandSupply.lean:155 | characters |
| `Salt.MR.mrtBands_A1_binds_at_Pseq_one_three` | Salt/MR/MRTSummandSupply.lean:192 | characters |
| `Salt.MR.mem_mrtShortWindow` | Salt/MR/MRTThmA1.lean:95 | characters |
| `Salt.MR.measurable_mrtShortMean` | Salt/MR/MRTThmA1.lean:139 | characters |
| `Salt.MR.norm_mrtShortMean_le` | Salt/MR/MRTThmA1.lean:150 | characters |
| `Salt.MR.intervalIntegrable_mrtThmA1_integrand` | Salt/MR/MRTThmA1.lean:172 | characters |
| `Salt.MR.sum_inv_sq_Icc_one_le_two` | Salt/MR/MRTThmA1.lean:204 | characters |
| `Salt.MR.sep_inv_sq_sum_le` | Salt/MR/MVCore.lean:222 | characters |
| `Salt.MR.mvHilbertUniform_holds` | Salt/MR/MVCore2.lean:575 | characters |
| `Salt.MR.dirichlet_poly_l2_mvt_final` | Salt/MR/MVCore2.lean:620 | characters |
| `Salt.MR.l2_duality` | Salt/MR/MVHilbert.lean:383 | characters |
| `Salt.MR.log_gap_ge_of_modEq` | Salt/MR/MVHilbertFinset.lean:56 | characters |
| `Salt.MR.dpolyS_l2_expand` | Salt/MR/MVHilbertFinset.lean:164 | characters |
| `Salt.MR.dpolyS_l2_diagonal` | Salt/MR/MVHilbertFinset.lean:191 | characters |
| `Salt.MR.offdiag_eq_hilbertS` | Salt/MR/MVHilbertFinset.lean:239 | characters |
| `Salt.MR.dpolyS_l2_mvt_final` | Salt/MR/MVHilbertFinset.lean:320 | characters |
| `Salt.MR.dpolyS_meanSq_reflect` | Salt/MR/MVHilbertFinset.lean:331 | characters |
| `Salt.MR.pretFloorShape_le_of_le` | Salt/MR/MWindowBridge.lean:107 | characters |
| `Salt.MR.dist_floor_far_sep` | Salt/MR/MWindowBridge.lean:144 | characters |
| `Salt.MR.dist_floor_far_range` | Salt/MR/MWindowBridge.lean:174 | characters |
| `Salt.MR.M_win_bddBelow` | Salt/MR/MWindowBridge.lean:203 | characters |
| `Salt.MR.M_win_window_nonempty` | Salt/MR/MWindowBridge.lean:209 | characters |
| `Salt.MR.M_win_le` | Salt/MR/MWindowBridge.lean:213 | characters |
| `Salt.MR.M_win_approx` | Salt/MR/MWindowBridge.lean:221 | characters |
| `Salt.MR.M_win_anti` | Salt/MR/MWindowBridge.lean:234 | characters |
| `Salt.MR.M_window_bridge` | Salt/MR/MWindowBridge.lean:260 | characters |
| `Salt.MR.M_window_bridge_inf` | Salt/MR/MWindowBridge.lean:287 | characters |
| `Salt.MR.M_window_bridge_seam` | Salt/MR/MWindowBridge.lean:323 | characters |
| `Salt.MR.M_rangeCap_window_nonempty` | Salt/MR/MWindowBridge.lean:360 | characters |
| `Salt.MR.M_rangeCap_le_M_range` | Salt/MR/MWindowBridge.lean:387 | characters |
| `Salt.MR.Mrange_cap_one_floor` | Salt/MR/MWindowBridge.lean:405 | characters |
| `Salt.MR.Mrange_one_floor_2X` | Salt/MR/MWindowBridge.lean:430 | characters |
| `Salt.MR.log_sq_le_self` | Salt/MR/MWindowBridge.lean:441 | characters |
| `Salt.MR.contour_height_le_two_mul` | Salt/MR/MWindowBridge.lean:468 | characters |
| `Salt.MR.dist_floor_far_sep_at` | Salt/MR/MWindowExtend.lean:87 | characters |
| `Salt.MR.dist_floor_far_reach` | Salt/MR/MWindowExtend.lean:117 | characters |
| `Salt.MR.M_window_bridge_reach` | Salt/MR/MWindowExtend.lean:147 | characters |
| `Salt.MR.M_window_bridge_seam_reach` | Salt/MR/MWindowExtend.lean:184 | characters |
| `Salt.MR.M_window_bridge_seam_2X` | Salt/MR/MWindowExtend.lean:205 | characters |
| `Salt.MR.M_window_bridge_seam_3X` | Salt/MR/MWindowExtend.lean:221 | characters |
| `Salt.MR.hM0_at_centre` | Salt/MR/MWindowExtend.lean:259 | characters |
| `Salt.MR.pretFloorShape_quarter_at_pow` | Salt/MR/MWindowExtend.lean:298 | characters |
| `Salt.MR.pretFloorShape_quarter_sq` | Salt/MR/MWindowExtend.lean:354 | characters |
| `Salt.MR.Tstar_two_mul_le_quarter` | Salt/MR/MWindowExtend.lean:376 | characters |
| `Salt.MR.seamGateRstar_le_two_mul` | Salt/MR/MWindowExtend.lean:450 | characters |
| `Salt.MR.zeta_block_secondDeriv` | Salt/MR/MidBand.lean:81 | characters |
| `Salt.MR.halasz_socket_midHigh` | Salt/MR/MidBand.lean:479 | characters |
| `Salt.MR.halasz_socket` | Salt/MR/MidBand.lean:830 | characters |
| `Salt.MR.log_nat_nonneg` | Salt/MR/MinorArcCore.lean:88 | characters |
| `Salt.MR.log_nat_mono` | Salt/MR/MinorArcCore.lean:94 | characters |
| `Salt.MR.log_nat_monotone` | Salt/MR/MinorArcCore.lean:101 | characters |
| `Salt.MR.dist₁_neg_zero` | Salt/MR/MinorArcCore.lean:105 | characters |
| `Salt.MR.inner_range_eq` | Salt/MR/MinorArcCore.lean:112 | characters |
| `Salt.MR.eR_phase_reindex` | Salt/MR/MinorArcCore.lean:133 | characters |
| `Salt.MR.partial_phase_bound` | Salt/MR/MinorArcCore.lean:140 | characters |
| `Salt.MR.inner_phase_bound` | Salt/MR/MinorArcCore.lean:154 | characters |
| `Salt.MR.sum_Ioc_abel` | Salt/MR/MinorArcCore.lean:177 | characters |
| `Salt.MR.norm_sum_Ioc_weighted_le` | Salt/MR/MinorArcCore.lean:193 | characters |
| `Salt.MR.inner_log_phase_bound` | Salt/MR/MinorArcCore.lean:223 | characters |
| `Salt.MR.typeI_one_bound` | Salt/MR/MinorArcCore.lean:270 | characters |
| `Salt.MR.typeI_two_bound` | Salt/MR/MinorArcCore.lean:296 | characters |
| `Salt.MR.typeI_bound` | Salt/MR/MinorArcCore.lean:332 | characters |
| `Salt.MR.typeIIData_eq_zero_of_le` | Salt/MR/MinorArcCore.lean:370 | characters |
| `Salt.MR.typeII_inner_vanishes` | Salt/MR/MinorArcCore.lean:381 | characters |
| `Salt.MR.typeII_block_eq_zero` | Salt/MR/MinorArcCore.lean:397 | characters |
| `Salt.MR.dpair_range_eq` | Salt/MR/MinorArcCore.lean:410 | characters |
| `Salt.MR.typeIIBlockBd_nonneg` | Salt/MR/MinorArcCore.lean:682 | characters |
| `Salt.MR.typeII_block_bound` | Salt/MR/MinorArcCore.lean:688 | characters |
| `Salt.MR.norm_lambda_head_le` | Salt/MR/MinorArcCore.lean:775 | characters |
| `Salt.MR.lambda_head_add_tail` | Salt/MR/MinorArcCore.lean:791 | characters |
| `Salt.MR.typeII_dyadic_bound` | Salt/MR/MinorArcCore.lean:815 | characters |
| `Salt.MR.vinogradov_lambda` | Salt/MR/MinorArcCore.lean:847 | characters |
| `Salt.MR.vinogradov_lambda_dyadic` | Salt/MR/MinorArcCore.lean:867 | characters |
| `Salt.MR.vinogradov_lambda_sq` | Salt/MR/MinorArcCore.lean:885 | characters |
| `Salt.MR.sqrt_add_le_sqrt_add_sqrt` | Salt/MR/MinorArcExit.lean:96 | characters |
| `Salt.MR.norm_sum_Ioc_weighted_le_antitone` | Salt/MR/MinorArcExit.lean:121 | characters |
| `Salt.MR.expSum_eq_indicator` | Salt/MR/MinorArcExit.lean:157 | characters, exponential sums |
| `Salt.MR.sum_lambda_not_prime_le` | Salt/MR/MinorArcExit.lean:203 | characters |
| `Salt.MR.norm_thetaPhase_sub_lambdaPhase` | Salt/MR/MinorArcExit.lean:229 | characters |
| `Salt.MR.prime_sum_to_lambda` | Salt/MR/MinorArcExit.lean:245 | characters |
| `Salt.MR.approx_c_form` | Salt/MR/MinorArcExit.lean:387 | characters |
| `Salt.MR.expSum_abel` | Salt/MR/MinorArcExit.lean:407 | characters, exponential sums |
| `Salt.MR.typeII_dyadic_trunc` | Salt/MR/MinorArcExit.lean:471 | characters |
| `Salt.MR.typeIIBlockBd_le_crude` | Salt/MR/MinorArcExit.lean:511 | characters |
| `Salt.MR.typeII_dyadic_sum_le` | Salt/MR/MinorArcExit.lean:617 | characters |
| `Salt.MR.vinoBd_mono` | Salt/MR/MinorArcExit.lean:674 | characters |
| `Salt.MR.lambdaPhase_le` | Salt/MR/MinorArcExit.lean:706 | characters |
| `Salt.MR.expSum_le_vinoBd` | Salt/MR/MinorArcExit.lean:729 | characters, exponential sums |
| `Salt.MR.two_le_winBot` | Salt/MR/MinorArcExit.lean:796 | characters |
| `Salt.MR.winBot_le_winTop` | Salt/MR/MinorArcExit.lean:810 | characters |
| `Salt.MR.one_le_vaughanW` | Salt/MR/MinorArcExit.lean:822 | characters |
| `Salt.MR.vaughanW_sq_le` | Salt/MR/MinorArcExit.lean:828 | characters |
| `Salt.MR.winTop_le_pow` | Salt/MR/MinorArcExit.lean:834 | characters |
| `Salt.MR.primeWindow_sub` | Salt/MR/MinorArcExit.lean:852 | characters |
| `Salt.MR.mem_primeWindow_of_mem` | Salt/MR/MinorArcExit.lean:865 | characters |
| `Salt.MR.eK_eq_eR` | Salt/MR/MinorArcVaughan.lean:93 | characters |
| `Salt.MR.norm_one_sub_eR` | Salt/MR/MinorArcVaughan.lean:100 | characters |
| `Salt.MR.eR_add_intCast` | Salt/MR/MinorArcVaughan.lean:104 | characters |
| `Salt.MR.eR_mul_natCast` | Salt/MR/MinorArcVaughan.lean:108 | characters |
| `Salt.MR.dist₁_eq_sub_zero` | Salt/MR/MinorArcVaughan.lean:122 | characters |
| `Salt.MR.abs_sin_pi_mul_add_intCast` | Salt/MR/MinorArcVaughan.lean:126 | characters |
| `Salt.MR.two_mul_dist₁_le_abs_sin` | Salt/MR/MinorArcVaughan.lean:136 | characters |
| `Salt.MR.inv_le_dist₁_intCast_div` | Salt/MR/MinorArcVaughan.lean:162 | characters |
| `Salt.MR.vaughan_expSum` | Salt/MR/MinorArcVaughan.lean:191 | characters |
| `Salt.MR.norm_moebius_le` | Salt/MR/MinorArcVaughan.lean:205 | characters |
| `Salt.MR.norm_typeICoeff_le` | Salt/MR/MinorArcVaughan.lean:214 | characters |
| `Salt.MR.norm_typeIIData_le` | Salt/MR/MinorArcVaughan.lean:220 | characters |
| `Salt.MR.geom_phase_card_bound` | Salt/MR/MinorArcVaughan.lean:227 | characters |
| `Salt.MR.geom_phase_dist_bound` | Salt/MR/MinorArcVaughan.lean:237 | characters |
| `Salt.MR.minTerm_le_left` | Salt/MR/MinorArcVaughan.lean:274 | characters |
| `Salt.MR.minTerm_le_inv` | Salt/MR/MinorArcVaughan.lean:280 | characters |
| `Salt.MR.minTerm_nonneg` | Salt/MR/MinorArcVaughan.lean:284 | characters |
| `Salt.MR.minTerm_mono_left` | Salt/MR/MinorArcVaughan.lean:291 | characters |
| `Salt.MR.geom_phase_bound` | Salt/MR/MinorArcVaughan.lean:298 | characters |
| `Salt.MR.one_add_log_le_two_mul_log` | Salt/MR/MinorArcVaughan.lean:323 | characters |
| `Salt.MR.sum_range_inv_succ_le` | Salt/MR/MinorArcVaughan.lean:334 | characters |
| `Salt.MR.minsum_residue_count` | Salt/MR/MinorArcVaughan.lean:348 | characters |
| `Salt.MR.minsum_block_core` | Salt/MR/MinorArcVaughan.lean:480 | characters |
| `Salt.MR.minsum_block` | Salt/MR/MinorArcVaughan.lean:626 | characters |
| `Salt.MR.minsum_shift` | Salt/MR/MinorArcVaughan.lean:653 | characters |
| `Salt.MR.four_mul_ge_of_mem_blockExc_zero` | Salt/MR/MinorArcVaughan.lean:691 | characters |
| `Salt.MR.minsum_d_dependent` | Salt/MR/MinorArcVaughan.lean:737 | characters |
| `Salt.MR.muGr_isMultiplicative` | Salt/MR/MobiusChiRamare.lean:160 | characters |
| `Salt.MR.ramTailWeight_nonneg` | Salt/MR/MobiusChiRamare.lean:214 | characters |
| `Salt.MR.ramTailWeight_support` | Salt/MR/MobiusChiRamare.lean:224 | characters |
| `Salt.MR.ramTailWeight_zero_param` | Salt/MR/MobiusChiRamare.lean:233 | characters |
| `Salt.MR.ramTailWeight_le_zero_param` | Salt/MR/MobiusChiRamare.lean:244 | characters |
| `Salt.MR.ramTailWeight_isMultiplicative` | Salt/MR/MobiusChiRamare.lean:257 | characters |
| `Salt.MR.ramTailWeight_prime_pow` | Salt/MR/MobiusChiRamare.lean:312 | characters |
| `Salt.MR.ramTailWeight_eq_zeta_mul_muGr` | Salt/MR/MobiusChiRamare.lean:334 | characters |
| `Salt.MR.ramTailWeight_eq_sum_divisors` | Salt/MR/MobiusChiRamare.lean:382 | characters |
| `Salt.MR.mu_mul_ramTailWeight` | Salt/MR/MobiusChiRamare.lean:393 | characters |
| `Salt.MR.muGr_eq_sum_divisorsAntidiagonal` | Salt/MR/MobiusChiRamare.lean:404 | characters |
| `Salt.MR.muGr_twist_eq_sum_divisorsAntidiagonal` | Salt/MR/MobiusChiRamare.lean:425 | characters |
| `Salt.MR.MmuChi_inner_dvd` | Salt/MR/MobiusChiRamare.lean:457 | characters |
| `Salt.MR.MmuGrChi_eq_sum` | Salt/MR/MobiusChiRamare.lean:492 | characters |
| `Salt.MR.norm_MmuGrChi_le_split` | Salt/MR/MobiusChiRamare.lean:560 | characters |
| `Salt.MR.MmuRamChi_eq_integral` | Salt/MR/MobiusChiRamare.lean:777 | characters |
| `Salt.MR.norm_MmuRamChi_le_of_uniform` | Salt/MR/MobiusChiRamare.lean:802 | characters |
| `Salt.MR.muGrMask_isMultiplicative` | Salt/MR/MobiusChiRamareUnion.lean:170 | characters |
| `Salt.MR.maskTailWeight_nonneg` | Salt/MR/MobiusChiRamareUnion.lean:210 | characters |
| `Salt.MR.maskTailWeight_support` | Salt/MR/MobiusChiRamareUnion.lean:219 | characters |
| `Salt.MR.maskTailWeight_zero_param` | Salt/MR/MobiusChiRamareUnion.lean:228 | characters |
| `Salt.MR.maskTailWeight_le_zero_param` | Salt/MR/MobiusChiRamareUnion.lean:237 | characters |
| `Salt.MR.maskTailWeight_isMultiplicative` | Salt/MR/MobiusChiRamareUnion.lean:248 | characters |
| `Salt.MR.maskTailWeight_prime_pow` | Salt/MR/MobiusChiRamareUnion.lean:279 | characters |
| `Salt.MR.maskTailWeight_eq_zeta_mul_muGrMask` | Salt/MR/MobiusChiRamareUnion.lean:299 | characters |
| `Salt.MR.maskTailWeight_eq_sum_divisors` | Salt/MR/MobiusChiRamareUnion.lean:342 | characters |
| `Salt.MR.mu_mul_maskTailWeight` | Salt/MR/MobiusChiRamareUnion.lean:350 | characters |
| `Salt.MR.muGrMask_eq_sum_divisorsAntidiagonal` | Salt/MR/MobiusChiRamareUnion.lean:358 | characters |
| `Salt.MR.muGrMask_twist_eq_sum_divisorsAntidiagonal` | Salt/MR/MobiusChiRamareUnion.lean:378 | characters |
| `Salt.MR.MmuGrChiMask_eq_sum` | Salt/MR/MobiusChiRamareUnion.lean:414 | characters |
| `Salt.MR.norm_MmuGrChiMask_le_split` | Salt/MR/MobiusChiRamareUnion.lean:473 | characters |
| `Salt.MR.MmuRamChiMask_eq_integral` | Salt/MR/MobiusChiRamareUnion.lean:669 | characters |
| `Salt.MR.norm_MmuRamChiMask_le_of_uniform` | Salt/MR/MobiusChiRamareUnion.lean:693 | characters |
| `Salt.MR.muGrMask_blockMask` | Salt/MR/MobiusChiRamareUnion.lean:774 | characters |
| `Salt.MR.maskTailWeight_blockMask` | Salt/MR/MobiusChiRamareUnion.lean:778 | characters |
| `Salt.MR.MmuGrChiMask_blockMask` | Salt/MR/MobiusChiRamareUnion.lean:784 | characters |
| `Salt.MR.MmuRamChiMask_blockMask` | Salt/MR/MobiusChiRamareUnion.lean:788 | characters |
| `Salt.MR.unionOmega_eq_add_of_lt` | Salt/MR/MobiusChiRamareUnion.lean:802 | characters |
| `Salt.MR.unionDamp_eq_mul` | Salt/MR/MobiusChiRamareUnion.lean:819 | characters |
| `Salt.MR.muGrU_apply_of_lt` | Salt/MR/MobiusChiRamareUnion.lean:848 | characters |
| `Salt.MR.MmuGrChiU_eq_sum` | Salt/MR/MobiusChiRamareUnion.lean:855 | characters |
| `Salt.MR.exp_phase_eq_cpow` | Salt/MR/MobiusChiRate.lean:92 | characters |
| `Salt.MR.chiBarTwist_eq_inv_mul_cpow` | Salt/MR/MobiusChiRate.lean:109 | characters |
| `Salt.MR.norm_muChiTw_le_one` | Salt/MR/MobiusChiRate.lean:130 | characters |
| `Salt.MR.LSeries_muChiTw_eq_LFunction_inv` | Salt/MR/MobiusChiRate.lean:159 | zeros, characters |
| `Salt.MR.muChiTw_summable_dom` | Salt/MR/MobiusChiRate.lean:203 | characters |
| `Salt.MR.mmu1Chi_eq_integral_LSeries` | Salt/MR/MobiusChiRate.lean:229 | zeros, characters |
| `Salt.MR.mmu1Chi_eq_integral` | Salt/MR/MobiusChiRate.lean:297 | characters |
| `Salt.MR.norm_LFunction_inv_shifted_cline_le` | Salt/MR/MobiusChiRate.lean:324 | characters |
| `Salt.MR.norm_muChiTw_LSeries_cline_le` | Salt/MR/MobiusChiRate.lean:331 | zeros, characters |
| `Salt.MR.boxWidth_pos` | Salt/MR/MobiusChiRate.lean:393 | characters |
| `Salt.MR.vkBoxWidth_le_of_le` | Salt/MR/MobiusChiRate.lean:427 | characters |
| `Salt.MR.log_le_of_below_floor` | Salt/MR/MobiusChiRate.lean:473 | characters |
| `Salt.MR.LFunction_no_zero_in_box` | Salt/MR/MobiusChiRate.lean:509 | characters |
| `Salt.MR.LFunction_no_zero_in_shifted_box` | Salt/MR/MobiusChiRate.lean:586 | characters |
| `Salt.MR.vkShallowWidth_pos` | Salt/MR/MobiusChiRate.lean:683 | characters |
| `Salt.MR.mmu1Chi_contour_shift` | Salt/MR/MobiusChiRateClose.lean:87 | characters |
| `Salt.MR.mmu1Chi_rate_of_pinned` | Salt/MR/MobiusChiRateClose.lean:374 | characters |
| `Salt.MR.pin_scale_facts` | Salt/MR/MobiusChiRateClose.lean:729 | characters |
| `Salt.MR.logq_le_thirteen` | Salt/MR/MobiusChiRateClose.lean:754 | characters |
| `Salt.MR.pinW_le_sharp` | Salt/MR/MobiusChiRateClose.lean:769 | characters |
| `Salt.MR.pinW_le_boxWidth_half` | Salt/MR/MobiusChiRateClose.lean:805 | characters |
| `Salt.MR.x_mul_Mmu1Chi` | Salt/MR/MobiusChiRateClose.lean:851 | characters |
| `Salt.MR.MmuChi_split` | Salt/MR/MobiusChiRateClose.lean:861 | characters |
| `Salt.MR.TsumChi_split` | Salt/MR/MobiusChiRateClose.lean:867 | characters |
| `Salt.MR.desmooth_identity_chi` | Salt/MR/MobiusChiRateClose.lean:874 | characters |
| `Salt.MR.remainder_bound_chi` | Salt/MR/MobiusChiRateClose.lean:894 | characters |
| `Salt.MR.mmuChiRate_of_smoothed` | Salt/MR/MobiusChiRateClose.lean:937 | characters |
| `Salt.MR.xiCarveWidth_of_half` | Salt/MR/MobiusChiRateClose.lean:1112 | characters |
| `Salt.MR.eulerFac_differentiable` | Salt/MR/MobiusChiRateClose.lean:1392 | characters |
| `Salt.MR.norm_one_sub_prime_cpow_ge` | Salt/MR/MobiusChiRateClose.lean:1406 | characters |
| `Salt.MR.one_le_pow_mul_norm_eulerFac` | Salt/MR/MobiusChiRateClose.lean:1433 | characters |
| `Salt.MR.eulerFac_ne_zero` | Salt/MR/MobiusChiRateClose.lean:1446 | characters |
| `Salt.MR.two_pow_omega_le` | Salt/MR/MobiusChiRateClose.lean:1453 | characters |
| `Salt.MR.norm_eulerFac_inv_le` | Salt/MR/MobiusChiRateClose.lean:1459 | characters |
| `Salt.MR.pinW_le_quarter` | Salt/MR/MobiusChiRateClose.lean:1499 | characters |
| `Salt.MR.moment_core_bound` | Salt/MR/MomentsA2.lean:82 | characters |
| `Salt.MR.lemma13_moment` | Salt/MR/MomentsA2.lean:246 | characters |
| `Salt.MR.lemma12_meansq_conditional` | Salt/MR/MomentsA2.lean:364 | characters |
| `Salt.MR.abel_master` | Salt/MR/MultShiu.lean:65 | characters |
| `Salt.MR.lambda_partial_alpha` | Salt/MR/MultShiu.lean:157 | characters |
| `Salt.MR.lambda_tail_shift` | Salt/MR/MultShiu.lean:204 | characters |
| `Salt.MR.rough_prime_tail` | Salt/MR/MultShiu.lean:251 | characters |
| `Salt.MR.ht_valuation_partition` | Salt/MR/MultShiu.lean:408 | characters |
| `Salt.MR.hall_tenenbaum_core` | Salt/MR/MultShiu.lean:783 | characters |
| `Salt.MR.euler_exp_bound` | Salt/MR/MultShiu.lean:937 | characters |
| `Salt.MR.hall_tenenbaum_euler` | Salt/MR/MultShiu.lean:1037 | characters |
| `Salt.MR.euler_exp_bound_shifted` | Salt/MR/MultShiu.lean:1094 | characters |
| `Salt.MR.smooth_rough_split` | Salt/MR/MultShiu.lean:1280 | characters |
| `Salt.MR.mult_shiu_MS_A` | Salt/MR/MultShiu.lean:1427 | characters |
| `Salt.MR.ms_b_rough_factor` | Salt/MR/MultShiu.lean:1705 | characters |
| `Salt.MR.mult_shiu_MS_B` | Salt/MR/MultShiu.lean:2209 | characters |
| `Salt.MR.mult_shiu_MS_EXIT` | Salt/MR/MultShiu.lean:2444 | characters |
| `Salt.MR.spoly_mul` | Salt/MR/MultShiuBridge.lean:91 | characters |
| `Salt.MR.ramQ_eq_spoly_bounded` | Salt/MR/MultShiuBridge.lean:182 | characters |
| `Salt.MR.multShiuCoeff_support_low` | Salt/MR/MultShiuBridge.lean:290 | characters |
| `Salt.MR.multShiuCoeff_support_high` | Salt/MR/MultShiuBridge.lean:304 | characters |
| `Salt.MR.ramQ_pow_mul_ramR_eq_spoly` | Salt/MR/MultShiuBridge.lean:321 | characters |
| `Salt.MR.af_mul_oneAf_apply` | Salt/MR/MultShiuBridge.lean:371 | characters |
| `Salt.MR.norm_af_mul_le` | Salt/MR/MultShiuBridge.lean:386 | characters |
| `Salt.MR.norm_multShiuCoeff_le` | Salt/MR/MultShiuBridge.lean:454 | characters |
| `Salt.MR.blockPrimeAf_pow_bound` | Salt/MR/MultShiuBridge.lean:548 | characters |
| `Salt.MR.maj_le_factorial_blockDiv` | Salt/MR/MultShiuBridge.lean:619 | characters |
| `Salt.MR.coeff_bound_factorial_blockDiv` | Salt/MR/MultShiuBridge.lean:642 | characters |
| `Salt.MR.multShiu_moment` | Salt/MR/MultShiuBridge.lean:659 | characters |
| `Salt.MR.ramQblock_subset_dyadic_block` | Salt/MR/MultShiuBridge.lean:703 | characters |
| `Salt.MR.ramRrange_ceil_bot_le` | Salt/MR/MultShiuBridge.lean:731 | characters |
| `Salt.MR.multShiu_moment_pinned` | Salt/MR/MultShiuBridge.lean:742 | characters |
| `Salt.MR.loglog_height_le` | Salt/MR/NonPret.lean:65 | characters |
| `Salt.MR.lambda_nonpret_of_bridge` | Salt/MR/NonPret.lean:114 | zeros, characters |
| `Salt.MR.log_norm_zeta_eq_re_tsum` | Salt/MR/NonPret.lean:194 | zeros, characters |
| `Salt.MR.lambda_nonpret` | Salt/MR/NonPretClose.lean:49 | characters |
| `Salt.MR.shiu_moment_sq_bounded` | Salt/MR/NumeralCt.lean:61 | characters |
| `Salt.MR.lemma13_moment_bounded` | Salt/MR/NumeralCt.lean:202 | characters |
| `Salt.SW.zero_free_region_real_bounded` | Salt/MR/NumeralKq.lean:194 | characters |
| `Salt.SW.zero_free_region_all'_bounded` | Salt/MR/NumeralKq.lean:450 | characters |
| `Salt.MR.twisted_rect_zero_free_siegel_bounded` | Salt/MR/NumeralKq.lean:502 | characters |
| `Salt.MR.one_line_pow_growth` | Salt/MR/OneLinePowGrowth.lean:324 | zeros, characters |
| `Salt.MR.perron_trunc_trivial` | Salt/MR/ParsevalAsm.lean:118 | characters |
| `Salt.MR.perron_trunc_min` | Salt/MR/ParsevalAsm.lean:189 | characters |
| `Salt.MR.Aperron_representation` | Salt/MR/ParsevalAsm.lean:296 | characters |
| `Salt.MR.sv_average_identity` | Salt/MR/ParsevalSL.lean:101 | characters |
| `Salt.MR.lpoly_mean_sq_bound` | Salt/MR/ParsevalSL.lean:145 | characters |
| `Salt.MR.vtail_single_mean_sq_bound` | Salt/MR/ParsevalSingle.lean:161 | characters |
| `Salt.MR.vtail_single_meansq_damped` | Salt/MR/ParsevalSingle.lean:199 | characters |
| `Salt.MR.vtail_single_meansq_kernel` | Salt/MR/ParsevalSingle.lean:433 | characters |
| `Salt.MR.vtail_single_meansq_kernel_neg` | Salt/MR/ParsevalSingle.lean:491 | characters |
| `Salt.MR.contour_single_h_kernel` | Salt/MR/ParsevalSingle.lean:663 | characters |
| `Salt.MR.perron_gap_single_le_gapMaj` | Salt/MR/ParsevalSingle.lean:815 | characters |
| `Salt.MR.parseval_single_h` | Salt/MR/ParsevalSingle.lean:876 | characters |
| `Salt.MR.zone_sum_collapsed_wide` | Salt/MR/PerronLimit.lean:237 | characters |
| `Salt.MR.Aperron_short_interval_collapsed_wide` | Salt/MR/PerronLimit.lean:324 | characters |
| `Salt.MR.lemma14_shortInterval_concrete` | Salt/MR/PerronLimit.lean:444 | characters |
| `Salt.MR.Aperron_error_le_of_T` | Salt/MR/PerronLimit.lean:530 | characters |
| `Salt.MR.Aperron_tendsto` | Salt/MR/PerronLimit.lean:562 | characters |
| `Salt.MR.perron_gap_tendsto` | Salt/MR/PerronLimit.lean:663 | characters |
| `Salt.MR.zone_min_sum_split` | Salt/MR/PerronMeanSq.lean:304 | characters |
| `Salt.MR.gapMaj_meansq_le` | Salt/MR/PerronMeanSq.lean:709 | characters |
| `Salt.MR.gapMaj_meansq_sqrt` | Salt/MR/PerronMeanSq.lean:831 | characters |
| `Salt.MR.lemma14_shortInterval_meansq` | Salt/MR/PerronMeanSq.lean:914 | characters |
| `Salt.MR.lemma14_shortInterval_meansq_concrete` | Salt/MR/PerronMeanSq.lean:1045 | characters |
| `Salt.MR.sv_smooth_kernel_bound` | Salt/MR/PerronSharp.lean:120 | characters |
| `Salt.MR.sharp_kernel_factor` | Salt/MR/PerronSharp.lean:155 | characters |
| `Salt.MR.perron_trunc` | Salt/MR/PerronTrunc.lean:389 | characters |
| `Salt.MR.log_ratio_ge` | Salt/MR/PerronZones.lean:50 | characters |
| `Salt.MR.harmonic_zone_bound` | Salt/MR/PerronZones.lean:92 | characters |
| `Salt.MR.perron_sum_error_collapsed` | Salt/MR/PerronZones.lean:442 | characters |
| `Salt.MR.log_le_rpow_fifth` | Salt/MR/PinFamily.lean:122 | characters |
| `Salt.MR.pin2_basic` | Salt/MR/PinFamily.lean:205 | characters |
| `Salt.MR.width_pin_gates_pin2` | Salt/MR/PinFamily.lean:285 | characters |
| `Salt.MR.width_pin_gate_bandwidth_fails_pin2` | Salt/MR/PinFamily.lean:319 | characters |
| `Salt.MR.prop21_uniform_at_scale_pin2` | Salt/MR/PinFamily.lean:401 | characters |
| `Salt.MR.far_window_mass_le2` | Salt/MR/PinFamily.lean:524 | characters |
| `Salt.MR.far_kernel_bound_T2` | Salt/MR/PinFamily.lean:562 | characters |
| `Salt.MR.far_kernel_bound_star2` | Salt/MR/PinFamily.lean:620 | characters |
| `Salt.MR.two_mul_pow_four_le_ypin2` | Salt/MR/PinFamily.lean:636 | characters |
| `Salt.MR.far_kfar_star2_le` | Salt/MR/PinFamily.lean:680 | characters |
| `Salt.MR.hfar_star2` | Salt/MR/PinFamily.lean:847 | characters |
| `Salt.MR.joint_supF_pin_at2` | Salt/MR/PinFamily.lean:933 | characters |
| `Salt.MR.far_supF_bound2` | Salt/MR/PinFamily.lean:989 | characters |
| `Salt.MR.log_Tstar2_self` | Salt/MR/PinFamily.lean:1033 | characters |
| `Salt.MR.farErr34_local_closes_of_gate` | Salt/MR/PinFamily.lean:1115 | characters |
| `Salt.MR.three_twentieths_gap` | Salt/MR/PinFamily.lean:1209 | characters |
| `Salt.MR.farErr34_local_closes` | Salt/MR/PinFamily.lean:1231 | characters |
| `Salt.MR.E_slot_pin2_le` | Salt/MR/PinFamily.lean:1268 | characters |
| `Salt.MR.E_slot_pin2_closes` | Salt/MR/PinFamily.lean:1289 | characters |
| `Salt.MR.cofactor_Rbd34_assembled` | Salt/MR/PinFamily.lean:1321 | characters |
| `Salt.MR.pow_four_le_ypin2` | Salt/MR/PinFamily2.lean:113 | characters |
| `Salt.MR.width_pin_gates_pin2_old_A` | Salt/MR/PinFamily2.lean:129 | characters |
| `Salt.MR.width_pin_gates_pin2_at_pin` | Salt/MR/PinFamily2.lean:165 | characters |
| `Salt.MR.Tstar2_mono` | Salt/MR/PinFamily2.lean:192 | characters |
| `Salt.MR.seamGateRstar2_nonneg` | Salt/MR/PinFamily2.lean:219 | characters |
| `Salt.MR.seam_gate_star2_of_nonempty` | Salt/MR/PinFamily2.lean:236 | characters |
| `Salt.MR.exists_min_gate_star2` | Salt/MR/PinFamily2.lean:246 | characters |
| `Salt.MR.seam_gate_star2_package` | Salt/MR/PinFamily2.lean:255 | characters |
| `Salt.MR.joint_supF_pin_trunc2` | Salt/MR/PinFamily2.lean:360 | characters |
| `Salt.MR.caseAS2_nonneg` | Salt/MR/PinFamily2.lean:866 | characters |
| `Salt.MR.caseAS2_absorbs_E_slot` | Salt/MR/PinFamily2.lean:889 | characters |
| `Salt.MR.caseAS2_absorbs_E_slot_closes` | Salt/MR/PinFamily2.lean:902 | characters |
| `Salt.MR.sum_vonMangoldt_nonunit_le` | Salt/MR/PortAssembly.lean:97 | sieves, characters |
| `Salt.MR.window_lambda_support` | Salt/MR/PortAssembly.lean:152 | sieves, characters |
| `Salt.MR.summable_window_lambda_chi` | Salt/MR/PortAssembly.lean:163 | sieves, characters |
| `Salt.MR.norm_principal_sub_untwisted_le` | Salt/MR/PortAssembly.lean:172 | sieves, characters |
| `Salt.MR.error_double_row_gen` | Salt/MR/PortAssembly.lean:273 | characters |
| `Salt.MR.pair_phase_conj` | Salt/MR/PortAssembly.lean:419 | characters |
| `Salt.MR.conj_pairMatrix` | Salt/MR/PortAssembly.lean:569 | characters |
| `Salt.MR.primal_of_dual_pair` | Salt/MR/PortAssembly.lean:579 | characters |
| `Salt.MR.loglog5_le` | Salt/MR/PortAssembly.lean:620 | characters |
| `Salt.MR.D4_5T1_le_D4` | Salt/MR/PortAssembly.lean:640 | characters |
| `Salt.MR.D5_5T1_le` | Salt/MR/PortAssembly.lean:676 | characters |
| `Salt.MR.natLog2_floor_le_sqrt` | Salt/MR/PortAssembly.lean:716 | characters |
| `Salt.MR.absorb_exp_term` | Salt/MR/PortAssembly.lean:781 | characters |
| `Salt.MR.siegel_real_carve` | Salt/MR/PortAssembly.lean:1180 | characters |
| `Salt.MR.twisted_rect_zero_free_siegel` | Salt/MR/PortAssembly.lean:1281 | characters |
| `Salt.MR.xiCarveWidth_of_siegel` | Salt/MR/PortClose.lean:76 | characters |
| `Salt.MR.mmuChiRate_holds_gated` | Salt/MR/PortClose.lean:157 | characters |
| `Salt.MR.lambdaChiSummatory_holds_gated` | Salt/MR/PortClose.lean:163 | characters |
| `Salt.MR.halaszPrimesChi_pointwise_of_gates` | Salt/MR/PortClose.lean:230 | characters |
| `Salt.MR.usetChi_window_meansq_gated` | Salt/MR/PortClose.lean:386 | characters |
| `Salt.MR.gates_jointly_satisfiable` | Salt/MR/PortNonVacuous.lean:75 | characters |
| `Salt.MR.socket_nonvacuous` | Salt/MR/PortNonVacuous.lean:157 | characters |
| `Salt.MR.mmuChiRate_instantiated` | Salt/MR/PortNonVacuous.lean:176 | characters |
| `Salt.MR.smooth_euler_product` | Salt/MR/PretSupply.lean:217 | characters |
| `Salt.MR.head_dist_floor_gen` | Salt/MR/PretSupply.lean:306 | zeros, characters |
| `Salt.MR.supF_pret_pointwise` | Salt/MR/PretSupply.lean:354 | characters |
| `Salt.MR.supF_pret_majorant_sigma` | Salt/MR/PretSupply.lean:422 | characters |
| `Salt.MR.joint_sigma_integral` | Salt/MR/PretSupply.lean:481 | characters |
| `Salt.MR.pretentious_pointwise_triangle` | Salt/MR/PretentiousTriangle.lean:100 | characters |
| `Salt.MR.pretDist_triangle` | Salt/MR/PretentiousTriangle.lean:172 | characters |
| `Salt.MR.dist_mul_half` | Salt/MR/PretentiousTriangle.lean:213 | characters |
| `Salt.MR.mertens_first_upper` | Salt/MR/PrimeSigmaShift.lean:46 | characters |
| `Salt.MR.sigma_shift` | Salt/MR/PrimeSigmaShift.lean:95 | characters |
| `Salt.MR.euler_osc_truncation` | Salt/MR/PrimeSigmaShift.lean:242 | characters |
| `Salt.MR.cpeel_le_two` | Salt/MR/PrimeSigmaShift.lean:307 | characters |
| `Salt.MR.primeTailConst_le_27` | Salt/MR/PrimeTail.lean:62 | characters |
| `Salt.MR.prime_tail_shift` | Salt/MR/PrimeTail.lean:383 | characters |
| `Salt.MR.log_euler_osc_zeta_unconditional` | Salt/MR/PrimeTail.lean:417 | zeros, characters |
| `Salt.MR.euler_osc_bridge_unconditional` | Salt/MR/PrimeTail.lean:436 | characters |
| `Salt.MR.expEM_le_of_floor_corrected` | Salt/MR/Prop1Assembly.lean:93 | characters |
| `Salt.MR.T1_pointwise_decay_corrected` | Salt/MR/Prop1Assembly.lean:135 | characters |
| `Salt.MR.T1_decay_corrected_fgJ` | Salt/MR/Prop1Assembly.lean:171 | characters |
| `Salt.MR.prop_A3'_assembly` | Salt/MR/Prop1Assembly.lean:254 | characters |
| `Salt.MR.moment_core_bound_shifted` | Salt/MR/Prop1Assembly.lean:316 | characters |
| `Salt.MR.prop_A3_T1_row_moment` | Salt/MR/Prop1Assembly.lean:396 | characters |
| `Salt.MR.prop_A3_T1_row_moment_polyT` | Salt/MR/Prop1Assembly.lean:558 | characters |
| `Salt.MR.prop_A3_T1_row_moment_le` | Salt/MR/Prop1Assembly.lean:628 | characters |
| `Salt.MR.prop21_unconditional_uniform` | Salt/MR/Prop21Uniform.lean:383 | characters |
| `Salt.MR.prop21_uniform_at_scale` | Salt/MR/Prop21Uniform.lean:468 | characters |
| `Salt.MR.dist_split_A4_frozen` | Salt/MR/PropA3Core.lean:172 | characters |
| `Salt.MR.T1_pointwise_decay` | Salt/MR/PropA3Core.lean:330 | characters |
| `Salt.MR.center_dist_floor` | Salt/MR/RHSGrade.lean:187 | characters |
| `Salt.MR.crossKer_sharp_sigma_bound` | Salt/MR/RHSGrade.lean:363 | characters |
| `Salt.MR.rhs_grade_at_scale` | Salt/MR/RHSGrade.lean:672 | characters |
| `Salt.MR.joint_supF_pinC` | Salt/MR/RHSGradeC.lean:110 | characters |
| `Salt.MR.ramP2coeffEndMR_chiBar` | Salt/MR/RamErrWS.lean:116 | characters |
| `Salt.MR.ramRrange_subset_Icc_sharp` | Salt/MR/RamRAdapter.lean:112 | characters |
| `Salt.MR.norm_ramRcoeff_le_one` | Salt/MR/RamRAdapter.lean:134 | characters |
| `Salt.MR.norm_ramRcoeff_cterm_le` | Salt/MR/RamRAdapter.lean:147 | characters |
| `Salt.MR.ramR_split_top` | Salt/MR/RamRAdapter.lean:164 | characters |
| `Salt.MR.ramRtop_card_le_two` | Salt/MR/RamRAdapter.lean:201 | characters |
| `Salt.MR.norm_ramRtop_le` | Salt/MR/RamRAdapter.lean:219 | characters |
| `Salt.MR.ramR_abel_sup` | Salt/MR/RamRAdapter.lean:267 | characters |
| `Salt.MR.ramR_abel_window_floor` | Salt/MR/RamRAdapter.lean:304 | characters |
| `Salt.MR.inv_blockOmega_succ_eq_integral` | Salt/MR/RamWeight.lean:72 | characters |
| `Salt.MR.blockOmega_pow_mul_coprime` | Salt/MR/RamWeight.lean:95 | characters |
| `Salt.MR.gxDatum_norm_le_one` | Salt/MR/RamWeight.lean:108 | characters |
| `Salt.MR.ellLin_gxDatum` | Salt/MR/RamWeight.lean:143 | characters |
| `Salt.MR.ramR_norm_le_of_damp_le` | Salt/MR/RamWeight.lean:202 | characters |
| `Salt.MR.ramRdamp_eq_spoly` | Salt/MR/RamWeight.lean:214 | characters |
| `Salt.MR.ramRdamp_ellLin` | Salt/MR/RamWeight.lean:228 | characters |
| `Salt.MR.sum_blockWindowPrimes_le` | Salt/MR/RamWeight.lean:254 | characters |
| `Salt.MR.gxDatum_pretDistSq_ge` | Salt/MR/RamWeight.lean:270 | characters |
| `Salt.MR.gxDatum_pretDistSq_ge_one` | Salt/MR/RamWeight.lean:320 | characters |
| `Salt.MR.gxDatum_pretDistSq_costwist` | Salt/MR/RamWeight.lean:332 | characters |
| `Salt.MR.ramare_decomp_pm` | Salt/MR/RamareDpoly.lean:55 | characters |
| `Salt.MR.spoly_ramare_eq16` | Salt/MR/RamareDpoly.lean:143 | characters |
| `Salt.MR.seam_sum_identity` | Salt/MR/RamareErr.lean:107 | characters |
| `Salt.MR.ramWindowErr_moment_sharp` | Salt/MR/RamareErr.lean:573 | characters |
| `Salt.MR.ramWindowErr_moment_grade` | Salt/MR/RamareErr.lean:594 | characters |
| `Salt.MR.lemma12_meansq_sharp` | Salt/MR/RamareErr.lean:648 | characters |
| `Salt.MR.lemma12_meansq_sharp_blockSupport` | Salt/MR/RamareErr.lean:704 | characters |
| `Salt.MR.seam_sum_identity_mr` | Salt/MR/RamareErr.lean:761 | characters |
| `Salt.MR.spoly_ramare_split_mr` | Salt/MR/RamareMR.lean:548 | characters |
| `Salt.MR.lemma12_meansq_mr` | Salt/MR/RamareMR.lean:804 | characters |
| `Salt.MR.lemma12_meansq_mr_blockSupport` | Salt/MR/RamareMR.lean:832 | characters |
| `Salt.MR.lemma12_meansq_mr_consume` | Salt/MR/RamareMR.lean:907 | characters |
| `Salt.MR.sum_inv_primeBand_le` | Salt/MR/RamareMassTail.lean:104 | characters |
| `Salt.MR.divisorRpow_prime_pow_le` | Salt/MR/RamareMassTail.lean:181 | characters |
| `Salt.MR.windowSmooth_rpow_sum_le` | Salt/MR/RamareMassTail.lean:227 | characters |
| `Salt.MR.prod_band_geom_one_le` | Salt/MR/RamareMassTail.lean:298 | characters |
| `Salt.MR.ramTailWeight_mass_le` | Salt/MR/RamareMassTail.lean:376 | characters |
| `Salt.MR.windowMassConst_eq_ratio_rpow` | Salt/MR/RamareMassTail.lean:386 | characters |
| `Salt.MR.loglog_calQK_sub_calP` | Salt/MR/RamareMassTail.lean:408 | characters |
| `Salt.MR.ramTailWeight_mass_door` | Salt/MR/RamareMassTail.lean:429 | characters |
| `Salt.MR.prod_band_geom_shift_le` | Salt/MR/RamareMassTail.lean:465 | characters |
| `Salt.MR.ramTailWeight_tail_le` | Salt/MR/RamareMassTail.lean:582 | characters |
| `Salt.MR.ramTailWeight_tail_calibrated` | Salt/MR/RamareMassTail.lean:602 | characters |
| `Salt.MR.ramTailWeight_htail_door` | Salt/MR/RamareMassTail.lean:660 | characters |
| `Salt.MR.ramP2corrEndMR_eq_spoly` | Salt/MR/RamareP2End.lean:78 | characters |
| `Salt.MR.ramP2corrEndMR_moment` | Salt/MR/RamareP2End.lean:107 | characters |
| `Salt.MR.spoly_ram_decomp` | Salt/MR/RamareWindows.lean:93 | characters |
| `Salt.MR.lemma12_meansq_of_windowErr` | Salt/MR/RamareWindows.lean:129 | characters |
| `Salt.MR.window_card_le` | Salt/MR/RamareWindows.lean:317 | characters |
| `Salt.MR.clean_dyadic_sub_main` | Salt/MR/RamareWindows.lean:373 | characters |
| `Salt.MR.ramErr_window_decomp` | Salt/MR/RamareWindows.lean:392 | characters |
| `Salt.MR.ramCopTail_moment` | Salt/MR/RamareWindows.lean:420 | characters |
| `Salt.MR.ramP2corr_moment` | Salt/MR/RamareWindows.lean:565 | characters |
| `Salt.MR.lemma12_meansq` | Salt/MR/RamareWindows.lean:671 | characters |
| `Salt.MR.lemma12_meansq_pretty` | Salt/MR/RamareWindows.lean:723 | characters |
| `Salt.MR.rampSliverMass_eq_zero_of_gap` | Salt/MR/RampSliver.lean:104 | characters |
| `Salt.MR.ramp_sliver_bound` | Salt/MR/RampSliver.lean:138 | sieves, characters |
| `Salt.MR.s5_spec` | Salt/MR/RegimeHead.lean:168 | characters |
| `Salt.MR.s5_spec_of_le` | Salt/MR/RegimeHead.lean:177 | characters |
| `Salt.MR.anchor_le_gJoin` | Salt/MR/RegimeHead.lean:220 | sieves, characters |
| `Salt.MR.s5x0_le_gJoin` | Salt/MR/RegimeHead.lean:226 | sieves, characters |
| `Salt.MR.carm_le_gJoin` | Salt/MR/RegimeHead.lean:231 | sieves, characters |
| `Salt.MR.mrThreshold_le_gJoin` | Salt/MR/RegimeHead.lean:237 | characters |
| `Salt.MR.omega_le_gJoin` | Salt/MR/RegimeHead.lean:244 | characters |
| `Salt.MR.gJoin_pos` | Salt/MR/RegimeHead.lean:253 | characters |
| `Salt.MR.chowlaRegime_exists_param_head` | Salt/MR/RegimeHead.lean:271 | characters |
| `Salt.MR.chowlaRegime_exists_param_of_head` | Salt/MR/RegimeHead.lean:282 | characters |
| `Salt.MR.chowlaRegime_exists_param_head_gJoin` | Salt/MR/RegimeHead.lean:292 | characters |
| `Salt.MR.s5x0_le_of_gJoin` | Salt/MR/RegimeHead.lean:302 | sieves, characters |
| `Salt.MR.s5_at_regime` | Salt/MR/RegimeHead.lean:312 | sieves, characters |
| `Salt.MR.mrThreshold_le_x` | Salt/MR/RegimeHead.lean:322 | characters |
| `Salt.MR.heps_arm_of_epsFloor` | Salt/MR/RegimeHead.lean:340 | characters |
| `Salt.MR.regime_head_W_headroom` | Salt/MR/RegimeHead.lean:363 | characters |
| `Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist` | Salt/MR/RegisterCompose.lean:164 | characters |
| `Salt.MR.logChowla2_ineffective_v6` | Salt/MR/RegisterCompose.lean:345 | characters |
| `Salt.MR.s16cof_exit_decay` | Salt/MR/RegisterInhabit.lean:102 | characters |
| `Salt.MR.cofk_ramI_bot_mem` | Salt/MR/RegisterInhabit.lean:150 | characters |
| `Salt.MR.cofkL_bulk_infeasible` | Salt/MR/RegisterInhabit.lean:209 | characters |
| `Salt.MR.cofkL_bulk_infeasible_loglog` | Salt/MR/RegisterInhabit.lean:229 | characters |
| `Salt.MR.cofk_sqrt_le_ramRbot` | Salt/MR/RegisterInhabit.lean:294 | characters |
| `Salt.MR.cofk_ballQuarter_at_band` | Salt/MR/RegisterInhabit.lean:349 | characters |
| `Salt.MR.cofk_wideThreshold_at_band` | Salt/MR/RegisterInhabit.lean:372 | characters |
| `Salt.MR.cofk_seamRad_at_band` | Salt/MR/RegisterInhabit.lean:391 | characters |
| `Salt.MR.cofk_descent_at_band` | Salt/MR/RegisterInhabit.lean:428 | characters |
| `Salt.MR.cofk_dilation_price` | Salt/MR/RegisterInhabit.lean:494 | characters |
| `Salt.MR.cofkRSconst_pos` | Salt/MR/RegisterRepair.lean:109 | characters |
| `Salt.MR.cofkRConst_pos` | Salt/MR/RegisterRepair.lean:119 | characters |
| `Salt.MR.cofkR_band_log_lower` | Salt/MR/RegisterRepair.lean:129 | characters |
| `Salt.MR.cofkR_two_rpow_three_fifths` | Salt/MR/RegisterRepair.lean:182 | characters |
| `Salt.MR.cofkR_Tstar2_le` | Salt/MR/RegisterRepair.lean:193 | characters |
| `Salt.MR.cofkR_box_of_le` | Salt/MR/RegisterRepair.lean:204 | characters |
| `Salt.MR.cofkR_descent_crude` | Salt/MR/RegisterRepair.lean:220 | characters |
| `Salt.MR.cofkR_mfl_nonneg` | Salt/MR/RegisterRepair.lean:249 | characters |
| `Salt.MR.cofkR_window_lower` | Salt/MR/RegisterRepair.lean:310 | characters |
| `Salt.MR.cofkR_caseASwide_priced` | Salt/MR/RegisterRepair.lean:356 | characters |
| `Salt.MR.cofkR_farSup_priced` | Salt/MR/RegisterRepair.lean:436 | characters |
| `Salt.MR.cofkR_cofactorSupply_L_gk` | Salt/MR/RegisterRepair.lean:476 | characters |
| `Salt.MR.s16_baseScaleCap96_L_of_xwindow` | Salt/MR/RegisterSupply.lean:131 | characters |
| `Salt.MR.s16_baseScaleCap96_L_of_x_small` | Salt/MR/RegisterSupply.lean:175 | characters |
| `Salt.MR.cofkL_logQK_eq` | Salt/MR/RegisterSupply.lean:211 | characters |
| `Salt.MR.cofkL_debit_bound` | Salt/MR/RegisterSupply.lean:285 | characters |
| `Salt.MR.hall_tenenbaum_core_two` | Salt/MR/Renormalise.lean:94 | characters |
| `Salt.MR.euler_exp_bound_two` | Salt/MR/Renormalise.lean:182 | characters |
| `Salt.MR.ht_tail_ratio` | Salt/MR/Renormalise.lean:292 | characters |
| `Salt.MR.renormalise` | Salt/MR/Renormalise.lean:1003 | characters |
| `Salt.MR.renormalise_shifted` | Salt/MR/Renormalise.lean:1172 | characters |
| `Salt.MR.cs_closed_form_ge_exp_neg_hundred` | Salt/MR/RiderTrace.lean:132 | characters |
| `Salt.MR.arc36_of_floor` | Salt/MR/S11Arc36.lean:51 | characters |
| `Salt.MR.arc36_of_floor_h` | Salt/MR/S11Arc36.lean:98 | characters |
| `Salt.MR.arc36_of_regime` | Salt/MR/S11Arc36.lean:141 | characters |
| `Salt.MR.arc36_of_floor_h_14` | Salt/MR/S11Arc36.lean:162 | characters |
| `Salt.MR.memSCoeff_seamCoefWS_punct_gen_U` | Salt/MR/S11CoefWS.lean:54 | characters |
| `Salt.MR.doorCoeffU_seamCoefWS_punct_H` | Salt/MR/S11CoefWS.lean:80 | characters |
| `Salt.MR.doorRowZeroBase_coefWS_witness` | Salt/MR/S11CoefWS.lean:102 | characters |
| `Salt.MR.norm_doorPunctCoeffU_le_one` | Salt/MR/S11CoefWS.lean:112 | characters |
| `Salt.MR.m4_exit_socket_split_45` | Salt/MR/S11Exit45.lean:69 | characters |
| `Salt.MR.tower_conjunct_45_le_five` | Salt/MR/S11Exit45.lean:94 | characters |
| `Salt.MR.m4_exit_socket_split_sq` | Salt/MR/S11ExitL2.lean:81 | characters |
| `Salt.MR.m4_exit_socket_split_sq_arc` | Salt/MR/S11ExitL2.lean:121 | sieves, characters |
| `Salt.MR.m4_exit_socket_split_sq_arc_at_mrt_floors` | Salt/MR/S11ExitL2.lean:189 | sieves, characters |
| `Salt.MR.m4_exit_socket_split_sq_arc_at_mrt_floors_34` | Salt/MR/S11ExitL2.lean:231 | sieves, characters |
| `Salt.MR.s11_windowMassConst_door_le_L` | Salt/MR/S11HoistLinear.lean:59 | characters |
| `Salt.MR.regime_Hfloor_of_loglogFloor50` | Salt/MR/S12Compose.lean:195 | characters |
| `Salt.MR.s12DeltaSock_pos` | Salt/MR/S12Compose.lean:218 | characters |
| `Salt.MR.s13_band_log_calP_one_L` | Salt/MR/S13BandCapLinear.lean:34 | characters |
| `Salt.MR.s13_band_log_calP_one_L_gk` | Salt/MR/S13BandCapLinear.lean:39 | characters |
| `Salt.MR.s13_band_log_calQK_two_L` | Salt/MR/S13BandCapLinear.lean:44 | characters |
| `Salt.MR.s13_band_log_calQK_two_L_gk` | Salt/MR/S13BandCapLinear.lean:54 | characters |
| `Salt.MR.s13_band_loglog_calP_one_L` | Salt/MR/S13BandCapLinear.lean:69 | characters |
| `Salt.MR.s13_band_loglog_calP_one_L_gk` | Salt/MR/S13BandCapLinear.lean:86 | characters |
| `Salt.MR.s13_band_log_calQK_two_ge_L` | Salt/MR/S13BandCapLinear.lean:93 | characters |
| `Salt.MR.s13_band_log_calQK_two_ge_L_gk` | Salt/MR/S13BandCapLinear.lean:107 | characters |
| `Salt.MR.capfloor_one_lt_QK2_L` | Salt/MR/S13BandCapLinear.lean:143 | characters |
| `Salt.MR.capfloor_one_lt_QK2_L_gk` | Salt/MR/S13BandCapLinear.lean:148 | characters |
| `Salt.MR.capfloor_logH_le_third_sqrt` | Salt/MR/S13CapFloor.lean:768 | characters |
| `Salt.MR.s16_budget_field_L_gk_96` | Salt/MR/S13CapGateLinear.lean:663 | characters |
| `Salt.MR.capeps_master_60` | Salt/MR/S13CapGateLinearLH.lean:72 | characters |
| `Salt.MR.capeps_expbound_60` | Salt/MR/S13CapGateLinearLH.lean:99 | characters |
| `Salt.MR.capeps_bigexp_60` | Salt/MR/S13CapGateLinearLH.lean:117 | characters |
| `Salt.MR.capeps_Pbig_h` | Salt/MR/S13CapGateLinearLH.lean:144 | characters |
| `Salt.MR.capfloor_lam_core_h` | Salt/MR/S13CapGateLinearLH.lean:179 | characters |
| `Salt.MR.capfloor_floor3_numeric_h` | Salt/MR/S13CapGateLinearLH.lean:187 | characters |
| `Salt.MR.h_le_exp_seven` | Salt/MR/S13CapGateLinearLH.lean:1165 | characters |
| `Salt.MR.h_le_exp_fourteen` | Salt/MR/S13CapGateLinearLH.lean:1182 | characters |
| `Salt.MR.capeps_row_phi_h` | Salt/MR/S13CapGateLinearLH.lean:1189 | characters |
| `Salt.MR.capeps_row_tail_h` | Salt/MR/S13CapGateLinearLH.lean:1231 | characters |
| `Salt.MR.capeps_row_p2_h` | Salt/MR/S13CapGateLinearLH.lean:1338 | characters |
| `Salt.MR.s15_crossing_supplied_LH_gk_ceiling` | Salt/MR/S13CapGateLinearLH.lean:1947 | characters |
| `Salt.MR.capeps_master_63` | Salt/MR/S13CapGateLinearLH.lean:2004 | characters |
| `Salt.MR.capeps_expbound_63` | Salt/MR/S13CapGateLinearLH.lean:2032 | characters |
| `Salt.MR.capeps_row_phi_h_14` | Salt/MR/S13CapGateLinearLH.lean:2053 | characters |
| `Salt.MR.capeps_row_tail_h_14` | Salt/MR/S13CapGateLinearLH.lean:2101 | characters |
| `Salt.MR.capeps_Pbig_h_e20` | Salt/MR/S13CapGateLinearLH.lean:2215 | characters |
| `Salt.MR.capfloor_lam_core_h_232` | Salt/MR/S13CapGateLinearLH.lean:2249 | characters |
| `Salt.MR.capfloor_floor3_numeric_h_10` | Salt/MR/S13CapGateLinearLH.lean:2257 | characters |
| `Salt.MR.capeps_row_p2_h_b9` | Salt/MR/S13CapGateLinearLH.lean:2408 | characters |
| `Salt.MR.s13Delta0_ge` | Salt/MR/S13FramesA.lean:71 | characters |
| `Salt.MR.s13M_log` | Salt/MR/S13FramesA.lean:85 | characters |
| `Salt.MR.s13_b_floor_cert` | Salt/MR/S13FramesA.lean:98 | characters |
| `Salt.MR.s13_sieveBlockGate` | Salt/MR/S13FramesA.lean:145 | sieves, characters |
| `Salt.MR.s13_doorGates_of_arm` | Salt/MR/S13FramesA.lean:375 | characters |
| `Salt.MR.s13_endpoint_of_arm` | Salt/MR/S13FramesA.lean:414 | characters |
| `Salt.MR.s13_loglogHhi_le` | Salt/MR/S13FramesA.lean:450 | characters |
| `Salt.MR.s13_g2_jfloor` | Salt/MR/S13FramesA.lean:500 | characters |
| `Salt.MR.s13_gate8` | Salt/MR/S13FramesA.lean:524 | characters |
| `Salt.MR.s13_smallGradeFits` | Salt/MR/S13FramesA.lean:581 | characters |
| `Salt.MR.s13_doorRowZeroBase_five` | Salt/MR/S13FramesA.lean:761 | characters |
| `Salt.MR.s13GArm'_le` | Salt/MR/S13FramesA.lean:851 | characters |
| `Salt.MR.s13_doorGates_of_arm'` | Salt/MR/S13FramesA.lean:857 | characters |
| `Salt.MR.s13_endpoint_of_arm'` | Salt/MR/S13FramesA.lean:893 | characters |
| `Salt.MR.s13_log263_le_six` | Salt/MR/S13FramesA.lean:965 | characters |
| `Salt.MR.s13_MSelect_of_headroom` | Salt/MR/S13FramesA.lean:1030 | characters |
| `Salt.MR.s13_loglogHhi_le_tight` | Salt/MR/S13FramesA.lean:1094 | characters |
| `Salt.MR.memSCoeff_seamCoefWS_band_gen_U` | Salt/MR/S13FramesB.lean:142 | characters |
| `Salt.MR.doorCoeffU_seamCoefWS_band_H` | Salt/MR/S13FramesB.lean:170 | characters |
| `Salt.MR.theta293_pos_le_one` | Salt/MR/S13FramesB.lean:370 | characters |
| `Salt.MR.s13_H83_le` | Salt/MR/S13FramesB.lean:379 | characters |
| `Salt.MR.s13BlockFloor_le_L` | Salt/MR/S13FramesLinear.lean:61 | characters |
| `Salt.MR.s13_sieveBlockGate_gen` | Salt/MR/S13FramesLinear.lean:77 | sieves, characters |
| `Salt.MR.s13_sieveBlockGate_L` | Salt/MR/S13FramesLinear.lean:232 | sieves, characters |
| `Salt.MR.s13_sieveBlockGate_L_gk` | Salt/MR/S13FramesLinear.lean:237 | sieves, characters |
| `Salt.MR.s13_gate8_L` | Salt/MR/S13FramesLinear.lean:270 | characters |
| `Salt.MR.s13_gate8_L_gk` | Salt/MR/S13FramesLinear.lean:278 | characters |
| `Salt.MR.s13_doorRowZeroBase_five_L` | Salt/MR/S13FramesLinear.lean:331 | characters |
| `Salt.MR.s13_doorRowZeroBase_five_L_gk` | Salt/MR/S13FramesLinear.lean:342 | characters |
| `Salt.MR.s13_MSelect_L_of_headroom` | Salt/MR/S13FramesLinear.lean:451 | characters |
| `Salt.MR.s13_MSelect_L_of_headroom_gk` | Salt/MR/S13FramesLinear.lean:476 | characters |
| `Salt.MR.s13_winFit_of_halfWindow_gen` | Salt/MR/S13FramesLinear.lean:509 | characters |
| `Salt.MR.s13_MSelect'_L_of_headroom` | Salt/MR/S13FramesLinear.lean:652 | characters |
| `Salt.MR.s13_MSelect'_L_of_headroom_gk` | Salt/MR/S13FramesLinear.lean:679 | characters |
| `Salt.MR.s13_MSelect'_L_of_halfWindow` | Salt/MR/S13FramesLinear.lean:709 | characters |
| `Salt.MR.s13_MSelect'_L_of_halfWindow_gk` | Salt/MR/S13FramesLinear.lean:720 | characters |
| `Salt.MR.s13BlockExp_L_head` | Salt/MR/S15SelLinear.lean:75 | characters |
| `Salt.MR.s13BlockExp_L_le` | Salt/MR/S15SelLinear.lean:82 | characters |
| `Salt.MR.flat_exp_half_ge` | Salt/MR/S15SelLinear.lean:204 | characters |
| `Salt.MR.flat_exp_sq` | Salt/MR/S15SelLinear.lean:215 | characters |
| `Salt.MR.flat_exp_ge_quartic` | Salt/MR/S15SelLinear.lean:221 | characters |
| `Salt.MR.flatDoorM_le` | Salt/MR/S15SelLinear.lean:227 | characters |
| `Salt.MR.flatDoorM_ge` | Salt/MR/S15SelLinear.lean:230 | characters |
| `Salt.MR.flatDoorM_one_le` | Salt/MR/S15SelLinear.lean:236 | characters |
| `Salt.MR.s15_sel''_L_witness_flat` | Salt/MR/S15SelLinear.lean:267 | characters |
| `Salt.MR.s13BlockExp_L_gk_head` | Salt/MR/S15SelLinear.lean:495 | characters |
| `Salt.MR.s13BlockExp_L_gk_le` | Salt/MR/S15SelLinear.lean:503 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat` | Salt/MR/S15SelLinear.lean:550 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_b9` | Salt/MR/S15SelLinear.lean:727 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_b9` | Salt/MR/S15SelLinear.lean:936 | characters |
| `Salt.MR.flat_exp_ge_lin` | Salt/MR/S15SelLinearWide.lean:50 | characters |
| `Salt.MR.flat_gRows_line` | Salt/MR/S15SelLinearWide.lean:69 | characters |
| `Salt.MR.flat_anchor_line` | Salt/MR/S15SelLinearWide.lean:82 | characters |
| `Salt.MR.flat_half_line` | Salt/MR/S15SelLinearWide.lean:101 | characters |
| `Salt.MR.flat_gP1_line` | Salt/MR/S15SelLinearWide.lean:127 | characters |
| `Salt.MR.flat_lvl_line` | Salt/MR/S15SelLinearWide.lean:153 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_charge` | Salt/MR/S15SelLinearWide.lean:219 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_wide` | Salt/MR/S15SelLinearWide.lean:263 | characters |
| `Salt.MR.flat_blk_line_gk` | Salt/MR/S15SelLinearWide.lean:284 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_wide` | Salt/MR/S15SelLinearWide.lean:301 | characters |
| `Salt.MR.flatC_bracket` | Salt/MR/S15SelLinearWide.lean:325 | characters |
| `Salt.MR.flat_rpow_four_le` | Salt/MR/S15SelLinearWide.lean:333 | characters |
| `Salt.MR.flat_linear_joint_point` | Salt/MR/S15SelLinearWide.lean:369 | characters |
| `Salt.MR.s13BlockExp_le_L` | Salt/MR/S15SelLinearWide.lean:428 | characters |
| `Salt.MR.flatDoorM_natLog_le` | Salt/MR/S15SelLinearWide.lean:500 | characters |
| `Salt.MR.flat_landed_ladder_break` | Salt/MR/S15SelLinearWide.lean:528 | characters |
| `Salt.MR.flat_blk_line_gk_b9` | Salt/MR/S15SelLinearWide.lean:565 | characters |
| `Salt.MR.s16_audit_rho_ge_wide_h` | Salt/MR/S16Budget.lean:990 | characters |
| `Salt.MR.s16_audit_neglog_rho_le_wide_h` | Salt/MR/S16Budget.lean:1023 | characters |
| `Salt.MR.s16_audit_neglog_rho_le_417_h` | Salt/MR/S16Budget.lean:1043 | characters |
| `Salt.MR.flat_socket_uniform_ceiling` | Salt/MR/S16Compose.lean:205 | sieves, characters |
| `Salt.MR.s15_crossing_supplied_L_gk_ceiling` | Salt/MR/S16Compose.lean:960 | characters |
| `Salt.MR.logChowla2_ineffective_v3` | Salt/MR/S16Compose.lean:1112 | characters |
| `Salt.MR.s15_crossing_supplied_LH_gk_ceiling_sharpT0` | Salt/MR/S16ComposeLH.lean:2560 | characters |
| `Salt.MR.logChowla2_ineffective_v3_h` | Salt/MR/S16ComposeLH.lean:2718 | characters |
| `Salt.MR.s15_crossing_supplied_LH_gk_ceiling_sharpT0_khoist_csfree_kswin` | Salt/MR/S16ComposeLH.lean:3283 | characters |
| `Salt.MR.s15_crossing_supplied_LH_gk_ceiling_sharpT0_khoist_csfree_kswin_b9` | Salt/MR/S16ComposeLH.lean:3915 | characters |
| `Salt.MR.s16_bandLaneWinL_holdsU` | Salt/MR/S16ComposeV4.lean:93 | characters |
| `Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0` | Salt/MR/S16ComposeV4.lean:805 | characters |
| `Salt.MR.logChowla2_ineffective_v4` | Salt/MR/S16ComposeV4.lean:1002 | characters |
| `Salt.MR.s15_crossing_supplied_L_gk` | Salt/MR/S16FlatFinal.lean:65 | characters |
| `Salt.MR.budgetAFlat_spend` | Salt/MR/S16FlatTerminal.lean:75 | characters |
| `Salt.MR.flat_design_window_demand` | Salt/MR/S16FlatTerminal.lean:84 | characters |
| `Salt.MR.flatHead_budget_pair` | Salt/MR/S16FlatTerminal.lean:105 | characters |
| `Salt.MR.flat_window_forces_cD3` | Salt/MR/S16FlatTerminal.lean:120 | characters |
| `Salt.MR.flat_design_window_necessary` | Salt/MR/S16FlatTerminal.lean:155 | characters |
| `Salt.MR.flatCap_le_s15WitFloor2_forces_cD3` | Salt/MR/S16FlatTerminal.lean:188 | characters |
| `Salt.MR.flatWitFloor_arc` | Salt/MR/S16FlatTerminal.lean:206 | characters |
| `Salt.MR.flatWitFloor_ll` | Salt/MR/S16FlatTerminal.lean:210 | characters |
| `Salt.MR.flatCap_le_flatWitFloor` | Salt/MR/S16FlatTerminal.lean:218 | characters |
| `Salt.MR.flatWitFloor_design` | Salt/MR/S16FlatTerminal.lean:227 | characters |
| `Salt.MR.flatWitFloor_le_ceil_exp` | Salt/MR/S16FlatTerminal.lean:242 | characters |
| `Salt.MR.flat_base_in_s15_window` | Salt/MR/S16FlatTerminal.lean:267 | characters |
| `Salt.MR.s15_window_eq_cap_window` | Salt/MR/S16FlatTerminal.lean:275 | characters |
| `Salt.MR.flatCap_join_floor` | Salt/MR/S16FlatTerminal.lean:286 | characters |
| `Salt.MR.flatWitA_ge` | Salt/MR/S16FlatTerminal.lean:730 | characters |
| `Salt.MR.flatWitA_budget` | Salt/MR/S16FlatTerminal.lean:732 | characters |
| `Salt.MR.flatWitFloor_regime_exists` | Salt/MR/S16FlatTerminal.lean:738 | characters |
| `Salt.MR.s15w2_anchor_landed_margin` | Salt/MR/S16FlatTerminal.lean:751 | characters |
| `Salt.MR.s15w2_anchor_flat_break` | Salt/MR/S16FlatTerminal.lean:763 | characters |
| `Salt.MR.s15w2_gRows_flat_break` | Salt/MR/S16FlatTerminal.lean:769 | characters |
| `Salt.MR.s15w2_gRows_flat_doorL` | Salt/MR/S16FlatTerminal.lean:773 | characters |
| `Salt.MR.s11_grade_absorption'_L` | Salt/MR/S16FlatTerminalLinear.lean:330 | characters |
| `Salt.MR.s13_doorGates_of_arm'_L_gk` | Salt/MR/S16FlatTerminalLinear.lean:878 | characters |
| `Salt.MR.s13_g2_jfloor_gen` | Salt/MR/S16FlatTerminalLinear.lean:920 | characters |
| `Salt.MR.calQK_L_one_gk_eq` | Salt/MR/S16FlatTerminalLinear.lean:942 | characters |
| `Salt.MR.gRowsZeroGate'''_L_gk_of_budget` | Salt/MR/S16FlatTerminalLinear.lean:947 | characters |
| `Salt.MR.flat_arm_eps_le_h` | Salt/MR/S16FlatTerminalLinear.lean:1306 | characters |
| `Salt.MR.flat_arm_budget_le_h` | Salt/MR/S16FlatTerminalLinear.lean:1331 | characters |
| `Salt.MR.arc36_of_regime_h` | Salt/MR/S16FlatTerminalLinear.lean:1425 | characters |
| `Salt.MR.s13_g2_jfloor_of_MSelect'_L_gk_h` | Salt/MR/S16FlatTerminalLinear.lean:1474 | characters |
| `Salt.MR.flat_witFloor_eq_designBase_h` | Salt/MR/S16FlatTerminalLinear.lean:1497 | characters |
| `Salt.MR.flatWitFloor_log_ge` | Salt/MR/S16FlatTerminalLinear.lean:1600 | characters |
| `Salt.MR.flat_L_width_of_base_at_design` | Salt/MR/S16FlatTerminalLinear.lean:1759 | characters |
| `Salt.MR.flatWitFloor_loglog_ge_fifty` | Salt/MR/S16FlatTerminalLinear.lean:1880 | characters |
| `Salt.MR.flatDoorM_pos_at_162` | Salt/MR/S16FlatTerminalLinear.lean:1888 | characters |
| `Salt.MR.flat_L_regime_exists` | Salt/MR/S16FlatTerminalLinear.lean:1898 | characters |
| `Salt.MR.flat_linear_joint_point_at_162` | Salt/MR/S16FlatTerminalLinear.lean:1911 | characters |
| `Salt.MR.arc36_of_regime_h_14` | Salt/MR/S16FlatTerminalLinear.lean:2409 | characters |
| `Salt.MR.flat_arm_eps_le_h_b9` | Salt/MR/S16FlatTerminalLinear.lean:2457 | characters |
| `Salt.MR.flat_arm_budget_le_h_b9` | Salt/MR/S16FlatTerminalLinear.lean:2481 | characters |
| `Salt.MR.s13_g2_jfloor_of_MSelect'_L_gk_h_b9` | Salt/MR/S16FlatTerminalLinear.lean:2574 | characters |
| `Salt.MR.flat_witFloor_eq_designBase_h_b9` | Salt/MR/S16FlatTerminalLinear.lean:2602 | characters |
| `Salt.MR.hArcDen_nonneg` | Salt/MR/S16FlatTerminalLinearH.lean:81 | characters |
| `Salt.MR.arcDen_le_hArcDen` | Salt/MR/S16FlatTerminalLinearH.lean:85 | characters |
| `Salt.MR.one_le_hArcDen_of_regime` | Salt/MR/S16FlatTerminalLinearH.lean:92 | characters |
| `Salt.MR.one_le_hArcDen_of_cap` | Salt/MR/S16FlatTerminalLinearH.lean:98 | characters |
| `Salt.MR.one_le_of_hArcDen` | Salt/MR/S16FlatTerminalLinearH.lean:103 | characters |
| `Salt.MR.four_le_hArcDen_of_regime` | Salt/MR/S16FlatTerminalLinearH.lean:109 | characters |
| `Salt.MR.strataResidualH_one` | Salt/MR/S16FlatTerminalLinearH.lean:120 | characters |
| `Salt.MR.strataResidualH_eq` | Salt/MR/S16FlatTerminalLinearH.lean:125 | characters |
| `Salt.MR.strataResidualH_nonneg` | Salt/MR/S16FlatTerminalLinearH.lean:134 | characters |
| `Salt.MR.one_le_blockLenH` | Salt/MR/S16FlatTerminalLinearH.lean:149 | characters |
| `Salt.MR.blockLenH_le` | Salt/MR/S16FlatTerminalLinearH.lean:151 | characters |
| `Salt.MR.hArcDen_lt_floor_succ` | Salt/MR/S16FlatTerminalLinearH.lean:156 | characters |
| `Salt.MR.floor_succ_le_two_mul_h` | Salt/MR/S16FlatTerminalLinearH.lean:162 | characters |
| `Salt.MR.blockLenH_drift` | Salt/MR/S16FlatTerminalLinearH.lean:170 | characters |
| `Salt.MR.blockLenH_narrow` | Salt/MR/S16FlatTerminalLinearH.lean:201 | characters |
| `Salt.MR.blockLenH_arc_floor` | Salt/MR/S16FlatTerminalLinearH.lean:233 | characters |
| `Salt.MR.abs_mul_window_le_of_cap_block` | Salt/MR/S16FlatTerminalLinearH.lean:268 | characters |
| `Salt.MR.norm_absWindowSum_le_drift_blocked_Q` | Salt/MR/S16FlatTerminalLinearH.lean:284 | characters |
| `Salt.MR.norm_absWindowSum_sq_le_drift_blocked_Q` | Salt/MR/S16FlatTerminalLinearH.lean:312 | characters |
| `Salt.MR.m4_chiSummedFreeRow_trivialH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:426 | characters |
| `Salt.MR.m4ChiRowGradedH_big_L` | Salt/MR/S16FlatTerminalLinearH.lean:1672 | characters |
| `Salt.MR.m4ChiRowGradedH_small_L` | Salt/MR/S16FlatTerminalLinearH.lean:1675 | characters |
| `Salt.MR.m4ChiRowGradedH_an_L` | Salt/MR/S16FlatTerminalLinearH.lean:1680 | characters |
| `Salt.MR.m4_arith_rs_ceiling_met_rhoH_two` | Salt/MR/S16FlatTerminalLinearH.lean:1731 | characters |
| `Salt.MR.RSanDoorRhoH_le_RSanDoorRho` | Salt/MR/S16FlatTerminalLinearLH.lean:385 | characters |
| `Salt.MR.s13_gate8_L_gk_h` | Salt/MR/S16FlatTerminalLinearLH.lean:413 | characters |
| `Salt.MR.s13_smallGradeFits_h` | Salt/MR/S16FlatTerminalLinearLH.lean:634 | characters |
| `Salt.MR.s13_winFit_h_of_halfWindow_gen` | Salt/MR/S16FlatTerminalLinearLH.lean:828 | characters |
| `Salt.MR.s13_smallGradeFits_of_halfWindow_L_gk_h` | Salt/MR/S16FlatTerminalLinearLH.lean:891 | characters |
| `Salt.MR.s13_gate8_L_gk_h_b9` | Salt/MR/S16FlatTerminalLinearLH.lean:1163 | characters |
| `Salt.MR.s13_smallGradeFits_h_b9` | Salt/MR/S16FlatTerminalLinearLH.lean:1201 | characters |
| `Salt.MR.s13_winFit_h_of_halfWindow_gen_b9` | Salt/MR/S16FlatTerminalLinearLH.lean:1377 | characters |
| `Salt.MR.s13_smallGradeFits_of_halfWindow_L_gk_h_b9` | Salt/MR/S16FlatTerminalLinearLH.lean:1434 | characters |
| `Salt.MR.RSanDoorRhoH_one` | Salt/MR/S16ProducersH.lean:74 | characters |
| `Salt.MR.RSanDoorRhoH_nonneg` | Salt/MR/S16ProducersH.lean:77 | characters |
| `Salt.MR.one_le_strataResidualH` | Salt/MR/S16ProducersH.lean:81 | characters |
| `Salt.MR.three_le_of_one_lt_log` | Salt/MR/S16ProducersH.lean:88 | characters |
| `Salt.MR.one_le_hArcDen_of_loglog` | Salt/MR/S16ProducersH.lean:100 | characters |
| `Salt.MR.m4_arith_rs_ceiling_met_rhoH` | Salt/MR/S16ProducersH.lean:114 | characters |
| `Salt.MR.m4_arith_rs_ceiling_met_of_deltaH` | Salt/MR/S16ProducersH.lean:139 | characters |
| `Salt.MR.hArcDen_mul_strataResidualH_sq_le` | Salt/MR/S16ProducersH.lean:155 | characters |
| `Salt.MR.s15ArmH_one` | Salt/MR/S16ProducersH.lean:710 | characters |
| `Salt.MR.s15ArmH_demoted` | Salt/MR/S16ProducersH.lean:715 | characters |
| `Salt.MR.s15ArmH_rho` | Salt/MR/S16ProducersH.lean:720 | characters |
| `Salt.MR.gArmDoorRho_zero_mul_le` | Salt/MR/S16ProducersH.lean:729 | characters |
| `Salt.MR.s15ArmH_le_mul` | Salt/MR/S16ProducersH.lean:747 | characters |
| `Salt.MR.h_le_1096_of_hh7` | Salt/MR/S16ProducersH.lean:766 | characters |
| `Salt.MR.s15ArmH_log_le` | Salt/MR/S16ProducersH.lean:793 | characters |
| `Salt.MR.s13_band_qfit_h` | Salt/MR/S16ProducersH.lean:918 | characters |
| `Salt.MR.rStrWitness_G1_h` | Salt/MR/S16ProducersH.lean:1131 | characters |
| `Salt.MR.rStrWitness_mul_nonneg` | Salt/MR/S16ProducersH.lean:1136 | characters |
| `Salt.MR.g2_of_j0_floor_h` | Salt/MR/S16ProducersH.lean:1141 | characters |
| `Salt.MR.m4_arith_gate4_rhoH_L` | Salt/MR/S16ProducersH.lean:1174 | characters |
| `Salt.MR.m4_chiSummedFreeRowBig_of_doorGradeGated_poolH_L_gk` | Salt/MR/S16ProducersH.lean:1242 | characters |
| `Salt.MR.hArcDen_mul_strataResidualH_sq_le_14` | Salt/MR/S16ProducersH.lean:1468 | characters |
| `Salt.MR.h_le_8103_of_hh9` | Salt/MR/S16ProducersH.lean:1624 | characters |
| `Salt.MR.s13_band_qfit_h_b9` | Salt/MR/S16ProducersH.lean:1642 | characters |
| `Salt.MR.flat_socket_uniform` | Salt/MR/S16Uniform.lean:359 | sieves, characters |
| `Salt.MR.s16_bandLaneWinL_holds` | Salt/MR/S16Uniform.lean:1200 | characters |
| `Salt.MR.logChowla2_ineffective_v2` | Salt/MR/S16Uniform.lean:1707 | characters |
| `Salt.MR.s16_bandLaneWinL_holds_uniform` | Salt/MR/S16Uniform.lean:1781 | characters |
| `Salt.MR.s16_bandLaneWinLH_holds` | Salt/MR/S16UniformLH.lean:310 | characters |
| `Salt.MR.s16_bandLaneWinLH_holdsU` | Salt/MR/S16UniformLH.lean:342 | characters |
| `Salt.MR.restrictAbove_one_prime` | Salt/MR/SPartCore.lean:67 | characters |
| `Salt.MR.ellLinInv_congr_primes` | Salt/MR/SPartCore.lean:73 | characters |
| `Salt.MR.ellLin_congr_primes` | Salt/MR/SPartCore.lean:83 | characters |
| `Salt.MR.smoothPart_one_eq_sPart` | Salt/MR/SPartCore.lean:94 | characters |
| `Salt.MR.sPart_factorization` | Salt/MR/SPartCore.lean:99 | characters |
| `Salt.MR.sPart_factorization_smoothPart` | Salt/MR/SPartCore.lean:103 | characters |
| `Salt.MR.sPart_apply` | Salt/MR/SPartCore.lean:115 | characters |
| `Salt.MR.sPart_prime_pow` | Salt/MR/SPartCore.lean:126 | characters |
| `Salt.MR.sPart_apply_prime` | Salt/MR/SPartCore.lean:136 | characters |
| `Salt.MR.sPart_prime_pow_norm_le` | Salt/MR/SPartCore.lean:145 | characters |
| `Salt.MR.sPart_isMultiplicative` | Salt/MR/SPartCore.lean:158 | characters |
| `Salt.MR.squarefull_of_sPart_ne_zero` | Salt/MR/SPartCore.lean:195 | characters |
| `Salt.MR.sum_Icc_divisorsAntidiagonal` | Salt/MR/SPartCore.lean:209 | characters |
| `Salt.MR.filter_mul_le_eq_Icc_div` | Salt/MR/SPartCore.lean:239 | characters |
| `Salt.MR.sum_hyperbola_eq_nested` | Salt/MR/SPartCore.lean:251 | characters |
| `Salt.MR.conv_partial_sum_dissect` | Salt/MR/SPartCore.lean:268 | characters |
| `Salt.MR.conv_partial_sum_dissect_range` | Salt/MR/SPartCore.lean:288 | characters |
| `Salt.MR.pretDistSq_scale_gap` | Salt/MR/SPartCore.lean:312 | characters |
| `Salt.MR.mertens_gap_le` | Salt/MR/SPartCore.lean:366 | characters |
| `Salt.MR.pretDistSq_scale_gap_dilate` | Salt/MR/SPartCore.lean:391 | characters |
| `Salt.MR.norm_ellLinInv_le_one` | Salt/MR/SPartCore.lean:411 | characters |
| `Salt.MR.norm_sPart_le_card_divisors` | Salt/MR/SPartCore.lean:423 | characters |
| `Salt.MR.card_divisors_mul_le_real` | Salt/MR/SPartCore.lean:437 | characters |
| `Salt.MR.sum_tau_weight_le` | Salt/MR/SPartCore.lean:446 | characters |
| `Salt.MR.sum_tau_le` | Salt/MR/SPartCore.lean:491 | characters |
| `Salt.MR.sum_tau_sq_le` | Salt/MR/SPartCore.lean:499 | characters |
| `Salt.MR.sum_tau_cube_le` | Salt/MR/SPartCore.lean:519 | characters |
| `Salt.MR.rpow_neg_three_halves` | Salt/MR/SPartCore.lean:547 | characters |
| `Salt.MR.rpow_neg_two` | Salt/MR/SPartCore.lean:554 | characters |
| `Salt.MR.step_three_halves` | Salt/MR/SPartCore.lean:560 | characters |
| `Salt.MR.step_two` | Salt/MR/SPartCore.lean:584 | characters |
| `Salt.MR.sum_Icc_eq_sum_range_of_zero` | Salt/MR/SPartCore.lean:594 | characters |
| `Salt.MR.sum_range_three_halves_le` | Salt/MR/SPartCore.lean:607 | characters |
| `Salt.MR.sum_range_two_le` | Salt/MR/SPartCore.lean:619 | characters |
| `Salt.MR.sum_Icc_three_halves_le` | Salt/MR/SPartCore.lean:631 | characters |
| `Salt.MR.sum_Icc_two_le` | Salt/MR/SPartCore.lean:643 | characters |
| `Salt.MR.prime_of_mem_factorization_support` | Salt/MR/SPartCore.lean:665 | characters |
| `Salt.MR.one_le_sqPartOf` | Salt/MR/SPartCore.lean:669 | characters |
| `Salt.MR.one_le_cubePartOf` | Salt/MR/SPartCore.lean:674 | characters |
| `Salt.MR.rpow_sq_cube_le` | Salt/MR/SPartCore.lean:730 | characters |
| `Salt.MR.sPart_dirichlet_bound_three_quarters` | Salt/MR/SPartCore.lean:753 | characters |
| `Salt.MR.sPart_dirichlet_bound` | Salt/MR/SPartCore.lean:887 | characters |
| `Salt.MR.sPart_tail_bound` | Salt/MR/SPartCore.lean:901 | characters |
| `Salt.MR.cm_pow` | Salt/MR/SPartCore.lean:954 | characters |
| `Salt.MR.cm_isMultiplicative` | Salt/MR/SPartCore.lean:962 | characters |
| `Salt.MR.alt_sum_shift` | Salt/MR/SPartCore.lean:971 | characters |
| `Salt.MR.sPart_cm_prime_pow` | Salt/MR/SPartCore.lean:981 | characters |
| `Salt.MR.sPart_cm_prime_pow_norm_le_one` | Salt/MR/SPartCore.lean:994 | characters |
| `Salt.MR.sPart_factorization_prod` | Salt/MR/SPartCore.lean:1002 | characters |
| `Salt.MR.sPart_cm_norm_le_one` | Salt/MR/SPartCore.lean:1018 | characters |
| `Salt.MR.sPart_cm_factorization_even` | Salt/MR/SPartCore.lean:1030 | characters |
| `Salt.MR.sPart_cm_square_support` | Salt/MR/SPartCore.lean:1052 | characters |
| `Salt.MR.rpow_sq_neg_three_quarters` | Salt/MR/SPartCore.lean:1072 | characters |
| `Salt.MR.sPart_cm_dirichlet_bound` | Salt/MR/SPartCore.lean:1082 | characters |
| `Salt.MR.seamCoeff_one_eq_one` | Salt/MR/SPartCore.lean:1147 | characters |
| `Salt.MR.seamCoeff_isMultiplicative` | Salt/MR/SPartCore.lean:1153 | characters |
| `Salt.MR.norm_seamCoeff_trivial_le` | Salt/MR/SPartCore.lean:1174 | characters |
| `Salt.MR.sPart_seamCoeff_factorization` | Salt/MR/SPartCore.lean:1180 | characters |
| `Salt.MR.sPart_seamCoeff_dirichlet_bound` | Salt/MR/SPartCore.lean:1186 | characters |
| `Salt.MR.sPart_seamCoeff_tail_bound` | Salt/MR/SPartCore.lean:1198 | characters |
| `Salt.MR.ellLin_seamCoeff` | Salt/MR/SPartStation.lean:127 | characters |
| `Salt.MR.eIu_natCast_mul` | Salt/MR/SPartStation.lean:146 | characters |
| `Salt.MR.center_halasz_supply_wide` | Salt/MR/SPartStation.lean:302 | characters |
| `Salt.MR.dilGap_div` | Salt/MR/SPartStation.lean:453 | characters |
| `Salt.MR.pretDistSq_floor_dilate` | Salt/MR/SPartStation.lean:466 | characters |
| `Salt.MR.hCenter_dissected` | Salt/MR/SPartStation.lean:608 | characters |
| `Salt.MR.abs_sum_mul_le_of_bounded` | Salt/MR/Sawtooth.lean:65 | characters |
| `Salt.MR.abs_sum_shift_mul_le_of_bounded` | Salt/MR/Sawtooth.lean:100 | characters |
| `Salt.MR.tendsto_tsum_div_rpow` | Salt/MR/Sawtooth.lean:134 | characters |
| `Salt.MR.exp_pow_im` | Salt/MR/Sawtooth.lean:281 | characters |
| `Salt.MR.sin_pi_mul_pos` | Salt/MR/Sawtooth.lean:289 | characters |
| `Salt.MR.one_sub_cos_two_pi_mul` | Salt/MR/Sawtooth.lean:295 | characters |
| `Salt.MR.one_sub_exp_eq` | Salt/MR/Sawtooth.lean:302 | characters |
| `Salt.MR.norm_one_sub_exp` | Salt/MR/Sawtooth.lean:316 | characters |
| `Salt.MR.exp_ne_one` | Salt/MR/Sawtooth.lean:321 | characters |
| `Salt.MR.abs_sum_sin_le` | Salt/MR/Sawtooth.lean:329 | characters |
| `Salt.MR.tendsto_sum_sin_div_nat` | Salt/MR/Sawtooth.lean:392 | characters |
| `Salt.MR.sinZeta_apply_one` | Salt/MR/Sawtooth.lean:502 | characters |
| `Salt.MR.hurwitzZetaOdd_apply_zero` | Salt/MR/Sawtooth.lean:578 | characters |
| `Salt.MR.coe_unitAddCircle_ne_zero` | Salt/MR/Sawtooth.lean:595 | characters |
| `Salt.MR.hurwitzZeta_apply_zero` | Salt/MR/Sawtooth.lean:613 | characters |
| `Salt.MR.sawtoothOdd` | Salt/MR/Sawtooth.lean:835 | characters |
| `Salt.MR.L1_lower_odd` | Salt/MR/Sawtooth.lean:839 | characters |
| `Salt.MR.l1LowerOddEffective_pi` | Salt/MR/Sawtooth.lean:845 | characters |
| `Salt.MR.l1LowerOddEffective_one` | Salt/MR/Sawtooth.lean:849 | characters |
| `Salt.MR.ball_leg_of_sup_weighted` | Salt/MR/SeamBallWeighted.lean:162 | characters |
| `Salt.MR.prop_A3_T1_row_split_weighted` | Salt/MR/SeamBallWeighted.lean:248 | characters |
| `Salt.MR.sigma_cutoff_pretentious_gen` | Salt/MR/SeamBallWeighted.lean:325 | characters |
| `Salt.MR.sigma_cutoff_pretentious_crit` | Salt/MR/SeamBallWeighted.lean:424 | characters |
| `Salt.MR.sigma_cutoff_pretentious_half` | Salt/MR/SeamBallWeighted.lean:459 | characters |
| `Salt.MR.integral_exp_neg_mul` | Salt/MR/SeamBallWeighted.lean:523 | characters |
| `Salt.MR.exp_neg_mul_integral_ge_midpoint` | Salt/MR/SeamBallWeighted.lean:567 | characters |
| `Salt.MR.finset_weighted_integral_ge_midpoint` | Salt/MR/SeamBallWeighted.lean:607 | characters |
| `Salt.MR.sigma_cut_lower_theta` | Salt/MR/SeamBallWeighted.lean:669 | characters |
| `Salt.MR.dist_identification_sigma_theta` | Salt/MR/SeamBallWeighted.lean:756 | characters |
| `Salt.MR.scale_floor_theta` | Salt/MR/SeamBallWeighted.lean:798 | characters |
| `Salt.MR.head_sigma_bound_theta` | Salt/MR/SeamBallWeighted.lean:822 | zeros, characters |
| `Salt.MR.calE_one` | Salt/MR/SeamCalibration.lean:113 | characters |
| `Salt.MR.calE_mono` | Salt/MR/SeamCalibration.lean:116 | characters |
| `Salt.MR.calE_step` | Salt/MR/SeamCalibration.lean:123 | characters |
| `Salt.MR.calQ_mono` | Salt/MR/SeamCalibration.lean:130 | characters |
| `Salt.MR.log_calP` | Salt/MR/SeamCalibration.lean:134 | characters |
| `Salt.MR.log_calQ` | Salt/MR/SeamCalibration.lean:140 | characters |
| `Salt.MR.le_rpow_half_of_sq_le` | Salt/MR/SeamCalibration.lean:149 | characters |
| `Salt.MR.calFrame_satisfiable` | Salt/MR/SeamCalibration.lean:348 | characters |
| `Salt.MR.calibrated_block_nonempty` | Salt/MR/SeamCalibration.lean:380 | characters |
| `Salt.MR.ladder_below_station` | Salt/MR/SeamCalibration.lean:394 | characters |
| `Salt.MR.calQK_mono` | Salt/MR/SeamCalibrationK.lean:130 | characters |
| `Salt.MR.calP_le_calQK` | Salt/MR/SeamCalibrationK.lean:138 | characters |
| `Salt.MR.calFrameK_satisfiable` | Salt/MR/SeamCalibrationK.lean:392 | characters |
| `Salt.MR.calibrated_block_nonemptyK` | Salt/MR/SeamCalibrationK.lean:448 | characters |
| `Salt.MR.ladder_below_stationK` | Salt/MR/SeamCalibrationK.lean:465 | characters |
| `Salt.MR.log_calP_div_log_calQK` | Salt/MR/SeamCalibrationK.lean:476 | characters |
| `Salt.MR.sum_ratioK_le` | Salt/MR/SeamCalibrationK.lean:509 | characters |
| `Salt.MR.eq28_clears_of_M` | Salt/MR/SeamCalibrationK.lean:538 | characters |
| `Salt.MR.sum_ratioK_pinned_clears` | Salt/MR/SeamCalibrationK.lean:555 | characters |
| `Salt.MR.ramP2mass_direct` | Salt/MR/SeamCalibrationK.lean:845 | characters |
| `Salt.MR.sum_lemma12Rows_priced_calibratedK` | Salt/MR/SeamCalibrationK.lean:1090 | characters |
| `Salt.MR.seamAnn_inter_seamBall_center_le` | Salt/MR/SeamGate.lean:79 | characters |
| `Salt.MR.ball_center_dichotomy_two_sided` | Salt/MR/SeamGate.lean:96 | characters |
| `Salt.MR.seamGateR_nonneg` | Salt/MR/SeamGate.lean:118 | characters |
| `Salt.MR.log_pow_four_le_of_le_two_mul` | Salt/MR/SeamGate.lean:128 | characters |
| `Salt.MR.seam_gate_of_nonempty` | Salt/MR/SeamGate.lean:142 | characters |
| `Salt.MR.seam_gate_of_nonempty_nat` | Salt/MR/SeamGate.lean:152 | characters |
| `Salt.MR.exists_min_gate` | Salt/MR/SeamGate.lean:170 | characters |
| `Salt.MR.seam_gate_package` | Salt/MR/SeamGate.lean:183 | characters |
| `Salt.MR.seam_sup_binder_of_inter_empty` | Salt/MR/SeamGate.lean:202 | characters |
| `Salt.MR.ball_leg_of_inter_empty` | Salt/MR/SeamGate.lean:212 | characters |
| `Salt.MR.TsetG_unique` | Salt/MR/SeamGraded.lean:120 | characters |
| `Salt.MR.TsetG_disjoint` | Salt/MR/SeamGraded.lean:133 | characters |
| `Salt.MR.TsetG_UsetG_disjoint` | Salt/MR/SeamGraded.lean:139 | characters |
| `Salt.MR.exists_TsetG_or_mem_UsetG` | Salt/MR/SeamGraded.lean:148 | characters |
| `Salt.MR.measurableSet_UsetG` | Salt/MR/SeamGraded.lean:184 | characters |
| `Salt.MR.measurableSet_TsetG` | Salt/MR/SeamGraded.lean:198 | characters |
| `Salt.MR.measurableSet_seamTtotG` | Salt/MR/SeamGraded.lean:230 | characters |
| `Salt.MR.sdiff_biUnion_TsetG` | Salt/MR/SeamGraded.lean:237 | characters |
| `Salt.MR.seam_T_additivityG` | Salt/MR/SeamGraded.lean:263 | characters |
| `Salt.MR.seam_TU_splitG` | Salt/MR/SeamGraded.lean:284 | characters |
| `Salt.MR.prop_A3_T1_row_split_weightedG` | Salt/MR/SeamGraded.lean:315 | characters |
| `Salt.MR.prop_A3_T1_row_split_weightedG_crude` | Salt/MR/SeamGraded.lean:351 | characters |
| `Salt.MR.seamAnn_integral_split` | Salt/MR/SeamLemma14.lean:83 | characters |
| `Salt.MR.spoly_eq_dpolyA_filter` | Salt/MR/SeamLemma14.lean:121 | characters |
| `Salt.MR.seamS0_range` | Salt/MR/SeamLemma14.lean:133 | characters |
| `Salt.MR.seamS0_pos` | Salt/MR/SeamLemma14.lean:141 | characters |
| `Salt.MR.seam_midrange_bound` | Salt/MR/SeamLemma14.lean:182 | characters |
| `Salt.MR.seam_split_four` | Salt/MR/SeamLemma14.lean:194 | characters |
| `Salt.MR.seam_Msup` | Salt/MR/SeamLemma14.lean:226 | characters |
| `Salt.MR.seam_midrange_of_tall_row` | Salt/MR/SeamLemma14.lean:243 | characters |
| `Salt.MR.lemma14_contour_of_Msup_at` | Salt/MR/SeamLemma14.lean:451 | characters |
| `Salt.MR.lemma14_contour_seam_supplied` | Salt/MR/SeamLemma14.lean:605 | characters |
| `Salt.MR.lemma14_contour_seam_supplied_single` | Salt/MR/SeamLemma14.lean:633 | characters |
| `Salt.MR.sum_ratioK_le_basel` | Salt/MR/SeamNumber.lean:264 | characters |
| `Salt.MR.eq28_clears_of_M_basel` | Salt/MR/SeamNumber.lean:290 | characters |
| `Salt.MR.seamCoefW_of_global` | Salt/MR/SeamRowWindowed.lean:135 | characters |
| `Salt.MR.seamCoefWLevels_of_global` | Salt/MR/SeamRowWindowed.lean:163 | characters |
| `Salt.MR.winCut_supp` | Salt/MR/SeamRowWindowed.lean:178 | characters |
| `Salt.MR.winCut_supp_real` | Salt/MR/SeamRowWindowed.lean:184 | characters |
| `Salt.MR.norm_winCut_le` | Salt/MR/SeamRowWindowed.lean:193 | characters |
| `Salt.MR.winCut_of_mem` | Salt/MR/SeamRowWindowed.lean:201 | characters |
| `Salt.MR.seamCoefW_winCut` | Salt/MR/SeamRowWindowed.lean:218 | characters |
| `Salt.MR.seam_coef_contract_windowed_sat` | Salt/MR/SeamRowWindowed.lean:243 | characters |
| `Salt.MR.second_window_le_first_row` | Salt/MR/SeamRowWindowed.lean:698 | characters |
| `Salt.MR.annulus_ball_far_split` | Salt/MR/SeamSplit.lean:185 | characters |
| `Salt.MR.spoly_abel_sup` | Salt/MR/SeamSplit.lean:270 | characters |
| `Salt.MR.ball_leg_of_sup` | Salt/MR/SeamSplit.lean:362 | characters |
| `Salt.MR.seam_TU_split` | Salt/MR/SeamSplit.lean:535 | characters |
| `Salt.MR.far_leg_collapse` | Salt/MR/SeamSplit.lean:559 | characters |
| `Salt.MR.prop_A3_T1_row_split` | Salt/MR/SeamSplit.lean:624 | characters |
| `Salt.MR.prop_A3_T1_row_split_crude` | Salt/MR/SeamSplit.lean:692 | characters |
| `Salt.MR.seam_window_datum_zero` | Salt/MR/SeamTerminal.lean:100 | characters |
| `Salt.MR.seam_Dmax_bridge` | Salt/MR/SeamTerminal.lean:112 | characters |
| `Salt.MR.gJ_prime_pow` | Salt/MR/Sec9Glue.lean:150 | characters |
| `Salt.MR.prod_one_sub_gJ` | Salt/MR/Sec9Glue.lean:236 | characters |
| `Salt.MR.lemma5_middle` | Salt/MR/Sec9Glue.lean:259 | characters |
| `Salt.MR.lemma5` | Salt/MR/Sec9Glue.lean:275 | characters |
| `Salt.MR.lemma5_MR_middle` | Salt/MR/Sec9Glue.lean:293 | characters |
| `Salt.MR.lemma5_MR` | Salt/MR/Sec9Glue.lean:300 | characters |
| `Salt.MR.lemma5_budget` | Salt/MR/Sec9Glue.lean:313 | characters |
| `Salt.MR.lemma5_budget_pinned` | Salt/MR/Sec9Glue.lean:332 | characters |
| `Salt.MR.door_h_le_hTwo` | Salt/MR/Sec9Glue.lean:377 | characters |
| `Salt.MR.sec9_split` | Salt/MR/Sec9Glue.lean:399 | characters |
| `Salt.MR.sec9_count_identity` | Salt/MR/Sec9Glue.lean:440 | characters |
| `Salt.MR.sec9_four_term` | Salt/MR/Sec9Glue.lean:456 | characters |
| `Salt.MR.card_not_memS_le_sum` | Salt/MR/Sec9Glue.lean:478 | characters |
| `Salt.MR.sec9_eq28` | Salt/MR/Sec9Glue.lean:507 | sieves, characters |
| `Salt.MR.sec9_eq28_exit` | Salt/MR/Sec9Glue.lean:524 | sieves, characters |
| `Salt.MR.seven_eighths_bound` | Salt/MR/SevenEighths.lean:293 | characters |
| `Salt.MR.seven_eighths_bound_loglog` | Salt/MR/SevenEighths.lean:318 | characters |
| `Salt.MR.seven_eighths_bound_primes` | Salt/MR/SevenEighths.lean:406 | characters |
| `Salt.MR.shiu_moment_sq` | Salt/MR/ShiuMoment.lean:436 | characters |
| `Salt.MR.shortInterval_vonMangoldt_le` | Salt/MR/ShortIntervalPsi.lean:407 | sieves, characters |
| `Salt.MR.rampSliverMass_bound_unconditional` | Salt/MR/ShortIntervalPsi.lean:585 | characters |
| `Salt.MR.LFunction_band_lower` | Salt/MR/SiegelArm.lean:161 | characters |
| `Salt.MR.eulerFactor_prod_lower` | Salt/MR/SiegelArm.lean:177 | characters |
| `Salt.MR.LFunction_band_lower_principal` | Salt/MR/SiegelArm.lean:231 | characters |
| `Salt.MR.chi_Llower_band` | Salt/MR/SiegelArm.lean:275 | characters |
| `Salt.MR.chi_floor_all_complete` | Salt/MR/SiegelArm.lean:323 | characters |
| `Salt.MR.chi_floor_all_complete_twisted` | Salt/MR/SiegelArm.lean:348 | characters |
| `Salt.MR.zeta_upper_band` | Salt/MR/SiegelArm.lean:392 | zeros, characters |
| `Salt.MR.LFunctionTrivChar_norm_le` | Salt/MR/SiegelArm.lean:423 | zeros, characters |
| `Salt.MR.norm_deriv_LFunction_ball_le` | Salt/MR/SiegelArm.lean:454 | characters |
| `Salt.MR.LFunction_lower_of_L1` | Salt/MR/SiegelArm.lean:479 | characters |
| `Salt.MR.chi_Llower_real_far` | Salt/MR/SiegelArm.lean:512 | characters |
| `Salt.MR.chi_Llower_real_of_L1` | Salt/MR/SiegelArm.lean:618 | characters |
| `Salt.MR.chi_floor_real_of_L1` | Salt/MR/SiegelArm.lean:725 | characters |
| `Salt.MR.exists_L1_lower` | Salt/MR/SiegelArm.lean:771 | characters |
| `Salt.MR.chi_Llower_band_single` | Salt/MR/SiegelBand.lean:81 | characters |
| `Salt.MR.chi_Llower_band_uniform` | Salt/MR/SiegelBand.lean:105 | characters |
| `Salt.MR.chi_floor_band_uniform` | Salt/MR/SiegelBand.lean:158 | characters |
| `Salt.MR.chi_floor_band_uniform_twisted` | Salt/MR/SiegelBand.lean:174 | characters |
| `Salt.MR.capfree_threshold` | Salt/MR/SiegelBand.lean:196 | characters |
| `Salt.MR.capfree_threshold_lt` | Salt/MR/SiegelBand.lean:201 | characters |
| `Salt.MR.band_gate_threshold` | Salt/MR/SiegelBand.lean:208 | characters |
| `Salt.MR.band_gate_threshold_cfb` | Salt/MR/SiegelBand.lean:218 | characters |
| `Salt.MR.quality_gate_threshold` | Salt/MR/SiegelBand.lean:228 | characters |
| `Salt.MR.siegelBandB_spec` | Salt/MR/SiegelBand.lean:246 | characters |
| `Salt.MR.modulus_bound_mono` | Salt/MR/SiegelBand.lean:260 | characters |
| `Salt.MR.sec9_eq28_const` | Salt/MR/SieveGlue.lean:103 | sieves, characters |
| `Salt.MR.eq28_clears_of_M_const` | Salt/MR/SieveGlue.lean:117 | sieves, characters |
| `Salt.MR.sec9_eq28_exit_const` | Salt/MR/SieveGlue.lean:146 | sieves, characters |
| `Salt.MR.card_blockfree_le` | Salt/MR/SieveGlue.lean:183 | sieves, characters |
| `Salt.MR.hreg_of_small_h` | Salt/MR/SieveGlue.lean:249 | sieves, characters |
| `Salt.MR.hbig_of_floor` | Salt/MR/SieveGlue.lean:272 | sieves, characters |
| `Salt.MR.herr_of_mertens` | Salt/MR/SieveGlue.lean:287 | sieves, characters |
| `Salt.MR.two_le_calP` | Salt/MR/SieveGlue.lean:315 | sieves, characters |
| `Salt.MR.herr_of_floor` | Salt/MR/SieveGlue.lean:338 | sieves, characters |
| `Salt.MR.hsieve_of_engine` | Salt/MR/SieveGlue.lean:438 | sieves, characters |
| `Salt.MR.memS_congr` | Salt/MR/SieveGlue.lean:524 | sieves, characters |
| `Salt.MR.card_notMemS_pin` | Salt/MR/SieveGlue.lean:533 | sieves, characters |
| `Salt.MR.sec9_eq28_exit_calFamily` | Salt/MR/SieveGlue.lean:556 | sieves, characters |
| `Salt.MR.mertensM_ge_neg_seventeen` | Salt/MR/SmallStones.lean:93 | characters |
| `Salt.MR.sixteenth_loglog_le_SPartial_div_eight` | Salt/MR/SmallStones.lean:152 | characters |
| `Salt.MR.hMball_of_A4_cap` | Salt/MR/SmallStones.lean:180 | characters |
| `Salt.MR.ramP2mass_le` | Salt/MR/SmallStones.lean:419 | characters |
| `Salt.MR.lemma12_meansq_mr_final` | Salt/MR/SmallStones.lean:491 | characters |
| `Salt.MR.zHead_A_pays` | Salt/MR/StrideDoorAllGrades.lean:379 | characters |
| `Salt.MR.zCount_form` | Salt/MR/StrideDoorAllGrades.lean:389 | characters |
| `Salt.MR.zBuilder_absorb_L` | Salt/MR/StrideDoorAllGrades.lean:404 | characters |
| `Salt.MR.chowlaRegimeFlat_exists_param_gen_ceiling_mul_L` | Salt/MR/StrideDoorAllGrades.lean:439 | characters |
| `Salt.MR.s13_g2_jfloor_of_MSelect'_L_gk_h_L` | Salt/MR/StrideDoorAllGrades.lean:902 | characters |
| `Salt.MR.hArcDen_mul_strataResidualH_sq_le_L` | Salt/MR/StrideDoorAllGrades.lean:939 | characters |
| `Salt.MR.arc36_of_regime_h_L` | Salt/MR/StrideDoorAllGrades.lean:1181 | characters |
| `Salt.MR.s13_band_qfit_h_L` | Salt/MR/StrideDoorAllGrades.lean:1511 | characters |
| `Salt.MR.s13_smallGradeFits_h_L` | Salt/MR/StrideDoorAllGrades.lean:1603 | characters |
| `Salt.MR.s13_winFit_h_of_halfWindow_gen_L` | Salt/MR/StrideDoorAllGrades.lean:1772 | characters |
| `Salt.MR.s13_gate8_L_gk_h_L` | Salt/MR/StrideDoorAllGrades.lean:2125 | characters |
| `Salt.MR.s13_smallGradeFits_of_halfWindow_L_gk_h_L` | Salt/MR/StrideDoorAllGrades.lean:2160 | characters |
| `Salt.MR.s15ArmH_log_le_L` | Salt/MR/StrideDoorAllGrades.lean:2180 | characters |
| `Salt.MR.zSplit_arm_L` | Salt/MR/StrideDoorAllGrades.lean:2243 | characters |
| `Salt.MR.zSplit_arm_L2` | Salt/MR/StrideDoorAllGrades.lean:2356 | characters |
| `Salt.MR.zH_le_logH` | Salt/MR/StrideDoorAllGrades.lean:2859 | characters |
| `Salt.MR.zH_le_exp` | Salt/MR/StrideDoorAllGrades.lean:2871 | characters |
| `Salt.MR.capfloor_lam_core_h_L` | Salt/MR/StrideDoorAllGrades.lean:2880 | characters |
| `Salt.MR.capfloor_floor3_numeric_h_L` | Salt/MR/StrideDoorAllGrades.lean:2891 | characters |
| `Salt.MR.capeps_master_L` | Salt/MR/StrideDoorAllGrades.lean:2926 | characters |
| `Salt.MR.capeps_expbound_L` | Salt/MR/StrideDoorAllGrades.lean:2957 | characters |
| `Salt.MR.capeps_bigexp_L` | Salt/MR/StrideDoorAllGrades.lean:2977 | characters |
| `Salt.MR.capeps_Pbig_h_L` | Salt/MR/StrideDoorAllGrades.lean:3006 | characters |
| `Salt.MR.capeps_row_phi_h_L` | Salt/MR/StrideDoorAllGrades.lean:4266 | characters |
| `Salt.MR.capeps_row_tail_h_L` | Salt/MR/StrideDoorAllGrades.lean:4314 | characters |
| `Salt.MR.capeps_row_p2_h_L` | Salt/MR/StrideDoorAllGrades.lean:4427 | characters |
| `Salt.MR.s15_crossing_supplied_LH_gk_ceiling_sharpT0_khoist_csfree_kswin_L` | Salt/MR/StrideDoorAllGrades.lean:4768 | characters |
| `Salt.MR.loglog_mul_flatDesignBase_le_L` | Salt/MR/StrideDoorAllGrades.lean:5002 | characters |
| `Salt.MR.flatDesignBase_clears_stride_floors_L` | Salt/MR/StrideDoorAllGrades.lean:5055 | characters |
| `Salt.MR.zCharge_exists` | Salt/MR/StrideDoorAllGrades.lean:5431 | characters |
| `Salt.MR.zE_beaten` | Salt/MR/StrideDoorAllGrades.lean:5473 | characters |
| `Salt.MR.zCount_affine` | Salt/MR/StrideDoorAllGrades.lean:5566 | characters |
| `Salt.MR.strideDoorAllGradesW_holds` | Salt/MR/StrideDoorAllGrades.lean:5602 | characters |
| `Salt.MR.grade12_pin_bridge` | Salt/MR/StrideGrade12Walls.lean:55 | characters |
| `Salt.MR.grade12_split_admits_primorial_eleven` | Salt/MR/StrideGrade12Walls.lean:61 | characters |
| `Salt.MR.grade12_product_cap_refuses_primorial_eleven` | Salt/MR/StrideGrade12Walls.lean:68 | characters |
| `Salt.MR.grade11_refuses_primorial_eleven` | Salt/MR/StrideGrade12Walls.lean:74 | characters |
| `Salt.MR.landed_prize_cap_refuses_primorial_eleven` | Salt/MR/StrideGrade12Walls.lean:81 | characters |
| `Salt.MR.s16_audit_rho_ge_wide_h_g12` | Salt/MR/StrideGrade12Walls.lean:92 | characters |
| `Salt.MR.s16_audit_neglog_rho_le_wide_h_g12` | Salt/MR/StrideGrade12Walls.lean:124 | characters |
| `Salt.MR.flatDoorM_bfloor_bump_g12` | Salt/MR/StrideGrade12Walls.lean:153 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_charge_g12b` | Salt/MR/StrideGrade12bWalls.lean:49 | characters |
| `Salt.MR.s15ArmH_log_le_g12b` | Salt/MR/StrideGrade12bWalls.lean:93 | characters |
| `Salt.MR.s16_audit_neglog_rho_le_425_h_g12b` | Salt/MR/StrideGrade12bWalls.lean:151 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_wide_g12b` | Salt/MR/StrideGrade12bWalls.lean:162 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_wide_g12b` | Salt/MR/StrideGrade12bWalls.lean:183 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_bumped_win_h_g12b` | Salt/MR/StrideGrade12bWalls.lean:210 | characters |
| `Salt.MR.reach14_ceiling_eq` | Salt/MR/StrideGradeReach.lean:87 | characters |
| `Salt.MR.reach14_reaches_the_million` | Salt/MR/StrideGradeReach.lean:90 | characters |
| `Salt.MR.reach14_arm_family_fits` | Salt/MR/StrideGradeReach.lean:94 | characters |
| `Salt.MR.reach14_capgate_room` | Salt/MR/StrideGradeReach.lean:98 | characters |
| `Salt.MR.landed_ceiling_refuses_the_million` | Salt/MR/StrideGradeReach.lean:103 | characters |
| `Salt.MR.landed_capgate_refuses_the_million` | Salt/MR/StrideGradeReach.lean:108 | characters |
| `Salt.MR.reach14_countpin_refuses_stride_two` | Salt/MR/StrideGradeReach.lean:127 | characters |
| `Salt.MR.h_le_1202604_of_hh14` | Salt/MR/StrideGradeReach.lean:135 | characters |
| `Salt.MR.capfloor_logH_le_quarter_sqrt` | Salt/MR/StrideGradeReach.lean:161 | characters |
| `Salt.MR.flat_half_line_g14` | Salt/MR/StrideGradeReach.lean:183 | characters |
| `Salt.MR.flat_anchor_line_wide_g14` | Salt/MR/StrideGradeReach.lean:207 | characters |
| `Salt.MR.flat_gP1_line_g14` | Salt/MR/StrideGradeReach.lean:216 | characters |
| `Salt.MR.flat_lvl_line_g14` | Salt/MR/StrideGradeReach.lean:240 | characters |
| `Salt.MR.s15Arm_log_le_scaled_g14` | Salt/MR/StrideGradeReach.lean:317 | characters |
| `Salt.MR.s15ArmH_log_le_g14` | Salt/MR/StrideGradeReach.lean:515 | characters |
| `Salt.MR.s15ArmH_log_le_14` | Salt/MR/StrideGradeReach.lean:573 | characters |
| `Salt.MR.log_chowla_aff_of_door_crowned_unslotted_g` | Salt/MR/StrideGradeReceipt.lean:46 | characters |
| `Salt.MR.logChowlaAffSupplyW_holds` | Salt/MR/StrideGradeReceipt.lean:57 | characters |
| `Salt.MR.zRough_oddOmega_infinite_primorial` | Salt/MR/StrideGradeReceipt.lean:70 | characters |
| `Salt.MR.log_chowla_aff_of_door_crowned_unslotted_g12b` | Salt/MR/StrideGradeReceipt12b.lean:40 | characters |
| `Salt.MR.hah9_of_primorial_le_2310` | Salt/MR/StrideGradeReceipt12b.lean:71 | characters |
| `Salt.MR.one_sub_liouville_shift_two` | Salt/MR/StrideGradeReceipt12b.lean:92 | characters |
| `Salt.MR.roughOdd_filter_eq_odd_filter` | Salt/MR/StrideGradeReceipt12b.lean:111 | characters |
| `Salt.MR.zRough_oddOmega_logMass_class` | Salt/MR/StrideGradeReceipt12b.lean:130 | characters |
| `Salt.MR.zRough_oddOmega_infinite_class` | Salt/MR/StrideGradeReceipt12b.lean:201 | characters |
| `Salt.MR.zRough_oddOmega_logMass_class_mutant_false` | Salt/MR/StrideGradeReceipt12b.lean:241 | characters |
| `Salt.MR.s16_audit_rho_ge_wide_h_g` | Salt/MR/StrideGradeWalls.lean:65 | characters |
| `Salt.MR.s16_audit_neglog_rho_le_wide_h_g` | Salt/MR/StrideGradeWalls.lean:96 | characters |
| `Salt.MR.s16_audit_neglog_rho_le_425_h` | Salt/MR/StrideGradeWalls.lean:116 | characters |
| `Salt.MR.flat_half_line_g` | Salt/MR/StrideGradeWalls.lean:130 | characters |
| `Salt.MR.flat_anchor_line_wide_g` | Salt/MR/StrideGradeWalls.lean:155 | characters |
| `Salt.MR.flat_gP1_line_g` | Salt/MR/StrideGradeWalls.lean:165 | characters |
| `Salt.MR.flat_lvl_line_g` | Salt/MR/StrideGradeWalls.lean:189 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_charge_g` | Salt/MR/StrideGradeWalls.lean:256 | characters |
| `Salt.MR.s15_sel''_L_witness_flat_wide_g` | Salt/MR/StrideGradeWalls.lean:296 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_wide_g` | Salt/MR/StrideGradeWalls.lean:318 | characters |
| `Salt.MR.flatDoorM_bfloor_bump_g` | Salt/MR/StrideGradeWalls.lean:347 | characters |
| `Salt.MR.s15_sel''_L_gk_witness_flat_bumped_win_h_g` | Salt/MR/StrideGradeWalls.lean:382 | characters |
| `Salt.MR.s15Arm_log_le_scaled_g` | Salt/MR/StrideGradeWalls.lean:433 | characters |
| `Salt.MR.s15ArmH_log_le_g` | Salt/MR/StrideGradeWalls.lean:633 | characters |
| `Salt.MR.chowlaRegimeFlat_exists_param_gen_ceiling_mul` | Salt/MR/StridePairReceipt.lean:200 | characters |
| `Salt.MR.xceil_arm_split_mul_h` | Salt/MR/StridePairReceipt.lean:1341 | characters |
| `Salt.MR.mrtUniformityXiL2H_holds_flat` | Salt/MR/StridePairReceipt.lean:2038 | characters |
| `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride` | Salt/MR/StridePairReceipt.lean:2121 | characters |
| `Salt.MR.chowlaRegimeFlat_exists_param_gen_ceiling_mul_b9` | Salt/MR/StridePairReceipt.lean:2571 | characters |
| `Salt.MR.xceil_arm_split_mul_h_b9` | Salt/MR/StridePairReceipt.lean:2870 | characters |
| `Salt.MR.mrtUniformityXiL2H_holds_flat_g` | Salt/MR/StridePairReceiptG.lean:1118 | characters |
| `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride_g` | Salt/MR/StridePairReceiptG.lean:1173 | characters |
| `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride_g12b` | Salt/MR/StridePairReceiptG12b.lean:1140 | characters |
| `Salt.MR.pell_yn_odd_not_dvd` | Salt/MR/StridePrizePell.lean:39 | characters |
| `Salt.MR.pell_xn_sub_one_mul` | Salt/MR/StridePrizePell.lean:59 | characters |
| `Salt.MR.zRough_oddOmega_infinite_of_pell_seed` | Salt/MR/StridePrizePell.lean:82 | characters |
| `Salt.MR.zRough_oddOmega_infinite_pell_4620` | Salt/MR/StridePrizePell.lean:128 | characters |
| `Salt.MR.pell_state_periodic` | Salt/MR/StridePrizePellClass.lean:38 | characters |
| `Salt.MR.pell_class_iter` | Salt/MR/StridePrizePellClass.lean:93 | characters |
| `Salt.MR.zRough_oddOmega_infinite_class_of_seed` | Salt/MR/StridePrizePellClass.lean:108 | characters |
| `Salt.MR.s4ArrowUncapped_holds` | Salt/MR/StrideSupplyAllStrides.lean:312 | characters |
| `Salt.MR.strideSupplyAllStridesW_holds` | Salt/MR/StrideSupplyAllStrides.lean:316 | characters |
| `Salt.MR.twinLogWeight_support_infinite_all_P` | Salt/MR/StrideSupplyAllStrides.lean:348 | characters |
| `Salt.MR.joint_supF_pin_at` | Salt/MR/SupClose.lean:139 | characters |
| `Salt.MR.center_dist_floor_recentred` | Salt/MR/SupClose.lean:224 | characters |
| `Salt.MR.joint_supF_pin_trunc` | Salt/MR/SupClose.lean:248 | characters |
| `Salt.MR.ellLin_euler_product` | Salt/MR/SupF.lean:141 | zeros, characters |
| `Salt.MR.euler_log_bound` | Salt/MR/SupF.lean:186 | zeros, characters |
| `Salt.MR.smooth_ratio_bound` | Salt/MR/SupF.lean:403 | characters |
| `Salt.MR.dist_identification` | Salt/MR/SupF.lean:521 | characters |
| `Salt.MR.head_pin_bound` | Salt/MR/SupF.lean:543 | zeros, characters |
| `Salt.MR.prime_sum_sigma` | Salt/MR/SupF.lean:599 | characters |
| `Salt.MR.dist_identification_sigma` | Salt/MR/SupF.lean:757 | characters |
| `Salt.MR.head_sigma_bound` | Salt/MR/SupF.lean:818 | zeros, characters |
| `Salt.MR.scale_floor` | Salt/MR/SupF.lean:869 | characters |
| `Salt.MR.scale_floor_Mrange` | Salt/MR/SupF.lean:960 | characters |
| `Salt.MR.sigma_cutoff_pretentious` | Salt/MR/SupF.lean:1005 | characters |
| `Salt.MR.scale_floor_Mrange_seam` | Salt/MR/SupF.lean:1155 | characters |
| `Salt.MR.jointIntegrableAt_pin_free` | Salt/MR/SupStation.lean:127 | characters |
| `Salt.MR.center_halasz_supply_uniform` | Salt/MR/SupStation.lean:286 | characters |
| `Salt.MR.ball_sup_supplied_uniform` | Salt/MR/SupStation.lean:412 | characters |
| `Salt.MR.seam_ball_leg_station` | Salt/MR/SupStation.lean:540 | characters |
| `Salt.MR.seamGateRstar_le_self` | Salt/MR/SupStation.lean:635 | characters |
| `Salt.MR.seam_ball_leg_station_M` | Salt/MR/SupStation.lean:717 | characters |
| `Salt.MR.prop_A3_T1_row_station` | Salt/MR/SupStation.lean:782 | characters |
| `Salt.MR.center_halasz_supply_Y` | Salt/MR/SupplyGeneric.lean:257 | characters |
| `Salt.MR.ball_sup_supplied_Y` | Salt/MR/SupplyGeneric.lean:409 | characters |
| `Salt.MR.bandLterm_pos` | Salt/MR/T0Band.lean:150 | characters |
| `Salt.MR.bandTail_nonneg` | Salt/MR/T0Band.lean:157 | characters |
| `Salt.MR.bandSupS_nonneg` | Salt/MR/T0Band.lean:163 | characters |
| `Salt.MR.ballErr_le_radius` | Salt/MR/T0Band.lean:173 | characters |
| `Salt.MR.band_sup_of_center` | Salt/MR/T0Band.lean:242 | characters |
| `Salt.MR.band_sup_supplied_Y` | Salt/MR/T0Band.lean:357 | characters |
| `Salt.MR.band_integral_of_sup` | Salt/MR/T0Band.lean:448 | characters |
| `Salt.MR.t0_band_supply` | Salt/MR/T0Band.lean:521 | characters |
| `Salt.MR.cfb_sup_of_center` | Salt/MR/T0BandCapFree.lean:147 | characters |
| `Salt.MR.band_integral_of_sup_crude` | Salt/MR/T0BandCapFree.lean:200 | characters |
| `Salt.MR.cfb_band_loglog` | Salt/MR/T0BandCapFree.lean:285 | characters |
| `Salt.MR.cfb_band_logloglog` | Salt/MR/T0BandCapFree.lean:318 | characters |
| `Salt.MR.chi_floor_band_strength` | Salt/MR/T0BandCapFree.lean:372 | characters |
| `Salt.MR.chi_floor_band_nonreal` | Salt/MR/T0BandCapFree.lean:417 | characters |
| `Salt.MR.band_floor_M0` | Salt/MR/T0BandCapFree.lean:500 | characters |
| `Salt.MR.band_floor_M0_liouChi` | Salt/MR/T0BandCapFree.lean:536 | characters |
| `Salt.MR.cfb_gate_decay` | Salt/MR/T0BandCapFree.lean:561 | characters |
| `Salt.MR.cfb_floor_clears_gate` | Salt/MR/T0BandCapFree.lean:596 | characters |
| `Salt.MR.cfb_ballerr_le` | Salt/MR/T0BandCapFree.lean:614 | characters |
| `Salt.MR.cfbC₁_nonneg` | Salt/MR/T0BandCapFree.lean:670 | characters |
| `Salt.MR.cfb_exit_summand_le` | Salt/MR/T0BandCapFree.lean:684 | characters |
| `Salt.MR.cfb_t0band_supply` | Salt/MR/T0BandCapFree.lean:723 | characters |
| `Salt.MR.cfb_seam_floor_of_band` | Salt/MR/T0BandCapFree.lean:851 | characters |
| `Salt.MR.cfb_t0band_supply_chi` | Salt/MR/T0BandCapFree.lean:874 | characters |
| `Salt.MR.chiBarCoeff_ramare` | Salt/MR/TLegChi.lean:104 | characters |
| `Salt.MR.chiBarCoeff_window` | Salt/MR/TLegChi.lean:131 | characters |
| `Salt.MR.not_blockSmallG_pred_of_mem_TsetG` | Salt/MR/TLegCover.lean:99 | characters |
| `Salt.MR.TsetG_level_ge_two_witness` | Salt/MR/TLegCover.lean:112 | characters |
| `Salt.MR.ramI_pred_nonempty_of_mem_TsetG` | Salt/MR/TLegCover.lean:122 | characters |
| `Salt.MR.TsetGr_subset_TsetG` | Salt/MR/TLegCover.lean:146 | characters |
| `Salt.MR.ramQ_violation_of_mem_TsetGr` | Salt/MR/TLegCover.lean:151 | characters |
| `Salt.MR.measurableSet_TsetGr` | Salt/MR/TLegCover.lean:168 | characters |
| `Salt.MR.TsetG_subset_biUnion_TsetGr` | Salt/MR/TLegCover.lean:179 | characters |
| `Salt.MR.setIntegral_le_finset_sum_of_cover` | Salt/MR/TLegCover.lean:205 | characters |
| `Salt.MR.integral_TsetG_le_sum_TsetGr` | Salt/MR/TLegCover.lean:263 | characters |
| `Salt.MR.integral_TsetG_le_card_mul` | Salt/MR/TLegCover.lean:291 | characters |
| `Salt.MR.one_le_normalized_of_mem_TsetGr` | Salt/MR/TLegCover.lean:309 | characters |
| `Salt.MR.one_le_normalized_pow` | Salt/MR/TLegCover.lean:330 | characters |
| `Salt.MR.one_le_ramQ_pow_mul_exp` | Salt/MR/TLegCover.lean:349 | characters |
| `Salt.MR.cell_integral_normalized` | Salt/MR/TLegCover.lean:377 | characters |
| `Salt.MR.measurableSet_annulus_TsetGr` | Salt/MR/TLegCover.lean:427 | characters |
| `Salt.MR.annulus_TsetGr_subset_Icc` | Salt/MR/TLegCover.lean:434 | characters |
| `Salt.MR.cell_integral_normalized_annulus` | Salt/MR/TLegCover.lean:445 | characters |
| `Salt.MR.norm_ramMain_sq_le_of_mem_TsetG` | Salt/MR/TLegE1.lean:127 | characters |
| `Salt.MR.integral_ramMain_sq_le_of_subset_TsetG` | Salt/MR/TLegE1.lean:147 | characters |
| `Salt.MR.ramRbot_one_le_of_mem_ramI` | Salt/MR/TLegE1.lean:213 | characters |
| `Salt.MR.sum_integral_ramMain_sq_le_of_subset_TsetG` | Salt/MR/TLegE1.lean:245 | characters |
| `Salt.MR.E1_bound_gen` | Salt/MR/TLegE1.lean:314 | characters |
| `Salt.MR.E1_bound` | Salt/MR/TLegE1.lean:353 | characters |
| `Salt.MR.exp_block_bottom_le_rpow` | Salt/MR/TLegE1.lean:392 | characters |
| `Salt.MR.rpow_growth_le_rpow_bottom` | Salt/MR/TLegE1.lean:409 | characters |
| `Salt.MR.E1_pin_gen` | Salt/MR/TLegE1.lean:436 | characters |
| `Salt.MR.E1_pin` | Salt/MR/TLegE1.lean:621 | characters |
| `Salt.MR.mrAlpha_mono` | Salt/MR/TLegExit.lean:105 | characters |
| `Salt.MR.mrAlpha_pos` | Salt/MR/TLegExit.lean:118 | characters |
| `Salt.MR.mrAlpha_le_quarter` | Salt/MR/TLegExit.lean:127 | characters |
| `Salt.MR.alpha_gates_from_eta` | Salt/MR/TLegExit.lean:140 | characters |
| `Salt.MR.ramI_bottom_deficit` | Salt/MR/TLegExit.lean:153 | characters |
| `Salt.MR.ramI_top_le` | Salt/MR/TLegExit.lean:164 | characters |
| `Salt.MR.ramI_pos_of_mem` | Salt/MR/TLegExit.lean:177 | characters |
| `Salt.MR.ramI_card_two_mul` | Salt/MR/TLegExit.lean:188 | characters |
| `Salt.MR.level_kill_budget` | Salt/MR/TLegExit.lean:205 | characters |
| `Salt.MR.cell_price_uniform` | Salt/MR/TLegExit.lean:276 | characters |
| `Salt.MR.level_geometry_collapse` | Salt/MR/TLegExit.lean:614 | characters |
| `Salt.MR.integral_ramMain_le_exp_mul_ramR` | Salt/MR/TLegExit.lean:681 | characters |
| `Salt.MR.sum_Ej_collected` | Salt/MR/TLegExit.lean:1026 | characters |
| `Salt.MR.ellPin_mul_block_le` | Salt/MR/TLegKill.lean:154 | characters |
| `Salt.MR.exp_ellPin_alpha_le` | Salt/MR/TLegKill.lean:168 | characters |
| `Salt.MR.exp_ellPin_cancel` | Salt/MR/TLegKill.lean:186 | characters |
| `Salt.MR.ellPin_window_bottom_ge` | Salt/MR/TLegKill.lean:212 | characters |
| `Salt.MR.factorial_sq_le_exp` | Salt/MR/TLegKill.lean:254 | characters |
| `Salt.MR.ell_log_ell_le` | Salt/MR/TLegKill.lean:280 | characters |
| `Salt.MR.factorial_sq_le_pin` | Salt/MR/TLegKill.lean:343 | characters |
| `Salt.MR.gate2_absorb` | Salt/MR/TLegKill.lean:470 | characters |
| `Salt.MR.cell_geometry_collapse` | Salt/MR/TLegKill.lean:495 | characters |
| `Salt.MR.mrAlpha_diff` | Salt/MR/TLegKill.lean:556 | characters |
| `Salt.MR.mrAlpha_decay_le` | Salt/MR/TLegKill.lean:571 | characters |
| `Salt.MR.mrAlpha_pred_lt` | Salt/MR/TLegKill.lean:581 | characters |
| `Salt.MR.level_kill_exponent` | Salt/MR/TLegKill.lean:596 | characters |
| `Salt.MR.level_kill_exp` | Salt/MR/TLegKill.lean:618 | characters |
| `Salt.MR.level_kill_collected` | Salt/MR/TLegKill.lean:646 | characters |
| `Salt.MR.level_kill_collected_P1` | Salt/MR/TLegKill.lean:682 | characters |
| `Salt.MR.ramQ_pow_mul_ramR_eq_spoly_mix` | Salt/MR/TLegKill.lean:725 | characters |
| `Salt.MR.norm_mixCoeff_le` | Salt/MR/TLegKill.lean:764 | characters |
| `Salt.MR.coeff_bound_mix` | Salt/MR/TLegKill.lean:785 | characters |
| `Salt.MR.mix_moment` | Salt/MR/TLegKill.lean:803 | characters |
| `Salt.MR.cell_ramR_normalized` | Salt/MR/TLegKill.lean:847 | characters |
| `Salt.MR.cell_bound_raw` | Salt/MR/TLegKill.lean:905 | characters |
| `Salt.MR.cell_bound_pinned` | Salt/MR/TLegKill.lean:979 | characters |
| `Salt.MR.blockSmallG_of_mem_TsetG` | Salt/MR/TLegPreamble.lean:101 | characters |
| `Salt.MR.ramQ_le_of_blockSmallG` | Salt/MR/TLegPreamble.lean:113 | characters |
| `Salt.MR.ramQ_sq_le_of_blockSmallG` | Salt/MR/TLegPreamble.lean:122 | characters |
| `Salt.MR.exists_mem_ramI_ramQ_le_of_mem_TsetG` | Salt/MR/TLegPreamble.lean:143 | characters |
| `Salt.MR.measurableSet_annulus_TsetG` | Salt/MR/TLegPreamble.lean:156 | characters |
| `Salt.MR.annulus_TsetG_subset_Icc` | Salt/MR/TLegPreamble.lean:164 | characters |
| `Salt.MR.lemma12_on_TsetG` | Salt/MR/TLegPreamble.lean:173 | characters |
| `Salt.MR.lemma12_on_TsetG_blockSupport` | Salt/MR/TLegPreamble.lean:202 | characters |
| `Salt.MR.cofactor_mvt_of_subset` | Salt/MR/TLegPreamble.lean:234 | characters |
| `Salt.MR.cofactor_mvt_sharp` | Salt/MR/TLegPreamble.lean:249 | characters |
| `Salt.MR.ramRrange_mass_le` | Salt/MR/TLegPreamble.lean:274 | characters |
| `Salt.MR.cofactor_mvt_mass_of_subset` | Salt/MR/TLegPreamble.lean:292 | characters |
| `Salt.MR.cofactor_mvt_sharp_exit` | Salt/MR/TLegPreamble.lean:309 | characters |
| `Salt.MR.exists_sharp_length` | Salt/MR/TLegPreamble.lean:331 | characters |
| `Salt.MR.cofactor_mvt_sharp_exit_visible` | Salt/MR/TLegPreamble.lean:350 | characters |
| `Salt.MR.cofactor_mvt_dyadic_lossy` | Salt/MR/TLegPreamble.lean:371 | characters |
| `Salt.MR.sum_exp_neg_graded` | Salt/MR/TLegPreamble.lean:404 | characters |
| `Salt.MR.sum_exp_neg_graded_rate` | Salt/MR/TLegPreamble.lean:433 | characters |
| `Salt.MR.sum_exp_neg_graded_card` | Salt/MR/TLegPreamble.lean:486 | characters |
| `Salt.MR.sum_exp_growth` | Salt/MR/TLegPreamble.lean:515 | characters |
| `Salt.MR.sum_exp_growth_top` | Salt/MR/TLegPreamble.lean:546 | characters |
| `Salt.MR.bandLterm_seamT0_le` | Salt/MR/ThmA2.lean:197 | characters |
| `Salt.MR.t0BandB_grade` | Salt/MR/ThmA2.lean:263 | characters |
| `Salt.MR.egap_small` | Salt/MR/ThmA2.lean:362 | characters |
| `Salt.MR.calFrameK_doorH1_at` | Salt/MR/ThmA2.lean:665 | characters |
| `Salt.MR.calFrameK_doorH1_at_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:556 | characters |
| `Salt.MR.exp_add_exp_sub_two_cos_le` | Salt/MR/ThmA2Open.lean:78 | characters |
| `Salt.MR.a3_prefactor_band_le_two` | Salt/MR/ThmA2Open.lean:92 | characters |
| `Salt.MR.a3_prefactor_max_le_three` | Salt/MR/ThmA2Open.lean:105 | characters |
| `Salt.MR.a3_logQ_third_mono` | Salt/MR/ThmA2Open.lean:120 | characters |
| `Salt.MR.a3_logQ_term_mono` | Salt/MR/ThmA2Open.lean:129 | characters |
| `Salt.MR.a3_head_le_third_grade` | Salt/MR/ThmA2Open.lean:137 | characters |
| `Salt.MR.parseval_a3_join` | Salt/MR/ThmA2Open.lean:164 | characters |
| `Salt.MR.far_of_mem_closedBall` | Salt/MR/ThmA2Open.lean:204 | characters |
| `Salt.MR.closedBall_subset_far` | Salt/MR/ThmA2Open.lean:212 | characters |
| `Salt.MR.ball_inf_floor_of_mem_far` | Salt/MR/ThmA2Open.lean:224 | characters |
| `Salt.MR.a2Mrow'_le_a2Mrow` | Salt/MR/ThmA2Prime.lean:70 | characters |
| `Salt.MR.seam_coef_contract_forces_vanishing` | Salt/MR/ThmA2Spine.lean:130 | characters |
| `Salt.MR.seam_coef_contract_absurd` | Salt/MR/ThmA2Spine.lean:160 | characters |
| `Salt.MR.far_tail_crude` | Salt/MR/ThmA2Spine.lean:212 | characters |
| `Salt.MR.regimeEnlargeX_self` | Salt/MR/TierSBand.lean:372 | characters |
| `Salt.MR.xTightCeil_nonneg` | Salt/MR/TierSBand.lean:394 | characters |
| `Salt.MR.xTightCeilArm_nonneg` | Salt/MR/TierSBand.lean:408 | characters |
| `Salt.MR.chowlaRegimeFlat_exists_param_gen_ceiling_mul_b9_tight` | Salt/MR/TierSBand.lean:420 | characters |
| `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride_g12b_band` | Salt/MR/TierSBand.lean:1619 | characters |
| `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride_g12b_of_band` | Salt/MR/TierSBand.lean:1908 | characters |
| `Salt.MR.bigXiAffU` | Salt/MR/TierSBandU.lean:58 | characters |
| `Salt.MR.bigXiAffD_subset_bigXiAffU` | Salt/MR/TierSBandU.lean:63 | characters |
| `Salt.MR.bigXiAffU_bounded_ceiling_of_pin_b9` | Salt/MR/TierSBandU.lean:74 | characters |
| `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride_g12b_band_bU` | Salt/MR/TierSBandU.lean:248 | characters |
| `Salt.MR.band_not_logChowlaFailsAff_g12b` | Salt/MR/TierSBridge.lean:94 | characters |
| `Salt.MR.band_Hhi_unbounded_g12b` | Salt/MR/TierSBridge.lean:173 | characters |
| `Salt.MR.class_scale_in_band` | Salt/MR/TierSLadder.lean:73 | characters |
| `Salt.MR.hah9_of_le_2310` | Salt/MR/TierSLadder.lean:87 | characters |
| `Salt.MR.ladder_placement` | Salt/MR/TierSLadder.lean:117 | characters |
| `Salt.MR.ladder_affFullRange_g12b` | Salt/MR/TierSLadder.lean:255 | characters |
| `Salt.MR.twinLogWeight_support_infinite_of_ladder` | Salt/MR/TierSLadder.lean:397 | characters |
| `Salt.MR.twinLogWeight_support_infinite_of_crown_g12b` | Salt/MR/TierSLadder.lean:427 | characters |
| `Salt.MR.socketBaseL_inhabited_at_twice_x` | Salt/MR/TierSSocket.lean:102 | characters |
| `Salt.MR.socketBaseLH_inhabited_at_twice_x` | Salt/MR/TierSSocket.lean:123 | characters |
| `Salt.MR.socketBaseLH_at_zero_false` | Salt/MR/TierSSocket.lean:149 | characters |
| `Salt.MR.thirtysecond_cap_to_SPartial` | Salt/MR/Transfer34.lean:118 | characters |
| `Salt.MR.thirtysecond_loglog_le_SPartial_div_32` | Salt/MR/Transfer34.lean:131 | characters |
| `Salt.MR.thirtysecond_cap_to_SPartial_293_descent` | Salt/MR/Transfer34.lean:164 | characters |
| `Salt.MR.budget_le_quarter` | Salt/MR/Transfer34.lean:214 | characters |
| `Salt.MR.exp_budget_le_34` | Salt/MR/Transfer34.lean:236 | characters |
| `Salt.MR.transfer_at_scale_34` | Salt/MR/Transfer34.lean:301 | characters |
| `Salt.MR.far_transfer_sup_34` | Salt/MR/Transfer34.lean:390 | characters |
| `Salt.MR.far_transfer_sup_34_of_pocket_cap` | Salt/MR/Transfer34.lean:548 | characters |
| `Salt.MR.farErr34_le_of_ambient_gate` | Salt/MR/Transfer34.lean:591 | characters |
| `Salt.MR.Rbd34_grade_priced` | Salt/MR/Transfer34.lean:659 | characters |
| `Salt.MR.Rbd34_grade_priced_of_ambient` | Salt/MR/Transfer34.lean:700 | characters |
| `Salt.MR.farErr34_at_TannGate_floor` | Salt/MR/Transfer34.lean:744 | characters |
| `Salt.MR.measurableSet_farRegion` | Salt/MR/TruncFactor.lean:66 | characters |
| `Salt.MR.measurableSet_farAbs` | Salt/MR/TruncFactor.lean:70 | characters |
| `Salt.MR.crossKerFar_nonneg` | Salt/MR/TruncFactor.lean:84 | characters |
| `Salt.MR.joint_inner_factor_trunc` | Salt/MR/TruncFactor.lean:130 | characters |
| `Salt.MR.joint_cs_factoring_trunc` | Salt/MR/TruncFactor.lean:200 | characters |
| `Salt.MR.kernel_far_mass` | Salt/MR/TruncFactor.lean:333 | characters |
| `Salt.MR.crossKerFar_le_tail` | Salt/MR/TruncFactor.lean:379 | characters |
| `Salt.MR.far_tail_absorb` | Salt/MR/TruncFactor.lean:435 | characters |
| `Salt.MR.crossKerFar_pin_le` | Salt/MR/TruncFactor.lean:477 | characters |
| `Salt.MR.center_dist_floor_trunc` | Salt/MR/TruncFactor.lean:504 | characters |
| `Salt.MR.center_dist_floor_compact` | Salt/MR/TruncFactor.lean:533 | characters |
| `Salt.MR.card_Icc_filter_dvd` | Salt/MR/TuranKubilius.lean:50 | characters |
| `Salt.MR.omega_eq_sum` | Salt/MR/TuranKubilius.lean:76 | characters |
| `Salt.MR.first_moment` | Salt/MR/TuranKubilius.lean:84 | characters |
| `Salt.MR.first_moment_le` | Salt/MR/TuranKubilius.lean:105 | characters |
| `Salt.MR.first_moment_ge` | Salt/MR/TuranKubilius.lean:113 | characters |
| `Salt.MR.second_moment_le` | Salt/MR/TuranKubilius.lean:157 | characters |
| `Salt.MR.variance_bound` | Salt/MR/TuranKubilius.lean:232 | characters |
| `Salt.MR.loglog_gap` | Salt/MR/TuranKubilius.lean:252 | characters |
| `Salt.MR.turan_kubilius` | Salt/MR/TuranKubilius.lean:288 | characters |
| `Salt.MR.near_norm_logDeriv_entire_le` | Salt/MR/TwistedEdge.lean:97 | characters |
| `Salt.MR.vk_char_box_growth_abs` | Salt/MR/TwistedEdge.lean:225 | characters |
| `Salt.MR.LFunction_crude_growth` | Salt/MR/TwistedEdge.lean:252 | characters |
| `Salt.MR.twisted_disc_engine` | Salt/MR/TwistedEdge.lean:296 | characters |
| `Salt.MR.twisted_zfree_of_margin` | Salt/MR/TwistedEdge.lean:377 | characters |
| `Salt.MR.twisted_edge_disc_core` | Salt/MR/TwistedEdge.lean:407 | characters |
| `Salt.MR.twistedEdgeLowConst_pos` | Salt/MR/TwistedEdge.lean:673 | characters |
| `Salt.MR.twisted_edge_moderate` | Salt/MR/TwistedEdge.lean:689 | characters |
| `Salt.MR.twisted_edge_price_strip` | Salt/MR/TwistedEdge.lean:879 | characters |
| `Salt.MR.twisted_dirichlet_cline` | Salt/MR/TwistedEdge.lean:962 | sieves, characters |
| `Salt.MR.norm_logDeriv_LFunction_cline_le` | Salt/MR/TwistedEdge.lean:999 | sieves, characters |
| `Salt.MR.logDeriv_LFunction_shift_differentiableOn` | Salt/MR/TwistedEdge.lean:1048 | characters |
| `Salt.MR.twisted_gate_of_height` | Salt/MR/TwistedEdge.lean:1090 | characters |
| `Salt.MR.twisted_window_price_gated_holds` | Salt/MR/TwistedEdge.lean:1107 | characters |
| `Salt.MR.densSieve_tail_le` | Salt/MR/TypicalDensity.lean:648 | sieves, characters |
| `Salt.MR.densGate_of_sqrt` | Salt/MR/TypicalDensity.lean:851 | characters |
| `Salt.MR.typical_density_le` | Salt/MR/TypicalDensity.lean:875 | characters |
| `Salt.MR.typical_density_union_le` | Salt/MR/TypicalDensity.lean:975 | characters |
| `Salt.MR.blockOmega_eq_zero_iff_coprime_bandProd` | Salt/MR/TypicalDensity.lean:1067 | characters |
| `Salt.MR.coprime_bandProd_of_blockOmega_zero` | Salt/MR/TypicalPrice.lean:99 | characters |
| `Salt.MR.blockfree_sum_le` | Salt/MR/TypicalPrice.lean:124 | characters |
| `Salt.MR.ramP2mass_win_le` | Salt/MR/TypicalPrice.lean:381 | characters |
| `Salt.MR.lemma12Rows_priced` | Salt/MR/TypicalPrice.lean:454 | characters |
| `Salt.MR.lemma12Rows_priced_ratio` | Salt/MR/TypicalPrice.lean:501 | characters |
| `Salt.MR.sum_lemma12Rows_priced` | Salt/MR/TypicalPrice.lean:555 | characters |
| `Salt.MR.log_calP_div_log_calQ` | Salt/MR/TypicalPrice.lean:600 | characters |
| `Salt.MR.sum_calibrated_ratio_eq` | Salt/MR/TypicalPrice.lean:616 | characters |
| `Salt.MR.calibrated_ratio_not_MR_shape` | Salt/MR/TypicalPrice.lean:632 | characters |
| `Salt.MR.calibrated_sum_ratio_ge_half` | Salt/MR/TypicalPrice.lean:648 | characters |
| `Salt.MR.sum_lemma12Rows_priced_calibrated` | Salt/MR/TypicalPrice.lean:666 | characters |
| `Salt.MR.lemma12Rows_pricedK` | Salt/MR/TypicalPriceK.lean:84 | characters |
| `Salt.MR.lemma12Rows_priced_ratioK` | Salt/MR/TypicalPriceK.lean:133 | characters |
| `Salt.MR.sum_lemma12Rows_pricedK` | Salt/MR/TypicalPriceK.lean:195 | characters |
| `Salt.MR.sum_lemma12Rows_priced_calibratedK2` | Salt/MR/TypicalPriceK.lean:253 | characters |
| `Salt.MR.sum_TS_add_TL` | Salt/MR/USetBalance.lean:84 | characters |
| `Salt.MR.uset_integral_to_branches` | Salt/MR/USetBalance.lean:105 | characters |
| `Salt.MR.sum_inv_sq_Icc_le` | Salt/MR/USetBalance.lean:232 | characters |
| `Salt.MR.block_sum_bound` | Salt/MR/USetBalance.lean:325 | characters |
| `Salt.MR.hU_exit_of_branches` | Salt/MR/USetBalance.lean:358 | characters |
| `Salt.MR.tL_block_weight` | Salt/MR/USetBalance.lean:383 | characters |
| `Salt.MR.mem_reflectChi` | Salt/MR/USetChi.lean:98 | characters |
| `Salt.MR.card_reflectChi` | Salt/MR/USetChi.lean:103 | characters |
| `Salt.MR.sum_reflectChi` | Salt/MR/USetChi.lean:107 | characters |
| `Salt.MR.reflectChi_subset_Icc` | Salt/MR/USetChi.lean:130 | characters |
| `Salt.MR.chiBarCoeff_div` | Salt/MR/USetChi.lean:152 | characters |
| `Salt.MR.blockSrc_chiBar` | Salt/MR/USetChi.lean:157 | characters |
| `Salt.MR.primeBlockPoly_chiBar_eq_dpolyChi` | Salt/MR/USetChi.lean:168 | characters |
| `Salt.MR.ramQsrc_chiBar` | Salt/MR/USetChi.lean:176 | characters |
| `Salt.MR.ramQ_chiBar_eq_spoly` | Salt/MR/USetChi.lean:186 | characters |
| `Salt.MR.ramQ_chiBar_eq_dpolyChi` | Salt/MR/USetChi.lean:194 | characters |
| `Salt.MR.ramQ_chiBar_eq_halaszSum` | Salt/MR/USetChi.lean:204 | characters |
| `Salt.MR.hybridblock_bound_mono` | Salt/MR/USetChi.lean:216 | characters |
| `Salt.MR.mem_UsetChi` | Salt/MR/USetChi.lean:282 | characters |
| `Salt.MR.tLsetChi_subset` | Salt/MR/USetChi.lean:420 | characters |
| `Salt.MR.mem_tLsetChi` | Salt/MR/USetChi.lean:424 | characters |
| `Salt.MR.ramRcoeff_chiBar` | Salt/MR/USetChiTS.lean:71 | characters |
| `Salt.MR.ramR_chiBar_eq_spoly` | Salt/MR/USetChiTS.lean:82 | characters |
| `Salt.MR.ramR_chiBar_eq_dpolyChi` | Salt/MR/USetChiTS.lean:90 | characters |
| `Salt.MR.ramRcoeff_chiBar_mass_le` | Salt/MR/USetChiTS.lean:98 | characters |
| `Salt.MR.thinBundleChi_nonneg` | Salt/MR/USetChiTS.lean:194 | characters |
| `Salt.MR.logpow_le_rpow_of_gate` | Salt/MR/USetChiTS.lean:289 | characters |
| `Salt.MR.logpow_gate_of_exp_floor` | Salt/MR/USetChiTS.lean:307 | characters |
| `Salt.MR.charDebit_le_rpow` | Salt/MR/USetChiTS.lean:346 | characters |
| `Salt.MR.mem_TsetSmallChi` | Salt/MR/USetChiTS.lean:421 | characters |
| `Salt.MR.TsetSmallChi_subset` | Salt/MR/USetChiTS.lean:427 | characters |
| `Salt.MR.tLsetChi_eq_filter_not` | Salt/MR/USetChiTS.lean:527 | characters |
| `Salt.MR.sum_TSChi_add_TLChi` | Salt/MR/USetChiTS.lean:537 | characters |
| `Salt.MR.mem_fibrePack` | Salt/MR/USetChiTS.lean:563 | characters |
| `Salt.MR.sum_fibrePack` | Salt/MR/USetChiTS.lean:577 | characters |
| `Salt.MR.usetChi_integral_to_branches` | Salt/MR/USetChiTS.lean:610 | characters |
| `Salt.MR.usetG_integral_to_branches` | Salt/MR/USetGradedBalance.lean:105 | characters |
| `Salt.MR.gradedPins_nondegenerate` | Salt/MR/USetGradedBalance.lean:136 | characters |
| `Salt.MR.hUG_exit_of_branches` | Salt/MR/USetGradedBalance.lean:408 | characters |
| `Salt.MR.pin2Gate_le_ballQuarterThreshold` | Salt/MR/USetGradedPrice.lean:90 | characters |
| `Salt.MR.Tstar2_window_mono` | Salt/MR/USetGradedPrice.lean:105 | characters |
| `Salt.MR.pocket_transport_pin2` | Salt/MR/USetGradedPrice.lean:148 | characters |
| `Salt.MR.damped_partial_transfer_34` | Salt/MR/USetGradedPrice.lean:203 | characters |
| `Salt.MR.cofactor_Rbd34_local` | Salt/MR/USetGradedPrice.lean:285 | characters |
| `Salt.MR.caseAS2_arm_priced` | Salt/MR/USetGradedPrice.lean:450 | characters |
| `Salt.MR.farErr34_le` | Salt/MR/USetGradedPrice.lean:521 | characters |
| `Salt.MR.farSupS34_le` | Salt/MR/USetGradedPrice.lean:548 | characters |
| `Salt.MR.cofactorRbd34loc_le_of_worst` | Salt/MR/USetGradedPrice.lean:559 | characters |
| `Salt.MR.Rbd34loc_uniform` | Salt/MR/USetGradedPrice.lean:581 | characters |
| `Salt.MR.Rbd34loc_grade_priced` | Salt/MR/USetGradedPrice.lean:632 | characters |
| `Salt.MR.Rbd34loc_grade_closes` | Salt/MR/USetGradedPrice.lean:690 | characters |
| `Salt.MR.thinBundleG_at_pin` | Salt/MR/USetGradedPrice.lean:739 | characters |
| `Salt.MR.thinBundleG_at_pin_Q` | Salt/MR/USetGradedPrice.lean:773 | characters |
| `Salt.MR.ramI_nonempty` | Salt/MR/USetGradedThin.lean:92 | characters |
| `Salt.MR.ramQbase_le_of_mem_ramI` | Salt/MR/USetGradedThin.lean:122 | characters |
| `Salt.MR.not_blockSmallG_witness_of_mem_UsetG` | Salt/MR/USetGradedThin.lean:160 | characters |
| `Salt.MR.gradeV_sq_le_rpow` | Salt/MR/USetGradedThin.lean:377 | characters |
| `Salt.MR.loglog_le_rpow` | Salt/MR/USetPins.lean:101 | characters |
| `Salt.MR.QJ_sq_subpoly` | Salt/MR/USetPins.lean:145 | characters |
| `Salt.MR.QJ_succ_sq_le_rpow` | Salt/MR/USetPins.lean:180 | characters |
| `Salt.MR.pin_Pii` | Salt/MR/USetPins.lean:242 | characters |
| `Salt.MR.pin_Pii_nat` | Salt/MR/USetPins.lean:255 | characters |
| `Salt.MR.pin_P83_le_Q83_of_gate` | Salt/MR/USetPins.lean:291 | characters |
| `Salt.MR.two_le_H83` | Salt/MR/USetPins.lean:299 | characters |
| `Salt.MR.TannGate_of_row_height` | Salt/MR/USetPins.lean:345 | characters |
| `Salt.MR.TannGate_fails_polylog_deg` | Salt/MR/USetPins.lean:394 | characters |
| `Salt.MR.balance_exit` | Salt/MR/USetPins.lean:432 | characters |
| `Salt.MR.exit_margin` | Salt/MR/USetPins.lean:475 | characters |
| `Salt.MR.exit_beats_c0` | Salt/MR/USetPins.lean:480 | characters |
| `Salt.MR.halved_fails` | Salt/MR/USetPins.lean:488 | characters |
| `Salt.MR.balance_exit_B4` | Salt/MR/USetPins.lean:500 | characters |
| `Salt.MR.loglog_absorb_B4` | Salt/MR/USetPins.lean:511 | characters |
| `Salt.MR.KS_priced` | Salt/MR/USetPrice.lean:120 | characters |
| `Salt.MR.KS_supplied` | Salt/MR/USetPrice.lean:156 | characters |
| `Salt.MR.cofactorRbd_le_of_worst` | Salt/MR/USetPrice.lean:244 | characters |
| `Salt.MR.Rbd_uniform` | Salt/MR/USetPrice.lean:267 | characters |
| `Salt.MR.ramI_card_le_pin` | Salt/MR/USetPrice.lean:322 | characters |
| `Salt.MR.floor_pin` | Salt/MR/USetPrice.lean:373 | characters |
| `Salt.MR.balance_priced_main` | Salt/MR/USetPrice.lean:407 | characters |
| `Salt.MR.rem_priced` | Salt/MR/USetPrice.lean:511 | characters |
| `Salt.MR.caseAS_arm_priced` | Salt/MR/USetResiduals.lean:227 | characters |
| `Salt.MR.farMain_priced` | Salt/MR/USetResiduals.lean:289 | characters |
| `Salt.MR.Rbd_grade_priced` | Salt/MR/USetResiduals.lean:326 | characters |
| `Salt.MR.farErr_le_of_ambient_gate` | Salt/MR/USetResiduals.lean:516 | characters |
| `Salt.MR.Rbd_grade_priced_of_ambient` | Salt/MR/USetResiduals.lean:571 | characters |
| `Salt.MR.ambient_cap_below_TannGate_floor` | Salt/MR/USetResiduals.lean:599 | characters |
| `Salt.MR.E_priced` | Salt/MR/USetResiduals.lean:624 | characters |
| `Salt.MR.E_priced_row_scale` | Salt/MR/USetResiduals.lean:647 | characters |
| `Salt.MR.EP2_gate_of_row` | Salt/MR/USetResiduals.lean:693 | characters |
| `Salt.MR.P2_route_64_over_Psq_insufficient` | Salt/MR/USetResiduals.lean:755 | characters |
| `Salt.MR.gate_Cq_CR` | Salt/MR/USetResiduals.lean:832 | characters |
| `Salt.MR.gate_KS_live_delta` | Salt/MR/USetResiduals.lean:849 | characters |
| `Salt.MR.gate_absorb_8640` | Salt/MR/USetResiduals.lean:923 | characters |
| `Salt.MR.numeral_gates_discharged` | Salt/MR/USetResiduals.lean:935 | characters |
| `Salt.MR.lemma12_meansq_on_subset` | Salt/MR/USetThin.lean:141 | characters |
| `Salt.MR.lemma12_meansq_on_subset_blockSupport` | Salt/MR/USetThin.lean:171 | characters |
| `Salt.MR.wellspaced_discretize` | Salt/MR/USetThin.lean:242 | characters |
| `Salt.MR.ramQ_eq_dpoly` | Salt/MR/USetThinTL.lean:150 | characters |
| `Salt.MR.ramQbase_le_pow_ten` | Salt/MR/USetThinTL.lean:332 | characters |
| `Salt.MR.ramQblock_inv_sum_le` | Salt/MR/USetThinTL.lean:407 | characters |
| `Salt.MR.tL_kill` | Salt/MR/USetThinTL.lean:545 | characters |
| `Salt.MR.ramR_eq_spoly` | Salt/MR/USetThinTS.lean:94 | characters |
| `Salt.MR.norm_ramMain_sq_le_of_small` | Salt/MR/USetThinTS.lean:178 | characters |
| `Salt.MR.dyadicPairs_card_le_exp` | Salt/MR/USetThinTS.lean:238 | characters |
| `Salt.MR.thin_sqrt_kill` | Salt/MR/USetThinTS.lean:303 | characters |
| `Salt.MR.ramRcoeff_mass_le` | Salt/MR/USetThinTS.lean:421 | characters |
| `Salt.MR.exp_neg_le_of_log_inv_le` | Salt/MR/V7A.lean:79 | characters |
| `Salt.MR.ks_rider_absorbed` | Salt/MR/V7A.lean:89 | characters |
| `Salt.MR.cs_floor_of_leaves` | Salt/MR/V7B.lean:71 | characters |
| `Salt.MR.per_pair_contour_floored` | Salt/MR/V7B.lean:102 | sieves, characters |
| `Salt.MR.halaszPrimesChi_pointwise_of_gates_bounded_cs` | Salt/MR/V7B.lean:1210 | characters |
| `Salt.MR.usetGChi_window_meansq_gated_family_perBlock_bounded_cs` | Salt/MR/V7B.lean:1237 | characters |
| `Salt.MR.usetGChi_row_exit_perChi_perBlock_bounded_cs` | Salt/MR/V7B.lean:1319 | characters |
| `Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree` | Salt/MR/V7B.lean:1676 | characters |
| `Salt.MR.logChowla2_ineffective_v6_csarm` | Salt/MR/V7B.lean:1839 | characters |
| `Salt.MR.flatDesignBase_sqrt_ge` | Salt/MR/V7C.lean:60 | characters |
| `Salt.MR.t0_arm_two_levels` | Salt/MR/V7C.lean:73 | characters |
| `Salt.MR.t0_arm_three_levels` | Salt/MR/V7C.lean:96 | characters |
| `Salt.MR.t0_arm_le_tolerance` | Salt/MR/V7C.lean:107 | characters |
| `Salt.MR.t0_arm_four_levels_fails` | Salt/MR/V7C.lean:121 | characters |
| `Salt.MR.logChowla2_ineffective_v6_T0arm` | Salt/MR/V7C.lean:177 | characters |
| `Salt.MR.logChowla2_ineffective_v7` | Salt/MR/V7E.lean:74 | characters |
| `Salt.MR.logChowla2_ineffective_v7_g0` | Salt/MR/V7E.lean:221 | characters |
| `Salt.MR.xceilRiderStrict_zero` | Salt/MR/V7Headline.lean:91 | characters |
| `Salt.MR.logChowla2_ineffective_v7_ksarm_g0` | Salt/MR/V7Headline.lean:157 | characters |
| `Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin` | Salt/MR/V7Ks.lean:244 | characters |
| `Salt.MR.logChowla2_ineffective_v7_ksarm` | Salt/MR/V7Ks.lean:437 | characters |
| `Salt.MR.logChowla2_ineffective_v7_of_ksarm` | Salt/MR/V7Ks.lean:567 | characters |
| `Salt.MR.cofkR_cushion_of_armVt` | Salt/MR/V7Rated.lean:162 | characters |
| `Salt.MR.cofkR_cofactorSupply_L_gk_rated` | Salt/MR/V7Rated.lean:241 | characters |
| `Salt.MR.logChowla2_v7_rated` | Salt/MR/V7Rated.lean:973 | characters |
| `Salt.MR.logChowla2_ineffective_v7_ksarm_g0_of_rated` | Salt/MR/V7Rated.lean:1112 | characters |
| `Salt.MR.cofkR_cofactorSupply_L_gk_rated_h` | Salt/MR/V7RatedH.lean:111 | characters |
| `Salt.MR.s16_baseScaleCapEnd_LH_of_xceil` | Salt/MR/V7RatedH.lean:825 | characters |
| `Salt.MR.klevF_capNumeral_h` | Salt/MR/V7RatedH.lean:935 | characters |
| `Salt.MR.s16_baseScaleCap96_LH_at_klevF` | Salt/MR/V7RatedH.lean:1028 | characters |
| `Salt.MR.logChowla2_v7_rated_h` | Salt/MR/V7RatedH.lean:1067 | characters |
| `Salt.MR.logChowla2_v7_rated_h_one` | Salt/MR/V7RatedH.lean:1220 | characters |
| `Salt.MR.klevF_capNumeral_h_b9` | Salt/MR/V7RatedH.lean:1319 | characters |
| `Salt.MR.cofkR_cofactorSupply_L_gk_rated_h_b9` | Salt/MR/V7RatedH.lean:1423 | characters |
| `Salt.MR.s16_baseScaleCap96_LH_at_klevF_b9` | Salt/MR/V7RatedH.lean:2112 | characters |
| `Salt.MR.norm_socketSum_eq_eR` | Salt/MR/VanDerCorput.lean:91 | characters |
| `Salt.MR.halasz_socket_large` | Salt/MR/VanDerCorput.lean:150 | characters |
| `Salt.MR.socketBlock_kusmin` | Salt/MR/VanDerCorput.lean:190 | characters |
| `Salt.MR.socketBlock_strip` | Salt/MR/VanDerCorput.lean:201 | characters |
| `Salt.MR.socket_hZ` | Salt/MR/VdCSocket.lean:501 | characters, exponential sums |
| `Salt.MR.norm_char_partial_sum_le` | Salt/MR/VkMidSharp.lean:96 | characters |
| `Salt.MR.norm_LFunction_le_logBound` | Salt/MR/VkMidSharp.lean:131 | characters |
| `Salt.MR.chi_Llower_341_height_sharp` | Salt/MR/VkMidSharp.lean:231 | characters |
| `Salt.MR.vkMidDebitSharp_nonneg` | Salt/MR/VkMidSharp.lean:275 | characters |
| `Salt.MR.capFreeFloor3_lamChi_unconditional_sharp` | Salt/MR/VkMidSharp.lean:389 | characters |
| `Salt.MR.capFreeFloor3_all_chi_vt` | Salt/MR/VkMidSharp.lean:418 | characters |
| `Salt.MR.capFreeFloor_all_chi_vt` | Salt/MR/VkMidSharp.lean:460 | characters |
| `Salt.MR.cffKVt_nonneg` | Salt/MR/VkMidSharp.lean:477 | characters |
| `Salt.MR.cffKVt_spec` | Salt/MR/VkMidSharp.lean:481 | characters |
| `Salt.MR.capFreeFloor3_liouChi_all_vt` | Salt/MR/VkMidSharp.lean:492 | characters |
| `Salt.MR.capFreeFloor3_margin_all_chi_vt` | Salt/MR/VkMidSharp.lean:505 | characters |
| `Salt.MR.capFreeFloor3_pieceDatum_vt` | Salt/MR/VkMidSharp.lean:559 | characters |
| `Salt.MR.vk_height_facts` | Salt/MR/VkTwistClose.lean:115 | characters |
| `Salt.MR.log_vkProfile` | Salt/MR/VkTwistClose.lean:128 | characters |
| `Salt.MR.chi_Llower_341_of_ub` | Salt/MR/VkTwistClose.lean:175 | characters |
| `Salt.MR.chi_Llower_341_height` | Salt/MR/VkTwistClose.lean:253 | characters |
| `Salt.MR.one_le_vkEulerCorr` | Salt/MR/VkTwistClose.lean:344 | characters |
| `Salt.MR.vkEulerCorr_pos` | Salt/MR/VkTwistClose.lean:354 | characters |
| `Salt.MR.norm_LFunction_le_vkEulerCorr` | Salt/MR/VkTwistClose.lean:363 | characters |
| `Salt.MR.vkTwistUB_of_primitive` | Salt/MR/VkTwistClose.lean:418 | characters |
| `Salt.MR.vkDebitConst_nonneg` | Salt/MR/VkTwistClose.lean:452 | characters |
| `Salt.MR.vkMidDebit_nonneg` | Salt/MR/VkTwistClose.lean:458 | characters |
| `Salt.MR.vk_debit_le` | Salt/MR/VkTwistClose.lean:524 | characters |
| `Salt.MR.vk_capfree_threshold` | Salt/MR/VkTwistClose.lean:638 | characters |
| `Salt.MR.vk_twist_block_le` | Salt/MR/VkTwistLadder.lean:90 | characters |
| `Salt.MR.vk_twist_head_le` | Salt/MR/VkTwistLadder.lean:266 | characters |
| `Salt.MR.char_sum_fourier_le` | Salt/MR/VkTwistLadder.lean:379 | characters |
| `Salt.MR.vk_twist_head_abs_le` | Salt/MR/VkTwistLadder.lean:496 | characters |
| `Salt.MR.vk_char_head_le` | Salt/MR/VkTwistLadder.lean:529 | characters |
| `Salt.MR.one_le_vkTwistConst` | Salt/MR/VkTwistLadder.lean:547 | characters |
| `Salt.MR.vkTwistConst_mono` | Salt/MR/VkTwistLadder.lean:553 | characters |
| `Salt.MR.vkProfile_mono` | Salt/MR/VkTwistLadder.lean:563 | characters |
| `Salt.MR.vk_LFunction_bridge_le_primitive` | Salt/MR/VkTwistLadder.lean:586 | characters |
| `Salt.MR.vkTwistUB_holds` | Salt/MR/VkTwistLadder.lean:762 | characters |
| `Salt.MR.capFreeFloor3_lamChi_unconditional` | Salt/MR/VkTwistLadder.lean:789 | characters |
| `Salt.MR.LFunction_zero_free_region_vk_pos` | Salt/MR/VkTwistRegion.lean:232 | characters |
| `Salt.MR.LFunction_inv_conj` | Salt/MR/VkTwistRegion.lean:306 | characters |
| `Salt.MR.LFunction_inv_conj_zero` | Salt/MR/VkTwistRegion.lean:365 | characters |
| `Salt.MR.LFunction_zero_free_region_vk` | Salt/MR/VkTwistRegion.lean:377 | characters |
| `Salt.MR.norm_LFunction_inv_cline_le` | Salt/MR/VkTwistRegionProbe.lean:67 | characters |
| `Salt.MR.LFunction_ratio_bound` | Salt/MR/VkTwistRegionProbe.lean:126 | characters |
| `Salt.MR.LFunction_keep_one_disc` | Salt/MR/VkTwistRegionProbe.lean:164 | characters |
| `Salt.MR.LFunction_drop_all_disc` | Salt/MR/VkTwistRegionProbe.lean:253 | characters |
| `Salt.MR.LFunction_zero_free_of_disc` | Salt/MR/VkTwistRegionProbe.lean:318 | characters |
| `Salt.MR.LFunction_region_of_uniform_growth` | Salt/MR/VkTwistRegionProbe.lean:394 | characters |
| `Salt.MR.LFunction_zero_free_width_law` | Salt/MR/VkTwistRegionProbe.lean:465 | characters |
| `Salt.MR.LFunction_zero_free_region_vk_shape` | Salt/MR/VkTwistRegionProbe.lean:672 | characters |
| `Salt.MR.zeta_strip_growth_explicit` | Salt/MR/VkTwistRegionReal.lean:68 | zeros, characters |
| `Salt.MR.zeta_box_growth_explicit` | Salt/MR/VkTwistRegionReal.lean:98 | zeros, characters |
| `Salt.MR.neg_re_logDeriv_trivChar_le_zeta` | Salt/MR/VkTwistRegionReal.lean:130 | zeros, characters |
| `Salt.MR.LFunction_real_zero_free_of_disc` | Salt/MR/VkTwistRegionReal.lean:210 | characters |
| `Salt.MR.LFunction_real_region_of_growth` | Salt/MR/VkTwistRegionReal.lean:305 | zeros, characters |
| `Salt.MR.LFunction_real_zero_free_region_vk_pos` | Salt/MR/VkTwistRegionReal.lean:523 | characters |
| `Salt.MR.LFunction_real_zero_free_region_vk` | Salt/MR/VkTwistRegionReal.lean:653 | characters |
| `Salt.MR.vk_twist_strip_sum_le` | Salt/MR/VkTwistStrip.lean:81 | characters |
| `Salt.MR.vk_twist_strip_abs_le` | Salt/MR/VkTwistStrip.lean:184 | characters |
| `Salt.MR.vk_char_strip_head_le` | Salt/MR/VkTwistStrip.lean:225 | characters |
| `Salt.MR.one_le_vkStripConst` | Salt/MR/VkTwistStrip.lean:241 | characters |
| `Salt.MR.vkTheta_le_thousandth` | Salt/MR/VkTwistStrip.lean:246 | characters |
| `Salt.MR.vk_char_strip_growth` | Salt/MR/VkTwistStrip.lean:267 | characters |
| `Salt.MR.vk_char_box_growth` | Salt/MR/VkTwistStrip.lean:372 | characters |
| `Salt.MR.band_second_moment_width` | Salt/MR/WidthGrade.lean:75 | characters |
| `Salt.MR.head_second_moment_grade_width` | Salt/MR/WidthGrade.lean:145 | sieves, characters |
| `Salt.MR.head_second_moment_grade_low_width` | Salt/MR/WidthGrade.lean:280 | sieves, characters |
| `Salt.MR.tail_lorentz_core` | Salt/MR/WidthGrade.lean:437 | characters |
| `Salt.MR.tail_lorentz_grade` | Salt/MR/WidthGrade.lean:541 | characters |
| `Salt.MR.band_weight_le_lorentz` | Salt/MR/WidthGrade.lean:622 | characters |
| `Salt.MR.crossKer_grade_width` | Salt/MR/WidthGrade.lean:679 | characters |
| `Salt.MR.line_moment_grade_width` | Salt/MR/WidthGrade.lean:908 | sieves, characters |
| `Salt.MR.line_moment_grade_low_width` | Salt/MR/WidthGrade.lean:933 | sieves, characters |
| `Salt.MR.crossKer_width_sigma_bound` | Salt/MR/WidthGrade.lean:1037 | characters |
| `Salt.MR.width_pin_gates` | Salt/MR/WidthGrade.lean:1247 | characters |
| `Salt.MR.crossKer_width_sigma_pin` | Salt/MR/WidthGrade.lean:1277 | characters |
| `Salt.MR.window_mass_product` | Salt/MR/WindowBridge.lean:143 | characters |
| `Salt.MR.window_bridge_shifted` | Salt/MR/WindowBridge.lean:227 | characters |
| `Salt.MR.window_bridge` | Salt/MR/WindowBridge.lean:322 | characters |
| `Salt.Entropy.Chowla.regime_outer_param_ceiling` | Salt/MR/XCeil.lean:185 | characters |
| `Salt.Entropy.Chowla.chowlaRegimeFlat_exists_param_gen_ceiling` | Salt/MR/XCeil.lean:386 | characters |
| `Salt.Entropy.Chowla.chowlaRegimeFlat_exists_param_head_ceiling` | Salt/MR/XCeil.lean:516 | characters |
| `Salt.Entropy.Chowla.flat_endpoint_loglog_gt_lever` | Salt/MR/XCeil.lean:546 | characters |
| `Salt.MR.s16_baseScaleCap96_L_of_xceil` | Salt/MR/XCeil.lean:584 | characters |
| `Salt.MR.s16_baseScaleCap96_L_supplied` | Salt/MR/XCeil.lean:645 | characters |
| `Salt.MR.flatA_endpoint_ceiling_misses_K_half` | Salt/MR/XCeil.lean:700 | characters |
| `Salt.MR.m4_exit_socket_split_sq_arc_forallX` | Salt/MR/XGapThread.lean:146 | sieves, characters |
| `Salt.MR.m4_exit_socket_split_sq_trivial_forallX` | Salt/MR/XGapThread.lean:188 | characters |
| `Salt.MR.xt_log_inv_rho_le` | Salt/MR/XThread.lean:213 | characters |
| `Salt.MR.xt_log_inv_rho_le_scaled` | Salt/MR/XThread.lean:263 | characters |
| `Salt.MR.xt_log_add_le` | Salt/MR/XThread.lean:304 | characters |
| `Salt.MR.s15Arm_log_le_scaled` | Salt/MR/XThread.lean:345 | characters |
| `Salt.MR.s15Arm_log_le` | Salt/MR/XThread.lean:543 | characters |
| `Salt.MR.xceil_arm_split_h` | Salt/MR/XThread.lean:1153 | characters |
| `Salt.MR.logChowla2_ineffective_v5` | Salt/MR/XThread.lean:1525 | characters |
| `Salt.MR.vkShallowWidthSharp_one` | Salt/MR/ZetaInvShallow.lean:81 | zeros, characters |
| `Salt.MR.exists_zetaShallowGate` | Salt/MR/ZetaInvShallow.lean:89 | zeros, characters |
| `Salt.MR.zeta_shallow_scales` | Salt/MR/ZetaInvShallow.lean:114 | zeros, characters |
| `Salt.MR.zeta_budget_log_bound` | Salt/MR/ZetaInvShallow.lean:155 | zeros, characters |
| `Salt.MR.mmuG_eq_zeta_inv'` | Salt/MR/ZetaInvShallow.lean:188 | zeros, characters |
| `Salt.MR.norm_mmuG_neg_im` | Salt/MR/ZetaInvShallow.lean:193 | zeros, characters |
| `Salt.MR.norm_Zc_lower_of_shallow_ball` | Salt/MR/ZetaInvShallow.lean:225 | zeros, characters |
| `Salt.MR.norm_Zc_ratio_le_of_shallow_ball` | Salt/MR/ZetaInvShallow.lean:348 | zeros, characters |
| `Salt.MR.norm_mmuG_shallow_far` | Salt/MR/ZetaInvShallow.lean:434 | zeros, characters |
| `Salt.MR.norm_mmuG_shallow_near` | Salt/MR/ZetaInvShallow.lean:539 | zeros, characters |
| `Salt.MR.zeta_no_zero_in_shallow_box` | Salt/MR/ZetaInvShallow.lean:568 | zeros, characters |
| `Salt.MR.zetaInvShallowVk_holds` | Salt/MR/ZetaInvShallow.lean:638 | zeros, characters |
| `Salt.MR.mmuChiRatePrincipal_holds` | Salt/MR/ZetaInvShallow.lean:888 | zeros, characters |
| `Salt.MR.zeta_lower_compact_mid` | Salt/MR/ZetaLowerAllT.lean:44 | zeros, characters |
| `Salt.MR.zeta_lower_small_t` | Salt/MR/ZetaLowerAllT.lean:103 | zeros, characters |
| `Salt.MR.zeta_lower_all_t_of_pow` | Salt/MR/ZetaLowerAllT.lean:185 | zeros, characters |
| `Salt.MR.zeta_lower_all_t` | Salt/MR/ZetaLowerAllT.lean:273 | zeros, characters |
| `Salt.MR.zeta_neg_re_logDeriv_ge` | Salt/MR/ZetaNegLogDerivLower.lean:53 | zeros, characters |
| `Salt.MR.zeta_pow_anchor` | Salt/MR/ZetaPowLower.lean:85 | zeros, characters |
| `Salt.MR.pow_region_width` | Salt/MR/ZetaPowLower.lean:94 | zeros, characters |
| `Salt.MR.zeta_dirichlet_re_le` | Salt/MR/ZetaPowLower.lean:104 | zeros, characters |
| `Salt.MR.hasDerivAt_log_norm_zeta` | Salt/MR/ZetaPowLower.lean:144 | zeros, characters |
| `Salt.MR.zeta_horiz_lower` | Salt/MR/ZetaPowLower.lean:198 | zeros, characters |
| `Salt.MR.zeta_pow_lower_far` | Salt/MR/ZetaPowLower.lean:247 | zeros, characters |
| `Salt.MR.near_norm_logDeriv_Zc_le` | Salt/MR/ZetaPowLower.lean:301 | zeros, characters |
| `Salt.MR.zeta_near_logDeriv_bound` | Salt/MR/ZetaPowLower.lean:781 | zeros, characters |
| `Salt.MR.zeta_near_bridge` | Salt/MR/ZetaPowLower.lean:843 | zeros, characters |
| `Salt.MR.zeta_pow_lower` | Salt/MR/ZetaPowLower.lean:902 | zeros, characters |
| `Salt.Maynard.bounded_gaps_from_eh_complete` | Salt/Maynard/Complete.lean:1472 | sieves |
| `Salt.Maynard.hdecomp_double` | Salt/Maynard/GehDecomp2.lean:165 | sieves |
| `Salt.Maynard.hshiu_wire_sharp` | Salt/Maynard/GehShiuWire.lean:84 | sieves |
| `Salt.Maynard.window_lambda_disc_le` | Salt/Maynard/GehSmallQEst.lean:194 | sieves |
| `tail_obligation_vP1` | Salt/Maynard/GehTail.lean:510 | sieves |
| `Salt.Maynard.windowPNT_holds` | Salt/Maynard/GehWindowPnt.lean:91 | sieves |
| `Salt.Maynard.ppLevel_holds` | Salt/Maynard/PpAssembly.lean:928 | sieves |
| `Salt.Maynard.s2_tensor_lower_closed` | Salt/Maynard/S2TensorClosed.lean:28 | sieves |
| `Salt.Mertens.integral_exp_neg_log` | Salt/Mertens/GammaIntegral.lean:34 | sieves |
| `Salt.Mertens.loglog_integral_asymp` | Salt/Mertens/GammaIntegral.lean:323 | sieves |
| `Salt.Mertens.neg_log_prod_eq` | Salt/Mertens/PrimePower.lean:130 | sieves |
| `Salt.Mertens.mertensB_nonneg` | Salt/Mertens/PrimePower.lean:155 | sieves |
| `Salt.Mertens.mertensB_tail_le` | Salt/Mertens/PrimePower.lean:188 | sieves |
| `Salt.Mertens.mertensB_le_two` | Salt/Mertens/PrimePower.lean:239 | sieves |
| `Salt.Mertens.mertens_second_sharp` | Salt/Mertens/Second.lean:216 | sieves |
| `Salt.Mertens.mertens_M_unique` | Salt/Mertens/Third.lean:83 | sieves |
| `Salt.Mertens.abel_primeZeta` | Salt/Mertens/Third.lean:414 | sieves |
| `Salt.Mertens.mertensM_eq_sub` | Salt/Mertens/Third.lean:653 | sieves |
| `Salt.Mertens.mertens_second_sharp'` | Salt/Mertens/Third.lean:679 | sieves |
| `Salt.Mertens.mertens_third_log` | Salt/Mertens/Third.lean:696 | sieves |
| `Salt.Mertens.mertens_third` | Salt/Mertens/Third.lean:743 | sieves |
| `Salt.Mertens.abs_prodFactor_sub_twinC2_le` | Salt/Mertens/TwinDensity.lean:201 | sieves |
| `Salt.Mertens.mertens_twin_density` | Salt/Mertens/TwinDensity.lean:290 | sieves |
| `Salt.Mertens.mertens_twin_density_singularSeries` | Salt/Mertens/TwinDensity.lean:389 | sieves |
| `Salt.Mertens.logZetaReal_eq` | Salt/Mertens/ZetaSide.lean:177 | zeros, sieves |
| `Salt.Mertens.primeZeta_tendsto` | Salt/Mertens/ZetaSide.lean:266 | zeros, sieves |
| `parityInv_S1_le_S2` | Salt/Parity/Instances.lean:37 | sieves, characters |
| `parityInv_twin_bar` | Salt/Parity/Instances.lean:45 | sieves |
| `parityInv_twin_gate_fails` | Salt/Parity/Instances.lean:53 | sieves |
| `parityInv_no_twin_weight` | Salt/Parity/Instances.lean:62 | sieves |
| `parityInv_noSiegel_iff` | Salt/Parity/Instances.lean:72 | sieves |
| `parityInv_chen_headline` | Salt/Parity/Instances.lean:79 | sieves |
| `parityInv_twin_almost_prime` | Salt/Parity/Instances.lean:86 | sieves |
| `parityInv_N6_2` | Salt/Parity/Instances.lean:93 | sieves |
| `parityInv_N5_3` | Salt/Parity/Instances.lean:99 | sieves |
| `parityInv_chen_second` | Salt/Parity/Instances.lean:106 | sieves |
| `Salt.Parity.parityInv_of_closed` | Salt/Parity/Z.lean:117 | sieves |
| `Salt.Parity.twinFree_twinMass` | Salt/Parity/Z.lean:137 | sieves |
| `Salt.Parity.twinMass_oneWeight_unbounded_iff` | Salt/Parity/Z.lean:149 | sieves |
| `Salt.Parity.oneWeight_mem` | Salt/Parity/Z.lean:460 | sieves |
| `Salt.Parity.twinFree_mem` | Salt/Parity/Z.lean:618 | sieves |
| `Salt.SW.norm_logDeriv_sub_sum_of_blaschke` | Salt/SW/BCBound.lean:153 | sieves |
| `Salt.SW.LFunction_norm_logDeriv_sub_sum` | Salt/SW/BCBound.lean:357 | sieves, characters |
| `Salt.SW.neg_re_logDeriv_le` | Salt/SW/BCBound.lean:403 | sieves |
| `Salt.SW.norm_logDeriv_le_of_bound_off_zeros` | Salt/SW/BCSup.lean:71 | sieves |
| `Salt.SW.norm_sub_le_of_norm_le_on_ball` | Salt/SW/BCSup.lean:119 | sieves |
| `Salt.SW.mem_of_LFunction_eq_zero` | Salt/SW/BCSup.lean:161 | sieves |
| `Salt.SW.multiplicity_eq_zeroMult` | Salt/SW/BCSup.lean:187 | sieves, characters |
| `Salt.SW.LFunction_partialFraction_remainder_diff` | Salt/SW/BCSup.lean:229 | sieves, characters |
| `Salt.SW.zeta_full_box_count` | Salt/SW/BoxCompose.lean:193 | sieves |
| `Salt.SW.zeta_local_density` | Salt/SW/BoxCompose.lean:201 | sieves |
| `Salt.SW.zeta_local_density_card` | Salt/SW/BoxCompose.lean:208 | zeros, sieves |
| `Salt.SW.Zc_sphere_bound_wide` | Salt/SW/BoxCount.lean:81 | sieves |
| `Salt.SW.zeta_box_divisor_le` | Salt/SW/BoxCount.lean:129 | sieves |
| `Salt.SW.zeta_box_count_half` | Salt/SW/BoxCount.lean:174 | zeros, sieves |
| `Salt.SW.zeta_analyticOrderAt_one_sub` | Salt/SW/BoxFold.lean:112 | zeros, sieves |
| `Salt.SW.zeta_zero_one_sub_iff` | Salt/SW/BoxFold.lean:124 | zeros, sieves |
| `Salt.SW.zeta_fe_factor_ne_zero` | Salt/SW/BoxFold.lean:138 | sieves |
| `Salt.SW.zeta_box_count_full` | Salt/SW/BoxFold.lean:206 | sieves |
| `Salt.SW.bvL_of_lt_one` | Salt/SW/BvL.lean:67 | sieves |
| `Salt.SW.innerG_eq_bvL` | Salt/SW/BvL.lean:79 | sieves, characters |
| `Salt.SW.abs_bvL_one_le` | Salt/SW/BvL.lean:178 | sieves |
| `Salt.SW.bvL_step` | Salt/SW/BvL.lean:247 | sieves |
| `Salt.SW.abs_bvL_le` | Salt/SW/BvL.lean:398 | sieves |
| `Salt.SW.innerG_eq_zero_of_not_squarefree` | Salt/SW/BvL.lean:481 | sieves |
| `Salt.SW.abs_innerG_le_sharp` | Salt/SW/BvL.lean:498 | sieves |
| `Salt.SW.bvWeight_eq_moebius_of_le` | Salt/SW/BvWeight.lean:83 | sieves, characters |
| `Salt.SW.bvWeight_eq_zero_of_gt` | Salt/SW/BvWeight.lean:113 | sieves |
| `Salt.SW.bvWeight_eq_of_mem` | Salt/SW/BvWeight.lean:120 | sieves, characters |
| `Salt.SW.sum_bvWeight_divisors_eq_zero` | Salt/SW/BvWeight.lean:141 | sieves |
| `Salt.SW.sum_bvWeight_divisors_one` | Salt/SW/BvWeight.lean:156 | sieves |
| `Salt.SW.sq_le_C_exp` | Salt/SW/CharDispatch.lean:41 | sieves, characters |
| `Salt.SW.E_shape_bound` | Salt/SW/CharDispatch.lean:71 | sieves, characters |
| `Salt.SW.psi1_char_bound` | Salt/SW/CharDispatch.lean:324 | sieves, characters |
| `Salt.SW.psi1_trivchar_bound` | Salt/SW/CharDispatch.lean:571 | sieves, characters |
| `Salt.SW.rectBI_eq_zero_of_differentiableOn` | Salt/SW/ContourShift.lean:104 | sieves |
| `Salt.SW.rectBI_dslope_eq_zero` | Salt/SW/ContourShift.lean:116 | sieves |
| `Salt.SW.rectBI_inv_eq_two_pi_I` | Salt/SW/ContourShift.lean:301 | sieves |
| `Salt.SW.rectBI_cif_eq` | Salt/SW/ContourShift.lean:341 | sieves |
| `Salt.SW.kernel_residue` | Salt/SW/ContourShift.lean:356 | sieves |
| `Salt.SW.sum_coprime_eq_moebius_multiples` | Salt/SW/CoprimeBV.lean:98 | sieves, characters |
| `Salt.SW.innerG_eq_coprime_sum` | Salt/SW/CoprimeBV.lean:184 | sieves, characters |
| `Salt.SW.log_le_sum_inv_Icc_floor` | Salt/SW/CoprimeHarmonic.lean:41 | sieves |
| `Salt.SW.exists_smooth_mul_coprime` | Salt/SW/CoprimeHarmonic.lean:48 | sieves |
| `Salt.SW.sum_inv_Icc_le_coprime_mul_smooth` | Salt/SW/CoprimeHarmonic.lean:77 | sieves |
| `Salt.SW.sum_inv_Icc_le_div_totient_mul_coprime` | Salt/SW/CoprimeHarmonic.lean:117 | sieves |
| `Salt.SW.sum_coprime_inv_le_zeta_two_mul_sqf` | Salt/SW/CoprimeHarmonic.lean:133 | sieves |
| `Salt.SW.sum_sf_coprime_inv_ge` | Salt/SW/CoprimeHarmonic.lean:172 | sieves |
| `Salt.SW.selHSum_ge_one` | Salt/SW/Crush.lean:42 | sieves, characters |
| `Salt.SW.selHSum_le_primorial` | Salt/SW/Crush.lean:55 | sieves, characters |
| `Salt.SW.selG_ge_partial_geom` | Salt/SW/Crush.lean:71 | sieves, characters |
| `Salt.SW.crush_pointwise` | Salt/SW/Crush.lean:155 | sieves |
| `Salt.SW.H_lower_of_parts` | Salt/SW/Crush.lean:177 | sieves, characters |
| `Salt.SW.crush_coverage` | Salt/SW/Crush.lean:226 | sieves, characters |
| `Salt.SW.selHSum_ge_dhA_div_sum` | Salt/SW/CrushC.lean:151 | sieves, characters |
| `Salt.SW.sum_divisors_eq_hyperbola_asymm` | Salt/SW/CrushE.lean:44 | sieves |
| `Salt.SW.dhAbel_hyperbola_asymm` | Salt/SW/CrushE.lean:165 | sieves, characters |
| `Salt.SW.dhAbel_leg1_cut_abs_le` | Salt/SW/CrushE.lean:202 | sieves, characters |
| `Salt.SW.dhAbel_inner_ge` | Salt/SW/CrushE.lean:413 | sieves, characters |
| `Salt.SW.dhAbel_inner_ge_err` | Salt/SW/CrushH.lean:48 | sieves, characters |
| `Salt.SW.H_lower` | Salt/SW/CrushH.lean:65 | sieves, characters |
| `Salt.SW.zfr_harvest` | Salt/SW/DHBal.lean:62 | sieves, characters |
| `Salt.SW.norm_bsum_kernel_zero_decay` | Salt/SW/DHBal.lean:116 | sieves, characters |
| `Salt.SW.dhA_mass_upper` | Salt/SW/DHBal.lean:203 | sieves, characters |
| `Salt.SW.sum_hyperbola_comm` | Salt/SW/DHBal.lean:404 | sieves |
| `Salt.SW.sum_abs_grahamGc_div_le` | Salt/SW/DHBal.lean:444 | sieves |
| `Salt.SW.dhA_mass_eq_char_count` | Salt/SW/DHBal2.lean:55 | sieves, characters |
| `Salt.SW.inner_coprime_eq` | Salt/SW/DHBal2.lean:85 | sieves, characters |
| `Salt.SW.dhA_mul_eq_sum` | Salt/SW/DHBal2.lean:106 | sieves, characters |
| `Salt.SW.inner_cop_swap` | Salt/SW/DHBal2.lean:167 | sieves, characters |
| `Salt.SW.dhA_mass_mul_eq_group` | Salt/SW/DHBal2.lean:200 | sieves, characters |
| `Salt.SW.dhA_mass_mul_le` | Salt/SW/DHBal2.lean:214 | sieves, characters |
| `Salt.SW.sqfree_card_divisors` | Salt/SW/DHBal2.lean:266 | sieves |
| `Salt.SW.sum_abs_grahamGc_sigmaSq_div_le` | Salt/SW/DHBal2.lean:277 | sieves |
| `Salt.SW.norm_riemannZeta_le` | Salt/SW/DHBalance.lean:116 | zeros, sieves |
| `Salt.SW.norm_dhIntegrand_le` | Salt/SW/DHBalance.lean:153 | sieves, characters |
| `Salt.SW.dh_repulsion_of_LFunction_one_lower` | Salt/SW/DHBalance.lean:196 | sieves, characters |
| `Salt.SW.LFunction_one_re_ge_partial` | Salt/SW/DHClose.lean:105 | sieves, characters |
| `Salt.SW.dh_repulsion_partial` | Salt/SW/DHClose.lean:154 | sieves, characters |
| `Salt.SW.selH_local_split` | Salt/SW/DHClose2.lean:47 | sieves, characters |
| `Salt.SW.one_sub_inv_pos` | Salt/SW/DHClose2.lean:57 | sieves |
| `Salt.SW.one_sub_chiRe_div_pos` | Salt/SW/DHClose2.lean:65 | sieves, characters |
| `Salt.SW.one_add_selG_eq_local_inv` | Salt/SW/DHClose2.lean:81 | sieves, characters |
| `Salt.SW.selHblock_divisors_eq` | Salt/SW/DHClose2.lean:107 | sieves, characters |
| `Salt.SW.dhExtractionW_regroup` | Salt/SW/DHClose2.lean:133 | sieves, characters |
| `Salt.SW.zetaHol_differentiable` | Salt/SW/DHContour.lean:110 | sieves |
| `Salt.SW.rectBI_zeta_shift_mul` | Salt/SW/DHContour.lean:217 | zeros, sieves |
| `Salt.SW.rectBI_zeta_LFunction_kernel` | Salt/SW/DHContour.lean:252 | zeros, sieves, characters |
| `Salt.SW.sum_rpow_neg_le` | Salt/SW/DHCore.lean:44 | sieves |
| `Salt.SW.T_em_real` | Salt/SW/DHCore.lean:90 | sieves |
| `Salt.SW.abs_zeta_re_le` | Salt/SW/DHCore.lean:132 | sieves |
| `Salt.SW.floor_div_mul_ge` | Salt/SW/DHCore.lean:159 | sieves |
| `Salt.SW.term_rpow_le` | Salt/SW/DHCore.lean:174 | sieves |
| `Salt.SW.natSqrt_le_sqrt` | Salt/SW/DHCore.lean:198 | sieves |
| `Salt.SW.natSqrt_mul_rpow_le` | Salt/SW/DHCore.lean:206 | sieves |
| `Salt.SW.sqrt_lt_two_natSqrt` | Salt/SW/DHCore.lean:217 | sieves |
| `Salt.SW.sqrt_pow_bound` | Salt/SW/DHCore.lean:236 | sieves |
| `Salt.SW.rpow_sub_le_tangent` | Salt/SW/DHCore.lean:263 | sieves |
| `Salt.SW.dhAbel_hyperbola` | Salt/SW/DHCore.lean:292 | sieves, characters |
| `Salt.SW.dhAbel_leg1_le` | Salt/SW/DHCore.lean:324 | sieves, characters |
| `Salt.SW.dhAbel_inner_le` | Salt/SW/DHCore.lean:578 | sieves, characters |
| `Salt.SW.unmoll_extraction_real` | Salt/SW/DHCore.lean:692 | sieves, characters |
| `Salt.SW.L1_lower_siegel` | Salt/SW/DHCore.lean:808 | sieves, characters |
| `Salt.SW.dhA_nonneg` | Salt/SW/DHDetector.lean:206 | sieves, characters |
| `Salt.SW.dhA_square_ge_one` | Salt/SW/DHDetector.lean:219 | sieves, characters |
| `Salt.SW.dhA_mass_floor_real` | Salt/SW/DHDetector.lean:264 | sieves, characters |
| `Salt.SW.dhA_hyperbola` | Salt/SW/DHDetector.lean:325 | sieves, characters |
| `Salt.SW.sum_mul_index_eq` | Salt/SW/DHExtract.lean:45 | sieves |
| `Salt.SW.kernel_abel_sum` | Salt/SW/DHExtract.lean:72 | sieves |
| `Salt.SW.sum_Icc_one_shift` | Salt/SW/DHExtract.lean:89 | sieves |
| `Salt.SW.sum_rpow_le_integral` | Salt/SW/DHExtract.lean:99 | sieves |
| `Salt.SW.chiRe_partial_at_zero_le` | Salt/SW/DHExtract.lean:131 | sieves, characters |
| `Salt.SW.norm_zeta_rho_le` | Salt/SW/DHExtractRho.lean:54 | zeros, sieves |
| `Salt.SW.norm_cpow_pos_floor_sub_le` | Salt/SW/DHExtractRho.lean:73 | sieves |
| `Salt.SW.dhAbel_hyperbola_rho` | Salt/SW/DHExtractRho.lean:117 | sieves, characters |
| `Salt.SW.emrho_perterm` | Salt/SW/DHExtractRho.lean:151 | zeros, sieves |
| `Salt.SW.clean_cpow_term` | Salt/SW/DHExtractRho.lean:215 | sieves |
| `Salt.SW.dhAbel_leg1_rho` | Salt/SW/DHExtractRho.lean:244 | sieves, characters |
| `Salt.SW.dhAbel_inner_rho` | Salt/SW/DHExtractRho.lean:447 | sieves, characters |
| `Salt.SW.kernel_abel_sum_real` | Salt/SW/DHExtractW.lean:61 | sieves |
| `Salt.SW.rpow_sub_le_tangent_upper` | Salt/SW/DHExtractW.lean:81 | sieves |
| `Salt.SW.dhAbel_inner_abs_le` | Salt/SW/DHExtractW.lean:113 | sieves, characters |
| `Salt.SW.sum_rpow_ge` | Salt/SW/DHExtractW.lean:212 | sieves |
| `Salt.SW.sum_rpow_sandwich` | Salt/SW/DHExtractW.lean:235 | sieves |
| `Salt.SW.unmoll_extraction_abs_real` | Salt/SW/DHExtractW.lean:293 | sieves, characters |
| `Salt.SW.inner_cop_swap_wt` | Salt/SW/DHExtractW.lean:491 | sieves, characters |
| `Salt.SW.weighted_char_count` | Salt/SW/DHExtractW.lean:527 | sieves, characters |
| `Salt.SW.dhA_kernel_reduction_inner` | Salt/SW/DHExtractW.lean:553 | sieves, characters |
| `Salt.SW.dhA_kernel_reduction` | Salt/SW/DHExtractW.lean:611 | sieves, characters |
| `Salt.SW.selWeight_ne_zero_squarefree` | Salt/SW/DHExtractW.lean:634 | sieves, characters |
| `Salt.SW.selWeight_ne_zero_le` | Salt/SW/DHExtractW.lean:640 | sieves, characters |
| `Salt.SW.gcW_selWeight_eq_zero_of_gt_sq` | Salt/SW/DHExtractW.lean:648 | sieves, characters |
| `Salt.SW.dhD0_scale_main` | Salt/SW/DHExtractW.lean:672 | sieves |
| `Salt.SW.dhD0_scale_err` | Salt/SW/DHExtractW.lean:683 | sieves |
| `Salt.SW.selHmul_collection` | Salt/SW/DHExtractW.lean:698 | sieves, characters |
| `Salt.SW.sum_gcW_selNu_eq_selMainTerm` | Salt/SW/DHExtractW.lean:774 | sieves, characters |
| `Salt.SW.omega_eq_primeFactors_card` | Salt/SW/DHExtractW.lean:874 | sieves |
| `Salt.SW.paircount` | Salt/SW/DHExtractW.lean:878 | sieves |
| `Salt.SW.pairkernel_per_m` | Salt/SW/DHExtractW.lean:895 | sieves |
| `Salt.SW.sum_gcW_pairkernel_le` | Salt/SW/DHExtractW.lean:926 | sieves, characters |
| `Salt.SW.dh_extraction_per_m` | Salt/SW/DHExtractW.lean:1010 | sieves, characters |
| `Salt.SW.dh_extraction_upper_W` | Salt/SW/DHExtractW.lean:1163 | sieves, characters |
| `Salt.SW.sum_moebius_mul_div_eq_one` | Salt/SW/DHMain.lean:61 | sieves, characters |
| `Salt.SW.abs_mwWeighted_le_one` | Salt/SW/DHMain.lean:97 | sieves |
| `Salt.SW.abs_sum_grahamTheta_div_le_one` | Salt/SW/DHMain.lean:218 | sieves |
| `Salt.SW.dhDetectorShift_regroup` | Salt/SW/DHMollified.lean:121 | sieves, characters |
| `Salt.SW.norm_shifted_detector_mollified_le` | Salt/SW/DHMollified.lean:356 | sieves, characters |
| `Salt.SW.dhDetector_floor` | Salt/SW/DHRepulsion.lean:112 | sieves, characters |
| `Salt.SW.dhDetector_mellin` | Salt/SW/DHRepulsion.lean:188 | sieves, characters |
| `Salt.SW.dhLSeries_identity` | Salt/SW/DHRepulsion.lean:239 | zeros, sieves, characters |
| `Salt.SW.psi1Chi_eq_sum_psi1AP` | Salt/SW/Defs.lean:83 | sieves, characters |
| `Salt.SW.psi1_fold` | Salt/SW/Defs.lean:123 | sieves, characters |
| `Salt.SW.psi1AP_nonneg` | Salt/SW/Defs.lean:177 | sieves |
| `Salt.SW.psi1AP_sandwich` | Salt/SW/Defs.lean:191 | sieves |
| `Salt.SW.psi1AP_sub_lower` | Salt/SW/Defs.lean:262 | sieves |
| `Salt.SW.psi1AP_sub_upper` | Salt/SW/Defs.lean:267 | sieves |
| `Salt.SW.neg_logDeriv_LSeries_eq_LSeries_twist` | Salt/SW/Defs.lean:279 | zeros, sieves, characters |
| `Salt.SW.log_39_37_lower` | Salt/SW/DensityCrude.lean:73 | sieves |
| `Salt.SW.windowConst_le_137` | Salt/SW/DensityCrude.lean:83 | sieves |
| `Salt.SW.efMultTotal_box_le` | Salt/SW/DensityCrude.lean:100 | sieves, characters |
| `Salt.SW.sum_range_inv_succ_eq_harmonic` | Salt/SW/DensityCrude.lean:181 | sieves |
| `Salt.SW.efMultHarmonic_box_le` | Salt/SW/DensityCrude.lean:201 | sieves, characters |
| `Salt.SW.zeroCountM_le` | Salt/SW/DensityCrude.lean:377 | zeros, sieves, characters |
| `Salt.SW.zeroCountM_density_crude` | Salt/SW/DensityCrude.lean:409 | zeros, sieves, characters |
| `Salt.SW.zeroCountM_density_log` | Salt/SW/DensityCrude.lean:459 | zeros, sieves, characters |
| `Salt.SW.zeroCountM_efHeight_le` | Salt/SW/DensityCrude.lean:478 | zeros, sieves, characters |
| `Salt.SW.zeroSum_rpow_le` | Salt/SW/DensityCrude.lean:526 | sieves, characters |
| `Salt.SW.efZeroSumM_norm_le` | Salt/SW/DensityCrude.lean:541 | sieves, characters |
| `Salt.SW.efZeroSumM_norm_le_harmonic` | Salt/SW/DensityCrude.lean:565 | sieves, characters |
| `Salt.SW.efZeroSumM_erase_norm_le_harmonic` | Salt/SW/DensityCrude.lean:585 | sieves, characters |
| `Salt.SW.efZeroSumM_spend_le` | Salt/SW/DensityCrude.lean:599 | sieves, characters |
| `Salt.SW.efZeroSumM_spend_at_efHeight` | Salt/SW/DensityCrude.lean:631 | sieves, characters |
| `Salt.SW.exists_gap_midpoint` | Salt/SW/DensityCrude.lean:686 | sieves |
| `Salt.SW.exists_contour_params` | Salt/SW/DensityCrude.lean:752 | sieves, characters |
| `Salt.SW.psi_explicit_sharpM_perZero_unsep` | Salt/SW/DensityCrude.lean:863 | sieves, characters |
| `Salt.SW.zeroCountM_density_logfree_low` | Salt/SW/DensityLogfree.lean:72 | zeros, sieves, characters |
| `Salt.SW.boxRep_mem` | Salt/SW/DensityLogfree.lean:199 | sieves, characters |
| `Salt.SW.boxIndex_mem_Icc` | Salt/SW/DensityLogfree.lean:207 | sieves, characters |
| `Salt.SW.zeroCountM_eq_sum_boxFibre` | Salt/SW/DensityLogfree.lean:231 | zeros, sieves, characters |
| `Salt.SW.boxFibre_subset_closedBall` | Salt/SW/DensityLogfree.lean:246 | sieves, characters |
| `Salt.SW.efMultTotal_boxFibre_le` | Salt/SW/DensityLogfree.lean:292 | sieves, characters |
| `Salt.SW.wellSpacedAt_parity_reps` | Salt/SW/DensityLogfree.lean:387 | sieves, characters |
| `Salt.SW.zeroCountM_le_box_bound_mul` | Salt/SW/DensityLogfree.lean:431 | zeros, sieves, characters |
| `Salt.SW.zeroCountM_eq_zero_of_one_le` | Salt/SW/DensityStrip.lean:83 | zeros, sieves, characters |
| `Salt.SW.zeroCountM_le_const_of_le` | Salt/SW/DensityStrip.lean:97 | zeros, sieves, characters |
| `Salt.SW.rpow_mul_le_rpow_of_le_150` | Salt/SW/DensityStrip.lean:115 | sieves |
| `Salt.SW.zeroCountM_density_logfree_strip` | Salt/SW/DensityStrip.lean:182 | zeros, sieves, characters |
| `Salt.SW.zeroCountM_density_logfree` | Salt/SW/DensityStrip.lean:271 | zeros, sieves, characters |
| `Salt.SW.vonMangoldt_mass_sdiff_le` | Salt/SW/EFSharp.lean:168 | sieves |
| `Salt.SW.psi1Chi_sub_eq` | Salt/SW/EFSharp.lean:216 | sieves, characters |
| `Salt.SW.psiChiR_sub_riesz_diff_le` | Salt/SW/EFSharp.lean:254 | sieves, characters |
| `Salt.SW.psi_sharp_of_riesz_bounds` | Salt/SW/EFSharp.lean:322 | sieves, characters |
| `Salt.SW.psi_sharp_riesz_at_height` | Salt/SW/EFSharp.lean:354 | sieves, characters |
| `Salt.SW.cpow_riesz_residue_desmooth` | Salt/SW/EFSharp.lean:396 | sieves |
| `Salt.SW.efRieszSum_diff_sub_efZeroSum_le` | Salt/SW/EFSharp.lean:482 | sieves |
| `Salt.SW.psi_explicit_sharp_of_riesz_residues` | Salt/SW/EFSharp.lean:526 | sieves, characters |
| `Salt.SW.LFunction_growth_sphere_wide` | Salt/SW/EFSharp.lean:589 | sieves, characters |
| `Salt.SW.log_four_M0Lbox_le` | Salt/SW/EFSharp.lean:631 | sieves |
| `Salt.SW.halfbox_subset_closedBall` | Salt/SW/EFSharp.lean:673 | sieves |
| `Salt.SW.LFunction_halfbox_zero_count` | Salt/SW/EFSharp.lean:698 | sieves, characters |
| `Salt.SW.analyticOrderAt_LFunction_ne_top` | Salt/SW/EFSharpMult.lean:91 | sieves, characters |
| `Salt.SW.analyticOrderAt_LFunction_eq` | Salt/SW/EFSharpMult.lean:103 | sieves, characters |
| `Salt.SW.zeroMult_eq_one` | Salt/SW/EFSharpMult.lean:108 | sieves, characters |
| `Salt.SW.one_le_zeroMult` | Salt/SW/EFSharpMult.lean:114 | sieves, characters |
| `Salt.SW.LFunction_local_factor` | Salt/SW/EFSharpMult.lean:128 | sieves, characters |
| `Salt.SW.efMultTotal_nonneg` | Salt/SW/EFSharpMult.lean:158 | sieves, characters |
| `Salt.SW.efRieszSumM_eq_of_simple` | Salt/SW/EFSharpMult.lean:163 | sieves, characters |
| `Salt.SW.efZeroSumM_eq_of_simple` | Salt/SW/EFSharpMult.lean:173 | sieves, characters |
| `Salt.SW.efMultTotal_eq_card_of_simple` | Salt/SW/EFSharpMult.lean:183 | sieves, characters |
| `Salt.SW.efZeroSumM_erase_split` | Salt/SW/EFSharpMult.lean:199 | sieves, characters |
| `Salt.SW.rectBI_const_mul` | Salt/SW/EFSharpMult.lean:211 | sieves |
| `Salt.SW.logDeriv_sub_const_pow` | Salt/SW/EFSharpMult.lean:219 | sieves |
| `Salt.SW.psi1_contour_shift_finsetM_gap` | Salt/SW/EFSharpMult.lean:260 | sieves, characters |
| `Salt.SW.psi1_contour_shift_finsetM` | Salt/SW/EFSharpMult.lean:905 | sieves, characters |
| `Salt.SW.efRieszSumM_diff_sub_efZeroSumM_le` | Salt/SW/EFSharpMult.lean:930 | sieves, characters |
| `Salt.SW.psi_explicit_sharpM_of_riesz_residues` | Salt/SW/EFSharpMult.lean:977 | sieves, characters |
| `Salt.SW.psi_explicit_sharpM` | Salt/SW/EFSharpMult.lean:1031 | sieves, characters |
| `Salt.SW.psi_sharp_at_efHeightM` | Salt/SW/EFSharpMult.lean:1066 | sieves, characters |
| `Salt.SW.efMultTotal_le_divisor` | Salt/SW/EFSharpMult.lean:1095 | sieves, characters |
| `Salt.SW.efMultTotal_halfbox_le` | Salt/SW/EFSharpMult.lean:1138 | sieves, characters |
| `Salt.SW.card_le_efMultTotal` | Salt/SW/EFSharpMult.lean:1150 | sieves, characters |
| `Salt.SW.efRieszSumM_diff_sub_efZeroSumM_le_perZero` | Salt/SW/EFSharpMult.lean:1176 | sieves, characters |
| `Salt.SW.psi_explicit_sharpM_of_riesz_residues_perZero` | Salt/SW/EFSharpMult.lean:1209 | sieves, characters |
| `Salt.SW.psi_explicit_sharpM_perZero` | Salt/SW/EFSharpMult.lean:1243 | sieves, characters |
| `Salt.SW.cpow_riesz_diff_norm_le` | Salt/SW/EFSharpMult.lean:1280 | sieves |
| `Salt.SW.efRieszSumM_diff_norm_le` | Salt/SW/EFSharpMult.lean:1329 | sieves, characters |
| `Salt.SW.efRieszSumM_diff_quotient_norm_le` | Salt/SW/EFSharpMult.lean:1366 | sieves, characters |
| `Salt.SW.psi_explicit_sharpM_perZero_box` | Salt/SW/EFSharpMult.lean:1396 | sieves, characters |
| `Salt.SW.psi_explicit_sharpM_box` | Salt/SW/EFSharpMult.lean:1433 | sieves, characters |
| `Salt.SW.rectBI_finsetSum` | Salt/SW/EFSharpZeros.lean:79 | zeros, sieves |
| `Salt.SW.psi1_contour_shift_finset` | Salt/SW/EFSharpZeros.lean:134 | zeros, sieves, characters |
| `Salt.SW.boxZeroSet_finite` | Salt/SW/EFSharpZeros.lean:770 | zeros, sieves, characters |
| `Salt.SW.mem_boxZeros` | Salt/SW/EFSharpZeros.lean:823 | zeros, sieves, characters |
| `Salt.SW.psi_explicit_sharp` | Salt/SW/EFSharpZeros.lean:849 | zeros, sieves, characters |
| `Salt.SW.psi_sharp_at_efHeight` | Salt/SW/EFSharpZeros.lean:879 | zeros, sieves, characters |
| `Salt.SW.zeta_zero_free_strip_sharp` | Salt/SW/EpsilonZero.lean:708 | zeros, sieves |
| `Salt.SW.zeta_zero_free_strip_sharp_bounded` | Salt/SW/EpsilonZero.lean:817 | zeros, sieves |
| `Salt.SW.zeta_zero_free_region_sharp` | Salt/SW/EpsilonZero.lean:833 | zeros, sieves |
| `Salt.SW.zeta_zero_free_region_sharp_bounded` | Salt/SW/EpsilonZero.lean:929 | zeros, sieves |
| `Salt.SW.landau_truncation` | Salt/SW/Estermann.lean:66 | sieves |
| `Salt.SW.estermannPositivity_core` | Salt/SW/Estermann.lean:244 | zeros, sieves |
| `Salt.SW.no_estermann_data_for_zero` | Salt/SW/EstermannInterface.lean:56 | sieves |
| `Salt.SW.zeta_nonpos` | Salt/SW/EstermannInterface.lean:112 | zeros, sieves |
| `Salt.SW.estermannInterface'` | Salt/SW/EstermannInterface.lean:231 | sieves |
| `Salt.SW.estermannInterface` | Salt/SW/EstermannInterface.lean:463 | sieves |
| `Salt.SW.estermannPositivity` | Salt/SW/EstermannInterface.lean:468 | sieves |
| `Salt.SW.eulerCorr_ne_zero` | Salt/SW/EulerBridge.lean:117 | sieves, characters |
| `Salt.SW.LFunction_eq_primitive_mul` | Salt/SW/EulerBridge.lean:128 | sieves, characters |
| `Salt.SW.logDeriv_LFunction_eq` | Salt/SW/EulerBridge.lean:145 | sieves, characters |
| `Salt.SW.LFunction_eq_zero_iff_primitive` | Salt/SW/EulerBridge.lean:183 | sieves, characters |
| `Salt.SW.norm_logDeriv_LFunction_sub_primitive_le` | Salt/SW/EulerBridge.lean:245 | sieves, characters |
| `Salt.SW.sqfree_rpow_prod` | Salt/SW/EulerEff.lean:54 | sieves |
| `Salt.SW.alpha_weighted_divprod` | Salt/SW/EulerEff.lean:64 | sieves |
| `Salt.SW.rankin_tail_le` | Salt/SW/EulerEff.lean:86 | sieves |
| `Salt.SW.squarefree_primorial` | Salt/SW/EulerEff.lean:135 | sieves |
| `Salt.SW.sqfree_le_eq_primorial_divisors` | Salt/SW/EulerEff.lean:148 | sieves |
| `Salt.SW.selHSum_eq_primorial_le` | Salt/SW/EulerEff.lean:160 | sieves, characters |
| `Salt.SW.selHFull_eq_zetaL` | Salt/SW/EulerEff.lean:172 | sieves, characters |
| `Salt.SW.selHFull_eq_add_tail` | Salt/SW/EulerEff.lean:180 | sieves, characters |
| `Salt.SW.selHSum_ge_full_sub_rankin` | Salt/SW/EulerEff.lean:191 | sieves, characters |
| `Salt.SW.selHSum_ge_zetaL_sub_rankin` | Salt/SW/EulerEff.lean:216 | sieves, characters |
| `Salt.SW.primorial_primeFactors` | Salt/SW/EulerEff.lean:234 | sieves |
| `Salt.SW.selHFull_eq_zeta_mul_L` | Salt/SW/EulerEff.lean:242 | sieves, characters |
| `Salt.SW.zeta_side_prod_eq` | Salt/SW/EulerLink.lean:39 | sieves |
| `Salt.SW.mertens_prod_pos` | Salt/SW/EulerLink.lean:45 | sieves |
| `Salt.SW.zeta_side_ge` | Salt/SW/EulerLink.lean:57 | sieves |
| `Salt.SW.psi1AP_main_bound` | Salt/SW/Fold.lean:157 | sieves |
| `Salt.SW.fourfold_vonMangoldt_nonneg` | Salt/SW/FourFold.lean:69 | sieves, characters |
| `Salt.SW.fourfoldCoeff_apply_one` | Salt/SW/FourFold.lean:93 | sieves, characters |
| `Salt.SW.fourfoldCoeff_nonneg` | Salt/SW/FourFold.lean:286 | sieves, characters |
| `Salt.SW.LSeriesSummable_fourfoldCoeff` | Salt/SW/FourFold.lean:310 | zeros, sieves, characters |
| `Salt.SW.LSeries_fourfoldCoeff_eq` | Salt/SW/FourFold.lean:330 | zeros, sieves, characters |
| `Salt.SW.changeLevel_quadratic` | Salt/SW/FourFold.lean:345 | sieves, characters |
| `Salt.SW.siegelWalfisz_holds` | Salt/SW/Gate.lean:150 | sieves |
| `Salt.SW.bounded_gaps_unconditional` | Salt/SW/Gate.lean:376 | sieves |
| `Salt.SW.sum_divisors_moebius_mul_log_div_eq` | Salt/SW/GrahamHard.lean:105 | sieves, characters |
| `Salt.SW.tailT_eq_zero_of_le` | Salt/SW/GrahamHard.lean:132 | sieves |
| `Salt.SW.log_mul_sum_grahamTheta_eq` | Salt/SW/GrahamHard.lean:145 | sieves |
| `Salt.SW.grahamW_le_two_mul_sq` | Salt/SW/GrahamHard.lean:186 | sieves |
| `Salt.SW.sum_vonMangoldt_sq_le` | Salt/SW/GrahamHard.lean:212 | sieves |
| `Salt.SW.grahamW_sum_le_low` | Salt/SW/GrahamHard.lean:256 | sieves |
| `Salt.SW.sum_sigmaQ_le` | Salt/SW/GrahamHard.lean:516 | sieves |
| `Salt.SW.sum_sigmaQ_div_le` | Salt/SW/GrahamHard.lean:557 | sieves |
| `Salt.SW.sum_inv_mul_log_sq_le` | Salt/SW/GrahamHard.lean:690 | sieves |
| `Salt.SW.sum_rpow_neg_half_log_sigmaQ_le` | Salt/SW/GrahamHard.lean:799 | sieves |
| `Salt.SW.abs_sum_moebius_le_div_log_pow` | Salt/SW/GrahamHard.lean:893 | sieves |
| `Salt.SW.sum_tailT_sq_eq` | Salt/SW/GrahamHard.lean:1161 | sieves, characters |
| `Salt.SW.abs_sum_moebius_div_le_inv_log_pow` | Salt/SW/GrahamHard.lean:1727 | sieves |
| `Salt.SW.summable_coprime_indicator` | Salt/SW/GrahamHard2.lean:109 | sieves |
| `Salt.SW.coprimeSeries_eq_of_primeFactors_eq` | Salt/SW/GrahamHard2.lean:131 | sieves |
| `Salt.SW.coprimeSeries_eq_mul_prime` | Salt/SW/GrahamHard2.lean:168 | sieves |
| `Salt.SW.coprimeSeries_mul_prod_eq` | Salt/SW/GrahamHard2.lean:269 | sieves |
| `Salt.SW.totient_div_mul_coprimeSeries_moebius_div_sq` | Salt/SW/GrahamHard2.lean:370 | sieves, characters |
| `Salt.SW.kappa_mul_of_coprime` | Salt/SW/GrahamHard2.lean:435 | sieves |
| `Salt.SW.summable_moebius_sq_div_kappa_totient` | Salt/SW/GrahamHard2.lean:485 | sieves, characters |
| `Salt.SW.div_totient_mul_coprimeSeries_inv_kappa_totient` | Salt/SW/GrahamHard2.lean:521 | sieves, characters |
| `Salt.SW.sum_moebius_sq_dvd_eq` | Salt/SW/GrahamHard2.lean:694 | sieves, characters |
| `Salt.SW.abs_card_coprime_sub_le` | Salt/SW/GrahamHard2.lean:804 | sieves |
| `Salt.SW.sqf_coprime_count_eq` | Salt/SW/GrahamHard2.lean:959 | sieves |
| `Salt.SW.sqf_coprime_sum_log_mul_log_eq` | Salt/SW/GrahamHard2.lean:1572 | sieves |
| `Salt.SW.log_rpow_le_rpow_quarter` | Salt/SW/GrahamHard2.lean:2062 | sieves |
| `Salt.SW.sum_moebius_div_mul_harmonic_eq` | Salt/SW/GrahamHard2.lean:2107 | sieves, characters |
| `Salt.SW.abs_sum_moebius_mul_log_floor_ratio_le` | Salt/SW/GrahamHard2.lean:2378 | sieves |
| `Salt.SW.abs_sum_moebius_div_mul_log_div_sub_one_le` | Salt/SW/GrahamHard2.lean:2919 | sieves |
| `Salt.SW.abs_sum_moebius_mul_log_div_add_one_le` | Salt/SW/GrahamHard2.lean:3231 | sieves |
| `Salt.SW.sum_coprime_moebius_eq_sum_smooth` | Salt/SW/GrahamHard2.lean:3444 | sieves, characters |
| `Salt.SW.sum_smooth_inv_le` | Salt/SW/GrahamHard2.lean:3632 | sieves |
| `Salt.SW.div_totient_sub_sum_smooth_inv_le` | Salt/SW/GrahamHard2.lean:4231 | sieves |
| `Salt.SW.abs_coprime_sum_moebius_div_le` | Salt/SW/GrahamHard2.lean:4401 | sieves |
| `Salt.SW.coprime_sum_moebius_div_log_eq` | Salt/SW/GrahamHard2.lean:4839 | sieves |
| `Salt.SW.sigmaQ_mul_le` | Salt/SW/GrahamHard2.lean:5332 | sieves |
| `Salt.SW.coprime_sum_moebius_div_kappa_le` | Salt/SW/GrahamHard2.lean:5482 | sieves |
| `Salt.SW.one_le_c0` | Salt/SW/GrahamHard2.lean:5918 | sieves |
| `Salt.SW.coprime_sum_moebius_div_kappa_log_eq` | Salt/SW/GrahamHard2.lean:6073 | sieves |
| `Salt.SW.coprime_sum_moebius_div_kappa_log_exists` | Salt/SW/GrahamHard2.lean:6607 | sieves |
| `Salt.SW.sum_filter_side_eq_sqfLogPair_sub` | Salt/SW/GrahamHard3.lean:153 | sieves, characters |
| `Salt.SW.sum_tailT_sq_eq_box` | Salt/SW/GrahamHard3.lean:335 | sieves, characters |
| `Salt.SW.abs_sqfLogPair_sub_le` | Salt/SW/GrahamHard3.lean:474 | sieves |
| `Salt.SW.abs_aKernel_sub_c0_le` | Salt/SW/GrahamHard3.lean:662 | sieves |
| `Salt.SW.sum_inv_mul_abs_aKernel_le` | Salt/SW/GrahamHard3.lean:818 | sieves |
| `Salt.SW.abs_bKernel_le` | Salt/SW/GrahamHard3.lean:1070 | sieves |
| `Salt.SW.sum_abs_bKernel_le` | Salt/SW/GrahamHard3.lean:1317 | sieves |
| `Salt.SW.sum_rpow_neg_half_sigmaQ_one_add_log_le` | Salt/SW/GrahamHard3.lean:1377 | sieves |
| `Salt.SW.sum_sum_errUpper_le` | Salt/SW/GrahamHard3.lean:1426 | sieves |
| `Salt.SW.sum_sum_errLower_le` | Salt/SW/GrahamHard3.lean:1595 | sieves |
| `Salt.SW.sum_rpow_neg_three_half_le` | Salt/SW/GrahamHard3.lean:1813 | sieves |
| `Salt.SW.sum_tailT_sq_le` | Salt/SW/GrahamHard3.lean:2194 | sieves |
| `Salt.SW.grahamW_sum_le_full` | Salt/SW/GrahamHard3.lean:2401 | sieves |
| `Salt.SW.sum_sq_sum_bvWeight_le_full` | Salt/SW/GrahamHard3.lean:2498 | sieves |
| `Salt.SW.sum_sq_sum_bvWeight_le_low` | Salt/SW/GrahamHard3.lean:2559 | sieves |
| `Salt.SW.grahamW_eq_sum_grahamGc` | Salt/SW/GrahamL2.lean:82 | sieves |
| `Salt.SW.abs_grahamGc_le` | Salt/SW/GrahamL2.lean:173 | sieves |
| `Salt.SW.graham_diagonalisation` | Salt/SW/GrahamL2.lean:230 | sieves |
| `Salt.SW.sum_totient_innerG_sq_le` | Salt/SW/GrahamMean.lean:148 | sieves |
| `Salt.SW.grahamW_sum_eq_floor` | Salt/SW/GrahamMean.lean:247 | sieves |
| `Salt.SW.sum_grahamGc_div_eq` | Salt/SW/GrahamMean.lean:283 | sieves |
| `Salt.SW.sum_abs_grahamTheta_le` | Salt/SW/GrahamMean.lean:364 | sieves |
| `Salt.SW.sum_abs_grahamGc_le` | Salt/SW/GrahamMean.lean:406 | sieves |
| `Salt.SW.grahamW_sum_le` | Salt/SW/GrahamMean.lean:483 | sieves |
| `Salt.SW.sum_sq_sum_bvWeight_le` | Salt/SW/GrahamMean.lean:582 | sieves |
| `Salt.SW.grahamTheta_floor` | Salt/SW/GrahamWeights.lean:131 | sieves |
| `Salt.SW.sum_abs_grahamTheta_rpow_le` | Salt/SW/GrahamWeights.lean:156 | sieves |
| `Salt.SW.LFunction_eq_growthSum` | Salt/SW/Growth.lean:359 | sieves |
| `Salt.SW.LFunction_growth` | Salt/SW/Growth.lean:400 | sieves, characters |
| `Salt.SW.LFunction_growth_sphere` | Salt/SW/Growth.lean:422 | sieves, characters |
| `Salt.SW.sum_divisors_eq_hyperbola_symm` | Salt/SW/Hyperbola.lean:55 | sieves |
| `Salt.SW.dhA_hyperbola_symm` | Salt/SW/Hyperbola.lean:184 | sieves, characters |
| `Salt.SW.abs_bvWeight_le_one` | Salt/SW/JutilaDetector.lean:128 | sieves |
| `Salt.SW.abs_sum_bvWeight_divisors_le_card` | Salt/SW/JutilaDetector.lean:155 | sieves |
| `Salt.SW.jutilaCoeff_zero` | Salt/SW/JutilaDetector.lean:162 | sieves, characters |
| `Salt.SW.jutilaCoeff_one` | Salt/SW/JutilaDetector.lean:166 | sieves, characters |
| `Salt.SW.jutilaCoeff_eq_zero_of_le` | Salt/SW/JutilaDetector.lean:176 | sieves, characters |
| `Salt.SW.jutilaFull_eq_add_detector` | Salt/SW/JutilaDetector.lean:181 | sieves, characters |
| `Salt.SW.norm_jutilaLocal_selbergPsi_le` | Salt/SW/JutilaDetector.lean:247 | sieves, characters |
| `Salt.SW.sum_Icc_rpow_neg_half_le` | Salt/SW/JutilaDetector.lean:309 | sieves |
| `Salt.SW.norm_jutilaM_selbergPsi_le` | Salt/SW/JutilaDetector.lean:324 | sieves, characters |
| `Salt.SW.sum_rFilter_inv_mul_rpow_le` | Salt/SW/JutilaDetector.lean:405 | sieves |
| `Salt.SW.norm_jutilaMollifier_le` | Salt/SW/JutilaDetector.lean:445 | sieves, characters |
| `Salt.SW.norm_jutilaCoeff_le` | Salt/SW/JutilaDetector.lean:472 | sieves, characters |
| `Salt.SW.LSeriesSummable_jutilaCoeff` | Salt/SW/JutilaDetector.lean:519 | zeros, sieves, characters |
| `Salt.SW.LSeries_jutilaCoeff_eq` | Salt/SW/JutilaDetector.lean:539 | zeros, sieves, characters |
| `Salt.SW.LSeries_mul_natCast_cpow_neg` | Salt/SW/JutilaDetector.lean:553 | zeros, sieves |
| `Salt.SW.summable_jutilaCoeff_kernel` | Salt/SW/JutilaDetector.lean:563 | sieves, characters |
| `Salt.SW.jutilaFull_eq_tsum` | Salt/SW/JutilaDetector.lean:587 | sieves, characters |
| `Salt.SW.jutilaFull_mellin` | Salt/SW/JutilaDetector.lean:605 | sieves, characters |
| `Salt.SW.jutilaDetector_mellin` | Salt/SW/JutilaDetector.lean:655 | sieves, characters |
| `Salt.SW.jutilaMollifier_differentiable` | Salt/SW/JutilaDetector.lean:669 | sieves, characters |
| `Salt.SW.jutilaPhi_differentiableOn` | Salt/SW/JutilaDetector.lean:698 | sieves, characters |
| `Salt.SW.jutilaPhi_zero` | Salt/SW/JutilaDetector.lean:734 | sieves, characters |
| `Salt.SW.dslope_jutilaPhi_eq` | Salt/SW/JutilaDetector.lean:739 | sieves, characters |
| `Salt.SW.rectBI_dslope_jutilaPhi_eq_zero` | Salt/SW/JutilaDetector.lean:747 | sieves, characters |
| `Salt.SW.norm_jutilaIntegrand_le` | Salt/SW/JutilaDetector.lean:768 | sieves, characters |
| `Salt.SW.norm_inv_denom2_le_abs_im_cube` | Salt/SW/JutilaDetector.lean:788 | sieves |
| `Salt.SW.norm_integral_jutilaIntegrand_edge_le` | Salt/SW/JutilaDetector.lean:807 | sieves, characters |
| `Salt.SW.norm_inv_denom2_cubic_le_of_min` | Salt/SW/JutilaDetector.lean:877 | sieves |
| `Salt.SW.integrable_inv_sq_add_sq_rpow` | Salt/SW/JutilaDetector.lean:960 | sieves |
| `Salt.SW.integrable_abs_mul_inv_sq_add_sq_rpow` | Salt/SW/JutilaDetector.lean:968 | sieves |
| `Salt.SW.integrable_jutilaIntegrand_line` | Salt/SW/JutilaDetector.lean:976 | sieves, characters |
| `Salt.SW.integral_jutilaIntegrand_shift` | Salt/SW/JutilaDetector.lean:1068 | sieves, characters |
| `Salt.SW.integral_inv_sq_add_sq` | Salt/SW/JutilaDetector.lean:1215 | sieves |
| `Salt.SW.integral_inv_sq_add_sq_rpow_le` | Salt/SW/JutilaDetector.lean:1229 | sieves |
| `Salt.SW.integral_abs_mul_inv_sq_add_sq_rpow_le` | Salt/SW/JutilaDetector.lean:1237 | sieves |
| `Salt.SW.norm_jutilaFull_le` | Salt/SW/JutilaDetector.lean:1244 | sieves, characters |
| `Salt.SW.jutilaDetector_floor_at_zero` | Salt/SW/JutilaDetector.lean:1392 | sieves, characters |
| `Salt.SW.div_totient_le_card_primeFactors_add_one` | Salt/SW/JutilaDetector.lean:1478 | sieves |
| `Salt.SW.card_primeFactors_le_log_div_log_two` | Salt/SW/JutilaDetector.lean:1508 | sieves |
| `Salt.SW.inv_log_le_totient_div` | Salt/SW/JutilaDetector.lean:1524 | sieves |
| `Salt.SW.f5_error_bound` | Salt/SW/JutilaDetector.lean:1536 | sieves |
| `Salt.SW.f5_exp_dominates` | Salt/SW/JutilaDetector.lean:1624 | sieves |
| `Salt.SW.f5_error_le_main` | Salt/SW/JutilaDetector.lean:1658 | sieves |
| `Salt.SW.jutilaDetector_floor_F5` | Salt/SW/JutilaDetector.lean:1708 | sieves, characters |
| `Salt.SW.jutilaDetector_eq_dirichletPolyChi` | Salt/SW/JutilaHalasz.lean:105 | sieves, characters |
| `Salt.SW.jutilaB_pos_of_ne_zero` | Salt/SW/JutilaHalasz.lean:125 | sieves |
| `Salt.SW.summable_jutilaB_series` | Salt/SW/JutilaHalasz.lean:147 | sieves, characters |
| `Salt.SW.sum_normSq_jutilaA_div_jutilaB_le` | Salt/SW/JutilaHalasz.lean:168 | sieves |
| `Salt.SW.sum_sq_sum_bvWeight_mul_rpow_le` | Salt/SW/JutilaHalasz.lean:461 | sieves |
| `Salt.SW.sq_sum_norm_jutilaDetector_le` | Salt/SW/JutilaHalasz.lean:585 | sieves, characters |
| `Salt.SW.jutilaDetector_floor_sum` | Salt/SW/JutilaHalasz.lean:615 | sieves, characters |
| `Salt.SW.jutilaDetector_floor_half_sum` | Salt/SW/JutilaHalasz.lean:655 | sieves, characters |
| `Salt.SW.integral_norm_resKernel_diag_le` | Salt/SW/JutilaHalasz.lean:743 | sieves |
| `Salt.SW.norm_integral_resKernel_offdiag_le` | Salt/SW/JutilaHalasz.lean:796 | sieves |
| `Salt.SW.halaszBTsum_jutilaB_exp_eq_sum` | Salt/SW/JutilaRatio.lean:64 | sieves, characters |
| `Salt.SW.continuous_jutilaB_exp` | Salt/SW/JutilaRatio.lean:83 | sieves |
| `Salt.SW.continuous_halaszB_sum_exp` | Salt/SW/JutilaRatio.lean:97 | sieves, characters |
| `Salt.SW.continuous_resKernel_exp` | Salt/SW/JutilaRatio.lean:107 | sieves |
| `Salt.SW.const_mul_le_integral_integral_of_le` | Salt/SW/JutilaRatio.lean:136 | sieves |
| `Salt.SW.jutilaB_zero` | Salt/SW/JutilaResidue.lean:255 | sieves |
| `Salt.SW.jutilaB_ofReal_eq` | Salt/SW/JutilaResidue.lean:259 | sieves |
| `Salt.SW.jutilaB_nonneg` | Salt/SW/JutilaResidue.lean:267 | sieves |
| `Salt.SW.jutilaB_eq_zero_of_le` | Salt/SW/JutilaResidue.lean:280 | sieves |
| `Salt.SW.jutilaB_eq_of_le` | Salt/SW/JutilaResidue.lean:293 | sieves |
| `Salt.SW.jutilaB_pos` | Salt/SW/JutilaResidue.lean:304 | sieves |
| `Salt.SW.resKernelFun_zero` | Salt/SW/JutilaResidue.lean:318 | sieves |
| `Salt.SW.resKernel_of_ne_zero` | Salt/SW/JutilaResidue.lean:321 | sieves |
| `Salt.SW.resKernel_zero` | Salt/SW/JutilaResidue.lean:330 | sieves |
| `Salt.SW.norm_resKernel_le_div` | Salt/SW/JutilaResidue.lean:364 | sieves |
| `Salt.SW.norm_resKernel_le_log` | Salt/SW/JutilaResidue.lean:415 | sieves |
| `Salt.SW.cpow_mul_resKernel_div` | Salt/SW/JutilaResidue.lean:497 | sieves |
| `Salt.SW.two_pow_card_primeFactors_le` | Salt/SW/JutilaResidue.lean:534 | sieves |
| `Salt.SW.norm_LFunctionTrivChar_le` | Salt/SW/JutilaResidue.lean:545 | zeros, sieves |
| `Salt.SW.norm_riemannZeta_le_of_half_le` | Salt/SW/JutilaResidue.lean:562 | zeros, sieves |
| `Salt.SW.norm_riemannZeta_half_le` | Salt/SW/JutilaResidue.lean:583 | zeros, sieves |
| `Salt.SW.norm_prod_one_sub_inv_le_one` | Salt/SW/JutilaResidue.lean:599 | sieves |
| `Salt.SW.summable_trivChar_kern2` | Salt/SW/JutilaResidue.lean:616 | sieves, characters |
| `Salt.SW.tsum_trivChar_mul_cpow_eq` | Salt/SW/JutilaResidue.lean:653 | sieves, characters |
| `Salt.SW.tsum_trivChar_kern2_eq_integral` | Salt/SW/JutilaResidue.lean:677 | sieves, characters |
| `Salt.SW.tsum_trivChar_kern2_diff_eq_integral` | Salt/SW/JutilaResidue.lean:748 | sieves, characters |
| `Salt.SW.resPhi_differentiableOn` | Salt/SW/JutilaResidue.lean:798 | sieves |
| `Salt.SW.resPhi_zero` | Salt/SW/JutilaResidue.lean:838 | sieves |
| `Salt.SW.resIntegrand_eq_dslope_div` | Salt/SW/JutilaResidue.lean:842 | sieves |
| `Salt.SW.dslope_resPhi_neg` | Salt/SW/JutilaResidue.lean:860 | sieves |
| `Salt.SW.rectBI_resPhi_dslope_div_eq` | Salt/SW/JutilaResidue.lean:894 | sieves |
| `Salt.SW.norm_resIntegrand_le` | Salt/SW/JutilaResidue.lean:938 | sieves |
| `Salt.SW.norm_integral_resIntegrand_edge_le` | Salt/SW/JutilaResidue.lean:983 | sieves |
| `Salt.SW.integrable_resIntegrand_line` | Salt/SW/JutilaResidue.lean:1085 | sieves |
| `Salt.SW.integral_resIntegrand_shift` | Salt/SW/JutilaResidue.lean:1196 | sieves |
| `Salt.SW.halaszBTsum_jutilaB_eq_sum` | Salt/SW/JutilaResidue.lean:1398 | sieves, characters |
| `Salt.SW.halaszBTsum_jutilaB_expand` | Salt/SW/JutilaResidue.lean:1417 | sieves, characters |
| `Salt.SW.halaszBTsum_jutilaB_eq` | Salt/SW/JutilaResidue.lean:1579 | sieves, characters |
| `Salt.SW.sum_rFilter_totient_div_sq_le` | Salt/SW/JutilaResidue.lean:1687 | sieves |
| `Salt.SW.sum_two_pow_card_primeFactors_le` | Salt/SW/JutilaResidue.lean:1700 | sieves |
| `Salt.SW.sum_rFilter_abs_hCoef_le` | Salt/SW/JutilaResidue.lean:1794 | sieves |
| `Salt.SW.norm_jutilaI_le` | Salt/SW/JutilaResidue.lean:1857 | sieves |
| `Salt.SW.kernel_identity` | Salt/SW/Kernel.lean:195 | sieves |
| `Salt.SW.kernel_sum_swap` | Salt/SW/Kernel.lean:254 | sieves |
| `Salt.SW.kern2_eq_sq_kern` | Salt/SW/Kernel2.lean:41 | sieves |
| `Salt.SW.continuous_kern2` | Salt/SW/Kernel2.lean:44 | sieves |
| `Salt.SW.hasMellin_kern2` | Salt/SW/Kernel2.lean:68 | sieves |
| `Salt.SW.s2_ne_zero` | Salt/SW/Kernel2.lean:107 | sieves |
| `Salt.SW.norm_inv_denom2_le` | Salt/SW/Kernel2.lean:111 | sieves |
| `Salt.SW.norm_inv_denom2_cubic_le` | Salt/SW/Kernel2.lean:132 | sieves |
| `Salt.SW.verticalIntegrable_mellin_kern2` | Salt/SW/Kernel2.lean:161 | sieves |
| `Salt.SW.kern2_value` | Salt/SW/Kernel2.lean:178 | sieves |
| `Salt.SW.kernel_identity_2` | Salt/SW/Kernel2.lean:185 | sieves |
| `Salt.SW.integrable_Fterm2` | Salt/SW/Kernel2.lean:215 | sieves |
| `Salt.SW.kernel_sum_swap_2` | Salt/SW/Kernel2.lean:246 | sieves |
| `Salt.SW.landau_neg_logDeriv_re_lower` | Salt/SW/LandauPage.lean:96 | sieves, characters |
| `Salt.SW.analyticOrderAt_eq_of_factorization` | Salt/SW/LandauPage.lean:155 | sieves |
| `Salt.SW.landau_one_exceptional_at` | Salt/SW/LandauPage.lean:192 | sieves, characters |
| `Salt.SW.landau_one_exceptional` | Salt/SW/LandauPage.lean:353 | sieves, characters |
| `Salt.SW.landau_one_exceptional_simple` | Salt/SW/LandauPage.lean:367 | sieves, characters |
| `Salt.SW.norm_reflectedFactor_eq_on_sphere` | Salt/SW/MaxModulus.lean:63 | sieves |
| `Salt.SW.LFunction_norm_logDeriv_sub_sum'` | Salt/SW/MaxModulus.lean:89 | sieves, characters |
| `Salt.SW.LSeries_moebius_eq_zeta_inv` | Salt/SW/MobiusRate.lean:82 | zeros, sieves |
| `Salt.SW.mmu1_eq_integral` | Salt/SW/MobiusRate.lean:187 | zeros, sieves |
| `Salt.SW.mmu_rectBI_eq_zero` | Salt/SW/MobiusRate.lean:229 | zeros, sieves |
| `Salt.SW.mmuRate_smoothed` | Salt/SW/MobiusRateClose.lean:784 | sieves |
| `Salt.SW.mmuRate_holds` | Salt/SW/MobiusRateClose.lean:1059 | sieves |
| `Salt.SW.mwWeighted_tendsto_zero` | Salt/SW/MoebiusDiv.lean:469 | sieves |
| `Salt.SW.abs_sum_moebius_div_mul_log_le` | Salt/SW/MoebiusLog.lean:206 | sieves |
| `Salt.SW.abs_sum_grahamTheta_div_le_inv_log` | Salt/SW/MoebiusLog.lean:334 | sieves |
| `Salt.SW.abs_mwWeighted_le_div_log` | Salt/SW/MoebiusRateSharp.lean:207 | sieves |
| `Salt.SW.neg_reLogDeriv_changeLevel_le` | Salt/SW/Page.lean:79 | sieves, characters |
| `Salt.SW.product_ne_one` | Salt/SW/Page.lean:143 | sieves, characters |
| `Salt.SW.page_positivity` | Salt/SW/Page.lean:253 | zeros, sieves, characters |
| `Salt.SW.page_cross_modulus` | Salt/SW/Page.lean:295 | sieves, characters |
| `Salt.SW.logDeriv_prod_pow` | Salt/SW/PartialFractions.lean:80 | sieves |
| `Salt.SW.LFunction_exists_factorization` | Salt/SW/PartialFractions.lean:111 | sieves, characters |
| `Salt.SW.LFunction_partialFraction` | Salt/SW/PartialFractions.lean:245 | sieves, characters |
| `Salt.SW.norm_logDeriv_sub_sum_le` | Salt/SW/PartialFractions.lean:321 | sieves |
| `Salt.SW.pseudoChar_one_right` | Salt/SW/PseudoChar.lean:48 | sieves, characters |
| `Salt.SW.pseudoChar_one_left` | Salt/SW/PseudoChar.lean:51 | sieves, characters |
| `Salt.SW.pseudoChar_of_coprime` | Salt/SW/PseudoChar.lean:54 | sieves, characters |
| `Salt.SW.pseudoChar_mul_right_of_coprime` | Salt/SW/PseudoChar.lean:58 | sieves, characters |
| `Salt.SW.gcd_mul_eq_gcd_mul_gcd_div` | Salt/SW/PseudoChar.lean:65 | sieves, characters |
| `Salt.SW.pseudoChar_mul_of_squarefree` | Salt/SW/PseudoChar.lean:83 | sieves, characters |
| `Salt.SW.pseudoChar_mul_left_of_coprime` | Salt/SW/PseudoChar.lean:93 | sieves, characters |
| `Salt.SW.pseudoChar_prime_left` | Salt/SW/PseudoChar.lean:103 | sieves, characters |
| `Salt.SW.abs_pseudoChar_le_sum_divisors` | Salt/SW/PseudoChar.lean:112 | sieves, characters |
| `Salt.SW.selbergPsi_isMultiplicative` | Salt/SW/PseudoChar.lean:125 | sieves, characters |
| `Salt.SW.selbergPsi_apply_prime` | Salt/SW/PseudoChar.lean:132 | sieves, characters |
| `Salt.SW.abs_selbergPsi_le` | Salt/SW/PseudoChar.lean:138 | sieves, characters |
| `Salt.SW.abs_pseudoChar_selbergPsi_le` | Salt/SW/PseudoChar.lean:147 | sieves, characters |
| `Salt.SW.pseudoChar_selbergPsi_prime_of_dvd` | Salt/SW/PseudoChar.lean:151 | sieves, characters |
| `Salt.SW.pseudoChar_selbergPsi_four_two_two` | Salt/SW/PseudoChar.lean:156 | sieves, characters |
| `Salt.SW.jutilaLocal_one` | Salt/SW/PseudoCharEuler.lean:70 | sieves, characters |
| `Salt.SW.jutilaLocal_prime` | Salt/SW/PseudoCharEuler.lean:73 | sieves, characters |
| `Salt.SW.jutilaLocal_mul_of_coprime` | Salt/SW/PseudoCharEuler.lean:77 | sieves, characters |
| `Salt.SW.norm_jutilaLocal_le` | Salt/SW/PseudoCharEuler.lean:83 | sieves, characters |
| `Salt.SW.LSeries_dvd_mul_eq` | Salt/SW/PseudoCharEuler.lean:103 | zeros, sieves, characters |
| `Salt.SW.LSeriesSummable_pseudoChar_twist` | Salt/SW/PseudoCharEuler.lean:143 | zeros, sieves, characters |
| `Salt.SW.LSeries_pseudoChar_twist_eq` | Salt/SW/PseudoCharEuler.lean:230 | zeros, sieves, characters |
| `Salt.SW.LSeries_jutila_coeff_eq` | Salt/SW/PseudoCharEuler.lean:256 | zeros, sieves, characters |
| `Salt.SW.LSeriesSummable_jutila_coeff` | Salt/SW/PseudoCharEuler.lean:333 | zeros, sieves, characters |
| `Salt.SW.LSeries_jutila_coeff_sum_eq` | Salt/SW/PseudoCharEuler.lean:344 | zeros, sieves, characters |
| `Salt.SW.hCoef_of_squarefree` | Salt/SW/PseudoCharH.lean:86 | sieves, characters |
| `Salt.SW.hCoef_of_not_squarefree` | Salt/SW/PseudoCharH.lean:90 | sieves, characters |
| `Salt.SW.hCoef_one` | Salt/SW/PseudoCharH.lean:93 | sieves, characters |
| `Salt.SW.hCoef_prime` | Salt/SW/PseudoCharH.lean:96 | sieves, characters |
| `Salt.SW.pseudoChar_prime_right` | Salt/SW/PseudoCharH.lean:102 | sieves, characters |
| `Salt.SW.hCoef_prime_of_not_dvd` | Salt/SW/PseudoCharH.lean:111 | sieves, characters |
| `Salt.SW.hCoef_isMultiplicative` | Salt/SW/PseudoCharH.lean:121 | sieves, characters |
| `Salt.SW.hCoef_eq_zero_of_not_dvd` | Salt/SW/PseudoCharH.lean:136 | sieves, characters |
| `Salt.SW.sum_divisors_eq_prod_primeFactors_of_squarefree_support` | Salt/SW/PseudoCharH.lean:160 | sieves, characters |
| `Salt.SW.sum_divisors_hCoef_mul_eq_prod` | Salt/SW/PseudoCharH.lean:194 | sieves, characters |
| `Salt.SW.sum_divisors_hCoef_div_eq_prod` | Salt/SW/PseudoCharH.lean:207 | sieves, characters |
| `Salt.SW.sum_divisors_abs_hCoef_eq_prod` | Salt/SW/PseudoCharH.lean:216 | sieves, characters |
| `Salt.SW.pseudoChar_eq_prod_primeFactors` | Salt/SW/PseudoCharH.lean:229 | sieves, characters |
| `Salt.SW.pseudoChar_mul_eq_sum_hCoef` | Salt/SW/PseudoCharH.lean:250 | sieves, characters |
| `Salt.SW.pseudoChar_mul_eq_sum_hCoef_filter` | Salt/SW/PseudoCharH.lean:284 | sieves, characters |
| `Salt.SW.hCoef_selbergPsi_prime` | Salt/SW/PseudoCharH.lean:325 | sieves, characters |
| `Salt.SW.hCoef_sum_div_eq` | Salt/SW/PseudoCharH.lean:336 | sieves, characters |
| `Salt.SW.hCoef_abs_sum_le` | Salt/SW/PseudoCharH.lean:391 | sieves, characters |
| `Salt.SW.psi1_eq_integral` | Salt/SW/Psi1Identity.lean:119 | zeros, sieves, characters |
| `Salt.SW.psi1_eq_integral_logDeriv` | Salt/SW/Psi1Identity.lean:191 | zeros, sieves, characters |
| `Salt.SW.psi1_transfer` | Salt/SW/Psi1Transfer.lean:176 | sieves, characters |
| `Salt.SW.psi1Chi_one_primitive` | Salt/SW/Psi1Transfer.lean:232 | sieves, characters |
| `Salt.SW.psi1_transfer_one` | Salt/SW/Psi1Transfer.lean:244 | sieves, characters |
| `Salt.SW.selberg_diag` | Salt/SW/SelAlgebra.lean:51 | sieves |
| `Salt.SW.selberg_diag_nonneg` | Salt/SW/SelAlgebra.lean:112 | sieves |
| `Salt.SW.rescale_inv_ge` | Salt/SW/SelAlgebra.lean:123 | sieves |
| `Salt.SW.selNu_inv_eq` | Salt/SW/SelOpt.lean:145 | sieves, characters |
| `Salt.SW.selCore_collapse` | Salt/SW/SelOpt.lean:259 | sieves, characters |
| `Salt.SW.selY_collapse` | Salt/SW/SelOpt.lean:360 | sieves, characters |
| `Salt.SW.selMainTerm_diag` | Salt/SW/SelOpt.lean:376 | sieves, characters |
| `Salt.SW.selberg_opt_eq` | Salt/SW/SelOpt.lean:440 | sieves, characters |
| `Salt.SW.partial_H_bound` | Salt/SW/SelOpt.lean:483 | sieves, characters |
| `Salt.SW.selweight_abs_le_one` | Salt/SW/SelOpt.lean:536 | sieves, characters |
| `Salt.SW.dhWeightSqW_one` | Salt/SW/SelWeight.lean:74 | sieves |
| `Salt.SW.dhCoeffW_one` | Salt/SW/SelWeight.lean:93 | sieves, characters |
| `Salt.SW.dhCoeffW_nonneg` | Salt/SW/SelWeight.lean:99 | sieves, characters |
| `Salt.SW.dhWeightSqW_eq_sum_gcW` | Salt/SW/SelWeight.lean:107 | sieves |
| `Salt.SW.gcW_eq_zero_of_not_squarefree` | Salt/SW/SelWeight.lean:156 | sieves |
| `Salt.SW.abs_gcW_le` | Salt/SW/SelWeight.lean:171 | sieves |
| `Salt.SW.sum_abs_gcW_sigmaSq_div_le` | Salt/SW/SelWeight.lean:204 | sieves |
| `Salt.SW.norm_dhCoeffW_term` | Salt/SW/SelWeight.lean:241 | sieves, characters |
| `Salt.SW.selH_pos` | Salt/SW/SelWeight.lean:260 | sieves, characters |
| `Salt.SW.selH_le_two` | Salt/SW/SelWeight.lean:272 | sieves, characters |
| `Salt.SW.selH_lt_of_prime` | Salt/SW/SelWeight.lean:284 | sieves, characters |
| `Salt.SW.selG_pos` | Salt/SW/SelWeight.lean:300 | sieves, characters |
| `Salt.SW.selGmul_pos` | Salt/SW/SelWeight.lean:311 | sieves, characters |
| `Salt.SW.selHSum_pos` | Salt/SW/SelWeight.lean:320 | sieves, characters |
| `Salt.SW.selWeight_apply_one` | Salt/SW/SelWeight.lean:350 | sieves, characters |
| `Salt.SW.tail_shift_to_beta0` | Salt/SW/SelWeight.lean:381 | sieves |
| `Salt.SW.psi1_contour_shift` | Salt/SW/ShiftAssembly.lean:478 | sieves, characters |
| `Salt.SW.norm_logDeriv_eulerCorr_trivChar_le` | Salt/SW/ShiftTrivChar.lean:131 | sieves, characters |
| `Salt.SW.norm_logDeriv_Zc_le_of_ball_dist` | Salt/SW/ShiftTrivChar.lean:186 | sieves, characters |
| `Salt.SW.psi1_contour_shift_trivchar` | Salt/SW/ShiftTrivChar.lean:425 | zeros, sieves, characters |
| `Salt.SW.psi1_contour_shift_trivchar_full` | Salt/SW/ShiftTrivChar.lean:922 | zeros, sieves, characters |
| `Salt.SW.norm_logDeriv_le_of_ball_dist` | Salt/SW/ShiftVariants.lean:45 | sieves, characters |
| `Salt.SW.rectBI_sub_of_edge_eq` | Salt/SW/ShiftVariants.lean:194 | sieves |
| `Salt.SW.psi1_contour_shift_exceptional` | Salt/SW/ShiftVariants.lean:230 | sieves, characters |
| `Salt.SW.LFunction_pos_of_one_lt` | Salt/SW/Siegel.lean:67 | sieves, characters |
| `Salt.SW.LFunction_apply_one_pos` | Salt/SW/Siegel.lean:98 | sieves, characters |
| `Salt.SW.fourfold_pos_of_one_lt` | Salt/SW/Siegel.lean:129 | zeros, sieves, characters |
| `Salt.SW.lambda_pos` | Salt/SW/Siegel.lean:146 | sieves, characters |
| `Salt.SW.siegel_dichotomy` | Salt/SW/Siegel.lean:227 | sieves, characters |
| `Salt.SW.siegel_L_one_extract` | Salt/SW/Siegel.lean:247 | sieves, characters |
| `Salt.SW.siegel_zero_free_of_exceptional_case` | Salt/SW/Siegel.lean:310 | sieves, characters |
| `Salt.SW.norm_eulerCorr_one_le` | Salt/SW/SiegelClose.lean:136 | sieves, characters |
| `Salt.SW.LFunction_norm_le_near_one` | Salt/SW/SiegelClose.lean:315 | sieves, characters |
| `Salt.SW.LFunction_apply_one_norm_le` | Salt/SW/SiegelClose.lean:389 | sieves, characters |
| `Salt.SW.norm_deriv_LFunction_near_one` | Salt/SW/SiegelClose.lean:406 | sieves, characters |
| `Salt.SW.LFunction_one_re_le_mvt_sharp` | Salt/SW/SiegelClose.lean:458 | sieves, characters |
| `Salt.SW.siegel_theorem` | Salt/SW/SiegelClose.lean:841 | sieves, characters |
| `Salt.SW.LFunction_one_re_le_mvt` | Salt/SW/SiegelFinal.lean:106 | sieves, characters |
| `Salt.SW.fourfold_disk_bound` | Salt/SW/SiegelFinal.lean:272 | sieves, characters |
| `Salt.SW.siegel_L_one_exceptional` | Salt/SW/SiegelFinal.lean:324 | sieves, characters |
| `Salt.SW.siegel_zero_free_exceptional` | Salt/SW/SiegelFinal.lean:440 | sieves, characters |
| `Salt.SW.tendsto_partialLSeries` | Salt/SW/StripConvergence.lean:372 | sieves |
| `Salt.SW.norm_LFunction_sub_partial_le_strip` | Salt/SW/StripConvergence.lean:438 | sieves |
| `Salt.SW.dhW_detector_floor_beta0` | Salt/SW/TBalClose.lean:43 | sieves, characters |
| `Salt.SW.dh_balance_beta0_real` | Salt/SW/TBalClose.lean:76 | sieves, characters |
| `Salt.SW.dh_extraction_upper_rho` | Salt/SW/TBalCompose.lean:489 | sieves, characters |
| `Salt.SW.norm_LFunction_one_eq_re` | Salt/SW/TBalFinal.lean:42 | sieves, characters |
| `Salt.SW.sum_mul_index_eq_rho` | Salt/SW/TBalFinal.lean:63 | sieves |
| `Salt.SW.kernel_abel_sum_rho` | Salt/SW/TBalFinal.lean:91 | sieves |
| `Salt.SW.cpow_unit_tangent_bound` | Salt/SW/TBalFinal.lean:121 | sieves |
| `Salt.SW.norm_ofReal_cpow_seg_le` | Salt/SW/TBalFinal.lean:198 | sieves |
| `Salt.SW.sum_cpow_sandwich_rho` | Salt/SW/TBalFinal.lean:227 | sieves |
| `Salt.SW.unmoll_extraction_rho` | Salt/SW/TBalFinal.lean:442 | sieves, characters |
| `Salt.SW.dhW_detector_floor_rho` | Salt/SW/TBalR7.lean:47 | sieves, characters |
| `Salt.SW.dh_balance` | Salt/SW/TBalR7.lean:100 | sieves, characters |
| `Salt.SW.tbal_tau_le_split` | Salt/SW/TBalR8.lean:50 | sieves |
| `Salt.SW.tbal_tau_le_split_k1` | Salt/SW/TBalR8.lean:97 | sieves |
| `Salt.SW.dh_master_ray` | Salt/SW/TBalR8.lean:127 | sieves, characters |
| `Salt.SW.exp_sub_one_le_e_mul` | Salt/SW/TBalR8.lean:250 | sieves |
| `Salt.SW.rpow_sub_one_le` | Salt/SW/TBalR8.lean:266 | sieves |
| `Salt.SW.neg_log_le_rpow` | Salt/SW/TBalR8.lean:279 | sieves |
| `Salt.SW.neg_log_le_rpow'` | Salt/SW/TBalR8.lean:290 | sieves |
| `Salt.SW.log_add_two_le_rpow_nine_tenths` | Salt/SW/TBalR8.lean:313 | sieves |
| `Salt.SW.ray_pow_bound` | Salt/SW/TBalR8.lean:361 | sieves |
| `Salt.SW.ray_pow_bound_conv` | Salt/SW/TBalR8.lean:409 | sieves |
| `Salt.SW.row_1x_cap` | Salt/SW/TBalR8.lean:447 | sieves |
| `Salt.SW.row_A_cap` | Salt/SW/TBalR8.lean:507 | sieves |
| `Salt.SW.row_A_cap_k1` | Salt/SW/TBalR8.lean:700 | sieves |
| `Salt.SW.row_rho_main_cap` | Salt/SW/TBalR8.lean:964 | sieves |
| `Salt.SW.row_rho_main_cap_k1` | Salt/SW/TBalR8.lean:1067 | sieves |
| `Salt.SW.logz_factor_le` | Salt/SW/TBalR8.lean:1176 | sieves |
| `Salt.SW.logz_factor_pow9_le` | Salt/SW/TBalR8.lean:1218 | sieves |
| `Salt.SW.row_Eβ_cap` | Salt/SW/TBalR8.lean:1252 | sieves |
| `Salt.SW.row_Eβ_cap_k1` | Salt/SW/TBalR8.lean:1408 | sieves |
| `Salt.SW.row_Eρ_cap` | Salt/SW/TBalR8.lean:1586 | sieves |
| `Salt.SW.tbal_hguard` | Salt/SW/TBalR8.lean:1702 | sieves |
| `Salt.SW.tbal_hscale` | Salt/SW/TBalR8.lean:1738 | sieves |
| `Salt.SW.tbal_hcov` | Salt/SW/TBalR8.lean:1825 | sieves |
| `Salt.SW.C2Rho_le` | Salt/SW/TBalR8.lean:2027 | sieves |
| `Salt.SW.dh_repulsion_ordered` | Salt/SW/TBalR8.lean:2514 | sieves, characters |
| `Salt.SW.zeta_partial_em_free` | Salt/SW/TBalTall.lean:79 | zeros, sieves |
| `Salt.SW.norm_zeta_rho_le_tall` | Salt/SW/TBalTall.lean:107 | zeros, sieves |
| `Salt.SW.emrho_perterm_tall` | Salt/SW/TBalTall.lean:124 | zeros, sieves |
| `Salt.SW.dhAbel_leg1_rho_tall` | Salt/SW/TBalTall.lean:190 | sieves, characters |
| `Salt.SW.dhAbel_inner_rho_tall` | Salt/SW/TBalTall.lean:392 | sieves, characters |
| `Salt.SW.unmoll_extraction_rho_tall` | Salt/SW/TBalTall.lean:523 | sieves, characters |
| `Salt.SW.dh_extraction_upper_rho_tall` | Salt/SW/TBalTall.lean:1193 | sieves, characters |
| `Salt.SW.dh_master_ray_tall` | Salt/SW/TBalTall.lean:1326 | sieves, characters |
| `Salt.SW.C2Rho_le_tall` | Salt/SW/TBalTall.lean:1463 | sieves |
| `Salt.SW.row_Eρ_cap_tall` | Salt/SW/TBalTall.lean:1579 | sieves |
| `Salt.SW.row_Eρ_cap_tall_k1` | Salt/SW/TBalTall.lean:1711 | sieves |
| `Salt.SW.dh_repulsion_tall` | Salt/SW/TBalTall.lean:2725 | sieves, characters |
| `Salt.SW.dh_repulsion_tall_of_floor` | Salt/SW/TBalTall.lean:2861 | sieves, characters |
| `Salt.SW.dh_repulsion_k1_of_floor` | Salt/SW/TBalTall.lean:2971 | sieves, characters |
| `Salt.SW.boxZeros_re_le_at_efHeight` | Salt/SW/TBalTall.lean:3128 | sieves, characters |
| `Salt.SW.zetaHol_norm_le_of_lt` | Salt/SW/TauExt.lean:95 | sieves |
| `Salt.SW.zetaHol_norm_le` | Salt/SW/TauExt.lean:121 | sieves |
| `Salt.SW.zetaHol_bound_tall` | Salt/SW/TauExt.lean:152 | sieves |
| `Salt.SW.zetaHol_bound_five` | Salt/SW/TauExt.lean:162 | sieves |
| `Salt.SW.repulsion_ceiling_of_contract` | Salt/SW/TauExt.lean:182 | sieves |
| `Salt.SW.repulsionCeiling_mono` | Salt/SW/TauExt.lean:208 | sieves |
| `Salt.SW.boxZeros_re_le_of_repulsion` | Salt/SW/TauExt.lean:259 | sieves, characters |
| `Salt.SW.efZeroSumM_spend_at_repulsion` | Salt/SW/TauExt.lean:306 | sieves, characters |
| `Salt.SW.boxZeros_re_le_unit_box` | Salt/SW/TauExt.lean:340 | sieves, characters |
| `Salt.SW.three_four_one_termwise` | Salt/SW/ThreeFourOne.lean:76 | zeros, sieves, characters |
| `Salt.SW.three_four_one` | Salt/SW/ThreeFourOne.lean:137 | zeros, sieves, characters |
| `Salt.SW.three_four_one_logDeriv` | Salt/SW/ThreeFourOne.lean:180 | zeros, sieves, characters |
| `Salt.SW.LFunction_center_lower` | Salt/SW/ZeroCount.lean:99 | zeros, sieves, characters |
| `Salt.SW.LFunction_zero_count_le` | Salt/SW/ZeroCount.lean:179 | zeros, sieves, characters |
| `Salt.SW.norm_deriv_le_of_re_le` | Salt/SW/ZeroCount.lean:230 | zeros, sieves |
| `Salt.SW.LFunction_zero_count_near_one` | Salt/SW/ZeroCountNearOne.lean:98 | zeros, sieves, characters |
| `Salt.SW.LFunction_zero_count_near_one_guarded` | Salt/SW/ZeroCountNearOne.lean:260 | zeros, sieves, characters |
| `Salt.SW.landau_neg_logDeriv_re_lower_of_re` | Salt/SW/ZeroCountNearOne.lean:337 | zeros, sieves, characters |
| `Salt.SW.re_one_div_sub_ge_at_height` | Salt/SW/ZeroCountNearOne.lean:395 | zeros, sieves |
| `Salt.SW.LFunction_zero_count_near_one_at_height` | Salt/SW/ZeroCountNearOne.lean:418 | zeros, sieves, characters |
| `Salt.SW.LFunction_zero_count_near_one_at_height_guarded` | Salt/SW/ZeroCountNearOne.lean:579 | zeros, sieves, characters |
| `Salt.SW.zero_free_region_primitive` | Salt/SW/ZeroFree.lean:258 | zeros, sieves, characters |
| `Salt.SW.zero_free_region` | Salt/SW/ZeroFree.lean:387 | zeros, sieves, characters |
| `Salt.SW.LFunction_conj` | Salt/SW/ZeroFreeReal.lean:74 | zeros, sieves, characters |
| `Salt.SW.neg_re_logDeriv_trivChar_complex_le` | Salt/SW/ZeroFreeReal.lean:148 | zeros, sieves, characters |
| `Salt.SW.zero_free_region_real` | Salt/SW/ZeroFreeReal.lean:388 | zeros, sieves, characters |
| `Salt.SW.zero_free_region_all` | Salt/SW/ZeroFreeReal.lean:605 | zeros, sieves, characters |
| `Salt.SW.zero_free_region_all'` | Salt/SW/ZeroFreeReal.lean:642 | zeros, sieves, characters |
| `Salt.SW.zetaApprox_strip` | Salt/SW/ZetaEM.lean:48 | zeros, sieves |
| `Salt.SW.norm_zeta_sub_approx_le_strip` | Salt/SW/ZetaEM.lean:109 | zeros, sieves |
| `Salt.SW.zeta_partial_em` | Salt/SW/ZetaEM.lean:123 | zeros, sieves |
| `Salt.SW.zetaHol_bound` | Salt/SW/ZetaEM.lean:152 | zeros, sieves |
| `Salt.SW.Zc_patch_lower` | Salt/SW/ZetaInvShallow.lean:58 | zeros, sieves |
| `Salt.SW.zeta_inv_shallow` | Salt/SW/ZetaInvShallow.lean:121 | zeros, sieves |
| `Salt.SW.tail_psum_le` | Salt/SW/ZetaLogBound.lean:69 | zeros, sieves |
| `Salt.SW.zeta_log_bound` | Salt/SW/ZetaLogBound.lean:123 | zeros, sieves |
| `Salt.SW.zeta_norm_le_zc` | Salt/SW/ZetaLowerShallow.lean:47 | zeros, sieves |
| `Salt.SW.zeta_real_upper` | Salt/SW/ZetaLowerShallow.lean:62 | zeros, sieves |
| `Salt.SW.zeta_anchor` | Salt/SW/ZetaLowerShallow.lean:105 | zeros, sieves |
| `Salt.SW.zeta_deriv_bound` | Salt/SW/ZetaLowerShallow.lean:193 | zeros, sieves |
| `Salt.SW.zeta_lower_shallow` | Salt/SW/ZetaLowerShallow.lean:328 | zeros, sieves |
| `Salt.SW.neg_logDeriv_zeta_split` | Salt/SW/ZetaPartialFractions.lean:98 | zeros, sieves |
| `Salt.SW.entire_zero_count_le` | Salt/SW/ZetaPartialFractions.lean:134 | zeros, sieves |
| `Salt.SW.entire_norm_logDeriv_sub_sum'` | Salt/SW/ZetaPartialFractions.lean:171 | zeros, sieves |
| `Salt.SW.Zc_growth` | Salt/SW/ZetaPartialFractions.lean:851 | zeros, sieves |
| `Salt.SW.zeta_neg_re_logDeriv_le` | Salt/SW/ZetaPartialFractions.lean:942 | zeros, sieves |
| `Salt.SW.neg_logDeriv_zeta_le` | Salt/SW/ZetaPole.lean:189 | zeros, sieves |
| `Salt.SW.neg_logDeriv_LFunction_trivChar_le` | Salt/SW/ZetaPole.lean:351 | zeros, sieves, characters |
| `Salt.SW.zeta_neg_re_logDeriv_le_keep` | Salt/SW/ZetaZeroFree.lean:102 | zeros, sieves |
| `Salt.SW.zeta_zero_free_strip` | Salt/SW/ZetaZeroFree.lean:180 | zeros, sieves |
| `Salt.SW.zeta_zero_free_region` | Salt/SW/ZetaZeroFree.lean:235 | zeros, sieves |
| `Salt.Twelve.M5_cert` | Salt/Twelve/Certificate.lean:265 | sieves |
| `Salt.Twelve.winFrontierMW_of` | Salt/Twelve/FrontierM.lean:155 | sieves |
| `Salt.Twelve.collision_yF_M` | Salt/Twelve/InnerS1.lean:949 | sieves |
| `Salt.Twelve.phiUpperAtom_final` | Salt/Twelve/PhiUpperReindex.lean:458 | sieves |
| `Salt.Twelve.bounded_gaps_reduces_twelve` | Salt/Twelve/Pigeonhole12.lean:98 | sieves |
| `Salt.Twelve.primorial_ratio_le` | Salt/Twelve/PrimorialRatio.lean:188 | sieves |
| `Salt.TwinBar.cs_bound_ignores_constraint` | Salt/TwinBar/Constrained.lean:198 | sieves |
| `Salt.TwinBar.no_twin_weight_constrained` | Salt/TwinBar/Constrained.lean:209 | sieves |
| `Salt.TwinBar.admissible_witness` | Salt/TwinBar/Constrained.lean:377 | sieves |
| `Salt.TwinBar.I₂_nonneg` | Salt/TwinBar/Defs.lean:60 | sieves |
| `Salt.TwinBar.J₁_nonneg` | Salt/TwinBar/Defs.lean:68 | sieves |
| `Salt.TwinBar.J₂_nonneg` | Salt/TwinBar/Defs.lean:74 | sieves |
| `Salt.TwinBar.w₁_nonneg` | Salt/TwinBar/Defs.lean:95 | sieves |
| `Salt.TwinBar.w₂_nonneg` | Salt/TwinBar/Defs.lean:99 | sieves |
| `Salt.TwinBar.w₁_le_two` | Salt/TwinBar/Defs.lean:103 | sieves |
| `Salt.TwinBar.w₂_le_two` | Salt/TwinBar/Defs.lean:107 | sieves |
| `Salt.TwinBar.w₁_continuous` | Salt/TwinBar/Defs.lean:111 | sieves |
| `Salt.TwinBar.w₂_continuous` | Salt/TwinBar/Defs.lean:117 | sieves |
| `Salt.TwinBar.slice₁_continuousOn` | Salt/TwinBar/Defs.lean:143 | sieves |
| `Salt.TwinBar.slice₂_continuousOn` | Salt/TwinBar/Defs.lean:154 | sieves |
| `Salt.TwinBar.slice₁_intervalIntegrable` | Salt/TwinBar/Defs.lean:165 | sieves |
| `Salt.TwinBar.slice₂_intervalIntegrable` | Salt/TwinBar/Defs.lean:174 | sieves |
| `Salt.TwinBar.slice₁_sq_intervalIntegrable` | Salt/TwinBar/Defs.lean:183 | sieves |
| `Salt.TwinBar.slice₂_sq_intervalIntegrable` | Salt/TwinBar/Defs.lean:191 | sieves |
| `Salt.TwinBar.slice₁_weight_sq_intervalIntegrable` | Salt/TwinBar/Defs.lean:201 | sieves |
| `Salt.TwinBar.slice₂_weight_sq_intervalIntegrable` | Salt/TwinBar/Defs.lean:212 | sieves |
| `Salt.TwinBar.twin_bar_asymmetric` | Salt/TwinBar/Enlarged.lean:159 | sieves |
| `Salt.TwinBar.twin_bar_signed` | Salt/TwinBar/Enlarged.lean:169 | sieves |
| `Salt.TwinBar.twin_bar_enlarged` | Salt/TwinBar/Enlarged.lean:329 | sieves |
| `Salt.TwinBar.no_twin_weight_enlarged` | Salt/TwinBar/Enlarged.lean:344 | sieves |
| `Salt.TwinBar.two_fifths_below_threshold` | Salt/TwinBar/Enlarged.lean:355 | sieves |
| `Salt.TwinBar.I₄_nonneg` | Salt/TwinBar/FourBar.lean:112 | sieves |
| `Salt.TwinBar.J₁₄_nonneg` | Salt/TwinBar/FourBar.lean:125 | sieves |
| `Salt.TwinBar.J₂₄_nonneg` | Salt/TwinBar/FourBar.lean:134 | sieves |
| `Salt.TwinBar.J₃₄_nonneg` | Salt/TwinBar/FourBar.lean:143 | sieves |
| `Salt.TwinBar.J₄₄_nonneg` | Salt/TwinBar/FourBar.lean:152 | sieves |
| `Salt.TwinBar.logWeight_third` | Salt/TwinBar/FourBar.lean:210 | sieves |
| `Salt.TwinBar.log_slice_CS_third` | Salt/TwinBar/FourBar.lean:229 | sieves |
| `Salt.TwinBar.four_thirds_log_four_lt_two` | Salt/TwinBar/FourBar.lean:304 | sieves |
| `Salt.TwinBar.sliceCS₁₄` | Salt/TwinBar/FourBar.lean:362 | sieves |
| `Salt.TwinBar.sliceCS₂₄` | Salt/TwinBar/FourBar.lean:375 | sieves |
| `Salt.TwinBar.sliceCS₃₄` | Salt/TwinBar/FourBar.lean:388 | sieves |
| `Salt.TwinBar.sliceCS₄₄` | Salt/TwinBar/FourBar.lean:401 | sieves |
| `Salt.TwinBar.J₄₄_bound` | Salt/TwinBar/FourBarAsm.lean:123 | sieves |
| `Salt.TwinBar.J₁₄_bound` | Salt/TwinBar/FourBarAsm.lean:187 | sieves |
| `Salt.TwinBar.J₃₄_bound` | Salt/TwinBar/FourBarAsm.lean:252 | sieves |
| `Salt.TwinBar.J₂₄_bound` | Salt/TwinBar/FourBarAsm.lean:326 | sieves |
| `Salt.TwinBar.four_bar` | Salt/TwinBar/FourBarAsm.lean:406 | sieves |
| `Salt.TwinBar.fourBar_holds` | Salt/TwinBar/FourBarAsm.lean:482 | sieves |
| `Salt.TwinBar.no_quad_weight` | Salt/TwinBar/FourBarAsm.lean:487 | sieves |
| `Salt.TwinBar.twin_bar` | Salt/TwinBar/Impossibility.lean:173 | sieves |
| `Salt.TwinBar.twin_gate_fails` | Salt/TwinBar/Impossibility.lean:262 | sieves |
| `Salt.TwinBar.no_twin_weight` | Salt/TwinBar/Impossibility.lean:276 | sieves |
| `Salt.TwinBar.liouville_eq_chiSq_mul_moebius` | Salt/TwinBar/LambdaRate.lean:202 | sieves, characters |
| `Salt.TwinBar.Mlambda_eq_sum_Mmu` | Salt/TwinBar/LambdaRate.lean:303 | sieves |
| `Salt.TwinBar.Mmu_abs_le` | Salt/TwinBar/LambdaRate.lean:348 | sieves |
| `Salt.TwinBar.maynard_closed_at_two` | Salt/TwinBar/LeastK.lean:77 | sieves |
| `Salt.TwinBar.maynard_closed_at_three` | Salt/TwinBar/LeastK.lean:86 | sieves |
| `Salt.TwinBar.maynard_closed_at_four` | Salt/TwinBar/LeastK.lean:95 | sieves |
| `Salt.TwinBar.maynard_open_at_five` | Salt/TwinBar/LeastK.lean:108 | sieves |
| `Salt.TwinBar.least_k_theorem` | Salt/TwinBar/LeastK.lean:127 | sieves |
| `Salt.TwinBar.logWeight` | Salt/TwinBar/LogWeight.lean:36 | sieves |
| `Salt.TwinBar.siftedSum_sPlus` | Salt/TwinBar/ParityWall.lean:259 | sieves |
| `Salt.TwinBar.siftedSum_sMinus` | Salt/TwinBar/ParityWall.lean:271 | sieves |
| `Salt.TwinBar.lambda_mult_sum` | Salt/TwinBar/ParityWall.lean:309 | sieves, characters |
| `Salt.TwinBar.sPlus_rem_bound` | Salt/TwinBar/ParityWall.lean:398 | sieves |
| `Salt.TwinBar.sMinus_rem_bound` | Salt/TwinBar/ParityWall.lean:403 | sieves |
| `Salt.TwinBar.sieveAgree_pair` | Salt/TwinBar/ParityWall.lean:422 | sieves |
| `Salt.TwinBar.dirichlet₂` | Salt/TwinBar/RationalTie.lean:185 | sieves |
| `Salt.TwinBar.no_twin_certificate` | Salt/TwinBar/RationalTie.lean:527 | sieves |
| `Salt.TwinBar.twin_certificate_example` | Salt/TwinBar/RationalTie.lean:542 | sieves |
| `Salt.TwinBar.bridge_consistency` | Salt/TwinBar/RationalTie.lean:561 | sieves |
| `Salt.TwinBar.Sep.wall_of_indistinguishable` | Salt/TwinBar/Separation.lean:67 | sieves |
| `Salt.TwinBar.Sep.parity_wall_via_master` | Salt/TwinBar/Separation.lean:120 | sieves |
| `Salt.TwinBar.boxEntry_reduces` | Salt/TwinBar/SiegelCorrStrong.lean:59 | sieves |
| `Salt.TwinBar.infinitely_iff_not_noSiegel` | Salt/TwinBar/SiegelTwin.lean:111 | sieves |
| `Salt.TwinBar.noSiegelZeros_iff_not_infinitely` | Salt/TwinBar/SiegelTwin.lean:129 | sieves |
| `Salt.TwinBar.badHyp_false` | Salt/TwinBar/SiegelTwin.lean:153 | sieves |
| `Salt.TwinBar.Δ₄_isClosed` | Salt/TwinBar/Simplex4.lean:54 | sieves |
| `Salt.TwinBar.Δ₄_isCompact` | Salt/TwinBar/Simplex4.lean:66 | sieves |
| `Salt.TwinBar.Δ₄_measurableSet` | Salt/TwinBar/Simplex4.lean:75 | sieves |
| `Salt.TwinBar.psi₄` | Salt/TwinBar/Simplex4.lean:84 | sieves |
| `Salt.TwinBar.region_integrable₄` | Salt/TwinBar/Simplex4.lean:107 | sieves |
| `Salt.TwinBar.outer_marg₄_fst` | Salt/TwinBar/Simplex4.lean:115 | sieves |
| `Salt.TwinBar.outer_marg₄_swap` | Salt/TwinBar/Simplex4.lean:141 | sieves |
| `Salt.TwinBar.j4order_eq_region` | Salt/TwinBar/Simplex4.lean:162 | sieves |
| `Salt.TwinBar.j3order_eq_region` | Salt/TwinBar/Simplex4.lean:203 | sieves |
| `Salt.TwinBar.psi_eq₄` | Salt/TwinBar/Simplex4Inner.lean:50 | sieves |
| `Salt.TwinBar.reduce3_canonical_int` | Salt/TwinBar/Simplex4Inner.lean:99 | sieves |
| `Salt.TwinBar.outer_marg₃_lst_int` | Salt/TwinBar/Simplex4Inner.lean:117 | sieves |
| `Salt.TwinBar.canonical4_eq_region` | Salt/TwinBar/Simplex4Inner.lean:168 | sieves |
| `Salt.TwinBar.outer_marg₄_lst` | Salt/TwinBar/Simplex4Inner.lean:188 | sieves |
| `Salt.TwinBar.j2order_eq_region` | Salt/TwinBar/Simplex4Inner.lean:207 | sieves |
| `Salt.TwinBar.outer_marg₄_lst_swap` | Salt/TwinBar/Simplex4Inner.lean:233 | sieves |
| `Salt.TwinBar.Δ₃_isClosed` | Salt/TwinBar/SimplexS.lean:47 | sieves |
| `Salt.TwinBar.Δ₃_isCompact` | Salt/TwinBar/SimplexS.lean:59 | sieves |
| `Salt.TwinBar.Δ₃_measurableSet` | Salt/TwinBar/SimplexS.lean:67 | sieves |
| `Salt.TwinBar.slice_fix_fst₃` | Salt/TwinBar/SimplexS.lean:88 | sieves |
| `Salt.TwinBar.slice_fix₄_fst` | Salt/TwinBar/SimplexS.lean:102 | sieves |
| `Salt.TwinBar.slice_fix₄_snd` | Salt/TwinBar/SimplexS.lean:119 | sieves |
| `Salt.TwinBar.psi_eq₃` | Salt/TwinBar/SimplexS.lean:139 | sieves |
| `Salt.TwinBar.region_integrable₃` | Salt/TwinBar/SimplexS.lean:181 | sieves |
| `Salt.TwinBar.canonical_eq_region₃` | Salt/TwinBar/SimplexS.lean:192 | sieves |
| `Salt.TwinBar.w3order_eq_region₃` | Salt/TwinBar/SimplexS.lean:211 | sieves |
| `Salt.TwinBar.outer_marg₃_fst` | Salt/TwinBar/SimplexS.lean:266 | sieves |
| `Salt.TwinBar.outer_marg₃_lst` | Salt/TwinBar/SimplexS.lean:301 | sieves |
| `Salt.TwinBar.interval_CS` | Salt/TwinBar/SliceCS.lean:39 | sieves |
| `Salt.TwinBar.sliceCS₁` | Salt/TwinBar/SliceCS.lean:73 | sieves |
| `Salt.TwinBar.sliceCS₂` | Salt/TwinBar/SliceCS.lean:148 | sieves |
| `Salt.TwinBar.log_slice_CS` | Salt/TwinBar/ThreeBar.lean:242 | sieves |
| `Salt.TwinBar.three_halves_log_three_lt_two` | Salt/TwinBar/ThreeBar.lean:317 | sieves |
| `Salt.TwinBar.three_bar` | Salt/TwinBar/ThreeBarAsm.lean:678 | sieves |
| `Salt.TwinBar.tripleBar_holds` | Salt/TwinBar/ThreeBarAsm.lean:730 | sieves |
| `Salt.TwinBar.no_triple_weight` | Salt/TwinBar/ThreeBarAsm.lean:736 | sieves |
| `Salt.TwinBar.simplex_swap` | Salt/TwinBar/Tonelli.lean:83 | sieves |
| `Salt.TwinBar.twinC2_multipliable` | Salt/TwinBar/TwinDoor.lean:160 | sieves |
| `Salt.TwinBar.twinC2_pos` | Salt/TwinBar/TwinDoor.lean:171 | sieves |
| `Salt.TwinBar.twin_survivor_of_pos` | Salt/TwinBar/TwinDoor.lean:204 | sieves |
| `Salt.TwinBar.coprime_twinProd_iff_mod` | Salt/TwinBar/TwinParityAtomClasses.lean:92 | sieves |
| `Salt.TwinBar.sum_twinCoprime_eq_sum_admClasses` | Salt/TwinBar/TwinParityAtomClasses.lean:112 | sieves |
| `Salt.TwinBar.card_admClasses_eq_mul_W` | Salt/TwinBar/TwinParityAtomClasses.lean:147 | sieves, characters |
| `Salt.TwinBar.moebius_twinNu_sum_ge_inv` | Salt/TwinBar/TwinParityAtomClasses.lean:233 | sieves, characters |
| `Salt.TwinBar.admClasses_budget_lt_W` | Salt/TwinBar/TwinParityAtomClasses.lean:270 | sieves, characters |
| `Salt.TwinBar.class_sum_le_affine_form` | Salt/TwinBar/TwinParityAtomClasses.lean:300 | sieves |
| `Salt.TwinBar.twinLogWeight_support_infinite_of_atom_rate_frequently` | Salt/TwinBar/TwinParityAtomClasses.lean:597 | sieves, characters |
| `Salt.TwinBar.abs_sum_Icc_le_of_windows` | Salt/TwinBar/TwinParityAtomClasses.lean:678 | sieves |
| `Salt.TwinBar.log_natCast_le_sum_inv_Icc` | Salt/TwinBar/TwinParityCount.lean:61 | sieves |
| `Salt.TwinBar.moebius_sum_inv_dvd_ge` | Salt/TwinBar/TwinParityCount.lean:96 | sieves, characters |
| `Salt.TwinBar.sum_divisors_moebius_twinNu_pos` | Salt/TwinBar/TwinParityCount.lean:120 | sieves, characters |
| `Salt.TwinBar.twinLogWeight_support_infinite_of_atom` | Salt/TwinBar/TwinParityCount.lean:142 | sieves, characters |
| `Salt.TwinBar.twinLogWeight_support_infinite_of_atom_rate` | Salt/TwinBar/TwinParityCount.lean:186 | sieves, characters |
| `Salt.TwinBar.twinParitySieve_totalMass` | Salt/TwinBar/TwinParitySieve.lean:91 | sieves, characters |
| `Salt.TwinBar.L_one` | Salt/TwinBar/TwinParitySieve.lean:111 | sieves, characters |
| `Salt.TwinBar.twinParitySieve_multSum` | Salt/TwinBar/TwinParitySieve.lean:118 | sieves |
| `Salt.TwinBar.rem_split` | Salt/TwinBar/TwinParitySieve.lean:133 | sieves |
| `Salt.TwinBar.twinParitySieve_totalMass_nonneg` | Salt/TwinBar/TwinParitySieve.lean:155 | sieves |
| `Salt.TwinBar.one_lt_of_zThresh` | Salt/TwinBar/TwinParitySieve.lean:165 | sieves |
| `Salt.TwinBar.twinParitySieve_hMert` | Salt/TwinBar/TwinParitySieve.lean:177 | sieves |
| `Salt.TwinBar.twinParitySieve_brun_lower_ell1` | Salt/TwinBar/TwinParitySieve.lean:207 | sieves |
| `Salt.TwinBar.twinRem_sum_le` | Salt/TwinBar/TwinParitySieve.lean:251 | sieves |
| `Salt.TwinBar.one_le_ell1_level` | Salt/TwinBar/TwinParitySieve.lean:324 | sieves |
| `Salt.TwinBar.nu_one` | Salt/TwinBar/TwinParitySieve.lean:485 | sieves |
| `Salt.TwinBar.twinDisp_row_one` | Salt/TwinBar/TwinParitySieve.lean:489 | sieves |
| `Salt.TwinBar.liouvilleTwinDisp_sum_erase_one` | Salt/TwinBar/TwinParitySieve.lean:499 | sieves |
| `Salt.TwinBar.liouvilleTwinDisp_iff_erase_one` | Salt/TwinBar/TwinParitySieve.lean:516 | sieves |
| `Salt.TwinBar.logWeight_affine_le` | Salt/TwinBar/TwinParitySieve.lean:545 | sieves |
| `Salt.TwinBar.logWeight_affine_le_div` | Salt/TwinBar/TwinParitySieve.lean:568 | sieves |
| `Salt.TwinBar.support_infinite_of_partialSums_unbounded` | Salt/TwinBar/TwinParitySieve.lean:607 | sieves |
| `Salt.TwinBar.support_infinite_of_lower_unbounded` | Salt/TwinBar/TwinParitySieve.lean:628 | sieves |
| `Salt.TwinBar.sum_inv_affine_le` | Salt/TwinBar/TwinParitySieve.lean:661 | sieves |
| `Salt.TwinBar.sum_inv_affine_ge` | Salt/TwinBar/TwinParitySieve.lean:684 | sieves |
| `Salt.TwinBar.sum_twinCoprime_eq_moebius_divisors` | Salt/TwinBar/TwinParitySieve.lean:723 | sieves, characters |
| `Salt.TwinBar.nu_nonneg` | Salt/TwinBar/TwinParitySieve.lean:790 | sieves |
| `Salt.TwinBar.twinDisp_row_le_two_objects` | Salt/TwinBar/TwinParitySieve.lean:797 | sieves |
| `Salt.TwinBar.liouvilleTwinDisp_of_two_objects` | Salt/TwinBar/TwinParitySieve.lean:812 | sieves |
| `Salt.TwinBar.liouville_twinProd_mul` | Salt/TwinBar/TwinParitySieve.lean:854 | sieves, characters |
| `Salt.TwinBar.sum_logTwin_split` | Salt/TwinBar/TwinParitySieve.lean:864 | sieves, characters |
| `Salt.TwinBar.sum_logTwin_split_shift` | Salt/TwinBar/TwinParitySieve.lean:876 | sieves, characters |
| `Salt.TwinBar.log_succ_le_sum_inv_Icc` | Salt/TwinBar/TwinParitySieve.lean:907 | sieves |
| `Salt.TwinBar.log_le_sum_inv_Icc` | Salt/TwinBar/TwinParitySieve.lean:934 | sieves |
| `Salt.TwinBar.sum_inv_Icc_unbounded` | Salt/TwinBar/TwinParitySieve.lean:944 | sieves |
| `Salt.TwinBar.sum_logTwin_split_on` | Salt/TwinBar/TwinParitySieve.lean:976 | sieves, characters |
| `Salt.TwinBar.logSifted_lower_of_count_and_atoms` | Salt/TwinBar/TwinParitySieve.lean:994 | sieves, characters |
| `Salt.TwinBar.sum_divisors_moebius_nu_eq_W` | Salt/TwinBar/TwinParitySieve.lean:1043 | sieves, characters |
| `Salt.TwinBar.sum_divisors_moebius_twinNu_eq_W` | Salt/TwinBar/TwinParitySieve.lean:1055 | sieves, characters |
| `Salt.TwinBar.sum_inv_class_le` | Salt/TwinBar/TwinParitySieve.lean:1093 | sieves |
| `Salt.TwinBar.sum_inv_affine_sub_harmonic` | Salt/TwinBar/TwinParitySieve.lean:1203 | sieves |
| `Salt.TwinBar.twinLogWeight_nonneg` | Salt/TwinBar/TwinParitySieve.lean:1307 | sieves |
| `Salt.TwinBar.sum_twinLogWeight_range` | Salt/TwinBar/TwinParitySieve.lean:1319 | sieves, characters |
| `Salt.TwinBar.twinLogWeight_support_infinite_of_win` | Salt/TwinBar/TwinParitySieve.lean:1341 | sieves, characters |
| `Salt.TwinBar.twinLogWeight_ne_zero_iff` | Salt/TwinBar/TwinParitySieve.lean:1361 | sieves |
| `Salt.TwinBar.hdiv_of_log_growth` | Salt/TwinBar/TwinParitySieve.lean:1418 | sieves |
| `Salt.TwinBar.twinLogWeight_support_infinite_of_rate` | Salt/TwinBar/TwinParitySieve.lean:1452 | sieves, characters |
| `Salt.TwinBar.twinIdx_twinProd` | Salt/TwinBar/TwinParitySieveLog.lean:49 | sieves |
| `Salt.TwinBar.twinParitySieveLog_totalMass` | Salt/TwinBar/TwinParitySieveLog.lean:82 | sieves, characters |
| `Salt.TwinBar.Llog_one` | Salt/TwinBar/TwinParitySieveLog.lean:103 | sieves, characters |
| `Salt.TwinBar.Clog_one` | Salt/TwinBar/TwinParitySieveLog.lean:107 | sieves |
| `Salt.TwinBar.twinParitySieveLog_multSum` | Salt/TwinBar/TwinParitySieveLog.lean:111 | sieves |
| `Salt.TwinBar.rem_split_log` | Salt/TwinBar/TwinParitySieveLog.lean:122 | sieves |
| `Salt.TwinBar.twinParitySieveLog_totalMass_nonneg` | Salt/TwinBar/TwinParitySieveLog.lean:138 | sieves |
| `Salt.TwinBar.twinParitySieveLog_hMert` | Salt/TwinBar/TwinParitySieveLog.lean:152 | sieves |
| `Salt.TwinBar.twinParitySieveLog_brun_lower_ell1` | Salt/TwinBar/TwinParitySieveLog.lean:164 | sieves |
| `Salt.TwinBar.remLogCount_abs_le` | Salt/TwinBar/TwinParitySieveLog.lean:291 | sieves |
| `Salt.TwinBar.twinRemLog_sum_le` | Salt/TwinBar/TwinParitySieveLog.lean:334 | sieves |
| `Salt.TwinBar.twinParitySieveLog_siftedSum_eq` | Salt/TwinBar/TwinParitySieveLog.lean:417 | sieves |
| `Salt.TwinBar.lamChi_mult` | Salt/TwinBar/TwistedSieve.lean:149 | sieves, characters |
| `Salt.TwinBar.abs_lamChi_le_tau` | Salt/TwinBar/TwistedSieve.lean:165 | sieves, characters |
| `Salt.TwinBar.twistedErrSum_le_tauRemainder` | Salt/TwinBar/TwistedSieve.lean:181 | sieves, characters |
| `Salt.TwinBar.twistedMainSum_euler` | Salt/TwinBar/TwistedSieve.lean:201 | sieves, characters |
| `Salt.TwinBar.parity_wall` | Salt/TwinBar/Wall.lean:138 | sieves |
| `Salt.TwinBar.phiLowerR_certificate` | Salt/TwinBar/Wall.lean:195 | sieves |
| `Salt.TwinBar.sum_inv_Icc_le` | Salt/TwinBar/Wall.lean:220 | sieves |
| `Salt.TwinBar.witness_rosserRemainder_le` | Salt/TwinBar/Wall.lean:255 | sieves |
| `Salt.TwinBar.corr2_witness_diff` | Salt/TwinBar/WallCorr.lean:106 | sieves, characters |
| `Salt.TwinBar.corr2_witness_diff_Mlambda` | Salt/TwinBar/WallCorr.lean:135 | sieves |
| `Salt.TwinBar.corr2_witness_budget` | Salt/TwinBar/WallCorr.lean:148 | sieves |
| `Salt.TwinBar.parity_wall_corr` | Salt/TwinBar/WallCorr.lean:188 | sieves |
| `Salt.TwinBar.parity_wall_corr_stable` | Salt/TwinBar/WallCorr.lean:220 | sieves |
| `Salt.TwinBar.lambdaSummatory_holds` | Salt/TwinBar/WallUnconditional.lean:37 | sieves |
| `Salt.TwinBar.parity_wall_unconditional` | Salt/TwinBar/WallUnconditional.lean:43 | sieves |
| `Salt.TwinBar.no_parity_beating_certificate_unconditional` | Salt/TwinBar/WallUnconditional.lean:56 | sieves |
| `Salt.TwinBar.twin_witness` | Salt/TwinBar/Witness.lean:238 | sieves |
| `Salt.TwinBar.M₂_squeeze` | Salt/TwinBar/Witness.lean:253 | sieves |
| `Salt.Vk.genFun_fract` | Salt/Vk/Block.lean:48 | zeros, exponential sums |
| `Salt.Vk.fract_mem_Icc` | Salt/Vk/Block.lean:56 | zeros, exponential sums |
| `Salt.Vk.vk_shift_genFun_phase` | Salt/Vk/Block.lean:65 | zeros, exponential sums |
| `Salt.Vk.norm_vk_shift_sum` | Salt/Vk/Block.lean:80 | zeros, exponential sums |
| `Salt.Vk.vk_pow_sum_le` | Salt/Vk/Block.lean:94 | zeros, exponential sums |
| `Salt.Vk.vk_shift_average` | Salt/Vk/Block.lean:103 | zeros, exponential sums |
| `Salt.Vk.vk_shift_to_orbit` | Salt/Vk/Block.lean:121 | zeros, exponential sums |
| `Salt.Vk.vk_block_taylor_reduce` | Salt/Vk/Block.lean:170 | zeros, exponential sums |
| `Salt.Vk.genFun_eq_eR_sum` | Salt/Vk/BoxAvg.lean:31 | zeros, exponential sums |
| `Salt.Vk.genFun_lipschitz` | Salt/Vk/BoxAvg.lean:39 | zeros, exponential sums |
| `Salt.Vk.genFun_box_variation` | Salt/Vk/BoxAvg.lean:54 | zeros, exponential sums |
| `Salt.Vk.eR_intCast` | Salt/Vk/BoxMeasure.lean:47 | zeros, exponential sums |
| `Salt.Vk.genFun_add_int` | Salt/Vk/BoxMeasure.lean:55 | zeros, exponential sums |
| `Salt.Vk.vk_box_disjoint_avg` | Salt/Vk/BoxMeasure.lean:74 | zeros, exponential sums |
| `Salt.Vk.unitMeasure_Ioc_toReal` | Salt/Vk/BoxMeasure.lean:167 | zeros, exponential sums |
| `Salt.Vk.vkBox_measurable` | Salt/Vk/BoxMeasure.lean:178 | zeros, exponential sums |
| `Salt.Vk.clip_width_ge` | Salt/Vk/BoxMeasure.lean:182 | zeros, exponential sums |
| `Salt.Vk.vkBox_measureReal_ge` | Salt/Vk/BoxMeasure.lean:189 | zeros, exponential sums |
| `Salt.Vk.vkBox_disjoint` | Salt/Vk/BoxMeasure.lean:209 | zeros, exponential sums |
| `Salt.Vk.vk_box_disjoint_avg_of_centers` | Salt/Vk/BoxMeasure.lean:226 | zeros, exponential sums |
| `Salt.Vk.vk_eta_le` | Salt/Vk/Core.lean:38 | zeros, exponential sums |
| `Salt.Vk.vk_const_le` | Salt/Vk/Core.lean:69 | zeros, exponential sums |
| `Salt.Vk.vkDelta_prod_inv` | Salt/Vk/Core.lean:122 | zeros, exponential sums |
| `Salt.Vk.vkDelta_slack_le` | Salt/Vk/Core.lean:160 | zeros, exponential sums |
| `Salt.Vk.vk_two_Y_le` | Salt/Vk/Core.lean:217 | zeros, exponential sums |
| `Salt.Vk.vk_exp_ineq` | Salt/Vk/Core.lean:229 | zeros, exponential sums |
| `Salt.Vk.vk_block_core` | Salt/Vk/Core.lean:256 | zeros, exponential sums |
| `Salt.Vk.zeta_sub_dirichlet_bound` | Salt/Vk/Growth.lean:30 | zeros, exponential sums |
| `Salt.Vk.vk_ladder_prefix` | Salt/Vk/GrowthPow.lean:51 | zeros, exponential sums |
| `Salt.Vk.vk_window_prefix` | Salt/Vk/GrowthPow.lean:177 | zeros, exponential sums |
| `Salt.Vk.vk_window_scale_prefix` | Salt/Vk/GrowthPow.lean:235 | zeros, exponential sums |
| `Salt.Vk.vk_window_mid_prefix` | Salt/Vk/GrowthPow.lean:451 | zeros, exponential sums |
| `Salt.Vk.vk_dirichlet_block_le` | Salt/Vk/GrowthPow.lean:671 | zeros, exponential sums |
| `Salt.Vk.vk_dirichlet_sum_le` | Salt/Vk/GrowthPow.lean:851 | zeros, exponential sums |
| `Salt.Vk.zeta_growth_pow` | Salt/Vk/GrowthPow.lean:977 | zeros, exponential sums |
| `Salt.Vk.zeta_zero_free_region_pow` | Salt/Vk/GrowthPow.lean:1044 | zeros, exponential sums |
| `Salt.Vk.entire_norm_logDeriv_sub_sum_scaled` | Salt/Vk/Landau.lean:35 | zeros, exponential sums |
| `Salt.Vk.littlewood_uniform_growth` | Salt/Vk/Littlewood.lean:52 | zeros, exponential sums |
| `Salt.Vk.zeta_zero_free_littlewood_core` | Salt/Vk/Littlewood.lean:105 | zeros, exponential sums |
| `Salt.Vk.littlewood_bracket` | Salt/Vk/Littlewood.lean:276 | zeros, exponential sums |
| `Salt.Vk.zeta_zero_free_region_littlewood` | Salt/Vk/Littlewood.lean:409 | zeros, exponential sums |
| `Salt.Vk.vk_window_mid` | Salt/Vk/Mid.lean:103 | zeros, exponential sums |
| `Salt.Vk.poly_shift_orbit` | Salt/Vk/Pointwise.lean:34 | zeros, exponential sums |
| `Salt.Vk.vkTheta_anti` | Salt/Vk/PowRegion.lean:40 | zeros, exponential sums |
| `Salt.Vk.vkTheta_pos` | Salt/Vk/PowRegion.lean:66 | zeros, exponential sums |
| `Salt.Vk.pow_uniform_growth` | Salt/Vk/PowRegion.lean:92 | zeros, exponential sums |
| `Salt.Vk.zeta_zero_free_pow_core` | Salt/Vk/PowRegion.lean:153 | zeros, exponential sums |
| `Salt.Vk.riemannZeta_conj` | Salt/Vk/Region.lean:37 | zeros, exponential sums |
| `Salt.Vk.riemannZeta_conj_zero` | Salt/Vk/Region.lean:90 | zeros, exponential sums |
| `Salt.Vk.Zc_ratio_sphere_bound` | Salt/Vk/Region.lean:104 | zeros, exponential sums |
| `Salt.Vk.zeta_keep_one_disc` | Salt/Vk/Region.lean:180 | zeros, exponential sums |
| `Salt.Vk.zeta_drop_all_disc` | Salt/Vk/Region.lean:279 | zeros, exponential sums |
| `Salt.Vk.zeta_zero_free_of_disc` | Salt/Vk/Region.lean:345 | zeros, exponential sums |
| `Salt.Vk.region_of_uniform_growth` | Salt/Vk/RegionGrowth.lean:37 | zeros, exponential sums |
| `Salt.Vk.vk_sum_Ioc_split` | Salt/Vk/Scale.lean:30 | zeros, exponential sums |
| `Salt.Vk.vk_sum_Ioc_split_norm_le` | Salt/Vk/Scale.lean:43 | zeros, exponential sums |
| `Salt.Vk.eR_lipschitz` | Salt/Vk/Shift.lean:45 | zeros, exponential sums |
| `Salt.Vk.norm_sum_eR_sub_le` | Salt/Vk/Shift.lean:61 | zeros, exponential sums |
| `Salt.Vk.block_reduction` | Salt/Vk/Shift.lean:72 | zeros, exponential sums |
| `Salt.Vk.sum_Ioc_shift_boundary` | Salt/Vk/Shift.lean:96 | zeros, exponential sums |
| `Salt.Vk.fract_sub_abs_ge` | Salt/Vk/Spacing.lean:47 | zeros, exponential sums |
| `Salt.Vk.vkCoef_abs` | Salt/Vk/Spacing.lean:86 | zeros, exponential sums |
| `Salt.Vk.choose_mul_sub_le` | Salt/Vk/Spacing.lean:113 | zeros, exponential sums |
| `Salt.Vk.pow_diff_abs_le` | Salt/Vk/Spacing.lean:133 | zeros, exponential sums |
| `Salt.Vk.orbit_term_bound` | Salt/Vk/Spacing.lean:159 | zeros, exponential sums |
| `Salt.Vk.orbit_tail_geom_le` | Salt/Vk/Spacing.lean:237 | zeros, exponential sums |
| `Salt.Vk.vkOrbit_diff_sub_linear_bound` | Salt/Vk/Spacing.lean:267 | zeros, exponential sums |
| `Salt.Vk.vkOrbit_linear_abs` | Salt/Vk/Spacing.lean:313 | zeros, exponential sums |
| `Salt.Vk.log_2diff_upper` | Salt/Vk/Strip.lean:34 | zeros, exponential sums |
| `Salt.Vk.log_2diff_lower` | Salt/Vk/Strip.lean:50 | zeros, exponential sums |
| `Salt.Vk.zeta_block_strip` | Salt/Vk/Strip.lean:69 | zeros, exponential sums |
| `Salt.Vk.log_series_remainder` | Salt/Vk/Taylor.lean:77 | zeros, exponential sums |
| `Salt.Vk.phi_taylor_block` | Salt/Vk/Taylor.lean:164 | zeros, exponential sums |
| `Salt.Vk.phi_taylor_block_PY` | Salt/Vk/Taylor.lean:211 | zeros, exponential sums |
| `Salt.Vk.twistCoef_of_two_le` | Salt/Vk/Twist.lean:61 | zeros, exponential sums |
| `Salt.Vk.twistCoef_sum_Icc` | Salt/Vk/Twist.lean:70 | zeros, exponential sums |
| `Salt.Vk.phi_taylor_block_twist` | Salt/Vk/Twist.lean:92 | zeros, exponential sums |
| `Salt.Vk.phi_taylor_block_twist_PY` | Salt/Vk/Twist.lean:110 | zeros, exponential sums |
| `Salt.Vk.vkOrbit_congr` | Salt/Vk/Twist.lean:128 | zeros, exponential sums |
| `Salt.Vk.vkOrbit_twistCoef` | Salt/Vk/Twist.lean:139 | zeros, exponential sums |
| `Salt.Vk.vkOrbitPoint_twistCoef` | Salt/Vk/Twist.lean:147 | zeros, exponential sums |
| `Salt.Vk.vk_block_taylor_reduce_twist` | Salt/Vk/Twist.lean:160 | zeros, exponential sums |
| `Salt.Vk.zeta_block_dispatch_twist` | Salt/Vk/TwistHigh.lean:47 | zeros, exponential sums |
| `Salt.Vk.vk_dirichlet_block_twist_all` | Salt/Vk/TwistHigh.lean:204 | zeros, exponential sums |
| `Salt.Vk.vk_block_core_twist` | Salt/Vk/TwistLadder.lean:92 | zeros, exponential sums |
| `Salt.Vk.vk_window_bound_twist` | Salt/Vk/TwistLadder.lean:417 | zeros, exponential sums |
| `Salt.Vk.vk_window_prefix_twist` | Salt/Vk/TwistLadder.lean:470 | zeros, exponential sums |
| `Salt.Vk.vk_window_scale_twist` | Salt/Vk/TwistLadder.lean:699 | zeros, exponential sums |
| `Salt.Vk.vk_window_scale_prefix_twist` | Salt/Vk/TwistLadder.lean:718 | zeros, exponential sums |
| `Salt.Vk.vk_window_mid_twist` | Salt/Vk/TwistLadder.lean:1042 | zeros, exponential sums |
| `Salt.Vk.vk_window_mid_prefix_twist` | Salt/Vk/TwistLadder.lean:1060 | zeros, exponential sums |
| `Salt.Vk.vk_weighted_block_twist` | Salt/Vk/TwistLadder.lean:1086 | zeros, exponential sums |
| `Salt.Vk.vk_dirichlet_block_twist_le` | Salt/Vk/TwistLadder.lean:1150 | zeros, exponential sums |
| `Salt.Vk.vk_dirichlet_block_twist_le_of_high` | Salt/Vk/TwistLadder.lean:1273 | zeros, exponential sums |
| `Salt.Vk.vk_window_bound` | Salt/Vk/Window.lean:84 | zeros, exponential sums |
| `Salt.Vk.vk_logP_ge` | Salt/Vk/Window.lean:144 | zeros, exponential sums |
| `Salt.Vk.vk_logP_ub` | Salt/Vk/Window.lean:154 | zeros, exponential sums |
| `Salt.Vk.vk_hW2c_form` | Salt/Vk/Window.lean:178 | zeros, exponential sums |
| `Salt.Vk.vk_hW2b_form` | Salt/Vk/Window.lean:209 | zeros, exponential sums |
| `Salt.Vk.vk_hW1_form` | Salt/Vk/Window.lean:230 | zeros, exponential sums |
| `Salt.Vk.vk_hW2a_form` | Salt/Vk/Window.lean:248 | zeros, exponential sums |
| `Salt.Vk.vk_window_scale` | Salt/Vk/Window.lean:285 | zeros, exponential sums |
| `Salt.Vk.vk_ladder_bound` | Salt/Vk/Windows.lean:34 | zeros, exponential sums |
| `Salt.Vmvt.multiset_map_eq_of_powerSum_eq` | Salt/Vmvt/BaseCase.lean:92 | exponential sums |
| `Salt.Vmvt.exists_perm_of_powerSum_eq` | Salt/Vmvt/BaseCase.lean:145 | exponential sums |
| `Salt.Vmvt.Jk_le_of_le` | Salt/Vmvt/BaseCase.lean:154 | exponential sums |
| `Salt.Vmvt.Jk_mono` | Salt/Vmvt/Defs.lean:90 | exponential sums |
| `Salt.Vmvt.Jk_ge_card_pow` | Salt/Vmvt/Defs.lean:98 | exponential sums |
| `Salt.Vmvt.Jk_image_add` | Salt/Vmvt/Defs.lean:147 | exponential sums |
| `Salt.Vmvt.Jk_image_mul` | Salt/Vmvt/Defs.lean:197 | exponential sums |
| `Salt.Vmvt.Jk_image_affine` | Salt/Vmvt/Defs.lean:254 | exponential sums |
| `Salt.Vmvt.integral_eR_unit` | Salt/Vmvt/Fourier.lean:90 | exponential sums |
| `Salt.Vmvt.integral_setGen_mul_conj` | Salt/Vmvt/Fourier.lean:196 | exponential sums |
| `Salt.Vmvt.integral_norm_pow_eq_Jk` | Salt/Vmvt/Fourier.lean:259 | exponential sums |
| `Salt.Vmvt.pairEqBox_Ncount_eq_integral` | Salt/Vmvt/Fourier.lean:271 | exponential sums |
| `Salt.Vmvt.rpow_self_improve` | Salt/Vmvt/Holder.lean:77 | exponential sums |
| `Salt.Vmvt.crude_exp_ge_vmvtExp` | Salt/Vmvt/Holder.lean:180 | exponential sums |
| `Salt.Vmvt.sum_prod_filter_eq` | Salt/Vmvt/HolderTwo.lean:78 | exponential sums |
| `Salt.Vmvt.setGen_pairEqBox_factor` | Salt/Vmvt/HolderTwo.lean:179 | exponential sums |
| `Salt.Vmvt.holder_step` | Salt/Vmvt/HolderTwo.lean:240 | exponential sums |
| `Salt.Vmvt.pairEq_Ncount_le_frac` | Salt/Vmvt/HolderTwo.lean:326 | exponential sums |
| `Salt.Vmvt.linnik_lemma` | Salt/Vmvt/Linnik.lean:306 | exponential sums |
| `Salt.Vmvt.old_c0_le` | Salt/Vmvt/MeanValue.lean:221 | exponential sums |
| `Salt.Vmvt.vmvt_base` | Salt/Vmvt/MeanValue.lean:260 | exponential sums |
| `Salt.Vmvt.primes_in_Ioc_ge` | Salt/Vmvt/PrimeCount.lean:152 | exponential sums |
| `Salt.Vmvt.primes_in_Ioc_eff` | Salt/Vmvt/PrimeEff.lean:217 | exponential sums |
| `Salt.Vmvt.Ncount_shift_le` | Salt/Vmvt/Shifted.lean:221 | exponential sums |
| `Salt.Vmvt.Jk_shift_le` | Salt/Vmvt/Shifted.lean:257 | exponential sums |
| `Salt.Vmvt.Ncount_union_le` | Salt/Vmvt/Shifted.lean:282 | exponential sums |
| `Salt.Vmvt.vmvt_collect_exp` | Salt/Vmvt/StepFull.lean:62 | exponential sums |
| `Salt.Vmvt.collector_rpow` | Salt/Vmvt/StepFull.lean:73 | exponential sums |
| `Salt.Vmvt.transBox_le_ih` | Salt/Vmvt/StepFull.lean:118 | exponential sums |
| `Salt.Vmvt.le_scale_pow` | Salt/Vmvt/StepFull.lean:146 | exponential sums |
| `Salt.Vmvt.vmvtExp_ge_k` | Salt/Vmvt/StepFull.lean:177 | exponential sums |
| `Salt.Vmvt.bracket_le` | Salt/Vmvt/StepFull.lean:216 | exponential sums |
| `Salt.Vmvt.one_add_rpow_le_exp` | Salt/Vmvt/StepFull.lean:270 | exponential sums |
| `Salt.Vmvt.correction_le` | Salt/Vmvt/StepFull.lean:294 | exponential sums |
| `Salt.Vmvt.transBox_le_const` | Salt/Vmvt/StepFull.lean:371 | exponential sums |
| `Salt.Vmvt.n0_bounds` | Salt/Vmvt/StepFull.lean:418 | exponential sums |
| `Salt.Vmvt.JkI_crude` | Salt/Vmvt/Summit.lean:54 | exponential sums |
| `Salt.Vmvt.vmvtEta_ge` | Salt/Vmvt/Summit.lean:69 | exponential sums |
| `Salt.Vmvt.b_le_vmvtExp` | Salt/Vmvt/Summit.lean:97 | exponential sums |
| `Salt.Vmvt.vmvt_trivial_branch` | Salt/Vmvt/Summit.lean:129 | exponential sums |
| `Salt.Vmvt.pow_le_pow_base` | Salt/Vmvt/Summit2.lean:57 | exponential sums |
| `Salt.Vmvt.nine_ksq_r_pow_le` | Salt/Vmvt/Summit2.lean:66 | exponential sums |
| `Salt.Vmvt.exists_transversal_prime_set'` | Salt/Vmvt/Summit2.lean:90 | exponential sums |
| `Salt.Vmvt.vmvt` | Salt/Vmvt/Summit2.lean:151 | exponential sums |
| `Salt.Vmvt.transversal_prime_exists` | Salt/Vmvt/Transversal.lean:115 | exponential sums |
| `Salt.Vmvt.Jk_le_two_mul_filter_split` | Salt/Vmvt/Transversal.lean:251 | exponential sums |
| `Salt.Vmvt.JkI_le_two_mul_split` | Salt/Vmvt/Transversal.lean:293 | exponential sums |
| `Salt.Vmvt.distinctBox_le_card_mul_sum` | Salt/Vmvt/Transversal.lean:304 | exponential sums |
| `Salt.Vmvt.degenBox_Ncount_le` | Salt/Vmvt/Transversal.lean:359 | exponential sums |
| `Salt.Vmvt.residue_distinctModP` | Salt/Vmvt/Transversal2.lean:67 | exponential sums |
| `Salt.Vmvt.residue_mem_LinnikSol` | Salt/Vmvt/Transversal2.lean:87 | exponential sums |
| `Salt.Vmvt.desigFibre_card_le` | Salt/Vmvt/Transversal2.lean:129 | exponential sums |
| `Salt.Vmvt.powerSumEq_sub_const` | Salt/Vmvt/Transversal3.lean:43 | exponential sums |
| `Salt.Vmvt.sum_prod_transRestBox` | Salt/Vmvt/Transversal3.lean:121 | exponential sums |
| `Salt.Vmvt.setGen_transBox_factor` | Salt/Vmvt/Transversal3.lean:259 | exponential sums |
| `Salt.Vmvt.setGen_mixBox_factor` | Salt/Vmvt/Transversal3.lean:270 | exponential sums |
| `Salt.Vmvt.genFun_eq_sum_residue` | Salt/Vmvt/Transversal3.lean:302 | exponential sums |
| `Salt.Vmvt.transBox_Ncount_le_sum_mixBox` | Salt/Vmvt/Transversal3.lean:318 | exponential sums |
| `Salt.Vmvt.ndFibre_card_le` | Salt/Vmvt/Transversal3.lean:398 | exponential sums |
| `Salt.Vmvt.gradedPairs_card_le` | Salt/Vmvt/Transversal3.lean:459 | exponential sums |
| `Salt.Vmvt.powerSum_split` | Salt/Vmvt/Transversal3.lean:524 | exponential sums |
| `Salt.Vmvt.Jk_restSet_le` | Salt/Vmvt/Transversal3.lean:538 | exponential sums |
| `Salt.Vmvt.mixBox_fibre_le` | Salt/Vmvt/Transversal3.lean:585 | exponential sums |
| `Salt.Vmvt.proj_mem_gradedPairs` | Salt/Vmvt/Transversal3.lean:667 | exponential sums |
| `Salt.Vmvt.mixBox_Ncount_le` | Salt/Vmvt/Transversal3.lean:706 | exponential sums |
| `Salt.Vmvt.transBox_Ncount_le` | Salt/Vmvt/Transversal3.lean:743 | exponential sums |
| `Salt.Weil.trace_surjective` | Salt/Weil/ArtinSchreier.lean:45 | exponential sums |
| `Salt.Weil.range_artinSchreier_eq_ker_trace` | Salt/Weil/ArtinSchreier.lean:97 | exponential sums |
| `Salt.Weil.card_artinSchreier_solutions` | Salt/Weil/ArtinSchreier.lean:133 | exponential sums |
| `Salt.Weil.kloosterman_mul_of_coprime` | Salt/Weil/Composite.lean:107 | exponential sums |
| `Salt.Weil.norm_kloosterman_le_mul_of_coprime` | Salt/Weil/Composite.lean:190 | exponential sums |
| `Salt.Weil.norm_kloosterman_prime_pow_ge_two` | Salt/Weil/CompositeFull.lean:230 | exponential sums |
| `Salt.Weil.norm_kloosterman_prime_pow_odd` | Salt/Weil/CompositeFull.lean:299 | exponential sums |
| `Salt.Weil.kloosterman_zero_right` | Salt/Weil/CompositeFull.lean:309 | exponential sums |
| `Salt.Weil.norm_kloosterman_prime_unit` | Salt/Weil/CompositeFull.lean:351 | exponential sums |
| `Salt.Weil.norm_kloosterman_le_tau_sqrt` | Salt/Weil/CompositeFull.lean:384 | exponential sums |
| `Salt.Weil.kloosterman_mul_of_coprime_unit_twist` | Salt/Weil/CompositeTail.lean:144 | exponential sums |
| `Salt.Weil.kloosterman_mul_of_coprime_unit` | Salt/Weil/CompositeTail.lean:225 | exponential sums |
| `Salt.Weil.norm_kloosterman_le_mul_of_coprime_unit` | Salt/Weil/CompositeTail.lean:250 | exponential sums |
| `Salt.Weil.card_kloosterman_fiber` | Salt/Weil/CurveBridge.lean:56 | exponential sums |
| `Salt.Weil.curvePoly_coeff_zero_ne_zero` | Salt/Weil/CurveBridge.lean:137 | exponential sums |
| `Salt.Weil.curvePoly_natDegree` | Salt/Weil/CurveBridge.lean:153 | exponential sums |
| `Salt.Weil.curvePoly_not_isSquare` | Salt/Weil/CurveBridge.lean:179 | exponential sums |
| `Salt.Weil.sum_card_fiber_eq_pointCount` | Salt/Weil/CurveBridge.lean:244 | exponential sums |
| `Salt.Weil.sum_kloostermanMoment_eq_pointCount` | Salt/Weil/CurveBridge.lean:277 | exponential sums |
| `Salt.Weil.sum_kloostermanMoment_erase_zero_eq` | Salt/Weil/CurveBridge.lean:294 | exponential sums |
| `Salt.Weil.norm_localRoots_eq_sqrt` | Salt/Weil/Descent.lean:194 | exponential sums |
| `Salt.Weil.norm_kloosterman_le_two_sqrt` | Salt/Weil/Descent.lean:206 | exponential sums |
| `Salt.Weil.norm_kloosterman_le_two_sqrt'` | Salt/Weil/Descent.lean:222 | exponential sums |
| `Salt.Weil.pj_cube_eq_zero` | Salt/Weil/Estermann.lean:68 | exponential sums |
| `Salt.Weil.klSummand_mul_ushift3` | Salt/Weil/Estermann.lean:131 | exponential sums |
| `Salt.Weil.crit_mul_ushift3` | Salt/Weil/Estermann.lean:145 | exponential sums |
| `Salt.Weil.norm_quadExpSum` | Salt/Weil/Estermann.lean:167 | exponential sums |
| `Salt.Weil.castHom_eq_zero_iff_not_isUnit` | Salt/Weil/Estermann.lean:252 | exponential sums |
| `Salt.Weil.norm_kloosterman_prime_pow_odd_sharp` | Salt/Weil/Estermann.lean:268 | exponential sums |
| `Salt.Weil.norm_kloosterman_prime_pow_unit_sharp` | Salt/Weil/Estermann.lean:459 | exponential sums |
| `Salt.Weil.norm_kloosterman_prime_pow_gcd` | Salt/Weil/Estermann.lean:498 | exponential sums |
| `Salt.Weil.natCast_chineseRemainder_fst` | Salt/Weil/EstermannGlobal.lean:75 | exponential sums |
| `Salt.Weil.natCast_chineseRemainder_snd` | Salt/Weil/EstermannGlobal.lean:82 | exponential sums |
| `Salt.Weil.gcd_unit_twist_nat` | Salt/Weil/EstermannGlobal.lean:93 | exponential sums |
| `Salt.Weil.norm_kloosterman_estermann_nat` | Salt/Weil/EstermannGlobal.lean:125 | exponential sums |
| `Salt.Weil.norm_kloosterman_estermann` | Salt/Weil/EstermannGlobal.lean:318 | exponential sums |
| `Salt.Weil.norm_kloosterman_estermann_road` | Salt/Weil/EstermannGlobal.lean:343 | exponential sums |
| `Salt.Weil.two_pow_totient_le_estermann` | Salt/Weil/EstermannTwoAdic.lean:57 | exponential sums |
| `Salt.Weil.norm_kloosterman_two_pow_estermann` | Salt/Weil/EstermannTwoAdic.lean:92 | exponential sums |
| `Salt.Weil.norm_kloosterman_estermann_nat_of_v2_le` | Salt/Weil/EstermannTwoAdic.lean:114 | exponential sums |
| `Salt.Weil.norm_kloosterman_estermann_of_v2_le` | Salt/Weil/EstermannTwoAdic.lean:221 | exponential sums |
| `Salt.Weil.norm_kloosterman_estermann_road_clean` | Salt/Weil/EstermannTwoAdic.lean:234 | exponential sums |
| `Salt.Weil.stdAddChar_mul_descend` | Salt/Weil/GcdBranch.lean:63 | exponential sums |
| `Salt.Weil.stdAddChar_pow_descend` | Salt/Weil/GcdBranch.lean:77 | exponential sums |
| `Salt.Weil.unitsMap_prime_pow_fiber_card` | Salt/Weil/GcdBranch.lean:92 | exponential sums |
| `Salt.Weil.kloosterman_descent` | Salt/Weil/GcdBranch.lean:132 | exponential sums |
| `Salt.Weil.kloosterman_eq_sum_crit` | Salt/Weil/GcdBranch.lean:197 | exponential sums |
| `Salt.Weil.isUnit_of_prime_pow_iff` | Salt/Weil/GcdBranch.lean:249 | exponential sums |
| `Salt.Weil.prime_pow_cast_ne_zero` | Salt/Weil/GcdBranch.lean:257 | exponential sums |
| `Salt.Weil.kloosterman_zero_right_prime_pow` | Salt/Weil/GcdBranch.lean:274 | exponential sums |
| `Salt.Weil.norm_kloosterman_zero_right_prime_pow` | Salt/Weil/GcdBranch.lean:295 | exponential sums |
| `Salt.Weil.odd_of_coprime_of_two_dvd` | Salt/Weil/GcdBranch.lean:315 | exponential sums |
| `Salt.Weil.factorization_two_mul_odd_mul_odd` | Salt/Weil/GcdBranch.lean:324 | exponential sums |
| `Salt.Weil.factorization_two_kloosterman_modulus` | Salt/Weil/GcdBranch.lean:347 | exponential sums |
| `Salt.Weil.two_pow_factorization_dvd_of_odd_cofactors` | Salt/Weil/GcdBranch.lean:355 | exponential sums |
| `Salt.Weil.sqrt_gcd_le_sum_sqrt_common_divisors` | Salt/Weil/GcdDivisorSum.lean:97 | exponential sums |
| `Salt.Weil.sum_sqrt_gcd_div_le` | Salt/Weil/GcdDivisorSum.lean:178 | exponential sums |
| `Salt.Weil.sum_sqrt_gcd_div_le_log_two_mul` | Salt/Weil/GcdDivisorSum.lean:214 | exponential sums |
| `Salt.Weil.log_two_inv_not_removable` | Salt/Weil/GcdDivisorSum.lean:236 | exponential sums |
| `Salt.Weil.sum_sqrt_gcd_dyadic_le` | Salt/Weil/GcdDivisorSum.lean:287 | exponential sums |
| `Salt.Weil.hdvd_is_load_bearing` | Salt/Weil/GcdDivisorSum.lean:318 | exponential sums |
| `Salt.Weil.card_divisors_le_of_dvd` | Salt/Weil/GcdDivisorSum.lean:354 | exponential sums |
| `Salt.Weil.sum_sqrt_gcd_dyadic_le_of_dvd` | Salt/Weil/GcdDivisorSum.lean:363 | exponential sums |
| `Salt.Weil.norm_incomplete_kloosterman_le` | Salt/Weil/Incomplete.lean:181 | exponential sums |
| `Salt.Weil.norm_kloosterman_le_sub_one` | Salt/Weil/Kloosterman.lean:61 | exponential sums |
| `Salt.Weil.kloosterman_conj` | Salt/Weil/Kloosterman.lean:79 | exponential sums |
| `Salt.Weil.X_sub_C_pow_dvd_iff_hasseDeriv` | Salt/Weil/Kloosterman.lean:123 | exponential sums |
| `Salt.Weil.galoisField_trace_eq_sum_frobenius` | Salt/Weil/Kloosterman.lean:157 | exponential sums |
| `Salt.Weil.eta_mul` | Salt/Weil/LFunction.lean:55 | exponential sums |
| `Salt.Weil.T5_a1` | Salt/Weil/LFunction.lean:160 | exponential sums |
| `Salt.Weil.T5_ad` | Salt/Weil/LFunction.lean:209 | exponential sums |
| `Salt.Weil.T5_a2` | Salt/Weil/LFunction.lean:254 | exponential sums |
| `Salt.Weil.localPowerSum_rec` | Salt/Weil/LocalFactor.lean:96 | exponential sums |
| `Salt.Weil.localPowerSum_im` | Salt/Weil/LocalFactor.lean:134 | exponential sums |
| `Salt.Weil.abs_le_sqrt_of_powerSum_bound` | Salt/Weil/LocalFactor.lean:145 | exponential sums |
| `Salt.Weil.dist₁_zero_eq_norm_unitAddCircle` | Salt/Weil/MajorantExpansion.lean:85 | exponential sums |
| `Salt.Weil.majorantCircle_coe` | Salt/Weil/MajorantExpansion.lean:107 | exponential sums |
| `Salt.Weil.fourierCoeff_majorantCircle` | Salt/Weil/MajorantExpansion.lean:114 | exponential sums |
| `Salt.Weil.summable_fourierCoeff_majorantCircle` | Salt/Weil/MajorantExpansion.lean:128 | exponential sums |
| `Salt.Weil.hasSum_majorantCoeff` | Salt/Weil/MajorantExpansion.lean:142 | exponential sums |
| `Salt.Weil.sawtoothMajorant_fourier_expansion` | Salt/Weil/MajorantExpansion.lean:166 | exponential sums |
| `Salt.Weil.summable_majorantCoeff_mul_e` | Salt/Weil/MajorantExpansion.lean:172 | exponential sums |
| `Salt.Weil.kloostermanMoment_eq_neg_localPowerSum` | Salt/Weil/MomentEigen.lean:146 | exponential sums |
| `Salt.Weil.kloostermanMoment_eq_cCoeff` | Salt/Weil/MomentOrbit.lean:436 | exponential sums |
| `Salt.Weil.kloostermanMoment_im` | Salt/Weil/Moments.lean:113 | exponential sums |
| `Salt.Weil.kloostermanMoment_one` | Salt/Weil/Moments.lean:124 | exponential sums |
| `Salt.Weil.sum_kloostermanMoment_twist` | Salt/Weil/Moments.lean:200 | exponential sums |
| `Salt.Weil.forall_norm_le_of_powerSum_bound` | Salt/Weil/MultiExtract.lean:37 | exponential sums |
| `Salt.Weil.norm_eq_sqrt_of_pair_of_le` | Salt/Weil/MultiExtract.lean:209 | exponential sums |
| `Salt.Weil.norm_add_le_two_mul_sqrt` | Salt/Weil/MultiExtract.lean:228 | exponential sums |
| `Salt.Weil.newton_bridge` | Salt/Weil/NewtonBridge.lean:339 | exponential sums |
| `Salt.Weil.galoisField_minpoly_natDegree_dvd` | Salt/Weil/Orbits.lean:60 | exponential sums |
| `Salt.Weil.squarefree_X_pow_card_pow_sub_X` | Salt/Weil/Orbits.lean:107 | exponential sums |
| `Salt.Weil.irreducible_monic_dvd_X_pow_card_pow_sub_X_iff` | Salt/Weil/Orbits.lean:115 | exponential sums |
| `Salt.Weil.exists_quotient_hasseDeriv_mul_pow` | Salt/Weil/PointCount.lean:42 | exponential sums |
| `Salt.Weil.stepanov_locus_card_le` | Salt/Weil/PointCount.lean:141 | exponential sums |
| `Salt.Weil.pointCount_sub_card` | Salt/Weil/PointCount.lean:187 | exponential sums |
| `Salt.Weil.norm_kloosterman_prime_pow_even` | Salt/Weil/PrimePower.lean:228 | exponential sums |
| `Salt.Weil.dvd_roadModulus` | Salt/Weil/RoadModulus.lean:65 | exponential sums |
| `Salt.Weil.dvd_roadModulus_mul` | Salt/Weil/RoadModulus.lean:72 | exponential sums |
| `Salt.Weil.dvd_roadModulus_left` | Salt/Weil/RoadModulus.lean:76 | exponential sums |
| `Salt.Weil.factorization_two_roadModulus` | Salt/Weil/RoadModulus.lean:93 | exponential sums |
| `Salt.Weil.factorization_two_roadModulus_le` | Salt/Weil/RoadModulus.lean:107 | exponential sums |
| `Salt.Weil.dist₁_neg_zero` | Salt/Weil/Sawtooth.lean:63 | exponential sums |
| `Salt.Weil.norm_sawtoothRem_le_linear` | Salt/Weil/Sawtooth.lean:240 | exponential sums |
| `Salt.Weil.norm_sawtoothRem_le_dist` | Salt/Weil/Sawtooth.lean:345 | exponential sums |
| `Salt.Weil.norm_sawtoothRem_le` | Salt/Weil/Sawtooth.lean:440 | exponential sums |
| `Salt.Weil.sawtoothMajorant_eq_inv_max` | Salt/Weil/Sawtooth.lean:521 | exponential sums |
| `Salt.Weil.integral_sawtoothMajorant_eq` | Salt/Weil/Sawtooth.lean:574 | exponential sums |
| `Salt.Weil.integral_sawtoothMajorant_le` | Salt/Weil/Sawtooth.lean:648 | exponential sums |
| `Salt.Weil.norm_majorantCoeff_le` | Salt/Weil/Sawtooth.lean:666 | exponential sums |
| `Salt.Weil.norm_majorantCoeff_le_sq` | Salt/Weil/Sawtooth.lean:970 | exponential sums |
| `Salt.Weil.norm_congrExpSum_le_length` | Salt/Weil/Sawtooth.lean:1119 | exponential sums |
| `Salt.Weil.norm_congrExpSum_le_dist` | Salt/Weil/Sawtooth.lean:1187 | exponential sums |
| `Salt.Weil.norm_congrExpSum_le` | Salt/Weil/Sawtooth.lean:1227 | exponential sums |
| `Salt.Weil.dist₁_mul_div_eq_zero_iff` | Salt/Weil/Sawtooth.lean:1241 | exponential sums |
| `Salt.Weil.summable_norm_majorantCoeff` | Salt/Weil/Sawtooth.lean:1428 | exponential sums |
| `Salt.Weil.tsum_norm_majorantCoeff_le` | Salt/Weil/Sawtooth.lean:1434 | exponential sums |
| `Salt.Weil.tsum_norm_majorantCoeff_le_log` | Salt/Weil/Sawtooth.lean:1444 | exponential sums |
| `Salt.Weil.stepanovAux_natDegree_le` | Salt/Weil/Stepanov.lean:75 | exponential sums |
| `Salt.Weil.X_pow_dvd_of_range_sum_eq_zero` | Salt/Weil/Stepanov.lean:94 | exponential sums |
| `Salt.Weil.stepanovAux_ne_zero` | Salt/Weil/Stepanov.lean:129 | exponential sums |
| `Salt.Weil.stepanov_dimension_count` | Salt/Weil/StepanovCore.lean:71 | exponential sums |
| `Salt.Weil.stepanovAux_dvd_of_reduced_eval_zero` | Salt/Weil/StepanovCore.lean:234 | exponential sums |
| `Salt.Weil.stepanov_multiplicity_card_le` | Salt/Weil/StepanovCore.lean:248 | exponential sums |
| `Salt.Weil.stepanov_solution_exists` | Salt/Weil/StepanovSolve.lean:217 | exponential sums |
| `Salt.Weil.stepanov_one_sided_card_le` | Salt/Weil/StepanovSolve.lean:254 | exponential sums |
| `Salt.Weil.weil_stepanov` | Salt/Weil/WeilStepanov.lean:77 | exponential sums |

## conditional (1605)

| name | file:line | objects | hypotheses |
|---|---|---|---|
| `Salt.BV.psiToPiTransfer_of_core` | Salt/BV/Abel.lean:126 | sieves | `Salt.BV.PsiToPiCore` |
| `Salt.BV.hasLevel_half_of_siegelWalfisz` | Salt/BV/AbelCore.lean:753 | sieves | `Salt.BV.SiegelWalfisz` |
| `Salt.BV.bounded_gaps_of_siegelWalfisz` | Salt/BV/AbelCore.lean:757 | sieves | `Salt.BV.SiegelWalfisz` |
| `Salt.BV.siegelWalfisz_psiTot` | Salt/BV/Defs.lean:76 | sieves | `Salt.BV.SiegelWalfisz` |
| `Salt.BV.psi_BV_of_siegelWalfisz` | Salt/BV/Dispersion.lean:778 | sieves | `Salt.BV.SiegelWalfisz` |
| `Salt.BV.psi_BV_of_siegelWalfisz'` | Salt/BV/DispersionClose.lean:439 | sieves | `Salt.BV.SiegelWalfisz` |
| `Salt.BV.bounded_gaps_of_siegelWalfisz_of_bridge` | Salt/BV/Headline.lean:26 | sieves | `Salt.BV.SiegelWalfisz`, `Salt.BV.PsiToPiTransfer` |
| `Salt.BV.hasLevel_half_of_siegelWalfisz_of_bridge` | Salt/BV/PsiToPi.lean:139 | sieves | `Salt.BV.SiegelWalfisz`, `Salt.BV.PsiToPiTransfer` |
| `Salt.BV.psiChi_le_of_siegelWalfisz` | Salt/BV/SWChar.lean:96 | sieves, characters | `Salt.BV.SiegelWalfisz` |
| `Salt.BV.psiChi_le_of_siegelWalfisz_absorbed` | Salt/BV/SWChar.lean:157 | sieves, characters | `Salt.BV.SiegelWalfisz` |
| `Salt.BrunLower.chi_imp_windowed` | Salt/BrunLower/Defs.lean:177 | sieves | `Salt.BrunLower.chi` |
| `Salt.BrunLower.chi_dvd_closed` | Salt/BrunLower/Defs.lean:202 | sieves | `Salt.BrunLower.chi` |
| `Salt.BrunLower.chi_add_smaller_prime` | Salt/BrunLower/Defs.lean:235 | sieves | `Salt.BrunLower.chi` |
| `Salt.BrunLower.siftedSum_ge_sum_of_lowerMoebius` | Salt/BrunLower/LowerMoebius.lean:41 | sieves | `Salt.BrunLower.IsLowerMoebius` |
| `Salt.BrunLower.siftedSum_ge_mainSum_errSum_of_lowerMoebius` | Salt/BrunLower/LowerMoebius.lean:67 | sieves | `Salt.BrunLower.IsLowerMoebius` |
| `Salt.Certs.cert_parity_gap` | Salt/Certs/ParityGap.lean:74 | other | `Salt.Parity.TwinSufficient` |
| `Salt.Chen.aCount_ge_one_of_W` | Salt/Chen/Assembly.lean:609 | sieves | `Salt.Chen.TripleP` |
| `Salt.Chen.chi_lower_lt` | Salt/Chen/BrunEll1.lean:116 | sieves | `Salt.BrunLower.chi` |
| `Salt.Chen.rosserCond_upper_lt` | Salt/Chen/Buchstab.lean:139 | sieves | `Salt.Chen.rosserCond` |
| `Salt.Chen.rosserCond_lower_lt` | Salt/Chen/Buchstab.lean:163 | sieves | `Salt.Chen.rosserCond` |
| `Salt.Chen.rosserCond_dvd_closed` | Salt/Chen/LinearSieve.lean:503 | sieves | `Salt.Chen.rosserCond` |
| `Salt.Chen.rosserCond_add_prime` | Salt/Chen/LinearSieve.lean:541 | sieves | `Salt.Chen.rosserCond` |
| `Salt.Chen.bjs_theorem6_upper'` | Salt/Chen/StepBound2.lean:250 | sieves | `Salt.Chen.StepHyp` |
| `Salt.Chen.bjs_theorem6_lower'` | Salt/Chen/StepBound2.lean:268 | sieves | `Salt.Chen.StepHyp` |
| `Salt.Chen.bjs_theorem6_upper_sifted'` | Salt/Chen/StepBound2.lean:286 | sieves | `Salt.Chen.StepHyp` |
| `Salt.Chen.bjs_theorem6_lower_sifted'` | Salt/Chen/StepBound2.lean:307 | sieves | `Salt.Chen.StepHyp` |
| `Salt.Chen.boxHonestDisc_zero_of_windowDisjoint` | Salt/Chen/SwitchDyadic.lean:257 | sieves | `Salt.Chen.windowDisjoint` |
| `Salt.Chen.twin_A1_lower_B_W` | Salt/Chen/TwinA1W.lean:400 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.twin_A2_per_prime_W` | Salt/Chen/TwinA2W.lean:361 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.twin_A1_lower_B` | Salt/Chen/TwinSharp.lean:52 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.twin_A2_per_prime_B` | Salt/Chen/TwinSharp.lean:106 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.impostor_feasible` | Salt/Chen/WeightNoGo.lean:70 | sieves | `Salt.Chen.Feasible` |
| `Salt.Chen.no_readable_certificate` | Salt/Chen/WeightNoGo.lean:82 | sieves | `Salt.Chen.Feasible` |
| `Salt.Chen.no_affine_certificate` | Salt/Chen/WeightNoGo.lean:180 | sieves | `Salt.Chen.Feasible` |
| `Salt.Chen.chen_weight_struct` | Salt/Chen/WeightTrivia.lean:391 | sieves | `¬Salt.Chen.IsP2` |
| `Salt.Chen.T_le_of_peel_step_w` | Salt/Chen/WindowedStep.lean:256 | sieves | `Salt.Chen.StepHypW` |
| `Salt.Chen.stepHypWPC_of_wp` | Salt/Chen/WindowedStepC.lean:73 | sieves | `Salt.Chen.StepHypWP` |
| `Salt.Chen.T_le_of_peel_step_wpc` | Salt/Chen/WindowedStepC.lean:92 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.hlevel_wpc_upper` | Salt/Chen/WindowedStepC.lean:173 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.hlevel_wpc_lower` | Salt/Chen/WindowedStepC.lean:205 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.bjs_theorem6_windowed_c_upper` | Salt/Chen/WindowedStepC.lean:245 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.bjs_theorem6_windowed_c_lower` | Salt/Chen/WindowedStepC.lean:273 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.bjs_theorem6_windowed_cB_upper` | Salt/Chen/WindowedStepC.lean:427 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.bjs_theorem6_windowed_cB_lower` | Salt/Chen/WindowedStepC.lean:453 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Chen.T_le_of_peel_step_wp` | Salt/Chen/WindowedStepP.lean:89 | sieves | `Salt.Chen.StepHypWP` |
| `Salt.Chen.hlevel_wp_upper` | Salt/Chen/WindowedStepP.lean:168 | sieves | `Salt.Chen.StepHypWP` |
| `Salt.Chen.hlevel_wp_lower` | Salt/Chen/WindowedStepP.lean:199 | sieves | `Salt.Chen.StepHypWP` |
| `Salt.Chen.bjs_theorem6_windowed_p_upper` | Salt/Chen/WindowedStepP.lean:235 | sieves | `Salt.Chen.StepHypWP` |
| `Salt.Chen.bjs_theorem6_windowed_p_lower` | Salt/Chen/WindowedStepP.lean:262 | sieves | `Salt.Chen.StepHypWP` |
| `Salt.Chen.bjs_theorem6_windowed_sharp_upper` | Salt/Chen/WindowedStepP.lean:354 | sieves | `Salt.Chen.StepHypWP` |
| `Salt.Chen.bjs_theorem6_windowed_sharp_lower` | Salt/Chen/WindowedStepP.lean:380 | sieves | `Salt.Chen.StepHypWP` |
| `ProbabilityTheory.chain_rule'` | Salt/Entropy/Basic.lean:219 | entropy | `FiniteRange` |
| `ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy` | Salt/Entropy/Basic.lean:311 | entropy | `FiniteRange` |
| `ProbabilityTheory.condMutualInfo_nonneg` | Salt/Entropy/Basic.lean:325 | entropy | `FiniteRange` |
| `Salt.Entropy.Chowla.affWindow_survivorMass_ge` | Salt/Entropy/Chowla/AffineFork.lean:107 | characters, entropy | `¬Salt.Entropy.Chowla.logChowlaFailsAff` |
| `Salt.Entropy.Chowla.exists_affSurvivor_of_not_failsAff` | Salt/Entropy/Chowla/AffineFork.lean:153 | characters, entropy | `¬Salt.Entropy.Chowla.logChowlaFailsAff` |
| `Salt.Entropy.Chowla.zRough_oddOmega_infinite_of_affSupply` | Salt/Entropy/Chowla/AffineFork.lean:308 | entropy | `Salt.Entropy.Chowla.LogChowlaAffSupply` |
| `Salt.Entropy.Chowla.zRough_oddOmega_infinite_of_affSupply_primorial` | Salt/Entropy/Chowla/AffineFork.lean:345 | entropy | `Salt.Entropy.Chowla.LogChowlaAffSupply` |
| `Salt.Entropy.Chowla.singleCorr_of_fails` | Salt/Entropy/Chowla/ChowlaFailure.lean:81 | entropy | `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.h211_of_logChowla2Fails` | Salt/Entropy/Chowla/ChowlaFailure.lean:120 | characters, entropy | `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.singleCorr_of_fails_h_one` | Salt/Entropy/Chowla/ChowlaFailure.lean:239 | entropy | `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq_count_hloCap_pinned_flat_h` | Salt/Entropy/Chowla/HloExportFlatH.lean:220 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2H` |
| `Salt.Entropy.Chowla.flat_head_uniform_h` | Salt/Entropy/Chowla/HloExportFlatH.lean:410 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2H` |
| `Salt.Entropy.Chowla.contradiction_of_mrtDoor` | Salt/Entropy/Chowla/MRTDoor.lean:62 | entropy, exponential sums | `Salt.Entropy.Chowla.MRTUniformity` |
| `Salt.Entropy.Chowla.mrtUniformity_implies_xi` | Salt/Entropy/Chowla/MRTDoor.lean:121 | entropy | `Salt.Entropy.Chowla.MRTUniformity` |
| `Salt.Entropy.Chowla.contradiction_of_mrtDoorXi` | Salt/Entropy/Chowla/MRTDoor.lean:132 | entropy, exponential sums | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2` | Salt/Entropy/Chowla/MRTDoor.lean:205 | entropy, exponential sums | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.Entropy.Chowla.mrtUniformityXiL2_of_xi` | Salt/Entropy/Chowla/MRTDoor.lean:255 | entropy | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.mutualInfo_eq_integral_condDistrib_defect` | Salt/Entropy/Chowla/MarkovExtract.lean:91 | entropy | `FiniteRange` |
| `Salt.Entropy.Chowla.decrement_markov` | Salt/Entropy/Chowla/MarkovExtract.lean:112 | entropy | `FiniteRange` |
| `Salt.Entropy.Chowla.twinDetecting'_imp` | Salt/Entropy/Chowla/PinDichotomy.lean:82 | entropy | `Salt.Entropy.Chowla.TwinDetecting'` |
| `Salt.Entropy.Chowla.blind_iff_const_fails_unguarded` | Salt/Entropy/Chowla/PinDichotomy.lean:119 | entropy | `Salt.Entropy.Chowla.PairCollapse` |
| `Salt.Entropy.Chowla.blind_iff_const` | Salt/Entropy/Chowla/PinDichotomy.lean:137 | entropy | `Salt.Entropy.Chowla.PmNormalized`, `Salt.Entropy.Chowla.PairCollapse` |
| `Salt.Entropy.Chowla.pin_iff_detecting` | Salt/Entropy/Chowla/PinDichotomy.lean:211 | entropy | `Salt.Entropy.Chowla.PmNormalized`, `Salt.Entropy.Chowla.PairCollapse` |
| `Salt.Entropy.Chowla.pinned_door` | Salt/Entropy/Chowla/PinDichotomy.lean:229 | entropy | `Salt.Entropy.Chowla.PmNormalized`, `Salt.Entropy.Chowla.PairCollapse` |
| `Salt.Entropy.Chowla.pin_minimal` | Salt/Entropy/Chowla/PinDichotomy.lean:235 | entropy | `Salt.Entropy.Chowla.PmNormalized`, `Salt.Entropy.Chowla.PairCollapse`, `Salt.Entropy.Chowla.TwinDetecting'` |
| `Salt.Entropy.Chowla.door_criterion_exists` | Salt/Entropy/Chowla/PinDichotomy.lean:367 | entropy | `Salt.Entropy.Chowla.PmNormalized`, `Salt.Entropy.Chowla.PairCollapse` |
| `Salt.Entropy.Chowla.door_criterion` | Salt/Entropy/Chowla/PinDichotomy.lean:385 | entropy | `Salt.Entropy.Chowla.PmNormalized`, `Salt.Entropy.Chowla.PairCollapse` |
| `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiH` | Salt/Entropy/Chowla/ShiftFork.lean:345 | entropy, exponential sums | `Salt.Entropy.Chowla.MRTUniformityXiH` |
| `Salt.Entropy.Chowla.mrtUniformity_implies_xiH` | Salt/Entropy/Chowla/ShiftFork.lean:504 | entropy | `Salt.Entropy.Chowla.MRTUniformity` |
| `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2H` | Salt/Entropy/Chowla/ShiftFork.lean:579 | entropy, exponential sums | `Salt.Entropy.Chowla.MRTUniformityXiL2H` |
| `Salt.Entropy.Chowla.sign_split_of_not_fails` | Salt/Entropy/Chowla/SignSplit.lean:209 | entropy | `¬Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.sign_split_door_only` | Salt/Entropy/Chowla/SignSplit.lean:230 | entropy | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.sign_split_quarter_log` | Salt/Entropy/Chowla/SignSplit.lean:252 | entropy | `¬Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.sign_split_fifth` | Salt/Entropy/Chowla/SignSplit.lean:278 | entropy | `¬Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.log_chowla_two_conditional` | Salt/Entropy/Chowla/SpineClose.lean:28 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformity`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.log_chowla_two_conditional_regime` | Salt/Entropy/Chowla/SpineClose.lean:177 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformity`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq_count_hloCap_epsFamily` | Salt/Entropy/Chowla/SpineEpsFamily.lean:65 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.Entropy.Chowla.log_chowla_two_conditional_hoisted` | Salt/Entropy/Chowla/SpineFinal.lean:360 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformity`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.Entropy.Chowla.log_chowla_two_final` | Salt/Entropy/Chowla/SpineFinal.lean:425 | entropy | `Salt.Entropy.Chowla.MRTUniformity` |
| `Salt.Entropy.Chowla.log_chowla_two_final_xi` | Salt/Entropy/Chowla/SpineFinal.lean:521 | entropy | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head` | Salt/Entropy/Chowla/SpineFinal.lean:750 | entropy | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head_g` | Salt/Entropy/Chowla/SpineFinal.lean:873 | entropy | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.log_chowla_two_door_only_xi` | Salt/Entropy/Chowla/SpineFinal.lean:966 | entropy | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.log_chowla_two_door_only` | Salt/Entropy/Chowla/SpineFinal.lean:981 | entropy | `Salt.Entropy.Chowla.MRTUniformity` |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head_g_45` | Salt/Entropy/Chowla/SpineFinal.lean:1011 | entropy | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq_count` | Salt/Entropy/Chowla/SpineFinal.lean:1359 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head_g_sq` | Salt/Entropy/Chowla/SpineFinal.lean:1459 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.Entropy.Chowla.h211_aff` | Salt/Entropy/Chowla/StrideBridge.lean:665 | characters, entropy | `Salt.Entropy.Chowla.logChowlaFailsAff` |
| `Salt.Entropy.Chowla.h211_aff_one_zero` | Salt/Entropy/Chowla/StrideBridge.lean:699 | characters, entropy | `Salt.Entropy.Chowla.logChowlaFails` |
| `Salt.Entropy.Chowla.log_chowla_aff_of_door_unslotted` | Salt/Entropy/Chowla/StrideCircle.lean:1090 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.singleCorr_of_failsAff` | Salt/Entropy/Chowla/StrideFork.lean:138 | entropy | `Salt.Entropy.Chowla.logChowlaFailsAff` |
| `Salt.Entropy.Chowla.singleCorr_of_failsAff'` | Salt/Entropy/Chowla/StrideFork.lean:176 | entropy | `Salt.Entropy.Chowla.logChowlaFailsAff` |
| `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiAff` | Salt/Entropy/Chowla/StrideFork.lean:725 | entropy, exponential sums | `Salt.Entropy.Chowla.MRTUniformityXiAff` |
| `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2Aff` | Salt/Entropy/Chowla/StrideFork.lean:759 | entropy, exponential sums | `Salt.Entropy.Chowla.MRTUniformityXiL2Aff` |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_x_mul` | Salt/Entropy/Chowla/StridePair.lean:291 | entropy | `Salt.Entropy.Chowla.StrideScale` |
| `Salt.Entropy.Chowla.mrtUniformityXiL2AffW_of_aff` | Salt/Entropy/Chowla/StridePair.lean:370 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2Aff` |
| `Salt.Entropy.Chowla.mrtUniformityXiL2AffW_mono` | Salt/Entropy/Chowla/StridePair.lean:381 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.contradiction_of_mrtDoorXiL2AffW` | Salt/Entropy/Chowla/StridePair.lean:390 | entropy, exponential sums | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.mrtUniformityXiL2AffW_of_set` | Salt/Entropy/Chowla/StridePair.lean:583 | entropy | `Salt.Entropy.Chowla.StrideScale`, `Salt.Entropy.Chowla.MRTUniformityXiL2Set` |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_x_mul_b9` | Salt/Entropy/Chowla/StridePair.lean:1061 | entropy | `Salt.Entropy.Chowla.StrideScale` |
| `Salt.Entropy.Chowla.mrtUniformityXiL2AffW_of_set_b9` | Salt/Entropy/Chowla/StridePair.lean:1079 | entropy | `Salt.Entropy.Chowla.StrideScale`, `Salt.Entropy.Chowla.MRTUniformityXiL2Set` |
| `Salt.Entropy.Chowla.logChowlaAffSupplyW_of_supply` | Salt/Entropy/Chowla/StridePrize.lean:95 | entropy | `Salt.Entropy.Chowla.LogChowlaAffSupply` |
| `Salt.Entropy.Chowla.zRough_oddOmega_infinite_of_affSupplyW` | Salt/Entropy/Chowla/StridePrize.lean:121 | entropy | `Salt.Entropy.Chowla.LogChowlaAffSupplyW` |
| `Salt.Entropy.Chowla.zRough_oddOmega_infinite_of_affSupplyW_primorial` | Salt/Entropy/Chowla/StridePrize.lean:150 | entropy | `Salt.Entropy.Chowla.LogChowlaAffSupplyW` |
| `Salt.Entropy.Chowla.log_chowla_aff_composed_of_headG` | Salt/Entropy/Chowla/StridePrize.lean:197 | entropy | `Salt.Entropy.Chowla.GradedAffHeadAt` |
| `Salt.Entropy.Chowla.logChowlaAffSupplyW_of_headG` | Salt/Entropy/Chowla/StridePrize.lean:280 | entropy | `Salt.Entropy.Chowla.GradedAffHeadAt` |
| `Salt.Entropy.Chowla.log_chowla_aff_composed_of_headG_g12b` | Salt/Entropy/Chowla/StridePrize.lean:321 | entropy | `Salt.Entropy.Chowla.GradedAffHeadAt_g12b` |
| `Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq_aff` | Salt/Entropy/Chowla/StrideShell.lean:125 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.spine_False_core_xi_sq_aff` | Salt/Entropy/Chowla/StrideShell.lean:245 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW`, `Salt.Entropy.Chowla.logChowlaFailsAff` |
| `Salt.Entropy.Chowla.log_chowla_aff_of_door` | Salt/Entropy/Chowla/StrideShell.lean:433 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq_aff_one_zero` | Salt/Entropy/Chowla/StrideShell.lean:665 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.log_chowla_aff_of_door_at_regime_g12b` | Salt/Entropy/Chowla/StrideShellBand.lean:90 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.gradedAffHeadAt_g12b_of_at_regime` | Salt/Entropy/Chowla/StrideShellBand.lean:369 | entropy | `¬Salt.Entropy.Chowla.logChowlaFailsAff`, `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.log_chowla_aff_of_door_g` | Salt/Entropy/Chowla/StrideShellG.lean:50 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.log_chowla_aff_of_door_unslotted_g` | Salt/Entropy/Chowla/StrideShellG.lean:275 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.log_chowla_aff_of_door_g12b` | Salt/Entropy/Chowla/StrideShellG.lean:320 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.log_chowla_aff_of_door_unslotted_g12b` | Salt/Entropy/Chowla/StrideShellG.lean:544 | entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.Entropy.Chowla.log_chowla_two_shell` | Salt/Entropy/Chowla/Theorem23Shell.lean:132 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformity` |
| `Salt.Entropy.Chowla.log_chowla_two_shell_xi` | Salt/Entropy/Chowla/Theorem23Shell.lean:243 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq` | Salt/Entropy/Chowla/Theorem23Shell.lean:362 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.Entropy.Chowla.log_chowla_two_shell_xi_h` | Salt/Entropy/Chowla/Theorem23Shell.lean:488 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXiH` |
| `Salt.Entropy.Chowla.log_chowla_two_shell_xi_sq_h` | Salt/Entropy/Chowla/Theorem23Shell.lean:627 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2H` |
| `Salt.Entropy.Chowla.log_chowla_two_of_door` | Salt/Entropy/Chowla/TowerDischarge.lean:97 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformity` |
| `Salt.Entropy.Chowla.slots_iff_completelyMult` | Salt/Entropy/Chowla/TransportWall.lean:109 | entropy | `Salt.Entropy.Chowla.PmNormalized` |
| `Salt.Entropy.Chowla.orthogonality_wall` | Salt/Entropy/Chowla/TransportWall.lean:143 | entropy | `Salt.Entropy.Chowla.PairCollapse` |
| `Salt.Entropy.Chowla.no_slot_derived_twin_linkage` | Salt/Entropy/Chowla/TransportWall.lean:155 | entropy | `Salt.Entropy.Chowla.TwinDetecting` |
| `FiniteRange.real_full` | Salt/Entropy/FiniteRange.lean:159 | entropy | `FiniteRange` |
| `FiniteRange.null_of_compl` | Salt/Entropy/FiniteRange.lean:164 | entropy | `FiniteRange` |
| `ProbabilityTheory.Kernel.entropy_compProd` | Salt/Entropy/Kernel/Basic.lean:309 | entropy | `ProbabilityTheory.FiniteSupport`, `ProbabilityTheory.Kernel.AEFiniteKernelSupport` |
| `ProbabilityTheory.Kernel.chain_rule` | Salt/Entropy/Kernel/Basic.lean:350 | entropy | `ProbabilityTheory.FiniteSupport`, `ProbabilityTheory.Kernel.AEFiniteKernelSupport` |
| `ProbabilityTheory.Kernel.entropy_triple_add_entropy_le'` | Salt/Entropy/Kernel/MutualInfo.lean:360 | entropy | `ProbabilityTheory.FiniteSupport`, `ProbabilityTheory.Kernel.AEFiniteKernelSupport` |
| `ProbabilityTheory.measureEntropy_prod` | Salt/Entropy/Measure.lean:505 | entropy | `ProbabilityTheory.FiniteSupport` |
| `ProbabilityTheory.measureMutualInfo_nonneg` | Salt/Entropy/Measure.lean:813 | entropy | `ProbabilityTheory.FiniteSupport` |
| `Salt.ExpSum.isVdCBound_affine` | Salt/ExpSum/Twist.lean:143 | exponential sums | `Salt.ExpSum.IsVdCBound` |
| `Salt.Fulcrum.imsz_implies_fulcrum_of_gadget` | Salt/Fulcrum/Basic.lean:193 | other | `Salt.Fulcrum.SiegelModulusUnbounded`, `Salt.TwinBar.InfinitelyManySiegelZeros` |
| `Salt.Fulcrum.not_fulcrum_implies_noSiegelZeros` | Salt/Fulcrum/Dichotomy.lean:82 | other | `¬Salt.Fulcrum.FulcrumQualityMin` |
| `Salt.Fulcrum.fulcrum_dichotomy` | Salt/Fulcrum/Dichotomy.lean:102 | other | `TwinPrimeConjecture` |
| `Salt.Fulcrum.imsz_gives_fulcrum_witnesses` | Salt/Fulcrum/Gadget.lean:128 | characters | `Salt.TwinBar.InfinitelyManySiegelZeros` |
| `Salt.Goldbach.gold_A1_lower_B` | Salt/Goldbach/A1.lean:235 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Goldbach.gold_A1_lower_B_W` | Salt/Goldbach/A1W.lean:264 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.Goldbach.gold_A2_per_prime_W` | Salt/Goldbach/A2W.lean:313 | sieves | `Salt.Chen.StepHypWPC` |
| `Salt.HB.deltaSum_nuG_mul_additive` | Salt/HB/CrownAssembly.lean:381 | characters | `Salt.HB.IsAdditiveOn` |
| `Salt.HB.deltaSum_nuG_mul_additive_le` | Salt/HB/CrownAssembly.lean:523 | characters | `Salt.HB.IsAdditiveOn` |
| `Salt.HB.deltaSum_nuG_mul_sq_additive_le` | Salt/HB/CrownAssembly.lean:812 | characters | `Salt.HB.IsAdditiveOn` |
| `Salt.HB.moebSum_nuG_mul_additive` | Salt/HB/CrownAssembly.lean:942 | sieves, characters | `Salt.HB.IsAdditiveOn` |
| `Salt.HB.moebSum_nuG_mul_additive_le` | Salt/HB/CrownAssembly.lean:964 | characters | `Salt.HB.IsAdditiveOn` |
| `Salt.HB.moebSum_nuG_mul_sq_additive_le` | Salt/HB/CrownAssembly.lean:991 | characters | `Salt.HB.IsAdditiveOn` |
| `Salt.HB.hb_transfer_additive` | Salt/HB/CrownAssembly.lean:1144 | characters | `Salt.HB.IsAdditiveOn` |
| `Salt.HB.hb_transfer_sq_additive` | Salt/HB/CrownAssembly.lean:1160 | characters | `Salt.HB.IsAdditiveOn` |
| `Salt.HB.hb_p200_upper` | Salt/HB/CrownAssembly.lean:1671 | sieves, characters | `Salt.HB.Lemma5Eval` |
| `Salt.HB.hb_p200_lower` | Salt/HB/CrownAssembly.lean:1704 | sieves, characters | `Salt.HB.Lemma5Eval` |
| `Salt.HB.hbZ_packet` | Salt/HB/CrownTheorem1.lean:649 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.re_le_beta0_of_ne` | Salt/HB/CrownTheorem1.lean:975 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.dh_ceiling_box` | Salt/HB/CrownTheorem1.lean:1151 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.dh_floor_ball` | Salt/HB/CrownTheorem1.lean:1284 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.sinv_ball` | Salt/HB/CrownTheorem1.lean:1380 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.hb_zero_data` | Salt/HB/CrownTheorem1.lean:1565 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.hb_L1_lower_at_hb_point` | Salt/HB/CrownTheorem1.lean:1693 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.hb_L1_upper_at_hb_point` | Salt/HB/CrownTheorem1.lean:1921 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.pretenseSum_at_hb_point` | Salt/HB/CrownTheorem1.lean:2169 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.chiOne_kill_at_hb_point` | Salt/HB/CrownTheorem1.lean:2196 | sieves, characters | `Salt.HB.N9Regime` |
| `Salt.HB.real_zeros_below_zfrCeil` | Salt/HB/CrownTheorem1.lean:2238 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.logChiSum_tail_at_window` | Salt/HB/CrownTheorem1.lean:3517 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.hbEulerLog_tendsto` | Salt/HB/CrownTheorem1.lean:3612 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.hcorr_at_split` | Salt/HB/CrownTheorem1.lean:3857 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.hb_L2_at_hb_point` | Salt/HB/CrownTheorem1.lean:3979 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.hb_lemma4_at_hb_point` | Salt/HB/CrownTheorem1.lean:4930 | characters | `Salt.HB.N9Regime` |
| `Salt.HB.hb_S3_lower_at_hb_point` | Salt/HB/CrownTheorem1.lean:5440 | characters | `Salt.HB.N9Regime`, `Salt.HB.N7Exit` |
| `Salt.HB.hb_theorem1` | Salt/HB/CrownTheorem1.lean:6043 | characters | `Salt.HB.N9Regime`, `Salt.HB.N7Exit` |
| `Salt.HB.hb_theorem1_lower` | Salt/HB/CrownTheorem1.lean:6311 | characters | `Salt.HB.N9Regime`, `Salt.HB.N7Exit` |
| `Salt.HB.noSiegelZerosPoly_mono` | Salt/HB/CrownTheorem1.lean:6384 | characters | `Salt.HB.NoSiegelZerosPoly` |
| `Salt.HB.not_fulcrumPoly_implies_noSiegelZerosPoly` | Salt/HB/CrownTheorem1.lean:6414 | characters | `¬Salt.HB.FulcrumQualityPoly` |
| `Salt.HB.fulcrum_dichotomy_poly` | Salt/HB/CrownTheorem1.lean:6463 | characters | `TwinPrimeConjecture` |
| `Salt.HB.fulcrumQualityMin_of_poly` | Salt/HB/CrownTheorem1.lean:6519 | characters | `Salt.HB.FulcrumQualityPoly` |
| `Salt.HB.crown_handover_k1` | Salt/HB/CrownTheorem1.lean:6577 | characters | `Salt.HB.N7Exit`, `Salt.Fulcrum.FulcrumQualityMin` |
| `Salt.HB.crown_handover` | Salt/HB/CrownTheorem1.lean:6902 | characters | `Salt.HB.N7Exit`, `Salt.HB.FulcrumQualityPoly` |
| `Salt.HB.hEngine_poly_of_N7` | Salt/HB/CrownTheorem1.lean:6916 | characters | `Salt.HB.N7Exit`, `Salt.HB.FulcrumQualityPoly` |
| `Salt.HB.hEngine_of_N7` | Salt/HB/CrownTheorem1.lean:6925 | characters | `Salt.HB.N7Exit`, `Salt.Fulcrum.FulcrumQualityMin` |
| `Salt.HB.heathBrownDichotomyPoly_of_N7` | Salt/HB/CrownTheorem1.lean:6939 | characters | `Salt.HB.N7Exit` |
| `Salt.HB.heathBrownDichotomy_of_N7` | Salt/HB/CrownTheorem1.lean:6957 | characters | `Salt.HB.N7Exit` |
| `Salt.HB.hb_p200_lower_HB` | Salt/HB/CrownWireHB.lean:257 | sieves, characters | `Salt.HB.Lemma5Eval` |
| `Salt.HB.hb_lemma3_at_repulsion_floor` | Salt/HB/Lemma3Floor.lean:160 | characters | `Salt.HB.CoprimeSupport` |
| `Salt.HB.hb_lemma3_unconditional` | Salt/HB/Lemma3Uncond.lean:58 | characters | `Salt.HB.CoprimeSupport` |
| `Salt.HB.hb_lemma2_of_pretenseSum_le` | Salt/HB/PretenseSumProof.lean:612 | characters | `Salt.HB.CoprimeSupport` |
| `Salt.HB.hb_lemma2_at_hb_rate` | Salt/HB/PretenseSumProof.lean:630 | characters | `Salt.HB.CoprimeSupport` |
| `Salt.HB.HasTwoFormGcdBound.mul` | Salt/HB/RealPrimitive.lean:191 | characters | `Salt.HB.HasTwoFormGcdBound` |
| `Salt.HB.sum_two_forms_le_gcd_of_split` | Salt/HB/RealPrimitive.lean:383 | characters | `Salt.HB.HasTwoFormGcdBound` |
| `Salt.HB.chi_log_le_level` | Salt/HB/RosserDim4.lean:186 | characters | `Salt.BrunLower.chi` |
| `Salt.HB.chi_le_rpow_level` | Salt/HB/RosserDim4.lean:295 | characters | `Salt.BrunLower.chi` |
| `Salt.HB.flB_level_bound` | Salt/HB/RosserDim4FL.lean:168 | characters | `Salt.BrunLower.chi` |
| `Salt.HB.exists_firstFailure` | Salt/HB/RosserDim4FL.lean:557 | characters | `¬Salt.BrunLower.chi` |
| `Salt.HB.failSet_forced_count` | Salt/HB/RosserDim4FL.lean:710 | characters | `¬Salt.BrunLower.chi`, `Salt.BrunLower.chi` |
| `Salt.HB.S1_le_S2Gen` | Salt/HB/SignChain.lean:511 | characters | `Salt.HB.IsSignFunction` |
| `Salt.HB.neutrality_rate` | Salt/HB/SignRate.lean:53 | characters | `Salt.HB.IsSignFunction` |
| `Salt.HB.S2_sub_S1_le` | Salt/HB/Transfer.lean:199 | characters | `Salt.HB.CoprimeSupport` |
| `Salt.HB.hb_lemma2` | Salt/HB/TransferFull.lean:204 | characters | `Salt.HB.CoprimeSupport` |
| `Salt.HB.hb_lemma3_final` | Salt/HB/TwistedMertens.lean:797 | characters | `Salt.HB.CoprimeSupport` |
| `Salt.LS.analytic_LS` | Salt/LS/AnalyticLS.lean:58 | sieves, exponential sums | `Salt.LS.Spaced` |
| `Salt.MR.seam_row_number_nocap3_end'` | Salt/MR/A3Middle.lean:203 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.seam_row_number_capfree3_end'` | Salt/MR/A3Middle.lean:331 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.a2Rows_of_capfree3_end'` | Salt/MR/A3Middle.lean:437 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.seam_row_number_nocap3'` | Salt/MR/A3Middle.lean:572 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.seam_row_number_capfree3'` | Salt/MR/A3Middle.lean:698 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.a2Rows_of_capfree3'` | Salt/MR/A3Middle.lean:804 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.largeRangeFixedEps_of_fixed` | Salt/MR/A4FLargeRange.lean:101 | characters | `Salt.MR.MRTLargeRangeEquidistributionFixed` |
| `Salt.MR.lemmaA4iiFixed34E_of_fixed34T` | Salt/MR/A4FLargeRange.lean:115 | characters | `Salt.MR.MRTLemmaA4iiFixed34T` |
| `Salt.MR.mrtLemmaA4iiFixed34T_of_largeRangeFixed` | Salt/MR/A4FThreshold.lean:124 | characters | `Salt.MR.MRTLargeRangeEquidistributionFixed` |
| `Salt.MR.DoorArithFrameRho_L.armWeak` | Salt/MR/ArithPageLinear.lean:356 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.DoorArithFrameRho_L.loglogX_ge` | Salt/MR/ArithPageLinear.lean:363 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.DoorArithFrameRho_L.one_lt_logX` | Salt/MR/ArithPageLinear.lean:370 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.DoorArithFrameRho_L.of_landed` | Salt/MR/ArithPageLinear.lean:379 | characters | `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.a2DoorGrade_L_priced_rho` | Salt/MR/ArithPageLinear.lean:529 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.socketBase_of_socketBaseL` | Salt/MR/ArithPageLinear.lean:702 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.s15_doorArithFrameRho_L_at_socket''` | Salt/MR/ArithPageLinear.lean:718 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.s15_doorArithFrameRho_L_family''` | Salt/MR/ArithPageLinear.lean:775 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.a2DoorGrade_pool_L_priced_rho` | Salt/MR/ArithPageLinear.lean:819 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_arith_henv_rho_L` | Salt/MR/ArithPageLinear.lean:864 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_scale_gate_at_socket` | Salt/MR/BandRatedSocket.lean:99 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_threshold_at_socket_rated` | Salt/MR/BandRatedSocket.lean:192 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_capFreeFloor_at_socket_rated` | Salt/MR/BandRatedSocket.lean:293 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.nearRat_mono` | Salt/MR/BigXiArc.lean:188 | characters | `Salt.MR.NearRat` |
| `Salt.MR.exists_large_den_of_not_nearRat` | Salt/MR/BigXiArc.lean:274 | characters | `¬Salt.MR.NearRat` |
| `Salt.MR.exists_large_den_of_minor` | Salt/MR/BigXiArc.lean:331 | characters | `¬Salt.MR.NearRat` |
| `Salt.MR.bigXiArc_of_minorArc` | Salt/MR/BigXiArc.lean:480 | characters | `Salt.MR.MinorArcBound` |
| `Salt.MR.bigXiArc_mono` | Salt/MR/BigXiArc.lean:502 | characters | `Salt.MR.BigXiArc` |
| `Salt.MR.nearRat_of_nearRatTight` | Salt/MR/BigXiArc.lean:581 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.nearRatTight_imp_nearRat` | Salt/MR/BigXiArc.lean:595 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.nearRatTight_mono` | Salt/MR/BigXiArc.lean:604 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.exists_large_den_of_not_nearRatTight` | Salt/MR/BigXiArc.lean:684 | characters | `¬Salt.MR.NearRatTight` |
| `Salt.MR.exists_large_den_of_minorTight` | Salt/MR/BigXiArc.lean:712 | characters | `¬Salt.MR.NearRatTight` |
| `Salt.MR.bigXiArcTight_of_minorArcTight` | Salt/MR/BigXiArc.lean:736 | characters | `Salt.MR.MinorArcBoundTight` |
| `Salt.MR.bigXiArc_of_bigXiArcTight` | Salt/MR/BigXiArc.lean:750 | characters | `Salt.MR.BigXiArcTight` |
| `Salt.MR.minorArcBound_of_minorArcBoundTight` | Salt/MR/BigXiArc.lean:762 | characters | `Salt.MR.MinorArcBoundTight` |
| `Salt.MR.bigXiArcTight_mono` | Salt/MR/BigXiArc.lean:782 | characters | `Salt.MR.BigXiArcTight` |
| `Salt.MR.no_pocket_of_floor` | Salt/MR/CapFreeArm.lean:140 | characters | `Salt.MR.CapFreeFloor` |
| `Salt.MR.pocketSocket_of_row` | Salt/MR/CapFreeArm.lean:209 | characters | `Salt.MR.collisionGate` |
| `Salt.MR.pocketSocket_of_floor` | Salt/MR/CapFreeArm.lean:230 | characters | `Salt.MR.CapFreeFloor` |
| `Salt.MR.cofactor_Rbd34_local_nocap` | Salt/MR/CapFreeArm.lean:281 | characters | `Salt.MR.PocketSocket`, `Salt.MR.CaseASocket2` |
| `Salt.MR.tL_supply_discharged34_local_nocap` | Salt/MR/CapFreeArm.lean:351 | characters | `Salt.MR.WellSpaced`, `Salt.MR.PocketSocket`, `Salt.MR.CaseASocket2` |
| `Salt.MR.hUG34_supplied_nocap` | Salt/MR/CapFreeArm.lean:413 | characters | `Salt.MR.TannGate`, `Salt.MR.PocketSocket`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocket2` |
| `Salt.MR.hUG34_fully_priced_nocap` | Salt/MR/CapFreeArm.lean:517 | characters | `Salt.MR.TannGate`, `Salt.MR.PocketSocket`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocket2` |
| `Salt.MR.hUG34_unconditional_nocap` | Salt/MR/CapFreeArm.lean:644 | characters | `Salt.MR.TannGate`, `Salt.MR.PocketSocket`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.hUG34_unconditional_beats_door_nocap` | Salt/MR/CapFreeArm.lean:750 | characters | `Salt.MR.TannGate`, `Salt.MR.PocketSocket`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.seam_row_calibratedK_nocap` | Salt/MR/CapFreeArm.lean:843 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.PocketSocket`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.seam_row_number_nocap` | Salt/MR/CapFreeArm.lean:1018 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.PocketSocket`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.seam_row_number_capfree` | Salt/MR/CapFreeArm.lean:1176 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CapFreeFloor`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.capFreeFloor_of_capFreeFloor3` | Salt/MR/CapFreeArm3.lean:82 | characters | `Salt.MR.CapFreeFloor3` |
| `Salt.MR.no_pocket_of_floor3` | Salt/MR/CapFreeArm3.lean:100 | characters | `Salt.MR.CapFreeFloor3` |
| `Salt.MR.pocketSocket_of_floor3` | Salt/MR/CapFreeArm3.lean:152 | characters | `Salt.MR.CapFreeFloor3` |
| `Salt.MR.cofactor_Rbd34_local_nocap3` | Salt/MR/CapFreeArm3.lean:175 | characters | `Salt.MR.PocketSocket3`, `Salt.MR.CaseASocket2` |
| `Salt.MR.CofactorSocket.mono` | Salt/MR/CapFreeArm3.lean:264 | characters | `Salt.MR.CofactorSocket` |
| `Salt.MR.cofactorSocket_of_pieces` | Salt/MR/CapFreeArm3.lean:289 | characters | `Salt.MR.CofactorSocket` |
| `Salt.MR.cofactorSocket_of_ellLin` | Salt/MR/CapFreeArm3.lean:311 | characters | `Salt.MR.PocketSocket3`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocket2` |
| `Salt.MR.tL_supply_discharged34_local_nocap3` | Salt/MR/CapFreeArm3.lean:345 | characters | `Salt.MR.WellSpaced`, `Salt.MR.CofactorSocket` |
| `Salt.MR.hUG34_supplied_nocap3` | Salt/MR/CapFreeArm3.lean:381 | characters | `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.hUG34_fully_priced_nocap3` | Salt/MR/CapFreeArm3.lean:466 | characters | `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.hUG34_unconditional_nocap3` | Salt/MR/CapFreeArm3.lean:574 | characters | `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.seam_row_calibratedK_nocap3` | Salt/MR/CapFreeArm3.lean:646 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.seam_row_number_nocap3` | Salt/MR/CapFreeArm3.lean:814 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.seam_row_number_capfree3` | Salt/MR/CapFreeArm3.lean:948 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.A2Frame3.box_at` | Salt/MR/CapFreeArm3.lean:1102 | characters | `Salt.MR.A2Frame3` |
| `Salt.MR.A2Frame3.ksGate_at` | Salt/MR/CapFreeArm3.lean:1110 | characters | `Salt.MR.A2Frame3` |
| `Salt.MR.seam_row_calibratedK_nocap3_end` | Salt/MR/CapFreeArm3.lean:1134 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.seam_row_number_nocap3_end` | Salt/MR/CapFreeArm3.lean:1298 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.seam_row_number_capfree3_end` | Salt/MR/CapFreeArm3.lean:1422 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.CofactorSocket`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.capFreeFloor3_liouChi_of_lamChi` | Salt/MR/CapFreeAssembly.lean:479 | characters | `Salt.MR.CapFreeFloor3` |
| `Salt.MR.joint_cs_trunc_pin2C` | Salt/MR/CaseASocket.lean:548 | characters | `Salt.MR.JointIntegrableAtC` |
| `Salt.MR.beta_integral_pin_const2C` | Salt/MR/CaseASocket.lean:634 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.rhs_grade_at_scale_window2C` | Salt/MR/CaseASocket.lean:717 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAtC` |
| `Salt.MR.caseA_rhs_socket2` | Salt/MR/CaseASocket.lean:849 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseA_partial_supply2` | Salt/MR/CaseASocket.lean:918 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseA_slice2` | Salt/MR/CaseASocket.lean:1014 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseASocket2_discharged` | Salt/MR/CaseASocket.lean:1059 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseA_partial_supply_wide` | Salt/MR/CaseAWide.lean:410 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseA_slice_wide` | Salt/MR/CaseAWide.lean:498 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseA_wide_floor` | Salt/MR/CaseAWide.lean:543 | characters | `Salt.MR.CapFreeFloor3` |
| `Salt.MR.caseA_inner_wide` | Salt/MR/CaseAWide.lean:580 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseASocketGen_mono` | Salt/MR/CaseAWide.lean:614 | characters | `Salt.MR.CaseASocketGen` |
| `Salt.MR.caseASocketGen_wide` | Salt/MR/CaseAWide.lean:632 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.CapFreeFloor3` |
| `Salt.MR.caseASocketGen_discharged_door` | Salt/MR/CaseAWide.lean:679 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.CapFreeFloor3` |
| `Salt.MR.cofactorSocket_of_gen_tb` | Salt/MR/CaseAWide.lean:719 | characters | `Salt.MR.PocketSocket3Gen`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocketGen` |
| `Salt.MR.cofactorSocket_door_tb` | Salt/MR/CaseAWide.lean:749 | characters | `Salt.MR.CapFreeFloor3`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocketGen` |
| `Salt.MR.m4_supplier_complete` | Salt/MR/CaseAWide.lean:810 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.CapFreeFloor3`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.caseB_ramR_bound` | Salt/MR/CofactorBall.lean:586 | characters | `Salt.MR.collisionGate` |
| `Salt.MR.cofkL_socket_floors` | Salt/MR/CofactorBulk.lean:201 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_q_le_arcCap` | Salt/MR/CofactorBulk.lean:236 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_cofactorSupply_L_gk_of_bulk` | Salt/MR/CofactorBulk.lean:349 | characters | `Salt.MR.CofactorBulkL` |
| `Salt.MR.cofkL_cofactorSupply_L_gk_flat` | Salt/MR/CofactorBulk.lean:606 | characters | `Salt.MR.CofactorBulkL` |
| `Salt.MR.caseA_rhs_socket` | Salt/MR/CofactorGrade.lean:428 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseA_partial_supply` | Salt/MR/CofactorGrade.lean:508 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseA_ramR_bound` | Salt/MR/CofactorGrade.lean:687 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.caseA_ramR_bound_293` | Salt/MR/CofactorGrade.lean:778 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.cofactor_Rbd_local` | Salt/MR/CofactorLocal.lean:228 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.tL_supply_discharged_local` | Salt/MR/CofactorLocal.lean:352 | characters | `Salt.MR.WellSpaced`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate` |
| `Salt.MR.cofactorSocket_of_pieces_finset` | Salt/MR/CofactorSupplier.lean:201 | characters | `Salt.MR.CofactorSocket` |
| `Salt.MR.cofactorSocket_door_of_pieces` | Salt/MR/CofactorSupplier.lean:240 | characters | `Salt.MR.CofactorSocket` |
| `Salt.MR.pocketSocket3Gen_of_floor3` | Salt/MR/CofactorSupplier.lean:500 | characters | `Salt.MR.CapFreeFloor3` |
| `Salt.MR.cofactor_Rbd34_local_nocap3_gen` | Salt/MR/CofactorSupplier.lean:672 | characters | `Salt.MR.PocketSocket3Gen`, `Salt.MR.CaseASocketGen` |
| `Salt.MR.cofactorSocket_of_gen` | Salt/MR/CofactorSupplier.lean:737 | characters | `Salt.MR.PocketSocket3Gen`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocketGen` |
| `Salt.MR.cofactorSocket_door` | Salt/MR/CofactorSupplier.lean:781 | characters | `Salt.MR.CapFreeFloor3`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocketGen` |
| `Salt.MR.caseA_floor_of_capFreeFloor3` | Salt/MR/CofactorSupplier.lean:1012 | characters | `Salt.MR.CapFreeFloor3` |
| `Salt.MR.caseA_partial_supply_slice` | Salt/MR/CofactorSupply.lean:214 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.cofactor_Rbd` | Salt/MR/CofactorSupply.lean:396 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate` |
| `Salt.MR.cofactor_Rbd_293` | Salt/MR/CofactorSupply.lean:648 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.tL_supply_discharged` | Salt/MR/CofactorSupply.lean:711 | characters | `Salt.MR.WellSpaced`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate` |
| `Salt.MR.budget_head_at_H0door` | Salt/MR/DoorFloor.lean:250 | characters | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.MR.budget_head_grade_closed` | Salt/MR/DoorFloor.lean:264 | characters | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.MR.budget_head_grade_closed_g` | Salt/MR/DoorFloor.lean:296 | characters | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.MR.budget_head_at_mrt_floors` | Salt/MR/DoorFloor.lean:503 | characters | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.MR.budget_head_sq_at_mrt_floors` | Salt/MR/DoorFloor.lean:580 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.budget_head_at_mrt_floors_34` | Salt/MR/DoorFloor.lean:612 | characters | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.MR.budget_head_sq_at_mrt_floors_34` | Salt/MR/DoorFloor.lean:636 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.chi_floor_real_door_w` | Salt/MR/DoorFloor1500.lean:353 | characters | `Salt.MR.L1LowerEffective` |
| `Salt.MR.chi_floor_real_door_12` | Salt/MR/DoorFloor1500.lean:383 | characters | `Salt.MR.L1LowerEffective` |
| `Salt.MR.s16_baseScaleCapL_of_baseScaleCap` | Salt/MR/DoorLinear.lean:488 | characters | `Salt.MR.S16BaseScaleCap_gk` |
| `Salt.MR.s16_baseScaleCapL96_of_baseScaleCapL` | Salt/MR/DoorLinear.lean:504 | characters | `Salt.MR.S16BaseScaleCapL_gk` |
| `Salt.MR.flat_socket_generic` | Salt/MR/DoorReceipt.lean:144 | characters | `Salt.MR.FlatHeadForm` |
| `Salt.MR.flat_doorL2_generic` | Salt/MR/DoorReceipt.lean:192 | characters | `Salt.MR.FlatSocketForm` |
| `Salt.MR.flat_road_generic` | Salt/MR/DoorReceipt.lean:273 | characters | `Salt.MR.FlatDoorL2Form` |
| `Salt.MR.flat_capstone_generic` | Salt/MR/DoorReceipt.lean:433 | characters | `Salt.MR.FlatRoadForm`, `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.flat_conditional_generic` | Salt/MR/DoorReceipt.lean:610 | characters | `Salt.MR.FlatCapstoneForm` |
| `Salt.MR.flat_kswin_generic` | Salt/MR/DoorReceipt.lean:775 | characters | `Salt.MR.FlatConditionalForm` |
| `Salt.MR.flat_v7_generic` | Salt/MR/DoorReceipt.lean:873 | characters | `Salt.MR.FlatKswinForm` |
| `Salt.MR.flat_chain_generic` | Salt/MR/DoorReceipt.lean:1076 | characters | `Salt.MR.FlatHeadForm` |
| `Salt.MR.mrtUniformityXi_of_xiL2` | Salt/MR/DoorReceipt.lean:1128 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.door_absWindowSum_sq_le_strata` | Salt/MR/DoorRoadCompose.lean:73 | sieves, characters | `Salt.MR.NearRatTight` |
| `Salt.MR.door_absWindowSum_sq_le_dyadic` | Salt/MR/DoorRoadCompose.lean:144 | sieves, characters | `Salt.MR.NearRatTight` |
| `Salt.MR.logChowla2_epsFamily_of_allGrades` | Salt/MR/EpsFamilyReceipt.lean:42 | characters | `Salt.MR.MRTDoorAllGrades` |
| `Salt.MR.eq26` | Salt/MR/Eq26Bridge.lean:223 | characters | `Salt.MR.Lemma4Comparison` |
| `Salt.MR.eq26_pinned` | Salt/MR/Eq26Bridge.lean:242 | characters | `Salt.MR.Lemma4Comparison` |
| `Salt.MR.Lemma4Datum.gJR_mul` | Salt/MR/Eq26Bridge.lean:325 | characters | `Salt.MR.Lemma4Datum` |
| `Salt.MR.thm3_of_step1_and_eq26` | Salt/MR/Eq26Compose.lean:315 | characters | `Salt.MR.Lemma4Comparison` |
| `Salt.MR.thm3_meansq_pinned` | Salt/MR/Eq26Compose.lean:376 | characters | `Salt.MR.Lemma4Comparison` |
| `Salt.MR.thm3_meansq_of_kernel` | Salt/MR/Eq26Compose.lean:458 | characters | `Salt.MR.Lemma4Comparison` |
| `Salt.MR.rhs_grade_at_scale_closed` | Salt/MR/FarClose.lean:460 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.hRHS_socket_of_far` | Salt/MR/FarClose.lean:516 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.ball_sup_closed` | Salt/MR/FarClose.lean:568 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.plog_floor_nonreal` | Salt/MR/FarL2.lean:323 | characters | `Salt.MR.VkTwistUB` |
| `Salt.MR.joint_cs_trunc_polylog` | Salt/MR/FarL2Dyadic.lean:774 | characters | `Salt.MR.JointIntegrableAtC` |
| `Salt.MR.dilated_scale_grade_polylog` | Salt/MR/FarL2Dyadic.lean:833 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.rhs_grade_at_scale_closed_star` | Salt/MR/FarStar.lean:712 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.hRHS_socket_star` | Salt/MR/FarStar.lean:755 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.ball_sup_closed_star` | Salt/MR/FarStar.lean:826 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.flatHeadFormEpsW_at_grade` | Salt/MR/FlatDoorAllGrades.lean:89 | characters | `Salt.MR.FlatHeadFormEpsW` |
| `Salt.MR.crownWd_zero_level_landed` | Salt/MR/FlatDoorAllGrades.lean:121 | characters | `Salt.MR.FlatDoorAllGradesW` |
| `Salt.MR.crownWd_L1_on_flat` | Salt/MR/FlatDoorAllGrades.lean:134 | characters | `Salt.MR.FlatDoorAllGradesW` |
| `Salt.MR.crownNV_Wdelta_nonvacuous` | Salt/MR/FlatDoorAllGrades.lean:150 | characters | `Salt.MR.FlatDoorAllGradesW`, `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.crownNV_Wdelta_nonvacuous_holds` | Salt/MR/FlatDoorAllGrades.lean:172 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_at_tight` | Salt/MR/FlatDoorAllGradesBand.lean:491 | characters | `Salt.MR.XCeilRiderAt` |
| `Salt.MR.flat_socket_generic_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:718 | characters | `Salt.MR.FlatHeadFormEpsW_band` |
| `Salt.MR.flat_doorL2_generic_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:752 | characters | `Salt.MR.FlatSocketFormEpsW_band` |
| `Salt.MR.flat_road_generic_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:802 | characters | `Salt.MR.FlatDoorL2FormEpsW_band` |
| `Salt.MR.flat_capstone_generic_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:872 | characters | `Salt.MR.FlatRoadFormEpsW_band`, `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.flat_conditional_generic_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:1062 | characters | `Salt.MR.FlatCapstoneFormEpsW_band` |
| `Salt.MR.flat_kswin_generic_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:1216 | characters | `Salt.MR.FlatConditionalFormEpsW_band` |
| `Salt.MR.flat_v7_generic_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:1329 | characters | `Salt.MR.FlatKswinFormEpsW_band` |
| `Salt.MR.flat_chain_generic_epsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:1473 | characters | `Salt.MR.FlatHeadFormEpsW_band` |
| `Salt.MR.flatHeadFormEpsW_band_at_grade` | Salt/MR/FlatDoorAllGradesBand.lean:1497 | characters | `Salt.MR.FlatHeadFormEpsW_band` |
| `Salt.MR.crownBand_door_at_bottom` | Salt/MR/FlatDoorAllGradesBand.lean:1726 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.crownBand_zero_level` | Salt/MR/FlatDoorAllGradesBand.lean:1735 | characters | `Salt.MR.FlatDoorAllGradesBandW` |
| `Salt.MR.mrtUniformityXiL2_mono` | Salt/MR/FlatDoorEpsChain.lean:54 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.s16CofactorSupply_L_of_LH` | Salt/MR/FlatDoorEpsChain.lean:62 | characters | `Salt.MR.S16CofactorSupply_LH_gk` |
| `Salt.MR.s16BaseScaleCap96_L_of_LH` | Salt/MR/FlatDoorEpsChain.lean:69 | characters | `Salt.MR.S16BaseScaleCap96_LH_gk` |
| `Salt.MR.flat_socket_generic_eps` | Salt/MR/FlatDoorEpsChain.lean:713 | characters | `Salt.MR.FlatHeadFormEps` |
| `Salt.MR.flat_doorL2_generic_eps` | Salt/MR/FlatDoorEpsChain.lean:738 | characters | `Salt.MR.FlatSocketFormEps` |
| `Salt.MR.flat_road_generic_eps` | Salt/MR/FlatDoorEpsChain.lean:783 | characters | `Salt.MR.FlatDoorL2FormEps` |
| `Salt.MR.flat_capstone_generic_eps` | Salt/MR/FlatDoorEpsChain.lean:845 | characters | `Salt.MR.FlatRoadFormEps`, `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.flat_conditional_generic_eps` | Salt/MR/FlatDoorEpsChain.lean:993 | characters | `Salt.MR.FlatCapstoneFormEps` |
| `Salt.MR.flat_kswin_generic_eps` | Salt/MR/FlatDoorEpsChain.lean:1121 | characters | `Salt.MR.FlatConditionalFormEps` |
| `Salt.MR.flat_v7_generic_eps` | Salt/MR/FlatDoorEpsChain.lean:1211 | characters | `Salt.MR.FlatKswinFormEps` |
| `Salt.MR.flat_chain_generic_eps` | Salt/MR/FlatDoorEpsChain.lean:1340 | characters | `Salt.MR.FlatHeadFormEps` |
| `Salt.MR.mrtUniformityXiL2_holds_flat_epsFamily_capped` | Salt/MR/FlatDoorEpsFamily.lean:155 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.mrtUniformityXiL2_holds_flat_of_epsFamily` | Salt/MR/FlatDoorEpsFamily.lean:191 | characters | `Salt.MR.FlatDoorEpsFamilyW` |
| `Salt.MR.logChowla2_epsFamily_of_flatDoor` | Salt/MR/FlatDoorEpsFamily.lean:208 | characters | `Salt.MR.FlatDoorEpsFamilyW` |
| `Salt.MR.logChowla2_epsFamily_of_flatDoor_floor` | Salt/MR/FlatDoorEpsFamily.lean:224 | characters | `Salt.MR.FlatDoorEpsFamilyW` |
| `Salt.MR.mrtUniformityXiL2_holds_flat_epsFamily_capped_of_epsFamily` | Salt/MR/FlatDoorEpsFamily.lean:243 | characters | `Salt.MR.FlatDoorEpsFamilyW`, `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.mrtUniformityXiL2_holds_flat_epsFamily_of_payload` | Salt/MR/FlatDoorEpsFamily.lean:312 | characters | `Salt.MR.FlatDoorPayload`, `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.cofk_tower_logfloor_L` | Salt/MR/FlatDoorEpsRung2.lean:550 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_tower_logH_L` | Salt/MR/FlatDoorEpsRung2.lean:582 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_twoj_le_H_L` | Salt/MR/FlatDoorEpsRung2.lean:606 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_logA_ge_sqrt_L` | Salt/MR/FlatDoorEpsRung2.lean:629 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_loglogA_sharp_L` | Salt/MR/FlatDoorEpsRung2.lean:710 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_mu_lo_L` | Salt/MR/FlatDoorEpsRung2.lean:730 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_core_L` | Salt/MR/FlatDoorEpsRung2.lean:745 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_mu_2000_L` | Salt/MR/FlatDoorEpsRung2.lean:786 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Lambda_sharp_L` | Salt/MR/FlatDoorEpsRung2.lean:801 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Lambda_lo_L` | Salt/MR/FlatDoorEpsRung2.lean:823 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_socket_floors_L` | Salt/MR/FlatDoorEpsRung2.lean:845 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_logX_floor_L` | Salt/MR/FlatDoorEpsRung2.lean:981 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_mu_floor_L` | Salt/MR/FlatDoorEpsRung2.lean:1131 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_X_ge_expexp_L` | Salt/MR/FlatDoorEpsRung2.lean:1164 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_scale_gate_at_socket_L` | Salt/MR/FlatDoorEpsRung2.lean:1202 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_threshold_at_socket_rated_L` | Salt/MR/FlatDoorEpsRung2.lean:1291 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_capFreeFloor_at_socket_rated_uniform_L` | Salt/MR/FlatDoorEpsRung2.lean:1386 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.xCeilGateAt_mono` | Salt/MR/FlatDoorEpsRung2.lean:2862 | characters | `Salt.MR.XCeilGateAt` |
| `Salt.MR.xCeilRiderAt_mono` | Salt/MR/FlatDoorEpsRung2.lean:2868 | characters | `Salt.MR.XCeilRiderAt` |
| `Salt.MR.xCeilRiderStrictAt_mono` | Salt/MR/FlatDoorEpsRung2.lean:2873 | characters | `Salt.MR.XCeilRiderStrictAt` |
| `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_at` | Salt/MR/FlatDoorEpsRung2.lean:2900 | characters | `Salt.MR.XCeilRiderAt` |
| `Salt.MR.xCeilRiderAt_arm_add` | Salt/MR/FlatDoorEpsRung2.lean:3004 | characters | `Salt.MR.XCeilRiderStrictAt` |
| `Salt.MR.S15Sel''_L.toT` | Salt/MR/FlatDoorEpsRung2.lean:3878 | characters | `Salt.MR.S15Sel''_L` |
| `Salt.MR.S15Sel''_L_gk.toT` | Salt/MR/FlatDoorEpsRung2.lean:3910 | characters | `Salt.MR.S15Sel''_L_gk` |
| `Salt.MR.S15Sel''_L_T.head` | Salt/MR/FlatDoorEpsRung2.lean:3942 | characters | `Salt.MR.S15Sel''_L_T` |
| `Salt.MR.S15Sel''_L_gk_T.head` | Salt/MR/FlatDoorEpsRung2.lean:3955 | characters | `Salt.MR.S15Sel''_L_gk_T` |
| `Salt.MR.s15_sel''_L_gk_T_of_L_T` | Salt/MR/FlatDoorEpsRung2.lean:3969 | characters | `Salt.MR.S15Sel''_L_T` |
| `Salt.MR.s15_bandGate''_of_grade_L_gk_T` | Salt/MR/FlatDoorEpsRung2.lean:3992 | characters | `Salt.MR.S15Sel''_L_gk_T` |
| `Salt.MR.s12c_eps_threshold_at_socket_flat_T` | Salt/MR/FlatDoorEpsRung2.lean:4040 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s15_heps293_at_socket_flat_T` | Salt/MR/FlatDoorEpsRung2.lean:4076 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s15_hband4096_at_socket_flat_T` | Salt/MR/FlatDoorEpsRung2.lean:4129 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s15_gRows_const_at_socket_flat_doorL_gk_T` | Salt/MR/FlatDoorEpsRung2.lean:4188 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.s15_replay_reads_L_gk_T` | Salt/MR/FlatDoorEpsRung2.lean:4399 | characters | `Salt.MR.S15Sel''_L_gk_T`, `Salt.MR.SocketBaseL` |
| `Salt.MR.flat_socket_generic_epsW` | Salt/MR/FlatDoorEpsRung2.lean:4952 | characters | `Salt.MR.FlatHeadFormEpsW` |
| `Salt.MR.flat_doorL2_generic_epsW` | Salt/MR/FlatDoorEpsRung2.lean:4978 | characters | `Salt.MR.FlatSocketFormEpsW` |
| `Salt.MR.flat_road_generic_epsW` | Salt/MR/FlatDoorEpsRung2.lean:5023 | characters | `Salt.MR.FlatDoorL2FormEpsW` |
| `Salt.MR.flat_capstone_generic_epsW` | Salt/MR/FlatDoorEpsRung2.lean:5086 | characters | `Salt.MR.FlatRoadFormEpsW`, `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.flat_conditional_generic_epsW` | Salt/MR/FlatDoorEpsRung2.lean:5250 | characters | `Salt.MR.FlatCapstoneFormEpsW` |
| `Salt.MR.flat_kswin_generic_epsW` | Salt/MR/FlatDoorEpsRung2.lean:5380 | characters | `Salt.MR.FlatConditionalFormEpsW` |
| `Salt.MR.flat_v7_generic_epsW` | Salt/MR/FlatDoorEpsRung2.lean:5505 | characters | `Salt.MR.FlatKswinFormEpsW` |
| `Salt.MR.flat_chain_generic_epsW` | Salt/MR/FlatDoorEpsRung2.lean:5656 | characters | `Salt.MR.FlatHeadFormEpsW` |
| `Salt.MR.crownNV_landedW_nonvacuous` | Salt/MR/FlatDoorNonVacuity.lean:140 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.crownK6_grade_floor_at` | Salt/MR/FlatDoorParityFloor.lean:141 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.crownK6_grade_floor` | Salt/MR/FlatDoorParityFloor.lean:163 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.crownK6_Wdelta_regime_moves` | Salt/MR/FlatDoorParityFloor.lean:210 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.nextHopU_zero_level` | Salt/MR/FlatDoorUniform.lean:120 | characters | `Salt.MR.FlatDoorUniformW` |
| `Salt.MR.nextHopU_of_crown` | Salt/MR/FlatDoorUniform.lean:198 | characters | `Salt.MR.MRTDoorAllGrades` |
| `Salt.MR.flat_doorL2_generic_U` | Salt/MR/FlatDoorUniform.lean:876 | characters | `Salt.MR.FlatSocketFormU` |
| `Salt.MR.flat_road_generic_U` | Salt/MR/FlatDoorUniform.lean:921 | characters | `Salt.MR.FlatDoorL2FormU` |
| `Salt.MR.flat_capstone_generic_U` | Salt/MR/FlatDoorUniform.lean:985 | characters | `Salt.MR.FlatRoadFormU`, `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.flat_socket_generic_U` | Salt/MR/FlatDoorUniform.lean:1141 | characters | `Salt.MR.FlatHeadFormU` |
| `Salt.MR.flatHeadFormU_at_grade` | Salt/MR/FlatDoorUniform.lean:1223 | characters | `Salt.MR.FlatHeadFormU` |
| `Salt.MR.flat_conditional_generic_U` | Salt/MR/FlatDoorUniform.lean:1244 | characters | `Salt.MR.FlatCapstoneFormU` |
| `Salt.MR.flat_kswin_generic_U` | Salt/MR/FlatDoorUniform.lean:1348 | characters | `Salt.MR.FlatConditionalFormU` |
| `Salt.MR.flat_v7_generic_U` | Salt/MR/FlatDoorUniform.lean:1430 | characters | `Salt.MR.FlatKswinFormU` |
| `Salt.MR.flat_chain_U` | Salt/MR/FlatDoorUniform.lean:1595 | characters | `Salt.MR.FlatHeadFormU` |
| `Salt.MR.err_at_witness_mr` | Salt/MR/FrameWitness.lean:921 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.err_at_witness_mr_end` | Salt/MR/FrameWitness.lean:994 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.a2Frame3_witness` | Salt/MR/FrameWitness.lean:1082 | characters | `Salt.MR.TannGate`, `Salt.MR.SeamCoefW` |
| `Salt.MR.a2Frame3_witness_end` | Salt/MR/FrameWitness.lean:1161 | characters | `Salt.MR.TannGate`, `Salt.MR.SeamCoefWS` |
| `Salt.MR.hband_discharge_param` | Salt/MR/GradeConst.lean:89 | sieves, characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.crossKer_width_sigma_bound_param` | Salt/MR/GradeConst.lean:506 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.crossKer_width_pin_const` | Salt/MR/GradeConst.lean:865 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.beta_integral_pin_const` | Salt/MR/GradeConst.lean:1025 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.rhs_grade_at_scale_const` | Salt/MR/GradeConst.lean:1089 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.hRHS_discharged_const` | Salt/MR/GradeConst.lean:1308 | characters | `Salt.MR.JointIntegrableAt` |
| `Salt.MR.center_halasz_of_grade_const` | Salt/MR/GradeConst.lean:1353 | characters | `Salt.MR.JointIntegrableAt` |
| `Salt.MR.jointIntegrableAtC_of_gates` | Salt/MR/GradeWindowC.lean:217 | characters | `Salt.MR.JointIntegrableAt` |
| `Salt.MR.joint_cs_trunc_pinC` | Salt/MR/GradeWindowC.lean:450 | characters | `Salt.MR.JointIntegrableAtC` |
| `Salt.MR.rhs_grade_at_scale_windowC` | Salt/MR/GradeWindowC.lean:582 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAtC` |
| `Salt.MR.hUG34_unconditional` | Salt/MR/GradedCapstone.lean:88 | characters | `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.hUG34_unconditional_beats_door` | Salt/MR/GradedCapstone.lean:209 | characters | `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.nearRatTight_div_nat` | Salt/MR/HDoorArc.lean:85 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.nearRatTight_of_bigXiArcTight_H` | Salt/MR/HDoorArc.lean:139 | characters | `Salt.MR.BigXiArcTight` |
| `Salt.MR.sum_bigXiH_norm_windowExpSum_sq_le` | Salt/MR/HDoorArc.lean:211 | sieves, characters, exponential sums | `Salt.MR.NearRatTight` |
| `Salt.MR.sum_bigXiH_norm_windowExpSum_sq_le_sub` | Salt/MR/HDoorArc.lean:295 | sieves, characters, exponential sums | `Salt.MR.NearRatTight` |
| `Salt.MR.sum_bigXiH_norm_windowExpSum_sq_le_parseval` | Salt/MR/HDoorArc.lean:328 | sieves, characters, exponential sums | `Salt.MR.NearRatTight` |
| `Salt.MR.mrtUniformityXiL2H_of_absWindowSqBound` | Salt/MR/HDoorArc.lean:394 | sieves, characters | `Salt.MR.NearRatTight` |
| `Salt.MR.m4_doorL2_supply_H` | Salt/MR/HDoorArc.lean:491 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4SievedDoorSqH` |
| `Salt.MR.m4_doorL2_supply_500_H` | Salt/MR/HDoorArc.lean:575 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4SievedDoorSqH` |
| `Salt.MR.m4_classMeanSq_of_chiMeanSqH` | Salt/MR/HDoorClose.lean:106 | sieves, characters | `Salt.MR.M4ChiBlockMeanSqH` |
| `Salt.MR.m4_classBlockMeanSqH_of_chi` | Salt/MR/HDoorClose.lean:142 | sieves, characters | `Salt.MR.M4ChiBlockMeanSqH` |
| `Salt.MR.m4_blockMeanSqSupQH_of_classMeanSqH` | Salt/MR/HDoorClose.lean:161 | characters | `Salt.MR.M4ClassBlockMeanSqH` |
| `Salt.MR.m4_sievedDoorSqH_of_classMeanSqH` | Salt/MR/HDoorClose.lean:217 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ClassBlockMeanSqH` |
| `Salt.MR.m4_sievedDoorSqH_of_chiMeanSqH` | Salt/MR/HDoorClose.lean:239 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiBlockMeanSqH` |
| `Salt.MR.m4_doorL2_supply_500_H_of_chiMeanSqH` | Salt/MR/HDoorClose.lean:260 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiBlockMeanSqH` |
| `Salt.MR.m4_doorL2_supply_500_two_of_chiMeanSq` | Salt/MR/HDoorClose.lean:286 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiBlockMeanSqH` |
| `Salt.MR.socketBaseLH_of_socketBaseL` | Salt/MR/HDoorSupply.lean:562 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_logX_floor_h` | Salt/MR/HDoorSupply.lean:587 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_mu_floor_h` | Salt/MR/HDoorSupply.lean:736 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_X_ge_expexp_h` | Salt/MR/HDoorSupply.lean:766 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_scale_gate_at_socket_h` | Salt/MR/HDoorSupply.lean:801 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_threshold_at_socket_rated_h` | Salt/MR/HDoorSupply.lean:896 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_capFreeFloor_at_socket_rated_uniform_h` | Salt/MR/HDoorSupply.lean:1014 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_capFreeFloor_at_socket_rated_uniform_two` | Salt/MR/HDoorSupply.lean:1099 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.m4_sievedDoorSqH_of_supH` | Salt/MR/HDoorSupply.lean:1212 | sieves, characters | `Salt.MR.M4SievedDoorSqSupH` |
| `Salt.MR.m4_sievedDoorSqH_of_supH_uniform` | Salt/MR/HDoorSupply.lean:1262 | sieves, characters | `Salt.MR.M4SievedDoorSqSupH` |
| `Salt.MR.m4_cover_assembly_supQH` | Salt/MR/HDoorSupply.lean:1319 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4BlockMeanSqSupQH` |
| `Salt.MR.m4_sievedDoorSqH_of_blockQH` | Salt/MR/HDoorSupply.lean:1350 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4BlockMeanSqSupQH` |
| `Salt.MR.m4_doorL2_supply_500_H_of_blockQH` | Salt/MR/HDoorSupply.lean:1461 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4BlockMeanSqSupQH` |
| `Salt.MR.cofkL_logX_floor_h_b9` | Salt/MR/HDoorSupply.lean:1580 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_mu_floor_h_b9` | Salt/MR/HDoorSupply.lean:1714 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_X_ge_expexp_h_b9` | Salt/MR/HDoorSupply.lean:1744 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_scale_gate_at_socket_h_b9` | Salt/MR/HDoorSupply.lean:1784 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_threshold_at_socket_rated_h_b9` | Salt/MR/HDoorSupply.lean:1873 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.cofkL_capFreeFloor_at_socket_rated_uniform_h_b9` | Salt/MR/HDoorSupply.lean:1966 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.wellspaced_harmonic_double` | Salt/MR/HalaszIntegers.lean:595 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halasz_integers_log_split` | Salt/MR/HalaszIntegers.lean:806 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halasz_integers_of_vanDerCorput` | Salt/MR/HalaszIntegers.lean:908 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halaszIntegersChi_fibre` | Salt/MR/HalaszIntegersChiClose.lean:164 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halaszIntegersChi_phi` | Salt/MR/HalaszIntegersChiClose.lean:204 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.ramRChi_sq_sum_phi` | Salt/MR/HalaszIntegersChiClose.lean:270 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.TSChi_branch_meansq_phi` | Salt/MR/HalaszIntegersChiClose.lean:298 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.usetChi_TS_branch_meanvalue_phi` | Salt/MR/HalaszIntegersChiClose.lean:342 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.usetChi_TS_branch_exit_repinned` | Salt/MR/HalaszIntegersChiClose.lean:438 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.primePoly_wellspaced_l2` | Salt/MR/HalaszPrimes.lean:105 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halasz_primes_chi` | Salt/MR/HalaszPrimesChi.lean:234 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halasz_primes_chi_principal` | Salt/MR/HalaszPrimesChi.lean:278 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halasz_primes_chi_hybridHeight` | Salt/MR/HalaszPrimesChi.lean:307 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halasz_primes_chi_fibres` | Salt/MR/HalaszPrimesChi.lean:443 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.pole_row_sum` | Salt/MR/HalaszPrimesCore.lean:737 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.pole_double_row` | Salt/MR/HalaszPrimesCore.lean:3081 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.dual_core` | Salt/MR/HalaszPrimesCore.lean:3192 | sieves, characters | `Salt.MR.WellSpaced` |
| `Salt.MR.dual_assembly` | Salt/MR/HalaszPrimesCore.lean:3313 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halasz_primes_primal_raw` | Salt/MR/HalaszPrimesCore.lean:3339 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.halasz_primes_pow` | Salt/MR/HalaszPrimesCore.lean:3641 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.m4_second_road_L2_gk_flatRoot` | Salt/MR/HloExportMRFlatRoot.lean:344 | characters | `Salt.MR.M4DoorGates_gk`, `Salt.MR.M4ChiSummedFreeRow_gk` |
| `Salt.MR.dpolyChi_fibre_gallagher` | Salt/MR/HybridLargeValues.lean:268 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.hybrid_wellspaced_l2_family` | Salt/MR/HybridLargeValues.lean:347 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.hybrid_wellspaced_l2` | Salt/MR/HybridLargeValues.lean:461 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.hybrid_large_value_count_combined` | Salt/MR/HybridLargeValues.lean:550 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.hybrid_large_value_count` | Salt/MR/HybridLargeValues.lean:629 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.s16_baseScaleCap96_L_of_end` | Salt/MR/KLever.lean:311 | characters | `Salt.MR.S16BaseScaleCapEnd_L_gk` |
| `Salt.MR.s16_capGate_supply_L_gk_end` | Salt/MR/KLever.lean:441 | characters | `Salt.MR.S16BaseScaleCapEnd_L_gk`, `Salt.MR.S16CofactorSupply_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.s16_capGate_supply_L_gk_klevF` | Salt/MR/KLever.lean:465 | characters | `Salt.MR.S16CofactorSupply_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.lamTailWeightMask_apply_of` | Salt/MR/LambdaChiMask.lean:134 | characters | `Salt.MR.MaskSmooth` |
| `Salt.MR.lamTailWeightMask_eq_zero_of_not_smooth` | Salt/MR/LambdaChiMask.lean:150 | characters | `¬Salt.MR.MaskSmooth` |
| `Salt.MR.MlamGrChiMask_rate` | Salt/MR/LambdaChiMask.lean:537 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.MlamGrChiMask_rate_split` | Salt/MR/LambdaChiMask.lean:681 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.lamTailWeight_apply_of` | Salt/MR/LambdaChiRamare.lean:177 | characters | `Salt.MR.WindowSmooth` |
| `Salt.MR.MlamGrChi_rate` | Salt/MR/LambdaChiRamare.lean:660 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.MlamRamChi_rate` | Salt/MR/LambdaChiRamare.lean:831 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.MlambdaChi_rate` | Salt/MR/LambdaRateTwisted.lean:547 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.LambdaChiSummatory_of_MmuChiRate` | Salt/MR/LambdaRateTwisted.lean:722 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.chi_floor_real_uniform` | Salt/MR/LandauL1.lean:400 | characters | `Salt.MR.L1LowerEffective` |
| `Salt.MR.chi_floor_real_door` | Salt/MR/LandauL1.lean:439 | characters | `Salt.MR.L1LowerEffective` |
| `Salt.MR.LFunction_apply_zero_eq_sum_of_sawtooth` | Salt/MR/LandauOdd.lean:248 | characters | `Salt.MR.SawtoothOdd` |
| `Salt.MR.L0_floor_of_sawtooth` | Salt/MR/LandauOdd.lean:311 | characters | `Salt.MR.SawtoothOdd` |
| `Salt.MR.L1_lower_odd_primitive_of_sawtooth` | Salt/MR/LandauOdd.lean:335 | characters | `Salt.MR.SawtoothOdd` |
| `Salt.MR.L1_lower_odd_of_sawtooth` | Salt/MR/LandauOdd.lean:449 | characters | `Salt.MR.SawtoothOdd` |
| `Salt.MR.l1LowerOddEffective_of_l1LowerEffective` | Salt/MR/LandauOdd.lean:493 | characters | `Salt.MR.L1LowerEffective` |
| `Salt.MR.l1LowerOddEffective_of_sawtooth` | Salt/MR/LandauOdd.lean:499 | characters | `Salt.MR.SawtoothOdd` |
| `Salt.MR.l1LowerOddEffective_one_of_sawtooth` | Salt/MR/LandauOdd.lean:505 | characters | `Salt.MR.SawtoothOdd` |
| `Salt.MR.large_value_count_pre` | Salt/MR/LargeValueCount.lean:145 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.large_value_count` | Salt/MR/LargeValueCount.lean:631 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.wellspaced_card_le` | Salt/MR/LargeValues.lean:208 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.wellspaced_l2` | Salt/MR/LargeValues.lean:251 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.DoorArithFrame.one_lt_logH` | Salt/MR/M4ArithPage.lean:320 | characters | `Salt.MR.DoorArithFrame` |
| `Salt.MR.DoorArithFrame.armWeak` | Salt/MR/M4ArithPage.lean:323 | characters | `Salt.MR.DoorArithFrame` |
| `Salt.MR.DoorArithFrame.loglogX_ge` | Salt/MR/M4ArithPage.lean:329 | characters | `Salt.MR.DoorArithFrame` |
| `Salt.MR.DoorArithFrame.one_lt_logX` | Salt/MR/M4ArithPage.lean:334 | characters | `Salt.MR.DoorArithFrame` |
| `Salt.MR.a2DoorGrade_priced` | Salt/MR/M4ArithPage.lean:612 | characters | `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_arith_henv` | Salt/MR/M4ArithPage.lean:689 | characters | `Salt.MR.DoorArithFrame`, `Salt.MR.SocketBase` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorArith` | Salt/MR/M4ArithPage.lean:768 | characters | `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_arith_door_exit` | Salt/MR/M4ArithPage.lean:936 | characters | `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.a2DoorGrade_pool_priced` | Salt/MR/M4ArithPool.lean:110 | characters | `Salt.MR.DoorArithFrame` |
| `Salt.MR.a2DoorGrade_pool_priced_rho` | Salt/MR/M4ArithPool.lean:165 | characters | `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.m4_arith_henv_rho_pool` | Salt/MR/M4ArithPool.lean:245 | characters | `Salt.MR.DoorArithFrameRho`, `Salt.MR.SocketBase` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorArithRho_pool` | Salt/MR/M4ArithPool.lean:267 | characters | `Salt.MR.DoorFuseFrame_pool`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.gRows_zero_of_gate''` | Salt/MR/M4ArithPrime.lean:88 | characters | `Salt.MR.GRowsZeroGate''` |
| `Salt.MR.doorFuseFrame_pool'_of_gates` | Salt/MR/M4ArithPrime.lean:148 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate''` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_join` | Salt/MR/M4ArithPrime.lean:211 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate''` |
| `Salt.MR.m4_arith_door_exit_of_delta_L` | Salt/MR/M4ArithRhoLinear.lean:132 | characters | `Salt.MR.DoorFuseFrame_L`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_arith_door_exit_of_delta_L_gk` | Salt/MR/M4ArithRhoLinear.lean:255 | characters | `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorArith_zero` | Salt/MR/M4ArithZero.lean:140 | zeros, characters | `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_conditional_zero` | Salt/MR/M4ArithZero.lean:198 | zeros, characters | `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_bandfree_zero` | Salt/MR/M4ArithZero.lean:252 | zeros, characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.gRows_zero_of_gate` | Salt/MR/M4ArithZero.lean:433 | zeros, characters | `Salt.MR.GRowsZeroGate` |
| `Salt.MR.m4_socket_discharged_bandfree_zero_L` | Salt/MR/M4ArithZeroLinear.lean:541 | zeros, characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L`, `Salt.MR.DoorRowZeroBase_L`, `Salt.MR.DoorBandBase_L`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorArithRho_pool_L` | Salt/MR/M4ArithZeroLinear.lean:641 | zeros, characters | `Salt.MR.DoorFuseFrame_pool_L`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_join_L` | Salt/MR/M4ArithZeroLinear.lean:768 | zeros, characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate''_L` |
| `Salt.MR.m4_socket_discharged_fused_L` | Salt/MR/M4ArithZeroLinear.lean:814 | zeros, characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L`, `Salt.MR.DoorRowZeroBase_L`, `Salt.MR.DoorBandBase_L`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_socket_discharged_bandfree_zero_L_gk` | Salt/MR/M4ArithZeroLinear.lean:1135 | zeros, characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_fused_L_gk` | Salt/MR/M4ArithZeroLinear.lean:1412 | zeros, characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorArith_zero_L_gk_kwide` | Salt/MR/M4ArithZeroLinear.lean:1481 | zeros, characters | `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_conditional_zero_L_gk_kwide` | Salt/MR/M4ArithZeroLinear.lean:1533 | zeros, characters | `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_bandfree_zero_L_gk_kwide` | Salt/MR/M4ArithZeroLinear.lean:1589 | zeros, characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_fused_L_gk_kwide` | Salt/MR/M4ArithZeroLinear.lean:1645 | zeros, characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_chiFreeRowSq_sum_at_door` | Salt/MR/M4Assembly.lean:289 | characters | `Salt.MR.TannGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly` | Salt/MR/M4Assembly.lean:492 | characters | `Salt.MR.DoorFuseFrame` |
| `Salt.MR.m4_chiFreeRowSq_sum_at_door_pool` | Salt/MR/M4AssemblyPool.lean:117 | characters | `Salt.MR.TannGate` |
| `Salt.MR.DoorFuseFrame_pool.pool_nonneg` | Salt/MR/M4AssemblyPool.lean:205 | characters | `Salt.MR.DoorFuseFrame_pool` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool` | Salt/MR/M4AssemblyPool.lean:285 | characters | `Salt.MR.DoorFuseFrame_pool` |
| `Salt.MR.DoorFuseFrame_pool'.pool_nonneg` | Salt/MR/M4AssemblyPrime.lean:105 | characters | `Salt.MR.DoorFuseFrame_pool'` |
| `Salt.MR.DoorFuseFrame_pool'.of_pool` | Salt/MR/M4AssemblyPrime.lean:119 | characters | `Salt.MR.DoorFuseFrame_pool` |
| `Salt.MR.m4_chiFreeRowSq_sum_at_door_pool'` | Salt/MR/M4AssemblyPrime.lean:151 | characters | `Salt.MR.TannGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool'` | Salt/MR/M4AssemblyPrime.lean:218 | characters | `Salt.MR.DoorFuseFrame_pool'` |
| `Salt.MR.memSCoeff_eq_zero_of_not_memS` | Salt/MR/M4Band.lean:359 | characters | `¬Salt.MR.MemS` |
| `Salt.MR.seamCoefW_endpoint_forced` | Salt/MR/M4Band.lean:366 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.memSCoeff_endpoint_zero_of_seamCoefW` | Salt/MR/M4Band.lean:381 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_freeShiftBlock_at` | Salt/MR/M4BaseNarrow.lean:145 | sieves, characters | `Salt.MR.M4RowDatumAt` |
| `Salt.MR.m4_coprimeBlock_at` | Salt/MR/M4BaseNarrow.lean:633 | sieves, characters | `Salt.MR.M4RowDatumAt` |
| `Salt.MR.m4_classBlockMeanSq_of_rowDatum` | Salt/MR/M4BaseNarrow.lean:675 | characters | `Salt.MR.M4RowDatumAt` |
| `Salt.MR.m4_rowDatumAt_of_freeRowN` | Salt/MR/M4BaseNarrow.lean:824 | characters | `Salt.MR.M4ChiFreeRowMeanSqN` |
| `Salt.MR.m4_coprimeNN_supplied` | Salt/MR/M4BaseNarrow.lean:844 | characters | `Salt.MR.M4ChiFreeRowMeanSqN` |
| `Salt.MR.m4_rowDatum_dilated` | Salt/MR/M4BaseNarrow.lean:907 | characters | `Salt.MR.DoorRowCarriedT0` |
| `Salt.MR.m4_wave_collapsed` | Salt/MR/M4BaseNarrow.lean:1116 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.DoorRowCarriedT0` |
| `Salt.MR.m4_wave_collapsed_False` | Salt/MR/M4BaseNarrow.lean:1192 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.DoorRowCarriedT0`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_sievedDoorSq_of_blk` | Salt/MR/M4BridgeBlock.lean:386 | sieves, characters | `Salt.MR.M4SievedDoorSqBlk` |
| `Salt.MR.m4_cover_assembly_blk` | Salt/MR/M4BridgeBlock.lean:499 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4BlockMeanSqBlk` |
| `Salt.MR.m4_cover_assembly` | Salt/MR/M4BridgeCover.lean:404 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4BlockMeanSq` |
| `Salt.MR.m4_door_contradiction_of_blockMeanSq` | Salt/MR/M4BridgeCover.lean:488 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGate`, `Salt.MR.M4BlockMeanSq` |
| `Salt.MR.m4_door_False_of_blockMeanSq` | Salt/MR/M4BridgeCover.lean:506 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGate`, `Salt.MR.M4BlockMeanSq`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_door_contradiction_of_blockMeanSq_split` | Salt/MR/M4BridgeCover.lean:548 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4BlockMeanSq` |
| `Salt.MR.nearRatTight_dilate` | Salt/MR/M4BridgeDilate.lean:491 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.nearRatTight_dilate_door` | Salt/MR/M4BridgeDilate.lean:608 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.norm_absWindowSum_le_drift_tight` | Salt/MR/M4BridgePhase.lean:310 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.norm_absWindowSum_le_ratPartial` | Salt/MR/M4BridgePhase.lean:327 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.m4_sievedDoorSq_of_sup` | Salt/MR/M4BridgePhase.lean:434 | sieves, characters | `Salt.MR.M4SievedDoorSqSup` |
| `Salt.MR.m4_sievedDoorSq_of_sup_uniform` | Salt/MR/M4BridgePhase.lean:475 | sieves, characters | `Salt.MR.M4SievedDoorSqSup` |
| `Salt.MR.norm_absWindowSum_le_class_sum_of_nearRatTight` | Salt/MR/M4BridgeResidue.lean:281 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.norm_absWindowSum_le_liou_class_bound_of_nearRatTight` | Salt/MR/M4BridgeResidue.lean:425 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.m4_hcap_at_door` | Salt/MR/M4CapWire.lean:351 | characters | `Salt.MR.SocketBase`, `Salt.MR.TannGate` |
| `Salt.MR.m4_capRbd_at_door` | Salt/MR/M4CapWire.lean:423 | characters | `Salt.MR.CofactorSocket` |
| `Salt.MR.m4_socket_discharged_capwired` | Salt/MR/M4CapWire.lean:540 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.m4_hcap_at_door_L` | Salt/MR/M4CapWireLinear.lean:259 | characters | `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hcap_at_door_perBlock_L` | Salt/MR/M4CapWireLinear.lean:517 | characters | `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hcap_at_door_L_gk` | Salt/MR/M4CapWireLinear.lean:761 | characters | `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hcap_at_door_perBlock_L_gk` | Salt/MR/M4CapWireLinear.lean:998 | characters | `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.chiFreeRowSq_le_of_chiSummed` | Salt/MR/M4ChiSummed.lean:248 | characters | `Salt.MR.M4ChiSummedFreeRow` |
| `Salt.MR.m4_chiSummedShiftBlock_of_freeRow` | Salt/MR/M4ChiSummed.lean:454 | characters | `Salt.MR.M4ChiSummedFreeRow` |
| `Salt.MR.m4_chiSummedBlockN_of_shiftBlock` | Salt/MR/M4ChiSummed.lean:605 | characters | `Salt.MR.M4ChiSummedFreeShiftBlock` |
| `Salt.MR.m4_chiSummedN_supplied` | Salt/MR/M4ChiSummed.lean:1036 | characters | `Salt.MR.M4ChiSummedFreeRow` |
| `Salt.MR.m4_cover_assembly_supQ` | Salt/MR/M4ClassPrice.lean:347 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4BlockMeanSqSupQ` |
| `Salt.MR.m4_sievedDoorSq_of_classPrice` | Salt/MR/M4ClassPrice.lean:908 | sieves, characters | `Salt.MR.M4DoorGates` |
| `Salt.MR.m4_hbd_of_live` | Salt/MR/M4Close.lean:464 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGate`, `Salt.MR.M4SievedDoorSq`, `Salt.MR.NearRatTight` |
| `Salt.MR.m4_door_contradiction_of_live` | Salt/MR/M4Close.lean:537 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGate`, `Salt.MR.M4SievedDoorSq` |
| `Salt.MR.m4_door_False_of_live` | Salt/MR/M4Close.lean:555 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGate`, `Salt.MR.M4SievedDoorSq`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_hbd_of_live_split` | Salt/MR/M4Close.lean:710 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4SievedDoorSq`, `Salt.MR.NearRatTight` |
| `Salt.MR.m4_door_contradiction_of_live_split` | Salt/MR/M4Close.lean:771 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4SievedDoorSq` |
| `Salt.MR.m4_closure_fuse_end'_L` | Salt/MR/M4ClosureRepairLinear.lean:388 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L`, `Salt.MR.DoorRowEndBase_L`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_closure_fuse_zero'_L` | Salt/MR/M4ClosureRepairLinear.lean:444 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L`, `Salt.MR.DoorRowZeroBase_L`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_closure_fuse_end'_const_L` | Salt/MR/M4ClosureRepairLinear.lean:574 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L`, `Salt.MR.DoorRowEndBase_L`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_closure_fuse_zero'_const_L` | Salt/MR/M4ClosureRepairLinear.lean:635 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L`, `Salt.MR.DoorRowZeroBase_L`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_closure_fuse_end'_L_gk` | Salt/MR/M4ClosureRepairLinear.lean:998 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_closure_fuse_zero'_L_gk` | Salt/MR/M4ClosureRepairLinear.lean:1055 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_end'_gated_L_gk_kwide` | Salt/MR/M4ClosureRepairLinear.lean:1282 | characters | `Salt.MR.DoorFuseFrame_pool'_L_gk`, `Salt.MR.DoorRowEndBase_L_gk` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_gated_L_gk_kwide` | Salt/MR/M4ClosureRepairLinear.lean:1330 | characters | `Salt.MR.DoorFuseFrame_pool'_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk` |
| `Salt.MR.m4_closure_fuse_end'_L_gk_kwide` | Salt/MR/M4ClosureRepairLinear.lean:1379 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_closure_fuse_zero'_L_gk_kwide` | Salt/MR/M4ClosureRepairLinear.lean:1439 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_closure_fuse_end'_const_L_gk_kwide` | Salt/MR/M4ClosureRepairLinear.lean:1499 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_closure_fuse_zero'_const_L_gk_kwide` | Salt/MR/M4ClosureRepairLinear.lean:1563 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_wave_closed_coprime_discharged` | Salt/MR/M4Collapse.lean:158 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.DoorRowCarriedT0`, `Salt.MR.M4ChiFreeRowMeanSq` |
| `Salt.MR.m4_wave_closed_coprime_discharged_False` | Salt/MR/M4Collapse.lean:254 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.DoorRowCarriedT0`, `Salt.MR.M4ChiFreeRowMeanSq`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_coprimeMeanSqN_of_chiMeanSqN` | Salt/MR/M4CoprimeSupply.lean:178 | characters | `Salt.MR.M4CoprimeChiBlockMeanSqN` |
| `Salt.MR.m4_chiFreeShiftBlock_of_freeRow` | Salt/MR/M4CoprimeSupply.lean:291 | characters | `Salt.MR.M4ChiFreeRowMeanSq` |
| `Salt.MR.m4_coprimeChiN_of_freeShiftBlock` | Salt/MR/M4CoprimeSupply.lean:422 | characters | `Salt.MR.M4ChiFreeShiftBlockMeanSq` |
| `Salt.MR.m4_coprimeN_supplied` | Salt/MR/M4CoprimeSupply.lean:760 | characters | `Salt.MR.M4ChiFreeRowMeanSq` |
| `Salt.MR.m4_door_sieve_mass` | Salt/MR/M4Door.lean:616 | sieves, characters | `Salt.MR.SieveBlockGate` |
| `Salt.MR.m4_door_glue` | Salt/MR/M4Door.lean:708 | sieves, characters | `Salt.MR.SieveBlockGate` |
| `Salt.MR.m4_door_glue_liouville` | Salt/MR/M4Door.lean:765 | sieves, characters | `Salt.MR.SieveBlockGate` |
| `Salt.MR.m4_door_glue_liouChi` | Salt/MR/M4Door.lean:782 | sieves, characters | `Salt.MR.SieveBlockGate` |
| `Salt.MR.m4_door_meansq_carried` | Salt/MR/M4DoorClose.lean:389 | characters | `Salt.MR.DoorRowCarried` |
| `Salt.MR.m4_dyadicRow_carried` | Salt/MR/M4DoorClose.lean:523 | characters | `Salt.MR.DoorRowCarried` |
| `Salt.MR.m4_wave_structurally_closed` | Salt/MR/M4DoorClose.lean:579 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.DoorRowCarried`, `Salt.MR.M4CoprimeBlockMeanSq` |
| `Salt.MR.m4_doorL2_supply` | Salt/MR/M4DoorL2.lean:125 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4SievedDoorSq` |
| `Salt.MR.m4_doorL2_supply_500` | Salt/MR/M4DoorL2.lean:206 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4SievedDoorSq` |
| `Salt.MR.m4_gradeGateL2_const` | Salt/MR/M4DoorL2.lean:399 | characters | `Salt.MR.M4GradeGateL2` |
| `Salt.MR.m4_doorL2_feeds_head` | Salt/MR/M4DoorL2.lean:449 | sieves, characters | `Salt.MR.M4DoorL2HeadDemand`, `Salt.MR.M4DoorGates`, `Salt.MR.M4SievedDoorSq`, `Salt.MR.M4GradeGateL2` |
| `Salt.MR.m4_doorL2_feeds_head_split` | Salt/MR/M4DoorL2.lean:482 | sieves, characters | `Salt.MR.M4DoorL2HeadDemand`, `Salt.MR.M4DoorGates`, `Salt.MR.M4SievedDoorSq` |
| `Salt.MR.m4_doorL2_close_split_sq` | Salt/MR/M4DoorL2.lean:592 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4SievedDoorSq` |
| `Salt.MR.cofactorSocket_doorChiCoeff` | Salt/MR/M4DoorRow.lean:267 | characters | `Salt.MR.CofactorSocket` |
| `Salt.MR.E_priced_mr` | Salt/MR/M4ErrRewire.lean:93 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.E_priced_mr_row_scale` | Salt/MR/M4ErrRewire.lean:132 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.E_priced_mr_end` | Salt/MR/M4ErrRewire.lean:178 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.E_priced_mr_row_scale_end` | Salt/MR/M4ErrRewire.lean:215 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.mrtDeliveredGrade_le_doorGrade` | Salt/MR/M4Exit.lean:225 | characters | `Salt.MR.mrtGate` |
| `Salt.MR.absWindowBound_le_pin` | Salt/MR/M4Exit.lean:257 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.m4_exit_of_hbd` | Salt/MR/M4Exit.lean:283 | characters | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.MR.m4_exit_collision` | Salt/MR/M4Exit.lean:301 | characters, exponential sums | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.MR.m4_exit_of_hbd_split` | Salt/MR/M4Exit.lean:443 | characters | `Salt.Entropy.Chowla.MRTUniformityXi` |
| `Salt.MR.m4_freeBlockSup_of_chiSummed` | Salt/MR/M4Gauss.lean:760 | sieves, characters | `Salt.MR.M4ChiSummedBlockMeanSqN` |
| `Salt.MR.m4_cover_assembly_sup` | Salt/MR/M4Join.lean:248 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4BlockMeanSqSup` |
| `Salt.MR.m4_blockMeanSq_of_rowMeanSq` | Salt/MR/M4Join.lean:358 | characters | `Salt.MR.M4RowMeanSq` |
| `Salt.MR.m4_wave_exit` | Salt/MR/M4Join.lean:442 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4RowMeanSq` |
| `Salt.MR.m4_wave_False` | Salt/MR/M4Join.lean:463 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4RowMeanSq`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_wave_exit_sup` | Salt/MR/M4Join.lean:499 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGate`, `Salt.MR.M4BlockMeanSqSup` |
| `Salt.MR.m4_wave_exit_split` | Salt/MR/M4Join.lean:565 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4RowMeanSq` |
| `Salt.MR.m4_wave_exit_sup_split` | Salt/MR/M4Join.lean:608 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4BlockMeanSqSup` |
| `Salt.MR.m4_meansq_per_chi_gen_L` | Salt/MR/M4LadderLinear.lean:157 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_or_trivial_L_gk` | Salt/MR/M4LadderLinear.lean:773 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_per_chi_gen_pool_L` | Salt/MR/M4LadderLinear.lean:1017 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_per_chi_gen_join_L` | Salt/MR/M4LadderLinear.lean:1766 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_per_chi_gen_L_gk_kwide` | Salt/MR/M4LadderLinear.lean:2774 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_or_trivial_L_gk_kwide` | Salt/MR/M4LadderLinear.lean:2969 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_per_chi_gen_pool_L_gk_kwide` | Salt/MR/M4LadderLinear.lean:3114 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_or_trivial_pool_L_gk_kwide` | Salt/MR/M4LadderLinear.lean:3309 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_per_chi_gen_join_L_gk_kwide` | Salt/MR/M4LadderLinear.lean:3454 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_or_trivial_join_L_gk_kwide` | Salt/MR/M4LadderLinear.lean:3649 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4BclGraded_le_of_fits` | Salt/MR/M4Maximal.lean:751 | characters | `Salt.MR.m4SmallGradeFits` |
| `Salt.MR.m4_chiBlockMeanSq_of_shiftBlock` | Salt/MR/M4Maximal.lean:838 | characters | `Salt.MR.M4ChiShiftBlockMeanSq` |
| `Salt.MR.m4_chiShiftBlock_of_dyadicRow` | Salt/MR/M4Maximal.lean:1042 | characters | `Salt.MR.M4ChiDyadicRowMeanSq` |
| `Salt.MR.m4_chiBlockMeanSq_of_dyadicRow` | Salt/MR/M4Maximal.lean:1134 | characters | `Salt.MR.M4ChiDyadicRowMeanSq` |
| `Salt.MR.m4_wave_closed_of_dyadicRow` | Salt/MR/M4Maximal.lean:1181 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiDyadicRowMeanSq` |
| `Salt.MR.m4_wave_closed_of_dyadicRow_split` | Salt/MR/M4Maximal.lean:1238 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiDyadicRowMeanSq` |
| `Salt.MR.m4_cofactorSocket_at_witness` | Salt/MR/M4MeanSq.lean:414 | characters | `Salt.MR.CaseASocket2`, `Salt.MR.A2Frame3`, `Salt.MR.CapFreeFloor3`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.m4_meansq_per_chi_gen` | Salt/MR/M4MeanSq.lean:518 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_or_trivial` | Salt/MR/M4MeanSq.lean:796 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_per_chi_gen_pool` | Salt/MR/M4MeanSqPool.lean:83 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_or_trivial_pool` | Salt/MR/M4MeanSqPool.lean:285 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_per_chi_gen_join` | Salt/MR/M4MeanSqPrime.lean:74 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_meansq_or_trivial_join` | Salt/MR/M4MeanSqPrime.lean:275 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.CofactorSocket`, `Salt.MR.SeamCoefW` |
| `Salt.MR.m4_nonCoprime_classMeanSq` | Salt/MR/M4NonCoprime.lean:384 | characters | `Salt.MR.M4CoprimeBlockMeanSq` |
| `Salt.MR.m4_coprimeBlockMeanSqN_of_full` | Salt/MR/M4NonCoprime.lean:519 | characters | `Salt.MR.M4CoprimeBlockMeanSq` |
| `Salt.MR.m4_nonCoprime_classMeanSq_N` | Salt/MR/M4NonCoprime.lean:551 | characters | `Salt.MR.M4CoprimeBlockMeanSqN` |
| `Salt.MR.m4_door_insert_mass_integral` | Salt/MR/M4ParsevalStone.lean:281 | sieves, characters | `Salt.MR.SieveBlockGate` |
| `Salt.MR.parseval_insert_budget_door` | Salt/MR/M4ParsevalStone.lean:341 | sieves, characters | `Salt.MR.SieveBlockGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_L` | Salt/MR/M4RowAssemblyLinear.lean:158 | characters | `Salt.MR.DoorFuseFrame_L` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_L_gk` | Salt/MR/M4RowAssemblyLinear.lean:358 | characters | `Salt.MR.DoorFuseFrame_L_gk` |
| `Salt.MR.m4_wave_closed_coprime_discharged_L` | Salt/MR/M4RowAssemblyLinear.lean:422 | characters | `Salt.MR.M4DoorGates_L`, `Salt.MR.DoorRowCarriedT0_L`, `Salt.MR.M4ChiFreeRowMeanSq_L` |
| `Salt.MR.m4_wave_closed_coprime_discharged_False_L` | Salt/MR/M4RowAssemblyLinear.lean:513 | characters | `Salt.MR.M4DoorGates_L`, `Salt.MR.DoorRowCarriedT0_L`, `Salt.MR.M4ChiFreeRowMeanSq_L`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_L` | Salt/MR/M4RowAssemblyLinear.lean:3056 | characters | `Salt.MR.DoorFuseFrame_pool_L` |
| `Salt.MR.m4_wave_collapsed_L` | Salt/MR/M4RowAssemblyLinear.lean:4120 | characters | `Salt.MR.M4DoorGates_L`, `Salt.MR.DoorRowCarriedT0_L` |
| `Salt.MR.m4_wave_collapsed_False_L` | Salt/MR/M4RowAssemblyLinear.lean:4196 | characters | `Salt.MR.M4DoorGates_L`, `Salt.MR.DoorRowCarriedT0_L`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_end_L` | Salt/MR/M4RowAssemblyLinear.lean:5113 | characters | `Salt.MR.DoorFuseFrame_L`, `Salt.MR.DoorRowEndBase_L` |
| `Salt.MR.m4_wave_closed_coprime_discharged_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:5409 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.DoorRowCarriedT0_L_gk`, `Salt.MR.M4ChiFreeRowMeanSq_L_gk` |
| `Salt.MR.m4_wave_closed_coprime_discharged_False_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:5498 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.DoorRowCarriedT0_L_gk`, `Salt.MR.M4ChiFreeRowMeanSq_L_gk`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_door_meansq_carried_pool_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:5546 | characters | `Salt.MR.DoorRowCarriedPool_L_gk` |
| `Salt.MR.m4_dyadicRow_carried_pool_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:5674 | characters | `Salt.MR.DoorRowCarriedPool_L_gk` |
| `Salt.MR.m4_door_meansq_carried_join_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:5708 | characters | `Salt.MR.DoorRowCarriedJoin_L_gk` |
| `Salt.MR.m4_dyadicRow_carried_join_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:5836 | characters | `Salt.MR.DoorRowCarriedJoin_L_gk` |
| `Salt.MR.m4_rowDatum_dilated_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:5870 | characters | `Salt.MR.DoorRowCarriedT0_L_gk` |
| `Salt.MR.m4_hrowsSum_chi_door_end_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:5981 | characters | `Salt.MR.SeamCoefWS`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_end_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:6032 | characters | `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_end_L_gk_kwide` | Salt/MR/M4RowAssemblyLinear.lean:6088 | characters | `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowEndBase_L_gk` |
| `Salt.MR.m4_door_meansq_carried_L` | Salt/MR/M4RowLinear.lean:5558 | characters | `Salt.MR.DoorRowCarried_L` |
| `Salt.MR.m4_wave_structurally_closed_L` | Salt/MR/M4RowLinear.lean:5735 | characters | `Salt.MR.M4DoorGates_L`, `Salt.MR.DoorRowCarried_L`, `Salt.MR.M4CoprimeBlockMeanSq_L` |
| `Salt.MR.m4_door_meansq_carried_L_gk` | Salt/MR/M4RowLinear.lean:6022 | characters | `Salt.MR.DoorRowCarried_L_gk` |
| `Salt.MR.m4_wave_structurally_closed_L_gk` | Salt/MR/M4RowLinear.lean:6191 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.DoorRowCarried_L_gk`, `Salt.MR.M4CoprimeBlockMeanSq_L_gk` |
| `Salt.MR.m4_hT0band_at_door_discharged_split_graded_prod_L_gk` | Salt/MR/M4RowLinear.lean:7169 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_freeBlockSup_of_chiSummed_L` | Salt/MR/M4RowLinear.lean:9289 | sieves, characters | `Salt.MR.M4ChiSummedBlockMeanSqN_L` |
| `Salt.MR.m4_freeBlockSup_of_chiSummed_L_gk` | Salt/MR/M4RowLinear.lean:9750 | sieves, characters | `Salt.MR.M4ChiSummedBlockMeanSqN_L_gk` |
| `Salt.MR.m4_wave_closed_T0_discharged_L` | Salt/MR/M4RowLinear.lean:10369 | characters | `Salt.MR.M4DoorGates_L`, `Salt.MR.DoorRowCarriedT0_L`, `Salt.MR.M4CoprimeBlockMeanSq_L` |
| `Salt.MR.m4_wave_closed_T0_discharged_L_gk` | Salt/MR/M4RowLinear.lean:10712 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.DoorRowCarriedT0_L_gk`, `Salt.MR.M4CoprimeBlockMeanSq_L_gk` |
| `Salt.MR.m4_hpiece_at_door_split_graded_prod_L_gk_uniform` | Salt/MR/M4RowLinear.lean:10783 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_hT0band_at_door_discharged_split_graded_prod_L_gk_uniform` | Salt/MR/M4RowLinear.lean:10850 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_door_meansq_carried_L_gk_kwide` | Salt/MR/M4RowLinear.lean:10913 | characters | `Salt.MR.DoorRowCarried_L_gk` |
| `Salt.MR.m4_dyadicRow_carried_L_gk_kwide` | Salt/MR/M4RowLinear.lean:11047 | characters | `Salt.MR.DoorRowCarried_L_gk` |
| `Salt.MR.m4_wave_structurally_closed_L_gk_kwide` | Salt/MR/M4RowLinear.lean:11087 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.DoorRowCarried_L_gk`, `Salt.MR.M4CoprimeBlockMeanSq_L_gk` |
| `Salt.MR.m4_hrowsSum_chi_door_L_gk_kwide` | Salt/MR/M4RowLinear.lean:11154 | characters | `Salt.MR.TannGate` |
| `Salt.MR.m4_wave_closed_T0_discharged_L_gk_kwide` | Salt/MR/M4RowLinear.lean:11207 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.DoorRowCarriedT0_L_gk`, `Salt.MR.M4CoprimeBlockMeanSq_L_gk` |
| `Salt.MR.lemma12_meansq_on_subset_mr_windowed` | Salt/MR/M4RowMR.lean:108 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.lemma12_on_TsetG_mr_windowed` | Salt/MR/M4RowMR.lean:131 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.lemma12_meansq_on_subset_mr_windowed_end` | Salt/MR/M4RowMR.lean:324 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.lemma12_on_TsetG_mr_windowed_end` | Salt/MR/M4RowMR.lean:347 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.m4_second_road_L` | Salt/MR/M4RowSpineLinear.lean:364 | characters | `Salt.MR.M4DoorGates_L`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4ChiSummedFreeRow_L` |
| `Salt.MR.m4_second_road_L_gk` | Salt/MR/M4RowSpineLinear.lean:831 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4ChiSummedFreeRow_L_gk` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool'_L` | Salt/MR/M4RowSpineLinear.lean:1108 | characters | `Salt.MR.DoorFuseFrame_pool'_L` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_zero_L` | Salt/MR/M4RowSpineLinear.lean:1379 | characters | `Salt.MR.DoorFuseFrame_L`, `Salt.MR.DoorRowZeroBase_L` |
| `Salt.MR.m4_register_forces_endpoint_interval_L` | Salt/MR/M4RowSpineLinear.lean:1619 | characters | `Salt.MR.DoorRowCarriedT0_L` |
| `Salt.MR.m4_second_road_tower_L` | Salt/MR/M4RowSpineLinear.lean:1708 | characters | `Salt.MR.M4DoorGates_L`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4ChiSummedFreeRow_L` |
| `Salt.MR.m4_hrowsSum_chi_door_zero_L_gk_kwide` | Salt/MR/M4RowSpineLinear.lean:1800 | characters | `Salt.MR.SeamCoefWS`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_zero_L_gk_kwide` | Salt/MR/M4RowSpineLinear.lean:1850 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_zero_L_gk_kwide` | Salt/MR/M4RowSpineLinear.lean:1904 | characters | `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk` |
| `Salt.MR.m4_rowChi_capstone` | Salt/MR/M4RowsChi.lean:386 | characters | `Salt.MR.TannGate` |
| `Salt.MR.m4_rowChi_number_of_capstone` | Salt/MR/M4RowsChi.lean:587 | characters | `Salt.MR.CalFrameK` |
| `Salt.MR.m4_hrowsSum_chi` | Salt/MR/M4RowsChi.lean:953 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate` |
| `Salt.MR.m4_a2_spine_of_rowsChi` | Salt/MR/M4RowsChi.lean:1014 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSum_chi_door` | Salt/MR/M4RowsChi.lean:1154 | characters | `Salt.MR.TannGate` |
| `Salt.MR.chiBarCoeff_seamCoefWS` | Salt/MR/M4RowsChiEnd.lean:99 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.chiBarCoeff_seamCoefWS_levels` | Salt/MR/M4RowsChiEnd.lean:108 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.m4_rowChi_number_of_capstone_end` | Salt/MR/M4RowsChiEnd.lean:218 | characters | `Salt.MR.CalFrameK`, `Salt.MR.SeamCoefWS` |
| `Salt.MR.m4_hrowsSum_chi_end` | Salt/MR/M4RowsChiEnd.lean:595 | characters | `Salt.MR.CalFrameK`, `Salt.MR.SeamCoefWS`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSum_chi_door_end` | Salt/MR/M4RowsChiEnd.lean:706 | characters | `Salt.MR.SeamCoefWS`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_end` | Salt/MR/M4RowsChiEnd.lean:809 | characters | `Salt.MR.DoorRowEndBase`, `Salt.MR.SocketBase`, `Salt.MR.TannGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_end` | Salt/MR/M4RowsChiEnd.lean:885 | characters | `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowEndBase` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L` | Salt/MR/M4RowsChiPrimeLinear.lean:220 | characters | `Salt.MR.DoorFuseFrame_pool'_L`, `Salt.MR.DoorRowEndBase_L` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L` | Salt/MR/M4RowsChiPrimeLinear.lean:368 | characters | `Salt.MR.DoorFuseFrame_pool'_L`, `Salt.MR.DoorRowZeroBase_L` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L_gk` | Salt/MR/M4RowsChiPrimeLinear.lean:675 | characters | `Salt.MR.DoorFuseFrame_pool'_L_gk`, `Salt.MR.DoorRowEndBase_L_gk` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L_gk` | Salt/MR/M4RowsChiPrimeLinear.lean:724 | characters | `Salt.MR.DoorFuseFrame_pool'_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk` |
| `Salt.MR.m4_hrowsSum_chi_door_end'_L_gk_kwide` | Salt/MR/M4RowsChiPrimeLinear.lean:783 | characters | `Salt.MR.SeamCoefWS`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_end'_L_gk_kwide` | Salt/MR/M4RowsChiPrimeLinear.lean:833 | characters | `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSum_chi_door_zero'_L_gk_kwide` | Salt/MR/M4RowsChiPrimeLinear.lean:889 | characters | `Salt.MR.SeamCoefWS`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_zero'_L_gk_kwide` | Salt/MR/M4RowsChiPrimeLinear.lean:941 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L_gk_kwide` | Salt/MR/M4RowsChiPrimeLinear.lean:994 | characters | `Salt.MR.DoorFuseFrame_pool'_L_gk`, `Salt.MR.DoorRowEndBase_L_gk` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L_gk_kwide` | Salt/MR/M4RowsChiPrimeLinear.lean:1042 | characters | `Salt.MR.DoorFuseFrame_pool'_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk` |
| `Salt.MR.blockfree_row_zero` | Salt/MR/M4RowsChiZero.lean:153 | zeros, characters | `Salt.MR.BlockLive` |
| `Salt.MR.m4_hrowsSum_chi_zero` | Salt/MR/M4RowsChiZero.lean:648 | zeros, characters | `Salt.MR.CalFrameK`, `Salt.MR.SeamCoefWS`, `Salt.MR.BlockLive`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSum_chi_door_zero` | Salt/MR/M4RowsChiZero.lean:750 | zeros, characters | `Salt.MR.SeamCoefWS`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_zero` | Salt/MR/M4RowsChiZero.lean:801 | zeros, characters | `Salt.MR.DoorRowZeroBase`, `Salt.MR.SocketBase`, `Salt.MR.TannGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_zero` | Salt/MR/M4RowsChiZero.lean:868 | zeros, characters | `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase` |
| `Salt.MR.m4_sievedDoorSq_of_blk2` | Salt/MR/M4SecondRoad.lean:303 | sieves, characters | `Salt.MR.M4SievedDoorSqBlk2` |
| `Salt.MR.m4_cover_assembly_blk2` | Salt/MR/M4SecondRoad.lean:383 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4BlockMeanSqBlk2` |
| `Salt.MR.m4_blockMeanSqBlk2_of_chiSummed` | Salt/MR/M4SecondRoad.lean:485 | characters | `Salt.MR.M4ChiSummedBlockMeanSqN` |
| `Salt.MR.m4_second_road` | Salt/MR/M4SecondRoad.lean:683 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4ChiSummedFreeRow` |
| `Salt.MR.m4_second_road_rs_ceiling` | Salt/MR/M4SecondRoad.lean:966 | characters | `Salt.MR.M4GradeGateSplit` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorArith_end` | Salt/MR/M4SocketDischarge.lean:196 | characters | `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowEndBase`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_hband_at_door_slot` | Salt/MR/M4SocketDischarge.lean:296 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_socket_discharged_conditional` | Salt/MR/M4SocketDischarge.lean:344 | characters | `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowEndBase`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_bandfree` | Salt/MR/M4SocketDischarge.lean:412 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowEndBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_fused` | Salt/MR/M4SocketFused.lean:79 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.a2DoorGrade_L_priced` | Salt/MR/M4SocketLinear.lean:119 | characters | `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_bandfree_L` | Salt/MR/M4SocketLinear.lean:327 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L`, `Salt.MR.DoorRowEndBase_L`, `Salt.MR.DoorBandBase_L`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_bandfree_L_gk` | Salt/MR/M4SocketLinear.lean:637 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorArith_end_L_gk_kwide` | Salt/MR/M4SocketLinear.lean:727 | characters | `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_conditional_L_gk_kwide` | Salt/MR/M4SocketLinear.lean:778 | characters | `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.m4_socket_discharged_bandfree_L_gk_kwide` | Salt/MR/M4SocketLinear.lean:833 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowEndBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrame` |
| `Salt.MR.doorRowCarriedT0_endpoint` | Salt/MR/M4Spine.lean:563 | characters | `Salt.MR.DoorRowCarriedT0` |
| `Salt.MR.m4_register_forces_endpoint_interval` | Salt/MR/M4Spine.lean:578 | characters | `Salt.MR.DoorRowCarriedT0` |
| `Salt.MR.piece_partial_sum_rate` | Salt/MR/M4T0DatumDischarge.lean:262 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_hpiece_at_door` | Salt/MR/M4T0DatumDischarge.lean:410 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_hT0band_at_door_discharged` | Salt/MR/M4T0DatumDischarge.lean:474 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.piece_partial_sum_rate_split` | Salt/MR/M4T0DatumDischarge.lean:601 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_hpiece_at_door_split` | Salt/MR/M4T0DatumDischarge.lean:630 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_hT0band_at_door_discharged_split` | Salt/MR/M4T0DatumDischarge.lean:688 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.t0d_piece_hRHS` | Salt/MR/M4T0Discharge.lean:301 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.m4_t0band_discharged` | Salt/MR/M4T0Discharge.lean:431 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.doorRowCarried_of_t0free` | Salt/MR/M4T0Discharge.lean:733 | characters | `Salt.MR.DoorRowCarriedT0` |
| `Salt.MR.m4_wave_closed_T0_discharged` | Salt/MR/M4T0Discharge.lean:776 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.DoorRowCarriedT0`, `Salt.MR.M4CoprimeBlockMeanSq` |
| `Salt.MR.m4_blockMeanSqSupQ_of_classMeanSq` | Salt/MR/M4WaveClosed.lean:256 | characters | `Salt.MR.M4ClassBlockMeanSq` |
| `Salt.MR.m4_sievedDoorSq_of_classMeanSq` | Salt/MR/M4WaveClosed.lean:318 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ClassBlockMeanSq` |
| `Salt.MR.m4_classMeanSq_of_chiMeanSq` | Salt/MR/M4WaveClosed.lean:416 | sieves, characters | `Salt.MR.M4ChiBlockMeanSq` |
| `Salt.MR.m4_wave_closed` | Salt/MR/M4WaveClosed.lean:525 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ClassBlockMeanSq` |
| `Salt.MR.m4_wave_closed_False` | Salt/MR/M4WaveClosed.lean:552 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ClassBlockMeanSq`, `Salt.Entropy.Chowla.logChowla2Fails` |
| `Salt.MR.m4_wave_closed_of_chi` | Salt/MR/M4WaveClosed.lean:583 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiBlockMeanSq` |
| `Salt.MR.m4_wave_closed_split` | Salt/MR/M4WaveClosed.lean:635 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ClassBlockMeanSq` |
| `Salt.MR.m4_wave_closed_of_chi_split` | Salt/MR/M4WaveClosed.lean:663 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiBlockMeanSq` |
| `Salt.MR.m4_chiBlock_fixed_of_chiRow` | Salt/MR/M4WaveClosed.lean:748 | sieves, characters | `Salt.MR.M4ChiRowMeanSq` |
| `Salt.MR.m4_chiBlockMeanSq_of_row` | Salt/MR/M4WaveClosed.lean:810 | characters | `Salt.MR.M4ChiMaximalStep`, `Salt.MR.M4ChiRowMeanSq` |
| `Salt.MR.m4_wave_closed_of_row` | Salt/MR/M4WaveClosed.lean:840 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiMaximalStep`, `Salt.MR.M4ChiRowMeanSq` |
| `Salt.MR.m4_nonCoprime_classMeanSq_N_L` | Salt/MR/M4WaveLinear.lean:469 | characters | `Salt.MR.M4CoprimeBlockMeanSqN_L` |
| `Salt.MR.nearRatTight_of_bigXiArcTight` | Salt/MR/M4Window.lean:219 | characters | `Salt.MR.BigXiArcTight` |
| `Salt.MR.mrtUniformityXi_of_absWindowBound` | Salt/MR/M4Window.lean:243 | characters | `Salt.MR.NearRatTight` |
| `Salt.MR.sum_bigXi_norm_windowExpSum_sq_le` | Salt/MR/M4Window.lean:397 | sieves, characters, exponential sums | `Salt.MR.NearRatTight` |
| `Salt.MR.sum_bigXi_norm_windowExpSum_sq_le_sub` | Salt/MR/M4Window.lean:480 | sieves, characters, exponential sums | `Salt.MR.NearRatTight` |
| `Salt.MR.sum_bigXi_norm_windowExpSum_sq_le_parseval` | Salt/MR/M4Window.lean:510 | sieves, characters, exponential sums | `Salt.MR.NearRatTight` |
| `Salt.MR.mrtUniformityXiL2_of_absWindowSqBound` | Salt/MR/M4Window.lean:606 | sieves, characters | `Salt.MR.NearRatTight` |
| `Salt.MR.mrtQuality_lower_of_capFreeFloor` | Salt/MR/MRTPort.lean:350 | characters | `Salt.MR.CapFreeFloor` |
| `Salt.MR.door_contradiction_with_headroom_and_tower` | Salt/MR/MRTPort.lean:471 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4SievedDoorSq` |
| `Salt.MR.mrtThmA1_at_lamCoeff` | Salt/MR/MRTPortA1.lean:91 | characters | `Salt.MR.MRTThmA1` |
| `Salt.MR.mrtA1_lamCoeff_le_const` | Salt/MR/MRTPortA1Const.lean:77 | characters | `Salt.MR.MRTThmA1` |
| `Salt.MR.m4_doorSq_of_rowMeanSqLam` | Salt/MR/MRTPortRowLam.lean:59 | characters | `Salt.MR.M4RowMeanSqLam`, `Salt.MR.NearRatTight` |
| `Salt.MR.mrtBands_bandCount_incompatible_at_one` | Salt/MR/MRTPropA3.lean:598 | characters | `Salt.MR.MRTBands`, `Salt.MR.MRTBandCount` |
| `Salt.MR.sifted_empty_at_one` | Salt/MR/MRTPropA3.lean:611 | characters | `Salt.MR.MRTBands`, `Salt.MR.MRTBandCount` |
| `Salt.MR.mrtA6_at_centre` | Salt/MR/MRTPropA3.lean:2015 | characters | `Salt.MR.MRTLemmaA6` |
| `Salt.MR.mrtA3_T0_bound_of_A6` | Salt/MR/MRTPropA3.lean:2343 | characters | `Salt.MR.MRTLemmaA6` |
| `Salt.MR.mrtPropA3_in_bridge_shape` | Salt/MR/MRTPropA3.lean:2787 | characters | `Salt.MR.MRTPropA3`, `Salt.MR.MRTBands`, `Salt.MR.MRTBandCount`, `Salt.MR.MRTPropA3Ambient` |
| `Salt.MR.mrtA3_ambient_excludes_degeneracies` | Salt/MR/MRTPropA3.lean:3004 | characters | `Salt.MR.MRTPropA3Ambient` |
| `Salt.MR.mrtA3_band_bound_of_A6` | Salt/MR/MRTPropA3.lean:3030 | characters | `Salt.MR.MRTLemmaA6` |
| `Salt.MR.mrtA4ii_far_of_named_splitting` | Salt/MR/MRTPropA3.lean:3873 | characters | `Salt.MR.MRTShortSegmentSplitting` |
| `Salt.MR.mrtThmA1_of_mrtThmA1GJ_empty` | Salt/MR/MRTPropA3.lean:4014 | characters | `Salt.MR.MRTThmA1GJ` |
| `Salt.MR.mrtThmA1Statement_of_constantMatch` | Salt/MR/MRTPropA3.lean:4095 | characters | `Salt.MR.MRTParsevalConstantMatch` |
| `Salt.MR.mrtThmA1_of_mrtThmA1GJ_empty_34` | Salt/MR/MRTPropA3.lean:4578 | characters | `Salt.MR.MRTThmA1GJ_34` |
| `Salt.MR.mrtThmA1Statement_of_constantMatch_34` | Salt/MR/MRTPropA3.lean:4592 | characters | `Salt.MR.MRTParsevalConstantMatch_34` |
| `Salt.MR.mrtBands_log_Qseq_one_le` | Salt/MR/MRTSummandSupply.lean:57 | characters | `Salt.MR.MRTBands` |
| `Salt.MR.mrtBands_log_Qseq_one_rpow_le` | Salt/MR/MRTSummandSupply.lean:71 | characters | `Salt.MR.MRTBands` |
| `Salt.MR.mrtA3_first_summand_le_of_bands` | Salt/MR/MRTSummandSupply.lean:87 | characters | `Salt.MR.MRTBands` |
| `Salt.MR.mrtA3_first_summand_le_of_bands_ambient` | Salt/MR/MRTSummandSupply.lean:99 | characters | `Salt.MR.MRTBands` |
| `Salt.MR.mrtA3_first_summand_le_of_floor` | Salt/MR/MRTSummandSupply.lean:118 | characters | `Salt.MR.MRTBands` |
| `Salt.MR.mvHilbertUniform_of_l2` | Salt/MR/MVCore.lean:133 | characters | `Salt.MR.L2KernelUniform` |
| `Salt.MR.dirichlet_poly_l2_mvt` | Salt/MR/MVHilbert.lean:269 | characters | `Salt.MR.MVHilbertUniform` |
| `Salt.MR.norm_hilbertLogSumS_le` | Salt/MR/MVHilbertFinset.lean:257 | characters | `Salt.MR.MVHilbertUniform` |
| `Salt.MR.dpolyS_l2_mvt` | Salt/MR/MVHilbertFinset.lean:271 | characters | `Salt.MR.MVHilbertUniform` |
| `Salt.MR.halasz_integers` | Salt/MR/MidBand.lean:879 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.approx_reduced` | Salt/MR/MinorArcExit.lean:333 | characters | `¬Salt.MR.NearRatTight` |
| `Salt.MR.exists_q_expSum_le` | Salt/MR/MinorArcExit.lean:895 | characters, exponential sums | `¬Salt.MR.NearRatTight` |
| `Salt.MR.minorArcBoundTight_of_exitClose` | Salt/MR/MinorArcExit.lean:1000 | characters | `Salt.MR.ExitClose` |
| `Salt.MR.minorArcBoundTight_twelve_of_close` | Salt/MR/MinorArcExit.lean:1019 | characters | `Salt.MR.ExitClose` |
| `Salt.MR.bigXiArcTight_twelve_of_close` | Salt/MR/MinorArcExit.lean:1024 | characters | `Salt.MR.ExitClose` |
| `Salt.MR.ramTailWeight_apply_of` | Salt/MR/MobiusChiRamare.lean:200 | characters | `Salt.MR.WindowSmooth` |
| `Salt.MR.ramTailWeight_eq_zero_of_not_smooth` | Salt/MR/MobiusChiRamare.lean:204 | characters | `¬Salt.MR.WindowSmooth` |
| `Salt.MR.MmuGrChi_rate` | Salt/MR/MobiusChiRamare.lean:666 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.MmuRamChi_rate` | Salt/MR/MobiusChiRamare.lean:826 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.maskTailWeight_apply_of` | Salt/MR/MobiusChiRamareUnion.lean:200 | characters | `Salt.MR.MaskSmooth` |
| `Salt.MR.MmuGrChiMask_rate` | Salt/MR/MobiusChiRamareUnion.lean:565 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.MmuRamChiMask_rate` | Salt/MR/MobiusChiRamareUnion.lean:708 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.MmuGrChiU_rate` | Salt/MR/MobiusChiRamareUnion.lean:868 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.MmuRamChiU_rate` | Salt/MR/MobiusChiRamareUnion.lean:885 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.mmuChiRate_nonprincipal` | Salt/MR/MobiusChiRateClose.lean:1127 | characters | `Salt.MR.XiCarveWidth` |
| `Salt.MR.mmuChiRate_of_rows` | Salt/MR/MobiusChiRateClose.lean:1334 | characters | `Salt.MR.MmuChiRatePrincipal` |
| `Salt.MR.mmuChiRate_of_carve_and_principal` | Salt/MR/MobiusChiRateClose.lean:1362 | characters | `Salt.MR.XiCarveWidth`, `Salt.MR.MmuChiRatePrincipal` |
| `Salt.MR.lambdaChiSummatory_of_carve_and_principal` | Salt/MR/MobiusChiRateClose.lean:1370 | characters | `Salt.MR.XiCarveWidth`, `Salt.MR.MmuChiRatePrincipal` |
| `Salt.MR.mmuChiRatePrincipal_of_zetaShallow` | Salt/MR/MobiusChiRateClose.lean:1517 | characters | `Salt.MR.ZetaInvShallowVk` |
| `Salt.MR.mmuChiRate_of_carve_and_zetaShallow` | Salt/MR/MobiusChiRateClose.lean:1711 | characters | `Salt.MR.XiCarveWidth`, `Salt.MR.ZetaInvShallowVk` |
| `Salt.MR.lambdaChiSummatory_of_carve_and_zetaShallow` | Salt/MR/MobiusChiRateClose.lean:1717 | characters | `Salt.MR.XiCarveWidth`, `Salt.MR.ZetaInvShallowVk` |
| `Salt.MR.TLeg_feeds_capstone_gen_bounded` | Salt/MR/NumeralCt.lean:723 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.m4_hrowsSlot_at_door_zero'_L_gk_bounded` | Salt/MR/NumeralCt.lean:993 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_zero'_L_gk_ceiling` | Salt/MR/NumeralCt.lean:1060 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSum_chi_door_zero'_L_gk_bounded_kwide` | Salt/MR/NumeralCt.lean:1106 | characters | `Salt.MR.SeamCoefWS`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_zero'_L_gk_bounded_kwide` | Salt/MR/NumeralCt.lean:1158 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hrowsSlot_at_door_zero'_L_gk_ceiling_kwide` | Salt/MR/NumeralCt.lean:1211 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_gk_bounded` | Salt/MR/NumeralKq.lean:1140 | characters | `Salt.MR.DoorCapBasePerBlock_gk`, `Salt.MR.SocketBase`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_gk_ceiling` | Salt/MR/NumeralKq.lean:1198 | characters | `Salt.MR.DoorCapBasePerBlock_gk`, `Salt.MR.SocketBase`, `Salt.MR.TannGate` |
| `Salt.MR.joint_cs_trunc_pin2` | Salt/MR/PinFamily2.lean:386 | characters | `Salt.MR.JointIntegrableAt` |
| `Salt.MR.crossKer_width_pin_const2` | Salt/MR/PinFamily2.lean:439 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.beta_integral_pin_const2` | Salt/MR/PinFamily2.lean:478 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.rhs_grade_at_scale_trunc2` | Salt/MR/PinFamily2.lean:553 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.rhs_grade_at_scale_closed_star2` | Salt/MR/PinFamily2.lean:735 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.hRHS_socket_star2` | Salt/MR/PinFamily2.lean:804 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.wellSpaced_fibre` | Salt/MR/PortAssembly.lean:310 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.pole_double_row_fibre` | Salt/MR/PortAssembly.lean:320 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.dual_core_pair` | Salt/MR/PortAssembly.lean:439 | sieves, characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.halaszPrimesChiGated_of_price` | Salt/MR/PortAssembly.lean:802 | characters | `Salt.MR.TwistedWindowPriceGated` |
| `Salt.MR.halasz_primes_chi_pair_of_gates` | Salt/MR/PortAssembly.lean:1468 | characters | `Salt.MR.TwistedWindowPriceGated`, `Salt.MR.FibreWellSpaced` |
| `Salt.MR.halaszPrimesChi_holds_gated` | Salt/MR/PortClose.lean:187 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.usetChi_window_meansq_of_socket` | Salt/MR/PortClose.lean:286 | characters | `Salt.MR.HalaszPrimesChi` |
| `Salt.MR.euler_osc_bridge` | Salt/MR/PrimeSigmaShift.lean:445 | characters | `Salt.MR.PrimeTailShiftBounded` |
| `Salt.MR.euler_osc_bridge_le` | Salt/MR/PrimeSigmaShift.lean:497 | zeros, characters | `Salt.MR.PrimeTailShiftBounded` |
| `Salt.MR.log_euler_osc_zeta` | Salt/MR/PrimeSigmaShift.lean:511 | zeros, characters | `Salt.MR.PrimeTailShiftBounded` |
| `Salt.MR.hRHS_discharged` | Salt/MR/RHSGrade.lean:827 | characters | `Salt.MR.JointIntegrableAt` |
| `Salt.MR.center_halasz_of_grade` | Salt/MR/RHSGrade.lean:894 | characters | `Salt.MR.JointIntegrableAt` |
| `Salt.MR.beta_integral_pin_constC` | Salt/MR/RHSGradeC.lean:313 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.ramErr_meanSq_all_chi_ws` | Salt/MR/RamErrWS.lean:175 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.ramErr_meanSq_all_chi_ws_priced` | Salt/MR/RamErrWS.lean:298 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.m4_capE_at_door` | Salt/MR/RamErrWS.lean:466 | characters | `Salt.MR.DoorCapErrWS` |
| `Salt.MR.m4_socket_discharged_capwired_ws` | Salt/MR/RamErrWS.lean:581 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorCapBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.windowSmooth_dvd_bandPow` | Salt/MR/RamareMassTail.lean:201 | characters | `Salt.MR.WindowSmooth` |
| `Salt.MR.m4_hcap_at_door_perBlock_L_gk_bounded_khoist` | Salt/MR/RegisterCompose.lean:52 | characters | `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist` | Salt/MR/RegisterCompose.lean:113 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist` | Salt/MR/RegisterCompose.lean:209 | characters | `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.cofkL_bulk_grade_floor` | Salt/MR/RegisterInhabit.lean:161 | characters | `Salt.MR.CofactorBulkL` |
| `Salt.MR.cofkL_bulk_false_at_socket` | Salt/MR/RegisterInhabit.lean:260 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_logX_floor` | Salt/MR/RegisterSupply.lean:323 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_mu_floor` | Salt/MR/RegisterSupply.lean:453 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_threshold_at_socket` | Salt/MR/RegisterSupply.lean:484 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_capFreeFloor_at_socket` | Salt/MR/RegisterSupply.lean:590 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.m4_hband_at_door_slot_hoisted` | Salt/MR/S11Hoist.lean:58 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_socket_discharged_fused_hoisted` | Salt/MR/S11Hoist.lean:92 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.m4_socket_discharged_capwired_ws_hoisted` | Salt/MR/S11Hoist.lean:158 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorCapBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.m4_hband_at_door_slot_split` | Salt/MR/S11Hoist.lean:307 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_socket_discharged_fused_split` | Salt/MR/S11Hoist.lean:341 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.m4_socket_discharged_capwired_ws_hoisted_perBlock_split` | Salt/MR/S11Hoist.lean:402 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorRowZeroBase`, `Salt.MR.DoorCapBasePerBlock`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.m4_socket_discharged_fused_split_graded_L` | Salt/MR/S11HoistLinear.lean:349 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L`, `Salt.MR.DoorRowZeroBase_L`, `Salt.MR.DoorBandBase_L`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_socket_discharged_fused_split_graded_L_gk` | Salt/MR/S11HoistLinear.lean:796 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_hband_at_door_slot_split_graded_L_gk_uniform` | Salt/MR/S11HoistLinear.lean:861 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_socket_discharged_fused_hoisted_L_gk_kwide` | Salt/MR/S11HoistLinear.lean:932 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_socket_discharged_fused_split_L_gk_kwide` | Salt/MR/S11HoistLinear.lean:992 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_socket_discharged_fused_split_graded_L_gk_kwide` | Salt/MR/S11HoistLinear.lean:1053 | characters | `Salt.MR.MmuChiRate`, `Salt.MR.DoorFuseFrame_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_door_contradiction_of_live_split_tower` | Salt/MR/S11Thread.lean:49 | sieves, characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4SievedDoorSq` |
| `Salt.MR.m4_second_road_tower` | Salt/MR/S11Thread.lean:73 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4GradeGateSplit`, `Salt.MR.M4ChiSummedFreeRow` |
| `Salt.MR.m4_second_road_L2` | Salt/MR/S12Compose.lean:100 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.M4ChiSummedFreeRow` |
| `Salt.MR.logChowla2_capstone_conditional` | Salt/MR/S12Compose.lean:283 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorCapBase`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.doorFuseFrame_reEps` | Salt/MR/S12Compose.lean:696 | characters | `Salt.MR.DoorFuseFrame` |
| `Salt.MR.logChowla2_capstone_final` | Salt/MR/S12Compose.lean:710 | characters | `Salt.MR.M4DoorGates`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorFuseFrame`, `Salt.MR.DoorCapBasePerBlock`, `Salt.MR.DoorBandBase`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.logChowla2_capstone_final_const'_graded_gk_flat` | Salt/MR/S12ConstComposeFlat.lean:45 | characters | `Salt.MR.M4DoorGates_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_gk`, `Salt.MR.DoorBandBase_gk`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.logChowla2_capstone_final_const'_graded_gk_pinned_flat` | Salt/MR/S12ConstComposeFlat.lean:141 | characters | `Salt.MR.M4DoorGates_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_gk`, `Salt.MR.DoorBandBase_gk`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.capfloor_QTann_L` | Salt/MR/S13BandCapLinear.lean:183 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.capfloor_QTann_L_gk` | Salt/MR/S13BandCapLinear.lean:192 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.capfloor_kappa30Q_L` | Salt/MR/S13BandCapLinear.lean:201 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.capfloor_kappa30Q_L_gk` | Salt/MR/S13BandCapLinear.lean:211 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s13CapFloor_all_L` | Salt/MR/S13BandCapLinear.lean:223 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s13CapFloor_all_L_gk` | Salt/MR/S13BandCapLinear.lean:256 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s14_p2_in_logs_L` | Salt/MR/S13BandCapLinear.lean:295 | characters | `Salt.MR.GRowsZeroGate'''_L` |
| `Salt.MR.s13_doorCapErrWS_perBlock_L_gk` | Salt/MR/S13CapGateLinear.lean:212 | characters | `Salt.MR.S13CapGatePerBlock_L_gk` |
| `Salt.MR.s13_doorCapBase_perBlock_L_gk` | Salt/MR/S13CapGateLinear.lean:308 | characters | `Salt.MR.S13CapGatePerBlock_L_gk` |
| `Salt.MR.doorCapBundle_at_workingPoint_perBlock_L_gk` | Salt/MR/S13CapGateLinear.lean:504 | characters | `Salt.MR.S13CapGatePerBlock_L_gk` |
| `Salt.MR.s13CapGrid_all_L_gk` | Salt/MR/S13CapGateLinear.lean:552 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.s16_baseScaleCap96_L_of_baseScaleCap96` | Salt/MR/S13CapGateLinear.lean:914 | characters | `Salt.MR.S16BaseScaleCap96_gk` |
| `Salt.MR.s16_capGate_supply_L_gk` | Salt/MR/S13CapGateLinear.lean:939 | characters | `Salt.MR.S16BaseScaleCap96_L_gk`, `Salt.MR.S16CofactorSupply_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.s13_abs8640_of_socketBase_LH` | Salt/MR/S13CapGateLinearLH.lean:265 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_abs8640_at_base_LH` | Salt/MR/S13CapGateLinearLH.lean:272 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_abs8640_at_shift_LH` | Salt/MR/S13CapGateLinearLH.lean:286 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_twoj_le_H_LH` | Salt/MR/S13CapGateLinearLH.lean:292 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_mu_lo_LH` | Salt/MR/S13CapGateLinearLH.lean:306 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_mu_2000_LH` | Salt/MR/S13CapGateLinearLH.lean:316 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logH_le_mu_LH` | Salt/MR/S13CapGateLinearLH.lean:327 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Lambda_sharp_LH` | Salt/MR/S13CapGateLinearLH.lean:335 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Lambda_lo_LH` | Salt/MR/S13CapGateLinearLH.lean:352 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logX_eight_LH` | Salt/MR/S13CapGateLinearLH.lean:367 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_q_logX_LH` | Salt/MR/S13CapGateLinearLH.lean:381 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logqT_L_LH` | Salt/MR/S13CapGateLinearLH.lean:421 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logTann_lo_LH` | Salt/MR/S13CapGateLinearLH.lean:473 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Tann_one_LH` | Salt/MR/S13CapGateLinearLH.lean:497 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_kappa_Tann_LH` | Salt/MR/S13CapGateLinearLH.lean:522 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_kappa30_LH` | Salt/MR/S13CapGateLinearLH.lean:550 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_BT_LH` | Salt/MR/S13CapGateLinearLH.lean:576 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_BT10_LH` | Salt/MR/S13CapGateLinearLH.lean:610 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_logq_le_LH` | Salt/MR/S13CapGateLinearLH.lean:636 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_twoj_le_H_LH` | Salt/MR/S13CapGateLinearLH.lean:659 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_core_LH` | Salt/MR/S13CapGateLinearLH.lean:673 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_muLambda_LH` | Salt/MR/S13CapGateLinearLH.lean:709 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_T0_Tann_sharp_LH` | Salt/MR/S13CapGateLinearLH.lean:744 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_T0_Tann_LH` | Salt/MR/S13CapGateLinearLH.lean:756 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_rhs_legs_LH` | Salt/MR/S13CapGateLinearLH.lean:779 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_tannGate_LH` | Salt/MR/S13CapGateLinearLH.lean:809 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_QTann_gen_LH` | Salt/MR/S13CapGateLinearLH.lean:853 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_kappa30Q_gen_LH` | Salt/MR/S13CapGateLinearLH.lean:871 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_QTann_LH_gk` | Salt/MR/S13CapGateLinearLH.lean:882 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_kappa30Q_LH_gk` | Salt/MR/S13CapGateLinearLH.lean:891 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor1_LH` | Salt/MR/S13CapGateLinearLH.lean:907 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor2_LH` | Salt/MR/S13CapGateLinearLH.lean:930 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor3_LH` | Salt/MR/S13CapGateLinearLH.lean:964 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor4_LH` | Salt/MR/S13CapGateLinearLH.lean:1013 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapFloor_all_LH_gk` | Salt/MR/S13CapGateLinearLH.lean:1106 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_capEps_register_LH` | Salt/MR/S13CapGateLinearLH.lean:1444 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_abs8640_LH` | Salt/MR/S13CapGateLinearLH.lean:1478 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_q_arcDen_LH` | Salt/MR/S13CapGateLinearLH.lean:1490 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_EP2_gate_LH` | Salt/MR/S13CapGateLinearLH.lean:1500 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_all_LH` | Salt/MR/S13CapGateLinearLH.lean:1589 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_pin_floors_LH` | Salt/MR/S13CapGateLinearLH.lean:1621 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_pins_supply_LH` | Salt/MR/S13CapGateLinearLH.lean:1654 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Q2_reg_LH_gk` | Salt/MR/S13CapGateLinearLH.lean:1676 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_all_LH_gk` | Salt/MR/S13CapGateLinearLH.lean:1683 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s16_capGate_supply_LH_gk` | Salt/MR/S13CapGateLinearLH.lean:1756 | characters | `Salt.MR.S16BaseScaleCap96_LH_gk`, `Salt.MR.S16CofactorSupply_LH_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hcap_at_door_perBlock_LH_gk_bounded` | Salt/MR/S13CapGateLinearLH.lean:1843 | characters | `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_LH_gk_ceiling` | Salt/MR/S13CapGateLinearLH.lean:1901 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.capfloor_logq_le_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2286 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_twoj_le_H_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2310 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Q2_reg_LH_gk_b9` | Salt/MR/S13CapGateLinearLH.lean:2325 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_twoj_le_H_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2333 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_mu_lo_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2349 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_core_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2361 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_abs8640_of_socketBase_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2511 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_abs8640_at_base_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2519 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_mu_2000_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2535 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Lambda_sharp_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2549 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Lambda_lo_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2569 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logX_eight_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2585 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_q_logX_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2597 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logqT_L_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2639 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logTann_lo_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2693 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Tann_one_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2718 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_kappa_Tann_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2744 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_muLambda_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2774 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_T0_Tann_sharp_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2811 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_rhs_legs_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2825 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_tannGate_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2857 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_QTann_gen_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2903 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_kappa30Q_gen_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2923 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_QTann_LH_gk_b9` | Salt/MR/S13CapGateLinearLH.lean:2936 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_kappa30Q_LH_gk_b9` | Salt/MR/S13CapGateLinearLH.lean:2948 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor1_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2963 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor2_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:2987 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor3_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3023 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_capEps_register_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3067 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_q_arcDen_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3102 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_EP2_gate_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3114 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_pin_floors_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3202 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_abs8640_at_shift_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3244 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_kappa30_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3254 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_BT_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3284 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_BT10_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3322 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_abs8640_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3338 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_all_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3351 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_pins_supply_LH_b9` | Salt/MR/S13CapGateLinearLH.lean:3384 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_all_LH_gk_b9` | Salt/MR/S13CapGateLinearLH.lean:3401 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_gate8_of_MSelect` | Salt/MR/S13FramesA.lean:983 | characters | `Salt.MR.MSelect` |
| `Salt.MR.s13_g2_jfloor_of_MSelect` | Salt/MR/S13FramesA.lean:992 | characters | `Salt.MR.MSelect` |
| `Salt.MR.s13_doorGates_of_MSelect` | Salt/MR/S13FramesA.lean:1059 | characters | `Salt.MR.MSelect` |
| `Salt.MR.s13_doorCapErrWS` | Salt/MR/S13FramesB.lean:408 | characters | `Salt.MR.S13CapGate` |
| `Salt.MR.s13_doorCapBase` | Salt/MR/S13FramesB.lean:442 | characters | `Salt.MR.S13CapGate` |
| `Salt.MR.doorCapBundle_at_workingPoint` | Salt/MR/S13FramesB.lean:636 | characters | `Salt.MR.S13CapGate` |
| `Salt.MR.doorCapBundle_family` | Salt/MR/S13FramesB.lean:666 | characters | `Salt.MR.SocketBase`, `Salt.MR.TannGate` |
| `Salt.MR.s13_gate8_of_MSelect_L` | Salt/MR/S13FramesLinear.lean:394 | characters | `Salt.MR.MSelect_L` |
| `Salt.MR.s13_gate8_of_MSelect_L_gk` | Salt/MR/S13FramesLinear.lean:401 | characters | `Salt.MR.MSelect_L_gk` |
| `Salt.MR.s13_g2_jfloor_of_MSelect_L` | Salt/MR/S13FramesLinear.lean:410 | characters | `Salt.MR.MSelect_L` |
| `Salt.MR.s13_g2_jfloor_of_MSelect_L_gk` | Salt/MR/S13FramesLinear.lean:424 | characters | `Salt.MR.MSelect_L_gk` |
| `Salt.MR.s13_gate8_of_MSelect'_L` | Salt/MR/S13FramesLinear.lean:591 | characters | `Salt.MR.MSelect'_L` |
| `Salt.MR.s13_gate8_of_MSelect'_L_gk` | Salt/MR/S13FramesLinear.lean:598 | characters | `Salt.MR.MSelect'_L_gk` |
| `Salt.MR.s13_g2_jfloor_of_MSelect'_L` | Salt/MR/S13FramesLinear.lean:606 | characters | `Salt.MR.MSelect'_L` |
| `Salt.MR.s13_g2_jfloor_of_MSelect'_L_gk` | Salt/MR/S13FramesLinear.lean:620 | characters | `Salt.MR.MSelect'_L_gk` |
| `Salt.MR.s13_smallGradeFits_of_MSelect'_L` | Salt/MR/S13FramesLinear.lean:635 | characters | `Salt.MR.MSelect'_L` |
| `Salt.MR.s13_smallGradeFits_of_MSelect'_L_gk` | Salt/MR/S13FramesLinear.lean:643 | characters | `Salt.MR.MSelect'_L_gk` |
| `Salt.MR.MSelect'_L_of_S15Sel''_L` | Salt/MR/S13FramesLinear.lean:739 | characters | `Salt.MR.S15Sel''_L` |
| `Salt.MR.MSelect'_L_gk_of_S15Sel''_L_gk` | Salt/MR/S13FramesLinear.lean:748 | characters | `Salt.MR.S15Sel''_L_gk` |
| `Salt.MR.S15Sel''_L.head` | Salt/MR/S15SelLinear.lean:172 | characters | `Salt.MR.S15Sel''_L` |
| `Salt.MR.S15Sel''_L_gk.head` | Salt/MR/S15SelLinear.lean:183 | characters | `Salt.MR.S15Sel''_L_gk` |
| `Salt.MR.s15_sel''_L_gk_of_L` | Salt/MR/S15SelLinear.lean:524 | characters | `Salt.MR.S15Sel''_L` |
| `Salt.MR.s15_sel''_L_blk_landed` | Salt/MR/S15SelLinearWide.lean:441 | characters | `Salt.MR.S15Sel''_L` |
| `Salt.MR.s15_sel''_L_half_landed` | Salt/MR/S15SelLinearWide.lean:451 | characters | `Salt.MR.S15Sel''_L` |
| `Salt.MR.s15_gRows_const_at_socket_flat_doorL` | Salt/MR/S15SelLinearWide.lean:464 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.flat_head_uniform_ceiling` | Salt/MR/S16Compose.lean:82 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.flat_doorL2_uniform_ceiling` | Salt/MR/S16Compose.lean:254 | sieves, characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSq_L_gk` |
| `Salt.MR.flat_road_uniform_ceiling` | Salt/MR/S16Compose.lean:317 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRow_L_gk` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling` | Salt/MR/S16Compose.lean:412 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_capstone_uniform_win_ceiling` | Salt/MR/S16Compose.lean:484 | characters | `Salt.MR.S16BandLaneCBoundedL_win`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_ceiling` | Salt/MR/S16Compose.lean:723 | characters | `Salt.MR.S16BandLaneCBoundedL_win`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.m4_hcap_at_door_perBlock_L_gk_bounded` | Salt/MR/S16Compose.lean:847 | characters | `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_L_gk_ceiling` | Salt/MR/S16Compose.lean:910 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_ceiling` | Salt/MR/S16Compose.lean:1004 | characters | `Salt.MR.S16BandLaneCBoundedL_win` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_L_gk_ceiling_kwide` | Salt/MR/S16Compose.lean:1189 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_capstone_uniform_win_ceiling_kwide` | Salt/MR/S16Compose.lean:1257 | characters | `Salt.MR.S16BandLaneCBoundedL_win`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_ceiling_kwide` | Salt/MR/S16Compose.lean:1493 | characters | `Salt.MR.S16BandLaneCBoundedL_win`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.m4_hrowsSlot_at_door_zero'H_L_gk_ceiling` | Salt/MR/S16ComposeLH.lean:65 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling` | Salt/MR/S16ComposeLH.lean:120 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_capstone_uniform_win_ceiling_h` | Salt/MR/S16ComposeLH.lean:197 | characters | `Salt.MR.S16BandLaneCBoundedLH_win`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_ceiling_h` | Salt/MR/S16ComposeLH.lean:449 | characters | `Salt.MR.S16BandLaneCBoundedLH_win`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_LH_gk` |
| `Salt.MR.m4_hrowsSlot_at_door_zero'H_L_gk_ceiling_kwide` | Salt/MR/S16ComposeLH.lean:572 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide` | Salt/MR/S16ComposeLH.lean:627 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_capstone_uniform_win_ceiling_kwide_h` | Salt/MR/S16ComposeLH.lean:697 | characters | `Salt.MR.S16BandLaneCBoundedLH_win`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_ceiling_kwide_h` | Salt/MR/S16ComposeLH.lean:937 | characters | `Salt.MR.S16BandLaneCBoundedLH_win`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_LH_gk` |
| `Salt.MR.m4_doorL2_supply_H_L_gk_khoist` | Salt/MR/S16ComposeLH.lean:1072 | sieves, characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSqH_L_gk` |
| `Salt.MR.m4_second_road_L2_H_gk_flatRoot_L_khoist` | Salt/MR/S16ComposeLH.lean:1138 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.m4_second_road_L2_H_gk_flatRoot_L_exit_uniform_khoist` | Salt/MR/S16ComposeLH.lean:1221 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.flat_capstone_uniform_win_ceiling_kwide_khoist_h` | Salt/MR/S16ComposeLH.lean:1278 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_ceiling_kwide_khoist_h` | Salt/MR/S16ComposeLH.lean:1520 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_LH_gk` |
| `Salt.MR.flat_head_uniform_xceil_h` | Salt/MR/S16ComposeLH.lean:1670 | characters | `Salt.Entropy.Chowla.XCeilRider`, `Salt.Entropy.Chowla.MRTUniformityXiL2H` |
| `Salt.MR.m4_second_road_L2_H_gk_flatRoot_L_exit_uniform_xceil_khoist` | Salt/MR/S16ComposeLH.lean:1833 | characters | `Salt.Entropy.Chowla.XCeilRider`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.flat_capstone_uniform_win_xceil_kwide_khoist_h` | Salt/MR/S16ComposeLH.lean:1892 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.Entropy.Chowla.XCeilRider`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_xceil_kwide_khoist_h` | Salt/MR/S16ComposeLH.lean:2143 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.Entropy.Chowla.XCeilRiderStrict`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_LH_gk` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_ceiling_h` | Salt/MR/S16ComposeLH.lean:2326 | characters | `Salt.MR.S16BandLaneCBoundedLH_win` |
| `Salt.MR.s13CapFloor_all_LH_gk_sharpT0` | Salt/MR/S16ComposeLH.lean:2426 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s16_capGate_supply_LH_gk_sharpT0` | Salt/MR/S16ComposeLH.lean:2471 | characters | `Salt.MR.S16BaseScaleCap96_LH_gk`, `Salt.MR.S16CofactorSupply_LH_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_khoist_h` | Salt/MR/S16ComposeLH.lean:2606 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU` |
| `Salt.MR.capfloor_floor4_sharp_LH` | Salt/MR/S16ComposeLH.lean:2794 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor4_of_regimeWin_LH` | Salt/MR/S16ComposeLH.lean:2889 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapFloor_all_LH_gk_sharpT0_kswin` | Salt/MR/S16ComposeLH.lean:2914 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s16_capGate_supply_LH_gk_sharpT0_kswin` | Salt/MR/S16ComposeLH.lean:2960 | characters | `Salt.MR.S16BaseScaleCap96_LH_gk`, `Salt.MR.S16CofactorSupply_LH_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hcap_at_door_perBlock_LH_gk_bounded_khoist` | Salt/MR/S16ComposeLH.lean:3052 | characters | `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_hcap_at_door_perBlock_LH_gk_bounded_khoist_cs` | Salt/MR/S16ComposeLH.lean:3114 | characters | `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_LH_gk_ceiling_khoist` | Salt/MR/S16ComposeLH.lean:3179 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_LH_gk_ceiling_khoist_cs` | Salt/MR/S16ComposeLH.lean:3228 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin_h` | Salt/MR/S16ComposeLH.lean:3338 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide_14` | Salt/MR/S16ComposeLH.lean:3449 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_hcap_at_door_perBlock_LH_gk_bounded_khoist_cs_b9` | Salt/MR/S16ComposeLH.lean:3527 | characters | `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_LH_gk_ceiling_khoist_cs_b9` | Salt/MR/S16ComposeLH.lean:3591 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.capfloor_floor4_sharp_LH_b9` | Salt/MR/S16ComposeLH.lean:3653 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor4_of_regimeWin_LH_b9` | Salt/MR/S16ComposeLH.lean:3749 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapFloor_all_LH_gk_sharpT0_kswin_b9` | Salt/MR/S16ComposeLH.lean:3773 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s16_capGate_supply_LH_gk_sharpT0_kswin_b9` | Salt/MR/S16ComposeLH.lean:3822 | characters | `Salt.MR.S16BaseScaleCap96_LH_gk`, `Salt.MR.S16CofactorSupply_LH_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.flat_doorL2_uniform_ceiling_khoist` | Salt/MR/S16ComposeV4.lean:128 | sieves, characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSq_L_gk` |
| `Salt.MR.flat_road_uniform_ceiling_khoist` | Salt/MR/S16ComposeV4.lean:192 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRow_L_gk` |
| `Salt.MR.flat_capstone_uniform_win_ceiling_kwide_khoist` | Salt/MR/S16ComposeV4.lean:291 | characters | `Salt.MR.S16BandLaneCBoundedL_winU`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_ceiling_kwide_khoist` | Salt/MR/S16ComposeV4.lean:532 | characters | `Salt.MR.S16BandLaneCBoundedL_winU`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.s13CapFloor_all_L_gk_sharpT0` | Salt/MR/S16ComposeV4.lean:670 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s16_capGate_supply_L_gk_sharpT0` | Salt/MR/S16ComposeV4.lean:714 | characters | `Salt.MR.S16BaseScaleCap96_L_gk`, `Salt.MR.S16CofactorSupply_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_ceiling_khoist` | Salt/MR/S16ComposeV4.lean:850 | characters | `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2` | Salt/MR/S16FlatFinal.lean:136 | characters | `Salt.MR.S16BandLaneCBoundedL` |
| `Salt.MR.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot` | Salt/MR/S16FlatTerminal.lean:305 | characters | `Salt.MR.S16BandLaneCBounded`, `Salt.MR.M4DoorGates_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_gk`, `Salt.MR.DoorBandBase_gk`, `Salt.MR.DoorArithFrameRho` |
| `Salt.MR.logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot` | Salt/MR/S16FlatTerminal.lean:536 | characters | `Salt.MR.S16BandLaneCBounded`, `Salt.MR.S15Sel''_gk`, `Salt.MR.S15CrossingBound_gk` |
| `Salt.MR.logChowla2_witnessed_scale_flat` | Salt/MR/S16FlatTerminal.lean:682 | characters | `Salt.MR.S16BandLaneCBounded` |
| `Salt.MR.mrtUniformityXiL2H_mono` | Salt/MR/S16FlatTerminalExitH.lean:69 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2H` |
| `Salt.MR.m4_second_road_L2_H_gk_flatRoot_L_exit` | Salt/MR/S16FlatTerminalExitH.lean:87 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.doorFuseFrame_pool'_of_gates_const_pos_L_gk` | Salt/MR/S16FlatTerminalLinear.lean:82 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_L_gk` | Salt/MR/S16FlatTerminalLinear.lean:110 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_doorL2_close_split_sq_gk_flatRoot_L` | Salt/MR/S16FlatTerminalLinear.lean:180 | sieves, characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSq_L_gk` |
| `Salt.MR.m4_second_road_L2_gk_flatRoot_L` | Salt/MR/S16FlatTerminalLinear.lean:240 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRow_L_gk` |
| `Salt.MR.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L` | Salt/MR/S16FlatTerminalLinear.lean:357 | characters | `Salt.MR.S16BandLaneCBoundedL`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.frames_logX_ge_L` | Salt/MR/S16FlatTerminalLinear.lean:584 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.doorBaseFrame_at_socket_L` | Salt/MR/S16FlatTerminalLinear.lean:599 | characters | `Salt.MR.SocketBaseL`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.s15_block_at_socket_gen` | Salt/MR/S16FlatTerminalLinear.lean:714 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s15_block_at_socket_L_gk` | Salt/MR/S16FlatTerminalLinear.lean:758 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s13_band_baseFloor_L` | Salt/MR/S16FlatTerminalLinear.lean:769 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.s15_bandGate''_of_grade_L_gk` | Salt/MR/S16FlatTerminalLinear.lean:800 | characters | `Salt.MR.S15Sel''_L_gk` |
| `Salt.MR.doorBandBase_family'_L_gk` | Salt/MR/S16FlatTerminalLinear.lean:815 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.S13BandGate'_L_gk`, `Salt.MR.SocketBaseL` |
| `Salt.MR.s13_doorGates_of_MSelect'_L_gk` | Salt/MR/S16FlatTerminalLinear.lean:910 | characters | `Salt.MR.MSelect'_L_gk` |
| `Salt.MR.s15_gRows_const_at_socket_flat_doorL_gk` | Salt/MR/S16FlatTerminalLinear.lean:964 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L` | Salt/MR/S16FlatTerminalLinear.lean:1034 | characters | `Salt.MR.S16BandLaneCBoundedL`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L` | Salt/MR/S16FlatTerminalLinear.lean:1672 | characters | `Salt.MR.S16BandLaneCBoundedL` |
| `Salt.MR.m4_fuse_hcap_of_capWS_L_gk` | Salt/MR/S16FlatTerminalLinear.lean:1935 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_L_gk_kwide` | Salt/MR/S16FlatTerminalLinear.lean:1990 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_L_kwide` | Salt/MR/S16FlatTerminalLinear.lean:2059 | characters | `Salt.MR.S16BandLaneCBoundedL`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_L_kwide` | Salt/MR/S16FlatTerminalLinear.lean:2288 | characters | `Salt.MR.S16BandLaneCBoundedL`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.m4_sievedDoorSq_L_gk_of_H` | Salt/MR/S16FlatTerminalLinearH.lean:417 | sieves, characters | `Salt.MR.M4SievedDoorSqH_L_gk` |
| `Salt.MR.m4_chiSummedShiftBlock_of_freeRowH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:445 | characters | `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.m4_chiSummedBlockN_of_shiftBlockH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:510 | characters | `Salt.MR.M4ChiSummedFreeShiftBlockH_L_gk` |
| `Salt.MR.m4_chiSummedN_suppliedH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:949 | characters | `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.m4_freeBlockSup_of_chiSummedH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:982 | sieves, characters | `Salt.MR.M4ChiSummedBlockMeanSqNH_L_gk` |
| `Salt.MR.m4_blockMeanSqBlk2_of_chiSummedH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:1228 | characters | `Salt.MR.M4ChiSummedBlockMeanSqNH_L_gk` |
| `Salt.MR.m4_cover_assembly_blk2H_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:1363 | sieves, characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4BlockMeanSqBlk2H_L_gk` |
| `Salt.MR.m4_sievedDoorSq_of_blk2H_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:1384 | sieves, characters | `Salt.MR.M4SievedDoorSqBlk2H_L_gk` |
| `Salt.MR.m4_doorL2_supply_H_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:1470 | sieves, characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSqH_L_gk` |
| `Salt.MR.m4_doorL2_supply_500_H_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:1547 | sieves, characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSqH_L_gk` |
| `Salt.MR.m4_second_road_L2_H_gk_flatRoot_L` | Salt/MR/S16FlatTerminalLinearH.lean:1588 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.m4_chiSummedFreeRow_of_bigH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:1701 | characters | `Salt.MR.M4ChiSummedFreeRowBigH_L_gk` |
| `Salt.MR.logChowla2_capstone_final_const'_graded_gk_pinned_Mfl_flatRoot_LH` | Salt/MR/S16FlatTerminalLinearLH.lean:155 | characters | `Salt.MR.S16BandLaneCBoundedLH`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.doorBaseFrame_at_socket_LH` | Salt/MR/S16FlatTerminalLinearLH.lean:450 | characters | `Salt.MR.SocketBaseLH`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.s15_gRows_const_at_socket_flat_doorLH_gk` | Salt/MR/S16FlatTerminalLinearLH.lean:572 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_g2_jfloor_of_MSelect'_L_gk_shift28` | Salt/MR/S16FlatTerminalLinearLH.lean:910 | characters | `Salt.MR.MSelect'_L_gk` |
| `Salt.MR.logChowla2_conditional_sharp2_atK_gk_pinned_Mfl_flatRoot_LH` | Salt/MR/S16FlatTerminalLinearLH.lean:934 | characters | `Salt.MR.S16BandLaneCBoundedLH`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_LH_gk` |
| `Salt.MR.logChowla2_witnessed_scale_flat_LH` | Salt/MR/S16FlatTerminalLinearLH.lean:1067 | characters | `Salt.MR.S16BandLaneCBoundedLH` |
| `Salt.MR.s13_g2_jfloor_of_MSelect'_L_gk_shift36` | Salt/MR/S16FlatTerminalLinearLH.lean:1148 | characters | `Salt.MR.MSelect'_L_gk` |
| `Salt.MR.s15_gRows_const_at_socket_flat_doorLH_gk_b9` | Salt/MR/S16FlatTerminalLinearLH.lean:1456 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.a2DoorGrade_pool_L_priced_rhoH` | Salt/MR/S16ProducersH.lean:217 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.a2DoorGrade_pool_L_priced_rhoH_gk` | Salt/MR/S16ProducersH.lean:260 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.price_at_constPool_socketH_L` | Salt/MR/S16ProducersH.lean:274 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.m4_arith_henv_rho_poolH_L_gk` | Salt/MR/S16ProducersH.lean:292 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.m4_arith_henv_constPoolH_L_gk` | Salt/MR/S16ProducersH.lean:310 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_xscale_LH` | Salt/MR/S16ProducersH.lean:332 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_logA_ge_sqrt_LH` | Salt/MR/S16ProducersH.lean:345 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_loglogA_sharp_LH` | Salt/MR/S16ProducersH.lean:408 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_loglogA_LH` | Salt/MR/S16ProducersH.lean:425 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s14_loglogX_ge_of_socket_LH` | Salt/MR/S16ProducersH.lean:447 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s12c_llX_ge_LH` | Salt/MR/S16ProducersH.lean:462 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_block_at_socket_gen_LH` | Salt/MR/S16ProducersH.lean:480 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_band_X400_LH` | Salt/MR/S16ProducersH.lean:531 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_band_baseFloor_LH` | Salt/MR/S16ProducersH.lean:552 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s12c_eps_threshold_at_socket_flatH` | Salt/MR/S16ProducersH.lean:573 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_heps293_at_socket_flatH` | Salt/MR/S16ProducersH.lean:598 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_hband4096_at_socket_flatH` | Salt/MR/S16ProducersH.lean:640 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_block_at_socketH_L_gk` | Salt/MR/S16ProducersH.lean:686 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_doorArithFrameRho_L_at_socketH''` | Salt/MR/S16ProducersH.lean:833 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_doorArithFrameRho_L_familyH''` | Salt/MR/S16ProducersH.lean:896 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_band_arm_at_top_LH` | Salt/MR/S16ProducersH.lean:938 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_band_err_free_LH` | Salt/MR/S16ProducersH.lean:984 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.doorBandBase_family'H_L_gk` | Salt/MR/S16ProducersH.lean:1031 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.m4_hband_at_door_slotH_L_gk` | Salt/MR/S16ProducersH.lean:1100 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_hrowsSlot_at_door_zero'H_L_gk` | Salt/MR/S16ProducersH.lean:1190 | characters | `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_chiSummedFreeRow_of_doorAssembly_pool'_gatedH_L_gk` | Salt/MR/S16ProducersH.lean:1275 | characters | `Salt.MR.DoorFuseFrame_pool'_L_gk` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_H_L_gk` | Salt/MR/S16ProducersH.lean:1322 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_chiSummedN_supplied_of_rowH_L_gk` | Salt/MR/S16ProducersH.lean:1396 | characters | `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.a2DoorGrade_pool_L_priced_rhoH_14` | Salt/MR/S16ProducersH.lean:1526 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.a2DoorGrade_pool_L_priced_rhoH_gk_14` | Salt/MR/S16ProducersH.lean:1569 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_arith_henv_rho_poolH_L_gk_14` | Salt/MR/S16ProducersH.lean:1582 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.m4_arith_henv_constPoolH_L_gk_14` | Salt/MR/S16ProducersH.lean:1600 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_logA_ge_sqrt_LH_b9` | Salt/MR/S16ProducersH.lean:1665 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_loglogA_sharp_LH_b9` | Salt/MR/S16ProducersH.lean:1729 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_block_at_socket_gen_LH_b9` | Salt/MR/S16ProducersH.lean:1749 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_block_at_socketH_L_gk_b9` | Salt/MR/S16ProducersH.lean:1800 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.doorBandBase_family'H_L_gk_b9` | Salt/MR/S16ProducersH.lean:1814 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_socketBase_loglogA_LH_b9` | Salt/MR/S16ProducersH.lean:1891 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s14_loglogX_ge_of_socket_LH_b9` | Salt/MR/S16ProducersH.lean:1915 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s12c_llX_ge_LH_b9` | Salt/MR/S16ProducersH.lean:1931 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s12c_eps_threshold_at_socket_flatH_b9` | Salt/MR/S16ProducersH.lean:1950 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_heps293_at_socket_flatH_b9` | Salt/MR/S16ProducersH.lean:1977 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_hband4096_at_socket_flatH_b9` | Salt/MR/S16ProducersH.lean:2021 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.flat_head_uniform` | Salt/MR/S16Uniform.lean:235 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.flat_doorL2_uniform` | Salt/MR/S16Uniform.lean:408 | sieves, characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSq_L_gk` |
| `Salt.MR.flat_road_uniform` | Salt/MR/S16Uniform.lean:470 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRow_L_gk` |
| `Salt.MR.flat_capstone_uniform` | Salt/MR/S16Uniform.lean:567 | characters | `Salt.MR.S16BandLaneCBoundedL`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform` | Salt/MR/S16Uniform.lean:802 | characters | `Salt.MR.S16BandLaneCBoundedL`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform` | Salt/MR/S16Uniform.lean:933 | characters | `Salt.MR.S16BandLaneCBoundedL` |
| `Salt.MR.logChowla2_ineffective` | Salt/MR/S16Uniform.lean:1061 | characters | `Salt.MR.S16BandLaneCBoundedL` |
| `Salt.MR.s16_bandLaneWinL_of_bandL` | Salt/MR/S16Uniform.lean:1183 | characters | `Salt.MR.S16BandLaneCBoundedL` |
| `Salt.MR.flat_capstone_uniform_win` | Salt/MR/S16Uniform.lean:1239 | characters | `Salt.MR.S16BandLaneCBoundedL_win`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win` | Salt/MR/S16Uniform.lean:1475 | characters | `Salt.MR.S16BandLaneCBoundedL_win`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win` | Salt/MR/S16Uniform.lean:1598 | characters | `Salt.MR.S16BandLaneCBoundedL_win` |
| `Salt.MR.flat_capstone_uniform_kwide` | Salt/MR/S16Uniform.lean:1823 | characters | `Salt.MR.S16BandLaneCBoundedL`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_kwide` | Salt/MR/S16Uniform.lean:2055 | characters | `Salt.MR.S16BandLaneCBoundedL`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.flat_capstone_uniform_win_kwide` | Salt/MR/S16Uniform.lean:2169 | characters | `Salt.MR.S16BandLaneCBoundedL_win`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_kwide` | Salt/MR/S16Uniform.lean:2404 | characters | `Salt.MR.S16BandLaneCBoundedL_win`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.m4_second_road_L2_H_gk_flatRoot_L_exit_uniform` | Salt/MR/S16UniformLH.lean:69 | characters | `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.m4_hband_at_door_slot_split_graded_LH_gk` | Salt/MR/S16UniformLH.lean:177 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.m4_hband_at_door_slot_split_graded_LH_gk_uniform` | Salt/MR/S16UniformLH.lean:241 | characters | `Salt.MR.MmuChiRate` |
| `Salt.MR.sPart_eq_zero_of_not_squarefull` | Salt/MR/SPartCore.lean:170 | characters | `¬Salt.MR.Squarefull` |
| `Salt.MR.sqPartOf_sq_mul_cubePartOf_cube` | Salt/MR/SPartCore.lean:682 | characters | `Salt.MR.Squarefull` |
| `Salt.MR.sqPartOf_le` | Salt/MR/SPartCore.lean:706 | characters | `Salt.MR.Squarefull` |
| `Salt.MR.cubePartOf_le` | Salt/MR/SPartCore.lean:714 | characters | `Salt.MR.Squarefull` |
| `Salt.MR.dilated_scale_grade` | Salt/MR/SPartStation.lean:507 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.seam_ball_leg_station_M_gen` | Salt/MR/SPartStation.lean:879 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.levelGates_calibrated` | Salt/MR/SeamCalibration.lean:211 | characters | `Salt.MR.CalFrame` |
| `Salt.MR.seam_row_calibrated` | Salt/MR/SeamCalibration.lean:431 | characters | `Salt.MR.CalFrame`, `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.levelGates_calibratedK` | Salt/MR/SeamCalibrationK.lean:202 | characters | `Salt.MR.CalFrameK` |
| `Salt.MR.seam_row_calibratedK` | Salt/MR/SeamCalibrationK.lean:908 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.rhs_grade_at_scale_seam_gate` | Salt/MR/SeamGate.lean:231 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.lemma14_contour_seam_supplied_calibrated` | Salt/MR/SeamLemma14.lean:699 | characters | `Salt.MR.CalFrame`, `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.seam_row_calibrated_station` | Salt/MR/SeamLemma14.lean:824 | characters | `Salt.MR.CalFrame`, `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.seam_row_number` | Salt/MR/SeamNumber.lean:98 | characters | `Salt.MR.CalFrameK`, `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.seamCoefWS_of_seamCoefW` | Salt/MR/SeamRowWindowed.lean:158 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.spoly_ramare_split_mr_windowed` | Salt/MR/SeamRowWindowed.lean:280 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.ramErr_decomp_mr_windowed` | Salt/MR/SeamRowWindowed.lean:350 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.ramErr_moment_split_mr_windowed` | Salt/MR/SeamRowWindowed.lean:363 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.lemma12_meansq_mr_windowed` | Salt/MR/SeamRowWindowed.lean:397 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.lemma12_meansq_mr_blockSupport_windowed` | Salt/MR/SeamRowWindowed.lean:424 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.lemma12_meansq_mr_consume_windowed` | Salt/MR/SeamRowWindowed.lean:454 | characters | `Salt.MR.SeamCoefW` |
| `Salt.MR.spoly_ramare_split_mr_windowed_end` | Salt/MR/SeamRowWindowed.lean:492 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.ramErr_decomp_mr_windowed_end` | Salt/MR/SeamRowWindowed.lean:567 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.ramErr_moment_split_mr_windowed_end` | Salt/MR/SeamRowWindowed.lean:581 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.lemma12_meansq_mr_windowed_end` | Salt/MR/SeamRowWindowed.lean:607 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.lemma12_meansq_mr_blockSupport_windowed_end` | Salt/MR/SeamRowWindowed.lean:634 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.lemma12_meansq_mr_consume_windowed_end` | Salt/MR/SeamRowWindowed.lean:663 | characters | `Salt.MR.SeamCoefWS` |
| `Salt.MR.seam_terminal_row` | Salt/MR/SeamTerminal.lean:143 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates` |
| `Salt.MR.seam_terminal_dichotomy` | Salt/MR/SeamTerminal.lean:267 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates` |
| `Salt.MR.seam_ball_leg_station_M_hoisted` | Salt/MR/StationHoist.lean:163 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.hStation_of_hoisted` | Salt/MR/StationHoist.lean:380 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.mrtUniformityXiL2Set_mono` | Salt/MR/StrideDoorAllGrades.lean:425 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2Set` |
| `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_mul_at_L` | Salt/MR/StrideDoorAllGrades.lean:618 | characters | `Salt.MR.XCeilRiderAt` |
| `Salt.MR.flat_door_head_xceil_h_Z` | Salt/MR/StrideDoorAllGrades.lean:755 | characters | `Salt.MR.XiFamily` |
| `Salt.MR.flatHeadFormHG_Z_at_grade` | Salt/MR/StrideDoorAllGrades.lean:842 | characters | `Salt.MR.FlatHeadFormHG_Z` |
| `Salt.MR.flat_roadExit_generic_h_Z` | Salt/MR/StrideDoorAllGrades.lean:872 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG_Z` |
| `Salt.MR.a2DoorGrade_pool_L_priced_rhoH_L` | Salt/MR/StrideDoorAllGrades.lean:996 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.a2DoorGrade_pool_L_priced_rhoH_gk_L` | Salt/MR/StrideDoorAllGrades.lean:1042 | characters | `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.m4_arith_henv_rho_poolH_L_gk_L` | Salt/MR/StrideDoorAllGrades.lean:1058 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.m4_arith_henv_constPoolH_L_gk_L` | Salt/MR/StrideDoorAllGrades.lean:1080 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.m4_closure_fuse_zero'_const_nonneg_H_L_gk_ceiling_kwide_L` | Salt/MR/StrideDoorAllGrades.lean:1104 | characters | `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorRowZeroBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_capstone_generic_h_Z` | Salt/MR/StrideDoorAllGrades.lean:1269 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatRoadExitFormHG_Z` |
| `Salt.MR.s13_socketBase_loglogA_LH_L` | Salt/MR/StrideDoorAllGrades.lean:1449 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s14_loglogX_ge_of_socket_LH_L` | Salt/MR/StrideDoorAllGrades.lean:1474 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s12c_llX_ge_LH_L` | Salt/MR/StrideDoorAllGrades.lean:1491 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_block_at_socket_gen_LH_L` | Salt/MR/StrideDoorAllGrades.lean:1539 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s12c_eps_threshold_at_socket_flatH_L` | Salt/MR/StrideDoorAllGrades.lean:1835 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_heps293_at_socket_flatH_L` | Salt/MR/StrideDoorAllGrades.lean:1870 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_hband4096_at_socket_flatH_L` | Salt/MR/StrideDoorAllGrades.lean:1922 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_gRows_const_at_socket_flat_doorLH_gk_L` | Salt/MR/StrideDoorAllGrades.lean:1980 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.doorBandBase_family'H_L_gk_L` | Salt/MR/StrideDoorAllGrades.lean:2033 | characters | `Salt.MR.DoorArithFrameRho_L`, `Salt.MR.SocketBaseLH` |
| `Salt.MR.s15_block_at_socketH_L_gk_L` | Salt/MR/StrideDoorAllGrades.lean:2109 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_g2_jfloor_of_MSelect'_L_gk_shiftL` | Salt/MR/StrideDoorAllGrades.lean:2218 | characters | `Salt.MR.MSelect'_L_gk` |
| `Salt.MR.flat_conditional_generic_h_Z` | Salt/MR/StrideDoorAllGrades.lean:2476 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatCapstoneFormHG_Z` |
| `Salt.MR.flat_v7_generic_h_Z` | Salt/MR/StrideDoorAllGrades.lean:2691 | characters | `Salt.MR.FlatKswinFormHG_Z` |
| `Salt.MR.zTower_loglog_at_H` | Salt/MR/StrideDoorAllGrades.lean:2844 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_muLambda_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3050 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor4_sharp_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3093 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logX_eight_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3190 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_q_logX_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3206 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logqT_L_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3261 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Q2_reg_LH_gk_L` | Salt/MR/StrideDoorAllGrades.lean:3317 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_twoj_le_H_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3327 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_logTann_lo_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3345 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_Tann_one_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3374 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_BT_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3404 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_kappa_Tann_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3443 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_kappa30_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3476 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_BT10_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3507 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapGrid_all_LH_gk_L` | Salt/MR/StrideDoorAllGrades.lean:3525 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_logq_le_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3588 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_tannGate_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3615 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_QTann_gen_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3664 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_QTann_LH_gk_L` | Salt/MR/StrideDoorAllGrades.lean:3687 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_kappa30Q_gen_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3702 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_kappa30Q_LH_gk_L` | Salt/MR/StrideDoorAllGrades.lean:3718 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_T0_Tann_sharp_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3735 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor1_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3754 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor2_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3787 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_rhs_legs_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3829 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor3_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3865 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.capfloor_floor4_of_regimeWin_LH_L` | Salt/MR/StrideDoorAllGrades.lean:3917 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapFloor_all_LH_gk_sharpT0_kswin_L` | Salt/MR/StrideDoorAllGrades.lean:3941 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.m4_hcap_at_door_perBlock_LH_gk_bounded_khoist_cs_L` | Salt/MR/StrideDoorAllGrades.lean:3996 | characters | `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_LH_gk_ceiling_khoist_cs_L` | Salt/MR/StrideDoorAllGrades.lean:4061 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.s13_capEps_register_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4112 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_pin_floors_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4150 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_pins_supply_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4187 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_abs8640_of_socketBase_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4206 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_abs8640_at_base_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4218 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13_abs8640_at_shift_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4237 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_abs8640_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4248 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_EP2_gate_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4528 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_q_arcDen_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4620 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s13CapEps_all_LH_L` | Salt/MR/StrideDoorAllGrades.lean:4634 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s16_capGate_supply_LH_gk_sharpT0_kswin_L` | Salt/MR/StrideDoorAllGrades.lean:4672 | characters | `Salt.MR.S16BaseScaleCap96_LH_gk`, `Salt.MR.S16CofactorSupply_LH_gk`, `Salt.MR.SocketBaseLH`, `Salt.MR.TannGate` |
| `Salt.MR.flat_kswin_generic_h_Z` | Salt/MR/StrideDoorAllGrades.lean:4826 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatConditionalFormHG_Z` |
| `Salt.MR.regimeShrinkX_stride_x_mul_L` | Salt/MR/StrideDoorAllGrades.lean:5280 | characters | `Salt.Entropy.Chowla.StrideScale` |
| `Salt.MR.mrtUniformityXiL2AffW_of_set_L` | Salt/MR/StrideDoorAllGrades.lean:5294 | characters | `Salt.Entropy.Chowla.StrideScale`, `Salt.Entropy.Chowla.MRTUniformityXiL2Set` |
| `Salt.MR.flat_chain_generic_h_Z` | Salt/MR/StrideDoorAllGrades.lean:5548 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG_Z` |
| `Salt.MR.strideDoor_zero_level_g12b` | Salt/MR/StrideDoorAllGrades.lean:5797 | characters | `Salt.MR.StrideDoorAllGradesW` |
| `Salt.MR.strideDoor_zero_level_flat` | Salt/MR/StrideDoorAllGrades.lean:5875 | characters | `Salt.MR.StrideDoorAllGradesW` |
| `Salt.MR.log_chowla_aff_of_door_crowned` | Salt/MR/StrideEntropyReceipt.lean:36 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.MR.log_chowla_aff_of_door_crowned_unslotted` | Salt/MR/StrideEntropyReceipt.lean:74 | characters, entropy | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.MR.xceilRider_mul_of_strict` | Salt/MR/StridePairReceipt.lean:121 | characters | `Salt.Entropy.Chowla.XCeilRiderStrict` |
| `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_mul` | Salt/MR/StridePairReceipt.lean:386 | characters | `Salt.Entropy.Chowla.XCeilRider` |
| `Salt.MR.nearRatTight_of_bigXiAffArcTight` | Salt/MR/StridePairReceipt.lean:520 | characters | `Salt.MR.BigXiArcTight` |
| `Salt.MR.nearRatTight_of_bigXiAffD` | Salt/MR/StridePairReceipt.lean:605 | characters | `Salt.MR.BigXiArcTight` |
| `Salt.MR.sum_Xi_norm_windowExpSum_sq_le_parseval` | Salt/MR/StridePairReceipt.lean:628 | sieves, characters, exponential sums | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight` |
| `Salt.MR.m4_doorL2_supply_Set_gk_khoist` | Salt/MR/StridePairReceipt.lean:748 | sieves, characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSqH_L_gk` |
| `Salt.MR.m4_second_road_L2_Set_gk_flatRoot_L_khoist` | Salt/MR/StridePairReceipt.lean:815 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRowH_L_gk` |
| `Salt.MR.flat_roadExit_generic_h` | Salt/MR/StridePairReceipt.lean:1161 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormH` |
| `Salt.MR.flat_capstone_generic_h` | Salt/MR/StridePairReceipt.lean:1189 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatRoadExitFormH` |
| `Salt.MR.flat_conditional_generic_h` | Salt/MR/StridePairReceipt.lean:1406 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatCapstoneFormH` |
| `Salt.MR.flat_kswin_generic_h` | Salt/MR/StridePairReceipt.lean:1613 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatConditionalFormH` |
| `Salt.MR.flat_v7_generic_h` | Salt/MR/StridePairReceipt.lean:1721 | characters | `Salt.MR.FlatKswinFormH` |
| `Salt.MR.flat_door_head_xceil_h` | Salt/MR/StridePairReceipt.lean:1881 | characters | `Salt.MR.XiFamily` |
| `Salt.MR.flat_chain_generic_h` | Salt/MR/StridePairReceipt.lean:1973 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormH` |
| `Salt.MR.mrtUniformityXiL2Set_holds_flat_floor` | Salt/MR/StridePairReceipt.lean:1994 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.Entropy.Chowla.XCeilRiderStrict` |
| `Salt.MR.mrtUniformityXiL2AffSet_holds_flat_floor` | Salt/MR/StridePairReceipt.lean:2064 | characters | `Salt.Entropy.Chowla.XCeilRiderStrict` |
| `Salt.MR.flat_roadExit_generic_h_14` | Salt/MR/StridePairReceipt.lean:2280 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormH` |
| `Salt.MR.flat_door_head_xceil_h_14` | Salt/MR/StridePairReceipt.lean:2310 | characters | `Salt.MR.XiFamily` |
| `Salt.MR.flat_capstone_generic_h_14` | Salt/MR/StridePairReceipt.lean:2411 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatRoadExitFormH` |
| `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_mul_b9` | Salt/MR/StridePairReceipt.lean:2749 | characters | `Salt.Entropy.Chowla.XCeilRider` |
| `Salt.MR.flat_roadExit_generic_h_g` | Salt/MR/StridePairReceiptG.lean:336 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG` |
| `Salt.MR.flat_capstone_generic_h_g` | Salt/MR/StridePairReceiptG.lean:365 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatRoadExitFormHG` |
| `Salt.MR.flat_conditional_generic_h_g` | Salt/MR/StridePairReceiptG.lean:516 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatCapstoneFormHG` |
| `Salt.MR.flat_kswin_generic_h_g` | Salt/MR/StridePairReceiptG.lean:719 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatConditionalFormHG` |
| `Salt.MR.flat_v7_generic_h_g` | Salt/MR/StridePairReceiptG.lean:823 | characters | `Salt.MR.FlatKswinFormHG` |
| `Salt.MR.flat_door_head_xceil_h_g` | Salt/MR/StridePairReceiptG.lean:967 | characters | `Salt.MR.XiFamily` |
| `Salt.MR.flat_chain_generic_h_g` | Salt/MR/StridePairReceiptG.lean:1061 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG` |
| `Salt.MR.mrtUniformityXiL2Set_holds_flat_floor_g` | Salt/MR/StridePairReceiptG.lean:1076 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.Entropy.Chowla.XCeilRiderStrict` |
| `Salt.MR.mrtUniformityXiL2AffSet_holds_flat_floor_g` | Salt/MR/StridePairReceiptG.lean:1139 | characters | `Salt.Entropy.Chowla.XCeilRiderStrict` |
| `Salt.MR.flat_roadExit_generic_h_g14` | Salt/MR/StridePairReceiptG.lean:1332 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG` |
| `Salt.MR.flat_door_head_xceil_h_g14` | Salt/MR/StridePairReceiptG.lean:1362 | characters | `Salt.MR.XiFamily` |
| `Salt.MR.flat_roadExit_generic_h_g12b` | Salt/MR/StridePairReceiptG12b.lean:320 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG_g12b` |
| `Salt.MR.flat_capstone_generic_h_g12b` | Salt/MR/StridePairReceiptG12b.lean:351 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatRoadExitFormHG_g12b` |
| `Salt.MR.flat_conditional_generic_h_g12b` | Salt/MR/StridePairReceiptG12b.lean:504 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatCapstoneFormHG_g12b` |
| `Salt.MR.flat_kswin_generic_h_g12b` | Salt/MR/StridePairReceiptG12b.lean:703 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatConditionalFormHG_g12b` |
| `Salt.MR.flat_v7_generic_h_g12b` | Salt/MR/StridePairReceiptG12b.lean:807 | characters | `Salt.MR.FlatKswinFormHG_g12b` |
| `Salt.MR.flat_door_head_xceil_h_g12b` | Salt/MR/StridePairReceiptG12b.lean:936 | characters | `Salt.MR.XiFamily` |
| `Salt.MR.flat_chain_generic_h_g12b` | Salt/MR/StridePairReceiptG12b.lean:1045 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG_g12b` |
| `Salt.MR.mrtUniformityXiL2Set_holds_flat_floor_g12b` | Salt/MR/StridePairReceiptG12b.lean:1061 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.Entropy.Chowla.XCeilRiderStrict` |
| `Salt.MR.mrtUniformityXiL2AffSet_holds_flat_floor_g12b` | Salt/MR/StridePairReceiptG12b.lean:1105 | characters | `Salt.Entropy.Chowla.XCeilRiderStrict` |
| `Salt.Entropy.Chowla.log_chowla_aff_of_door_at_regime_uncapped` | Salt/MR/StrideSupplyAllStrides.lean:89 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.MR.strideSupplyAllStridesW_of_arrow` | Salt/MR/StrideSupplyAllStrides.lean:295 | characters | `Salt.MR.S4ArrowUncapped` |
| `Salt.MR.twinLogWeight_support_infinite_of_supply` | Salt/MR/StrideSupplyAllStrides.lean:323 | characters | `Salt.MR.StrideSupplyAllStridesW` |
| `Salt.MR.joint_cs_trunc_pin` | Salt/MR/SupClose.lean:275 | characters | `Salt.MR.JointIntegrableAt` |
| `Salt.MR.rhs_grade_at_scale_trunc` | Salt/MR/SupClose.lean:334 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.jointIntegrableAt_of_zero` | Salt/MR/SupStation.lean:96 | characters | `Salt.MR.JointIntegrableAt` |
| `Salt.MR.ball_sup_closed_star_uniform` | Salt/MR/SupStation.lean:468 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.ball_sup_closed_star2` | Salt/MR/SupplyGeneric.lean:523 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.JointIntegrableAt` |
| `Salt.MR.TLeg_bound_chi` | Salt/MR/TLegChi.lean:160 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.TLeg_feeds_capstone_chi` | Salt/MR/TLegChi.lean:208 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.TLeg_bound_chiSummed` | Salt/MR/TLegChi.lean:267 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.TLeg_bound_chi_totient` | Salt/MR/TLegChi.lean:328 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.Ej_bound_gen` | Salt/MR/TLegExit.lean:765 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.Ej_bound` | Salt/MR/TLegExit.lean:989 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.TLeg_bound_gen` | Salt/MR/TLegExit.lean:1069 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.TLeg_bound` | Salt/MR/TLegExit.lean:1151 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.TLeg_feeds_capstone_gen` | Salt/MR/TLegExit.lean:1228 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.TLeg_feeds_capstone` | Salt/MR/TLegExit.lean:1274 | characters | `Salt.MR.LevelGates` |
| `Salt.MR.CellGates.loglogQ_le_of_gate2` | Salt/MR/TLegKill.lean:427 | characters | `Salt.MR.CellGates` |
| `Salt.MR.CellGates.logQ_le_rpow_of_gate2` | Salt/MR/TLegKill.lean:447 | characters | `Salt.MR.CellGates` |
| `Salt.MR.thm_a2'_of_rows` | Salt/MR/ThmA2.lean:513 | characters | `Salt.MR.TannGate` |
| `Salt.MR.a2_row_cap_of_not_capFreeFloor` | Salt/MR/ThmA2.lean:686 | characters | `¬Salt.MR.CapFreeFloor` |
| `Salt.MR.A2Frame.box_at` | Salt/MR/ThmA2.lean:754 | characters | `Salt.MR.A2Frame` |
| `Salt.MR.A2Frame.ksGate_at` | Salt/MR/ThmA2.lean:762 | characters | `Salt.MR.A2Frame` |
| `Salt.MR.thm_a2'_of_rows_L` | Salt/MR/ThmA2Linear.lean:359 | characters | `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_of_rows_L_gk` | Salt/MR/ThmA2Linear.lean:577 | characters | `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_L` | Salt/MR/ThmA2Linear.lean:1414 | characters | `Salt.MR.A2Frame`, `Salt.MR.collisionGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree3_end_L` | Salt/MR/ThmA2Linear.lean:1680 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_of_rows'_L` | Salt/MR/ThmA2Linear.lean:2686 | characters | `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree3_end'_L` | Salt/MR/ThmA2Linear.lean:2948 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree3'_L_gk` | Salt/MR/ThmA2Linear.lean:3352 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:3480 | characters | `Salt.MR.A2Frame`, `Salt.MR.CapFreeFloor`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_cap_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:3608 | characters | `Salt.MR.A2Frame`, `¬Salt.MR.CapFreeFloor`, `Salt.MR.collisionGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:3748 | characters | `Salt.MR.A2Frame`, `Salt.MR.collisionGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree3_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:3868 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree3_end_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:3987 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree3_end'_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:4106 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree3'_L_gk_kwide` | Salt/MR/ThmA2Linear.lean:4225 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_of_rows_pool` | Salt/MR/ThmA2Pool.lean:92 | characters | `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_of_rows_chiSummed_pool` | Salt/MR/ThmA2Pool.lean:231 | characters | `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_of_rows_pool'` | Salt/MR/ThmA2Prime.lean:116 | characters | `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_of_rows_chiSummed_pool'` | Salt/MR/ThmA2Prime.lean:252 | characters | `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'_of_rows'` | Salt/MR/ThmA2Prime.lean:324 | characters | `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree` | Salt/MR/ThmA2Rows.lean:305 | characters | `Salt.MR.A2Frame`, `Salt.MR.CapFreeFloor`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_cap` | Salt/MR/ThmA2Rows.lean:464 | characters | `Salt.MR.A2Frame`, `¬Salt.MR.CapFreeFloor`, `Salt.MR.collisionGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.TannGate` |
| `Salt.MR.thm_a2'` | Salt/MR/ThmA2Rows.lean:636 | characters | `Salt.MR.A2Frame`, `Salt.MR.collisionGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.TannGate` |
| `Salt.MR.a2_station_supply_pointwise` | Salt/MR/ThmA2Rows.lean:778 | characters | `Salt.MR.ShortIntervalDatum` |
| `Salt.MR.a2Frame_satisfiable_partial` | Salt/MR/ThmA2Rows.lean:818 | characters | `Salt.MR.TannGate`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.a2Rows_of_capfree3` | Salt/MR/ThmA2Rows.lean:892 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.a2Rows_of_capfree3_end` | Salt/MR/ThmA2Rows.lean:1025 | characters | `Salt.MR.A2Frame3`, `Salt.MR.CofactorSocket`, `Salt.MR.TannGate` |
| `Salt.MR.a2Frame3_satisfiable_partial` | Salt/MR/ThmA2Rows.lean:1155 | characters | `Salt.MR.TannGate`, `Salt.MR.TLBlockGates34` |
| `Salt.MR.seam_Msup_family` | Salt/MR/ThmA2Spine.lean:290 | characters | `Salt.MR.TannGate` |
| `Salt.MR.thm_a2_spine` | Salt/MR/ThmA2Spine.lean:394 | characters | `Salt.MR.TannGate` |
| `Salt.MR.strideScale_regimeEnlargeX` | Salt/MR/TierSBand.lean:377 | characters | `Salt.Entropy.Chowla.StrideScale` |
| `Salt.MR.chowlaRegimeFlat_exists_param_head_xceil_mul_b9_tight` | Salt/MR/TierSBand.lean:615 | characters | `Salt.Entropy.Chowla.XCeilRider` |
| `Salt.MR.flat_door_head_xceil_h_g12b_band` | Salt/MR/TierSBand.lean:746 | characters | `Salt.MR.XiFamily` |
| `Salt.MR.flat_roadExit_generic_h_g12b_band` | Salt/MR/TierSBand.lean:844 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG_g12b_band` |
| `Salt.MR.flat_capstone_generic_h_g12b_band` | Salt/MR/TierSBand.lean:874 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatRoadExitFormHG_g12b_band` |
| `Salt.MR.flat_conditional_generic_h_g12b_band` | Salt/MR/TierSBand.lean:1022 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatCapstoneFormHG_g12b_band` |
| `Salt.MR.flat_kswin_generic_h_g12b_band` | Salt/MR/TierSBand.lean:1272 | characters | `Salt.MR.S16BandLaneCBoundedLH_winU`, `Salt.MR.FlatConditionalFormHG_g12b_band` |
| `Salt.MR.flat_v7_generic_h_g12b_band` | Salt/MR/TierSBand.lean:1378 | characters | `Salt.MR.FlatKswinFormHG_g12b_band` |
| `Salt.MR.flat_chain_generic_h_g12b_band` | Salt/MR/TierSBand.lean:1507 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.MR.FlatHeadFormHG_g12b_band` |
| `Salt.MR.mrtUniformityXiL2Set_holds_flat_floor_g12b_band` | Salt/MR/TierSBand.lean:1524 | characters | `Salt.MR.XiFamily`, `Salt.MR.NearRatTight`, `Salt.Entropy.Chowla.XCeilRiderStrict`, `Salt.Entropy.Chowla.StrideScale` |
| `Salt.MR.mrtUniformityXiL2AffSet_holds_flat_floor_g12b_band` | Salt/MR/TierSBand.lean:1578 | characters | `Salt.Entropy.Chowla.XCeilRiderStrict`, `Salt.Entropy.Chowla.StrideScale` |
| `Salt.MR.flatHeadFormHG_g12b_of_band` | Salt/MR/TierSBand.lean:1800 | characters | `Salt.MR.XiFamily`, `Salt.MR.FlatHeadFormHG_g12b_band` |
| `Salt.MR.flatRoadExitFormHG_g12b_of_band` | Salt/MR/TierSBand.lean:1817 | characters | `Salt.MR.FlatRoadExitFormHG_g12b_band` |
| `Salt.MR.flatCapstoneFormHG_g12b_of_band` | Salt/MR/TierSBand.lean:1832 | characters | `Salt.MR.FlatCapstoneFormHG_g12b_band` |
| `Salt.MR.flatConditionalFormHG_g12b_of_band` | Salt/MR/TierSBand.lean:1852 | characters | `Salt.MR.FlatConditionalFormHG_g12b_band` |
| `Salt.MR.flatKswinFormHG_g12b_of_band` | Salt/MR/TierSBand.lean:1872 | characters | `Salt.MR.FlatKswinFormHG_g12b_band` |
| `Salt.MR.v7RatedFormHG_g12b_of_band` | Salt/MR/TierSBand.lean:1892 | characters | `Salt.MR.V7RatedFormHG_g12b_band` |
| `Salt.MR.nearRatTight_of_bigXiAffU` | Salt/MR/TierSBandU.lean:168 | characters | `Salt.MR.BigXiArcTight` |
| `Salt.MR.mrtUniformityXiL2Set_of_subset` | Salt/MR/TierSBandU.lean:190 | characters | `Salt.MR.XiFamily`, `Salt.Entropy.Chowla.MRTUniformityXiL2Set` |
| `Salt.MR.mrtUniformityXiL2AffSet_holds_flat_floor_g12b_band_U` | Salt/MR/TierSBandU.lean:205 | characters | `Salt.Entropy.Chowla.XCeilRiderStrict`, `Salt.Entropy.Chowla.StrideScale` |
| `Salt.MR.mrtUniformityXiL2AffW_holds_flat_stride_g12b_band_of_bU` | Salt/MR/TierSBandU.lean:444 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2AffW` |
| `Salt.MR.gradedAffHeadAt_g12b_of_at_regime_crowned` | Salt/MR/TierSBridge.lean:61 | characters | `¬Salt.Entropy.Chowla.logChowlaFailsAff` |
| `Salt.MR.affFullRangeAt_band_of_not_fails` | Salt/MR/TierSBridge.lean:135 | characters | `¬Salt.Entropy.Chowla.logChowlaFailsAff` |
| `Salt.MR.affFullRangeAt_normalise` | Salt/MR/TierSLadder.lean:60 | characters | `Salt.TwinBar.AffFullRangeAt` |
| `Salt.MR.TS_feed_of_thin` | Salt/MR/USetBalance.lean:162 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.TL_feed_of_supply` | Salt/MR/USetBalance.lean:283 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates`, `Salt.MR.WellSpaced` |
| `Salt.MR.hU_supplied` | Salt/MR/USetBalance.lean:421 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates` |
| `Salt.MR.hU_balance` | Salt/MR/USetBalance.lean:533 | characters | `Salt.MR.TannGate` |
| `Salt.MR.hU_balance_beats_door` | Salt/MR/USetBalance.lean:556 | characters | `Salt.MR.TannGate` |
| `Salt.MR.hU_discharged` | Salt/MR/USetBalance.lean:588 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates` |
| `Salt.MR.fibreWellSpaced_reflectChi` | Salt/MR/USetChi.lean:115 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.fibreWellSpaced_of_subset` | Salt/MR/USetChi.lean:141 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.hybridblock_count` | Salt/MR/USetChi.lean:233 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.UsetChi_thin` | Salt/MR/USetChi.lean:300 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.tLsetChi_fibreWellSpaced` | Salt/MR/USetChi.lean:431 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.ramQChi_large_count` | Salt/MR/USetChi.lean:440 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.ramQChi_large_count_Tfree` | Salt/MR/USetChi.lean:486 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.tLChi_sumsq_ramQ` | Salt/MR/USetChi.lean:599 | characters | `Salt.MR.HalaszPrimesChi`, `Salt.MR.FibreWellSpaced` |
| `Salt.MR.tLChi_ramQ_sumsq_killed` | Salt/MR/USetChi.lean:649 | characters | `Salt.MR.HalaszPrimesChi`, `Salt.MR.FibreWellSpaced` |
| `Salt.MR.tLChi_main_sumsq` | Salt/MR/USetChi.lean:776 | characters | `Salt.MR.HalaszPrimesChi`, `Salt.MR.FibreWellSpaced` |
| `Salt.MR.ramRChi_sq_sum_le` | Salt/MR/USetChiTS.lean:136 | characters | `Salt.MR.HalaszIntegersChi`, `Salt.MR.FibreWellSpaced` |
| `Salt.MR.ramRChi_sq_sum_mvt` | Salt/MR/USetChiTS.lean:164 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.UsetChi_thin_alpha` | Salt/MR/USetChiTS.lean:202 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.UsetChi_thin_sqrt_kill` | Salt/MR/USetChiTS.lean:247 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.UsetChi_thin_sqrt_kill_absorbed` | Salt/MR/USetChiTS.lean:375 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.TSChi_branch_meansq` | Salt/MR/USetChiTS.lean:435 | characters | `Salt.MR.HalaszIntegersChi`, `Salt.MR.FibreWellSpaced` |
| `Salt.MR.usetChi_TS_branch_meanvalue` | Salt/MR/USetChiTS.lean:477 | characters | `Salt.MR.HalaszIntegersChi`, `Salt.MR.FibreWellSpaced` |
| `Salt.MR.fibreWellSpaced_fibrePack` | Salt/MR/USetChiTS.lean:584 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.ramQChi_graded_count` | Salt/MR/USetGChiCount.lean:79 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.usetG_thin_bundle` | Salt/MR/USetGradedBalance.lean:171 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.usetG_thin_sqrt_kill` | Salt/MR/USetGradedBalance.lean:193 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.usetG_TS_branch` | Salt/MR/USetGradedBalance.lean:218 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.usetG_TS_branch_meanvalue` | Salt/MR/USetGradedBalance.lean:255 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.TSG_feed_of_thin` | Salt/MR/USetGradedBalance.lean:293 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.TLG_feed_of_supply_local` | Salt/MR/USetGradedBalance.lean:363 | characters | `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGatesLoc`, `Salt.MR.WellSpaced` |
| `Salt.MR.hUG_supplied` | Salt/MR/USetGradedBalance.lean:458 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGatesLoc` |
| `Salt.MR.hUG_balance` | Salt/MR/USetGradedBalance.lean:564 | characters | `Salt.MR.TannGate` |
| `Salt.MR.hUG_balance_beats_door` | Salt/MR/USetGradedBalance.lean:580 | characters | `Salt.MR.TannGate` |
| `Salt.MR.hUG_discharged` | Salt/MR/USetGradedBalance.lean:604 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGatesLoc` |
| `Salt.MR.tL_supply_discharged34_local` | Salt/MR/USetGradedPrice.lean:374 | characters | `Salt.MR.WellSpaced`, `Salt.MR.collisionGate`, `Salt.MR.CaseASocket2` |
| `Salt.MR.hUG34_supplied` | Salt/MR/USetGradedPrice.lean:836 | characters | `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocket2` |
| `Salt.MR.hUG34_fully_priced` | Salt/MR/USetGradedPrice.lean:957 | characters | `Salt.MR.TannGate`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates34`, `Salt.MR.CaseASocket2` |
| `Salt.MR.not_blockSmallG_witness` | Salt/MR/USetGradedThin.lean:140 | characters | `¬Salt.MR.BlockSmallG` |
| `Salt.MR.ramI_nonempty_of_not_blockSmallG` | Salt/MR/USetGradedThin.lean:152 | characters | `¬Salt.MR.BlockSmallG` |
| `Salt.MR.ramQ_graded_count` | Salt/MR/USetGradedThin.lean:184 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.usetG_thin` | Salt/MR/USetGradedThin.lean:285 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.usetG_thin_Q` | Salt/MR/USetGradedThin.lean:341 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.usetG_thin_pin` | Salt/MR/USetGradedThin.lean:413 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.kappa30_of_TannGate` | Salt/MR/USetPins.lean:328 | characters | `Salt.MR.TannGate` |
| `Salt.MR.hU_fully_priced` | Salt/MR/USetPrice.lean:585 | characters | `Salt.MR.TannGate`, `Salt.MR.ShortIntervalDatum`, `Salt.MR.collisionGate`, `Salt.MR.TLBlockGates` |
| `Salt.MR.priced_exit_beats_door` | Salt/MR/USetPrice.lean:702 | characters | `Salt.MR.TannGate` |
| `Salt.MR.farErr_TannGate_floor` | Salt/MR/USetResiduals.lean:375 | characters | `Salt.MR.TannGate` |
| `Salt.MR.Rbd_TannGate_floor` | Salt/MR/USetResiduals.lean:407 | characters | `Salt.MR.TannGate` |
| `Salt.MR.Rbd_grade_refuted` | Salt/MR/USetResiduals.lean:425 | characters | `Salt.MR.TannGate` |
| `Salt.MR.Rbd_and_Cq_gates_collide` | Salt/MR/USetResiduals.lean:452 | characters | `Salt.MR.TannGate` |
| `Salt.MR.Uset_thin` | Salt/MR/USetThin.lean:637 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.ramQ_large_count` | Salt/MR/USetThinTL.lean:207 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.ramQ_large_count_Tfree` | Salt/MR/USetThinTL.lean:269 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.tL_sumsq_ramQ` | Salt/MR/USetThinTL.lean:354 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.tL_ramQ_sumsq_killed` | Salt/MR/USetThinTL.lean:646 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.tL_main_sumsq` | Salt/MR/USetThinTL.lean:762 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.wellSpaced_neg_image` | Salt/MR/USetThinTS.lean:105 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.ramR_sq_sum_le` | Salt/MR/USetThinTS.lean:130 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.TS_branch_meansq` | Salt/MR/USetThinTS.lean:189 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.Uset_thin_alpha` | Salt/MR/USetThinTS.lean:256 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.Uset_thin_sqrt_kill` | Salt/MR/USetThinTS.lean:322 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.uset_TS_branch` | Salt/MR/USetThinTS.lean:354 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.uset_TS_branch_meanvalue` | Salt/MR/USetThinTS.lean:388 | characters | `Salt.MR.WellSpaced` |
| `Salt.MR.capfloor_floor4_sharp` | Salt/MR/V7A.lean:103 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.ks_sharp_of_rider` | Salt/MR/V7A.lean:191 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.capfloor_floor4_of_sharp` | Salt/MR/V7A.lean:202 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.capfloor_floor4_of_pos` | Salt/MR/V7A.lean:216 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.capfloor_floor4_of_design` | Salt/MR/V7A.lean:230 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.halaszPrimesChiGated_of_price_floored` | Salt/MR/V7B.lean:769 | characters | `Salt.MR.TwistedWindowPriceGated` |
| `Salt.MR.halasz_primes_chi_pair_of_gates_bounded_cs` | Salt/MR/V7B.lean:1122 | characters | `Salt.MR.TwistedWindowPriceGated`, `Salt.MR.FibreWellSpaced` |
| `Salt.MR.halaszPrimesChi_holds_gated_bounded_cs` | Salt/MR/V7B.lean:1176 | characters | `Salt.MR.FibreWellSpaced` |
| `Salt.MR.m4_rowChi_capstone_perBlock_bounded_cs` | Salt/MR/V7B.lean:1424 | characters | `Salt.MR.TannGate` |
| `Salt.MR.m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs` | Salt/MR/V7B.lean:1561 | characters | `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs` | Salt/MR/V7B.lean:1623 | characters | `Salt.MR.DoorCapBasePerBlock_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree` | Salt/MR/V7B.lean:1722 | characters | `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.capfloor_floor4_of_regimeWin` | Salt/MR/V7Ks.lean:74 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s13CapFloor_all_L_gk_sharpT0_kswin` | Salt/MR/V7Ks.lean:97 | characters | `Salt.MR.SocketBase` |
| `Salt.MR.s16_capGate_supply_L_gk_sharpT0_kswin` | Salt/MR/V7Ks.lean:145 | characters | `Salt.MR.S16BaseScaleCap96_L_gk`, `Salt.MR.S16CofactorSupply_L_gk`, `Salt.MR.SocketBaseL`, `Salt.MR.TannGate` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_cqhoist_csfree_kswin` | Salt/MR/V7Ks.lean:294 | characters | `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.cofkL_capFreeFloor_at_socket_rated_uniform` | Salt/MR/V7Rated.lean:73 | characters | `Salt.MR.SocketBaseL` |
| `Salt.MR.cofkL_socket_floors_h` | Salt/MR/V7RatedH.lean:51 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.s16_baseScaleCap96_LH_of_end` | Salt/MR/V7RatedH.lean:914 | characters | `Salt.MR.S16BaseScaleCapEnd_LH_gk` |
| `Salt.MR.cofkL_socket_floors_h_b9` | Salt/MR/V7RatedH.lean:1280 | characters | `Salt.MR.SocketBaseLH` |
| `Salt.MR.halasz_integers_unconditional` | Salt/MR/VdCSocket.lean:539 | characters, exponential sums | `Salt.MR.WellSpaced` |
| `Salt.MR.chi_floor_vk_pointwise_sharp` | Salt/MR/VkMidSharp.lean:322 | characters | `Salt.MR.VkTwistUB` |
| `Salt.MR.capFreeFloor3_lamChi_vk_sharp` | Salt/MR/VkMidSharp.lean:372 | characters | `Salt.MR.VkTwistUB` |
| `Salt.MR.chi_Llower_341_vk` | Salt/MR/VkTwistClose.lean:323 | characters | `Salt.MR.VkTwistUB` |
| `Salt.MR.chi_floor_vk_pointwise` | Salt/MR/VkTwistClose.lean:585 | characters | `Salt.MR.VkTwistUB` |
| `Salt.MR.capFreeFloor3_lamChi_vk` | Salt/MR/VkTwistClose.lean:650 | characters | `Salt.MR.VkTwistUB` |
| `Salt.MR.capFreeFloor_lamChi_vk` | Salt/MR/VkTwistClose.lean:668 | characters | `Salt.MR.VkTwistUB` |
| `Salt.Entropy.Chowla.log_chowla_two_budget_head_forallX_sq_count` | Salt/MR/XGapThread.lean:36 | characters | `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.Entropy.Chowla.chowlaRegimeFlat_exists_param_head_xceil` | Salt/MR/XThread.lean:96 | characters | `Salt.Entropy.Chowla.XCeilRider` |
| `Salt.MR.flat_head_uniform_xceil` | Salt/MR/XThread.lean:556 | characters | `Salt.Entropy.Chowla.XCeilRider`, `Salt.Entropy.Chowla.MRTUniformityXiL2` |
| `Salt.MR.flat_socket_uniform_xceil` | Salt/MR/XThread.lean:681 | sieves, characters | `Salt.Entropy.Chowla.XCeilRider` |
| `Salt.MR.flat_doorL2_uniform_xceil_khoist` | Salt/MR/XThread.lean:733 | sieves, characters | `Salt.Entropy.Chowla.XCeilRider`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4SievedDoorSq_L_gk` |
| `Salt.MR.flat_road_uniform_xceil_khoist` | Salt/MR/XThread.lean:798 | characters | `Salt.Entropy.Chowla.XCeilRider`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.M4ChiSummedFreeRow_L_gk` |
| `Salt.MR.flat_capstone_uniform_win_xceil_kwide_khoist` | Salt/MR/XThread.lean:897 | characters | `Salt.MR.S16BandLaneCBoundedL_winU`, `Salt.Entropy.Chowla.XCeilRider`, `Salt.MR.M4DoorGates_L_gk`, `Salt.MR.m4SmallGradeFits`, `Salt.MR.DoorBaseFrame`, `Salt.MR.GRowsZeroGate'''_L_gk`, `Salt.MR.DoorBandBase_L_gk`, `Salt.MR.DoorArithFrameRho_L` |
| `Salt.MR.flat_conditional_uniform_win_xceil_kwide_khoist` | Salt/MR/XThread.lean:1207 | characters | `Salt.MR.S16BandLaneCBoundedL_winU`, `Salt.Entropy.Chowla.XCeilRiderStrict`, `Salt.MR.S15Sel''_L_gk`, `Salt.MR.S15CrossingBound_L_gk` |
| `Salt.MR.logChowla2_witnessed_scale_flat_L_v2_uniform_win_xceil_khoist` | Salt/MR/XThread.lean:1368 | characters | `Salt.MR.S16BandLaneCBoundedL_winU` |
| `Salt.MR.mmuChiRate_of_carve` | Salt/MR/ZetaInvShallow.lean:894 | zeros, characters | `Salt.MR.XiCarveWidth` |
| `Salt.MR.lambdaChiSummatory_of_carve` | Salt/MR/ZetaInvShallow.lean:899 | zeros, characters | `Salt.MR.XiCarveWidth` |
| `GehAnchor.pieceObligationU_of_anchored_multiblock` | Salt/Maynard/GehAnchor.lean:505 | sieves | `GEH_min`, `CoeffAt`, `SWAtData` |
| `geh_door_of_obligations` | Salt/Maynard/GehClose.lean:97 | sieves | `GEH_min`, `CoeffAt`, `SWAt`, `PieceObligationU`, `WindowPNT` |
| `Salt.Parity.Z_trivial_of_not_completion` | Salt/Parity/Z.lean:125 | sieves | `¬Salt.Parity.Completion` |
| `Salt.Parity.TPC_implies_Z` | Salt/Parity/Z.lean:216 | sieves | `TwinPrimeConjecture` |
| `Salt.Parity.sufficient_true_not_parityInv` | Salt/Parity/Z.lean:678 | sieves | `Salt.Parity.TwinSufficient` |
| `Salt.Parity.Z_implies_TPC` | Salt/Parity/Z.lean:693 | sieves | `Salt.Parity.Z` |
| `Salt.SW.estermannPositivity_of_interface` | Salt/SW/Estermann.lean:289 | sieves | `Salt.SW.EstermannInterface` |
| `Salt.SW.card_system_le_rpow` | Salt/SW/JutilaRatio.lean:347 | sieves, characters | `Salt.SW.WellSpacedAt` |
| `Salt.SW.estermann_fourfold` | Salt/SW/Siegel.lean:190 | sieves, characters | `Salt.SW.EstermannPositivity` |
| `Salt.SW.goldfeld_L_one_lower` | Salt/SW/Siegel.lean:286 | sieves, characters | `Salt.SW.EstermannPositivity` |
| `Salt.SW.psi1AP_main_bound_of_standoff` | Salt/SW/StandoffGate.lean:201 | sieves | `Salt.SW.NoSiegelZerosAt` |
| `Salt.SW.siegelWalfisz_of_standoff` | Salt/SW/StandoffGate.lean:576 | sieves | `Salt.SW.NoSiegelZerosAt` |
| `Salt.SW.not_fulcrum_siegelFree_SW` | Salt/SW/StandoffGate.lean:805 | sieves | `¬Salt.Fulcrum.FulcrumQualityMin` |
| `Salt.SW.sum_inv_sq_sub_le_of_wellSpacedAt` | Salt/SW/WellSpacedAt.lean:93 | sieves | `Salt.SW.WellSpacedAt` |
| `Salt.Twelve.gaps_le_twelve_of_frontierM` | Salt/Twelve/GapsFinal.lean:268 | sieves | `WindowPNT`, `EHall`, `Salt.Twelve.WinFrontierM` |
| `Salt.Twelve.gaps_le_twelve` | Salt/Twelve/GapsUncond.lean:1061 | sieves | `WindowPNT`, `EHall` |
| `Salt.Twelve.s2_inner_yF` | Salt/Twelve/InnerS2.lean:1194 | sieves | `Salt.Twelve.PhiUpperAtom` |
| `Salt.Twelve.mv_I` | Salt/Twelve/MvI.lean:275 | sieves | `Salt.Twelve.PhiUpperAtom` |
| `Salt.Twelve.mv_J` | Salt/Twelve/MvJ.lean:2142 | sieves | `Salt.Twelve.PhiUpperAtom` |
| `Salt.Twelve.qdiag_bridge` | Salt/Twelve/QdiagBridge.lean:568 | sieves | `Salt.Twelve.PhiUpperAtom` |
| `Salt.Twelve.windowPNT_of_piAsymp` | Salt/Twelve/WindowPNTDischarge.lean:49 | sieves | `Salt.Twelve.PiAsymp` |
| `Salt.Twelve.gaps_le_twelve_of_piAsymp` | Salt/Twelve/WindowPNTDischarge.lean:130 | sieves | `Salt.Twelve.PiAsymp`, `EHall` |
| `Salt.TwinBar.twin_bar_constrained` | Salt/TwinBar/Constrained.lean:188 | sieves | `Salt.TwinBar.Admissible` |
| `Salt.TwinBar.no_quad_weight_of_fourBar` | Salt/TwinBar/FourBar.lean:441 | sieves | `Salt.TwinBar.FourBar` |
| `Salt.TwinBar.Mlambda_rate` | Salt/TwinBar/LambdaRate.lean:451 | sieves | `Salt.TwinBar.MmuRate` |
| `Salt.TwinBar.LambdaSummatory_of_MmuRate` | Salt/TwinBar/LambdaRate.lean:582 | sieves | `Salt.TwinBar.MmuRate` |
| `Salt.TwinBar.Sep.no_readable_certificate_via_master` | Salt/TwinBar/Separation.lean:99 | sieves | `Salt.Chen.Feasible` |
| `Salt.TwinBar.Sep.input_breaks_wall` | Salt/TwinBar/Separation.lean:229 | sieves | `Salt.TwinBar.TwinB_min` |
| `Salt.TwinBar.siegelSequence_implies_infinitely` | Salt/TwinBar/SiegelCorr.lean:64 | sieves | `Salt.TwinBar.SiegelSequence` |
| `Salt.TwinBar.corrWindow_box` | Salt/TwinBar/SiegelCorr.lean:96 | sieves | `Salt.TwinBar.CorrWindow` |
| `Salt.TwinBar.residue_lower` | Salt/TwinBar/SiegelCorr.lean:144 | sieves | `Salt.TwinBar.CorrWindow` |
| `Salt.TwinBar.siegel_correlation_dichotomy` | Salt/TwinBar/SiegelCorr.lean:184 | sieves, characters | `Salt.TwinBar.SiegelSequence`, `Salt.TwinBar.CorrWindow` |
| `Salt.TwinBar.siegel_correlation_strong` | Salt/TwinBar/SiegelCorrStrong.lean:270 | sieves, characters | `Salt.TwinBar.SiegelSequence`, `Salt.TwinBar.CorrWindowStrong` |
| `Salt.TwinBar.no_triple_weight_of_tripleBar` | Salt/TwinBar/ThreeBar.lean:458 | sieves | `Salt.TwinBar.TripleBar` |
| `Salt.TwinBar.twinTypeII_eventually_pos` | Salt/TwinBar/TwinDoor.lean:230 | sieves | `Salt.TwinBar.TwinTypeII` |
| `Salt.TwinBar.twinB_min_implies_twins` | Salt/TwinBar/TwinDoor.lean:270 | sieves | `Salt.TwinBar.TwinB_min` |
| `Salt.TwinBar.wall_or_door` | Salt/TwinBar/TwinDoor.lean:288 | sieves | `Salt.TwinBar.LambdaSummatory` |
| `Salt.TwinBar.class_atom_le_of_affFullRange` | Salt/TwinBar/TwinParityAtomClasses.lean:506 | sieves | `Salt.TwinBar.AffFullRangeAt` |
| `Salt.TwinBar.atom_abs_le_of_affFullRange_classes` | Salt/TwinBar/TwinParityAtomClasses.lean:558 | sieves | `Salt.TwinBar.AffFullRangeAt` |
| `Salt.TwinBar.twinLogWeight_support_infinite_of_affFullRange` | Salt/TwinBar/TwinParityAtomClasses.lean:635 | sieves | `Salt.TwinBar.AffFullRangeAt` |
| `Salt.TwinBar.twinLogWeight_support_infinite_of_affFullRange_all` | Salt/TwinBar/TwinParityAtomClasses.lean:654 | sieves | `Salt.TwinBar.AffFullRangeAt` |
| `Salt.TwinBar.twinParitySieve_rosserRemainder_le` | Salt/TwinBar/TwinParitySieve.lean:293 | sieves | `Salt.TwinBar.LiouvilleTwinDisp` |
| `Salt.TwinBar.twin_parity_survivor_or_chowla_of_liouvilleTwinDisp` | Salt/TwinBar/TwinParitySieve.lean:357 | sieves | `Salt.TwinBar.LiouvilleTwinDisp` |
| `Salt.TwinBar.twinParitySieve_siftedSum_lower_of_liouvilleTwinDisp` | Salt/TwinBar/TwinParitySieve.lean:410 | sieves | `Salt.TwinBar.LiouvilleTwinDisp` |
| `Salt.TwinBar.twinParitySieve_siftedSum_pos_of_margin` | Salt/TwinBar/TwinParitySieve.lean:447 | sieves | `Salt.TwinBar.LiouvilleTwinDisp` |
| `Salt.TwinBar.twinParitySieveLog_rosserRemainder_le` | Salt/TwinBar/TwinParitySieveLog.lean:372 | sieves | `Salt.TwinBar.LiouvilleTwinDispLog` |
| `Salt.TwinBar.twinParitySieveLog_siftedSum_lower` | Salt/TwinBar/TwinParitySieveLog.lean:393 | sieves | `Salt.TwinBar.LiouvilleTwinDispLog` |
| `Salt.TwinBar.twinParitySieveLog_support_infinite` | Salt/TwinBar/TwinParitySieveLog.lean:442 | sieves | `Salt.TwinBar.LiouvilleTwinDispLog` |
| `Salt.TwinBar.rosser_floor_undershoot` | Salt/TwinBar/Wall.lean:100 | sieves | `Salt.BrunLower.IsLowerMoebius` |
| `Salt.TwinBar.rosser_floor_vs_prime_mass` | Salt/TwinBar/Wall.lean:118 | sieves | `Salt.BrunLower.IsLowerMoebius` |
| `Salt.TwinBar.phiLowerR_tolerant` | Salt/TwinBar/Wall.lean:178 | sieves | `Salt.TwinBar.SieveAgree` |
| `Salt.TwinBar.rosserRemainder_sPlus_le` | Salt/TwinBar/Wall.lean:356 | sieves | `Salt.TwinBar.LambdaSummatory` |
| `Salt.TwinBar.rosserRemainder_sMinus_le` | Salt/TwinBar/Wall.lean:370 | sieves | `Salt.TwinBar.LambdaSummatory` |
| `Salt.TwinBar.parity_wall_effective` | Salt/TwinBar/Wall.lean:393 | sieves | `Salt.TwinBar.LambdaSummatory` |
| `Salt.TwinBar.no_parity_beating_certificate` | Salt/TwinBar/Wall.lean:533 | sieves | `Salt.TwinBar.LambdaSummatory` |
| `Salt.TwinBar.phiLowerR_tolerant_corr` | Salt/TwinBar/WallCorr.lean:94 | sieves | `Salt.TwinBar.SieveAgreeCorr` |
| `Salt.Vk.zeta_zero_free_region_pow_of_growth` | Salt/Vk/PowRegion.lean:354 | zeros, exponential sums | `Salt.Vk.ZetaGrowthPow` |
| `Salt.Vk.vk_orbit_fract_sep` | Salt/Vk/Spacing.lean:328 | zeros, exponential sums | `Salt.Vk.VkSpaced` |
| `Salt.Vmvt.pairEqDominant_JkI_le_const` | Salt/Vmvt/Holder.lean:248 | exponential sums | `Salt.Vmvt.PairEqFracBound` |
| `Salt.Vmvt.vmvt_step_transversal_large` | Salt/Vmvt/StepFull.lean:442 | exponential sums | `Salt.Vmvt.VmvtBound` |

## statement-only (211)

| name | file:line | objects |
|---|---|---|
| `Salt.Entropy.Chowla.logChowlaFailsAff` | Salt/Entropy/Chowla/AffineFork.lean:69 | entropy |
| `Salt.Entropy.Chowla.LogChowlaAffSupply` | Salt/Entropy/Chowla/AffineFork.lean:96 | entropy |
| `Salt.Entropy.Chowla.logChowlaFails` | Salt/Entropy/Chowla/ShiftFork.lean:62 | entropy |
| `Salt.Entropy.Chowla.MRTUniformityXiH` | Salt/Entropy/Chowla/ShiftFork.lean:303 | entropy |
| `Salt.Entropy.Chowla.MRTUniformityXiL2H` | Salt/Entropy/Chowla/ShiftFork.lean:545 | entropy |
| `Salt.Entropy.Chowla.MRTUniformityXiAff` | Salt/Entropy/Chowla/StrideFork.lean:644 | entropy |
| `Salt.Entropy.Chowla.MRTUniformityXiL2Aff` | Salt/Entropy/Chowla/StrideFork.lean:652 | entropy |
| `Salt.Entropy.Chowla.LogChowlaAffSupplyW` | Salt/Entropy/Chowla/StridePrize.lean:89 | entropy |
| `Salt.Entropy.Chowla.GradedAffHeadAt` | Salt/Entropy/Chowla/StridePrize.lean:166 | entropy |
| `Salt.Entropy.Chowla.GradedAffHeadAt_g12b` | Salt/Entropy/Chowla/StridePrize.lean:295 | entropy |
| `Salt.HB.IsAdditiveOn` | Salt/HB/CrownAssembly.lean:175 | characters |
| `Salt.HB.Lemma5Eval` | Salt/HB/CrownAssembly.lean:1191 | sieves, characters |
| `Salt.HB.N9Regime` | Salt/HB/CrownTheorem1.lean:442 | characters |
| `Salt.HB.N7Exit` | Salt/HB/CrownTheorem1.lean:512 | characters |
| `Salt.HB.FulcrumQualityPoly` | Salt/HB/CrownTheorem1.lean:6338 | characters |
| `Salt.HB.NoSiegelZerosPoly` | Salt/HB/CrownTheorem1.lean:6348 | characters |
| `Salt.HB.HeathBrownDichotomyPoly` | Salt/HB/CrownTheorem1.lean:6361 | characters |
| `Salt.MR.MRTLargeRangeEquidistributionFixedEps` | Salt/MR/A4FLargeRange.lean:71 | characters |
| `Salt.MR.MRTLemmaA4iiFixed34E` | Salt/MR/A4FLargeRange.lean:84 | characters |
| `Salt.MR.MRTLemmaA4iiFixed34T` | Salt/MR/A4FThreshold.lean:62 | characters |
| `Salt.MR.CofactorSocket` | Salt/MR/CapFreeArm3.lean:258 | characters |
| `Salt.MR.PocketSocket3Gen` | Salt/MR/CofactorSupplier.lean:491 | characters |
| `Salt.MR.CaseASocketGen` | Salt/MR/CofactorSupplier.lean:542 | characters |
| `Salt.MR.S16BaseScaleCapL_gk` | Salt/MR/DoorLinear.lean:473 | characters |
| `Salt.MR.S16BaseScaleCapL96_gk` | Salt/MR/DoorLinear.lean:479 | characters |
| `Salt.MR.MRTDoorReceipt` | Salt/MR/DoorReceipt.lean:84 | characters |
| `Salt.MR.FlatHeadForm` | Salt/MR/DoorReceipt.lean:91 | characters |
| `Salt.MR.FlatSocketForm` | Salt/MR/DoorReceipt.lean:113 | characters |
| `Salt.MR.FlatDoorL2Form` | Salt/MR/DoorReceipt.lean:168 | characters |
| `Salt.MR.FlatRoadForm` | Salt/MR/DoorReceipt.lean:237 | characters |
| `Salt.MR.FlatCapstoneForm` | Salt/MR/DoorReceipt.lean:335 | characters |
| `Salt.MR.FlatConditionalForm` | Salt/MR/DoorReceipt.lean:580 | characters |
| `Salt.MR.FlatKswinForm` | Salt/MR/DoorReceipt.lean:741 | characters |
| `Salt.MR.V7RatedForm` | Salt/MR/DoorReceipt.lean:850 | characters |
| `Salt.MR.MRTDoorAllGrades` | Salt/MR/DoorReceipt.lean:1213 | characters |
| `Salt.MR.FlatDoorAllGradesW` | Salt/MR/FlatDoorAllGrades.lean:50 | characters |
| `Salt.MR.FlatDoorAllGradesBandW` | Salt/MR/FlatDoorAllGradesBand.lean:122 | characters |
| `Salt.MR.FlatHeadFormEpsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:138 | characters |
| `Salt.MR.FlatSocketFormEpsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:164 | characters |
| `Salt.MR.FlatDoorL2FormEpsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:203 | characters |
| `Salt.MR.FlatRoadFormEpsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:234 | characters |
| `Salt.MR.FlatCapstoneFormEpsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:278 | characters |
| `Salt.MR.FlatConditionalFormEpsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:383 | characters |
| `Salt.MR.FlatKswinFormEpsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:413 | characters |
| `Salt.MR.V7RatedFormEpsW_band` | Salt/MR/FlatDoorAllGradesBand.lean:446 | characters |
| `Salt.MR.FlatHeadFormEps` | Salt/MR/FlatDoorEpsChain.lean:130 | characters |
| `Salt.MR.FlatSocketFormEps` | Salt/MR/FlatDoorEpsChain.lean:149 | characters |
| `Salt.MR.FlatDoorL2FormEps` | Salt/MR/FlatDoorEpsChain.lean:178 | characters |
| `Salt.MR.FlatRoadFormEps` | Salt/MR/FlatDoorEpsChain.lean:201 | characters |
| `Salt.MR.FlatCapstoneFormEps` | Salt/MR/FlatDoorEpsChain.lean:235 | characters |
| `Salt.MR.FlatConditionalFormEps` | Salt/MR/FlatDoorEpsChain.lean:328 | characters |
| `Salt.MR.FlatKswinFormEps` | Salt/MR/FlatDoorEpsChain.lean:352 | characters |
| `Salt.MR.V7RatedFormEps` | Salt/MR/FlatDoorEpsChain.lean:380 | characters |
| `Salt.MR.FlatDoorEpsFamilyW` | Salt/MR/FlatDoorEpsFamily.lean:126 | characters |
| `Salt.MR.FlatDoorPayload` | Salt/MR/FlatDoorEpsFamily.lean:299 | characters |
| `Salt.MR.XCeilGateAt` | Salt/MR/FlatDoorEpsRung2.lean:2829 | characters |
| `Salt.MR.XCeilRiderAt` | Salt/MR/FlatDoorEpsRung2.lean:2836 | characters |
| `Salt.MR.XCeilRiderStrictAt` | Salt/MR/FlatDoorEpsRung2.lean:2842 | characters |
| `Salt.MR.S15Sel''_L_T` | Salt/MR/FlatDoorEpsRung2.lean:3800 | characters |
| `Salt.MR.S15Sel''_L_gk_T` | Salt/MR/FlatDoorEpsRung2.lean:3837 | characters |
| `Salt.MR.FlatHeadFormEpsW` | Salt/MR/FlatDoorEpsRung2.lean:4478 | characters |
| `Salt.MR.FlatSocketFormEpsW` | Salt/MR/FlatDoorEpsRung2.lean:4499 | characters |
| `Salt.MR.FlatDoorL2FormEpsW` | Salt/MR/FlatDoorEpsRung2.lean:4529 | characters |
| `Salt.MR.FlatRoadFormEpsW` | Salt/MR/FlatDoorEpsRung2.lean:4554 | characters |
| `Salt.MR.FlatCapstoneFormEpsW` | Salt/MR/FlatDoorEpsRung2.lean:4590 | characters |
| `Salt.MR.FlatConditionalFormEpsW` | Salt/MR/FlatDoorEpsRung2.lean:4684 | characters |
| `Salt.MR.FlatKswinFormEpsW` | Salt/MR/FlatDoorEpsRung2.lean:4709 | characters |
| `Salt.MR.V7RatedFormEpsW` | Salt/MR/FlatDoorEpsRung2.lean:4738 | characters |
| `Salt.MR.M4SievedDoorSqH` | Salt/MR/HDoorArc.lean:441 | characters |
| `Salt.MR.M4ChiBlockMeanSqH` | Salt/MR/HDoorClose.lean:85 | characters |
| `Salt.MR.M4ClassBlockMeanSqH` | Salt/MR/HDoorClose.lean:94 | characters |
| `Salt.MR.SocketBaseLH` | Salt/MR/HDoorSupply.lean:542 | characters |
| `Salt.MR.M4SievedDoorSqSupH` | Salt/MR/HDoorSupply.lean:1196 | characters |
| `Salt.MR.M4BlockMeanSqSupQH` | Salt/MR/HDoorSupply.lean:1309 | characters |
| `Salt.MR.HalaszIntegersChiPhi` | Salt/MR/HalaszIntegersChiClose.lean:247 | characters |
| `Salt.MR.TwistedWindowPrice` | Salt/MR/HalaszPrimesChi.lean:750 | characters |
| `Salt.MR.LFunctionInvShallowVkSharp` | Salt/MR/LFunctionInvShallow.lean:1240 | characters |
| `Salt.MR.MmuChiRate_residue_sharp` | Salt/MR/LFunctionInvShallow.lean:1408 | characters |
| `Salt.MR.MmuChiRate` | Salt/MR/LambdaRateTwisted.lean:511 | characters |
| `Salt.MR.LambdaChiSummatory` | Salt/MR/LambdaRateTwisted.lean:522 | characters |
| `Salt.MR.DoorArithFrame` | Salt/MR/M4ArithPage.lean:291 | characters |
| `Salt.MR.SocketBase` | Salt/MR/M4Assembly.lean:431 | characters |
| `Salt.MR.DoorFuseFrame` | Salt/MR/M4Assembly.lean:440 | characters |
| `Salt.MR.M4RowDatumAt` | Salt/MR/M4BaseNarrow.lean:124 | characters |
| `Salt.MR.M4ChiFreeRowMeanSqN` | Salt/MR/M4BaseNarrow.lean:811 | characters |
| `Salt.MR.M4CoprimeBlockMeanSqNN` | Salt/MR/M4BaseNarrow.lean:834 | characters |
| `Salt.MR.M4SievedDoorSqBlk` | Salt/MR/M4BridgeBlock.lean:369 | characters |
| `Salt.MR.M4BlockMeanSqBlk` | Salt/MR/M4BridgeBlock.lean:485 | characters |
| `Salt.MR.M4BlockMeanSq` | Salt/MR/M4BridgeCover.lean:386 | characters |
| `Salt.MR.M4SievedDoorSqSup` | Salt/MR/M4BridgePhase.lean:384 | characters |
| `Salt.MR.DoorCapBase` | Salt/MR/M4CapWire.lean:179 | characters |
| `Salt.MR.M4ChiSummedFreeRow` | Salt/MR/M4ChiSummed.lean:199 | characters |
| `Salt.MR.M4ChiSummedFreeShiftBlock` | Salt/MR/M4ChiSummed.lean:397 | characters |
| `Salt.MR.M4ChiSummedBlockMeanSqN` | Salt/MR/M4ChiSummed.lean:535 | characters |
| `Salt.MR.M4BlockMeanSqSupQ` | Salt/MR/M4ClassPrice.lean:336 | characters |
| `Salt.MR.M4RowMeanSqUnphased` | Salt/MR/M4ClassPrice.lean:863 | characters |
| `Salt.MR.M4LiveAgree` | Salt/MR/M4Close.lean:344 | characters |
| `Salt.MR.M4BandTransport` | Salt/MR/M4Close.lean:350 | characters |
| `Salt.MR.M4SievedDoorSq` | Salt/MR/M4Close.lean:368 | characters |
| `Salt.MR.M4DoorGates` | Salt/MR/M4Close.lean:403 | characters |
| `Salt.MR.M4GradeGate` | Salt/MR/M4Close.lean:425 | characters |
| `Salt.MR.M4GradeGateSplit` | Salt/MR/M4Close.lean:674 | characters |
| `Salt.MR.M4CoprimeChiBlockMeanSqN` | Salt/MR/M4CoprimeSupply.lean:142 | characters |
| `Salt.MR.M4ChiFreeRowMeanSq` | Salt/MR/M4CoprimeSupply.lean:230 | characters |
| `Salt.MR.M4ChiFreeShiftBlockMeanSq` | Salt/MR/M4CoprimeSupply.lean:249 | characters |
| `Salt.MR.DoorRowCarried` | Salt/MR/M4DoorClose.lean:146 | characters |
| `Salt.MR.mrtGate` | Salt/MR/M4Exit.lean:160 | characters |
| `Salt.MR.m4SmallGradeFits` | Salt/MR/M4Maximal.lean:722 | characters |
| `Salt.MR.M4ChiShiftBlockMeanSq` | Salt/MR/M4Maximal.lean:776 | characters |
| `Salt.MR.M4ChiDyadicRowMeanSq` | Salt/MR/M4Maximal.lean:1026 | characters |
| `Salt.MR.M4CoprimeBlockMeanSq` | Salt/MR/M4NonCoprime.lean:339 | characters |
| `Salt.MR.M4CoprimeBlockMeanSqN` | Salt/MR/M4NonCoprime.lean:510 | characters |
| `Salt.MR.MemSPunct` | Salt/MR/M4Puncture.lean:61 | characters |
| `Salt.MR.DoorRowEndBase` | Salt/MR/M4RowsChiEnd.lean:779 | characters |
| `Salt.MR.M4SievedDoorSqBlk2` | Salt/MR/M4SecondRoad.lean:291 | characters |
| `Salt.MR.M4BlockMeanSqBlk2` | Salt/MR/M4SecondRoad.lean:372 | characters |
| `Salt.MR.DoorBandBase` | Salt/MR/M4SocketDischarge.lean:262 | characters |
| `Salt.MR.DoorRowT0Gates` | Salt/MR/M4T0Discharge.lean:571 | characters |
| `Salt.MR.DoorRowCarriedT0` | Salt/MR/M4T0Discharge.lean:581 | characters |
| `Salt.MR.M4ClassBlockMeanSq` | Salt/MR/M4WaveClosed.lean:198 | characters |
| `Salt.MR.M4ChiBlockMeanSq` | Salt/MR/M4WaveClosed.lean:384 | characters |
| `Salt.MR.M4ChiRowMeanSq` | Salt/MR/M4WaveClosed.lean:726 | characters |
| `Salt.MR.M4ChiMaximalStep` | Salt/MR/M4WaveClosed.lean:797 | characters |
| `Salt.MR.M4RowMeanSqLam` | Salt/MR/MRTPortRowLam.lean:49 | characters |
| `Salt.MR.MrtCompMultDatum` | Salt/MR/MRTProp24.lean:196 | characters |
| `Salt.MR.MRTProp24` | Salt/MR/MRTProp24.lean:267 | characters |
| `Salt.MR.MRTProp24Statement` | Salt/MR/MRTProp24.lean:284 | characters |
| `Salt.MR.MRTBands` | Salt/MR/MRTPropA3.lean:58 | characters |
| `Salt.MR.MRTBandCount` | Salt/MR/MRTPropA3.lean:68 | characters |
| `Salt.MR.MRTPropA3` | Salt/MR/MRTPropA3.lean:96 | characters |
| `Salt.MR.MRTPropA3Statement` | Salt/MR/MRTPropA3.lean:151 | characters |
| `Salt.MR.MRTLemmaA4i` | Salt/MR/MRTPropA3.lean:268 | characters |
| `Salt.MR.MRTLemmaA4ii` | Salt/MR/MRTPropA3.lean:296 | characters |
| `Salt.MR.MRTLemmaA6` | Salt/MR/MRTPropA3.lean:380 | characters |
| `Salt.MR.MRTLemmaA7` | Salt/MR/MRTPropA3.lean:393 | characters |
| `Salt.MR.MRTLemmaA6Statement` | Salt/MR/MRTPropA3.lean:407 | characters |
| `Salt.MR.MRTLemmaA7Statement` | Salt/MR/MRTPropA3.lean:410 | characters |
| `Salt.MR.MRTLemmaA4iiFixed` | Salt/MR/MRTPropA3.lean:1647 | characters |
| `Salt.MR.MRTLemmaA5` | Salt/MR/MRTPropA3.lean:1861 | characters |
| `Salt.MR.MRTLemmaA5Statement` | Salt/MR/MRTPropA3.lean:1877 | characters |
| `Salt.MR.MRTShortSegmentSplitting` | Salt/MR/MRTPropA3.lean:3855 | characters |
| `Salt.MR.MRTLargeRangeEquidistribution` | Salt/MR/MRTPropA3.lean:3910 | characters |
| `Salt.MR.MRTThmA1GJ` | Salt/MR/MRTPropA3.lean:3992 | characters |
| `Salt.MR.MRTParsevalConstantMatch` | Salt/MR/MRTPropA3.lean:4076 | characters |
| `Salt.MR.MRTLemmaA7Fixed` | Salt/MR/MRTPropA3.lean:4113 | characters |
| `Salt.MR.MRTLemmaA7FixedStatement` | Salt/MR/MRTPropA3.lean:4123 | characters |
| `Salt.MR.MRTPropA3Ambient34` | Salt/MR/MRTPropA3.lean:4509 | characters |
| `Salt.MR.MRTLemmaA4iiFixed34` | Salt/MR/MRTPropA3.lean:4515 | characters |
| `Salt.MR.MRTLemmaA5_34` | Salt/MR/MRTPropA3.lean:4526 | characters |
| `Salt.MR.MRTPropA3_34` | Salt/MR/MRTPropA3.lean:4540 | characters |
| `Salt.MR.MRTThmA1GJ_34` | Salt/MR/MRTPropA3.lean:4566 | characters |
| `Salt.MR.MRTParsevalConstantMatch_34` | Salt/MR/MRTPropA3.lean:4586 | characters |
| `Salt.MR.MRTLargeRangeEquidistributionFixed` | Salt/MR/MRTPropA3.lean:4758 | characters |
| `Salt.MR.MRTThmA1` | Salt/MR/MRTThmA1.lean:120 | characters |
| `Salt.MR.MRTThmA1Statement` | Salt/MR/MRTThmA1.lean:222 | characters |
| `Salt.MR.MRTThmA1_34` | Salt/MR/MRTThmA1.lean:229 | characters |
| `Salt.MR.MRTThmA1Statement_34` | Salt/MR/MRTThmA1.lean:240 | characters |
| `Salt.MR.MRTThmA2` | Salt/MR/MRTThmA2Stmt.lean:40 | characters |
| `Salt.MR.MRTThmA2Statement` | Salt/MR/MRTThmA2Stmt.lean:57 | characters |
| `Salt.MR.MRTThmA2_34` | Salt/MR/MRTThmA2Stmt.lean:63 | characters |
| `Salt.MR.WindowSmooth` | Salt/MR/MobiusChiRamare.lean:175 | characters |
| `Salt.MR.MaskSmooth` | Salt/MR/MobiusChiRamareUnion.lean:116 | characters |
| `Salt.MR.UnionSmooth` | Salt/MR/MobiusChiRamareUnion.lean:748 | characters |
| `Salt.MR.LFunctionInvShallowVk` | Salt/MR/MobiusChiRate.lean:732 | characters |
| `Salt.MR.MmuChiRate_residue` | Salt/MR/MobiusChiRate.lean:750 | characters |
| `Salt.MR.XiCarveWidth` | Salt/MR/MobiusChiRateClose.lean:1104 | characters |
| `Salt.MR.MmuChiRatePrincipal` | Salt/MR/MobiusChiRateClose.lean:1326 | characters |
| `Salt.MR.ZetaInvShallowVk` | Salt/MR/MobiusChiRateClose.lean:1490 | characters |
| `Salt.MR.HalaszPrimesChiGated` | Salt/MR/PortAssembly.lean:761 | characters |
| `Salt.MR.DoorCapErrWS` | Salt/MR/RamErrWS.lean:424 | characters |
| `Salt.MR.S16BaseScaleCap96_LH_gk` | Salt/MR/S13CapGateLinearLH.lean:226 | characters |
| `Salt.MR.S16CofactorSupply_LH_gk` | Salt/MR/S13CapGateLinearLH.lean:233 | characters |
| `Salt.MR.M4ChiSummedFreeRowH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:345 | characters |
| `Salt.MR.M4ChiSummedFreeShiftBlockH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:355 | characters |
| `Salt.MR.M4ChiSummedBlockMeanSqNH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:369 | characters |
| `Salt.MR.M4BlockMeanSqBlk2H_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:380 | characters |
| `Salt.MR.M4SievedDoorSqBlk2H_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:392 | characters |
| `Salt.MR.M4SievedDoorSqH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:406 | characters |
| `Salt.MR.M4ChiSummedFreeRowBigH_L_gk` | Salt/MR/S16FlatTerminalLinearH.lean:1689 | characters |
| `Salt.MR.SeamCoefWS` | Salt/MR/SeamRowWindowed.lean:151 | characters |
| `Salt.MR.FlatHeadFormHG_Z` | Salt/MR/StrideDoorAllGrades.lean:76 | characters |
| `Salt.MR.FlatRoadExitFormHG_Z` | Salt/MR/StrideDoorAllGrades.lean:105 | characters |
| `Salt.MR.FlatCapstoneFormHG_Z` | Salt/MR/StrideDoorAllGrades.lean:148 | characters |
| `Salt.MR.FlatConditionalFormHG_Z` | Salt/MR/StrideDoorAllGrades.lean:254 | characters |
| `Salt.MR.FlatKswinFormHG_Z` | Salt/MR/StrideDoorAllGrades.lean:286 | characters |
| `Salt.MR.V7RatedFormHG_Z` | Salt/MR/StrideDoorAllGrades.lean:325 | characters |
| `Salt.MR.MRTDoorReceiptSetG_Z` | Salt/MR/StrideDoorAllGrades.lean:351 | characters |
| `Salt.MR.StrideDoorAllGradesW` | Salt/MR/StrideDoorAllGrades.lean:363 | characters |
| `Salt.MR.FlatHeadFormHG` | Salt/MR/StridePairReceiptG.lean:86 | characters |
| `Salt.MR.FlatRoadExitFormHG` | Salt/MR/StridePairReceiptG.lean:109 | characters |
| `Salt.MR.FlatCapstoneFormHG` | Salt/MR/StridePairReceiptG.lean:151 | characters |
| `Salt.MR.FlatConditionalFormHG` | Salt/MR/StridePairReceiptG.lean:252 | characters |
| `Salt.MR.FlatKswinFormHG` | Salt/MR/StridePairReceiptG.lean:278 | characters |
| `Salt.MR.V7RatedFormHG` | Salt/MR/StridePairReceiptG.lean:311 | characters |
| `Salt.MR.MRTDoorReceiptSetG` | Salt/MR/StridePairReceiptG.lean:950 | characters |
| `Salt.MR.FlatHeadFormHG_g12b` | Salt/MR/StridePairReceiptG12b.lean:47 | characters |
| `Salt.MR.FlatRoadExitFormHG_g12b` | Salt/MR/StridePairReceiptG12b.lean:71 | characters |
| `Salt.MR.FlatCapstoneFormHG_g12b` | Salt/MR/StridePairReceiptG12b.lean:111 | characters |
| `Salt.MR.FlatConditionalFormHG_g12b` | Salt/MR/StridePairReceiptG12b.lean:212 | characters |
| `Salt.MR.FlatKswinFormHG_g12b` | Salt/MR/StridePairReceiptG12b.lean:238 | characters |
| `Salt.MR.V7RatedFormHG_g12b` | Salt/MR/StridePairReceiptG12b.lean:271 | characters |
| `Salt.MR.MRTDoorReceiptSetG_g12b` | Salt/MR/StridePairReceiptG12b.lean:295 | characters |
| `Salt.MR.StrideSupplyAllStridesW` | Salt/MR/StrideSupplyAllStrides.lean:279 | characters |
| `Salt.MR.S4ArrowUncapped` | Salt/MR/StrideSupplyAllStrides.lean:284 | characters |
| `Salt.MR.TwistedWindowPriceGated` | Salt/MR/TwistedEdge.lean:1068 | characters |
| `Salt.MR.HalaszPrimesChi` | Salt/MR/USetChi.lean:571 | characters |
| `Salt.MR.HalaszIntegersChi` | Salt/MR/USetChiTS.lean:124 | characters |
| `Salt.MR.S16BaseScaleCapEnd_LH_gk` | Salt/MR/V7RatedH.lean:811 | characters |
| `Salt.SW.NoSiegelZerosAt` | Salt/SW/StandoffGate.lean:88 | sieves |
| `Salt.TwinBar.LiouvilleTwinDisp` | Salt/TwinBar/TwinParitySieve.lean:145 | sieves |
| `Salt.TwinBar.LiouvilleTwinDispLog` | Salt/TwinBar/TwinParitySieveLog.lean:133 | sieves |

## infrastructure (481)

| name | file:line | objects |
|---|---|---|
| `Salt.BrunLower.zLev_zero` | Salt/BrunLower/Defs.lean:71 | sieves |
| `Salt.BrunLower.bigOmegaGe_eq_card_iff` | Salt/BrunLower/Defs.lean:160 | sieves |
| `Salt.Chen.EfoldTermAlpha_eq_prim` | Salt/Chen/AlphaSide.lean:146 | sieves, characters |
| `Salt.Chen.bilinTwist_coprimeRestrict_primitive` | Salt/Chen/BilinearDescent.lean:110 | sieves, characters |
| `Salt.Chen.blockTruncSieve₂` | Salt/Chen/BrunEll1.lean:76 | sieves |
| `Salt.Chen.blockTruncSieve₂_lam` | Salt/Chen/BrunEll1.lean:89 | sieves |
| `Salt.Chen.blockAlphaLow_eq_zero_of_pieceN_le` | Salt/Chen/ChenFinal.lean:180 | sieves |
| `Salt.Chen.blockAlphaSym_eq_zero_of_pieceM_le` | Salt/Chen/ChenFinal.lean:195 | sieves |
| `Salt.Chen.twinA1SieveW_W_eq` | Salt/Chen/PackB.lean:58 | sieves |
| `Salt.Chen.EfoldTerm_split` | Salt/Chen/PerEEngine2.lean:104 | sieves |
| `Salt.Chen.blockPrimeInd_dilated_eq_zero` | Salt/Chen/PerEEngine2.lean:118 | sieves |
| `Salt.Chen.EfoldTermBeta_eq_zero` | Salt/Chen/PerEEngine2.lean:147 | sieves |
| `Salt.Chen.blockHonestDisc_eq_sum_pieces` | Salt/Chen/PieceDecomp.lean:205 | sieves |
| `Salt.Chen.maxBlock_eq_zero_of_eps_self` | Salt/Chen/PriceThree.lean:151 | sieves |
| `Salt.Chen.Ebar_tail_eq` | Salt/Chen/SuperProfileDef.lean:118 | sieves |
| `Salt.Chen.Obar_tail_eq` | Salt/Chen/SuperProfileDef.lean:351 | sieves |
| `Salt.Chen.tripleSum_eq_sum_blockTripleSum` | Salt/Chen/SwitchBlocks.lean:194 | sieves |
| `Salt.Chen.blockSwitchSieve_W_eq` | Salt/Chen/SwitchBlocks.lean:254 | sieves |
| `Salt.Chen.switchHonestDisc_eq_sum_box` | Salt/Chen/SwitchDyadic.lean:175 | sieves |
| `Salt.Chen.switchSieveW_W_eq` | Salt/Chen/SwitchW.lean:179 | sieves |
| `Salt.Chen.blockSwitchSieveW_W_eq` | Salt/Chen/SwitchW.lean:193 | sieves |
| `Salt.Chen.blockSwitchSieveW_maxDepth_eq` | Salt/Chen/SwitchW.lean:199 | sieves |
| `Salt.Chen.tauChen_one` | Salt/Chen/TauNumeric.lean:116 | sieves |
| `Salt.Chen.nuChen_eq_inv_totient` | Salt/Chen/TwinA1.lean:109 | sieves |
| `Salt.Chen.omegaPrimeSumW_decomp` | Salt/Chen/TwinA2W.lean:301 | sieves |
| `Salt.Chen.p2Ind_split` | Salt/Chen/TwinDeficit.lean:155 | sieves |
| `Salt.Chen.chenWeightA_half` | Salt/Chen/WeightFamily.lean:103 | sieves |
| `Salt.Chen.readableAffineWeight_chenWeightA` | Salt/Chen/WeightNoGo.lean:154 | sieves |
| `Salt.Entropy.Chowla.logChowlaFailsAff_one_zero` | Salt/Entropy/Chowla/AffineFork.lean:78 | entropy |
| `Salt.Entropy.Chowla.bigXiTwistFilter` | Salt/Entropy/Chowla/CircleMethod.lean:945 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_h` | Salt/Entropy/Chowla/FBridge.lean:539 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_h` | Salt/Entropy/Chowla/FBridge.lean:547 | entropy |
| `Salt.Entropy.Chowla.chi4w` | Salt/Entropy/Chowla/PinDichotomy.lean:285 | entropy |
| `Salt.Entropy.Chowla.delta1w` | Salt/Entropy/Chowla/PinDichotomy.lean:288 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_liouville_apply` | Salt/Entropy/Chowla/Prop26.lean:87 | characters, entropy |
| `Salt.Entropy.Chowla.fBridgeF_h_liouville_apply` | Salt/Entropy/Chowla/Prop26.lean:212 | characters, entropy |
| `Salt.Entropy.Chowla.regimeEnlargeX'` | Salt/Entropy/Chowla/RegimeParam.lean:501 | entropy |
| `Salt.Entropy.Chowla.logChowla2Fails_eq_logChowlaFails_one` | Salt/Entropy/Chowla/ShiftFork.lean:72 | entropy |
| `Salt.Entropy.Chowla.bigXiH` | Salt/Entropy/Chowla/ShiftFork.lean:93 | entropy |
| `Salt.Entropy.Chowla.expSum_add_intCast` | Salt/Entropy/Chowla/ShiftFork.lean:134 | entropy, exponential sums |
| `Salt.Entropy.Chowla.agreeMass_add_disagreeMass` | Salt/Entropy/Chowla/SignSplit.lean:111 | entropy |
| `Salt.Entropy.Chowla.fBridgeG_aff` | Salt/Entropy/Chowla/StrideBridge.lean:86 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_aff` | Salt/Entropy/Chowla/StrideBridge.lean:96 | entropy |
| `Salt.Entropy.Chowla.fBridgeF_aff_liouville_apply` | Salt/Entropy/Chowla/StrideBridge.lean:453 | characters, entropy |
| `Salt.Entropy.Chowla.twistOffset` | Salt/Entropy/Chowla/StrideCircle.lean:83 | entropy |
| `Salt.Entropy.Chowla.xiEta` | Salt/Entropy/Chowla/StrideCircle.lean:89 | entropy |
| `Salt.Entropy.Chowla.affOffset_eq_mul_twistOffset` | Salt/Entropy/Chowla/StrideCircle.lean:95 | entropy |
| `Salt.Entropy.Chowla.mem_xiEta` | Salt/Entropy/Chowla/StrideCircle.lean:103 | entropy |
| `Salt.Entropy.Chowla.badSet_aff` | Salt/Entropy/Chowla/StrideCombine.lean:125 | entropy |
| `Salt.Entropy.Chowla.logMeasureAff_map_shift` | Salt/Entropy/Chowla/StrideDecrement.lean:73 | entropy |
| `Salt.Entropy.Chowla.towerEntropyAff` | Salt/Entropy/Chowla/StrideDecrement.lean:514 | entropy |
| `Salt.Entropy.Chowla.towerMIAff` | Salt/Entropy/Chowla/StrideDecrement.lean:520 | entropy |
| `Salt.Entropy.Chowla.logMeasureAff` | Salt/Entropy/Chowla/StrideFork.lean:75 | entropy |
| `Salt.Entropy.Chowla.logMeasureAff_one` | Salt/Entropy/Chowla/StrideFork.lean:80 | entropy |
| `Salt.Entropy.Chowla.integral_logMeasureAff` | Salt/Entropy/Chowla/StrideFork.lean:90 | entropy |
| `Salt.Entropy.Chowla.isProbabilityMeasure_logMeasureAff` | Salt/Entropy/Chowla/StrideFork.lean:102 | entropy |
| `Salt.Entropy.Chowla.affOffset` | Salt/Entropy/Chowla/StrideFork.lean:194 | entropy |
| `Salt.Entropy.Chowla.bigXiAff` | Salt/Entropy/Chowla/StrideFork.lean:206 | entropy |
| `Salt.Entropy.Chowla.ChowlaRegimeAff.ofRegime` | Salt/Entropy/Chowla/StrideFork.lean:500 | entropy |
| `Salt.Entropy.Chowla.ChowlaRegimeAff.ofRegime_toChowlaRegime` | Salt/Entropy/Chowla/StrideFork.lean:505 | entropy |
| `Salt.Entropy.Chowla.towerDropSum_eq_base_one` | Salt/Entropy/Chowla/StrideFork.lean:523 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_x` | Salt/Entropy/Chowla/StridePair.lean:229 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_omega` | Salt/Entropy/Chowla/StridePair.lean:235 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_a` | Salt/Entropy/Chowla/StridePair.lean:241 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_eps` | Salt/Entropy/Chowla/StridePair.lean:247 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_Hlo` | Salt/Entropy/Chowla/StridePair.lean:253 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_Hhi` | Salt/Entropy/Chowla/StridePair.lean:259 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_C0` | Salt/Entropy/Chowla/StridePair.lean:265 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_J` | Salt/Entropy/Chowla/StridePair.lean:271 | entropy |
| `Salt.Entropy.Chowla.bigXiAffD_of_dvd` | Salt/Entropy/Chowla/StridePair.lean:312 | entropy |
| `Salt.Entropy.Chowla.mrtUniformityXiL2Set_bigXiH_eq` | Salt/Entropy/Chowla/StridePair.lean:346 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_b9` | Salt/Entropy/Chowla/StridePair.lean:917 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_x_b9` | Salt/Entropy/Chowla/StridePair.lean:1010 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_omega_b9` | Salt/Entropy/Chowla/StridePair.lean:1016 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_a_b9` | Salt/Entropy/Chowla/StridePair.lean:1023 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_eps_b9` | Salt/Entropy/Chowla/StridePair.lean:1029 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_Hlo_b9` | Salt/Entropy/Chowla/StridePair.lean:1035 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_Hhi_b9` | Salt/Entropy/Chowla/StridePair.lean:1041 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_C0_b9` | Salt/Entropy/Chowla/StridePair.lean:1047 | entropy |
| `Salt.Entropy.Chowla.regimeShrinkX_stride_J_b9` | Salt/Entropy/Chowla/StridePair.lean:1053 | entropy |
| `Salt.Entropy.Chowla.shiftCorrAff` | Salt/Entropy/Chowla/StrideReduce.lean:272 | entropy |
| `Salt.Entropy.Chowla.shiftCorrAff_base` | Salt/Entropy/Chowla/StrideReduce.lean:278 | characters, entropy |
| `Salt.Entropy.Chowla.badSet_h` | Salt/Entropy/Chowla/Transport.lean:197 | entropy |
| `Salt.Goldbach.goldPs_nu_eq` | Salt/Goldbach/Density.lean:351 | sieves |
| `Salt.Goldbach.goldOmegaPrimeSum_decomp` | Salt/Goldbach/Omega.lean:122 | sieves |
| `Salt.Goldbach.goldBlockHonestDiscW_eq_sum_pieces` | Salt/Goldbach/SW2.lean:143 | sieves |
| `Salt.Goldbach.goldBlockBoxHonestDisc_split_m` | Salt/Goldbach/SW2.lean:234 | sieves |
| `Salt.Goldbach.goldTripleSum_eq_card` | Salt/Goldbach/Switch.lean:79 | sieves |
| `Salt.Goldbach.goldSwitchSieveW_W_eq` | Salt/Goldbach/Switch.lean:445 | sieves |
| `Salt.Goldbach.goldBlockSwitchSieveW_maxDepth_eq` | Salt/Goldbach/Switch.lean:475 | sieves |
| `Salt.HB.hbL1_eq` | Salt/HB/CharTrio.lean:128 | characters |
| `Salt.HB.hbDataN8` | Salt/HB/CrownAssembly.lean:121 | sieves, characters |
| `Salt.HB.hbDataN8_P` | Salt/HB/CrownAssembly.lean:129 | characters |
| `Salt.HB.n8ErrSum` | Salt/HB/CrownAssembly.lean:1219 | characters |
| `Salt.HB.mertens2C` | Salt/HB/CrownAssembly.lean:1224 | characters |
| `Salt.HB.n8C6` | Salt/HB/CrownAssembly.lean:1288 | characters |
| `Salt.HB.lemma4Err` | Salt/HB/CrownChain.lean:439 | characters |
| `Salt.HB.dhB` | Salt/HB/CrownTheorem1.lean:166 | characters |
| `Salt.HB.dhK` | Salt/HB/CrownTheorem1.lean:175 | characters |
| `Salt.HB.dhC` | Salt/HB/CrownTheorem1.lean:257 | characters |
| `Salt.HB.invSqC` | Salt/HB/CrownTheorem1.lean:280 | characters |
| `Salt.HB.merC` | Salt/HB/CrownTheorem1.lean:298 | characters |
| `Salt.HB.segC` | Salt/HB/CrownTheorem1.lean:309 | characters |
| `Salt.HB.n9Ell` | Salt/HB/CrownTheorem1.lean:326 | characters |
| `Salt.HB.n9EllAt` | Salt/HB/CrownTheorem1.lean:335 | characters |
| `Salt.HB.n9Floor` | Salt/HB/CrownTheorem1.lean:346 | characters |
| `Salt.HB.n9Cs` | Salt/HB/CrownTheorem1.lean:351 | characters |
| `Salt.HB.hbZ0A` | Salt/HB/CrownTheorem1.lean:355 | characters |
| `Salt.HB.hbZ0` | Salt/HB/CrownTheorem1.lean:361 | characters |
| `Salt.HB.hbZ` | Salt/HB/CrownTheorem1.lean:366 | characters |
| `Salt.HB.hbS` | Salt/HB/CrownTheorem1.lean:370 | characters |
| `Salt.HB.hbLL` | Salt/HB/CrownTheorem1.lean:376 | characters |
| `Salt.HB.hbKappaN9` | Salt/HB/CrownTheorem1.lean:382 | characters |
| `Salt.HB.n9E0` | Salt/HB/CrownTheorem1.lean:394 | characters |
| `Salt.HB.n9Tail` | Salt/HB/CrownTheorem1.lean:404 | characters |
| `Salt.HB.n9E0B3` | Salt/HB/CrownTheorem1.lean:409 | characters |
| `Salt.HB.n9K` | Salt/HB/CrownTheorem1.lean:528 | characters |
| `Salt.HB.n9K2` | Salt/HB/CrownTheorem1.lean:3875 | characters |
| `Salt.HB.n9K3` | Salt/HB/CrownTheorem1.lean:5354 | characters |
| `Salt.HB.n9Cq` | Salt/HB/CrownTheorem1.lean:6550 | characters |
| `Salt.HB.hbDataHB` | Salt/HB/CrownWireHB.lean:121 | sieves, characters |
| `Salt.HB.hbDataHB_P` | Salt/HB/CrownWireHB.lean:134 | characters |
| `Salt.HB.hbDataHB_S3_eq` | Salt/HB/CrownWireHB.lean:142 | characters |
| `Salt.HB.hbDataHB_eq_hbDataForms_twin` | Salt/HB/CrownWireHBForms.lean:38 | characters |
| `Salt.N7.invMod` | Salt/HB/Lemma10Chain.lean:50 | characters |
| `Salt.N7.hbPhase` | Salt/HB/Lemma10Chain.lean:53 | characters |
| `Salt.N7.hbPhase'` | Salt/HB/Lemma10Chain.lean:57 | characters |
| `Salt.N7.klPhaseSum` | Salt/HB/Lemma10Chain.lean:61 | characters |
| `Salt.N7.lem10Coeff` | Salt/HB/Lemma10Chain.lean:183 | characters |
| `Salt.N7.lem10ExpSum_eq_sum_coeff` | Salt/HB/Lemma10Chain.lean:187 | characters, exponential sums |
| `Salt.N7.lem10ExpSum_kl_mul` | Salt/HB/Lemma10Chain.lean:353 | characters, exponential sums |
| `Salt.N7.norm_lem10ExpSum_neg` | Salt/HB/Lemma10Chain.lean:1276 | characters, exponential sums |
| `Salt.N7.lem10PsiSum` | Salt/HB/Lemma10Seal.lean:76 | characters |
| `Salt.N7.lem10ExpSumZ` | Salt/HB/Lemma10Seal.lean:82 | characters |
| `Salt.N7.sealK` | Salt/HB/Lemma10Seal.lean:134 | characters |
| `Salt.N7.HBForms.twin` | Salt/HB/Lemma5Bilinear.lean:263 | characters |
| `Salt.N7.HBForms.twin_l₁` | Salt/HB/Lemma5Bilinear.lean:296 | characters |
| `Salt.N7.HBForms.twin_l₂` | Salt/HB/Lemma5Bilinear.lean:297 | characters |
| `Salt.N7.HBForms.twin_gcd_eq` | Salt/HB/Lemma5Bilinear.lean:298 | characters |
| `Salt.N7.hbDataForms` | Salt/HB/Lemma5Bilinear.lean:395 | sieves, characters |
| `Salt.N7.hbDataForms_S` | Salt/HB/Lemma5Bilinear.lean:404 | characters |
| `Salt.N7.LamPrime` | Salt/HB/Lemma5Bilinear.lean:413 | characters |
| `Salt.N7.hbQ` | Salt/HB/Lemma5Bilinear.lean:417 | characters |
| `Salt.N7.logDivChiSum` | Salt/HB/Lemma5Bilinear.lean:421 | characters |
| `Salt.N7.LamStarTrunc` | Salt/HB/Lemma5Bilinear.lean:426 | characters |
| `Salt.N7.hbQRad` | Salt/HB/Lemma5Bilinear.lean:557 | characters |
| `Salt.N7.cellCount` | Salt/HB/Lemma5Bilinear.lean:1511 | characters |
| `Salt.N7.unitRep` | Salt/HB/Lemma5Bilinear.lean:1590 | characters |
| `Salt.N7.chiRe_modEq` | Salt/HB/Lemma5Bilinear.lean:1640 | characters |
| `Salt.N7.hbT₁` | Salt/HB/Lemma5Bilinear.lean:2614 | characters |
| `Salt.N7.hbT₂` | Salt/HB/Lemma5Bilinear.lean:2621 | characters |
| `Salt.N7.kb5f_C` | Salt/HB/Lemma5Bilinear.lean:3134 | characters |
| `Salt.HB.primeProdBelow_eq` | Salt/HB/Lemma7Kappa.lean:77 | characters |
| `Salt.HB.hbPairSieve` | Salt/HB/PairInstance.lean:85 | sieves, characters |
| `Salt.HB.crtIn₁` | Salt/HB/RealPrimStructure.lean:103 | characters |
| `Salt.HB.crtIn₂` | Salt/HB/RealPrimStructure.lean:107 | characters |
| `Salt.HB.crtFactor₁` | Salt/HB/RealPrimStructure.lean:151 | characters |
| `Salt.HB.crtFactor₂` | Salt/HB/RealPrimStructure.lean:159 | characters |
| `Salt.HB.hbSieve` | Salt/HB/RosserDim4Instance.lean:161 | sieves, characters |
| `Salt.HB.chiReChar` | Salt/HB/SieveWire.lean:80 | sieves, characters |
| `Salt.HB.hbData` | Salt/HB/SieveWire.lean:130 | sieves, characters |
| `Salt.HB.hbData_P` | Salt/HB/SieveWire.lean:138 | sieves, characters |
| `Salt.HB.hbData_S3_eq` | Salt/HB/SieveWire.lean:145 | sieves, characters |
| `Salt.HB.S2Gen_sub_S1_eq` | Salt/HB/SignChain.lean:519 | characters |
| `Salt.HB.S2Gen_lamR_eq_S1` | Salt/HB/SignLiouville.lean:97 | characters |
| `Salt.HB.overshootExactGen_lamR` | Salt/HB/SignLiouville.lean:103 | characters |
| `Salt.HB.PretenseSumGen_lamR_eq_zero` | Salt/HB/SignLiouville.lean:109 | characters |
| `Salt.HB.n9CB2` | Salt/HB/TailShells.lean:44 | characters |
| `Salt.HB.n9DB2` | Salt/HB/TailShells.lean:47 | characters |
| `Salt.HB.overshootLog_eq_zero_of_nMinus_ne_one` | Salt/HB/Transfer.lean:124 | characters |
| `Salt.HB.overshootPP_eq_zero_of_not_isPrimePow` | Salt/HB/Transfer.lean:133 | characters |
| `Salt.MR.a2DoorGrade_pool_L_at_decay` | Salt/MR/ArithPageLinear.lean:802 | characters |
| `Salt.MR.mem_bigXi_iff` | Salt/MR/BigXiArc.lean:373 | characters, exponential sums |
| `Salt.MR.lamChi_eq_liouChi_prime` | Salt/MR/CapFreeAssembly.lean:458 | characters |
| `Salt.MR.caseASwide` | Salt/MR/CaseAWide.lean:379 | characters |
| `Salt.MR.caseASwide_eq_caseAS2` | Salt/MR/CaseAWide.lean:385 | characters |
| `Salt.MR.seamCoeff_twist_combine` | Salt/MR/CenterSupply.lean:92 | characters |
| `Salt.MR.pretDistSq_twist_slot` | Salt/MR/CenterSupply.lean:121 | characters |
| `Salt.MR.pieceDatum` | Salt/MR/CofactorSupplier.lean:71 | characters |
| `Salt.MR.doorCofactor0` | Salt/MR/CofactorSupplier.lean:77 | characters |
| `Salt.MR.pieceDatum_mul` | Salt/MR/CofactorSupplier.lean:119 | characters |
| `Salt.MR.pieceDatum_insert_prime` | Salt/MR/CofactorSupplier.lean:289 | characters |
| `Salt.MR.dampDatum` | Salt/MR/CofactorSupplier.lean:438 | characters |
| `Salt.MR.cofactorRbdGen` | Salt/MR/CofactorSupplier.lean:551 | characters |
| `Salt.MR.caseAS_293` | Salt/MR/CofactorSupply.lean:626 | characters |
| `Salt.MR.pretDistSq_continuous_freq` | Salt/MR/CompactMin.lean:104 | characters |
| `Salt.MR.pretDistSq_principal` | Salt/MR/Dist.lean:66 | characters |
| `Salt.MR.pretDistSq_liouville_split` | Salt/MR/Dist.lean:83 | characters |
| `Salt.MR.HplusStar70` | Salt/MR/DoorFloor.lean:416 | characters |
| `Salt.MR.AdoorL` | Salt/MR/DoorLinear.lean:82 | characters |
| `Salt.MR.doorRowFloorL` | Salt/MR/DoorLinear.lean:530 | characters |
| `Salt.MR.gJR_ofReal` | Salt/MR/Eq26Bridge.lean:115 | characters |
| `Salt.MR.gJR_prime_pow` | Salt/MR/Eq26Bridge.lean:295 | characters |
| `Salt.MR.e4aEta_def` | Salt/MR/EvenChiEta.lean:220 | characters |
| `Salt.MR.e4a_zetaO_image` | Salt/MR/EvenChiEta.lean:326 | characters |
| `Salt.MR.e4a_toC_conductor_eq` | Salt/MR/EvenChiRingBridge.lean:125 | characters |
| `Salt.MR.e4a_toC_isPrimitive_iff` | Salt/MR/EvenChiRingBridge.lean:131 | characters |
| `Salt.MR.E4aChiBridge.e4a_signOf_eq_one_or_neg_one` | Salt/MR/EvenChiSign.lean:158 | characters |
| `Salt.MR.plogM0` | Salt/MR/FarL2.lean:385 | characters |
| `Salt.MR.plogM0_add_debit` | Salt/MR/FarL2.lean:390 | characters |
| `Salt.MR.boxM0` | Salt/MR/FarL2.lean:650 | characters |
| `Salt.MR.winL2Coeff` | Salt/MR/FarL2.lean:717 | characters |
| `Salt.MR.windowSum_eq_dpoly` | Salt/MR/FarL2.lean:750 | characters |
| `Salt.MR.winL2Mass` | Salt/MR/FarL2.lean:773 | characters |
| `Salt.MR.winL2Coeff_l2_eq` | Salt/MR/FarL2.lean:782 | characters |
| `Salt.MR.winL2Tail` | Salt/MR/FarL2.lean:822 | characters |
| `Salt.MR.boxM0_add_debit` | Salt/MR/FarL2.lean:956 | characters |
| `Salt.MR.blockCoeff` | Salt/MR/FarL2Dyadic.lean:107 | characters |
| `Salt.MR.dpoly_block_eq` | Salt/MR/FarL2Dyadic.lean:124 | characters |
| `Salt.MR.dpolyBlockMass` | Salt/MR/FarL2Dyadic.lean:171 | characters |
| `Salt.MR.blockCoeff_l2_eq` | Salt/MR/FarL2Dyadic.lean:178 | characters |
| `Salt.MR.sum_dpolyBlockMass_eq` | Salt/MR/FarL2Dyadic.lean:420 | characters |
| `Salt.MR.winL2Price` | Salt/MR/FarL2Dyadic.lean:429 | characters |
| `Salt.MR.farL2Grade` | Salt/MR/FarL2Dyadic.lean:481 | characters |
| `Salt.MR.farL2Threshold` | Salt/MR/FarL2Dyadic.lean:537 | characters |
| `Salt.MR.farKfarPolylog` | Salt/MR/FarL2Dyadic.lean:815 | characters |
| `Salt.MR.xCeilGateAt_fifty` | Salt/MR/FlatDoorEpsRung2.lean:2849 | characters |
| `Salt.MR.xCeilRiderAt_fifty` | Salt/MR/FlatDoorEpsRung2.lean:2853 | characters |
| `Salt.MR.xCeilRiderStrictAt_fifty` | Salt/MR/FlatDoorEpsRung2.lean:2857 | characters |
| `Salt.MR.crownK6_windowExpSum_zero` | Salt/MR/FlatDoorParityFloor.lean:51 | characters, exponential sums |
| `Salt.MR.jointIntegrableAt_iff_C` | Salt/MR/GradeWindowC.lean:206 | characters |
| `Salt.MR.socketBaseLH_one_iff` | Salt/MR/HDoorSupply.lean:552 | characters |
| `Salt.MR.seamCoeff_trivial_dist_eq` | Salt/MR/HalaszHead.lean:375 | characters |
| `Salt.MR.dpolyChi_Icc` | Salt/MR/HybridLargeValues.lean:484 | characters |
| `Salt.MR.chiBarCoeff` | Salt/MR/HybridMoments.lean:113 | characters |
| `Salt.MR.chiBarAf` | Salt/MR/HybridMoments.lean:208 | characters |
| `Salt.MR.shallowGrowth` | Salt/MR/LFunctionInvShallow.lean:297 | characters |
| `Salt.MR.vkShallowWidthSharp` | Salt/MR/LFunctionInvShallow.lean:456 | characters |
| `Salt.MR.shallowA` | Salt/MR/LFunctionInvShallow.lean:499 | characters |
| `Salt.MR.lamGrMask` | Salt/MR/LambdaChiMask.lean:91 | characters |
| `Salt.MR.lamTailWeightMask` | Salt/MR/LambdaChiMask.lean:125 | characters |
| `Salt.MR.MlamGrChiMask` | Salt/MR/LambdaChiMask.lean:356 | characters |
| `Salt.MR.lamGr` | Salt/MR/LambdaChiRamare.lean:130 | characters |
| `Salt.MR.lamTailWeight` | Salt/MR/LambdaChiRamare.lean:167 | characters |
| `Salt.MR.MlamGrChi` | Salt/MR/LambdaChiRamare.lean:453 | characters |
| `Salt.MR.MlamRamChi` | Salt/MR/LambdaChiRamare.lean:774 | characters |
| `Salt.MR.chiBarTwist` | Salt/MR/LambdaRateTwisted.lean:222 | characters |
| `Salt.MR.MmuChi` | Salt/MR/LambdaRateTwisted.lean:295 | characters |
| `Salt.MR.MlambdaChi` | Salt/MR/LambdaRateTwisted.lean:300 | characters |
| `Salt.MR.MmuChi_one_zero` | Salt/MR/LambdaRateTwisted.lean:309 | characters |
| `Salt.MR.MlambdaChi_one_zero` | Salt/MR/LambdaRateTwisted.lean:317 | characters |
| `Salt.MR.primitiveCharacter_odd_iff` | Salt/MR/LandauDescent.lean:249 | characters |
| `Salt.MR.doorRho` | Salt/MR/M4ArithPage.lean:592 | characters |
| `Salt.MR.RSanDoor` | Salt/MR/M4ArithPage.lean:599 | characters |
| `Salt.MR.gArmDoor` | Salt/MR/M4ArithPage.lean:815 | characters |
| `Salt.MR.doorCoeffU` | Salt/MR/M4Assembly.lean:171 | characters |
| `Salt.MR.a2DoorGrade` | Salt/MR/M4Assembly.lean:213 | characters |
| `Salt.MR.a2DoorGrade_pool_at_decay` | Salt/MR/M4AssemblyPool.lean:71 | characters |
| `Salt.MR.numBlocks` | Salt/MR/M4BridgeBlock.lean:125 | characters |
| `Salt.MR.blockCut` | Salt/MR/M4BridgeBlock.lean:151 | characters |
| `Salt.MR.blockSupSq` | Salt/MR/M4BridgeBlock.lean:330 | characters |
| `Salt.MR.doorSievedCoeff` | Salt/MR/M4BridgeCover.lean:361 | characters |
| `Salt.MR.dilLen` | Salt/MR/M4BridgeDilate.lean:124 | characters |
| `Salt.MR.classCoeff` | Salt/MR/M4BridgeDilate.lean:283 | characters |
| `Salt.MR.dilCoeff` | Salt/MR/M4BridgeDilate.lean:288 | characters |
| `Salt.MR.classWindowSum` | Salt/MR/M4BridgeDilate.lean:293 | characters |
| `Salt.MR.classWindowSum_eq_absWindowSum` | Salt/MR/M4BridgeDilate.lean:314 | characters |
| `Salt.MR.absWindowSum_dilCoeff_memS_door` | Salt/MR/M4BridgeDilate.lean:393 | characters |
| `Salt.MR.classWindowSum_eq_classPhaseSum` | Salt/MR/M4BridgeDilate.lean:674 | characters |
| `Salt.MR.doorCoeffPhase` | Salt/MR/M4BridgeIntegral.lean:168 | characters |
| `Salt.MR.absWindowSum_eq_eR_sum` | Salt/MR/M4BridgePhase.lean:173 | characters |
| `Salt.MR.phaseCoeff` | Salt/MR/M4BridgePhase.lean:188 | characters |
| `Salt.MR.sum_Ioc_phaseCoeff_eq` | Salt/MR/M4BridgePhase.lean:195 | characters |
| `Salt.MR.subWindowSup` | Salt/MR/M4BridgePhase.lean:217 | characters |
| `Salt.MR.absWindowSum_add_eq_phase_sum` | Salt/MR/M4BridgePhase.lean:276 | characters |
| `Salt.MR.residueClassOn` | Salt/MR/M4BridgeResidue.lean:108 | characters |
| `Salt.MR.windowClass` | Salt/MR/M4BridgeResidue.lean:112 | characters |
| `Salt.MR.ratPhase` | Salt/MR/M4BridgeResidue.lean:161 | characters |
| `Salt.MR.classPhaseSum` | Salt/MR/M4BridgeResidue.lean:167 | characters |
| `Salt.MR.absWindowSum_residue_split` | Salt/MR/M4BridgeResidue.lean:240 | characters |
| `Salt.MR.chiFreeRowSq` | Salt/MR/M4ChiSummed.lean:154 | characters |
| `Salt.MR.absWindowSum_zero` | Salt/MR/M4ClassPrice.lean:113 | characters |
| `Salt.MR.classPhaseSum_zero` | Salt/MR/M4ClassPrice.lean:120 | characters |
| `Salt.MR.sievedWindow` | Salt/MR/M4ClassPrice.lean:181 | characters |
| `Salt.MR.m4DecayGrade` | Salt/MR/M4ClassPrice.lean:794 | characters |
| `Salt.MR.m4RawMS` | Salt/MR/M4Close.lean:206 | characters |
| `Salt.MR.m4Saving` | Salt/MR/M4Close.lean:216 | characters |
| `Salt.MR.arcDen_twelve_eq_m4W` | Salt/MR/M4Close.lean:221 | characters |
| `Salt.MR.m4Saving_eq` | Salt/MR/M4Close.lean:226 | characters |
| `Salt.MR.winCutH` | Salt/MR/M4DoorRow.lean:146 | characters |
| `Salt.MR.doorRowFloor` | Salt/MR/M4DoorRow.lean:462 | characters |
| `Salt.MR.log_dyadScale` | Salt/MR/M4Dyadic.lean:432 | characters |
| `Salt.MR.endMass` | Salt/MR/M4ErrRewire.lean:168 | characters |
| `Salt.MR.liouChi_mul` | Salt/MR/M4ErrRewire.lean:289 | characters |
| `Salt.MR.lamCoeff_eq_liouvilleC` | Salt/MR/M4Exit.lean:99 | characters |
| `Salt.MR.mrtDeliveredGrade` | Salt/MR/M4Exit.lean:153 | characters |
| `Salt.MR.H0scale` | Salt/MR/M4Exit.lean:194 | characters |
| `Salt.MR.chiGaussSum` | Salt/MR/M4Gauss.lean:101 | characters |
| `Salt.MR.capL` | Salt/MR/M4Gauss.lean:496 | characters |
| `Salt.MR.strataTerm` | Salt/MR/M4Gauss.lean:565 | characters |
| `Salt.MR.strataResidual` | Salt/MR/M4Gauss.lean:669 | characters |
| `Salt.MR.m4Cmax` | Salt/MR/M4Maximal.lean:674 | characters |
| `Salt.MR.m4BclGraded` | Salt/MR/M4Maximal.lean:698 | characters |
| `Salt.MR.memSPunctCoeff` | Salt/MR/M4Puncture.lean:74 | characters |
| `Salt.MR.m4Demand_door` | Salt/MR/M4Quality.lean:103 | characters |
| `Salt.MR.liouvilleC` | Salt/MR/M4Residue.lean:91 | characters |
| `Salt.MR.lemma12RowsMR` | Salt/MR/M4RowMR.lean:78 | characters |
| `Salt.MR.lemma12RowsMR_end` | Salt/MR/M4RowMR.lean:312 | characters |
| `Salt.MR.rowPairSetG` | Salt/MR/M4RowsChi.lean:135 | characters |
| `Salt.MR.rowPairSetG_fibre` | Salt/MR/M4RowsChi.lean:141 | characters |
| `Salt.MR.m4MrowChi` | Salt/MR/M4RowsChi.lean:794 | characters |
| `Salt.MR.m4MrowChiEnd` | Salt/MR/M4RowsChiEnd.lean:447 | characters |
| `Salt.MR.blockLen` | Salt/MR/M4SecondRoad.lean:173 | characters |
| `Salt.MR.truncBudget` | Salt/MR/M4SecondRoad.lean:775 | characters |
| `Salt.MR.truncD` | Salt/MR/M4SecondRoad.lean:791 | characters |
| `Salt.MR.rStrWitness` | Salt/MR/M4SecondRoad.lean:870 | characters |
| `Salt.MR.rSanWitness` | Salt/MR/M4SecondRoad.lean:881 | characters |
| `Salt.MR.m4ArcFloor` | Salt/MR/M4Spine.lean:147 | characters |
| `Salt.MR.arcDen_twelve_eq_pow` | Salt/MR/M4Spine.lean:159 | characters |
| `Salt.MR.cfbM0_add_debit` | Salt/MR/M4T0Datum.lean:616 | characters |
| `Salt.MR.jMask` | Salt/MR/M4T0DatumDischarge.lean:105 | characters |
| `Salt.MR.maskOmega_eq_zero_iff` | Salt/MR/M4T0DatumDischarge.lean:113 | characters |
| `Salt.MR.blockOmega_eq_zero_iff` | Salt/MR/M4T0DatumDischarge.lean:119 | characters |
| `Salt.MR.t0dM0` | Salt/MR/M4T0Discharge.lean:95 | characters |
| `Salt.MR.t0dB` | Salt/MR/M4T0Discharge.lean:99 | characters |
| `Salt.MR.t0dC1` | Salt/MR/M4T0Discharge.lean:105 | characters |
| `Salt.MR.classSup` | Salt/MR/M4WaveClosed.lean:141 | characters |
| `Salt.MR.doorSievedWindow` | Salt/MR/M4WaveClosed.lean:364 | characters |
| `Salt.MR.doorChiSup` | Salt/MR/M4WaveClosed.lean:369 | characters |
| `Salt.MR.doorChiCoeff` | Salt/MR/M4WaveClosed.lean:708 | characters |
| `Salt.MR.windowExpSum_eq_offWindowSum` | Salt/MR/M4Window.lean:100 | characters, exponential sums |
| `Salt.MR.offWindowSum_eq_rebase` | Salt/MR/M4Window.lean:151 | characters |
| `Salt.MR.absWindowSum_add_coeff` | Salt/MR/M4Window.lean:325 | characters |
| `Salt.MR.mrtM_lam_eq_lamCoeff` | Salt/MR/MRTPortA1.lean:54 | characters |
| `Salt.MR.mrtBandP` | Salt/MR/MRTProp24.lean:71 | characters |
| `Salt.MR.mrtBandQ` | Salt/MR/MRTProp24.lean:79 | characters |
| `Salt.MR.mrtBandP_one` | Salt/MR/MRTProp24.lean:90 | characters |
| `Salt.MR.mrtBandQ_one` | Salt/MR/MRTProp24.lean:97 | characters |
| `Salt.MR.mem_mrtBand_nat` | Salt/MR/MRTProp24.lean:111 | characters |
| `Salt.MR.mrtJ` | Salt/MR/MRTProp24.lean:122 | characters |
| `Salt.MR.mrtS` | Salt/MR/MRTProp24.lean:130 | characters |
| `Salt.MR.mem_mrtS` | Salt/MR/MRTProp24.lean:136 | characters |
| `Salt.MR.mrtP1` | Salt/MR/MRTProp24.lean:158 | characters |
| `Salt.MR.mrtQ1` | Salt/MR/MRTProp24.lean:161 | characters |
| `Salt.MR.mrtSProp24` | Salt/MR/MRTProp24.lean:167 | characters |
| `Salt.MR.mrtM` | Salt/MR/MRTProp24.lean:175 | characters |
| `Salt.MR.mrtQuality` | Salt/MR/MRTProp24.lean:187 | characters |
| `Salt.MR.mrtWindowExpSum` | Salt/MR/MRTProp24.lean:217 | characters |
| `Salt.MR.mrtT0` | Salt/MR/MRTPropA3.lean:214 | characters |
| `Salt.MR.mrtT1` | Salt/MR/MRTPropA3.lean:220 | characters |
| `Salt.MR.mrtT0_union_mrtT1` | Salt/MR/MRTPropA3.lean:225 | characters |
| `Salt.MR.blockOmega_eq_zero_of_le_one` | Salt/MR/MRTPropA3.lean:580 | characters |
| `Salt.MR.costwist_conj_avg` | Salt/MR/MRTPropA3.lean:683 | characters |
| `Salt.MR.mrtT0_eq_empty_of_high_M` | Salt/MR/MRTPropA3.lean:1598 | characters |
| `Salt.MR.mrtG` | Salt/MR/MRTPropA3.lean:1854 | characters |
| `Salt.MR.dpolyA_eq_dpolyS` | Salt/MR/MRTPropA3.lean:2381 | characters |
| `Salt.MR.blockOmega_eq_zero_of_lt` | Salt/MR/MRTPropA3.lean:2521 | characters |
| `Salt.MR.blockOmega_eq_zero_of_no_prime` | Salt/MR/MRTPropA3.lean:2557 | characters |
| `Salt.MR.costwist_one` | Salt/MR/MRTPropA3.lean:3126 | characters |
| `Salt.MR.costwist_mul` | Salt/MR/MRTPropA3.lean:3133 | characters |
| `Salt.MR.mrtShortMean` | Salt/MR/MRTThmA1.lean:89 | characters |
| `Salt.MR.pretFloorShape_def` | Salt/MR/MWindowBridge.lean:97 | characters |
| `Salt.MR.M_rangeCap_at_self` | Salt/MR/MWindowBridge.lean:356 | characters |
| `Salt.MR.muGr` | Salt/MR/MobiusChiRamare.lean:150 | characters |
| `Salt.MR.ramTailWeight` | Salt/MR/MobiusChiRamare.lean:193 | characters |
| `Salt.MR.MmuGrChi` | Salt/MR/MobiusChiRamare.lean:416 | characters |
| `Salt.MR.MmuRamChi` | Salt/MR/MobiusChiRamare.lean:768 | characters |
| `Salt.MR.MaskPrimeDivs` | Salt/MR/MobiusChiRamareUnion.lean:106 | characters |
| `Salt.MR.maskOmega` | Salt/MR/MobiusChiRamareUnion.lean:111 | characters |
| `Salt.MR.maskOmega_mul_coprime` | Salt/MR/MobiusChiRamareUnion.lean:137 | characters |
| `Salt.MR.maskOmega_prime_pow` | Salt/MR/MobiusChiRamareUnion.lean:145 | characters |
| `Salt.MR.maskSmooth_prime_pow_iff` | Salt/MR/MobiusChiRamareUnion.lean:153 | characters |
| `Salt.MR.muGrMask` | Salt/MR/MobiusChiRamareUnion.lean:163 | characters |
| `Salt.MR.maskTailWeight` | Salt/MR/MobiusChiRamareUnion.lean:193 | characters |
| `Salt.MR.MmuGrChiMask` | Salt/MR/MobiusChiRamareUnion.lean:370 | characters |
| `Salt.MR.MmuRamChiMask` | Salt/MR/MobiusChiRamareUnion.lean:662 | characters |
| `Salt.MR.blockMask` | Salt/MR/MobiusChiRamareUnion.lean:735 | characters |
| `Salt.MR.unionMask` | Salt/MR/MobiusChiRamareUnion.lean:741 | characters |
| `Salt.MR.unionOmega` | Salt/MR/MobiusChiRamareUnion.lean:745 | characters |
| `Salt.MR.maskOmega_blockMask` | Salt/MR/MobiusChiRamareUnion.lean:759 | characters |
| `Salt.MR.maskSmooth_blockMask_iff` | Salt/MR/MobiusChiRamareUnion.lean:765 | characters |
| `Salt.MR.muGrU` | Salt/MR/MobiusChiRamareUnion.lean:827 | characters |
| `Salt.MR.ramTailWeightU` | Salt/MR/MobiusChiRamareUnion.lean:832 | characters |
| `Salt.MR.MmuGrChiU` | Salt/MR/MobiusChiRamareUnion.lean:836 | characters |
| `Salt.MR.MmuRamChiU` | Salt/MR/MobiusChiRamareUnion.lean:842 | characters |
| `Salt.MR.muChiTw` | Salt/MR/MobiusChiRate.lean:122 | characters |
| `Salt.MR.MmuChi_eq_sum_muChiTw` | Salt/MR/MobiusChiRate.lean:145 | characters |
| `Salt.MR.Mmu1Chi` | Salt/MR/MobiusChiRate.lean:196 | characters |
| `Salt.MR.vkBoxWidth` | Salt/MR/MobiusChiRate.lean:367 | characters |
| `Salt.MR.clBoxWidth` | Salt/MR/MobiusChiRate.lean:373 | characters |
| `Salt.MR.boxWidth` | Salt/MR/MobiusChiRate.lean:378 | characters |
| `Salt.MR.vkShallowWidth` | Salt/MR/MobiusChiRate.lean:679 | characters |
| `Salt.MR.pinT` | Salt/MR/MobiusChiRateClose.lean:358 | characters |
| `Salt.MR.pinW` | Salt/MR/MobiusChiRateClose.lean:363 | characters |
| `Salt.MR.TsumChi` | Salt/MR/MobiusChiRateClose.lean:847 | characters |
| `Salt.MR.eulerFac` | Salt/MR/MobiusChiRateClose.lean:1390 | characters |
| `Salt.MR.spoly_of_support_le` | Salt/MR/MultShiuBridge.lean:68 | characters |
| `Salt.MR.costwist_re` | Salt/MR/NonPret.lean:56 | characters |
| `Salt.MR.K₄` | Salt/MR/PortAssembly.lean:637 | characters |
| `Salt.MR.K₅` | Salt/MR/PortAssembly.lean:673 | characters |
| `Salt.MR.rhsFbound_eq_rhsFboundC` | Salt/MR/RHSGradeC.lean:75 | characters |
| `Salt.MR.rhsSigmaG_eq_rhsSigmaGC` | Salt/MR/RHSGradeC.lean:80 | characters |
| `Salt.MR.rhsFboundC_eq_exp_mul` | Salt/MR/RHSGradeC.lean:86 | characters |
| `Salt.MR.blockOmega_mul_coprime` | Salt/MR/RamWeight.lean:86 | characters |
| `Salt.MR.ramR_eq_integral_damp` | Salt/MR/RamWeight.lean:179 | characters |
| `Salt.MR.ramP2domEndMR` | Salt/MR/RamareP2End.lean:51 | characters |
| `Salt.MR.ramP2corrEndMR` | Salt/MR/RamareP2End.lean:58 | characters |
| `Salt.MR.ramP2coeffEndMR` | Salt/MR/RamareP2End.lean:67 | characters |
| `Salt.MR.regimeEnlargeX_x` | Salt/MR/RegimeHead.lean:133 | characters |
| `Salt.MR.regimeEnlargeX_omega` | Salt/MR/RegimeHead.lean:136 | characters |
| `Salt.MR.regimeEnlargeX_eps` | Salt/MR/RegimeHead.lean:139 | characters |
| `Salt.MR.regimeEnlargeX_Hlo` | Salt/MR/RegimeHead.lean:142 | characters |
| `Salt.MR.regimeEnlargeX_Hhi` | Salt/MR/RegimeHead.lean:145 | characters |
| `Salt.MR.arcFloor36` | Salt/MR/S11Arc36.lean:47 | characters |
| `Salt.MR.loglogFloor50` | Salt/MR/S12Compose.lean:190 | characters |
| `Salt.MR.s12DeltaSock` | Salt/MR/S12Compose.lean:216 | characters |
| `Salt.MR.s12DeltaSock_sq` | Salt/MR/S12Compose.lean:222 | characters |
| `Salt.MR.s16BaseScaleCap96LH_gk_one_iff` | Salt/MR/S13CapGateLinearLH.lean:247 | characters |
| `Salt.MR.s16CofactorSupplyLH_gk_one_iff` | Salt/MR/S13CapGateLinearLH.lean:253 | characters |
| `Salt.MR.flatWitFloor` | Salt/MR/S16FlatTerminal.lean:201 | characters |
| `Salt.MR.flatWitA` | Salt/MR/S16FlatTerminal.lean:728 | characters |
| `Salt.MR.strataResidualH` | Salt/MR/S16FlatTerminalLinearH.lean:117 | characters |
| `Salt.MR.blockLenH` | Salt/MR/S16FlatTerminalLinearH.lean:147 | characters |
| `Salt.MR.m4ChiRowGradedH_L` | Salt/MR/S16FlatTerminalLinearH.lean:1669 | characters |
| `Salt.MR.s16BandLaneCBoundedLH_one_iff` | Salt/MR/S16FlatTerminalLinearLH.lean:114 | characters |
| `Salt.MR.s15CrossingBound_LH_gk_one_iff` | Salt/MR/S16FlatTerminalLinearLH.lean:122 | characters |
| `Salt.MR.RSanDoorRhoH` | Salt/MR/S16ProducersH.lean:71 | characters |
| `Salt.MR.s15ArmH` | Salt/MR/S16ProducersH.lean:706 | characters |
| `Salt.MR.s16BandLaneCBoundedLH_win_one_iff` | Salt/MR/S16UniformLH.lean:161 | characters |
| `Salt.MR.s16BandLaneCBoundedLH_winU_one_iff` | Salt/MR/S16UniformLH.lean:166 | characters |
| `Salt.MR.gJ_mul` | Salt/MR/Sec9Glue.lean:183 | characters |
| `Salt.MR.gJ_eq_prod` | Salt/MR/Sec9Glue.lean:205 | characters |
| `Salt.MR.memS_calFamily` | Salt/MR/SieveGlue.lean:515 | sieves, characters |
| `Salt.MR.regimeShrinkX_stride_L` | Salt/MR/StrideDoorAllGrades.lean:5134 | characters |
| `Salt.MR.regimeShrinkX_stride_x_L` | Salt/MR/StrideDoorAllGrades.lean:5207 | characters |
| `Salt.MR.regimeShrinkX_stride_omega_L` | Salt/MR/StrideDoorAllGrades.lean:5216 | characters |
| `Salt.MR.regimeShrinkX_stride_a_L` | Salt/MR/StrideDoorAllGrades.lean:5225 | characters |
| `Salt.MR.regimeShrinkX_stride_eps_L` | Salt/MR/StrideDoorAllGrades.lean:5234 | characters |
| `Salt.MR.regimeShrinkX_stride_Hlo_L` | Salt/MR/StrideDoorAllGrades.lean:5243 | characters |
| `Salt.MR.regimeShrinkX_stride_Hhi_L` | Salt/MR/StrideDoorAllGrades.lean:5252 | characters |
| `Salt.MR.regimeShrinkX_stride_C0_L` | Salt/MR/StrideDoorAllGrades.lean:5261 | characters |
| `Salt.MR.regimeShrinkX_stride_J_L` | Salt/MR/StrideDoorAllGrades.lean:5270 | characters |
| `Salt.MR.bandSupS_seamRad` | Salt/MR/T0Band.lean:148 | characters |
| `Salt.MR.cfbC₁_sq` | Salt/MR/T0BandCapFree.lean:665 | characters |
| `Salt.MR.twistedEdgeLowConst` | Salt/MR/TwistedEdge.lean:671 | characters |
| `Salt.MR.reflectPair` | Salt/MR/USetChi.lean:86 | characters |
| `Salt.MR.reflectChi` | Salt/MR/USetChi.lean:94 | characters |
| `Salt.MR.UsetChi` | Salt/MR/USetChi.lean:278 | characters |
| `Salt.MR.tLsetChi` | Salt/MR/USetChi.lean:416 | characters |
| `Salt.MR.thinBundleChi` | Salt/MR/USetChiTS.lean:190 | characters |
| `Salt.MR.TsetSmallChi` | Salt/MR/USetChiTS.lean:417 | characters |
| `Salt.MR.fibrePack` | Salt/MR/USetChiTS.lean:552 | characters |
| `Salt.MR.ramQ_eq_spoly` | Salt/MR/USetThinTL.lean:133 | characters |
| `Salt.MR.ramQ_eq_halaszSum` | Salt/MR/USetThinTL.lean:157 | characters |
| `Salt.MR.s16BaseScaleCapEndLH_gk_one_iff` | Salt/MR/V7RatedH.lean:817 | characters |
| `Salt.MR.vkProfile_const_mul` | Salt/MR/VkTwistClose.lean:411 | characters |
| `Salt.MR.vkDebitConst_vkEulerCorr` | Salt/MR/VkTwistClose.lean:478 | characters |
| `Salt.MR.vkStripConst` | Salt/MR/VkTwistStrip.lean:239 | characters |
| `Salt.SW.coprimeSeries_one` | Salt/SW/GrahamHard2.lean:120 | sieves |
| `Salt.SW.selbergPsi_apply` | Salt/SW/PseudoChar.lean:122 | sieves, characters |
| `Salt.SW.hCoef_apply` | Salt/SW/PseudoCharH.lean:81 | sieves, characters |
| `Salt.SW.noSiegelZeros_iff_exists_at` | Salt/SW/StandoffGate.lean:96 | sieves |
| `Salt.TwinBar.w₁_add_w₂` | Salt/TwinBar/Defs.lean:91 | sieves |
| `Salt.TwinBar.w_sum_four` | Salt/TwinBar/FourBar.lean:179 | sieves |
| `Salt.TwinBar.heathBrown_iff_dichotomy` | Salt/TwinBar/SiegelTwin.lean:136 | sieves |
| `Salt.TwinBar.Δ₄_eq_R₄` | Salt/TwinBar/Simplex4.lean:51 | sieves |
| `Salt.TwinBar.Δ₃_one_eq_R₃` | Salt/TwinBar/SimplexS.lean:44 | sieves |
| `Salt.TwinBar.w_sum_three` | Salt/TwinBar/ThreeBar.lean:202 | sieves |
| `Salt.TwinBar.twinParitySieve` | Salt/TwinBar/TwinParitySieve.lean:66 | sieves |
| `Salt.TwinBar.twinParitySieve_prodPrimes` | Salt/TwinBar/TwinParitySieve.lean:82 | sieves |
| `Salt.TwinBar.twinParitySieve_nu` | Salt/TwinBar/TwinParitySieve.lean:85 | sieves |
| `Salt.TwinBar.L` | Salt/TwinBar/TwinParitySieve.lean:106 | sieves |
| `Salt.TwinBar.Btwin` | Salt/TwinBar/TwinParitySieve.lean:242 | sieves |
| `Salt.TwinBar.twinIdx` | Salt/TwinBar/TwinParitySieveLog.lean:46 | sieves |
| `Salt.TwinBar.twinParitySieveLog` | Salt/TwinBar/TwinParitySieveLog.lean:56 | sieves |
| `Salt.TwinBar.twinParitySieveLog_prodPrimes` | Salt/TwinBar/TwinParitySieveLog.lean:73 | sieves |
| `Salt.TwinBar.twinParitySieveLog_nu` | Salt/TwinBar/TwinParitySieveLog.lean:76 | sieves |
| `Salt.TwinBar.Llog` | Salt/TwinBar/TwinParitySieveLog.lean:92 | sieves |
| `Salt.TwinBar.Clog` | Salt/TwinBar/TwinParitySieveLog.lean:97 | sieves |
| `Salt.TwinBar.remLogCount` | Salt/TwinBar/TwinParitySieveLog.lean:101 | sieves |
| `Salt.TwinBar.BtwinLog` | Salt/TwinBar/TwinParitySieveLog.lean:330 | sieves |
| `Salt.Vmvt.vmvtExp_succ` | Salt/Vmvt/MeanValue.lean:197 | exponential sums |
| `Salt.Vmvt.vmvtExp_step_diff` | Salt/Vmvt/StepFull.lean:46 | exponential sums |
| `Salt.Vmvt.vmvtResid_eq` | Salt/Vmvt/StepFull.lean:56 | exponential sums |
| `Salt.Vmvt.Jk_Icc_eq_JkI` | Salt/Vmvt/StepFull.lean:106 | exponential sums |
| `Salt.Vmvt.vmvtConst_eq` | Salt/Vmvt/Summit.lean:46 | exponential sums |
| `Salt.Weil.kloostermanMoment_zero_zero` | Salt/Weil/CurveBridge.lean:286 | exponential sums |
| `Salt.Weil.kloosterman_reindex_units` | Salt/Weil/Kloosterman.lean:103 | exponential sums |
| `Salt.Weil.roadModulus_eq_lcm` | Salt/Weil/RoadModulus.lean:62 | exponential sums |
| `Salt.Weil.dist₁_sub_zero` | Salt/Weil/Sawtooth.lean:59 | exponential sums |
| `Salt.Weil.sawtooth_fourier_expansion` | Salt/Weil/Sawtooth.lean:105 | exponential sums |

## unresolved (1)

| name | file:line | objects |
|---|---|---|
| `Salt.Entropy.Chowla.spine_False_core_xi_sq_flat_h_export` | (audited at) Salt/Entropy/All.lean:1188 | entropy |

