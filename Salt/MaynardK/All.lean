/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.Basis
import Salt.MaynardK.Capstone105
import Salt.MaynardK.Cert105
import Salt.MaynardK.CollisionS1
import Salt.MaynardK.Controls
import Salt.MaynardK.ControlsSquareM
import Salt.MaynardK.F1
import Salt.MaynardK.Frontier105
import Salt.MaynardK.Gaps636
import Salt.MaynardK.Gaps600
import Salt.MaynardK.ICRel
import Salt.MaynardK.InnerS2Gen
import Salt.MaynardK.ISplit
import Salt.MaynardK.JMain
import Salt.MaynardK.JMainM
import Salt.MaynardK.JMainSplit
import Salt.MaynardK.JSide
import Salt.MaynardK.JSplit
import Salt.MaynardK.LevelRange
import Salt.MaynardK.MomentI
import Salt.MaynardK.MomentJ
import Salt.MaynardK.MvIGen
import Salt.MaynardK.MvJGen
import Salt.MaynardK.PigeonholeK
import Salt.MaynardK.QBridge
import Salt.MaynardK.QFloor
import Salt.MaynardK.Ratio
import Salt.MaynardK.S2Half
import Salt.MaynardK.Series
import Salt.MaynardK.Slack105
import Salt.MaynardK.SlackRho
import Salt.MaynardK.Square
import Salt.MaynardK.SquareM
import Salt.MaynardK.Tuple105
import Salt.MaynardK.Tuple600
import Salt.MaynardK.Vandermonde
import Salt.MaynardK.WinCore105
import Salt.Tactic.AuditAxioms

/-!
# `Salt.MaynardK` — bounded gaps with gap at most 636, and at most 600

The k = 105 run of Maynard's proof of Theorem 1.3 (arXiv:1311.4600v3) with the first 105 primes
greater than 105 as the admissible tuple. The capstones are `Gaps636.gaps_le_636` (no
hypotheses), `Gaps636.maynard_105` (the tuple form) and `Gaps636.gaps_le_636_of_level`; the
general-`k` engines are checked against the landed k = 5 statements in `Controls`.
Nothing here bears on twin primes.
-/

-- Build-time axiom audit: a stray axiom on the capstone path fails `lake build` here.
open Salt.Tactic in
#audit_axioms Salt.MaynardK.gaps_le_636 Salt.MaynardK.maynard_105
  Salt.MaynardK.gaps_le_636_of_level Salt.MaynardK.winSlackM105_ev
  Salt.MaynardK.ratio_cert_105 Salt.MaynardK.Iform_eq Salt.MaynardK.Jform_eq
  Salt.MaynardK.mv_I_of_gen Salt.MaynardK.mv_J_of_gen Salt.MaynardK.mv_I_split_of_gen
  Salt.MaynardK.mv_J_split_of_gen Salt.MaynardK.s2_inner_yF_of_gen
  Salt.MaynardK.qdiag_bridge_k5 Salt.MaynardK.S1_lt_sum_S2mW_k5

-- B5: gap at most 600 on Engelsma's tuple (Tuple600), the same chain made generic in the tuple.
open Salt.Tactic in
#audit_axioms Salt.MaynardK.gaps_le_600 Salt.MaynardK.maynard_105_tuple600
  Salt.MaynardK.engelsmaTuple Salt.MaynardK.hSeq_engelsma_le_743
  Salt.MaynardK.hSeq_engelsma_diam_le_600
