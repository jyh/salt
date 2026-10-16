/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import SaltC1.MaynardK.Miller
import SaltC1.MaynardK.Keys54
import SaltC1.MaynardK.Series54
import SaltC1.MaynardK.MomentI54
import SaltC1.MaynardK.MomentJ54
import SaltC1.MaynardK.Ratio54
import SaltC1.MaynardK.F54
import Salt.Tactic.AuditAxioms

/-!
# C1 · A2d — the `k = 54` certificate's bridge to the Lean side

The aggregator of the bridge: the Miller recurrence and its uniqueness (`Miller`), the key
dictionary (`Keys54`), the series tables (`Series54`), the two value tables and the two forms
(`MomentI54`, `MomentJ54`), and the names the `k = 54` chain consumes (`Ratio54`, `F54`):
`Qsum54`, `Qsum54_pos`, `F54`, `eval_F54_abs_le_one`, `Iform54`, `Jform54`, `simplexInt_sq_F54`,
`simplexInt_sq_contractB_F54`, `ratio_cert_54`, `Iform54_pos` — the names and types of the
A3 stub `Cert54Stub`, which this module replaces. Nothing here bears on twin primes.
-/

-- Build-time axiom audit: every public theorem of the bridge, against the three standard axioms.
open Salt.Tactic in
#audit_axioms SaltC1.MaynardK.miller_coeff SaltC1.MaynardK.eq_coeff_pow_of_rec
  SaltC1.MaynardK.eulerD_mul SaltC1.MaynardK.mul_eulerD_pow
  SaltC1.MaynardK.mem_keysW SaltC1.MaynardK.boxL_ofFn SaltC1.MaynardK.encKey_inj
  SaltC1.MaynardK.decodeC_encKey SaltC1.MaynardK.factT_eq SaltC1.MaynardK.coefBT_getB
  SaltC1.MaynardK.cs54L_basis SaltC1.MaynardK.gT_eq SaltC1.MaynardK.rec_of_check
  SaltC1.MaynardK.p54T_eq SaltC1.MaynardK.p53T_eq SaltC1.MaynardK.p54T_eq'
  SaltC1.MaynardK.p53T_eq' SaltC1.MaynardK.WItree_eq SaltC1.MaynardK.WJtree_eq
  SaltC1.MaynardK.Iint_eq_IformM SaltC1.MaynardK.marginal_spec SaltC1.MaynardK.sum_T
  SaltC1.MaynardK.fs_encK SaltC1.MaynardK.reindex SaltC1.MaynardK.Jint_eq_JformM
  SaltC1.MaynardK.Qsum54_pos SaltC1.MaynardK.eval_F54_abs_le_one
  SaltC1.MaynardK.simplexInt_sq_F54 SaltC1.MaynardK.simplexInt_sq_contractB_F54
  SaltC1.MaynardK.ratio_cert_54 SaltC1.MaynardK.Iform54_pos
