/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Taylor
import Salt.Vk.Shift
import Salt.Vk.BoxAvg
import Salt.Vk.Pointwise
import Salt.Tactic.AuditAxioms

/-!
# The Vinogradov–Korobov track (`Vk`) — aggregate import

THE VMVT-VK CAMPAIGN (JYH ratified 2026-07-18: the power zero-free region
`σ ≥ 1 − c/((log t)^{3/4}(log log t)^3)` from the machine-checked
`Salt.Vmvt.vmvt`, merged with the Littlewood chain; the minimal-power
route θ = 3/4 < 1, MR-gate-satisfying). Freeze: `docs/exploration/vk-freeze.md`;
numeric refuter `scripts/vk_minpow_check.py`.

Opening wave (this file): R1 `VK-TAYLOR` (block Taylor of the ζ-phase),
R2 `VK-SHIFT` (the `2π`-Lipschitz character + block reduction + shift identity),
R3 `VK-BOX-AVG` pointwise core (the box-variation Slack, feeding the measure fold).
Residuals: `docs/blueprints/flags.md` node `VMVT-VK`.
-/

open Salt.Tactic in
#audit_axioms Salt.Vk.log_series_remainder
  Salt.Vk.phi_taylor_block
  Salt.Vk.phi_taylor_block_PY
  Salt.Vk.eR_lipschitz
  Salt.Vk.norm_sum_eR_sub_le
  Salt.Vk.block_reduction
  Salt.Vk.sum_Ioc_shift_boundary
  Salt.Vk.genFun_eq_eR_sum
  Salt.Vk.genFun_lipschitz
  Salt.Vk.genFun_box_variation
  Salt.Vk.poly_shift_orbit
