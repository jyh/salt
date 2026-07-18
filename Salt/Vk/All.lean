/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Taylor
import Salt.Vk.Shift
import Salt.Vk.BoxAvg
import Salt.Vk.BoxMeasure
import Salt.Vk.Pointwise
import Salt.Vk.Block
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
  Salt.Vk.eR_intCast
  Salt.Vk.genFun_add_int
  Salt.Vk.vk_box_disjoint_avg
  Salt.Vk.unitMeasure_Ioc_toReal
  Salt.Vk.vkBox_measurable
  Salt.Vk.clip_width_ge
  Salt.Vk.vkBox_measureReal_ge
  Salt.Vk.vkBox_disjoint
  Salt.Vk.vk_box_disjoint_avg_of_centers
  Salt.Vk.poly_shift_orbit
  Salt.Vk.genFun_fract
  Salt.Vk.fract_mem_Icc
  Salt.Vk.vk_shift_genFun_phase
  Salt.Vk.norm_vk_shift_sum
  Salt.Vk.vk_pow_sum_le
  Salt.Vk.vk_shift_average
  Salt.Vk.vk_shift_to_orbit
  Salt.Vk.vk_block_taylor_reduce
