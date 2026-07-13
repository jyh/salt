/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.RosserChain
import Salt.Chen.Tail
import Salt.Chen.LinearSieve
import Salt.Chen.Buchstab
import Salt.Chen.TnInduction
import Salt.Chen.Lemma11
import Salt.Chen.SwitchConstant
import Salt.Tactic.AuditAxioms

/-!
# The Chen rung (`chen`) — aggregate import

Design: `docs/blueprints/chen.md`. Target: **`chen_of_siegelWalfisz`**
(`p + 2 = P₂` infinitely often, modulo the SW gate) — the same gate the
SW arc is discharging, so the day it lands both bounded gaps AND Chen
become unconditional. Route: Tao 254A Supp. 5 (native twin form) with
the BJS explicit linear sieve (arXiv:2207.09452v6) as the constants
backbone; margin `M = 2log3 − log6 − c̄ ≈ 0.0424` at assembly
normalization (catch #20), governed by the frozen C0 budget ledger
(catches #21–#24).

## Landed (wave 1)

`RosserChain` (C1a, FULL): `fseq` (the BJS (15)–(17) Rosser-chain
system, total with documented junk-zero windows; the improper tails
realized as finite `intervalIntegral`s via `fseq_eq_zero_of_ge`),
`Fchain`/`fchain` at the **catch-#24-corrected parities** (F = 1 +
odd sum, f = 1 − EVEN sum; regression witness
`Fchain_add_fchain_one_ne_two` documents that the printed parity would
force F + f ≡ 2), first values `fseq_one_window`/`fseq_two_window`
(= BJS (19)), and the full integrability package (`fseq_props`
coupled induction → `fseq_measurable`/`fseq_bounded`/
`fseq_intervalIntegrable`/`fseq_shift_intervalIntegrable`).

`SwitchConstant` (C4a, FLOOR): `cbar` (the switch integral), `cbar_pos`,
and **`two_log_three_sub_log_six_sub_cbar_pos`** — the literal budget
line C5 consumes (`2log3 − log6 = log(3/2) ≥ 2/5 > 0.363084`). The
tight `cbar_lt : cbar < 0.363084` (gap 2.7e−7) is DEFERRED: mathlib has
no `Li₂`/polylog and no `norm_num` log extension, so neither the exact
dilog route nor a ≳220-panel tangent majorant is in scope — and C3d's
Lean-shape count bound may come from explicit prime sums rather than
the smooth integral, in which case `cbar_lt` is never consumed. See the
module docstring and `docs/blueprints/flags.md`.
-/

-- Build-time axiom audit: a stray axiom in the `chen` carriers fails
-- `lake build` here.
open Salt.Tactic in
#audit_axioms Salt.Chen.cbar_pos
  Salt.Chen.two_log_three_sub_log_six_sub_cbar_pos
  Salt.Chen.fseq_one_window Salt.Chen.fseq_two_window
  Salt.Chen.fseq_nonneg Salt.Chen.fseq_eq_zero_of_ge
  Salt.Chen.fseq_intervalIntegrable Salt.Chen.fseq_shift_intervalIntegrable
  Salt.Chen.Fchain_add_fchain Salt.Chen.Fchain_add_fchain_one_ne_two
  Salt.Chen.fseq_le Salt.Chen.fseq_tail_sum_le Salt.Chen.fseq_tail_le
  Salt.Chen.fchain_close Salt.Chen.Fchain_close
  Salt.Chen.TruncSieve.isUpperMoebius Salt.Chen.TruncSieve.isLowerMoebius
  Salt.Chen.rosserCond_one Salt.Chen.rosserCond_dvd_closed
  Salt.Chen.rosserCond_add_prime
  Salt.Chen.rosserSieve_isUpperMoebius Salt.Chen.rosserSieve_isLowerMoebius
  Salt.Chen.linear_sieve_upper Salt.Chen.linear_sieve_lower
  Salt.Chen.linear_sieve_upper_chain Salt.Chen.linear_sieve_lower_chain
  Salt.Chen.rosserCond_upper_lt Salt.Chen.rosserCond_lower_lt
  Salt.Chen.mainSum_moebius_eq_W Salt.Chen.mainSum_lam_defect
  Salt.Chen.linear_sieve_upper_rosser Salt.Chen.linear_sieve_lower_rosser
  Salt.Chen.buchstab_defect Salt.Chen.buchstab_upper Salt.Chen.buchstab_lower
  Salt.Chen.T_nonneg Salt.Chen.hbar_le_hBJS
  Salt.Chen.hmain_upper Salt.Chen.hmain_lower
  Salt.Chen.linear_sieve_upper_rosser_assembled
  Salt.Chen.linear_sieve_lower_rosser_assembled
  Salt.Chen.prod_telescope Salt.Chen.T_one_upper Salt.Chen.T_two_one_zero
  Salt.Chen.hlevel_one_upper Salt.Chen.tau_sum_le_of_recursion
  Salt.Chen.hTbound_upper_of_levels Salt.Chen.hTbound_lower_of_levels
  Salt.Chen.linear_sieve_upper_rosser_assembled_final
  Salt.Chen.linear_sieve_lower_rosser_assembled_final
