/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Base

/-!
# The Goldbach rung (`chen_goldbach`) — aggregate import

Sprint Q1 (full in-sprint, JYH-ratified 29a9a68): Chen's second theorem —
every sufficiently large even `N` is `p + P₂`. Design:
`docs/exploration/q1-design.md` (frozen statement D0, waves W0–W4,
post-gate corrections). The reuse contract (D1): the 2A backbone imports
unchanged; wave files are new siblings under `Salt/Goldbach/`. This
aggregator is HOUSE-OWNED: executors never edit it; each wave landing is
wired here at its ceremony.
-/
