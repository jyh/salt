/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.GLever

/-!
# `S13GK` — alias module for the G-lever base

THE KDESIGN names the lever's leaf module `Salt/MR/GLever.lean`; the dispatch brief also
refers to it as `Salt/MR/S13GK.lean`.  This one-line re-export makes BOTH import paths
resolve to the same declarations, so a later group that writes `import Salt.MR.S13GK`
gets `s13GK` and its basics with no cycle and no duplicate definition.

Everything lives in `Salt.MR.GLever`; nothing is declared here.
-/
