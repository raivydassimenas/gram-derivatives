---
name: project-constraints
description: Hard constraints that restrict refactoring of the Gram derivatives formalization
metadata:
  type: project
---

Constraints affecting refactoring decisions (from CLAUDE.md and task brief):

- Never change the definitions of `φ` and `δ` in Theorem1.lean — fixed by paper §1.
- Keep `N_step` and `S` abstract; do not specialize `N_step` to ζ-zero ordinates, do not
  couple Theorem1.lean to Karatsuba–Korolev / Riemann ζ.
- Axioms tagged `-- ASSUMPTION` are intentional gaps. The §0.5 sorry ledger lists
  `iteratedDeriv_α_part_isO`, `iteratedDeriv_j_isO`, `iteratedDeriv_tj_isO`, `δ_eq`.
  NOTE: as of 2026-05-22 the file header says it builds with zero `sorry`; the ledger
  comment in the task brief may be stale relative to the file. Verify before flagging.
- Lakefile: `relaxedAutoImplicit = false` (flag stray autobound implicits),
  `pp.unicode.fun = true`, `weak.linter.mathlibStandardSet = true`.
- `Corollary5.lean` must keep only `import Mathlib.Data.Real.Basic` — no heavier imports.

**Why:** These bound what counts as a valid refactor suggestion.
**How to apply:** Reject any suggestion that violates these; never propose them.
