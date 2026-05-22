---
name: theorem1-structure
description: Section layout and recurring proof idioms in GramDerivatives/Theorem1.lean
metadata:
  type: project
---

`Theorem1.lean` (~3600 lines) is organized §0–§8 plus §2.5 (ParametricIntegralJ section).
Build is `sorry`-free as of the file's header (header "Remaining gaps: None").

Recurring proof idioms observed:
- `iteratedDeriv_congr_of_nhds` is the workhorse for lifting a pointwise equality on
  `Set.Ioi 0` to an `iteratedDeriv` equality. Used in iteratedDeriv_φ, RatExpr.iteratedDeriv_eval,
  iteratedDeriv_α_part_isO, iteratedDeriv_δ_isO, theorem1.
- "Reindex `n = m + 2`" via `obtain ⟨m, rfl⟩ : ∃ m, n = m + 2` to avoid `Nat.sub` — iteratedDeriv_log,
  iteratedDeriv_φ.
- `Asymptotics.IsBigO.of_bound C` + `filter_upwards [Filter.eventually_ge_atTop 1]` is the
  standard shape for every `*_isO` lemma.
- HasDerivAt lemmas built by `convert ... using 1; field_simp; ring` (chain/product rule plumbing).
- `RatExpr`/`RatTerm` structure machinery (§5) encodes `c·t^a·(4t²+1)^{-b}` for the α_part bound.

**Why:** Knowing these idioms speeds future reviews and avoids re-deriving the same observations.
**How to apply:** When reviewing edits, check new code reuses these helpers rather than inlining.
