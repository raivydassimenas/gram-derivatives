---
name: theorem1-duplication
description: Known duplication hotspots in Theorem1.lean and the abstractions that would resolve them
metadata:
  type: project
---

Duplication findings in `Theorem1.lean` (as of review 2026-05-22):

1. **`Integrable.mono'` dominator pattern** — `integrable_jIntegrand`, `integrable_sigma_mixedDerivExpr`,
   `integrable_sigma_lorMix_integrand`, `integrable_lorMix_majorant` all repeat: obtain bound,
   build AEStronglyMeasurable, `refine Integrable.mono' ((integrableOn_pow_inv_shift _).const_mul _) _ ?_`,
   `(ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ...)`. A helper
   `integrableOn_of_pow_inv_dominated` would collapse the scaffold.

2. **`hasDerivAt_jK` vs `continuousAt_jK`** — near-identical scaffolding: same `nbhd`,
   `h_nbhd_mem`, `h_nbhd_bound`, `exists_bound_iteratedDeriv_kernel`, `bound`, `h_bound_int`.
   Only the differentiation-under-integral lemma differs.

3. **rpow→reciprocal-power conversions** — `t^(-(k:ℝ)-c) = (t^(k+c))⁻¹` rewrites are
   re-proved inline ~8 times (h_rpow, h_pow_real, h_pow_simp, h_rpow_eq, hrpow, he1, h_zpow_eq,
   h_zpow). One lemma `rpow_neg_natCast_eq_inv` would serve all.

4. **`σ`/`mixedDerivExpr` positivity preamble** — `hr_pos : 0 < u + 1/4`, `h_pow_pos`,
   `h_inv_nn` repeated at the top of nearly every §6 lemma.

5. **`abs_ρ_le_half` re-proved inline** in `integrable_jIntegrand` (lines ~569-574) despite
   the named lemma existing and being used in `norm_jIntegrand_le`.

The three `*_isO` ledger lemmas (`iteratedDeriv_α_part_isO`, `iteratedDeriv_j_isO`,
`iteratedDeriv_tj_isO`) do NOT share a literal duplicated body — each routes through different
machinery (RatExpr / jK / Leibniz). They share only the `=ᶠ[atTop]`-rewrite-then-`trans_isBigO`
*shape*, which is too thin to abstract beyond a possible `eventuallyEq_on_Ioi` helper.

**Why:** User previously flagged the `*_isO` trio as suspected duplication; recorded the
conclusion (shape-only, not body-level) plus the real hotspots.
**How to apply:** Reference these when reviewing §2.5/§6 edits; suggest the helpers above.
