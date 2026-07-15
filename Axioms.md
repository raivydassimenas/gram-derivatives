# Axiom audit

This file records the **complete axiom dependency** of every top-level result in
the project, as reported by Lean's `#print axioms` command. It is the
authoritative answer to "what does each theorem ultimately rest on?"

Regenerate at any time with the scratch module
[`GramDerivatives/AxiomAudit.lean`](GramDerivatives/AxiomAudit.lean):

```bash
lake build GramDerivatives.AxiomAudit   # prints the axiom list for each theorem
```

Last audited: 2026-07-15, against `lean4:v4.30.0-rc2` + matching Mathlib.

## Method

Every proof module builds with **zero `sorry`**. The deep analytic-number-theory
input that Mathlib lacks (Riemann ζ, the Riemann–Siegel θ, Karatsuba–Korolev,
Lavrik/Korolev Gram asymptotics, Kuipers–Niederreiter equidistribution) is
isolated into a small number of `axiom` declarations, each tagged `-- ASSUMPTION`
in source. `#print axioms` walks the full transitive dependency graph, so the
lists below are exhaustive: anything *not* listed is genuinely proved from
Mathlib.

Three axioms appear under every result and are **Lean's standard logical
foundation**, not project assumptions:

| Axiom | Role |
|---|---|
| `propext` | propositional extensionality |
| `Classical.choice` | the axiom of choice |
| `Quot.sound` | soundness of quotients |

These are accepted by essentially all of Mathlib and are omitted from the
discussion of custom assumptions below.

## Summary: custom axioms per theorem

| Theorem | Location | Custom axioms it depends on |
|---|---|---|
| `theorem1` | `Theorem1.lean:3638` | **none** (only the three standard Lean axioms) |
| `corollary2` | `Corollary2.lean:205` | **none** (only the three standard Lean axioms) |
| `theorem3` | `Theorem3.lean:3169` | `contDiffAt_gram`, `gram_asymp`, `gram_deriv_asymp` |
| `Gram.Theorem4.theorem4` | `Theorem4.lean:1925` | the 3 `gram*` axioms above **+** `isUDModOne_of_iteratedDeriv_decay` |
| `Gram.corollary5` | `Corollary5.lean:40` | the 4 axioms above **+** `continuous_ud_criterion`, `IsUDModOne.shift` |

### Notable findings

- **`theorem1` is axiom-free of custom assumptions.** The step-function slot
  is the bundled structure `StepFunction`: any function `ℝ → ℝ` that is
  locally constant off a prescribed *discrete* jump set (`jumpSet`). The
  former axioms are now **theorems about the class** —
  `StepFunction.contDiffAt` and `StepFunction.iteratedDeriv_eq_zero`, proved
  from the `locallyConstant_off` field — and `theorem1` is proved for *every*
  `F : StepFunction`, at the relativized filter `𝓝∞₀[F.jumpSet]` (nontrivial
  by `StepFunction.neBot_regularAtTop`, which uses discreteness of the jump
  set). `Theorem1.lean` contains zero `axiom` declarations.
- **`corollary2` is axiom-free of custom assumptions.** The axiom-light path was
  taken: `theta` is *defined* as `δ − π·φ − π` (not axiomatized), so
  `riemann_vonMangoldt` and `contDiffAt_theta` are **theorems**, and the proof
  reduces `θ^(n)` directly to `iteratedDeriv n δ`. It never touches `S` or
  any step function.
- **`gram` and `gram_spec` are no longer axioms.** The Gram function is
  *defined* (`Function.invFunOn theta (Set.Ici 7)`) and its defining relation
  `θ(t_u) = (u − 1)π` is a *theorem*, proved by the intermediate value theorem
  from the new `theta_tendsto_atTop` (`Corollary2.lean` §5). Theorem 3's
  custom-axiom surface is down from five axioms to three.
- **The dependencies are strictly cumulative** down the chain
  Theorem 3 → Theorem 4 → Corollary 5, with each step adding exactly the
  equidistribution axioms it needs.

## Catalog of custom axioms

### `Theorem1.lean` — the abstract decomposition of `S`

**No custom axioms.** The step-function slot is the `structure StepFunction`:
a function `toFun : ℝ → ℝ`, a jump set `jumpSet : Set ℝ` that is discrete
(`jumpSet_discrete` — every point of it is isolated in it), and a proof
`locallyConstant_off` that the function is locally constant off the jump set.
The regular-point properties `StepFunction.contDiffAt` and
`StepFunction.iteratedDeriv_eq_zero` are theorems derived from
`locallyConstant_off`. The proof of Theorem 1 uses only those two
local-constancy facts and holds for *every* `F : StepFunction`; the motivating
instance is the Riemann ζ zero-counting step `N(γ+0)`, whose jumps are the
ordinates of the nontrivial ζ-zeros — but Theorem 1 does **not** depend on
that interpretation. Discreteness of the jump set enters only through
`StepFunction.neBot_regularAtTop`, which shows the conclusion filter
`𝓝∞₀[F.jumpSet]` is nontrivial (Theorem 1 is never vacuous).

`S` is a `def` (`S F = φ − (1/π)·δ + F`) and `S_eq_φ_sub_δ_add_N` holds by
`rfl`, so the Karatsuba–Korolev decomposition is *not* an axiom here.

### `Theorem3.lean` — the Gram function and its base asymptotics

**`gram` is a `def`, not an axiom.** It is defined as an inverse of `theta`
on `[7, ∞)` via `Function.invFunOn`: `gram u` is a point `t ∈ [7, ∞)` with
`theta t = (u − 1)·π`. The defining relation `gram_spec` (eq. (7) of the
paper) and the range fact `gram_ge_seven` are **theorems**: for
`u ≥ gramThreshold` such a preimage exists by the intermediate value theorem
between `theta 7` and `theta_tendsto_atTop` — the latter a new theorem in
`Corollary2.lean` §5, proved from the concrete `theta = δ − π·φ − π` (the
`φ`-part tends to `+∞`; `δ` is eventually bounded below via `α_part ≥ 0`
and `j = O(t⁻²)` from `iteratedDeriv_j_isO` at order 0).

| Axiom | Signature | Provenance |
|---|---|---|
| `contDiffAt_gram` | `(n) {u} (hu : gramThreshold < u) → ContDiffAt ℝ n gram u` | `C^∞` on the tail, by the inverse function theorem |
| `gram_asymp` | `Iso (gram − L − L·ll/l) (L·ll/l) 𝓝∞`, `L = 2πu/log u` | eq. (8), Lavrik [14, Lemma 2] |
| `gram_deriv_asymp` | `Iso (gram' − A − A·ll/l) (A·ll/l) 𝓝∞`, `A = 2π/log u` | eq. (9), Korolev [10, Lemma 1.1] |

All three remaining axioms are statements about the *defined* `gram`; they
are true under the classical (unformalised) fact that `theta` is strictly
increasing on `[7, ∞)`, which makes `Function.invFunOn theta (Ici 7)` the
genuine monotone inverse there. `gram_asymp` and `gram_deriv_asymp` are
genuine number-theoretic asymptotics not formalizable from the repo's
analytic material alone; they are the `n = 0, 1` baselines that Theorem 3
generalizes. The remaining consequences (`gram_tendsto_atTop`,
`gram_isEquivalent_gramL`, …) are **derived** from these, no new axioms.

### `Theorem4.lean` — the higher-derivative equidistribution criterion

| Axiom | Signature (abridged) | Provenance |
|---|---|---|
| `isUDModOne_of_iteratedDeriv_decay` | `(f) (l) (1 ≤ l) (eventually ContDiffAt) (|f^(l)| eventually antitone) (f^(l) → 0) (u·|f^(l)| → ∞) → IsUDModOne (f ∘ ℕ-cast)` | higher-derivative Kuipers–Niederreiter / Fejér criterion; Kuipers–Niederreiter [11, Thm 2.5], Pańkowski [17, Proof of Thm 1] |

The leading-term asymptotic and the monotonicity / decay / growth hypotheses fed
into this axiom are all **proved** in §2–§3 (Faà di Bruno expansion of
`(·^n) ∘ gram`); only the criterion itself is assumed.

### `UDModOne.lean` — index shift of a UD sequence

| Axiom | Signature | Provenance |
|---|---|---|
| `IsUDModOne.shift` | `{a} (h : IsUDModOne a) → IsUDModOne (fun k => a (k+1))` | shifting the index by one preserves UD mod 1 (Cesàro tail estimate); kept axiomatic to bound refactor scope |

The definitions `IsUDModOne` / `IsCUDModOne` themselves are *honest* (Fourier /
Weyl-exponential Cesàro and time averages), not opaque `Prop` wrappers.

### `Corollary5.lean` — discrete-to-continuous bridge

| Axiom | Signature | Provenance |
|---|---|---|
| `continuous_ud_criterion` | `(f) (IsUDModOne (f∘ℕ)) (IsUDModOne (f(·+1)∘ℕ)) → IsCUDModOne f` | Kuipers–Niederreiter discrete ⇒ continuous UD criterion |

## Reproducing this audit

`GramDerivatives/AxiomAudit.lean` imports the root `GramDerivatives` (which
re-exports all five proof modules) and runs `#print axioms` on each top-level
result. It is a scratch/diagnostic module and is intentionally **not** imported
by the root library; build it explicitly when re-auditing.
