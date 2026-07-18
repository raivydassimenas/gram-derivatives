# Axiom audit

This file records the **complete axiom dependency** of every top-level result in
the project, as reported by Lean's `#print axioms` command. It is the
authoritative answer to "what does each theorem ultimately rest on?"

Regenerate at any time with the scratch module
[`GramDerivatives/AxiomAudit.lean`](GramDerivatives/AxiomAudit.lean):

```bash
lake build GramDerivatives.AxiomAudit   # prints the axiom list for each theorem
```

Last audited: 2026-07-18, against `lean4:v4.30.0-rc2` + matching Mathlib.

## Method

Every proof module builds with **zero `sorry`**. The deep analytic-number-theory
input that Mathlib lacks (Riemann ζ, the Riemann–Siegel θ, Karatsuba–Korolev,
Kuipers–Niederreiter equidistribution) is
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
| `theorem1` | `Theorem1.lean:3754` | **none** (only the three standard Lean axioms) |
| `Gram.UD.vdc_fundamental_inequality` | `VanDerCorput.lean` §4 | **none** (only the three standard Lean axioms) |
| `Gram.UD.isUDModOne_of_forall_diff` | `VanDerCorput.lean` §5 | **none** (only the three standard Lean axioms) |
| `corollary2` | `Corollary2.lean:209` | **none** (only the three standard Lean axioms) |
| `strictMonoOn_theta` | `Corollary2.lean` §7 | **none** (only the three standard Lean axioms) |
| `gram_theta` | `Theorem3.lean` §1 | **none** (only the three standard Lean axioms) |
| `theorem3` | `Theorem3.lean` | **none** (only the three standard Lean axioms) |
| `Gram.Theorem4.theorem4` | `Theorem4.lean:1925` | `isUDModOne_of_iteratedDeriv_decay` |
| `Gram.corollary5` | `Corollary5.lean:38` | `isUDModOne_of_iteratedDeriv_decay` (the same one — no further axioms) |

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
  from the new `theta_tendsto_atTop` (`Corollary2.lean` §5).
- **The Lavrik/Korolev base asymptotics (8) and (9) are no longer axioms.**
  `gram_asymp` and `gram_deriv_asymp` are *derived* (`Theorem3.lean` §1.7a,
  following the blueprint `Proof_Gram_fun_der.tex`) from `gram_spec` plus the
  leading-order behaviour of `θ` and `θ'` (`theta_eq_main_add_δ`,
  `theta_deriv_asymp` in `Corollary2.lean` §6, resting on the fully proved
  `δ = O(1/t)` and `δ' = O(1/t²)` bounds of `Theorem1.lean`).
- **`θ` is provably strictly increasing on `[7, ∞)`.** `strictMonoOn_theta`
  (`Corollary2.lean` §7) is an axiom-free theorem, resting on the explicit
  pointwise bound `|δ'(t)| ≤ 1/t²` (`abs_deriv_δ_le`, `Theorem1.lean` §7a).
  Consequently `gram` is a genuine left inverse of `theta` (`gram_theta`,
  axiom-free).
- **`theorem3` is axiom-free of custom assumptions.** The last analytic axiom,
  `contDiffAt_gram`, is now a **theorem**, by Mathlib's C^m inverse function
  theorem (`ContDiffAt.to_localInverse`) applied to `theta` at `gram u`
  (nonvanishing derivative from `deriv_theta_pos`), with the local inverse
  identified with `gram` near `u` via `injOn_theta`. The whole analytic chain
  Theorem 1 → Corollary 2 → Theorem 3 rests only on Lean's standard
  foundation; the equidistribution results (Theorem 4, Corollary 5) retain
  exactly **one** Kuipers–Niederreiter-type axiom, the discrete Fejér
  criterion `isUDModOne_of_iteratedDeriv_decay`.
- **The discrete-to-continuous bridge is proved, not assumed.** Corollary 5
  passes from Theorem 4 to continuous uniform distribution via
  Kuipers–Niederreiter Theorem 9.6(a) (Ryll-Nardzewski), which is a
  **theorem** (`Gram.UD.isCUDModOne_of_forall_shift`, `UDModOne.lean`):
  dominated convergence over `[0, 1]` of the shifted Cesàro averages, unit
  intervals spliced into `∫₀ᴺ`, and a floor-cutoff squeeze for real time.
  Its measurability hypothesis is discharged by `measurable_gram`
  (`Theorem3.lean`: `gram` is monotone above `θ(7)/π + 1` by injectivity of
  `θ` and constant below it, where `invFunOn` returns its default), and its
  shifted-UD hypothesis by `theorem4_shift` (`Theorem4.lean` §8: the four
  Fejér hypotheses transported along `u ↦ u + t`). So Corollary 5 depends on
  **the same single axiom as Theorem 4** and nothing more.

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

**No custom axioms.** The strict monotonicity of `theta` on `[7, ∞)` is
**formal** (`strictMonoOn_theta`, `Corollary2.lean` §7, axiom-free): `θ'(t) =
log(t/(2π))/2 + δ'(t) > 0` for `t ≥ 7`, using the explicit pointwise bound
`|δ'(t)| ≤ 1/t²` (`abs_deriv_δ_le`, `Theorem1.lean` §7a — derived from the
σ-integration-by-parts machinery with explicit constants, not merely the
asymptotic `iteratedDeriv_δ_isO`), the elementary `log x ≥ 1 − 1/x`, and
`π < 3.15`. Injectivity (`injOn_theta`) makes the `invFunOn`-defined `gram` a
genuine left inverse: `gram (θ(t)/π + 1) = t` for `t ≥ 7` (`gram_theta`).

`contDiffAt_gram` — formerly the project's last analytic axiom — is a
**theorem**: at `u > gramThreshold` the point `t₀ = gram u` satisfies
`t₀ > 7` strictly (`θ(t₀) = (u−1)π > θ(7)`), so Mathlib's C^m inverse
function theorem (`ContDiffAt.to_localInverse`, with the nonvanishing
derivative packaged by `HasDerivAt.hasFDerivAt_equiv` from
`deriv_theta_pos`) yields a `C^m` local inverse of `θ` at `θ(t₀)`; near `u`
it agrees with `gram` (both give preimages of `(u'−1)π` in `[7, ∞)`, equal
by `injOn_theta`), and smoothness transfers along the eventual equality.

The Lavrik/Korolev baselines `gram_asymp` (eq. (8), [14, Lemma 2]) and
`gram_deriv_asymp` (eq. (9), [10, Lemma 1.1]) — formerly axioms — are now
**theorems** (§1.7a), derived from the implicit equation `θ(gram u) = (u−1)π`:
`gram u → +∞` unconditionally (θ is bounded on compacts while `(u−1)π → ∞`),
the star equation `gram u·(log(gram u) − log(2π) − 1) = 2πu + O(1)` from the
closed form of `θ`, a logarithmic-scale sandwich
`log(gram u) = log u − log log u + O(1)`, and a shared inversion lemma
`1/D = (1/log u)·(1 + (1+o(1))·log log u/log u)` applied to the denominators
of (8) and (9); for (9) the chain rule identity `θ'(gram u)·gram'(u) = π`
converts the problem into the same inversion. All downstream consequences
(`gram_tendsto_atTop`, `gram_isEquivalent_gramL`, …) follow as before.

### `Theorem4.lean` — the higher-derivative equidistribution criterion

| Axiom | Signature (abridged) | Provenance |
|---|---|---|
| `isUDModOne_of_iteratedDeriv_decay` | `(f) (l) (1 ≤ l) (eventually ContDiffAt) (|f^(l)| eventually antitone) (f^(l) → 0) (u·|f^(l)| → ∞) → IsUDModOne (f ∘ ℕ-cast)` | higher-derivative Kuipers–Niederreiter / Fejér criterion; Kuipers–Niederreiter [11, Thm 2.5], Pańkowski [17, Proof of Thm 1] |

The leading-term asymptotic and the monotonicity / decay / growth hypotheses fed
into this axiom are all **proved** in §2–§3 (Faà di Bruno expansion of
`(·^n) ∘ gram`); only the criterion itself is assumed.

### `UDModOne.lean` — definitions, index shift, and the K–N 9.6(a) bridge

**No custom axioms.** The definitions `IsUDModOne` / `IsCUDModOne` are *honest*
(Fourier / Weyl-exponential Cesàro and time averages), not opaque `Prop`
wrappers, and the file's two lemmas are **theorems**:

- `IsUDModOne.shift` — formerly an axiom: the shifted Cesàro average
  telescopes against the unshifted one up to the boundary term
  `(1/N)·(e(N) − e(0))`, which has norm at most `2/N` (each Weyl exponential
  lies on the unit circle) and vanishes by `squeeze_zero_norm`.
- `isCUDModOne_of_forall_shift` — Kuipers–Niederreiter Theorem 9.6(a)
  (Ryll-Nardzewski): if `f` is measurable and every shifted integer sample
  `(f(k + t))ₖ`, `t ∈ [0, 1]`, is UD mod 1, then `f` is CUD mod 1. Proof:
  for each nonzero frequency, splice `∫₀ᴺ` of the Weyl exponential into unit
  intervals to identify the integer-cutoff time average with the
  `[0,1]`-integral of the shifted Cesàro averages; those tend to `0`
  pointwise with uniform bound `1`, so dominated convergence kills the
  integer averages; a floor cutoff (`N = ⌊T⌋₊`, leftover of norm `≤ 1`)
  squeezes the real-time average. (The classical statement needs only
  *almost all* `t`; the all-`t` form proved here is what the application
  supplies.)

### `VanDerCorput.lean` — van der Corput's inequality and difference theorem

**No custom axioms.** New module (not yet consumed by the main chain) working
toward a proof of the remaining Fejér axiom, formalizing Kuipers–Niederreiter
Chapter 1, §3:

- `vdc_fundamental_inequality` — K–N Lemma 3.1 (with the crude multiplicity
  bound `H` per correlation gap): pad the sequence by zeros, write `H·∑uₙ` as
  the sum of all length-`H` sliding-window sums, apply Cauchy–Schwarz
  (`sq_sum_le_card_mul_sum_sq`), and expand the window squares into a
  diagonal term (`H·∑‖uₙ‖²`) plus off-diagonal window cross-correlations,
  each of which *equals* a plain gap-`δ` correlation sum of the original
  sequence (`corr_eq`) and is counted at most `2H` times per gap.
- `isUDModOne_of_forall_diff` — K–N Theorem 3.1 (van der Corput's difference
  theorem): if every difference sequence `(a(n+h) − a(n))ₙ`, `h ≥ 1`, is UD
  mod 1, so is `(a(n))ₙ`. Weyl criterion: the correlation sums of the
  unimodular exponentials `e(n) = exp(2πik·aₙ)` are the Weyl sums of the
  difference sequences, hence `o(N)`; the fundamental inequality then gives
  `limsup ‖(1/N)∑e(n)‖² ≤ 4/H` for every `H`, packaged as an explicit
  `ε`/`H`/`N₀` argument.

Also proved here: `IsUDModOne.neg` and `isUDModOne_congr_eventually`
(stability of UD mod 1 under negation and finite modification).

### `Corollary5.lean` — discrete-to-continuous bridge

**No custom axioms** (formerly the axiom `continuous_ud_criterion`, now
deleted). `corollary5` applies `isCUDModOne_of_forall_shift` with
measurability from `measurable_gramPow` and shifted UD from `theorem4_shift`,
adding no assumptions beyond the single Fejér axiom already counted for
Theorem 4.

## Reproducing this audit

`GramDerivatives/AxiomAudit.lean` imports the root `GramDerivatives` (which
re-exports all five proof modules) and runs `#print axioms` on each top-level
result. It is a scratch/diagnostic module and is intentionally **not** imported
by the root library; build it explicitly when re-auditing.
