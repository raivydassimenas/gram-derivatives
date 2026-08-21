# Axiom audit

This file records the **complete axiom dependency** of every top-level result in
the project, as reported by Lean's `#print axioms` command. It is the
authoritative answer to "what does each theorem ultimately rest on?"

Regenerate at any time with the scratch module
[`GramDerivatives/AxiomAudit.lean`](GramDerivatives/AxiomAudit.lean):

```bash
lake build GramDerivatives.AxiomAudit   # prints the axiom list for each theorem
```

Last audited: 2026-08-20, against `lean4:v4.29.1` + matching Mathlib.

## Method

Every proof module builds with **zero `sorry`** and — as of 2026-08-20 —
**zero `axiom` declarations**: the last remaining assumption (the discrete
Fejér / Kuipers–Niederreiter criterion) is now a theorem, proved in
`Fejer.lean`. `#print axioms` walks the full transitive dependency graph, so
the lists below are exhaustive: anything *not* listed is genuinely proved
from Mathlib.

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
| `theorem1` | `Theorem1.lean:3710` | **none** (only the three standard Lean axioms) |
| `Gram.UD.vdc_fundamental_inequality` | `VanDerCorput.lean` §4 | **none** (only the three standard Lean axioms) |
| `Gram.UD.isUDModOne_of_forall_diff` | `VanDerCorput.lean` §5 | **none** (only the three standard Lean axioms) |
| `corollary2` | `Corollary2.lean:209` | **none** (only the three standard Lean axioms) |
| `strictMonoOn_theta` | `Corollary2.lean` §7 | **none** (only the three standard Lean axioms) |
| `gram_theta` | `Theorem3.lean` §1 | **none** (only the three standard Lean axioms) |
| `theorem3` | `Theorem3.lean` | **none** (only the three standard Lean axioms) |
| `Gram.UD.isUDModOne_of_antitone_diff` | `Fejer.lean` §3 | **none** (only the three standard Lean axioms) |
| `Gram.UD.isUDModOne_of_iteratedDeriv_decay` | `Fejer.lean` §6 | **none** (only the three standard Lean axioms) |
| `Gram.Theorem4.theorem4` | `Theorem4.lean` | **none** (only the three standard Lean axioms) |
| `Gram.corollary5` | `Corollary5.lean` | **none** (only the three standard Lean axioms) |

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
  Its one genuinely analytic ingredient — the bound `j^(n)(t) = O(t^(-n-2))`
  on the derivatives of the integral part of `δ` — is *proved*, by the
  differentiation-under-the-integral-sign argument of the paper's §2
  (see "The integral error term (§6)" below); no step of that chain is
  assumed.
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
  foundation.
- **The Fejér criterion is proved, not assumed.** The project's last axiom,
  `isUDModOne_of_iteratedDeriv_decay` (the higher-derivative
  Kuipers–Niederreiter / Fejér criterion), is now a **theorem**
  (`Fejer.lean`): the discrete Fejér theorem (K–N Theorem 2.5) is proved by
  Abel summation against `1/Δf(n)` with the global quadratic bound
  `‖exp(iθ) − 1 − iθ‖ ≤ 3θ²` and the Cesàro lemma; the mean value theorem
  transfers derivative hypotheses to difference sequences (base case
  `l = 1`, K–N Corollary 2.1); induction on the derivative order runs
  through van der Corput's difference theorem (`VanDerCorput.lean`); and an
  intermediate-value sign dichotomy reduces the `|f^(l)|` form to the
  sign-normalized master lemma. Consequently **every result in the project,
  including Theorem 4 and Corollary 5, is axiom-free**.
- **The discrete-to-continuous bridge is proved, not assumed.** Corollary 5
  passes from Theorem 4 to continuous uniform distribution via
  Kuipers–Niederreiter Theorem 9.6(a) (Ryll-Nardzewski), which is a
  **theorem** (`Gram.UD.isCUDModOne_of_forall_shift`, `UDModOne.lean`):
  dominated convergence over `[0, 1]` of the shifted Cesàro averages, unit
  intervals spliced into `∫₀ᴺ`, and a floor-cutoff squeeze for real time.
  Its measurability hypothesis is discharged by `measurable_gram`
  (`Theorem3.lean`: `gram` is monotone above `gramThreshold = θ(7)/π + 1` by
  injectivity of `θ` and constant below it, where `invFunOn` returns its
  default), and its shifted-UD hypothesis by `theorem4_shift`
  (`Theorem4.lean` §8: the four Fejér hypotheses transported along
  `u ↦ u + t`). So Corollary 5 depends on
  **exactly the same (empty) axiom set as Theorem 4**: nothing beyond Lean's
  standard foundation.

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

#### The integral error term (§6): differentiation under the integral sign

The only genuinely analytic input of `Theorem1.lean` is the bound
`j^(n)(t) = O(t^(-n-2))` on the derivatives of

```
j(t) = ∫₀^∞ ρ(u) / ((u + 1/4)² + (t/2)²) du,    ρ(u) = 1/2 − {u},
```

and it is derived in full, following the proof of Theorem 1 in §2 of the
paper step for step. **No stage of the chain is axiomatized.**

1. **Differentiation under the integral sign** (§2.5). `contDiffAt_j` —
   formerly an axiom — is a **theorem**. A joint induction (`contDiffOn_jK`,
   `iteratedDeriv_j_eqOn_jK`) shows `iteratedDeriv n j = jK n` on `(0, ∞)`,
   where `jK n t = ∫₀^∞ ρ(u)·∂ₜⁿ kernel(u,t) du`; each differentiation step
   (`hasDerivAt_jK`) is justified by Mathlib's
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le` against the dominator
   `C_k·(u+1/4)^(−(k+2))` (`exists_bound_iteratedDeriv_kernel`) — the paper's
   "integrable majorant uniform in `t` on `[T, ∞)`" (Rudin pp. 180–182).

2. **Integration by parts.** With `σ(u) = {u}(1−{u})/2` — the continuous
   antiderivative of `ρ` that vanishes at every integer and satisfies
   `0 ≤ σ ≤ 1/8` — per-unit-interval IBP (the boundary terms vanish at the
   integers, `σ_natCast_eq_zero`) plus countable additivity over
   `Ici 0 = ⋃ₖ [k, k+1)` give `jK_eq_sigma_integral`:

   ```
   jK n t = −∫₀^∞ σ(u) · ∂ᵤ ∂ₜⁿ kernel(u,t) du,
   ```

   i.e. the paper's `j(t) = 2∫₀^∞ σ(u)(u+1/4)/((u+1/4)²+(t/2)²)² du`
   differentiated `n` times.

3. **The paper's expansion of the `n`-th derivative.** Writing `a = 4u+1`,
   `mixedDerivExpr_eq_quadInv` rewrites the integrand as
   `−128·a·∂ₜⁿ quadInv a t` with `quadInv a t = ((a²+4t²)²)⁻¹`, and
   `iteratedDeriv_quadInv` expands

   ```
   ∂ₜⁿ (a² + 4t²)⁻² = ∑_{r ≤ n} dsC n r · t^(2r−n) / (a² + 4t²)^(r+2)
   ```

   by induction through the product rule (`hasDerivAt_dsTerm` for a single
   term, `dsC_sum_step` for the re-indexing that *is* the two-term recursion
   `dsC (n+1) r = dsC n r·(2r−n) − 8(r+1)·dsC n (r−1)`). Exponents are
   `ℤ`-valued `zpow`, so no truncated subtraction appears and only
   `dsC n r = 0` for `r > n` (`dsC_eq_zero_of_lt`) is needed; the paper's
   lower cutoff `r ≥ ⌈n/2⌉` is not required, since the terms it excludes
   carry a negative power of `t` and are already smaller than `t^(−n−2)`.

4. **The paper's substitution.** `integral_quadPow` evaluates each
   `u`-integral in closed form,

   ```
   ∫₀^∞ (4u+1) / ((4u+1)² + 4t²)^(r+2) du = 1 / (8(r+1)(1 + 4t²)^(r+1)),
   ```

   through the explicit antiderivative `quadAnti` and Mathlib's improper FTC
   (`integral_Ioi_of_hasDerivAt_of_nonneg'`, whose companion
   `integrableOn_Ioi_deriv_of_nonneg'` also supplies integrability). This is
   the paper's `v = (4u+1)² + 4t²`, `dv = 8(4u+1) du`, carried out without a
   change-of-variables lemma.

5. **Assembly.** `norm_sigma_mixedDerivExpr_le` bounds the integrand by
   `jMajorant` using `0 ≤ σ ≤ 1/8`; `integral_jMajorant_le` integrates it with
   step 4 and bounds each term by `2|dsC n r|·t^(−n−2)` using
   `1 + 4t² ≥ t²` (the paper keeps the sharper `1 + 4t² ≥ 4t²`, which is not
   needed for the conclusion). Summing over `r` gives
   `sigma_mixedDerivExpr_isO`, hence `jK_isO` and `iteratedDeriv_j_isO`. The
   Leibniz rule applied to `−(t/2)·j(t)` (`iteratedDeriv_tj_isO`) combines
   with the algebraic part (`iteratedDeriv_α_part_isO`) to give
   `iteratedDeriv_δ_isO`: `δ^(n)(t) = O(t^(−n−1))` for `n ≥ 1`.

§7a re-runs the same σ-IBP machinery with *explicit* constants — improper-FTC
evaluations of `∫_{u≥0} ∂ᵤ∂ₜⁿ kernel` at orders `0` and `1`, together with the
sign lemmas `mixedDerivExpr_zero_nonpos` / `mixedDerivExpr_one_nonneg` — to
obtain the pointwise bounds `|j(t)| ≤ 1/(2t²)` and `|δ'(t)| ≤ 1/t²` valid for
*every* `t > 0`. These are what `strictMonoOn_theta` (`Corollary2.lean` §7)
consumes, where an eventual `IsBigO` bound would say nothing about any
concrete `t`.

### `Theorem3.lean` — the Gram function and its base asymptotics

**`gram` is a `def`, not an axiom.** It is defined as an inverse of `theta`
on `[7, ∞)` via `Function.invFunOn`: `gram u` is a point `t ∈ [7, ∞)` with
`theta t = (u − 1)·π`. The defining relation `gram_spec` (eq. (7) of the
paper) and the range fact `gram_ge_seven` are **theorems**: for
`u ≥ gramThreshold` such a preimage exists by the intermediate value theorem
between `theta 7` and `theta_tendsto_atTop` — the latter a new theorem in
`Corollary2.lean` §5, proved from the concrete `theta = δ − π·φ − π` (the
`φ`-part tends to `+∞`; `δ` is eventually bounded below via `α_part ≥ 0`
and `j = O(t⁻²)` from `iteratedDeriv_j_isO` at order 0). The threshold is
`gramThreshold := θ(7)/π + 1`, i.e. exactly the condition `θ(7) ≤ (u − 1)π`,
so it is the largest half-line on which `gram` inverts `θ`.

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

**No custom axioms** (formerly one: `isUDModOne_of_iteratedDeriv_decay`, the
higher-derivative Kuipers–Niederreiter / Fejér criterion — K–N [11, Thm 2.5],
Pańkowski [17, Proof of Thm 1]). The criterion is now a **theorem**
delegating to `Gram.UD.isUDModOne_of_iteratedDeriv_decay` (`Fejer.lean`, see
below). The leading-term asymptotic and the monotonicity / decay / growth
hypotheses fed into it are all proved in §2–§3 (Faà di Bruno expansion of
`(·^n) ∘ gram`).

### `Fejer.lean` — Fejér's theorem and the higher-derivative criterion

**No custom axioms.** Proves the criterion consumed by `Theorem4.lean`,
following Kuipers–Niederreiter Chapter 1:

- `IsUDModOne.unshift` / `isUDModOne_of_shift` — u.d. of a tail
  `(a(n+m))ₙ` implies u.d. of `(a(n))ₙ` (telescoping boundary term `≤ 2/N`),
  so finitely many initial terms can be discarded.
- `norm_exp_mul_I_sub_one_sub_le` — the global quadratic Taylor bound
  `‖exp(iθ) − 1 − iθ‖ ≤ 3θ²` (Mathlib's `norm_exp_sub_one_sub_id_le` for
  `|θ| ≤ 1`, triangle inequality otherwise).
- `isUDModOne_of_antitone_diff` — **K–N Theorem 2.5** (discrete Fejér
  theorem, positive antitone differences): Abel summation of the Weyl
  exponentials against `1/d n` telescopes to the bound
  `2π|k|·‖∑_{n<N} e n‖ ≤ 2/d N + 12π²k²·∑_{n<N} d n`; after division by `N`
  the first term vanishes by `N·d N → ∞` and the second by the Cesàro lemma
  (`Filter.Tendsto.cesaro`).
- `isUDModOne_of_iteratedDeriv_pos_antitone` — the sign-normalized master
  lemma, by induction on the derivative order `l ≥ 1`
  (`Nat.le_induction`). Base case `l = 1` is **K–N Corollary 2.1** (Fejér's
  theorem): the mean value theorem on unit intervals transfers the
  hypotheses on `f'` to the difference sequence of `(f(n + n₀))ₙ`. The
  inductive step feeds the shifted differences `g(u) = f(u+h) − f(u)`
  (which satisfy the level-`l` hypotheses, again by the mean value theorem
  applied to `iteratedDeriv l f`) to van der Corput's difference theorem
  `isUDModOne_of_forall_diff`.
- `isUDModOne_of_iteratedDeriv_decay` — the sign-free form: since
  `u·|f^(l)(u)| → ∞` forces eventual nonvanishing and `f^(l)` is continuous
  on a tail, the intermediate value theorem gives an eventually constant
  sign; the master lemma applies to `f` or `−f`.

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

**No custom axioms.** Formalizes Kuipers–Niederreiter Chapter 1, §3; consumed
by `Fejer.lean` (inductive step of the master lemma):

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
adding no assumptions beyond those of Theorem 4 — that is, none at all.

## Reproducing this audit

`GramDerivatives/AxiomAudit.lean` imports the root `GramDerivatives` (which
re-exports all five proof modules) and runs `#print axioms` on each top-level
result. It is a scratch/diagnostic module and is intentionally **not** imported
by the root library; build it explicitly when re-auditing.
