# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build

```bash
lake build          # compile the project
lake doc            # generate documentation
```

Lean version is pinned in `lean-toolchain` (`leanprover/lean4:v4.30.0-rc2`). The sole dependency is Mathlib at the matching revision, declared in `lakefile.toml`.

## Project Overview

Lean 4 / Mathlib formalization of theorems from the paper *Higher derivatives of the Gram function* (Dundulis, Garunkštis, Laurinčikas, Šimėnas, 2026), included in the repo as `Gram_derivatives.pdf`. The project formalizes 5 results about asymptotic behavior of derivatives of the Gram function `gram(u)` (the inverse of the Riemann–Siegel theta function `θ`) and their uniform distribution properties.

## Architecture

```
GramDerivatives.lean              # root — currently only imports Basic
GramDerivatives/
  Basic.lean                      # placeholder
  GramDerOverview.lean            # high-level statement of all 5 results (spec)
  Theorem1.lean                   # detailed proof of Theorem 1
  Corollary5.lean                 # Theorem 4 + Corollary 5 (uniform distribution)
```

Note: the root `GramDerivatives.lean` does **not** re-export the proof modules — they must be opened or built directly (e.g. `lake build GramDerivatives.Theorem1`).

### Proof strategy

Deep analytic number theory unavailable in Mathlib (Riemann zeta, Riemann–Siegel theta, Karatsuba–Korolev formula, Kuipers–Niederreiter UD criteria) is introduced as `axiom` declarations, each marked `-- ASSUMPTION` in `Theorem1.lean`. This lets the *logical structure* of each proof compile while isolating the gaps. `Theorem1.lean` itself builds with **zero `sorry`** — every lemma that is provable in principle (including `iteratedDeriv_α_part_isO`, `iteratedDeriv_j_isO`, `iteratedDeriv_tj_isO`, and `δ_eq`) is fully discharged; only the `-- ASSUMPTION` axioms remain.

- **`GramDerOverview.lean`** — states all five results (`Theorem1`, `Corollary2`, `Theorem3`, `Theorem4`, `Corollary5`) inside `namespace GramPaper`; serves as the spec. UD/CUD are stubbed via lightweight `Prop` wrappers (`UDMod1`, `CUDMod1`) and the analytic input is bundled into one axiom `gramPow_good_for_UD`.
- **`Theorem1.lean`** — implements the paper's decomposition for Theorem 1: splits `S(t)` into a smooth main term `φ(t)` and an error term `δ(t)`, then bounds the n-th derivative of each. The fully completed proof here is `iteratedDeriv_log` (iterated derivatives of `log` by induction); `iteratedDeriv_φ` builds on it. The final theorem is `theorem1` (§8).
- **`Corollary5.lean`** — minimal-imports formalization (only `Mathlib.Data.Real.Basic`) inside `namespace Gram`. Uses opaque `Prop` wrappers `UDSeqModOne` / `UDContModOne`, takes Theorem 4 as an axiom, and derives `corollary5` via an abstract `continuous_ud_criterion` plus `UDSeqModOne_shift`. This is intentionally separate from the heavier `GramDerOverview.lean` formulation.

## Working on `Theorem1.lean`

`Theorem1.lean` is intentionally **independent of the Karatsuba–Korolev results**. Treat its setup abstractly:

- **`N_step` may be any piecewise-constant function** `ℝ → ℝ`. It need *not* be the zero-counting step function `N(γ+0)` tied to the ordinates of zeros of ζ. The only properties the proof uses are that it is locally constant on `(0, ∞)` — so `contDiffAt_N_step` holds and `N_step_iteratedDeriv_eq_zero` makes every `n ≥ 1` derivative vanish. Keep these axioms general; do not specialize `N_step` to ζ-zero ordinates.
- **`S` may be any function of the form** `S(t) = φ(t) − (1/π)·δ(t) + N_step(t)`. In `Theorem1.lean`, `S` *is* `def`-ined by exactly that formula, and `S_eq_φ_sub_δ_add_N` is a `rfl` theorem — not an imported analytic fact about `(1/π)·arg ζ(1/2 + it)`.
- **Do not change the definitions of `φ` and `δ`.** They stay exactly as in §1: `φ` the smooth main term and `δ = α_part − (t/2)·j` the error term. The leading-term asymptotic of Theorem 1 comes entirely from `φ`, and `δ^(n)(t) = O(t^(−n−1))` from `δ`.

Consequence: Theorem 1's proof in this file rests only on elementary calculus plus the abstract decomposition above — it does **not** depend on the Karatsuba–Korolev representation, the Riemann ζ function, or properties of its zeros. Docstrings and comments that still attribute `S`, `N_step`, or `S_eq_φ_sub_δ_add_N` to Karatsuba–Korolev describe the *original motivation* only; the formal content is the general statement.

## Assumed analytic facts

When working on proofs in this repo, treat the following as established results that do not need to be re-derived or questioned — introduce them as `axiom` declarations if not already present:

**Decomposition of `S`** — `S(t)` is defined as
```
S(t) = φ(t) − (1/π) δ(t) + N_step(t)
```
In `Theorem1.lean`, `S` is a `def` and `S_eq_φ_sub_δ_add_N` is a `rfl` theorem, not an imported number-theoretic fact. `S` may be any function of this form; see "Working on `Theorem1.lean`" above. The Karatsuba–Korolev representation is the motivation for this decomposition but is not needed by the proof.

**Analytic properties of `S`** — `S : ℝ → ℝ` is smooth on `(0, ∞)` away from a discrete set (the imaginary parts of zeros of ζ); at each interior point of a zero-free interval it is `ContDiffAt ℝ ⊤`. Axiom name: `contDiffAt_S` (or the per-piece variants already in `Theorem1.lean`).

**Analytic properties of `φ`** — the main term
```
φ(t) = −t/(2π) · log(t/(2π)) + t/(2π) − 7/8
```
is `C^∞` on `(0, ∞)`. Its n-th iterated derivative equals `(−1)^(n−1) · (n−2)! / (2π) · t^(1−n)` for `n ≥ 2`. Proved as `iteratedDeriv_φ` in `Theorem1.lean`; treat as established.

**Analytic properties of `δ`** — the error term
```
δ(t) = t/4 · log(1 + 1/(4t²)) + 1/4 · arctan(1/(2t)) − t/2 · j(t)
```
(where `j(t) = ∫₀^∞ ρ(u)/((u+1/4)²+(t/2)²) du` and `ρ(u) = 1/2 − {u}`) is `ContDiff ℝ ⊤` on `(0, ∞)`. Its n-th derivative satisfies `δ^(n)(t) = O(t^(−n−1))` for all `n ≥ 1`. Axiom name: `contDiffAt_δ`; the bound `iteratedDeriv_δ_isO` is proved via `iteratedDeriv_α_part_isO` + `iteratedDeriv_tj_isO`.

**Analytic properties of `N_step`** — `N_step : ℝ → ℝ` may be any piecewise-constant (locally constant) function on `(0, ∞)`; it need not be the ζ-zero-counting step function. Being locally constant, its n-th iterated derivative (`n ≥ 1`) vanishes. Axiom name: `N_step_iteratedDeriv_eq_zero` (already in `Theorem1.lean`).

### Lakefile options

```toml
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
```
