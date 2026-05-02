# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build

```bash
lake build          # compile the project
lake doc            # generate documentation
```

Lean version is pinned in `lean-toolchain` (`leanprover/lean4:v4.30.0-rc2`). The sole dependency is Mathlib at the matching revision, declared in `lakefile.toml`.

## Project Overview

This is a Lean 4 / Mathlib formalization of theorems from the paper *Higher derivatives of the Gram function* (Dundulis, Garunkštis, Laurinčikas, Šimenas, 2026), included in the repo as `Gram_derivatives.pdf`. The project formalizes 5 results about asymptotic behavior of derivatives of the Gram function `gram(u)` (the inverse of the Riemann-Siegel theta function) and their uniform distribution properties.

## Architecture

```
GramDerivatives.lean              # root import — re-exports all modules
GramDerivatives/
  Basic.lean                      # placeholder
  GramDerOverview.lean            # high-level statement of all 5 theorems
  SFuncGrowth.lean                # detailed proof of Theorem 1
  tFunContUnifDistr.lean          # Theorems 4 & 5 (uniform distribution)
```

### Proof strategy

Deep analytic number theory unavailable in Mathlib (Riemann zeta function, Riemann-Siegel theta, Karatsuba-Korolev formula) is introduced as `axiom` declarations. This lets the *logical structure* of the proof compile while isolating gaps. Complex lemmas that are provable in principle but require significant Mathlib bookkeeping use `sorry`.

- **`GramDerOverview.lean`** — states all five results; serves as the spec.
- **`SFuncGrowth.lean`** — implements the paper's proof decomposition for Theorem 1: splits `S(t)` into a smooth main term `φ(t)` and error term `δ(t)`, then bounds the n-th derivative of each. The one fully completed proof here is `iteratedDeriv_log` (iterated derivatives of log by induction).
- **`tFunContUnifDistr.lean`** — formalizes Theorems 4 & 5 using abstract criteria (`UD_of_deriv_pow_decays`, `CUD_of_deriv_pow_decays`); the analytic hypotheses needed to apply them are bundled into an axiom `gramPow_good_for_UD`.

### Lakefile options

```toml
set_option autoImplicit false
set_option maxSynthPendingDepth 3
```
