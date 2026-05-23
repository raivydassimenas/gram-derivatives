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
  Corollary2.lean                 # detailed proof of Corollary 2 (θ^(n) asymptotic)
  Corollary5.lean                 # Theorem 4 + Corollary 5 (uniform distribution)
```

Note: the root `GramDerivatives.lean` does **not** re-export the proof modules — they must be opened or built directly (e.g. `lake build GramDerivatives.Theorem1`).

### Proof strategy

Deep analytic number theory unavailable in Mathlib (Riemann zeta, Riemann–Siegel theta, Karatsuba–Korolev formula, Kuipers–Niederreiter UD criteria) is introduced as `axiom` declarations, each marked `-- ASSUMPTION` in `Theorem1.lean`. This lets the *logical structure* of each proof compile while isolating the gaps. `Theorem1.lean` itself builds with **zero `sorry`** — every lemma that is provable in principle (including `iteratedDeriv_α_part_isO`, `iteratedDeriv_j_isO`, `iteratedDeriv_tj_isO`, and `δ_eq`) is fully discharged; only the `-- ASSUMPTION` axioms remain.

- **`GramDerOverview.lean`** — states all five results (`Theorem1`, `Corollary2`, `Theorem3`, `Theorem4`, `Corollary5`) inside `namespace GramPaper`; serves as the spec. UD/CUD are stubbed via lightweight `Prop` wrappers (`UDMod1`, `CUDMod1`) and the analytic input is bundled into one axiom `gramPow_good_for_UD`.
- **`Theorem1.lean`** — implements the paper's decomposition for Theorem 1: splits `S(t)` into a smooth main term `φ(t)` and an error term `δ(t)`, then bounds the n-th derivative of each. The fully completed proof here is `iteratedDeriv_log` (iterated derivatives of `log` by induction); `iteratedDeriv_φ` builds on it. The final theorem is `theorem1` (§8).
- **`Corollary2.lean`** — derives the asymptotic for the n-th derivative of the Riemann–Siegel theta function `θ` from `theorem1` in `Theorem1.lean`. Imports `GramDerivatives.Theorem1` and reuses the decomposition `S = φ − (1/π)·δ + N_step` together with the Riemann–von Mangoldt / Karatsuba–Korolev relation `N(t) = (1/π)·θ(t) + 1 + S(t)`. See "Working on `Corollary2.lean`" below.
- **`Corollary5.lean`** — minimal-imports formalization (only `Mathlib.Data.Real.Basic`) inside `namespace Gram`. Uses opaque `Prop` wrappers `UDSeqModOne` / `UDContModOne`, takes Theorem 4 as an axiom, and derives `corollary5` via an abstract `continuous_ud_criterion` plus `UDSeqModOne_shift`. This is intentionally separate from the heavier `GramDerOverview.lean` formulation.

## Working on `Theorem1.lean`

`Theorem1.lean` is intentionally **independent of the Karatsuba–Korolev results**. Treat its setup abstractly:

- **`N_step` may be any piecewise-constant function** `ℝ → ℝ`. It need *not* be the zero-counting step function `N(γ+0)` tied to the ordinates of zeros of ζ. The only properties the proof uses are that it is locally constant on `(0, ∞)` — so `contDiffAt_N_step` holds and `N_step_iteratedDeriv_eq_zero` makes every `n ≥ 1` derivative vanish. Keep these axioms general; do not specialize `N_step` to ζ-zero ordinates.
- **`S` may be any function of the form** `S(t) = φ(t) − (1/π)·δ(t) + N_step(t)`. In `Theorem1.lean`, `S` *is* `def`-ined by exactly that formula, and `S_eq_φ_sub_δ_add_N` is a `rfl` theorem — not an imported analytic fact about `(1/π)·arg ζ(1/2 + it)`.
- **Do not change the definitions of `φ` and `δ`.** They stay exactly as in §1: `φ` the smooth main term and `δ = α_part − (t/2)·j` the error term. The leading-term asymptotic of Theorem 1 comes entirely from `φ`, and `δ^(n)(t) = O(t^(−n−1))` from `δ`.

Consequence: Theorem 1's proof in this file rests only on elementary calculus plus the abstract decomposition above — it does **not** depend on the Karatsuba–Korolev representation, the Riemann ζ function, or properties of its zeros. Docstrings and comments that still attribute `S`, `N_step`, or `S_eq_φ_sub_δ_add_N` to Karatsuba–Korolev describe the *original motivation* only; the formal content is the general statement.

## Working on `Corollary2.lean`

`Corollary2.lean` is where the abstract setup of `Theorem1.lean` is **specialized to the analytic-number-theory setting**. Unlike `Theorem1.lean`, this file genuinely depends on the Riemann–Siegel theta function `θ`, on the Riemann zeta zero-counting function `N`, and on the Karatsuba–Korolev / Riemann–von Mangoldt identity that relates them to `S`.

### Goal

Formalize **Corollary 2** of the paper:

```
For n ≥ 2, away from discontinuities,
  θ^(n)(t) = (-1)^n · (n-2)! / 2 · t^(1-n) + O(t^(-n-1)),  t → +∞.
```

### Interpretation of imported names

When importing `GramDerivatives.Theorem1`, fix the following analytic interpretation of its abstract symbols. These are *intent* commitments that drive how the new axioms in `Corollary2.lean` are stated; they do **not** require editing `Theorem1.lean`.

- **`S`** is `(1/π) · arg ζ(1/2 + it)`, where the argument is taken along the continuous branch from `s = 2` to `s = 2 + it` to `s = 1/2 + it` (and averaged at zeros). This is the function `S(t)` of the paper.
- **`N_step`** is `N(γ+0)`, the right-continuous Riemann ζ zero-counting function: the number of nontrivial zeros `ρ = β + iγ` with `0 < γ ≤ t`, `0 ≤ β ≤ 1`. It is integer-valued and piecewise constant on `(0, ∞)`, with jumps exactly at the ordinates of ζ-zeros — which justifies `N_step_iteratedDeriv_eq_zero` at every regular point. (The `True` placeholder slot in that axiom is conceptually a "not at a ζ-zero ordinate" predicate.)
- **`θ`** is the Riemann–Siegel theta function: the continuous branch of `arg(π^(-s/2) Γ(s/2))` along the segment from `s = 1/2` to `s = 1/2 + it`. It is `C^∞` on `(0, ∞)` (no exceptional points) and monotonically increasing for `t ≥ 7`.

### Karatsuba–Korolev input

The decomposition `S = φ − (1/π)·δ + N_step` from `Theorem1.lean` *is* the Karatsuba–Korolev expansion (equation (2) of the paper, [6, Proof of Theorem 2]) under the interpretation above. In `Theorem1.lean` it holds by `rfl`, but morally it is the Karatsuba–Korolev result.

The **second** Karatsuba–Korolev input — the one that lets us pass from `S` to `θ` — is the **Riemann–von Mangoldt formula** (equation (1) of the paper):

```
N(t) = (1/π) · θ(t) + 1 + S(t).
```

Solving for `θ`:

```
θ(t) = π · (N_step(t) − 1 − S(t)).
```

Equivalently, substituting the Karatsuba–Korolev expansion of `S`:

```
θ(t) = δ(t) − π · φ(t) − π,
```

which — note — does **not** involve `N_step` at all. Either form is acceptable; the second is preferable because it makes `θ` smooth on all of `(0, ∞)` without invoking the locally-constant axiom for `N_step`.

### Proof sketch

Once `θ` is introduced, the proof of Corollary 2 is a one-step reduction to `theorem1`:

1. Pointwise on `(0, ∞)` (away from ζ-zero ordinates if working with `N_step`),
   `θ(t) = π · (N_step(t) − 1 − S(t))`.
2. Apply `iteratedDeriv` `n` times. For `n ≥ 1`:
   - `iteratedDeriv n (1 : ℝ → ℝ) = 0` (constant), and
   - `iteratedDeriv n N_step t = 0` by `N_step_iteratedDeriv_eq_zero`.
   Hence `θ^(n)(t) = −π · S^(n)(t)`.
3. Substitute `theorem1`: for `n ≥ 2`,
   ```
   S^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n) + O(t^(-n-1)),
   ```
   so
   ```
   θ^(n)(t) = −π · (-1)^(n-1) · (n-2)! / (2π) · t^(1-n) + O(t^(-n-1))
            = (-1)^n · (n-2)! / 2 · t^(1-n) + O(t^(-n-1)).
   ```
4. Repackage as an `IsO` statement using the `IsO`/`𝓝∞` notation from `Theorem1.lean §0`.

### Axiom budget for `Corollary2.lean`

Introduce the following new axioms (each tagged `-- ASSUMPTION` and given a docstring identifying its provenance):

- `axiom theta : ℝ → ℝ` — the Riemann–Siegel theta function.
- `axiom contDiffAt_theta (n : ℕ) {s : ℝ} (hs : 0 < s) : ContDiffAt ℝ n theta s` — `θ` is `C^∞` on `(0, ∞)`.
- `axiom riemann_vonMangoldt (t : ℝ) (ht : 0 < t) : N_step t = (1 / Real.pi) * theta t + 1 + S t` — equation (1) of the paper; the Karatsuba–Korolev / Riemann–von Mangoldt identity.

The `N_step` and `S` here are the ones already defined in `Theorem1.lean`; do not redefine them.

Alternative axiom-light path: replace the axioms above with a **definition** `theta t := δ t − Real.pi * φ t − Real.pi`. Then `riemann_vonMangoldt` becomes a `rfl` (or near-`rfl`) theorem, smoothness of `θ` follows from `contDiffAt_δ` and `contDiffAt_φ`, and only the *interpretation* "this `theta` agrees with the Riemann–Siegel theta function" is informal. Prefer this path if it keeps the file `sorry`-free without adding genuine analytic-number-theory axioms; document the identification with the Riemann–Siegel θ in the module docstring.

### Final statement

The top-level theorem in `Corollary2.lean` should mirror the `theorem1` statement:

```lean
theorem corollary2 (n : ℕ) (hn : 2 ≤ n) :
    IsO
      (fun t =>
        iteratedDeriv n theta t
        - ((-1 : ℝ) ^ n * (n - 2).factorial
           * (1 / 2) * t ^ (1 - (n : ℝ))))
      (fun t => t ^ (-(n : ℝ) - 1))
      𝓝∞
```

Mirror `Theorem1.lean §8` in style: a pointwise rewrite on `Set.Ioi 0`, an `iteratedDeriv_congr_of_nhds` lift, a `ring` cleanup, and an `IsO` stitching via `Filter.eventually_gt_atTop`.

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

**Analytic properties of `N_step`** — `N_step : ℝ → ℝ` may be any piecewise-constant (locally constant) function on `(0, ∞)`; it need not be the ζ-zero-counting step function. Being locally constant, its n-th iterated derivative (`n ≥ 1`) vanishes. Axiom name: `N_step_iteratedDeriv_eq_zero` (already in `Theorem1.lean`). When working in `Corollary2.lean`, interpret `N_step` as the right-continuous Riemann ζ zero-counting function `N(γ+0)`, which is integer-valued and jumps only at the ordinates of nontrivial ζ-zeros.

**Riemann–Siegel theta function `θ`** — `θ : ℝ → ℝ` is the continuous branch of `arg(π^(-s/2) Γ(s/2))` along the segment from `s = 1/2` to `s = 1/2 + it`. It is `C^∞` on `(0, ∞)` (no exceptional points) and monotonically increasing for `t ≥ 7`. Axiom names in `Corollary2.lean`: `theta` (the function), `contDiffAt_theta` (smoothness). May alternatively be *defined* as `theta t := δ t − π · φ t − π` (see "Working on `Corollary2.lean`"), in which case smoothness follows from `contDiffAt_δ` and `contDiffAt_φ`.

**Riemann–von Mangoldt formula** — the identity (equation (1) of the paper, [6])
```
N(t) = (1/π) · θ(t) + 1 + S(t)
```
relates the Riemann ζ zero-counting function `N`, the Riemann–Siegel theta function `θ`, and the argument function `S`. Combined with the Karatsuba–Korolev expansion `S = φ − (1/π)·δ + N_step` (the decomposition that holds by `rfl` in `Theorem1.lean`), it yields `θ(t) = δ(t) − π·φ(t) − π`. Axiom name in `Corollary2.lean`: `riemann_vonMangoldt`. This is the **only** Karatsuba–Korolev / number-theoretic input needed for Corollary 2 beyond `theorem1`.

### Lakefile options

```toml
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
```
