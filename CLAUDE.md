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
GramDerivatives.lean              # root — re-exports the five proof modules
GramDerivatives/
  Theorem1.lean                   # detailed proof of Theorem 1
  Corollary2.lean                 # detailed proof of Corollary 2 (θ^(n) asymptotic)
  Theorem3.lean                   # detailed proof of Theorem 3 (t_u^(n) asymptotic; depends on Corollary2)
  Theorem4.lean                   # detailed proof of Theorem 4 (uniform distribution of {t_k^n})
  Corollary5.lean                 # Corollary 5 (continuous uniform distribution; depends on Theorem4)
  UDModOne.lean                   # honest UD/CUD-mod-1 definitions used by Theorem4/Corollary5
```

Note: the root `GramDerivatives.lean` imports all five proof modules, so a plain `lake build` (default target `GramDerivatives`) compiles the whole project. `Axioms.md` records the full `#print axioms` dependency of every top-level result; regenerate it with `lake build GramDerivatives.AxiomAudit`.

### Proof strategy

Deep analytic number theory unavailable in Mathlib (Riemann zeta, Riemann–Siegel theta, Karatsuba–Korolev formula, Kuipers–Niederreiter UD criteria) is introduced as `axiom` declarations, each marked `-- ASSUMPTION`, in the files that genuinely need it (`Theorem3.lean`, `Theorem4.lean`, `Corollary5.lean`, `UDModOne.lean`). This lets the *logical structure* of each proof compile while isolating the gaps. `Theorem1.lean` itself builds with **zero `sorry` and zero axioms** — every lemma (including `iteratedDeriv_α_part_isO`, `iteratedDeriv_j_isO`, `iteratedDeriv_tj_isO`, and `δ_eq`) is fully discharged, and the step-function slot is the bundled structure `StepFunction` (any function locally constant off a discrete jump set) whose regular-point properties are proved theorems; `theorem1` is proved for every instance.

- **`GramDerOverview.lean`** — states all five results (`Theorem1`, `Corollary2`, `Theorem3`, `Theorem4`, `Corollary5`) inside `namespace GramPaper`; serves as the spec. UD/CUD are stubbed via lightweight `Prop` wrappers (`UDMod1`, `CUDMod1`) and the analytic input is bundled into one axiom `gramPow_good_for_UD`.
- **`Theorem1.lean`** — implements the paper's decomposition for Theorem 1: splits `S(t)` into a smooth main term `φ(t)` and an error term `δ(t)`, then bounds the n-th derivative of each. The fully completed proof here is `iteratedDeriv_log` (iterated derivatives of `log` by induction); `iteratedDeriv_φ` builds on it. The final theorem is `theorem1` (§8).
- **`Corollary2.lean`** — derives the asymptotic for the n-th derivative of the Riemann–Siegel theta function `θ` from `theorem1` in `Theorem1.lean`. Imports `GramDerivatives.Theorem1` and reuses the decomposition `S F = φ − (1/π)·δ + F` (for `F : StepFunction`) together with the Riemann–von Mangoldt / Karatsuba–Korolev relation `N(t) = (1/π)·θ(t) + 1 + S(t)`. See "Working on `Corollary2.lean`" below.
- **`Theorem3.lean`** — planned: derives the asymptotic for the n-th derivative of the Gram function `t_u` (the inverse of `θ` on `[θ(7), ∞)`) by induction, differentiating the implicit relation `θ(t_u) = (u−1)π` and substituting the `θ^(n)` asymptotics from `Corollary2.lean`. See "Working on `Theorem3.lean`" below.
- **`Corollary5.lean`** — minimal-imports formalization (only `Mathlib.Data.Real.Basic`) inside `namespace Gram`. Uses opaque `Prop` wrappers `UDSeqModOne` / `UDContModOne`, takes Theorem 4 as an axiom, and derives `corollary5` via an abstract `continuous_ud_criterion` plus `UDSeqModOne_shift`. This is intentionally separate from the heavier `GramDerOverview.lean` formulation.

## Working on `Theorem1.lean`

`Theorem1.lean` is intentionally **independent of the Karatsuba–Korolev results**. Treat its setup abstractly:

- **The step-function slot is the bundled structure `StepFunction`**: a function `toFun : ℝ → ℝ` together with a jump set `jumpSet : Set ℝ` that is *discrete* (`jumpSet_discrete`: every point of it is isolated in it) and off which the function is locally constant (`locallyConstant_off`). It stands in for the zero-counting step function `N(γ+0)`; the proof uses only local constancy — `StepFunction.contDiffAt` and `StepFunction.iteratedDeriv_eq_zero` are **theorems** proved from that field. Discreteness is used only for `StepFunction.neBot_regularAtTop` (the relativized filter is nontrivial, so `theorem1` is never vacuous). Do not add ζ-specific properties.
- **`S` is parametrized over the class**: `S F (t) = φ(t) − (1/π)·δ(t) + F(t)` for any `F : StepFunction`, and `S_eq_φ_sub_δ_add_N` is a `rfl` theorem — not an imported analytic fact about `(1/π)·arg ζ(1/2 + it)`. `theorem1` takes `F` as its first argument and concludes at the filter `𝓝∞₀[F.jumpSet]`.
- **Do not change the definitions of `φ` and `δ`.** They stay exactly as in §1: `φ` the smooth main term and `δ = α_part − (t/2)·j` the error term. The leading-term asymptotic of Theorem 1 comes entirely from `φ`, and `δ^(n)(t) = O(t^(−n−1))` from `δ`.

Consequence: Theorem 1's proof in this file rests only on elementary calculus plus the abstract decomposition above — it does **not** depend on the Karatsuba–Korolev representation, the Riemann ζ function, or properties of its zeros. Docstrings and comments that still attribute `S`, the step function, or `S_eq_φ_sub_δ_add_N` to Karatsuba–Korolev describe the *original motivation* only; the formal content is the general statement.

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
- **The step function `F : StepFunction`** morally plays the role of `N(γ+0)`, the right-continuous Riemann ζ zero-counting function: the number of nontrivial zeros `ρ = β + iγ` with `0 < γ ≤ t`, `0 ≤ β ≤ 1` — integer-valued and piecewise constant on `(0, ∞)`, with jumps exactly at the ordinates of ζ-zeros. (Formally, `StepFunction` is the abstract class in `Theorem1.lean` of functions locally constant off a discrete jump set; `StepFunction.iteratedDeriv_eq_zero` is a theorem about it.)
- **`θ`** is the Riemann–Siegel theta function: the continuous branch of `arg(π^(-s/2) Γ(s/2))` along the segment from `s = 1/2` to `s = 1/2 + it`. It is `C^∞` on `(0, ∞)` (no exceptional points) and monotonically increasing for `t ≥ 7`.

### Karatsuba–Korolev input

The decomposition `S F = φ − (1/π)·δ + F` (for a step function `F`) from `Theorem1.lean` *is* the Karatsuba–Korolev expansion (equation (2) of the paper, [6, Proof of Theorem 2]) under the interpretation above. In `Theorem1.lean` it holds by `rfl`, but morally it is the Karatsuba–Korolev result.

The **second** Karatsuba–Korolev input — the one that lets us pass from `S` to `θ` — is the **Riemann–von Mangoldt formula** (equation (1) of the paper):

```
N(t) = (1/π) · θ(t) + 1 + S(t).
```

Solving for `θ`:

```
θ(t) = π · (F(t) − 1 − S F (t)).
```

Equivalently, substituting the Karatsuba–Korolev expansion of `S`:

```
θ(t) = δ(t) − π · φ(t) − π,
```

which — note — does **not** involve any step function at all. Either form is acceptable; the second is preferable because it makes `θ` smooth on all of `(0, ∞)` without invoking the local-constancy field of `StepFunction`.

### Proof sketch

Once `θ` is introduced, the proof of Corollary 2 is a one-step reduction to `theorem1`:

1. Pointwise on `(0, ∞)` (away from ζ-zero ordinates if working with a step function `F`),
   `θ(t) = π · (F(t) − 1 − S F (t))`.
2. Apply `iteratedDeriv` `n` times. For `n ≥ 1`:
   - `iteratedDeriv n (1 : ℝ → ℝ) = 0` (constant), and
   - `iteratedDeriv n F t = 0` by `StepFunction.iteratedDeriv_eq_zero`.
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
- `axiom riemann_vonMangoldt (F : StepFunction) (t : ℝ) (ht : 0 < t) : F t = (1 / Real.pi) * theta t + 1 + S F t` — equation (1) of the paper; the Karatsuba–Korolev / Riemann–von Mangoldt identity.

The `StepFunction` and `S` here are the ones already defined in `Theorem1.lean`; do not redefine them.

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

## Working on `Theorem3.lean`

`Theorem3.lean` formalizes **Theorem 3** of the paper — the asymptotic for the n-th derivative of the Gram function `t_u`. It depends on `Corollary2.lean` (for higher derivatives of `θ`) and introduces the Gram function as the inverse of the Riemann–Siegel theta function.

### Goal

Formalize **Theorem 3** of the paper:

```
For n ≥ 2, as u → +∞,
  t_u^(n) = (-1)^(n+1) · 2π · (n-2)! / (u^(n-1) · log² u)
            · (1 + (2 + o(1)) · log log u / log u).
```

This corrects the constant in [10, Lemma 1.1] for `n = 2` (Korolev).

### Setup

- **Gram function `t_u`** — for `t ≥ 7`, the Riemann–Siegel theta function `θ` is monotonically increasing, so it has a well-defined inverse on `[θ(7), ∞)`. The Gram function is defined implicitly by equation (7) of the paper:
  ```
  θ(t_u) = (u − 1) · π,   for u ≥ θ(7)/π + π.
  ```
  For positive integers `k`, `t_k` are the classical Gram points (Edwards [1, pp. 125–226]).

- **Background asymptotics already in the literature** (Lavrik [14, Lemma 2]; Korolev [10, Lemma 1.1]) — these are the `n = 0, 1` base lines that Theorem 3 generalizes:
  ```
  t_u   = (2π u / log u)   · (1 + (1 + o(1)) · log log u / log u),         (eq. 8)
  t_u'  = (2π   / log u)   · (1 + (1 + o(1)) · log log u / log u),         (eq. 9)
  ```
  as `u → +∞`.

### Proof sketch (paper §2, "Proof of Theorem 3")

Induction on `k ≥ 2`, inductive hypothesis:
```
t_u^(k) = (-1)^(k+1) · 2π · (k − 2)! / (u^(k-1) · log² u)
          · (1 + (2 + o(1)) · log log u / log u).
```

1. **Base case `k = 2`.** Differentiate `θ(t_u) = (u − 1)π` twice w.r.t. `u`:
   ```
   θ''(t_u) · (t_u')² + θ'(t_u) · t_u'' = 0,
   ```
   so `t_u'' = −θ''(t_u) · (t_u')² / θ'(t_u)`. Substitute the Corollary-2 asymptotics for `θ'(t_u), θ''(t_u)` and the eq.-(9) asymptotic for `t_u'`.
2. **Inductive step.** Differentiate the implicit relation `k` times via the Faà di Bruno / general Leibniz rule, isolate `t_u^(k)`, and substitute the asymptotics from Corollary 2 plus the inductive hypothesis for lower derivatives.

### Interpretation of imported names

When importing `GramDerivatives.Corollary2`:

- **`theta`** is the Riemann–Siegel theta function (as fixed in `Corollary2.lean`), monotonically increasing for `t ≥ 7`.
- **`gram : ℝ → ℝ`** — the Gram function, defined as the inverse of `theta` on `[θ(7), ∞)` (or equivalently the solution of `θ(t_u) = (u − 1)π`). Smoothness on `(θ(7)/π + π, ∞)` follows from the inverse function theorem applied to `theta` (which has nonvanishing derivative there).

### Axiom budget for `Theorem3.lean`

Introduce the following new axioms (each tagged `-- ASSUMPTION`):

- `axiom gram : ℝ → ℝ` — the Gram function `t_u`.
- `axiom gram_spec (u : ℝ) (hu : θ(7)/π + π ≤ u) : theta (gram u) = (u − 1) * Real.pi` — equation (7) of the paper.
- `axiom contDiffAt_gram (n : ℕ) {u : ℝ} (hu : θ(7)/π + π < u) : ContDiffAt ℝ n gram u` — smoothness on the open half-line, by the inverse function theorem.
- `axiom gram_asymp` and `axiom gram_deriv_asymp` — equations (8) and (9), the Lavrik / Korolev base-case asymptotics for `t_u` and `t_u'`.

Alternative axiom-light path: define `gram` directly via Mathlib's inverse function constructions applied to `theta`, and prove `gram_spec` and `contDiffAt_gram` from `contDiffAt_theta` + monotonicity. Equations (8) and (9) likely remain as axioms (they are number-theoretic asymptotic results, not formalizable from the `theta` axioms alone).

### Final statement

The top-level theorem should read:

```lean
theorem theorem3 (n : ℕ) (hn : 2 ≤ n) :
    IsLittleO 𝓝∞
      (fun u =>
        iteratedDeriv n gram u
        - ((-1 : ℝ) ^ (n + 1) * (2 * Real.pi) * (n - 2).factorial
           / (u ^ (n - 1) * Real.log u ^ 2)
           * (1 + 2 * Real.log (Real.log u) / Real.log u)))
      (fun u =>
        1 / (u ^ (n - 1) * Real.log u ^ 2)
        * (Real.log (Real.log u) / Real.log u))
```

i.e. the `(2 + o(1))` factor is encoded as a `IsLittleO` remainder against `log log u / log u`, in the same spirit as the `IsO` packaging used in `Theorem1.lean §8` and `Corollary2.lean`.

## Assumed analytic facts

When working on proofs in this repo, treat the following as established results that do not need to be re-derived or questioned — introduce them as `axiom` declarations if not already present:

**Decomposition of `S`** — for any step function `F : StepFunction`, `S F (t)` is defined as
```
S F (t) = φ(t) − (1/π) δ(t) + F(t)
```
In `Theorem1.lean`, `S` is a `def` parametrized over `StepFunction` and `S_eq_φ_sub_δ_add_N` is a `rfl` theorem, not an imported number-theoretic fact. See "Working on `Theorem1.lean`" above. The Karatsuba–Korolev representation is the motivation for this decomposition but is not needed by the proof.

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

**Analytic properties of the step function** — the step-function slot in the decomposition is the bundled structure `StepFunction` in `Theorem1.lean`: any function `ℝ → ℝ` locally constant off a discrete jump set (`jumpSet`); the proof only uses local constancy off `F.jumpSet`. Being locally constant at regular points, its n-th iterated derivative (`n ≥ 1`) vanishes there. Lemma names: `StepFunction.contDiffAt` and `StepFunction.iteratedDeriv_eq_zero` (theorems in `Theorem1.lean`, formerly axioms); `StepFunction.neBot_regularAtTop` shows the relativized filter `𝓝∞₀[F.jumpSet]` is nontrivial. When working in `Corollary2.lean`, the step function morally plays the role of the right-continuous Riemann ζ zero-counting function `N(γ+0)`, which is integer-valued and jumps only at the ordinates of nontrivial ζ-zeros.

**Riemann–Siegel theta function `θ`** — `θ : ℝ → ℝ` is the continuous branch of `arg(π^(-s/2) Γ(s/2))` along the segment from `s = 1/2` to `s = 1/2 + it`. It is `C^∞` on `(0, ∞)` (no exceptional points) and monotonically increasing for `t ≥ 7`. Axiom names in `Corollary2.lean`: `theta` (the function), `contDiffAt_theta` (smoothness). May alternatively be *defined* as `theta t := δ t − π · φ t − π` (see "Working on `Corollary2.lean`"), in which case smoothness follows from `contDiffAt_δ` and `contDiffAt_φ`.

**Gram function `t_u`** — the inverse of `θ` on the half-line where `θ` is monotonic. For `u ≥ θ(7)/π + π`, `t_u` is the unique real satisfying `θ(t_u) = (u − 1)π` (equation (7) of the paper). It is `C^∞` on `(θ(7)/π + π, ∞)` by the inverse function theorem (since `θ'` does not vanish there). The base-case asymptotics
```
t_u  = (2π u / log u) · (1 + (1 + o(1)) · log log u / log u),   (eq. 8, Lavrik [14])
t_u' = (2π   / log u) · (1 + (1 + o(1)) · log log u / log u),   (eq. 9, Korolev [10])
```
are taken as established. Axiom names in `Theorem3.lean`: `gram`, `gram_spec`, `contDiffAt_gram`, `gram_asymp`, `gram_deriv_asymp`. Used to derive Theorem 3.

**Riemann–von Mangoldt formula** — the identity (equation (1) of the paper, [6])
```
N(t) = (1/π) · θ(t) + 1 + S(t)
```
relates the Riemann ζ zero-counting function `N`, the Riemann–Siegel theta function `θ`, and the argument function `S`. Combined with the Karatsuba–Korolev expansion `S F = φ − (1/π)·δ + F` (the decomposition that holds by `rfl` in `Theorem1.lean`), it yields `θ(t) = δ(t) − π·φ(t) − π`. Name in `Corollary2.lean`: `riemann_vonMangoldt` (a theorem there, stated for every `F : StepFunction`). This is the **only** Karatsuba–Korolev / number-theoretic input needed for Corollary 2 beyond `theorem1`.

### Lakefile options

```toml
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
```
