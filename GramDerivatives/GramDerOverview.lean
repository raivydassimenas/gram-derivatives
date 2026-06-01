-- Correction: use a stable umbrella import to avoid version-specific module path changes.
import Mathlib
import GramDerivatives.UDModOne

/-!
Formalization sketch in Lean 4 / mathlib of Theorem 1, Corollary 2,
Theorem 3, Theorem 4, and Corollary 5 from
"Higher derivatives of the Gram function".

This file is **not** expected to compile as-is: a substantial amount of
analytic number theory is currently missing from mathlib (April 2026).
Instead, we:

* State the theorems in a simplified, slightly idealized setting.
* Isolate all deep analytic input into `axiom` / `sorry` stubs.
* Explain, in comments, how each Lean proof mirrors the argument in the
  paper (Faà di Bruno, asymptotics, uniform distribution criteria, etc.).

The intent is that this serves as a roadmap: each `sorry` can be
replaced by a genuine proof once the corresponding lemmas are
available in mathlib.

Correction note: imports were moved above this module docstring because
Lean requires `import` commands at the beginning of the file.
-/

open scoped Real Topology BigOperators
open Filter Asymptotics

namespace GramPaper

/-!
## Section 1: Abstract asymptotic input for `S` and `θ`

In the paper, `S(t) = (1/π) arg ζ(1/2 + i t)` and `θ(t)` is the
Riemann–Siegel theta function.  Here we *axiomatize* their analytic
properties as functions `S θ : ℝ → ℝ` with the required asymptotics.
-/

/-- Abstract version of the function `S` from the paper. -/
axiom S : ℝ → ℝ

/-- Abstract version of the Riemann–Siegel theta function `θ`. -/
axiom theta : ℝ → ℝ

/--
For simplicity we encode the asymptotic claimed in Theorem 1 as an axiom
in the language of `IsBigO` at `atTop`.

In the paper Theorem 1 says (for `n ≥ 2`)

`S^{(n)}(t) = (-1)^{n-1} (n-2)! / (2π) t^{1-n} + O(t^{-n-1})`.

We represent this as equality of functions up to a `IsBigO` error term.
-/
axiom S_iteratedDeriv_asymptotic
  (n : ℕ) (hn : 2 ≤ n) :
  (fun t : ℝ =>
    iteratedDeriv n S t
    - (-1 : ℝ)^(n-1) * (Nat.factorial (n-2)) / (2 * Real.pi) * t^(1-n))
  -- Correction: negative powers on `ℝ` use integer exponents, not `ℕ`.
  =O[atTop] fun t : ℝ => t^(- (n+1 : ℤ))

/--
Similarly, Corollary 2 gives an asymptotic formula for the derivatives of
`θ(t)`.
-/
axiom theta_iteratedDeriv_asymptotic
  (n : ℕ) (hn : 2 ≤ n) :
  (fun t : ℝ =>
    iteratedDeriv n theta t
    - (-1 : ℝ)^n * (Nat.factorial (n-2)) / 2 * t^(1-n))
  -- Correction: same exponent fix as above (`ℤ` exponent for negative power).
  =O[atTop] fun t : ℝ => t^(- (n+1 : ℤ))

/-!
## Section 2: Formal statements corresponding to Theorem 1 and Corollary 2

These theorems simply repackage the axioms above in a user-friendly
form.  In a fully developed library one would *prove* them from the
Riemann–von Mangoldt formula and the detailed analysis of `δ(t)`.
-/

/-- Theorem 1 (formal version): higher derivatives of `S`. -/
 theorem Theorem1
  (n : ℕ) (hn : 2 ≤ n) :
  (fun t : ℝ =>
    iteratedDeriv n S t
    - (-1 : ℝ)^(n-1) * (Nat.factorial (n-2)) / (2 * Real.pi) * t^(1-n))
  -- Correction: mirror the fixed `ℤ`-exponent asymptotic statement.
  =O[atTop] fun t : ℝ => t^(- (n+1 : ℤ)) :=
by
  -- In a full formalization this would expand the definition of `S`,
  -- differentiate the Riemann–von Mangoldt formula, and estimate the
  -- error term.  Here we simply refer to the axiom.
  simpa using S_iteratedDeriv_asymptotic n hn

/-- Corollary 2 (formal version): higher derivatives of `θ`. -/
 theorem Corollary2
  (n : ℕ) (hn : 2 ≤ n) :
  (fun t : ℝ =>
    iteratedDeriv n theta t
    - (-1 : ℝ)^n * (Nat.factorial (n-2)) / 2 * t^(1-n))
  -- Correction: mirror the fixed `ℤ`-exponent asymptotic statement.
  =O[atTop] fun t : ℝ => t^(- (n+1 : ℤ)) :=
by
  simpa using theta_iteratedDeriv_asymptotic n hn

/-!
## Section 3: Abstract Gram function and its derivatives (Theorem 3)

The Gram function `t_u` is defined implicitly by `θ(t_u) = (u - 1) π`.
We model it as a function `gram : ℝ → ℝ` which is a smooth inverse of
`θ` on a tail of the real line, and we assume the known first-order
asymptotics.  Then Theorem 3 is encoded as an axiom about higher
iterated derivatives of `gram`.
-/

/-- The Gram function, abstractly.  In the paper this is `t_u`. -/
axiom gram : ℝ → ℝ

/--
`gram` is eventually the inverse of `theta` on `[T,+∞)`, and smooth.
Here we only encode a weak form: `theta (gram u) = (u-1)π` for large `u`.
-/
axiom gram_is_implicit
  : ∀ᶠ u in atTop, theta (gram u) = (u - 1) * Real.pi

/--
Asymptotic for the first derivative `t'_u` (equation (9) in the paper).
This is used as a base case in the induction for higher derivatives.
-/
axiom gram_deriv_asymptotic
  : (fun u : ℝ =>
      deriv gram u
        - (2 * Real.pi) / Real.log u)
    =O[atTop] fun u : ℝ =>
      (Real.log (Real.log u) / (Real.log u)^2)

/--
Theorem 3 (formal, axiomatized): asymptotic for the `n`-th derivative of
`gram`.

In the paper:

`t_u^{(n)} ~ (-1)^{n+1} / (2π) (n-2)! / (u^{n-1} (log u)^2)
   * ( 1 + (2 + o(1)) (log log u)/(log u) )`.

We encode only the main term with an `IsBigO` error; extending to the
full second-order expansion is possible but would make the statement
heavier.
-/
axiom gram_iteratedDeriv_asymptotic
  (n : ℕ) (hn : 2 ≤ n) :
  (fun u : ℝ =>
    iteratedDeriv n gram u
      - (-1 : ℝ)^(n+1) * (Nat.factorial (n-2)) / (2 * Real.pi)
        * u^(1-n) / (Real.log u)^2)
  =O[atTop] fun u : ℝ =>
    u^(1-n) * (Real.log (Real.log u)) / (Real.log u)^3

/-- Theorem 3 (Lean version, re-export of the axiom). -/
 theorem Theorem3
  (n : ℕ) (hn : 2 ≤ n) :
  (fun u : ℝ =>
    iteratedDeriv n gram u
      - (-1 : ℝ)^(n+1) * (Nat.factorial (n-2)) / (2 * Real.pi)
        * u^(1-n) / (Real.log u)^2)
  =O[atTop] fun u : ℝ =>
    u^(1-n) * (Real.log (Real.log u)) / (Real.log u)^3 :=
by
  simpa using gram_iteratedDeriv_asymptotic n hn

/-!
### Comment on the proof structure (informal)

The actual proof in the paper proceeds by induction on `n` using
Faà di Bruno's formula applied to the identity `θ(gram u) = (u-1)π`.

In Lean, once the prerequisites are available, the structure would be:

```lean
  -- differentiate θ(gram u) n times using Faà di Bruno
  have hFaà : iteratedDeriv n (fun u => theta (gram u)) u = 0 := by
    ...

  -- rewrite in terms of iteratedDeriv n gram u, isolate the leading
  -- term, and estimate the remaining sum using previously proved
  -- asymptotics for lower-order derivatives.
```

Here we keep this at the level of an `axiom` to reflect that all the
technical analytic estimates are yet to be formalized.
-/

/-!
## Section 4: Uniform distribution of powers of the Gram function

Theorem 4 and Corollary 5 are results in the theory of uniform and
continuous uniform distribution modulo one.

The notions of (continuous) uniform distribution modulo one are reused from
`GramDerivatives.UDModOne`, where they are given honest Weyl-criterion
definitions on top of `Complex.exp` and the interval integral. The
abbreviations `UDMod1`, `CUDMod1` below are kept as local aliases for backward
compatibility with the rest of this file.
-/

/-- A sequence `a : ℕ → ℝ` is uniformly distributed modulo `1`. -/
abbrev UDMod1 (a : ℕ → ℝ) : Prop := Gram.UD.IsUDModOne a

/-- A function `f : ℝ → ℝ` is continuously uniformly distributed modulo `1`. -/
abbrev CUDMod1 (f : ℝ → ℝ) : Prop := Gram.UD.IsCUDModOne f

/--
The analytic criterion needed in the paper (Kuipers–Niederreiter,
Theorem 3.5): if `f^(l)` tends monotonically to `0` and `x | f^(l) x |
→ ∞`, then the integer sequence `f n` is uniformly distributed mod 1.

We state this abstractly as an axiom; a full formalization would work
in terms of bounded discrepancy and Weyl's criterion.
-/
axiom UD_of_deriv_pow_decays
  -- Correction (second pass): restore the stronger analytic hypothesis package.
  (f : ℝ → ℝ) (l : ℕ)
  (hC : ContDiff ℝ l f)
  -- Correction: explicitly type the eventual-variable as `ℝ` so `atTop` is resolved.
  (hmono : ∀ᶠ _x : ℝ in atTop, Monotone (fun t : ℝ => |iteratedDeriv l f t|))
  (h0 : Tendsto (fun x : ℝ => iteratedDeriv l f x) atTop (nhds (0 : ℝ)))
  (hInf : Tendsto (fun x : ℝ => x * |iteratedDeriv l f x|) atTop atTop) :
  UDMod1 (fun n : ℕ => f n)

/-!
Theorem 4 (formal version): the sequence `t_{n,k}` is uniformly
distributed modulo one for every `n ≥ 1`.

We encode `t_{n,k}` as `gram ( (k : ℝ)^n )`.
-/

/-- Power of the Gram function, as in the paper `t_u^n`. -/
noncomputable def gramPow (n : ℕ) (u : ℝ) : ℝ :=
  (gram u)^n

/-- Sequence `t_{n,k}`: `k ↦ gram(k)^n`. -/
noncomputable def gramSeq (n : ℕ) (k : ℕ) : ℝ :=
  gramPow n k

/--
Analytic assumptions on `gramPow n` needed to apply the criterion
`UD_of_deriv_pow_decays`.

In the paper these are proved by explicitly computing high derivatives
of `u ↦ (gram u)^n` and applying the asymptotics for `gram`.
-/
axiom gramPow_good_for_UD
  -- Correction (second pass): restore the full derivative-based assumptions.
  (n : ℕ) (hn : 1 ≤ n) :
  ∃ l : ℕ,
    ContDiff ℝ l (gramPow n)
    ∧ (∀ᶠ _x : ℝ in atTop, Monotone (fun t : ℝ => |iteratedDeriv l (gramPow n) t|))
    ∧ Tendsto (fun x : ℝ => iteratedDeriv l (gramPow n) x) atTop (nhds (0 : ℝ))
    ∧ Tendsto (fun x : ℝ => x * |iteratedDeriv l (gramPow n) x|) atTop atTop

/-- Theorem 4: uniform distribution of `t_{n,k}` mod 1. -/
 theorem Theorem4 (n : ℕ) (hn : 1 ≤ n) :
  UDMod1 (gramSeq n) :=
by
  -- Correction (second pass): reintroduce the criterion application from analytic hypotheses.
  rcases gramPow_good_for_UD n hn with ⟨l, hC, hmono, h0, hInf⟩
  change UDMod1 (fun k : ℕ => gramPow n k)
  exact UD_of_deriv_pow_decays (gramPow n) l hC hmono h0 hInf

/--
Corollary 5: continuous uniform distribution of `u ↦ gram(u)^n` mod 1.

We again treat this as a wrapper around the classical result of
Kuipers–Niederreiter used in the paper: conditions on higher derivatives
imply CUD, and we reuse the same analytic input bundled in
`gramPow_good_for_UD`.
-/
axiom CUD_of_deriv_pow_decays
  -- Correction (second pass): restore the stronger derivative-based CUD criterion.
  (f : ℝ → ℝ) (l : ℕ)
  (hC : ContDiff ℝ l f)
  (hmono : ∀ᶠ _x : ℝ in atTop, Monotone (fun t : ℝ => |iteratedDeriv l f t|))
  (h0 : Tendsto (fun x : ℝ => iteratedDeriv l f x) atTop (nhds (0 : ℝ)))
  (hInf : Tendsto (fun x : ℝ => x * |iteratedDeriv l f x|) atTop atTop) :
  CUDMod1 f

/-- Corollary 5: `u ↦ gram(u)^n` is continuously uniformly distributed mod 1. -/
 theorem Corollary5 (n : ℕ) (hn : 1 ≤ n) :
  CUDMod1 (gramPow n) :=
by
  -- Correction (second pass): derive CUD from the same derivative package as in Theorem 4.
  rcases gramPow_good_for_UD n hn with ⟨l, hC, hmono, h0, hInf⟩
  exact CUD_of_deriv_pow_decays (gramPow n) l hC hmono h0 hInf

end GramPaper
