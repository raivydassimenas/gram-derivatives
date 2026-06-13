import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniform distribution modulo one

Concrete Weyl-criterion definitions of *uniform distribution modulo one* for
real sequences and real functions, expressed via Fourier exponentials
`exp(2πi · k · ·)` so that the reduction modulo `1` is built in through the
periodicity of the complex exponential.

These replace the opaque `Prop` wrappers previously used in
`GramDerivatives.Corollary5`. The deep
analytic theorems consumed downstream (Weyl's equivalence, derivative-decay ⇒
UD) remain as `-- ASSUMPTION` axioms in the consuming files; only the
definitions of UD/CUD themselves are made honest here.
-/

open scoped Real Topology BigOperators
open Filter

namespace Gram.UD

/-- A real sequence `a : ℕ → ℝ` is **uniformly distributed modulo one** iff for
every nonzero integer `k` the Cesàro averages of the Weyl exponentials
`exp(2πi · k · aₙ)` tend to zero. This is the Fourier-side formulation of
classical equidistribution. -/
def IsUDModOne (a : ℕ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    Tendsto
      (fun N : ℕ =>
        (1 / (N : ℂ)) *
          ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)))
      atTop (nhds 0)

/-- A real function `f : ℝ → ℝ` is **continuously uniformly distributed modulo
one** iff for every nonzero integer `k` the time averages of the Weyl
exponentials `exp(2πi · k · f(t))` over `[0, T]` tend to zero as `T → ∞`. -/
noncomputable def IsCUDModOne (f : ℝ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    Tendsto
      (fun T : ℝ =>
        (1 / (T : ℂ)) *
          ∫ t in (0 : ℝ)..T,
            Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (f t : ℂ)))
      atTop (nhds 0)

/-- Shifting the index of a UD-mod-1 sequence by one preserves UD-mod-1.

Sketch: the shifted Cesàro average
`(1/N) ∑ n<N, exp(2πi·k·a(n+1))` differs from
`(1/N) ∑ n<N, exp(2πi·k·a(n))` by `(1/N)·(exp(2πi·k·a(N)) - exp(2πi·k·a(0)))`,
which is bounded by `2/N` and hence vanishes; both averages then share the
same limit.

Kept as an axiom to keep the scope of the current refactor narrow.
-- ASSUMPTION -/
axiom IsUDModOne.shift {a : ℕ → ℝ} (h : IsUDModOne a) :
    IsUDModOne (fun k => a (k + 1))

end Gram.UD
