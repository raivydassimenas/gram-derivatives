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
UD) remain as `-- ASSUMPTION` axioms in the consuming files; this file itself
is axiom-free — the definitions of UD/CUD are honest, and the index-shift
lemma `IsUDModOne.shift` is proved.
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

The shifted Cesàro average
`(1/N) ∑ n<N, exp(2πi·k·a(n+1))` differs from
`(1/N) ∑ n<N, exp(2πi·k·a(n))` by `(1/N)·(exp(2πi·k·a(N)) - exp(2πi·k·a(0)))`,
which is bounded by `2/N` and hence vanishes; both averages then share the
same limit. -/
theorem IsUDModOne.shift {a : ℕ → ℝ} (h : IsUDModOne a) :
    IsUDModOne (fun k => a (k + 1)) := by
  intro k hk
  set e : ℕ → ℂ := fun n =>
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)) with he
  have hnorm : ∀ n, ‖e n‖ = 1 := by
    intro n
    simp [he, Complex.norm_exp]
  -- The shifted partial sum telescopes against the unshifted one.
  have hsum : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, e (n + 1))
        = (∑ n ∈ Finset.range N, e n) + e N - e 0 := by
    intro N
    have h1 := Finset.sum_range_succ' e N
    have h2 := Finset.sum_range_succ e N
    linear_combination h2 - h1
  -- The boundary term `(1/N)·(e N - e 0)` vanishes at infinity.
  have herr :
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * (e N - e 0)) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun N => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat 2)
    calc ‖(1 / (N : ℂ)) * (e N - e 0)‖
        = 1 / (N : ℝ) * ‖e N - e 0‖ := by
          rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      _ ≤ 1 / (N : ℝ) * 2 := by
          have : ‖e N - e 0‖ ≤ 2 := by
            calc ‖e N - e 0‖ ≤ ‖e N‖ + ‖e 0‖ := norm_sub_le _ _
              _ = 2 := by rw [hnorm, hnorm]; norm_num
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 / (N : ℝ) := by ring
  -- Stitch: shifted average = unshifted average + boundary term.
  have hlim := (h k hk).add herr
  rw [add_zero] at hlim
  refine hlim.congr fun N => ?_
  change (1 / (N : ℂ)) * (∑ n ∈ Finset.range N, e n)
        + (1 / (N : ℂ)) * (e N - e 0)
      = (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, e (n + 1)
  rw [hsum N]; ring

end Gram.UD
