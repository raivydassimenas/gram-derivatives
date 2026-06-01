import GramDerivatives.UDModOne

/-!
# Corollary 5 for powers of the Gram function

Formalization of the logical structure behind Corollary 5 in the paper *Higher
derivatives of the Gram function*.

The paper states:

- **Theorem 4**: for every `n = 1, 2, 3, ...`, the sequence `{t_k^n}` is uniformly
  distributed modulo one;
- **Corollary 5**: the function `u ↦ t_u^n` is continuously uniformly distributed
  modulo one.

The notions of (continuous) uniform distribution modulo one are now imported
from `GramDerivatives.UDModOne`, where they are defined via the Weyl criterion
(`Gram.UD.IsUDModOne`, `Gram.UD.IsCUDModOne`). The deep theorems used below —
Theorem 4 itself, and the Kuipers–Niederreiter discrete-to-continuous bridge —
remain `-- ASSUMPTION` axioms.
-/

namespace Gram

/--
`gramPower n u` is intended to represent `t_u^n`, the `n`-th power of the Gram
function. We leave the actual analytic definition abstract, since Corollary 5
only uses the uniform distribution properties proved earlier in the paper.
-/
axiom gramPower : ℕ → ℝ → ℝ

/--
Theorem 4 from the paper, taken as an assumption:
for every `n`, the sequence `k ↦ t_k^n` is uniformly distributed modulo one.
-- ASSUMPTION -/
axiom theorem4 (n : ℕ) :
  Gram.UD.IsUDModOne (fun k : ℕ => gramPower n (k : ℝ))

/--
Abstract Kuipers–Niederreiter style criterion used to deduce continuous uniform
distribution from discrete uniform distribution data.

This is the formal bridge from Theorem 4 to Corollary 5.
-- ASSUMPTION -/
axiom continuous_ud_criterion
  (f : ℝ → ℝ)
  (h0 : Gram.UD.IsUDModOne (fun k : ℕ => f k))
  (h1 : Gram.UD.IsUDModOne (fun k : ℕ => f (k + 1))) :
  Gram.UD.IsCUDModOne f

/--
Corollary 5: for every `n`, the function `u ↦ t_u^n` is continuously uniformly
distributed modulo one.
-/
lemma corollary5 (n : ℕ) :
    Gram.UD.IsCUDModOne (fun u : ℝ => gramPower n u) := by
  refine continuous_ud_criterion (f := fun u : ℝ => gramPower n u) ?h0 ?h1
  · exact theorem4 n
  · -- Reconcile `gramPower n ↑(k+1)` (from the shift) with
    -- `gramPower n (↑k + 1)` (the expected `f (k+1)` form) via a Nat-cast rewrite,
    -- transported through `IsUDModOne` without unfolding its body.
    have h := Gram.UD.IsUDModOne.shift (theorem4 n)
    have heq :
        (fun k : ℕ => gramPower n (((k + 1 : ℕ) : ℝ)))
          = (fun k : ℕ => gramPower n ((k : ℝ) + 1)) := by
      funext k; push_cast; ring
    exact heq ▸ h

end Gram
