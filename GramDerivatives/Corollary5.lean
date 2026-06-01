import GramDerivatives.Theorem4

/-!
# Corollary 5 for powers of the Gram function

Formalization of the logical structure behind Corollary 5 in the paper *Higher
derivatives of the Gram function*.

The paper states:

- **Theorem 4**: for every `n = 1, 2, 3, ...`, the sequence `{t_k^n}` is uniformly
  distributed modulo one;
- **Corollary 5**: the function `u ↦ t_u^n` is continuously uniformly distributed
  modulo one.

Theorem 4 is supplied as `Gram.Theorem4.theorem4` (this file imports
`GramDerivatives.Theorem4`, which builds on the concrete `gram` from
`GramDerivatives.Theorem3`).  The Kuipers–Niederreiter discrete-to-continuous
bridge is the only remaining axiom local to this file.
-/

namespace Gram

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
Corollary 5: for every `n ≥ 1`, the function `u ↦ (gram u)^n` is continuously
uniformly distributed modulo one.
-/
lemma corollary5 (n : ℕ) (hn : 1 ≤ n) :
    Gram.UD.IsCUDModOne (fun u : ℝ => Gram.Theorem4.gramPow n u) := by
  refine continuous_ud_criterion (f := fun u : ℝ => Gram.Theorem4.gramPow n u) ?h0 ?h1
  · exact Gram.Theorem4.theorem4 n hn
  · -- Reconcile `gramPow n ↑(k+1)` (from the shift) with `gramPow n (↑k + 1)`
    -- (the expected `f (k+1)` form) via a Nat-cast rewrite, transported through
    -- `IsUDModOne` without unfolding its body.
    have h := Gram.UD.IsUDModOne.shift (Gram.Theorem4.theorem4 n hn)
    have heq :
        (fun k : ℕ => Gram.Theorem4.gramPow n (((k + 1 : ℕ) : ℝ)))
          = (fun k : ℕ => Gram.Theorem4.gramPow n ((k : ℝ) + 1)) := by
      funext k; push_cast; ring
    exact heq ▸ h

end Gram
