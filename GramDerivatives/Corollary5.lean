import GramDerivatives.Theorem4

/-!
# Corollary 5 for powers of the Gram function

Formalization of Corollary 5 in the paper *Higher derivatives of the Gram
function*.

The paper states:

- **Theorem 4**: for every `n = 1, 2, 3, ...`, the sequence `{t_k^n}` is uniformly
  distributed modulo one;
- **Corollary 5**: the function `u ↦ t_u^n` is continuously uniformly distributed
  modulo one.

This file contains **no axioms**.  The discrete-to-continuous bridge is
Kuipers–Niederreiter Theorem 9.6(a) (Ryll-Nardzewski), *proved* as
`Gram.UD.isCUDModOne_of_forall_shift` in `UDModOne.lean` via the dominated
convergence theorem.  Its two hypotheses are supplied by:

- `Gram.Theorem4.measurable_gramPow` — measurability of `u ↦ (gram u)^n`
  (from `measurable_gram` in `Theorem3.lean`);
- `Gram.Theorem4.theorem4_shift` — uniform distribution mod one of every
  shifted integer sample `((gram (k + t))^n)ₖ`, `t ∈ [0, 1]` (the four Fejér
  hypotheses of Theorem 4, transported along the translation `u ↦ u + t`).

Consequently `corollary5` depends on **no custom axioms at all**: the
discrete Fejér criterion `isUDModOne_of_iteratedDeriv_decay`, formerly the
project's last axiom, is now a theorem (`Fejer.lean`).
-/

namespace Gram

/--
Corollary 5: for every `n ≥ 1`, the function `u ↦ (gram u)^n` is continuously
uniformly distributed modulo one.
-/
lemma corollary5 (n : ℕ) (hn : 1 ≤ n) :
    Gram.UD.IsCUDModOne (fun u : ℝ => Gram.Theorem4.gramPow n u) := by
  refine Gram.UD.isCUDModOne_of_forall_shift
    (Gram.Theorem4.measurable_gramPow n) ?_
  intro t ht
  exact Gram.Theorem4.theorem4_shift n hn t ht.1

end Gram
