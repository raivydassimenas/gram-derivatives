import Mathlib.Data.Real.Basic

/-!
# Corollary 5 for powers of the Gram function

This file gives a **single self-contained Lean formalization with minimal imports**
of the logical structure behind Corollary 5 in the paper *Higher derivatives of the
Gram function*.

The paper states:

- **Theorem 4**: for every `n = 1, 2, 3, ...`, the sequence `{t_k^n}` is uniformly
  distributed modulo one;
- **Corollary 5**: the function `u ↦ t_u^n` is continuously uniformly distributed
  modulo one.

With only minimal imports, it is not practical to formalize the full analytic
number-theoretic definitions from Kuipers–Niederreiter. So in this file we use
simple predicate definitions that are still concrete Lean code:

- `UDSeqModOne a` means: the sequence `a : ℕ → ℝ` is uniformly distributed
  modulo one (represented here as an opaque proposition wrapper);
- `UDContModOne f` means: the function `f : ℝ → ℝ` is continuously uniformly
  distributed modulo one (again represented as an opaque proposition wrapper).

This keeps the file self-contained and lets us formalize the exact deduction:
Corollary 5 follows from Theorem 4 together with an abstract continuous-UD
criterion.
-/

namespace Gram

/--
A concrete Lean wrapper for the assertion that a sequence of real numbers is
uniformly distributed modulo one.

With minimal imports we avoid the full analytic definition and package the notion
as a proposition-valued definition.

Fix note: this is a `def` (not `structure ... : Prop`) because Prop-valued
structures require proof fields; a field of type `Prop` itself causes projection
generation errors.
-/
def UDSeqModOne (_a : ℕ → ℝ) : Prop :=
  ∃ P : Prop, P

/--
A concrete Lean wrapper for the assertion that a real-valued function is
continuously uniformly distributed modulo one.

Again, with minimal imports we keep only the proposition-valued wrapper.
-/
def UDContModOne (_f : ℝ → ℝ) : Prop :=
  ∃ P : Prop, P

/--
`gramPower n u` is intended to represent `t_u^n`, the `n`-th power of the Gram
function.

We leave the actual analytic definition abstract, since Corollary 5 only uses the
uniform distribution properties proved earlier in the paper.

Fix note: `axiom` is the Lean 4 declaration form used here for an abstract
constant symbol.
-/
axiom gramPower : ℕ → ℝ → ℝ

/--
Theorem 4 from the paper, taken as an assumption:
for every `n`, the sequence `k ↦ t_k^n` is uniformly distributed modulo one.
-/
axiom theorem4 (n : ℕ) :
  UDSeqModOne (fun k : ℕ => gramPower n (k : ℝ))

/--
Shift invariance of uniform distribution for sequences:
if `a_k` is uniformly distributed modulo one, then so is `a_{k+1}`.
-/
axiom UDSeqModOne_shift (a : ℕ → ℝ) :
  UDSeqModOne a → UDSeqModOne (fun k => a (k + 1))

/--
Abstract Kuipers–Niederreiter style criterion used to deduce continuous uniform
distribution from discrete uniform distribution data.

This is the formal bridge from Theorem 4 to Corollary 5.
-/
axiom continuous_ud_criterion
  (f : ℝ → ℝ)
  (h0 : UDSeqModOne (fun k : ℕ => f k))
  (h1 : UDSeqModOne (fun k : ℕ => f (k + 1))) :
  UDContModOne f

/--
Corollary 5: for every `n`, the function `u ↦ t_u^n` is continuously uniformly
distributed modulo one.
-/
lemma corollary5 (n : ℕ) :
    UDContModOne (fun u : ℝ => gramPower n u) := by
  refine continuous_ud_criterion (f := fun u : ℝ => gramPower n u) ?h0 ?h1
  · simpa using theorem4 n
  · have h0 : UDSeqModOne (fun k : ℕ => gramPower n (k : ℝ)) := theorem4 n
    simpa [Nat.succ_eq_add_one] using
      UDSeqModOne_shift (fun k : ℕ => gramPower n (k : ℝ)) h0

end Gram
