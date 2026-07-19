import GramDerivatives

/-!
# Axiom audit

Diagnostic module: runs `#print axioms` on every top-level result so the full
transitive axiom dependency can be inspected. Importing `GramDerivatives` (the
root) pulls in all five proof modules.

Run with:
```bash
lake build GramDerivatives.AxiomAudit
```

The output is recorded and discussed in `Axioms.md` at the repo root. This
module is intentionally not imported by the root library; build it explicitly
when re-auditing.
-/

#print axioms theorem1
#print axioms Gram.UD.vdc_fundamental_inequality
#print axioms Gram.UD.isUDModOne_of_forall_diff
#print axioms Gram.UD.isUDModOne_of_antitone_diff
#print axioms Gram.UD.isUDModOne_of_iteratedDeriv_decay
#print axioms corollary2
#print axioms strictMonoOn_theta
#print axioms gram_theta
#print axioms theorem3
#print axioms Gram.Theorem4.theorem4
#print axioms Gram.corollary5
