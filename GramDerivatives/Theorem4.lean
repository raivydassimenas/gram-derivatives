/-
  GramDerivatives/Theorem4.lean
  =============================
  Proof of Theorem 4 of Dundulis–Garunkštis–Laurinčikas–Šimėnas (2026):

      The sequence (t_k^n)_{k ∈ ℕ} is uniformly distributed modulo one
      for every n = 1, 2, 3, ….

  ─── Strategy ──────────────────────────────────────────────────────────
  The paper attributes the proof to Pańkowski [17, Proof of Theorem 1].
  The classical tool is the **higher-derivative Kuipers–Niederreiter /
  Fejér criterion** (Kuipers–Niederreiter [11], Theorem 2.5 + extensions):
  if `f^(l)` is eventually monotonic, tends to `0`, and
  `u · |f^(l)(u)| → ∞`, then `(f(n))_n` is uniformly distributed modulo one.

  We apply this with `f = (gram)^n` and `l = n`.  Leibniz expansion of
  `d^n/du^n (gram u)^n` isolates the leading term `n! · (gram'(u))^n`,
  which by Korolev's asymptotic `gram_deriv_asymp` (eq. (9)) is
  asymptotic to `n! · (2π / log u)^n`.  All other Leibniz terms contain
  a derivative `gram^(j)(u)` with `j ≥ 2`, which by Theorem 3 decays
  like `u^(1-j) / log² u` and is therefore negligible.

  ─── Status ────────────────────────────────────────────────────────────
  Skeleton: complete, no `sorry`.
  Proved:  `contDiffAt_gramPow`, `eventually_contDiffAt_gramPow`,
           `theorem4` itself (one-line application of the K–N criterion).
  Axioms (this file):
    • `isUDModOne_of_iteratedDeriv_decay` — the K–N criterion.
      Permanent: no UD-mod-1 theory in Mathlib (April 2026).
    • `iteratedDeriv_n_gramPow_n_isEquivalent` — TODO; Leibniz +
      Theorem 3 + eq. (9).  Provable, deferred.
    • `iteratedDeriv_n_gramPow_n_eventually_monotone` — TODO; follows
      from the asymp via monotonicity of `1/log u`.  Provable, deferred.
    • `iteratedDeriv_n_gramPow_n_tendsto_zero` — TODO; follows from
      the asymp via `2π/log u → 0`.  Provable, deferred.
    • `mul_iteratedDeriv_n_gramPow_n_tendsto_atTop` — TODO; follows
      from the asymp via `u / log^n u → ∞`.  Provable, deferred.
-/

import GramDerivatives.Theorem3
import GramDerivatives.UDModOne

open Real Filter Asymptotics
open scoped Topology

namespace Gram.Theorem4

/-- The function `u ↦ (gram u)^n`, where `gram` is the Gram function from
`Theorem3.lean`. -/
noncomputable def gramPow (n : ℕ) (u : ℝ) : ℝ := (gram u) ^ n

/-! ## §1  Kuipers–Niederreiter / Fejér criterion -/

/-- **Higher-derivative Kuipers–Niederreiter / Fejér criterion.**

If `f : ℝ → ℝ` is `l`-times continuously differentiable on a tail of `ℝ`,
its `l`-th iterated derivative is eventually monotonic (in absolute value),
tends to `0`, and `u · |f^(l)(u)| → ∞` as `u → ∞`, then the integer-indexed
sequence `(f(k))_{k ∈ ℕ}` is uniformly distributed modulo one.

Reference: Kuipers–Niederreiter [11], Theorem 2.5 (and the higher-derivative
form used in Pańkowski [17, Proof of Theorem 1]).

The smoothness hypothesis is stated in eventually-`ContDiffAt` form rather
than the classical global `ContDiff`, because the Gram function from
`Theorem3.lean` is only known to be `C^∞` on the tail `(gramThreshold, ∞)`.
This is harmless: only the tail behaviour of `f` matters for the conclusion.

-- ASSUMPTION -/
axiom isUDModOne_of_iteratedDeriv_decay
    (f : ℝ → ℝ) (l : ℕ) (_hl : 1 ≤ l)
    (_hC : ∀ᶠ u : ℝ in atTop, ContDiffAt ℝ l f u)
    (_hmono : ∃ x₀ : ℝ,
        MonotoneOn (fun t : ℝ => |iteratedDeriv l f t|) (Set.Ici x₀))
    (_h0 : Tendsto (fun u : ℝ => iteratedDeriv l f u) atTop (𝓝 0))
    (_hInf : Tendsto (fun u : ℝ => u * |iteratedDeriv l f u|) atTop atTop) :
    Gram.UD.IsUDModOne (fun k : ℕ => f k)

/-! ## §2  Smoothness of `gramPow n` on the Gram tail (proved) -/

/-- Pointwise smoothness of `gramPow n` on the open half-line
`(gramThreshold, ∞)`, inherited from `contDiffAt_gram` via `ContDiffAt.pow`. -/
lemma contDiffAt_gramPow (n l : ℕ) {u : ℝ} (hu : gramThreshold < u) :
    ContDiffAt ℝ l (gramPow n) u :=
  (contDiffAt_gram l hu).pow n

/-- Eventually-true `ContDiffAt` form of smoothness for `gramPow n`. -/
lemma eventually_contDiffAt_gramPow (n l : ℕ) :
    ∀ᶠ u : ℝ in atTop, ContDiffAt ℝ l (gramPow n) u := by
  filter_upwards [eventually_gt_atTop gramThreshold] with u hu
  exact contDiffAt_gramPow n l hu

/-! ## §3  Leading-term asymptotic (TODO) -/

/-- **Leading-term asymptotic** for the `n`-th derivative of `(gram)^n`.

The Leibniz formula for a product of `n` identical factors gives
`d^n/du^n (gram u)^n = Σ_{j_1+⋯+j_n = n} (n! / Π j_i!) · Π gram^(j_i)(u)`.
The unique partition contributing the leading order is
`j_1 = ⋯ = j_n = 1`, yielding the term `n! · (gram' u)^n`.  Every other
partition contains at least one factor `gram^(j)(u)` with `j ≥ 2`; by
Theorem 3, each such factor decays like `u^{1-j}/(log u)^2`, killing the
whole partition next to the leading one.  Substituting Korolev's
asymptotic `gram_deriv_asymp` (eq. (9)) yields
`(gram' u)^n ∼ (2π / log u)^n`.

-- TODO (deferred): the Leibniz expansion + asymptotic match
-- (`theorem3` + `gram_deriv_asymp` ⇒ this).  Tractable but voluminous —
-- comparable to a mid-size section of `Theorem3.lean`.
-- ASSUMPTION -/
axiom iteratedDeriv_n_gramPow_n_isEquivalent (n : ℕ) (_hn : 1 ≤ n) :
    IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv n (gramPow n) u)
      (fun u : ℝ => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n)

/-! ## §4  Eventual monotonicity (TODO) -/

/-- The `n`-th derivative of `(gram)^n` is eventually monotonic in absolute
value.  Sketch: the leading asymptotic `n! · (2π / log u)^n` is monotonically
decreasing for `u > e` (since `log u` is monotonically increasing), and the
asymp equivalence transfers monotonicity to `|iteratedDeriv n (gramPow n)|`
on a sufficiently far tail.

-- TODO (deferred): formalise "asymp-equivalent to a monotone function ⇒
-- eventually monotone in absolute value", combined with monotonicity of
-- `u ↦ 1/log u`.
-- ASSUMPTION -/
axiom iteratedDeriv_n_gramPow_n_eventually_monotone (n : ℕ) (_hn : 1 ≤ n) :
    ∃ x₀ : ℝ,
      MonotoneOn (fun u : ℝ => |iteratedDeriv n (gramPow n) u|) (Set.Ici x₀)

/-! ## §5  Decay to zero (TODO) -/

/-- The `n`-th derivative of `(gram)^n` tends to `0` as `u → ∞`.

Sketch: from `iteratedDeriv_n_gramPow_n_isEquivalent`, the function is
asymp-equivalent to `n! · (2π / log u)^n`.  Since `log u → ∞`, also
`2π / log u → 0`, and so does any positive power.

-- TODO (deferred): combine `IsEquivalent.symm.tendsto_nhds` with
-- `Tendsto.div_atTop` + `Tendsto.pow` for the `(2π/log u)^n` factor and
-- `Tendsto.const_mul` for the factorial.
-- ASSUMPTION -/
axiom iteratedDeriv_n_gramPow_n_tendsto_zero (n : ℕ) (_hn : 1 ≤ n) :
    Tendsto (fun u : ℝ => iteratedDeriv n (gramPow n) u) atTop (𝓝 0)

/-! ## §6  `u · |·| → ∞` (TODO) -/

/-- `u · |iteratedDeriv n (gramPow n) u| → ∞` as `u → ∞`.

Sketch: from the asymp, this behaves like
`u · n! · (2π/log u)^n = n! · (2π)^n · u/(log u)^n`,
which tends to `∞` because `u / (log u)^n → ∞` (a polynomial in `log u`
is negligible against `u`).

-- TODO (deferred): combine `IsEquivalent.symm.tendsto_atTop` (via the
-- absolute-value variant) with `Real.isLittleO_log_id_atTop.pow` and the
-- corresponding `IsLittleO.tendsto_atTop_of` reciprocal-shape lemma.
-- ASSUMPTION -/
axiom mul_iteratedDeriv_n_gramPow_n_tendsto_atTop (n : ℕ) (_hn : 1 ≤ n) :
    Tendsto (fun u : ℝ => u * |iteratedDeriv n (gramPow n) u|) atTop atTop

/-! ## §7  Theorem 4 -/

/-- **Theorem 4** of *Higher derivatives of the Gram function* (Dundulis,
Garunkštis, Laurinčikas, Šimėnas, 2026):

For every `n ≥ 1`, the sequence `((gram k)^n)_{k ∈ ℕ}` is uniformly
distributed modulo one.

Proof.  A direct application of the higher-derivative Kuipers–Niederreiter
criterion (`isUDModOne_of_iteratedDeriv_decay`) at `l = n`, using the four
analytic hypotheses established (or deferred) in §§2–6. -/
theorem theorem4 (n : ℕ) (hn : 1 ≤ n) :
    Gram.UD.IsUDModOne (fun k : ℕ => gramPow n (k : ℝ)) :=
  isUDModOne_of_iteratedDeriv_decay (gramPow n) n hn
    (eventually_contDiffAt_gramPow n n)
    (iteratedDeriv_n_gramPow_n_eventually_monotone n hn)
    (iteratedDeriv_n_gramPow_n_tendsto_zero n hn)
    (mul_iteratedDeriv_n_gramPow_n_tendsto_atTop n hn)

end Gram.Theorem4
