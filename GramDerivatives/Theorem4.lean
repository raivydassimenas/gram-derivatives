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
           `iteratedDeriv_n_gramPow_n_tendsto_zero`,
           `mul_iteratedDeriv_n_gramPow_n_tendsto_atTop`,
           `iteratedDeriv_n_gramPow_n_eventually_pos` (helper),
           `theorem4` itself (one-line application of the K–N criterion).
  Axioms (this file):
    • `isUDModOne_of_iteratedDeriv_decay` — the K–N criterion
      (antitone variant).  Permanent: no UD-mod-1 theory in Mathlib.
    • `iteratedDeriv_n_gramPow_n_isEquivalent` — TODO; Leibniz +
      Theorem 3 + eq. (9).  Provable, deferred.
    • `iteratedDeriv_n_gramPow_n_eventually_antitone` — TODO; needs
      the sign of the `(n+1)`-th derivative (not derivable from the §3
      asymp alone — see the docstring).
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

The eventual-monotonicity hypothesis is stated with `AntitoneOn`
(decreasing): in the application below, `|iteratedDeriv l f|` tends to
`0` from above, so the natural direction is antitone.  Mathematically
the classical K–N statement allows either direction, but the antitone
side is what our setting provides.

-- ASSUMPTION -/
axiom isUDModOne_of_iteratedDeriv_decay
    (f : ℝ → ℝ) (l : ℕ) (_hl : 1 ≤ l)
    (_hC : ∀ᶠ u : ℝ in atTop, ContDiffAt ℝ l f u)
    (_hmono : ∃ x₀ : ℝ,
        AntitoneOn (fun t : ℝ => |iteratedDeriv l f t|) (Set.Ici x₀))
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

/-! ## §4  Eventual antitone in absolute value (TODO) -/

/-- The `n`-th derivative of `(gram)^n` is **eventually antitone** in
absolute value: `|iteratedDeriv n (gramPow n) ·|` is decreasing on a tail.

Why this is genuinely harder than the §5/§6 corollaries.  The §3 asymp
equivalence
`iteratedDeriv n (gramPow n) u ∼ n! · (2π/log u)^n`
controls the function up to a multiplicative `(1 + o(1))` factor, but
asymp-equivalence to an antitone function is **not** enough to force
pointwise antitone behaviour (cf. `1/x + sin(x²)/x³ ∼ 1/x`, yet the LHS
is not eventually antitone).

The standard route is to show the `(n+1)`-th derivative of `(gram)^n`
is eventually **negative** and invoke `antitoneOn_of_deriv_nonpos`.  By
Leibniz, the leading term of `d^{n+1}/du^{n+1} (gram u)^n` is
`n! · n · (gram'(u))^{n-1} · gram''(u)`, which is negative for `u`
large (since `gram'(u) > 0` and `gram''(u) ∼ −2π / (u · log² u) < 0`
by Theorem 3 at `n = 2`).  Formalising this is a separate Leibniz +
asymptotic computation, comparable in size to §3.

-- TODO (deferred): two-stage proof —
--   (a) `iteratedDeriv (n+1) (gramPow n)` has leading term
--       `n! · n · (gram')^(n-1) · gram''`, eventually negative;
--   (b) `antitoneOn_of_deriv_nonpos` on the absolute value.
-- ASSUMPTION -/
axiom iteratedDeriv_n_gramPow_n_eventually_antitone (n : ℕ) (_hn : 1 ≤ n) :
    ∃ x₀ : ℝ,
      AntitoneOn (fun u : ℝ => |iteratedDeriv n (gramPow n) u|) (Set.Ici x₀)

/-- A small free corollary: `iteratedDeriv n (gramPow n) u > 0` eventually.
Useful in §6 and §7 and a witness that the §3 asymp axiom is "consistent
with positivity" (which the §4 antitone axiom also tacitly assumes). -/
lemma iteratedDeriv_n_gramPow_n_eventually_pos (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ u : ℝ in atTop, 0 < iteratedDeriv n (gramPow n) u := by
  have hLO : (fun u => iteratedDeriv n (gramPow n) u
                - (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n)
                =o[atTop]
              (fun u => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n) :=
    (iteratedDeriv_n_gramPow_n_isEquivalent n hn).isLittleO
  have hBound := hLO.def (c := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [hBound, eventually_gt_atTop (1 : ℝ)] with u hu hu1
  have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu1
  have hleadingPos : (0 : ℝ) < (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n := by
    refine mul_pos ?_ (pow_pos (by positivity) n)
    exact_mod_cast n.factorial_pos
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hu
  rw [abs_of_pos hleadingPos] at hu
  have := abs_sub_le_iff.mp hu
  linarith

/-! ## §5  Decay to zero (proved) -/

/-- `2π / log u → 0` as `u → ∞`. -/
private lemma tendsto_two_pi_div_log_atTop_zero :
    Tendsto (fun u : ℝ => 2 * Real.pi / Real.log u) atTop (𝓝 0) := by
  have hLog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have h1 : Tendsto (fun u : ℝ => (Real.log u)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLog
  have h2 : Tendsto (fun u : ℝ => 2 * Real.pi * (Real.log u)⁻¹) atTop
      (𝓝 (2 * Real.pi * 0)) := h1.const_mul (2 * Real.pi)
  simp only [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards with u
  rw [div_eq_mul_inv]

/-- `(2π / log u)^n → 0` as `u → ∞`, for `n ≥ 1`. -/
private lemma tendsto_two_pi_div_log_pow_atTop_zero (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun u : ℝ => (2 * Real.pi / Real.log u) ^ n) atTop (𝓝 0) := by
  have h := tendsto_two_pi_div_log_atTop_zero.pow n
  simpa [zero_pow (Nat.one_le_iff_ne_zero.mp hn)] using h

/-- `n! · (2π / log u)^n → 0` as `u → ∞`, for `n ≥ 1`. -/
private lemma tendsto_leading_atTop_zero (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun u : ℝ => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n)
      atTop (𝓝 0) := by
  have h := (tendsto_two_pi_div_log_pow_atTop_zero n hn).const_mul (n.factorial : ℝ)
  simpa using h

/-- The `n`-th derivative of `(gram)^n` tends to `0` as `u → ∞`.

Strategy: transfer through the leading-term asymp from §3
(`iteratedDeriv_n_gramPow_n_isEquivalent`) via `IsEquivalent.symm.tendsto_nhds`;
the leading-term limit is established by the helpers above. -/
lemma iteratedDeriv_n_gramPow_n_tendsto_zero (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun u : ℝ => iteratedDeriv n (gramPow n) u) atTop (𝓝 0) :=
  (iteratedDeriv_n_gramPow_n_isEquivalent n hn).symm.tendsto_nhds
    (tendsto_leading_atTop_zero n hn)

/-! ## §6  `u · |·| → ∞` (proved) -/

/-- `u / (log u)^n → ∞` as `u → ∞`.  Classical: a polynomial in `log u` is
negligible against `u`.  Proof: `(log u)^n =o[atTop] u` (Mathlib's
`Real.isLittleO_pow_log_id_atTop`), hence `(log u)^n / u → 0`, hence its
reciprocal tends to `∞`. -/
private lemma tendsto_id_div_log_pow_atTop_atTop (n : ℕ) :
    Tendsto (fun u : ℝ => u / (Real.log u) ^ n) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ n / x) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have h2 : ∀ᶠ x : ℝ in atTop, 0 < (Real.log x) ^ n / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hpow : 0 < (Real.log x) ^ n := by positivity
    exact div_pos hpow (by linarith)
  have h3 : Tendsto (fun x : ℝ => (Real.log x) ^ n / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h1, h2⟩
  have h4 : Tendsto (fun x : ℝ => ((Real.log x) ^ n / x)⁻¹) atTop atTop :=
    h3.inv_tendsto_nhdsGT_zero
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
  rw [inv_div]

/-- `u · |iteratedDeriv n (gramPow n) u| → ∞` as `u → ∞`.

Strategy.  Let `leading u := n! · (2π/log u)^n`.  From the §3 asymp,
`iteratedDeriv n (gramPow n) - leading = o(leading)`, so applying the
little-o bound at `ε = 1/2` gives `|iteratedDeriv - leading| ≤ leading/2`
eventually; combined with `leading > 0` (for `u > 1`) this forces
`iteratedDeriv ≥ leading/2 > 0`, hence `|iteratedDeriv| = iteratedDeriv ≥
leading/2`.  Then `u · |iteratedDeriv| ≥ u · leading / 2`, and
`u · leading / 2 = (n!·(2π)^n / 2) · (u / log^n u) → ∞` via
`tendsto_id_div_log_pow_atTop_atTop`. -/
lemma mul_iteratedDeriv_n_gramPow_n_tendsto_atTop (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun u : ℝ => u * |iteratedDeriv n (gramPow n) u|) atTop atTop := by
  set leading : ℝ → ℝ :=
    fun u => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n with hLeadDef
  -- u · leading u → ∞.
  have hConstPos : (0 : ℝ) < (n.factorial : ℝ) * (2 * Real.pi) ^ n := by
    refine mul_pos ?_ (pow_pos (by positivity) n)
    exact_mod_cast n.factorial_pos
  have hUmulLeading : Tendsto (fun u : ℝ => u * leading u) atTop atTop := by
    have hCore := tendsto_id_div_log_pow_atTop_atTop n
    have hScaled := hCore.const_mul_atTop hConstPos
    refine hScaled.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu
    have hlogne : Real.log u ≠ 0 := hlog.ne'
    simp only [hLeadDef, div_pow]
    field_simp
  -- (u · leading u) / 2 → ∞.
  have hHalf : Tendsto (fun u : ℝ => u * leading u / 2) atTop atTop :=
    hUmulLeading.atTop_div_const (show (0 : ℝ) < 2 by norm_num)
  -- Eventually `|iteratedDeriv u| ≥ leading u / 2`.
  have hLB : ∀ᶠ u : ℝ in atTop,
      leading u / 2 ≤ |iteratedDeriv n (gramPow n) u| := by
    have hLO : (fun u => iteratedDeriv n (gramPow n) u - leading u)
                  =o[atTop] leading :=
      (iteratedDeriv_n_gramPow_n_isEquivalent n hn).isLittleO
    have hBound := hLO.def (c := (1 / 2 : ℝ)) (by norm_num)
    filter_upwards [hBound, eventually_gt_atTop (1 : ℝ)] with u hu hu1
    have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu1
    have hleadingPos : 0 < leading u := by
      simp only [hLeadDef]
      refine mul_pos ?_ (pow_pos (by positivity) n)
      exact_mod_cast n.factorial_pos
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hu
    rw [abs_of_pos hleadingPos] at hu
    have h1 : leading u - leading u / 2 ≤ iteratedDeriv n (gramPow n) u := by
      have := abs_sub_le_iff.mp hu
      linarith
    have h2 : leading u / 2 ≤ iteratedDeriv n (gramPow n) u := by linarith
    have h3 : 0 < iteratedDeriv n (gramPow n) u := by linarith
    rw [abs_of_pos h3]
    exact h2
  -- Eventually `u · leading u / 2 ≤ u · |iteratedDeriv u|`.
  have hMonoBound : ∀ᶠ u : ℝ in atTop,
      u * leading u / 2 ≤ u * |iteratedDeriv n (gramPow n) u| := by
    filter_upwards [hLB, eventually_gt_atTop (0 : ℝ)] with u hu hu0
    have := mul_le_mul_of_nonneg_left hu hu0.le
    linarith
  -- Conclude.
  exact tendsto_atTop_mono' atTop hMonoBound hHalf

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
    (iteratedDeriv_n_gramPow_n_eventually_antitone n hn)
    (iteratedDeriv_n_gramPow_n_tendsto_zero n hn)
    (mul_iteratedDeriv_n_gramPow_n_tendsto_atTop n hn)

end Gram.Theorem4
