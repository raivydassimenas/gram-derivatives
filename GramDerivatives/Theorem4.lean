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
           `iteratedDeriv_one_gramPow_one_isEquivalent` (§3a, n=1 case
             of the §3 axiom, directly from `gram_deriv_asymp`),
           `theorem4` itself (one-line application of the K–N criterion).
  Axioms (this file):
    • `isUDModOne_of_iteratedDeriv_decay` — the K–N criterion
      (antitone variant).  Permanent: no UD-mod-1 theory in Mathlib.
    • `iteratedDeriv_n_gramPow_n_isEquivalent` — TODO for `n ≥ 2`;
      Leibniz + Theorem 3 + eq. (9).  The `n = 1` case is now proven
      in §3a as a smoke test.
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

### Mathematical content

By the Leibniz formula applied to the product of `n` identical factors,
`d^n/du^n (gram u)^n = Σ_{j_1+⋯+j_n = n} (n! / ∏ j_i!) · ∏ gram^(j_i)(u)`,
where the sum runs over compositions `(j_1, …, j_n)` of `n` into `n`
non-negative integers.

The *unique* leading composition is `(1, 1, …, 1)`, giving the term
`n! · (gram'(u))^n ∼ n! · (2π/log u)^n`  (by `gram_deriv_asymp`).

Every other composition contains at least one `j_i ≥ 2`.  By Theorem 3
and `gram_asymp` (eq. (8)), the magnitudes of the factor types are:
  • `gram^(0)(u)   = gram u            ∼ 2π·u/log u`             — order `u/log u`
  • `gram^(1)(u)   = gram' u           ∼ 2π/log u`                — order `1/log u`
  • `gram^(j)(u)`, `j ≥ 2`             ∼ const · u^(1−j)/(log u)² — order `u^(1−j)/(log u)²`

A short bookkeeping check: for a composition `(j_1, …, j_n)` with `c_j`
parts equal to `j` (so `Σ_j c_j = n` and `Σ_j j·c_j = n`), the term has
order `u^(c_0 − Σ_{j≥2}(j−1)c_j) / (log u)^(c_0 + c_1 + 2·Σ_{j≥2} c_j)`.
The first identity (`Σ_j j·c_j = n`) forces `c_0 = Σ_{j≥2}(j−1)c_j`, so
the `u`-exponent is `0` for every composition.  The `log`-exponent is
`c_0 + c_1 + 2·Σ_{j≥2} c_j = n + Σ_{j≥2} c_j` (using `Σ c_j = n`), so the
order is `1/(log u)^(n + #{i : j_i ≥ 2})`.  The leading
`(1,1,…,1)` composition has `Σ_{j≥2} c_j = 0` and is the unique one of
order `1/(log u)^n`; every other composition is smaller by at least a
factor of `1/log u`.

### Suggested Lean staging (for a future implementer)

  (1) `iteratedDeriv_pow_leibniz` : for `f : ℝ → ℝ`,
      `iteratedDeriv l (fun u => (f u)^n) u
        = Σ over compositions of l into n parts, ...`.
      Induction on `n` using Mathlib's `iteratedDeriv_mul` (or
      `deriv_pow` for the first step + product Leibniz for the rest).

  (2) `gramPow_n_leibniz_split (n)` : split the Leibniz sum at `l = n`
      into the `(1,…,1)` term + remainder.

  (3) `gramPow_n_leibniz_leading_asymp` : the `(1,…,1)` term equals
      `n! · (deriv gram u)^n` and is `IsEquivalent` to
      `n! · (2π/log u)^n` via `gram_deriv_asymp`.

  (4) `gramPow_n_leibniz_remainder_isLittleO` : every other composition
      is `o(leading)` (using Theorem 3 for high-order factors + the
      bookkeeping above).

  (5) Combine (2)–(4) via `IsEquivalent.add_isLittleO` (or hand assembly)
      to derive the §3 asymp.

Stages (1) and (4) are the bulk; estimated several hundred lines of Lean
each, comparable to a mid-size section of `Theorem3.lean`.

-- TODO (deferred): see staging above.
-- ASSUMPTION -/
axiom iteratedDeriv_n_gramPow_n_isEquivalent (n : ℕ) (_hn : 1 ≤ n) :
    IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv n (gramPow n) u)
      (fun u : ℝ => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n)

/-! ### §3a  Special case `n = 1`, proved directly from `gram_deriv_asymp` -/

/-- Auxiliary: `IsEquivalent atTop (iteratedDeriv 1 gram) (fun u => 2π/log u)`.

Strategy.  The Korolev refined asymp `gram_deriv_asymp` (eq. (9)) is
  `(iteratedDeriv 1 gram − A − B) =o[atTop] B`
where `A u := 2π/log u` and `B u := A u · (log log u / log u)`.  Since
`log log u / log u → 0` (compose `log v / v → 0` with `log`), `B =o A`.
Then `(iteratedDeriv 1 gram − A) = (iteratedDeriv 1 gram − A − B) + B`,
and both summands are `=o A`, giving the desired equivalence. -/
private lemma iteratedDeriv_one_gram_isEquivalent :
    IsEquivalent atTop (fun u : ℝ => iteratedDeriv 1 gram u)
      (fun u : ℝ => 2 * Real.pi / Real.log u) := by
  -- log log u / log u → 0
  have hLogLogDiv :
      Tendsto (fun u : ℝ => Real.log (Real.log u) / Real.log u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  -- (log log u / log u) =o[atTop] 1
  have hLLO_one :
      (fun u : ℝ => Real.log (Real.log u) / Real.log u)
        =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hLogLogDiv
  -- B := (2π/log u) · (log log u / log u)  is  =o (2π/log u)
  have hBoA :
      (fun u : ℝ => (2 * Real.pi / Real.log u)
                      * (Real.log (Real.log u) / Real.log u))
        =o[atTop] (fun u : ℝ => 2 * Real.pi / Real.log u) := by
    have h := hLLO_one.mul_isBigO
      (Asymptotics.isBigO_refl (fun u : ℝ => 2 * Real.pi / Real.log u) atTop)
    simpa [one_mul, mul_comm] using h
  -- C := (iteratedDeriv 1 gram − A − B)  =o B  (this is `gram_deriv_asymp`)
  have hCoB :
      (fun u : ℝ => iteratedDeriv 1 gram u
                      - (2 * Real.pi / Real.log u)
                      - (2 * Real.pi / Real.log u)
                          * (Real.log (Real.log u) / Real.log u))
        =o[atTop] (fun u : ℝ => (2 * Real.pi / Real.log u)
                                  * (Real.log (Real.log u) / Real.log u)) :=
    gram_deriv_asymp
  -- Transitivity: C =o A
  have hCoA :
      (fun u : ℝ => iteratedDeriv 1 gram u
                      - (2 * Real.pi / Real.log u)
                      - (2 * Real.pi / Real.log u)
                          * (Real.log (Real.log u) / Real.log u))
        =o[atTop] (fun u : ℝ => 2 * Real.pi / Real.log u) :=
    hCoB.trans hBoA
  -- Reassemble: (iteratedDeriv 1 gram − A) = C + B, both =o A.
  have hFinal :
      ((fun u : ℝ => iteratedDeriv 1 gram u)
        - (fun u : ℝ => 2 * Real.pi / Real.log u))
        =o[atTop] (fun u : ℝ => 2 * Real.pi / Real.log u) := by
    have hAdd :
        ((fun u : ℝ => iteratedDeriv 1 gram u)
          - (fun u : ℝ => 2 * Real.pi / Real.log u))
          = fun u : ℝ =>
              (iteratedDeriv 1 gram u
                - (2 * Real.pi / Real.log u)
                - (2 * Real.pi / Real.log u)
                    * (Real.log (Real.log u) / Real.log u))
              + (2 * Real.pi / Real.log u)
                  * (Real.log (Real.log u) / Real.log u) := by
      funext u
      change iteratedDeriv 1 gram u - 2 * Real.pi / Real.log u = _
      ring
    rw [hAdd]
    exact hCoA.add hBoA
  exact hFinal

/-- Auxiliary: `gramPow 1 = gram` as functions. -/
private lemma gramPow_one_eq_gram : gramPow 1 = (gram : ℝ → ℝ) := by
  funext u; simp [gramPow]

/-- **Special case `n = 1` of §3**, proved directly from `gram_deriv_asymp`
without needing the Leibniz machinery.  Serves as a smoke test that the §3
axiom is well-formed for the simplest case and that the surrounding proof
infrastructure (asymp algebra) works as intended. -/
lemma iteratedDeriv_one_gramPow_one_isEquivalent :
    IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv 1 (gramPow 1) u)
      (fun u : ℝ => ((1 : ℕ).factorial : ℝ) * (2 * Real.pi / Real.log u) ^ 1) := by
  have hLeft : (fun u : ℝ => iteratedDeriv 1 (gramPow 1) u)
                = (fun u : ℝ => iteratedDeriv 1 gram u) := by
    rw [gramPow_one_eq_gram]
  have hRight :
      (fun u : ℝ => ((1 : ℕ).factorial : ℝ) * (2 * Real.pi / Real.log u) ^ 1)
        = (fun u : ℝ => 2 * Real.pi / Real.log u) := by
    funext u; simp
  rw [hLeft, hRight]
  exact iteratedDeriv_one_gram_isEquivalent

/-! ### §3b  Special case `n = 2`, via binary Leibniz + Theorem 3

Step 1 of an inductive proof of §3 by Leibniz expansion.  For `n = 2`,
the binary Leibniz formula (`iteratedDeriv_mul`) applied to
`gramPow 2 u = gram u * gram u` gives

    (gramPow 2)''(u) = 2·gram(u)·gram''(u) + 2·(gram'(u))² .

The lemmas in this sub-section establish (1) the *pointwise* binary-Leibniz
identity and its eventually-true filter form, (2) the leading-term equivalent
`2·(gram'(u))² ~ 2·(2π/log u)²`, (3) the remainder bound
`2·gram(u)·gram''(u) =o[atTop] 2·(gram'(u))²`, and (4) the full §3b smoke test
`iteratedDeriv 2 (gramPow 2) ~ 2! · (2π/log u)²` — i.e. the n = 2 instance of
the §3 magnitude axiom, derived without using it. -/

/-- `gramPow 2 = fun u : ℝ => gram u * gram u`. -/
private lemma gramPow_two_eq_mul :
    (gramPow 2 : ℝ → ℝ) = fun u : ℝ => gram u * gram u := by
  funext u
  simp [gramPow, sq]

/-- **Binary Leibniz at n = 2**: at any `u > gramThreshold`,
    `(gramPow 2)''(u) = 2·gram(u)·gram''(u) + 2·(gram'(u))²`.
Foundation lemma for the n = 2 case of §3, derived directly from
`iteratedDeriv_mul` applied to `gram * gram`. -/
private lemma iteratedDeriv_two_gramPow_two_eq (u : ℝ) (hu : gramThreshold < u) :
    iteratedDeriv 2 (gramPow 2) u
      = 2 * gram u * iteratedDeriv 2 gram u
        + 2 * (iteratedDeriv 1 gram u) ^ 2 := by
  have hContDiff : ContDiffAt ℝ 2 gram u := contDiffAt_gram 2 hu
  rw [gramPow_two_eq_mul]
  rw [iteratedDeriv_fun_mul hContDiff hContDiff]
  -- Unfold the sum over i ∈ range 3.
  rw [show (2 : ℕ) + 1 = 3 from rfl]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
  simp [iteratedDeriv_zero, Nat.choose, sq]
  ring

/-- Eventually-true filter form of `iteratedDeriv_two_gramPow_two_eq`. -/
private lemma iteratedDeriv_two_gramPow_two_eventually_eq :
    (fun u : ℝ => iteratedDeriv 2 (gramPow 2) u)
      =ᶠ[atTop]
      (fun u : ℝ =>
        2 * gram u * iteratedDeriv 2 gram u
          + 2 * (iteratedDeriv 1 gram u) ^ 2) := by
  filter_upwards [eventually_gt_atTop gramThreshold] with u hu
  exact iteratedDeriv_two_gramPow_two_eq u hu

/-- **Leading-term equivalent**: `2 · (gram'(u))² ~ 2 · (2π/log u)²`.
Combine `iteratedDeriv_one_gram_isEquivalent` (from `Theorem3.lean`) with
`IsEquivalent.pow 2` and a `2`-scaling refl. -/
private lemma iteratedDeriv_two_gramPow_two_leading_isEquivalent :
    IsEquivalent atTop
      (fun u : ℝ => 2 * (iteratedDeriv 1 gram u) ^ 2)
      (fun u : ℝ => 2 * (2 * Real.pi / Real.log u) ^ 2) := by
  have hPow := iteratedDeriv_one_gram_isEquivalent.pow 2
  -- hPow : IsEquivalent atTop (iteratedDeriv 1 gram ^ 2)
  --                            ((fun u => 2 * Real.pi / Real.log u) ^ 2)
  have hConst : IsEquivalent atTop
      (fun _ : ℝ => (2 : ℝ)) (fun _ : ℝ => (2 : ℝ)) := IsEquivalent.refl
  have h := hConst.mul hPow
  -- Normalize both sides to pointwise form.
  have hLeftEq : ((fun _ : ℝ => (2 : ℝ)) * iteratedDeriv 1 gram ^ 2 : ℝ → ℝ)
                  = fun u : ℝ => 2 * (iteratedDeriv 1 gram u) ^ 2 := by
    funext u; simp [Pi.mul_apply, Pi.pow_apply]
  have hRightEq :
      ((fun _ : ℝ => (2 : ℝ)) * (fun u : ℝ => 2 * Real.pi / Real.log u) ^ 2 : ℝ → ℝ)
        = fun u : ℝ => 2 * (2 * Real.pi / Real.log u) ^ 2 := by
    funext u; simp [Pi.mul_apply, Pi.pow_apply]
  rw [hLeftEq, hRightEq] at h
  exact h

/-- **Remainder is little-o of leading** at `n = 2`:
`2·gram(u)·gram''(u) =o[atTop] 2·(gram'(u))²`.

Pointwise asymptotic content: `gram·gram'' ~ −4π²/log³u` while `(gram')² ~ 4π²/log²u`,
so the ratio `(gram·gram'')/(gram')²` is `~ −1/log u → 0`.  Closes the §3b smoke test
by showing the non-leading binary-Leibniz term is negligible. -/
private lemma iteratedDeriv_two_gramPow_two_remainder_isLittleO :
    (fun u : ℝ => 2 * gram u * iteratedDeriv 2 gram u)
      =o[atTop] (fun u : ℝ => 2 * (iteratedDeriv 1 gram u) ^ 2) := by
  -- Reassociate the LHS and strip the common constant `2`.
  have hLHS_assoc :
      (fun u : ℝ => 2 * gram u * iteratedDeriv 2 gram u)
        = (fun u : ℝ => 2 * (gram u * iteratedDeriv 2 gram u)) := by
    funext u; ring
  rw [hLHS_assoc,
      Asymptotics.isLittleO_const_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0),
      Asymptotics.isLittleO_const_mul_right_iff (by norm_num : (2 : ℝ) ≠ 0)]
  -- Now: `(gram · gram'') =o (gram')²`.
  -- (A) `gram · gram'' ~ (2π·u/log u) · (−2π/(u·log²u))`.
  have h_mul_eqv : IsEquivalent atTop
      (fun u : ℝ => gram u * iteratedDeriv 2 gram u)
      (fun u : ℝ => (2 * Real.pi * u / Real.log u)
                      * (-(2 * Real.pi) / (u * Real.log u ^ 2))) :=
    gram_isEquivalent.mul iteratedDeriv_two_gram_isEquivalent
  -- (B) `(gram')² ~ (2π/log u)²`.
  have h_sq_eqv : IsEquivalent atTop
      (fun u : ℝ => (iteratedDeriv 1 gram u) ^ 2)
      (fun u : ℝ => (2 * Real.pi / Real.log u) ^ 2) :=
    iteratedDeriv_one_gram_isEquivalent.pow 2
  -- (C) Simplify the LHS shape to `(−(1/log u)) · (2π/log u)²` eventually.
  have hShape_eq :
      (fun u : ℝ => (2 * Real.pi * u / Real.log u)
                      * (-(2 * Real.pi) / (u * Real.log u ^ 2)))
        =ᶠ[atTop]
        (fun u : ℝ => (-(1 / Real.log u)) * (2 * Real.pi / Real.log u) ^ 2) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu1
    have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu1
    have hlogne : Real.log u ≠ 0 := hlog.ne'
    have huNe : (u : ℝ) ≠ 0 := by linarith
    field_simp
  -- (D) `(−(1/log u)) · (2π/log u)² =o (2π/log u)²`.
  have hShape_lo :
      (fun u : ℝ => (-(1 / Real.log u)) * (2 * Real.pi / Real.log u) ^ 2)
        =o[atTop] (fun u : ℝ => (2 * Real.pi / Real.log u) ^ 2) := by
    have h_inv_to : Tendsto (fun u : ℝ => (Real.log u)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have h_one_div_to :
        Tendsto (fun u : ℝ => -(1 / Real.log u)) atTop (𝓝 0) := by
      have := h_inv_to.neg
      simpa [one_div] using this
    have h_small :
        (fun u : ℝ => -(1 / Real.log u)) =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
      (Asymptotics.isLittleO_one_iff ℝ).mpr h_one_div_to
    have h_prod := h_small.mul_isBigO
      (Asymptotics.isBigO_refl (fun u : ℝ => (2 * Real.pi / Real.log u) ^ 2) atTop)
    refine h_prod.trans_eventuallyEq ?_
    filter_upwards with u
    simp
  -- Compose: gram·gram'' ~ LHS-shape =ᶠ simpler-shape =o RHS-shape ~ (gram')².
  exact ((h_mul_eqv.trans_eventuallyEq hShape_eq).trans_isLittleO hShape_lo).trans_isEquivalent
    h_sq_eqv.symm

/-- **Smoke test, `n = 2`**: `iteratedDeriv 2 (gramPow 2) ~ 2! · (2π/log u)²`.

Mirrors `iteratedDeriv_one_gramPow_one_isEquivalent` and serves the same role: a working
`n = 2` instance of the §3 magnitude axiom, derived from `Theorem3.lean`'s public asymp
exports via the binary Leibniz identity (`iteratedDeriv_two_gramPow_two_eventually_eq`),
the leading equivalent (`iteratedDeriv_two_gramPow_two_leading_isEquivalent`), and the
remainder little-o (`iteratedDeriv_two_gramPow_two_remainder_isLittleO`). -/
lemma iteratedDeriv_two_gramPow_two_isEquivalent :
    IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv 2 (gramPow 2) u)
      (fun u : ℝ => ((2 : ℕ).factorial : ℝ) * (2 * Real.pi / Real.log u) ^ 2) := by
  have hLead := iteratedDeriv_two_gramPow_two_leading_isEquivalent
  have hRem_o :
      (fun u : ℝ => 2 * gram u * iteratedDeriv 2 gram u)
        =o[atTop] (fun u : ℝ => 2 * (2 * Real.pi / Real.log u) ^ 2) :=
    iteratedDeriv_two_gramPow_two_remainder_isLittleO.trans_isEquivalent hLead
  -- Combine: 2·gram·gram'' + 2·(gram')² ~ 2·(2π/log u)².
  -- Term order matches `iteratedDeriv_two_gramPow_two_eventually_eq`.
  have h_sum := hRem_o.add_isEquivalent hLead
  -- Transport across the pointwise identity.
  have h_eqv : IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv 2 (gramPow 2) u)
      (fun u : ℝ => 2 * (2 * Real.pi / Real.log u) ^ 2) :=
    iteratedDeriv_two_gramPow_two_eventually_eq.trans_isEquivalent h_sum
  -- Identify `2 = ((2 : ℕ).factorial : ℝ)`.
  have hTarget :
      (fun u : ℝ => 2 * (2 * Real.pi / Real.log u) ^ 2)
        = (fun u : ℝ => ((2 : ℕ).factorial : ℝ)
                          * (2 * Real.pi / Real.log u) ^ 2) := by
    funext u; simp
  rw [← hTarget]
  exact h_eqv

/-! ## §4  Eventual antitone in absolute value (proved, via §4-aux sign axiom) -/

/-- **Sign of the `(n+1)`-th derivative of `(gram)^n`.**

Eventually `iteratedDeriv (n+1) (gramPow n) u ≤ 0`.  This is the analytic
ingredient that turns asymp-equivalence into pointwise antitone
monotonicity: by `antitoneOn_of_deriv_nonpos`, a function with non-positive
derivative is antitone.

Sketch.  By Leibniz the leading term of `d^{n+1}/du^{n+1} (gram u)^n` is
`n! · n · (gram'(u))^{n-1} · gram''(u)`, and from Theorem 3 at order 2,
`gram''(u) ∼ −2π / (u · log² u) < 0` for `u` large.  Hence the leading
term is negative, and the remainder is `o`-of-it, so the whole expression
is eventually non-positive.

-- TODO (deferred): the Leibniz expansion + asymptotic match at order
-- `n + 1`.  Comparable in size to §3 (a separate Leibniz pass) but
-- isolated from §3 itself: the §3 asymp gives the order-`n` magnitude;
-- this axiom gives the order-`(n+1)` sign.
-- ASSUMPTION -/
axiom iteratedDeriv_succ_n_gramPow_n_eventually_nonpos (n : ℕ) (_hn : 1 ≤ n) :
    ∀ᶠ u : ℝ in atTop, iteratedDeriv (n + 1) (gramPow n) u ≤ 0

/-- A small free corollary: `iteratedDeriv n (gramPow n) u > 0` eventually.
Used by §4 to identify `|iteratedDeriv n …|` with `iteratedDeriv n …` on a
tail, and by §6 to lower-bound the latter by half the §3-leading.  A
witness that the §3 asymp axiom is "consistent with positivity" (which
the §4 sign axiom also tacitly assumes). -/
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

/-- The `n`-th derivative of `(gram)^n` is **eventually antitone** in
absolute value: `|iteratedDeriv n (gramPow n) ·|` is decreasing on a tail.

Proof.  On a sufficiently far tail `[x₀, ∞)`:
  • `iteratedDeriv n (gramPow n) u > 0` (`eventually_pos` from §3 asymp);
    so `|·| = iteratedDeriv n (gramPow n)` there.
  • `iteratedDeriv (n+1) (gramPow n) u ≤ 0` (the sign axiom above);
    this is `deriv (iteratedDeriv n (gramPow n)) u ≤ 0` by
    `iteratedDeriv_succ`.
  • `iteratedDeriv n (gramPow n)` is continuous and differentiable on the
    tail (`gramPow n` is `C^∞` on `(gramThreshold, ∞)` via `contDiffAt_gramPow`).
Apply `antitoneOn_of_deriv_nonpos` to conclude `AntitoneOn (iteratedDeriv n …)`
on `[x₀, ∞)`, then transport to `|·|` via the positivity identity. -/
lemma iteratedDeriv_n_gramPow_n_eventually_antitone (n : ℕ) (hn : 1 ≤ n) :
    ∃ x₀ : ℝ,
      AntitoneOn (fun u : ℝ => |iteratedDeriv n (gramPow n) u|) (Set.Ici x₀) := by
  -- Extract witness points for the three eventual conditions.
  obtain ⟨x_d, hx_d⟩ := eventually_atTop.mp
    (iteratedDeriv_succ_n_gramPow_n_eventually_nonpos n hn)
  obtain ⟨x_p, hx_p⟩ := eventually_atTop.mp
    (iteratedDeriv_n_gramPow_n_eventually_pos n hn)
  set x₀ : ℝ := max (max x_d x_p) (gramThreshold + 1) with hx₀_def
  refine ⟨x₀, ?_⟩
  -- Bookkeeping bounds on x₀.
  have hx₀_gt_gramT : gramThreshold < x₀ := by
    have h1 : gramThreshold + 1 ≤ x₀ := le_max_right _ _
    linarith
  have hx₀_ge_xd : x_d ≤ x₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hx₀_ge_xp : x_p ≤ x₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  -- Positivity of `iteratedDeriv n` on `[x₀, ∞)`.
  have hPos : ∀ u ∈ Set.Ici x₀, 0 < iteratedDeriv n (gramPow n) u := fun u hu =>
    hx_p u (le_trans hx₀_ge_xp hu)
  -- `|iteratedDeriv n| = iteratedDeriv n` on `[x₀, ∞)`.
  have hAbsEq : Set.EqOn (fun u : ℝ => |iteratedDeriv n (gramPow n) u|)
                          (fun u : ℝ => iteratedDeriv n (gramPow n) u)
                          (Set.Ici x₀) := fun u hu => abs_of_pos (hPos u hu)
  -- Non-positivity of `iteratedDeriv (n+1)` on `(x₀, ∞)`.
  have hNonPos : ∀ u ∈ Set.Ioi x₀,
      iteratedDeriv (n + 1) (gramPow n) u ≤ 0 := fun u hu =>
    hx_d u (le_trans hx₀_ge_xd hu.le)
  -- Smoothness scaffolding.
  have hUDiff : UniqueDiffOn ℝ (Set.Ioi gramThreshold) := isOpen_Ioi.uniqueDiffOn
  have hContDiffOn : ContDiffOn ℝ ((n : ℕ) + 2) (gramPow n) (Set.Ioi gramThreshold) :=
    fun u hu => (contDiffAt_gramPow n (n + 2) hu).contDiffWithinAt
  have hLE : ((n : ℕ) : WithTop ℕ∞) ≤ ((n + 2 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_add_right n 2
  have hLT : ((n : ℕ) : WithTop ℕ∞) < ((n + 2 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : n < n + 2)
  have hContWithin :
      ContinuousOn (iteratedDerivWithin n (gramPow n) (Set.Ioi gramThreshold))
                    (Set.Ioi gramThreshold) :=
    hContDiffOn.continuousOn_iteratedDerivWithin hLE hUDiff
  have hDiffWithin :
      DifferentiableOn ℝ
        (iteratedDerivWithin n (gramPow n) (Set.Ioi gramThreshold))
        (Set.Ioi gramThreshold) :=
    hContDiffOn.differentiableOn_iteratedDerivWithin hLT hUDiff
  -- `iteratedDerivWithin n (...) (Ioi gramThreshold) = iteratedDeriv n (...)` on the set.
  have hEqOn : Set.EqOn
      (iteratedDerivWithin n (gramPow n) (Set.Ioi gramThreshold))
      (iteratedDeriv n (gramPow n))
      (Set.Ioi gramThreshold) :=
    iteratedDerivWithin_of_isOpen isOpen_Ioi
  have hCont_on_Ioi :
      ContinuousOn (iteratedDeriv n (gramPow n)) (Set.Ioi gramThreshold) :=
    hContWithin.congr hEqOn.symm
  have hDiff_on_Ioi :
      DifferentiableOn ℝ (iteratedDeriv n (gramPow n)) (Set.Ioi gramThreshold) := by
    intro u hu
    have h := hDiffWithin u hu
    -- Transport via the EqOn (within = plain on open set).
    refine h.congr (fun v hv => (hEqOn hv).symm) (hEqOn hu).symm
  -- Restrict to `Ici x₀ ⊆ Ioi gramThreshold`.
  have hSubset : Set.Ici x₀ ⊆ Set.Ioi gramThreshold := fun u hu =>
    lt_of_lt_of_le hx₀_gt_gramT hu
  have hSubset' : Set.Ioi x₀ ⊆ Set.Ioi gramThreshold := fun u hu =>
    lt_trans hx₀_gt_gramT hu
  have hContIci :
      ContinuousOn (iteratedDeriv n (gramPow n)) (Set.Ici x₀) :=
    hCont_on_Ioi.mono hSubset
  have hDiffInterior :
      DifferentiableOn ℝ (iteratedDeriv n (gramPow n)) (interior (Set.Ici x₀)) := by
    rw [interior_Ici]
    exact hDiff_on_Ioi.mono hSubset'
  -- Antitone on `[x₀, ∞)` via `antitoneOn_of_deriv_nonpos`.
  have hAntit : AntitoneOn (iteratedDeriv n (gramPow n)) (Set.Ici x₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici x₀) hContIci hDiffInterior ?_
    intro u hu
    rw [interior_Ici] at hu
    rw [show deriv (iteratedDeriv n (gramPow n)) u
            = iteratedDeriv (n + 1) (gramPow n) u from
            (congrArg (· u) iteratedDeriv_succ.symm)]
    exact hNonPos u hu
  -- Transport antitone from `iteratedDeriv n` to `|iteratedDeriv n|` via positivity.
  exact hAntit.congr hAbsEq.symm

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
