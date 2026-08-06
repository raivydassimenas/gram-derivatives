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
  Complete, no `sorry`.
  Proved:  `contDiffAt_gramPow`, `eventually_contDiffAt_gramPow`,
           `iteratedDeriv_n_gramPow_n_isEquivalent` (§3 magnitude, ALL `n`;
             Faà di Bruno on `(·^n) ∘ gram` + Theorem 3 — see §3c),
           `iteratedDeriv_succ_gramPow_isEquivalent` (§3d sign asymptotic,
             ALL `n`: `(gram^n)^{(n+1)} ~ −n·n!·(2π)^n/(u·log^{n+1}u)`;
             order-`(n+1)` Faà di Bruno + `extendEquiv` signed count),
           `iteratedDeriv_succ_n_gramPow_n_eventually_nonpos` (§4 sign,
             formerly an axiom),
           `iteratedDeriv_n_gramPow_n_tendsto_zero`,
           `mul_iteratedDeriv_n_gramPow_n_tendsto_atTop`,
           `iteratedDeriv_n_gramPow_n_eventually_pos` (helper),
           `iteratedDeriv_n_gramPow_n_eventually_antitone` (§4),
           `iteratedDeriv_one_gramPow_one_isEquivalent` (§3a, n=1 smoke test),
           `iteratedDeriv_two_gramPow_two_isEquivalent` (§3b, n=2 smoke test),
           `iteratedDeriv_two_gramPow_one_eventually_nonpos` (§3d.0, n=1),
           `iteratedDeriv_three_gramPow_two_isEquivalent` (§3d.1, n=2),
           `theorem4` itself (one-line application of the K–N criterion).
  Axioms (this file): **none**.  The K–N criterion
  `isUDModOne_of_iteratedDeriv_decay` (antitone variant), formerly the
  project's last axiom, is now a theorem delegating to
  `Gram.UD.isUDModOne_of_iteratedDeriv_decay` in `Fejer.lean`.
-/

import GramDerivatives.Fejer
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

Formerly the project's last `-- ASSUMPTION` axiom; now a theorem, proved in
`Fejer.lean` (discrete Fejér theorem + mean value theorem + van der Corput's
difference theorem). -/
theorem isUDModOne_of_iteratedDeriv_decay
    (f : ℝ → ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hC : ∀ᶠ u : ℝ in atTop, ContDiffAt ℝ l f u)
    (hmono : ∃ x₀ : ℝ,
        AntitoneOn (fun t : ℝ => |iteratedDeriv l f t|) (Set.Ici x₀))
    (h0 : Tendsto (fun u : ℝ => iteratedDeriv l f u) atTop (𝓝 0))
    (hInf : Tendsto (fun u : ℝ => u * |iteratedDeriv l f u|) atTop atTop) :
    Gram.UD.IsUDModOne (fun k : ℕ => f k) :=
  Gram.UD.isUDModOne_of_iteratedDeriv_decay f l hl hC hmono h0 hInf

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

/-! ## §3  Leading-term asymptotic (proved)

The leading-term asymptotic `iteratedDeriv n (gramPow n) u ~ n!·(2π/log u)^n`
is now **proved** (no longer an axiom) as
`iteratedDeriv_n_gramPow_n_isEquivalent` in §3c.3 below, via the Faà di Bruno
expansion of `(·^n) ∘ gram` (`faadi_bruno_gramPow`).  The unique length-`n`
(atomic) partition supplies the leading term `n!·(gram'(u))^n`; every other
partition has a part of size `≥ 2` and is `o(leading)` by Theorem 3.

Sections §3a (`n = 1`) and §3b (`n = 2`) remain as standalone smoke tests, now
strict special cases of the general lemma. -/

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

/-! ### §3c  General case `n ≥ 2`, via Faà di Bruno + Theorem 3

Discharges the §3 magnitude axiom for all `n`.  Writing `gramPow n = (·^n) ∘ gram`
and applying Mathlib's Faà di Bruno formula
(`iteratedDeriv_comp_eq_sum_orderedFinpartition`) expands `(gram^n)^(n)` as a sum
over `OrderedFinpartition n`.  The atomic partition (all parts of size `1`) gives
the leading term `n!·(gram'(u))^n`; every other partition has a part of size `≥ 2`
and contributes `o` of the leading term by Theorem 3. -/

/-- **Faà di Bruno expansion, general order**: at `u > gramThreshold`,

    `iteratedDeriv m (gramPow n) u
       = ∑ c : OrderedFinpartition m,
           n.descFactorial c.length · (gram u)^(n − c.length)
             · ∏ j, iteratedDeriv (c.partSize j) gram u`.

The derivative order `m` is independent of the power `n`; the §3 magnitude
lemma uses `m = n`, the §3d sign analysis `m = n + 1`.  Terms with
`c.length > n` vanish because `n.descFactorial c.length = 0` there. -/
private lemma faadi_bruno_pow_gram (n m : ℕ) (u : ℝ) (hu : gramThreshold < u) :
    iteratedDeriv m (gramPow n) u
      = ∑ c : OrderedFinpartition m,
          (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u := by
  have hcomp_fun : (gramPow n : ℝ → ℝ) = (fun x : ℝ => x ^ n) ∘ gram := by
    funext x; rfl
  have hg : ContDiffAt ℝ m (fun x : ℝ => x ^ n) (gram u) := contDiffAt_id.pow n
  have hf : ContDiffAt ℝ m gram u := contDiffAt_gram m hu
  rw [hcomp_fun, iteratedDeriv_comp_eq_sum_orderedFinpartition hg hf le_rfl]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [iteratedDeriv_pow]

/-- **Faà di Bruno expansion** of `(gram^n)^(n)` at `u > gramThreshold`:
the `m = n` instance of `faadi_bruno_pow_gram`. -/
private lemma faadi_bruno_gramPow (n : ℕ) (u : ℝ) (hu : gramThreshold < u) :
    iteratedDeriv n (gramPow n) u
      = ∑ c : OrderedFinpartition n,
          (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u :=
  faadi_bruno_pow_gram n n u hu

/-- Eventually-true filter form of `faadi_bruno_gramPow`. -/
private lemma faadi_bruno_gramPow_eventually (n : ℕ) :
    (fun u : ℝ => iteratedDeriv n (gramPow n) u)
      =ᶠ[atTop]
      (fun u : ℝ =>
        ∑ c : OrderedFinpartition n,
          (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u) := by
  filter_upwards [eventually_gt_atTop gramThreshold] with u hu
  exact faadi_bruno_gramPow n u hu

/-- `(Real.log u)⁻¹ → 0` as `u → ∞`. -/
private lemma tendsto_inv_log_atTop_zero :
    Tendsto (fun u : ℝ => (Real.log u)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop

/-- `(Real.log u)⁻¹ =o[atTop] 1`. -/
private lemma inv_log_isLittleO_one :
    (fun u : ℝ => (Real.log u)⁻¹) =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
  (Asymptotics.isLittleO_one_iff ℝ).mpr tendsto_inv_log_atTop_zero

/-- **Sharp weak bound, `s ≥ 2`.**  `iteratedDeriv s gram =o[atTop] (u⁻¹)^(s−1)·(log u)⁻¹`.

The Theorem 3 monomial is `C·u^(1−s)/log²u = (C/log u)·[(u⁻¹)^(s−1)·(log u)⁻¹]`, and the
coefficient `C/log u → 0`, so the derivative is `o` of the weak bound. -/
private lemma iteratedDeriv_gram_isLittleO_weak (s : ℕ) (hs : 2 ≤ s) :
    (fun u : ℝ => iteratedDeriv s gram u)
      =o[atTop] (fun u : ℝ => (u⁻¹) ^ (s - 1) * (Real.log u)⁻¹) := by
  refine (iteratedDeriv_n_gram_isEquivalent s hs).trans_isLittleO ?_
  set C : ℝ := (-1 : ℝ) ^ (s + 1) * (2 * Real.pi) * ((s - 2).factorial : ℝ) with hC
  -- coefficient `C·(log u)⁻¹` is `=o 1`.
  have hcoeff : (fun u : ℝ => C * (Real.log u)⁻¹) =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    inv_log_isLittleO_one.const_mul_left C
  have hmul := hcoeff.mul_isBigO (Asymptotics.isBigO_refl
    (fun u : ℝ => (u⁻¹ : ℝ) ^ (s - 1) * (Real.log u)⁻¹) atTop)
  -- hmul : (fun u => (C·(log u)⁻¹)·((u⁻¹)^(s-1)·(log u)⁻¹)) =o (fun u => 1·((u⁻¹)^(s-1)·(log u)⁻¹))
  have hsimp : (fun u : ℝ => (1 : ℝ) * ((u⁻¹ : ℝ) ^ (s - 1) * (Real.log u)⁻¹))
                = (fun u : ℝ => (u⁻¹ : ℝ) ^ (s - 1) * (Real.log u)⁻¹) := by
    funext u; rw [one_mul]
  rw [hsimp] at hmul
  refine Filter.EventuallyEq.trans_isLittleO ?_ hmul
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu1
  have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu1
  have hune : (u : ℝ) ≠ 0 := by linarith
  have hlne : Real.log u ≠ 0 := hlog.ne'
  rw [inv_pow]
  field_simp

/-- **Weak uniform derivative bound.**  For every part size `s ≥ 1`,
`iteratedDeriv s gram =O[atTop] (u⁻¹)^(s−1) · (log u)⁻¹`.

For `s = 1` this is Korolev's `gram' ~ 2π/log u`; for `s ≥ 2` it follows from
`iteratedDeriv_gram_isLittleO_weak`. -/
private lemma iteratedDeriv_gram_isBigO_weak (s : ℕ) (hs : 1 ≤ s) :
    (fun u : ℝ => iteratedDeriv s gram u)
      =O[atTop] (fun u : ℝ => (u⁻¹) ^ (s - 1) * (Real.log u)⁻¹) := by
  rcases Nat.lt_or_ge s 2 with hs1 | hs2
  · -- s = 1
    obtain rfl : s = 1 := by omega
    refine iteratedDeriv_one_gram_isEquivalent.isBigO.trans ?_
    have hpow : (fun u : ℝ => (u⁻¹ : ℝ) ^ (1 - 1) * (Real.log u)⁻¹)
            = (fun u : ℝ => (Real.log u)⁻¹) := by funext u; simp
    rw [hpow]
    refine (isBigO_const_mul_self (2 * Real.pi) (fun u : ℝ => (Real.log u)⁻¹) atTop).congr_left ?_
    intro u; rw [div_eq_mul_inv]
  · exact (iteratedDeriv_gram_isLittleO_weak s hs2).isBigO

/-- **Sharp big-part O-bound, `s ≥ 2`**:
`iteratedDeriv s gram =O[atTop] (u⁻¹)^(s−1) · ((log u)⁻¹)²`.

Strengthens `iteratedDeriv_gram_isBigO_weak` by the true second log factor of
Theorem 3.  At order `n` (§3c) the single-log weak bound suffices, but at
order `n + 1` (§3d) the subdominant classes are only one log below the
dominant one, so the sharp form is needed. -/
private lemma iteratedDeriv_gram_isBigO_sharp (s : ℕ) (hs : 2 ≤ s) :
    (fun u : ℝ => iteratedDeriv s gram u)
      =O[atTop] (fun u : ℝ => (u⁻¹) ^ (s - 1) * ((Real.log u)⁻¹) ^ 2) := by
  refine (iteratedDeriv_n_gram_isEquivalent s hs).isBigO.trans ?_
  have heq :
      (fun u : ℝ => (-1 : ℝ) ^ (s + 1) * (2 * Real.pi) * ((s - 2).factorial : ℝ)
          / (u ^ (s - 1) * Real.log u ^ 2))
        = fun u : ℝ => ((-1 : ℝ) ^ (s + 1) * (2 * Real.pi) * ((s - 2).factorial : ℝ))
            * ((u⁻¹) ^ (s - 1) * ((Real.log u)⁻¹) ^ 2) := by
    funext u
    rw [div_eq_mul_inv, mul_inv, ← inv_pow, ← inv_pow]
  rw [heq]
  exact isBigO_const_mul_self _ _ atTop

/-! ### §3c.1  Combinatorial facts about `OrderedFinpartition` -/

/-- The part sizes of an ordered finpartition of `Fin n` sum to `n`. -/
private lemma orderedFinpartition_sum_partSize (n : ℕ) (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  have h := Fintype.card_congr c.equivSigma
  rw [Fintype.card_sigma, Fintype.card_fin] at h
  simpa [Fintype.card_fin] using h

/-- A strictly monotone self-map of `Fin n` is the identity. -/
private lemma strictMono_fin_eq_id {n : ℕ} (f : Fin n → Fin n) (hf : StrictMono f) (i : Fin n) :
    f i = i := by
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf.injective
  have hcoe : ((StrictMono.orderIsoOfSurjective f hf hsurj) i : ℕ) = (i : ℕ) :=
    Fin.coe_orderIso_apply _ i
  exact Fin.ext hcoe

/-- **`atomic` is the unique length-`n` ordered finpartition of `Fin n`.**
A finpartition of `Fin n` into exactly `n` parts must have every part a
singleton, and the ordering constraint then forces the embeddings to be the
identity. -/
private lemma orderedFinpartition_eq_atomic_of_length (n : ℕ)
    (c : OrderedFinpartition n) (hlen : c.length = n) :
    c = OrderedFinpartition.atomic n := by
  -- Every part has size 1.
  have hps1 : ∀ i, c.partSize i = 1 := by
    have hsum := orderedFinpartition_sum_partSize n c
    have hcard : Fintype.card (Fin c.length) = n := by rw [Fintype.card_fin, hlen]
    have e1 : ∑ i, c.partSize i = ∑ i : Fin c.length, ((c.partSize i - 1) + 1) :=
      Finset.sum_congr rfl (fun i _ => (Nat.sub_add_cancel (c.partSize_pos i)).symm)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul,
      mul_one] at e1
    have hzero : ∑ i, (c.partSize i - 1) = 0 := by omega
    intro i
    have hi := (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
    have hpos := c.partSize_pos i
    omega
  -- Destructure and substitute `length = n`.
  obtain ⟨len, partSize, hpos, emb, hembmono, hpartsmono, hdisj, hcov⟩ := c
  obtain rfl : len = n := hlen
  obtain rfl : partSize = fun _ => 1 := funext hps1
  -- The "largest-element" map is `m ↦ emb m 0`; it is strictly monotone, hence the identity.
  have hg : ∀ m : Fin len, emb m ⟨0, Nat.one_pos⟩ = m := by
    have hmono : StrictMono (fun m : Fin len => emb m ⟨0, Nat.one_pos⟩) := hpartsmono
    exact fun m => strictMono_fin_eq_id _ hmono m
  obtain rfl : emb = fun m _ => m := by
    funext m j
    have hj : j = ⟨0, Nat.one_pos⟩ := Subsingleton.elim _ _
    rw [hj]; exact hg m
  rfl

/-- Two nonzero-constant multiples of the same function are `=O` of each other. -/
private lemma isBigO_const_mul_const_mul (a b : ℝ) (hb : b ≠ 0) (f : ℝ → ℝ) :
    (fun u : ℝ => a * f u) =O[atTop] (fun u : ℝ => b * f u) := by
  have hrw : (fun u : ℝ => a * f u) = (fun u : ℝ => a / b * (b * f u)) := by
    funext u
    rw [show a / b * (b * f u) = a / b * b * f u from by ring, div_mul_cancel₀ a hb]
  rw [hrw]
  exact isBigO_const_mul_self (a / b) (fun u : ℝ => b * f u) atTop

/-! ### §3c.2  Non-leading partition terms are little-o of the leading term -/

/-- **A non-leading Faà di Bruno term is `o(leading)`.**  If `c` has at least one
part of size `≥ 2`, the corresponding term
`n.descFactorial c.length · (gram u)^(n−c.length) · ∏ⱼ gram^(c.partSize j)(u)`
is `o[atTop]` of `n!·(2π/log u)^n`.

The decay comes entirely from the size-`≥2` part: by the weak uniform bound every
factor is `O((u⁻¹)^(sⱼ−1)·(log u)⁻¹)`, and the distinguished part is `o` of its weak
bound (`iteratedDeriv_gram_isLittleO_weak`).  The `u`-powers cancel (`∑(sⱼ−1) = n−len`),
so the comparison product is `Θ((log u)⁻¹ⁿ) = Θ(leading)`. -/
private lemma orderedFinpartition_term_isLittleO (n : ℕ)
    (c : OrderedFinpartition n) (hc : ∃ i, 2 ≤ c.partSize i) :
    (fun u : ℝ => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
        * ∏ j, iteratedDeriv (c.partSize j) gram u)
      =o[atTop] (fun u : ℝ => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n) := by
  obtain ⟨i₀, hi₀⟩ := hc
  -- Exponent bookkeeping.
  have hsumsub : ∑ j, (c.partSize j - 1) = n - c.length := by
    have hsum := orderedFinpartition_sum_partSize n c
    have e1 : ∑ i, ((c.partSize i - 1) + 1) = ∑ i, c.partSize i :=
      Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (c.partSize_pos i))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, hsum] at e1
    omega
  have hnm : (n - c.length) + c.length = n := Nat.sub_add_cancel c.length_le
  -- (1) gram^(n-len) =O (2π u/log u)^(n-len).
  have hgramO : (fun u : ℝ => (gram u) ^ (n - c.length))
      =O[atTop] (fun u : ℝ => (2 * Real.pi * u / Real.log u) ^ (n - c.length)) :=
    (gram_isEquivalent.pow (n - c.length)).isBigO
  -- (2) ∏ deriv =o ∏ weakbound.
  have hprodo : (fun u : ℝ => ∏ j, iteratedDeriv (c.partSize j) gram u)
      =o[atTop] (fun u : ℝ => ∏ j, ((u⁻¹) ^ (c.partSize j - 1) * (Real.log u)⁻¹)) := by
    refine IsLittleO.finsetProd (fun j _ =>
      iteratedDeriv_gram_isBigO_weak (c.partSize j) (c.partSize_pos j)) ?_
    exact ⟨i₀, Finset.mem_univ i₀, iteratedDeriv_gram_isLittleO_weak (c.partSize i₀) hi₀⟩
  -- (3) product little-o.
  have hmul := hgramO.mul_isLittleO hprodo
  -- (4) the comparison product is =O leading.
  have hQO :
      (fun u : ℝ => (2 * Real.pi * u / Real.log u) ^ (n - c.length)
          * ∏ j, ((u⁻¹) ^ (c.partSize j - 1) * (Real.log u)⁻¹))
        =O[atTop] (fun u : ℝ => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n) := by
    -- Simplify the comparison product to `(2π)^(n-len) · (log u)⁻¹^n`.
    have hQeq :
        (fun u : ℝ => (2 * Real.pi * u / Real.log u) ^ (n - c.length)
            * ∏ j, ((u⁻¹) ^ (c.partSize j - 1) * (Real.log u)⁻¹))
          =ᶠ[atTop]
          (fun u : ℝ => (2 * Real.pi) ^ (n - c.length) * (Real.log u)⁻¹ ^ n) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu1
      have hlog : 0 < Real.log u := Real.log_pos hu1
      have hune : (u : ℝ) ≠ 0 := by linarith
      have hlne : Real.log u ≠ 0 := hlog.ne'
      have hpowmerge : (Real.log u)⁻¹ ^ (n - c.length) * (Real.log u)⁻¹ ^ c.length
          = (Real.log u)⁻¹ ^ n := by rw [← pow_add, hnm]
      have hbase : (2 * Real.pi * u / Real.log u) * u⁻¹ = 2 * Real.pi * (Real.log u)⁻¹ := by
        field_simp
      have hstep : (2 * Real.pi * u / Real.log u) ^ (n - c.length) * u⁻¹ ^ (n - c.length)
          = (2 * Real.pi) ^ (n - c.length) * (Real.log u)⁻¹ ^ (n - c.length) := by
        rw [← mul_pow, hbase, mul_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsumsub, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, ← mul_assoc, hstep, mul_assoc, hpowmerge]
    refine hQeq.trans_isBigO ?_
    -- leading = (n! · (2π)^n) · (log u)⁻¹^n.
    have hlead_eq :
        (fun u : ℝ => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n)
          = (fun u : ℝ => ((n.factorial : ℝ) * (2 * Real.pi) ^ n) * (Real.log u)⁻¹ ^ n) := by
      funext u; simp only [div_eq_mul_inv, mul_pow]; ring
    rw [hlead_eq]
    refine isBigO_const_mul_const_mul _ _ ?_ _
    have : (0 : ℝ) < (n.factorial : ℝ) * (2 * Real.pi) ^ n := by positivity
    exact this.ne'
  -- Assemble.
  have hgoal_eq :
      (fun u : ℝ => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u)
        = (fun u : ℝ => (n.descFactorial c.length : ℝ) * ((gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u)) := by
    funext u; ring
  rw [hgoal_eq]
  exact (hmul.const_mul_left (n.descFactorial c.length : ℝ)).trans_isBigO hQO

/-! ### §3c.3  The §3 magnitude lemma, assembled -/

/-- **§3 magnitude lemma (general `n`).**  For every `n ≥ 1`,

    `iteratedDeriv n (gramPow n) u ~ n!·(2π/log u)^n`  as `u → +∞`.

For `n = 1` this is `iteratedDeriv_one_gramPow_one_isEquivalent`.  For `n ≥ 2`,
the Faà di Bruno expansion `faadi_bruno_gramPow_eventually` splits off the
unique length-`n` (atomic) partition, whose term is `n!·(gram'(u))^n ~ leading`;
every other partition has a part of size `≥ 2` and is `o(leading)`
(`orderedFinpartition_term_isLittleO`). -/
lemma iteratedDeriv_n_gramPow_n_isEquivalent (n : ℕ) (hn : 1 ≤ n) :
    IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv n (gramPow n) u)
      (fun u : ℝ => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    exact iteratedDeriv_one_gramPow_one_isEquivalent
  · set leading : ℝ → ℝ :=
      fun u => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n with hlead
    set term : OrderedFinpartition n → ℝ → ℝ :=
      fun c u => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
        * ∏ j, iteratedDeriv (c.partSize j) gram u with hterm
    -- The atomic term is `n!·(gram')^n`, equivalent to `leading`.
    have hatom : IsEquivalent atTop (term (OrderedFinpartition.atomic n)) leading := by
      have hval : term (OrderedFinpartition.atomic n)
          = fun u : ℝ => (n.factorial : ℝ) * (iteratedDeriv 1 gram u) ^ n := by
        funext u
        rw [hterm]
        simp only [OrderedFinpartition.atomic_partSize]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          OrderedFinpartition.atomic_length, Nat.descFactorial_self, Nat.sub_self,
          pow_zero, mul_one]
      rw [hval, hlead]
      have hPow := iteratedDeriv_one_gram_isEquivalent.pow n
      have hConst : IsEquivalent atTop (fun _ : ℝ => (n.factorial : ℝ))
          (fun _ : ℝ => (n.factorial : ℝ)) := IsEquivalent.refl
      have h := hConst.mul hPow
      have hLeftEq :
          ((fun _ : ℝ => (n.factorial : ℝ)) * iteratedDeriv 1 gram ^ n : ℝ → ℝ)
            = fun u : ℝ => (n.factorial : ℝ) * (iteratedDeriv 1 gram u) ^ n := by
        funext u; simp [Pi.mul_apply, Pi.pow_apply]
      have hRightEq :
          ((fun _ : ℝ => (n.factorial : ℝ))
              * (fun u : ℝ => 2 * Real.pi / Real.log u) ^ n : ℝ → ℝ)
            = fun u : ℝ => (n.factorial : ℝ) * (2 * Real.pi / Real.log u) ^ n := by
        funext u; simp [Pi.mul_apply, Pi.pow_apply]
      rw [hLeftEq, hRightEq] at h
      exact h
    -- Every non-atomic term is `o(leading)`, so their sum is `o(leading)`.
    have hrem : (fun u : ℝ =>
          ∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic n), term c u)
        =o[atTop] leading := by
      refine IsLittleO.sum ?_
      intro c hcmem
      have hc2 : ∃ i, 2 ≤ c.partSize i := by
        by_contra h
        simp only [not_exists, not_le] at h
        have hps1 : ∀ i, c.partSize i = 1 := fun i => by
          have h1 := c.partSize_pos i; have h2 := h i; omega
        have hlen : c.length = n := by
          have hsum := orderedFinpartition_sum_partSize n c
          have hcl : ∑ i, c.partSize i = c.length := by
            rw [Finset.sum_congr rfl (fun i _ => hps1 i), Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, smul_eq_mul, mul_one]
          exact hcl.symm.trans hsum
        exact (Finset.mem_erase.mp hcmem).1
          (orderedFinpartition_eq_atomic_of_length n c hlen)
      exact orderedFinpartition_term_isLittleO n c hc2
    -- Split the Faà di Bruno sum, combine, and transport.
    have hsplit : (fun u : ℝ => ∑ c : OrderedFinpartition n, term c u)
        = fun u : ℝ => (∑ c ∈ Finset.univ.erase (OrderedFinpartition.atomic n), term c u)
            + term (OrderedFinpartition.atomic n) u := by
      funext u
      exact (Finset.sum_erase_add Finset.univ (fun c => term c u)
        (Finset.mem_univ (OrderedFinpartition.atomic n))).symm
    have hres : IsEquivalent atTop
        (fun u : ℝ => ∑ c : OrderedFinpartition n, term c u) leading := by
      rw [hsplit]; exact hrem.add_isEquivalent hatom
    exact (faadi_bruno_gramPow_eventually n).trans_isEquivalent hres

/-! ### §3d  Sign of the `(n+1)`-th derivative of `gramPow n`

Machinery for the §4 sign lemma
`iteratedDeriv_succ_n_gramPow_n_eventually_nonpos` (formerly an axiom).
Main result (§3d.5):

    `iteratedDeriv (n+1) (gramPow n) u ~ −n·n!·(2π)^n / (u·(log u)^(n+1))`.

Note: in the order-`(n+1)`
Faà di Bruno expansion of `(gram^n)^{(n+1)}`, *every* partition with exactly
one part of size `s ≥ 2` (and singletons elsewhere) contributes at the same
order `u⁻¹·(log u)^{−(n+1)}`, with alternating sign `(−1)^{s+1}`; the
`u`-exponent is `−1` for every non-vanishing partition.  The aggregate
constant is `n!·(2π)^n · ∑_{s=2}^{n+1} (−1)^{s+1}·C(n+1,s) = −n·n!·(2π)^n`,
negative as required.  Partitions with `≥ 2` big parts decay one log faster
and are negligible; partitions with `> n` parts vanish because the outer
function is the degree-`n` monomial (`descFactorial = 0`). -/

/-! #### §3d.0  Sign-transfer helper and smoke tests (`n = 1`, `n = 2`) -/

/-- If `f ~ g` along `atTop` and `g` is eventually negative, then `f` is
eventually non-positive.  Sign-transfer helper: reduces the §4 sign lemma to
the §3d leading-term equivalence. -/
private lemma eventually_nonpos_of_isEquivalent {f g : ℝ → ℝ}
    (h : IsEquivalent atTop f g) (hg : ∀ᶠ u : ℝ in atTop, g u < 0) :
    ∀ᶠ u : ℝ in atTop, f u ≤ 0 := by
  have hBound := h.isLittleO.def (c := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [hBound, hg] with u hu hgu
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hgu] at hu
  have := abs_sub_le_iff.mp hu
  linarith [this.1, this.2]

/-- **Sign smoke test, `n = 1`**: `iteratedDeriv 2 (gramPow 1) ~ −2π/(u·log²u)`.
Direct from `iteratedDeriv_two_gram_isEquivalent` since `gramPow 1 = gram`. -/
lemma iteratedDeriv_two_gramPow_one_isEquivalent :
    IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv 2 (gramPow 1) u)
      (fun u : ℝ => -(2 * Real.pi) / (u * Real.log u ^ 2)) := by
  have h : (fun u : ℝ => iteratedDeriv 2 (gramPow 1) u)
      = fun u : ℝ => iteratedDeriv 2 gram u := by
    rw [gramPow_one_eq_gram]
  rw [h]
  exact iteratedDeriv_two_gram_isEquivalent

/-- The model function `−n·n!·(2π)^n / (u·(log u)^(n+1))` is eventually
negative. -/
private lemma signModel_eventually_neg (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ u : ℝ in atTop,
      -(n * (n.factorial : ℝ) * (2 * Real.pi) ^ n)
        / (u * Real.log u ^ (n + 1)) < 0 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hden : 0 < u * Real.log u ^ (n + 1) := by positivity
  have hnum : 0 < (n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    positivity
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hnum) hden

/-- **`n = 1` instance of the §4 sign axiom**, derived without it: eventually
`iteratedDeriv 2 (gramPow 1) u ≤ 0`. -/
lemma iteratedDeriv_two_gramPow_one_eventually_nonpos :
    ∀ᶠ u : ℝ in atTop, iteratedDeriv 2 (gramPow 1) u ≤ 0 := by
  refine eventually_nonpos_of_isEquivalent
    iteratedDeriv_two_gramPow_one_isEquivalent ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hden : 0 < u * Real.log u ^ 2 := by positivity
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr h2pi) hden

/-! #### §3d.1  Smoke test `n = 2`: order-3 binary Leibniz

For `n = 2` the order-3 expansion has **two** same-order contributions:
`6·g'·g'' ~ −24π²/(u·log³u)` and `2·g·g''' ~ +8π²/(u·log³u)`.  Neither is
negligible against the other — only their *sum* `−16π²/(u·log³u)` (matching
the §3d model `−n·n!·(2π)^n` at `n = 2`) determines the sign.  This
validates the alternating-sum phenomenon described in the §3d header before
the general machinery is built. -/

/-- **Binary Leibniz at order 3**: at any `u > gramThreshold`,
`(gramPow 2)'''(u) = 2·g·g''' + 6·g'·g''`. -/
private lemma iteratedDeriv_three_gramPow_two_eq (u : ℝ) (hu : gramThreshold < u) :
    iteratedDeriv 3 (gramPow 2) u
      = 2 * (gram u * iteratedDeriv 3 gram u)
        + 6 * (iteratedDeriv 1 gram u * iteratedDeriv 2 gram u) := by
  have hContDiff : ContDiffAt ℝ 3 gram u := contDiffAt_gram 3 hu
  rw [gramPow_two_eq_mul]
  rw [iteratedDeriv_fun_mul hContDiff hContDiff]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
  simp [iteratedDeriv_zero, Nat.choose]
  ring

/-- Eventually-true filter form of `iteratedDeriv_three_gramPow_two_eq`. -/
private lemma iteratedDeriv_three_gramPow_two_eventually_eq :
    (fun u : ℝ => iteratedDeriv 3 (gramPow 2) u)
      =ᶠ[atTop]
      (fun u : ℝ =>
        2 * (gram u * iteratedDeriv 3 gram u)
          + 6 * (iteratedDeriv 1 gram u * iteratedDeriv 2 gram u)) := by
  filter_upwards [eventually_gt_atTop gramThreshold] with u hu
  exact iteratedDeriv_three_gramPow_two_eq u hu

/-- If `f ~ a·m` and `g ~ b·m` along `atTop` with `a`, `b`, `a + b` all
nonzero, then `f + g ~ (a+b)·m`.  Used to sum same-order Faà di Bruno
contributions whose constants partially (but not fully) cancel. -/
private lemma isEquivalent_add_same_scale {f g m : ℝ → ℝ} {a b : ℝ}
    (hf : IsEquivalent atTop f (fun u => a * m u))
    (hg : IsEquivalent atTop g (fun u => b * m u))
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    IsEquivalent atTop (fun u => f u + g u) (fun u => (a + b) * m u) := by
  have hf' : (f - fun u => a * m u) =o[atTop] m := by
    have h := hf.isLittleO
    rwa [Asymptotics.isLittleO_const_mul_right_iff ha] at h
  have hg' : (g - fun u => b * m u) =o[atTop] m := by
    have h := hg.isLittleO
    rwa [Asymptotics.isLittleO_const_mul_right_iff hb] at h
  have hsum := hf'.add hg'
  have heq : (fun x : ℝ => (f - fun u => a * m u) x + (g - fun u => b * m u) x)
      = ((fun u : ℝ => f u + g u) - fun u : ℝ => (a + b) * m u) := by
    funext u
    simp only [Pi.sub_apply]
    ring
  rw [heq] at hsum
  exact (Asymptotics.isLittleO_const_mul_right_iff hab).mpr hsum

/-- `6·g'·g'' ~ −24π² / (u·log³u)`: the size-`2` big-part class at `n = 2`. -/
private lemma three_gramPow_two_sixTerm_isEquivalent :
    IsEquivalent atTop
      (fun u : ℝ => 6 * (iteratedDeriv 1 gram u * iteratedDeriv 2 gram u))
      (fun u : ℝ => -(24 * Real.pi ^ 2) * (u * Real.log u ^ 3)⁻¹) := by
  have hMul := iteratedDeriv_one_gram_isEquivalent.mul iteratedDeriv_two_gram_isEquivalent
  have hConst : IsEquivalent atTop (fun _ : ℝ => (6 : ℝ)) (fun _ : ℝ => (6 : ℝ)) :=
    IsEquivalent.refl
  have h := hConst.mul hMul
  have hLeftEq :
      ((fun _ : ℝ => (6 : ℝ))
          * ((fun u : ℝ => iteratedDeriv 1 gram u) * iteratedDeriv 2 gram) : ℝ → ℝ)
        = fun u : ℝ => 6 * (iteratedDeriv 1 gram u * iteratedDeriv 2 gram u) := by
    funext u; simp [Pi.mul_apply]
  have hRightEq :
      ((fun _ : ℝ => (6 : ℝ))
          * ((fun u : ℝ => 2 * Real.pi / Real.log u)
              * fun u : ℝ => -(2 * Real.pi) / (u * Real.log u ^ 2)) : ℝ → ℝ)
        = fun u : ℝ => 6 * ((2 * Real.pi / Real.log u)
            * (-(2 * Real.pi) / (u * Real.log u ^ 2))) := by
    funext u; simp [Pi.mul_apply]
  rw [hLeftEq, hRightEq] at h
  refine h.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu1
  have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu1
  have hune : (u : ℝ) ≠ 0 := by linarith
  have hlne : Real.log u ≠ 0 := hlog.ne'
  field_simp
  ring

/-- `2·g·g''' ~ +8π² / (u·log³u)`: the size-`3` big-part class at `n = 2`.
Same order as the size-`2` class, opposite sign. -/
private lemma three_gramPow_two_twoTerm_isEquivalent :
    IsEquivalent atTop
      (fun u : ℝ => 2 * (gram u * iteratedDeriv 3 gram u))
      (fun u : ℝ => (8 * Real.pi ^ 2) * (u * Real.log u ^ 3)⁻¹) := by
  have h3 := iteratedDeriv_n_gram_isEquivalent 3 (by norm_num)
  have hMul := gram_isEquivalent.mul h3
  have hConst : IsEquivalent atTop (fun _ : ℝ => (2 : ℝ)) (fun _ : ℝ => (2 : ℝ)) :=
    IsEquivalent.refl
  have h := hConst.mul hMul
  have hLeftEq :
      ((fun _ : ℝ => (2 : ℝ)) * (gram * iteratedDeriv 3 gram) : ℝ → ℝ)
        = fun u : ℝ => 2 * (gram u * iteratedDeriv 3 gram u) := by
    funext u; simp [Pi.mul_apply]
  have hRightEq :
      ((fun _ : ℝ => (2 : ℝ))
          * ((fun u : ℝ => 2 * Real.pi * u / Real.log u)
              * fun u : ℝ => (-1 : ℝ) ^ (3 + 1) * (2 * Real.pi)
                  * (((3 : ℕ) - 2).factorial : ℝ)
                  / (u ^ (3 - 1) * Real.log u ^ 2)) : ℝ → ℝ)
        = fun u : ℝ => 2 * ((2 * Real.pi * u / Real.log u)
            * ((-1 : ℝ) ^ (3 + 1) * (2 * Real.pi) * (((3 : ℕ) - 2).factorial : ℝ)
                / (u ^ (3 - 1) * Real.log u ^ 2))) := by
    funext u; simp [Pi.mul_apply]
  rw [hLeftEq, hRightEq] at h
  refine h.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu1
  have hlog : (0 : ℝ) < Real.log u := Real.log_pos hu1
  have hune : (u : ℝ) ≠ 0 := by linarith
  have hlne : Real.log u ≠ 0 := hlog.ne'
  norm_num [Nat.factorial]
  field_simp
  ring

/-- **Smoke test, `n = 2`** (order-3 sign):
`iteratedDeriv 3 (gramPow 2) ~ −16π²/(u·log³u)`.  The constant matches the
§3d model: `−n·n!·(2π)^n = −2·2!·(2π)² = −16π²`. -/
lemma iteratedDeriv_three_gramPow_two_isEquivalent :
    IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv 3 (gramPow 2) u)
      (fun u : ℝ => -(16 * Real.pi ^ 2) * (u * Real.log u ^ 3)⁻¹) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsum := isEquivalent_add_same_scale
    three_gramPow_two_twoTerm_isEquivalent
    three_gramPow_two_sixTerm_isEquivalent
    (by positivity)
    (by simp only [neg_ne_zero]; positivity)
    (by nlinarith)
  have hconst :
      (fun u : ℝ => (8 * Real.pi ^ 2 + -(24 * Real.pi ^ 2)) * (u * Real.log u ^ 3)⁻¹)
        = fun u : ℝ => -(16 * Real.pi ^ 2) * (u * Real.log u ^ 3)⁻¹ := by
    funext u; ring
  rw [hconst] at hsum
  exact iteratedDeriv_three_gramPow_two_eventually_eq.trans_isEquivalent hsum

/-- **`n = 2` instance of the §4 sign axiom**, derived without it: eventually
`iteratedDeriv 3 (gramPow 2) u ≤ 0`. -/
lemma iteratedDeriv_three_gramPow_two_eventually_nonpos :
    ∀ᶠ u : ℝ in atTop, iteratedDeriv 3 (gramPow 2) u ≤ 0 := by
  refine eventually_nonpos_of_isEquivalent
    iteratedDeriv_three_gramPow_two_isEquivalent ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hposInv : 0 < (u * Real.log u ^ 3)⁻¹ := by positivity
  have hneg : -(16 * Real.pi ^ 2) < 0 := by
    have : (0 : ℝ) < 16 * Real.pi ^ 2 := by positivity
    linarith
  exact mul_neg_of_neg_of_pos hneg hposInv

/-! #### §3d.2  Subdominant classes at order `n + 1`

In the order-`(n+1)` expansion of `gramPow n`, partitions with more than `n`
parts vanish (the outer monomial has degree `n`), and partitions with at
least two parts of size `≥ 2` decay one full log below the dominant
single-big-part class. -/

/-- A Faà di Bruno term whose partition has more parts than the power `n`
vanishes identically: the outer monomial `(·)^n` has zero `c.length`-th
derivative, i.e. `n.descFactorial c.length = 0`. -/
private lemma term_eq_zero_of_length_gt {n m : ℕ} (c : OrderedFinpartition m)
    (hc : n < c.length) (u : ℝ) :
    (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
      * ∏ j, iteratedDeriv (c.partSize j) gram u = 0 := by
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr hc]
  simp

/-- **Two-big-part terms are negligible at order `n + 1`.**  If
`c : OrderedFinpartition (n+1)` has `c.length ≤ n` and at least two parts of
size `≥ 2`, its Faà di Bruno term is `o(u⁻¹·((log u)⁻¹)^(n+1))`.

Bookkeeping: the `u`-powers cancel exactly as in §3c.2 (every surviving term
is `Θ(u⁻¹·…)`), and each big part contributes `(log u)⁻²` by the sharp bound,
for a total of `(log u)^{-(n+B.card)}` — at least one log below the dominant
`(log u)^{-(n+1)}`. -/
private lemma term_succ_isLittleO_of_two_big (n : ℕ)
    (c : OrderedFinpartition (n + 1)) (hlen : c.length ≤ n)
    (hb : 2 ≤ (Finset.univ.filter fun j => 2 ≤ c.partSize j).card) :
    (fun u : ℝ => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
        * ∏ j, iteratedDeriv (c.partSize j) gram u)
      =o[atTop] (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) := by
  classical
  set B : Finset (Fin c.length) :=
    Finset.univ.filter (fun j => 2 ≤ c.partSize j) with hB
  -- Exponent bookkeeping: `∑ (sⱼ − 1) = (n+1) − ℓ` and `∑ eⱼ = ℓ + B.card`.
  have hsumsub : ∑ j, (c.partSize j - 1) = (n + 1) - c.length := by
    have hsum := orderedFinpartition_sum_partSize (n + 1) c
    have e1 : ∑ i, ((c.partSize i - 1) + 1) = ∑ i, c.partSize i :=
      Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (c.partSize_pos i))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, hsum] at e1
    omega
  have hesum : ∑ j, (if 2 ≤ c.partSize j then 2 else 1) = c.length + B.card := by
    have hsplit : ∀ j : Fin c.length,
        (if 2 ≤ c.partSize j then 2 else 1)
          = 1 + (if 2 ≤ c.partSize j then 1 else 0) := by
      intro j; by_cases h : 2 ≤ c.partSize j <;> simp [h]
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
      hB, Finset.card_filter]
  -- Per-factor O-bounds: sharp (two logs) for big parts, weak otherwise.
  have hfac : ∀ j : Fin c.length,
      (fun u : ℝ => iteratedDeriv (c.partSize j) gram u)
        =O[atTop] (fun u : ℝ => (u⁻¹) ^ (c.partSize j - 1)
            * ((Real.log u)⁻¹) ^ (if 2 ≤ c.partSize j then 2 else 1)) := by
    intro j
    by_cases h : 2 ≤ c.partSize j
    · simpa [h] using iteratedDeriv_gram_isBigO_sharp (c.partSize j) h
    · have h1 : c.partSize j = 1 := by have := c.partSize_pos j; omega
      simpa [h, h1] using
        iteratedDeriv_gram_isBigO_weak (c.partSize j) (c.partSize_pos j)
  have hprodO : (fun u : ℝ => ∏ j, iteratedDeriv (c.partSize j) gram u)
      =O[atTop] (fun u : ℝ => ∏ j, ((u⁻¹) ^ (c.partSize j - 1)
          * ((Real.log u)⁻¹) ^ (if 2 ≤ c.partSize j then 2 else 1))) :=
    IsBigO.finsetProd (fun j _ => hfac j)
  have hgramO : (fun u : ℝ => (gram u) ^ (n - c.length))
      =O[atTop] (fun u : ℝ => (2 * Real.pi * u / Real.log u) ^ (n - c.length)) :=
    (gram_isEquivalent.pow (n - c.length)).isBigO
  -- The comparison product is `o(model)`: one spare log from `B.card ≥ 2`.
  have hk1 : (n + 1) - c.length = (n - c.length) + 1 := by omega
  have hQ_lo :
      (fun u : ℝ => (2 * Real.pi * u / Real.log u) ^ (n - c.length)
          * ∏ j, ((u⁻¹) ^ (c.partSize j - 1)
              * ((Real.log u)⁻¹) ^ (if 2 ≤ c.partSize j then 2 else 1)))
        =o[atTop] (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) := by
    have hQeq :
        (fun u : ℝ => (2 * Real.pi * u / Real.log u) ^ (n - c.length)
            * ∏ j, ((u⁻¹) ^ (c.partSize j - 1)
                * ((Real.log u)⁻¹) ^ (if 2 ≤ c.partSize j then 2 else 1)))
          =ᶠ[atTop]
          (fun u : ℝ => (2 * Real.pi) ^ (n - c.length)
              * (((Real.log u)⁻¹) ^ (B.card - 1)
                  * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)))) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu1
      have hlog : 0 < Real.log u := Real.log_pos hu1
      have hune : (u : ℝ) ≠ 0 := by linarith
      have hlne : Real.log u ≠ 0 := hlog.ne'
      have hbase : (2 * Real.pi * u / Real.log u) * u⁻¹
          = 2 * Real.pi * (Real.log u)⁻¹ := by field_simp
      have hstep : (2 * Real.pi * u / Real.log u) ^ (n - c.length)
            * (u⁻¹) ^ (n - c.length)
          = (2 * Real.pi) ^ (n - c.length) * ((Real.log u)⁻¹) ^ (n - c.length) := by
        rw [← mul_pow, hbase, mul_pow]
      calc (2 * Real.pi * u / Real.log u) ^ (n - c.length)
              * ∏ j, ((u⁻¹) ^ (c.partSize j - 1)
                  * ((Real.log u)⁻¹) ^ (if 2 ≤ c.partSize j then 2 else 1))
          = (2 * Real.pi * u / Real.log u) ^ (n - c.length)
              * ((u⁻¹) ^ ((n + 1) - c.length)
                  * ((Real.log u)⁻¹) ^ (c.length + B.card)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
              Finset.prod_pow_eq_pow_sum, hsumsub, hesum]
        _ = ((2 * Real.pi * u / Real.log u) ^ (n - c.length)
                * (u⁻¹) ^ (n - c.length))
              * (u⁻¹ * ((Real.log u)⁻¹) ^ (c.length + B.card)) := by
            rw [hk1, pow_succ]; ring
        _ = ((2 * Real.pi) ^ (n - c.length) * ((Real.log u)⁻¹) ^ (n - c.length))
              * (u⁻¹ * ((Real.log u)⁻¹) ^ (c.length + B.card)) := by rw [hstep]
        _ = (2 * Real.pi) ^ (n - c.length)
              * (((Real.log u)⁻¹) ^ (B.card - 1)
                  * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1))) := by
            have hexp : (n - c.length) + (c.length + B.card)
                = (B.card - 1) + (n + 1) := by omega
            calc ((2 * Real.pi) ^ (n - c.length) * ((Real.log u)⁻¹) ^ (n - c.length))
                  * (u⁻¹ * ((Real.log u)⁻¹) ^ (c.length + B.card))
                = (2 * Real.pi) ^ (n - c.length)
                  * (((Real.log u)⁻¹) ^ ((n - c.length) + (c.length + B.card)) * u⁻¹) := by
                  rw [pow_add]; ring
              _ = (2 * Real.pi) ^ (n - c.length)
                  * (((Real.log u)⁻¹) ^ (B.card - 1)
                      * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1))) := by
                  rw [hexp, pow_add]; ring
    have hsmall : (fun u : ℝ => ((Real.log u)⁻¹) ^ (B.card - 1))
        =o[atTop] (fun _ : ℝ => (1 : ℝ)) := by
      have h0 : Tendsto (fun u : ℝ => ((Real.log u)⁻¹) ^ (B.card - 1)) atTop (𝓝 0) := by
        have h := tendsto_inv_log_atTop_zero.pow (B.card - 1)
        simpa [zero_pow (by omega : B.card - 1 ≠ 0)] using h
      exact (Asymptotics.isLittleO_one_iff ℝ).mpr h0
    have hQo : (fun u : ℝ => ((Real.log u)⁻¹) ^ (B.card - 1)
          * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)))
        =o[atTop] (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) := by
      have h := hsmall.mul_isBigO (Asymptotics.isBigO_refl
        (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) atTop)
      simpa using h
    exact hQeq.trans_isLittleO (hQo.const_mul_left _)
  -- Assemble: term =O comparison =o model.
  have hgoal_eq :
      (fun u : ℝ => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u)
        = (fun u : ℝ => (n.descFactorial c.length : ℝ) * ((gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u)) := by
    funext u; ring
  rw [hgoal_eq]
  exact ((hgramO.mul hprodO).const_mul_left _).trans_isLittleO hQ_lo

/-! #### §3d.3  The dominant class: single-big-part terms

A partition of `n + 1` with exactly one part of size `s ≥ 2` (all others
singletons) contributes

    `term c ~ (−1)^{s+1} · n!·(2π)^n · u⁻¹·(log u)^{−(n+1)}`

— the same order for *every* `s`, with alternating sign.  The factorial
bookkeeping is `n.descFactorial ℓ · (s−2)! = n!` (where `ℓ = n+2−s`). -/

/-- Pointwise algebra for the dominant-class shape: collects powers of `2π`,
`u`, `log u` from the three asymptotic factors. -/
private lemma dominant_shape_aux (k₁ k₂ : ℕ) (D A : ℝ) {u : ℝ} (hu : 1 < u) :
    D * ((2 * Real.pi * u / Real.log u) ^ k₁
        * ((2 * Real.pi / Real.log u) ^ k₂
            * (A / (u ^ (k₁ + 1) * Real.log u ^ 2))))
      = (D * A * (2 * Real.pi) ^ (k₁ + k₂))
          * (u⁻¹ * ((Real.log u)⁻¹) ^ (k₁ + k₂ + 2)) := by
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
  have hune : (u : ℝ) ≠ 0 := hu0.ne'
  have hlne : Real.log u ≠ 0 := hlog.ne'
  rw [div_pow, div_pow, inv_pow]
  field_simp
  ring

/-- **Dominant-class term asymptotic at order `n + 1`.**  If
`c : OrderedFinpartition (n+1)` has exactly one big part `j₀` (of size
`s := c.partSize j₀ ≥ 2`; all other parts singletons), then

    `term c ~ (−1)^{s+1}·n!·(2π)^n · u⁻¹·((log u)⁻¹)^{n+1}`.

Combines `gram ~ 2πu/log u` (power `n − ℓ = s − 2`), `g' ~ 2π/log u`
(power `ℓ − 1 = n+1−s`), and Theorem 3 for `g^{(s)}`. -/
private lemma term_succ_dominant_isEquivalent (n : ℕ)
    (c : OrderedFinpartition (n + 1)) (j₀ : Fin c.length)
    (hj₀ : 2 ≤ c.partSize j₀) (huniq : ∀ j, j ≠ j₀ → c.partSize j = 1) :
    IsEquivalent atTop
      (fun u : ℝ => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ => ((-1 : ℝ) ^ (c.partSize j₀ + 1) * (n.factorial : ℝ)
          * (2 * Real.pi) ^ n) * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1))) := by
  classical
  have hpos : 0 < c.length := c.length_pos (Nat.succ_pos n)
  -- `ℓ + s = n + 2` from the part sizes summing to `n + 1`.
  have hℓs : c.length + c.partSize j₀ = n + 2 := by
    have hsum := orderedFinpartition_sum_partSize (n + 1) c
    have hsplit : ∑ j, c.partSize j
        = (∑ j ∈ Finset.univ.erase j₀, c.partSize j) + c.partSize j₀ :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ j₀)).symm
    have hones : ∑ j ∈ Finset.univ.erase j₀, c.partSize j
        = (Finset.univ.erase j₀).card := by
      rw [Finset.sum_congr rfl (fun j hj => huniq j (Finset.ne_of_mem_erase hj)),
        Finset.sum_const, smul_eq_mul, mul_one]
    have hcard : (Finset.univ.erase j₀).card = c.length - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ,
        Fintype.card_fin]
    omega
  -- Factorial bookkeeping: `(s−2)! · n.descFactorial ℓ = n!`.
  have hfactN : (c.partSize j₀ - 2).factorial * n.descFactorial c.length
      = n.factorial := by
    have hk : c.length ≤ n := by omega
    have hs2 : c.partSize j₀ - 2 = n - c.length := by omega
    rw [hs2, Nat.factorial_mul_descFactorial hk]
  have hcastR : ((c.partSize j₀ - 2).factorial : ℝ) * (n.descFactorial c.length : ℝ)
      = (n.factorial : ℝ) := by exact_mod_cast hfactN
  -- The product over parts collapses to `(g')^(ℓ−1) · g^{(s)}`.
  have hterm_eq :
      (fun u : ℝ => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u)
        = fun u : ℝ => (n.descFactorial c.length : ℝ) * ((gram u) ^ (n - c.length)
            * ((iteratedDeriv 1 gram u) ^ (c.length - 1)
                * iteratedDeriv (c.partSize j₀) gram u)) := by
    funext u
    have hprod : ∏ j, iteratedDeriv (c.partSize j) gram u
        = (iteratedDeriv 1 gram u) ^ (c.length - 1)
            * iteratedDeriv (c.partSize j₀) gram u := by
      rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ j₀)]
      congr 1
      rw [Finset.prod_congr rfl
          (fun j hj => by rw [huniq j (Finset.ne_of_mem_erase hj)]),
        Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j₀),
        Finset.card_univ, Fintype.card_fin]
    rw [hprod]; ring
  -- Asymptotic equivalents for the three factors, then trans to closed form.
  have hA := gram_isEquivalent.pow (n - c.length)
  have hB := iteratedDeriv_one_gram_isEquivalent.pow (c.length - 1)
  have hC := iteratedDeriv_n_gram_isEquivalent (c.partSize j₀) hj₀
  have hD : IsEquivalent atTop (fun _ : ℝ => (n.descFactorial c.length : ℝ))
      (fun _ : ℝ => (n.descFactorial c.length : ℝ)) := IsEquivalent.refl
  have h := hD.mul (hA.mul (hB.mul hC))
  have hLeftEq : ((fun _ : ℝ => (n.descFactorial c.length : ℝ))
      * (gram ^ (n - c.length)
          * ((fun u : ℝ => iteratedDeriv 1 gram u) ^ (c.length - 1)
              * iteratedDeriv (c.partSize j₀) gram)) : ℝ → ℝ)
      = fun u : ℝ => (n.descFactorial c.length : ℝ) * ((gram u) ^ (n - c.length)
          * ((iteratedDeriv 1 gram u) ^ (c.length - 1)
              * iteratedDeriv (c.partSize j₀) gram u)) := by
    funext u; simp [Pi.mul_apply, Pi.pow_apply]
  have hRightEq : ((fun _ : ℝ => (n.descFactorial c.length : ℝ))
      * ((fun u : ℝ => 2 * Real.pi * u / Real.log u) ^ (n - c.length)
          * ((fun u : ℝ => 2 * Real.pi / Real.log u) ^ (c.length - 1)
              * fun u : ℝ => (-1 : ℝ) ^ (c.partSize j₀ + 1) * (2 * Real.pi)
                  * (((c.partSize j₀ : ℕ) - 2).factorial : ℝ)
                  / (u ^ (c.partSize j₀ - 1) * Real.log u ^ 2))) : ℝ → ℝ)
      = fun u : ℝ => (n.descFactorial c.length : ℝ)
          * ((2 * Real.pi * u / Real.log u) ^ (n - c.length)
              * ((2 * Real.pi / Real.log u) ^ (c.length - 1)
                  * ((-1 : ℝ) ^ (c.partSize j₀ + 1) * (2 * Real.pi)
                      * (((c.partSize j₀ : ℕ) - 2).factorial : ℝ)
                      / (u ^ (c.partSize j₀ - 1) * Real.log u ^ 2)))) := by
    funext u; simp [Pi.mul_apply, Pi.pow_apply]
  rw [hLeftEq, hRightEq] at h
  rw [hterm_eq]
  refine h.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu1
  have hs1 : c.partSize j₀ - 1 = (n - c.length) + 1 := by omega
  rw [hs1,
    dominant_shape_aux (n - c.length) (c.length - 1) _ _ hu1,
    show (n - c.length) + (c.length - 1) = n - 1 from by omega,
    show (n - 1) + 2 = n + 1 from by omega,
    show (2 * Real.pi) ^ n = (2 * Real.pi) ^ (n - 1) * (2 * Real.pi) from by
      rw [← pow_succ]; congr 1; omega,
    ← hcastR]
  ring

/-- Difference form of `term_succ_dominant_isEquivalent`, ready for summation
over the dominant class:
`term c − ε_c·model =o[atTop] model` with
`ε_c = (−1)^{s+1}·n!·(2π)^n` and `model = u⁻¹·((log u)⁻¹)^{n+1}`. -/
private lemma term_succ_dominant_sub_isLittleO (n : ℕ)
    (c : OrderedFinpartition (n + 1)) (j₀ : Fin c.length)
    (hj₀ : 2 ≤ c.partSize j₀) (huniq : ∀ j, j ≠ j₀ → c.partSize j = 1) :
    (fun u : ℝ => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u
        - ((-1 : ℝ) ^ (c.partSize j₀ + 1) * (n.factorial : ℝ)
            * (2 * Real.pi) ^ n) * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)))
      =o[atTop] (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) := by
  have h := (term_succ_dominant_isEquivalent n c j₀ hj₀ huniq).isLittleO
  have hε : ((-1 : ℝ) ^ (c.partSize j₀ + 1) * (n.factorial : ℝ)
      * (2 * Real.pi) ^ n) ≠ 0 := by
    have h1 : ((-1 : ℝ) ^ (c.partSize j₀ + 1)) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have h2 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_pos.ne'
    have h3 : ((2 : ℝ) * Real.pi) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  rw [Asymptotics.isLittleO_const_mul_right_iff hε] at h
  exact h

/-! #### §3d.4  Signed count over the dominant class

The aggregate sign constant requires `∑_{c dominant} (−1)^{s_c+1} = −n`,
summing over all single-big-part partitions of `n+1`.  Instead of a bijection
with subsets, we compute the sum by Mathlib's recursion
`OrderedFinpartition.extendEquiv`: every partition of `n+1` is uniquely
`c.extendLeft` (new singleton part) or `c.extendMiddle k` (grow part `k`) for
`c : OrderedFinpartition n`.  Fibre-by-fibre:

  * `c` atomic: the `n` middle extensions each create a fresh size-2 part,
    contributing `n · (−1)^{2+1} = −n`; `extendLeft` stays atomic.
  * `c` dominant with big size `s`: `extendLeft` keeps `s`, `extendMiddle` at
    the big part bumps it to `s+1` — the two contributions cancel; all other
    extensions create a second big part.
  * `c` with `≥ 2` big parts: every extension still has `≥ 2` big parts.

Total: `−n`. -/

/-- Number of "big" parts (size `≥ 2`) of an ordered finpartition. -/
private def bigCard {m : ℕ} (c : OrderedFinpartition m) : ℕ :=
  (Finset.univ.filter fun j => 2 ≤ c.partSize j).card

/-- `bigCard` as an indicator sum. -/
private lemma bigCard_eq_sum {m : ℕ} (c : OrderedFinpartition m) :
    bigCard c = ∑ j, if 2 ≤ c.partSize j then 1 else 0 :=
  Finset.card_filter _ _

/-- Signed weight `∑_{big parts} (−1)^{size+1}`; on the dominant class this
is `(−1)^{s+1}` for the unique big size `s`. -/
private noncomputable def sgnWeight {m : ℕ} (c : OrderedFinpartition m) : ℝ :=
  ∑ j, if 2 ≤ c.partSize j then (-1 : ℝ) ^ (c.partSize j + 1) else 0

/-- Dominant-class indicator weight: `sgnWeight` on single-big-part
partitions, `0` elsewhere. -/
private noncomputable def domWeight {m : ℕ} (c : OrderedFinpartition m) : ℝ :=
  if bigCard c = 1 then sgnWeight c else 0

private lemma bigCard_atomic (m : ℕ) :
    bigCard (OrderedFinpartition.atomic m) = 0 := by
  rw [bigCard_eq_sum]
  simp

private lemma sgnWeight_atomic (m : ℕ) :
    sgnWeight (OrderedFinpartition.atomic m) = 0 := by
  unfold sgnWeight
  simp

/-- Adding a new singleton part does not change the big parts. -/
private lemma bigCard_extendLeft {m : ℕ} (c : OrderedFinpartition m) :
    bigCard c.extendLeft = bigCard c := by
  rw [bigCard_eq_sum, bigCard_eq_sum]
  change (∑ j : Fin (c.length + 1),
      if 2 ≤ c.extendLeft.partSize j then (1 : ℕ) else 0) = _
  rw [Fin.sum_univ_succ]
  simp [OrderedFinpartition.extendLeft_partSize]

/-- Adding a new singleton part does not change the signed weight. -/
private lemma sgnWeight_extendLeft {m : ℕ} (c : OrderedFinpartition m) :
    sgnWeight c.extendLeft = sgnWeight c := by
  change (∑ j : Fin (c.length + 1),
      if 2 ≤ c.extendLeft.partSize j
      then (-1 : ℝ) ^ (c.extendLeft.partSize j + 1) else 0) = _
  rw [Fin.sum_univ_succ]
  simp [OrderedFinpartition.extendLeft_partSize, sgnWeight]

/-- Growing part `k` creates a new big part exactly when `k` was a
singleton. -/
private lemma bigCard_extendMiddle {m : ℕ} (c : OrderedFinpartition m)
    (k : Fin c.length) :
    bigCard (c.extendMiddle k)
      = bigCard c + (if 2 ≤ c.partSize k then 0 else 1) := by
  rw [bigCard_eq_sum, bigCard_eq_sum]
  change (∑ j : Fin c.length,
      if 2 ≤ (c.extendMiddle k).partSize j then (1 : ℕ) else 0) = _
  have hupdate : ∀ j : Fin c.length, (c.extendMiddle k).partSize j
      = Function.update c.partSize k (c.partSize k + 1) j := fun _ => rfl
  rw [Finset.sum_congr rfl (fun j _ => by rw [hupdate j]),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  have herase : ∑ j ∈ Finset.univ.erase k,
      (if 2 ≤ Function.update c.partSize k (c.partSize k + 1) j then (1 : ℕ) else 0)
      = ∑ j ∈ Finset.univ.erase k, (if 2 ≤ c.partSize j then 1 else 0) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [herase, Function.update_self]
  have h2 : 2 ≤ c.partSize k + 1 := by have := c.partSize_pos k; omega
  by_cases h : 2 ≤ c.partSize k <;> simp [h, h2]

/-- Effect of growing part `k` on the signed weight: the `k`-term becomes
`(−1)^{(s_k+1)+1}` (the grown part is always big), replacing the old
`k`-term. -/
private lemma sgnWeight_extendMiddle {m : ℕ} (c : OrderedFinpartition m)
    (k : Fin c.length) :
    sgnWeight (c.extendMiddle k)
      = sgnWeight c + (-1 : ℝ) ^ (c.partSize k + 2)
        - (if 2 ≤ c.partSize k then (-1 : ℝ) ^ (c.partSize k + 1) else 0) := by
  change (∑ j : Fin c.length,
      if 2 ≤ (c.extendMiddle k).partSize j
      then (-1 : ℝ) ^ ((c.extendMiddle k).partSize j + 1) else 0) = _
  have hupdate : ∀ j : Fin c.length, (c.extendMiddle k).partSize j
      = Function.update c.partSize k (c.partSize k + 1) j := fun _ => rfl
  rw [Finset.sum_congr rfl (fun j _ => by rw [hupdate j]), sgnWeight,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  have herase : ∑ j ∈ Finset.univ.erase k,
      (if 2 ≤ Function.update c.partSize k (c.partSize k + 1) j
        then (-1 : ℝ) ^ (Function.update c.partSize k (c.partSize k + 1) j + 1) else 0)
      = ∑ j ∈ Finset.univ.erase k,
          (if 2 ≤ c.partSize j then (-1 : ℝ) ^ (c.partSize j + 1) else 0) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [herase, Function.update_self]
  have h2 : 2 ≤ c.partSize k + 1 := by have := c.partSize_pos k; omega
  rw [if_pos h2, show c.partSize k + 1 + 1 = c.partSize k + 2 from rfl]
  by_cases h : 2 ≤ c.partSize k
  · simp only [if_pos h]
    ring
  · simp [h]

/-- A partition with no big part is atomic. -/
private lemma eq_atomic_of_bigCard_eq_zero {m : ℕ} (c : OrderedFinpartition m)
    (h : bigCard c = 0) : c = OrderedFinpartition.atomic m := by
  have hempty := Finset.card_eq_zero.mp h
  have hps1 : ∀ j, c.partSize j = 1 := by
    intro j
    by_contra hne
    have h2 : 2 ≤ c.partSize j := by have := c.partSize_pos j; omega
    have hmem : j ∈ Finset.univ.filter (fun j => 2 ≤ c.partSize j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, h2⟩
    rw [hempty] at hmem
    exact absurd hmem (by simp)
  have hlen : c.length = m := by
    have hsum := orderedFinpartition_sum_partSize m c
    have hcl : ∑ i, c.partSize i = c.length := by
      rw [Finset.sum_congr rfl (fun i _ => hps1 i), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  exact orderedFinpartition_eq_atomic_of_length m c hlen

/-- Extract the unique big part from a dominant partition. -/
private lemma exists_unique_big_of_bigCard_eq_one {m : ℕ}
    (c : OrderedFinpartition m) (h : bigCard c = 1) :
    ∃ j₀, 2 ≤ c.partSize j₀ ∧ ∀ j, j ≠ j₀ → c.partSize j = 1 := by
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp h
  refine ⟨j₀, ?_, ?_⟩
  · have hmem : j₀ ∈ Finset.univ.filter (fun j => 2 ≤ c.partSize j) := by
      rw [hj₀]; exact Finset.mem_singleton_self j₀
    exact (Finset.mem_filter.mp hmem).2
  · intro j hj
    have hnot : j ∉ Finset.univ.filter (fun j => 2 ≤ c.partSize j) := by
      rw [hj₀]; simpa using hj
    have h2 : ¬ 2 ≤ c.partSize j := fun h2 =>
      hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h2⟩)
    have := c.partSize_pos j
    omega

/-- On a dominant partition the signed weight is the single big term. -/
private lemma sgnWeight_of_unique_big {m : ℕ} (c : OrderedFinpartition m)
    (j₀ : Fin c.length) (hj₀ : 2 ≤ c.partSize j₀)
    (huniq : ∀ j, j ≠ j₀ → c.partSize j = 1) :
    sgnWeight c = (-1 : ℝ) ^ (c.partSize j₀ + 1) := by
  unfold sgnWeight
  rw [Finset.sum_eq_single j₀]
  · rw [if_pos hj₀]
  · intro j _ hj
    rw [huniq j hj]
    simp
  · intro h; exact absurd (Finset.mem_univ j₀) h

/-- **Fibre contribution of `extendEquiv`**: only the atomic fibre survives. -/
private lemma extend_fibre_contribution {m : ℕ} (c : OrderedFinpartition m) :
    (domWeight c.extendLeft + ∑ k, domWeight (c.extendMiddle k))
      = if c = OrderedFinpartition.atomic m then -(m : ℝ) else 0 := by
  rcases Nat.lt_or_ge (bigCard c) 1 with h0 | h1
  · -- `bigCard c = 0` ⇒ atomic: each middle extension contributes `−1`.
    have h0' : bigCard c = 0 := by omega
    have hc := eq_atomic_of_bigCard_eq_zero c h0'
    subst hc
    rw [if_pos rfl]
    have hL : domWeight (OrderedFinpartition.atomic m).extendLeft = 0 := by
      unfold domWeight
      rw [bigCard_extendLeft, bigCard_atomic]
      norm_num
    have hM : ∀ k : Fin (OrderedFinpartition.atomic m).length,
        domWeight ((OrderedFinpartition.atomic m).extendMiddle k) = -1 := by
      intro k
      unfold domWeight
      rw [bigCard_extendMiddle, bigCard_atomic, sgnWeight_extendMiddle,
        sgnWeight_atomic]
      norm_num
    rw [hL, Finset.sum_congr rfl (fun k _ => hM k), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, OrderedFinpartition.atomic_length]
    simp
  · rcases Nat.lt_or_ge (bigCard c) 2 with h1' | h2
    · -- `bigCard c = 1`: `extendLeft` and `extendMiddle j₀` cancel.
      have h1'' : bigCard c = 1 := by omega
      obtain ⟨j₀, hj₀, huniq⟩ := exists_unique_big_of_bigCard_eq_one c h1''
      have hne : c ≠ OrderedFinpartition.atomic m := by
        intro hc
        rw [hc, bigCard_atomic] at h1''
        omega
      rw [if_neg hne]
      have hsgn := sgnWeight_of_unique_big c j₀ hj₀ huniq
      have hL : domWeight c.extendLeft = (-1 : ℝ) ^ (c.partSize j₀ + 1) := by
        unfold domWeight
        rw [bigCard_extendLeft, if_pos h1'', sgnWeight_extendLeft, hsgn]
      have hM : ∀ k, domWeight (c.extendMiddle k)
          = if k = j₀ then -((-1 : ℝ) ^ (c.partSize j₀ + 1)) else 0 := by
        intro k
        rcases eq_or_ne k j₀ with rfl | hk
        · unfold domWeight
          rw [bigCard_extendMiddle, h1'', if_pos hj₀, if_pos rfl, if_pos rfl,
            sgnWeight_extendMiddle, hsgn, if_pos hj₀,
            show c.partSize k + 2 = (c.partSize k + 1) + 1 from rfl, pow_succ]
          ring
        · unfold domWeight
          have hk1 : c.partSize k = 1 := huniq k hk
          rw [bigCard_extendMiddle, h1'', hk1, if_neg hk]
          norm_num
      rw [hL, Finset.sum_congr rfl (fun k _ => hM k), Finset.sum_ite_eq']
      simp
    · -- `bigCard c ≥ 2`: every extension still has `≥ 2` big parts.
      have hne : c ≠ OrderedFinpartition.atomic m := by
        intro hc; rw [hc, bigCard_atomic] at h2; omega
      rw [if_neg hne]
      have hL : domWeight c.extendLeft = 0 := by
        unfold domWeight
        rw [bigCard_extendLeft, if_neg (by omega)]
      have hM : ∀ k, domWeight (c.extendMiddle k) = 0 := by
        intro k
        unfold domWeight
        rw [bigCard_extendMiddle,
          if_neg (by by_cases h : 2 ≤ c.partSize k <;> simp [h] <;> omega)]
      rw [hL, Finset.sum_congr rfl (fun k _ => hM k), Finset.sum_const, smul_zero]
      simp

/-- **Signed count over the dominant class**: summing `domWeight` over all
ordered finpartitions of `n + 1` gives `−n`. -/
private lemma sum_domWeight (n : ℕ) :
    ∑ C : OrderedFinpartition (n + 1), domWeight C = -(n : ℝ) := by
  classical
  calc ∑ C : OrderedFinpartition (n + 1), domWeight C
      = ∑ p : (c : OrderedFinpartition n) × Option (Fin c.length),
          domWeight (p.1.extend p.2) :=
        (Fintype.sum_equiv (OrderedFinpartition.extendEquiv n) _ _ fun _ => rfl).symm
    _ = ∑ c : OrderedFinpartition n, ∑ o : Option (Fin c.length),
          domWeight (c.extend o) := Fintype.sum_sigma _
    _ = ∑ c : OrderedFinpartition n,
          (if c = OrderedFinpartition.atomic n then -(n : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Fintype.sum_option]
        simp only [OrderedFinpartition.extend_none, OrderedFinpartition.extend_some]
        exact extend_fibre_contribution c
    _ = -(n : ℝ) := by
        rw [Finset.sum_ite_eq' Finset.univ (OrderedFinpartition.atomic n)
          (fun _ => -(n : ℝ))]
        simp

/-- The signed count in the filtered form used by the §3d assembly:
`∑_{c dominant} sgnWeight c = −n`. -/
private lemma sum_sgnWeight_dominant (n : ℕ) :
    ∑ c ∈ Finset.univ.filter
        (fun c : OrderedFinpartition (n + 1) => bigCard c = 1),
      sgnWeight c = -(n : ℝ) := by
  rw [Finset.sum_filter, ← sum_domWeight n]
  exact Finset.sum_congr rfl fun c _ => rfl

/-! #### §3d.5  The order-`(n+1)` equivalence, assembled -/

/-- **§3d main lemma.**  For every `n ≥ 1`,

    `iteratedDeriv (n+1) (gramPow n) u ~ −n·n!·(2π)^n · u⁻¹·((log u)⁻¹)^{n+1}`
    as `u → +∞`.

Assembly: the order-`(n+1)` Faà di Bruno sum (`faadi_bruno_pow_gram`) splits
into the vanishing class (`> n` parts), the dominant single-big-part class —
whose terms are `(−1)^{s+1}·n!·(2π)^n·model` up to `o(model)` and whose signed
count is `−n` (§3d.4) — and the `≥ 2`-big-part class, which is `o(model)`. -/
lemma iteratedDeriv_succ_gramPow_isEquivalent (n : ℕ) (hn : 1 ≤ n) :
    IsEquivalent atTop
      (fun u : ℝ => iteratedDeriv (n + 1) (gramPow n) u)
      (fun u : ℝ => (-(n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n)
          * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1))) := by
  classical
  -- (0) Faà di Bruno at order `n+1`, filter form.
  have hFdB : (fun u : ℝ => iteratedDeriv (n + 1) (gramPow n) u)
      =ᶠ[atTop]
      (fun u : ℝ => ∑ c : OrderedFinpartition (n + 1),
          (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u) := by
    filter_upwards [eventually_gt_atTop gramThreshold] with u hu
    exact faadi_bruno_pow_gram n (n + 1) u hu
  -- (1) The non-dominant classes are `o(model)`.
  have hrem : (fun u : ℝ => ∑ c ∈ Finset.univ.filter
        (fun c : OrderedFinpartition (n + 1) => ¬ bigCard c = 1),
        (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u)
      =o[atTop] (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) := by
    refine IsLittleO.sum ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    rcases Nat.lt_or_ge n c.length with hlen | hlen
    · -- more parts than the power: the term vanishes identically.
      have hzero : (fun u : ℝ => (n.descFactorial c.length : ℝ)
          * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u) = fun _ : ℝ => (0 : ℝ) := by
        funext u; exact term_eq_zero_of_length_gt c hlen u
      rw [hzero]
      exact Asymptotics.isLittleO_zero _ _
    · -- `length ≤ n` forces a big part; `≠ 1` big parts means `≥ 2`.
      have hb0 : bigCard c ≠ 0 := by
        intro h0
        have hatom := eq_atomic_of_bigCard_eq_zero c h0
        rw [hatom, OrderedFinpartition.atomic_length] at hlen
        omega
      have hb2 : 2 ≤ bigCard c := by
        have h1 := hc.2
        omega
      exact term_succ_isLittleO_of_two_big n c hlen hb2
  -- (2) Dominant class: per-term difference against `sgnWeight c · n!(2π)^n`.
  have hdom : (fun u : ℝ => ∑ c ∈ Finset.univ.filter
        (fun c : OrderedFinpartition (n + 1) => bigCard c = 1),
        ((n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u
          - sgnWeight c * ((n.factorial : ℝ) * (2 * Real.pi) ^ n)
              * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1))))
      =o[atTop] (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) := by
    refine IsLittleO.sum ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨j₀, hj₀, huniq⟩ := exists_unique_big_of_bigCard_eq_one c hc.2
    have h := term_succ_dominant_sub_isLittleO n c j₀ hj₀ huniq
    have heq : (fun u : ℝ => (n.descFactorial c.length : ℝ)
          * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u
        - ((-1 : ℝ) ^ (c.partSize j₀ + 1) * (n.factorial : ℝ)
            * (2 * Real.pi) ^ n) * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)))
        = (fun u : ℝ => (n.descFactorial c.length : ℝ)
            * (gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u
          - sgnWeight c * ((n.factorial : ℝ) * (2 * Real.pi) ^ n)
              * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1))) := by
      funext u
      rw [sgnWeight_of_unique_big c j₀ hj₀ huniq]
      ring
    rw [heq] at h
    exact h
  -- (3) Reassemble the dominant sum via the §3d.4 signed count.
  have hdom' : (fun u : ℝ => (∑ c ∈ Finset.univ.filter
        (fun c : OrderedFinpartition (n + 1) => bigCard c = 1),
        (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u)
        + (n : ℝ) * ((n.factorial : ℝ) * (2 * Real.pi) ^ n)
            * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)))
      =o[atTop] (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) := by
    refine hdom.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards with u
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_sgnWeight_dominant n]
    ring
  -- (4) Total: difference of the full sum against the target.
  have htotal : (fun u : ℝ => (∑ c : OrderedFinpartition (n + 1),
        (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
          * ∏ j, iteratedDeriv (c.partSize j) gram u)
        - (-(n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n)
            * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)))
      =o[atTop] (fun u : ℝ => u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1)) := by
    have h := hdom'.add hrem
    refine h.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards with u
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c : OrderedFinpartition (n + 1) => bigCard c = 1)
      (fun c => (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
        * ∏ j, iteratedDeriv (c.partSize j) gram u)]
    ring
  -- (5) Conclude.
  have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have h3 : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
  have h4 : (0 : ℝ) < (n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n :=
    mul_pos (mul_pos h1 h2) h3
  have hconst_ne : (-(n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n) ≠ 0 := by
    have hrw : -(n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n
        = -((n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n) := by ring
    rw [hrw]
    exact neg_ne_zero.mpr h4.ne'
  have hfinal : IsEquivalent atTop
      (fun u : ℝ => ∑ c : OrderedFinpartition (n + 1),
          (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ => (-(n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n)
          * (u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1))) :=
    (Asymptotics.isLittleO_const_mul_right_iff hconst_ne).mpr htotal
  exact hFdB.trans_isEquivalent hfinal

/-! ## §4  Eventual antitone in absolute value (proved) -/

/-- **Sign of the `(n+1)`-th derivative of `(gram)^n`** (formerly the last
analytic axiom of this file; now proved via §3d).

Eventually `iteratedDeriv (n+1) (gramPow n) u ≤ 0`.  This is the analytic
ingredient that turns asymp-equivalence into pointwise antitone
monotonicity: by `antitoneOn_of_deriv_nonpos`, a function with non-positive
derivative is antitone.

By `iteratedDeriv_succ_gramPow_isEquivalent`, the `(n+1)`-th derivative is
equivalent to `−n·n!·(2π)^n · u⁻¹·(log u)^{−(n+1)}`, which is negative for
`u > 1`; eventual non-positivity follows by
`eventually_nonpos_of_isEquivalent`. -/
lemma iteratedDeriv_succ_n_gramPow_n_eventually_nonpos (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ u : ℝ in atTop, iteratedDeriv (n + 1) (gramPow n) u ≤ 0 := by
  refine eventually_nonpos_of_isEquivalent
    (iteratedDeriv_succ_gramPow_isEquivalent n hn) ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
  have hmodel : 0 < u⁻¹ * ((Real.log u)⁻¹) ^ (n + 1) := by positivity
  have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have h3 : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
  have h4 : (0 : ℝ) < (n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n :=
    mul_pos (mul_pos h1 h2) h3
  have hC : -(n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ n < 0 := by linarith
  exact mul_neg_of_neg_of_pos hC hmodel

/-- A small free corollary: `iteratedDeriv n (gramPow n) u > 0` eventually.
Used by §4 to identify `|iteratedDeriv n …|` with `iteratedDeriv n …` on a
tail, and by §6 to lower-bound the latter by half the §3-leading. -/
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
  • `iteratedDeriv (n+1) (gramPow n) u ≤ 0` (the §4 sign lemma above);
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

/-! ## §8  Shifted variant, for the continuous result

Corollary 5 consumes Theorem 4 through the Kuipers–Niederreiter
discrete-to-continuous criterion (K–N Theorem 9.6(a), proved as
`Gram.UD.isCUDModOne_of_forall_shift` in `UDModOne.lean`), which needs
uniform distribution of every *shifted* integer sample
`(gramPow n (k + t))ₖ`, `t ∈ [0, 1]`.  Each shift satisfies the same
four Fejér hypotheses as the unshifted sequence: they transport along
the translation `u ↦ u + t` via `iteratedDeriv_comp_add_const`. -/

/-- `gramPow n` is measurable — inherited from `measurable_gram`
(`Theorem3.lean`), which glues the monotone true inverse above
`θ(7)/π + 1` with the constant `invFunOn` default below it. -/
lemma measurable_gramPow (n : ℕ) : Measurable (gramPow n) :=
  measurable_gram.pow_const n

/-- **Shifted Theorem 4**: for every `t ≥ 0`, the sequence
`((gram (k + t))^n)ₖ` is uniformly distributed modulo one.  The four
hypotheses of the Fejér criterion for `u ↦ gramPow n (u + t)` follow
from the ones proved in §§2–6 by translating along `u ↦ u + t`. -/
theorem theorem4_shift (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    Gram.UD.IsUDModOne (fun k : ℕ => gramPow n ((k : ℝ) + t)) := by
  have hshift : Tendsto (fun u : ℝ => u + t) atTop atTop :=
    tendsto_atTop_add_const_right _ t tendsto_id
  have hrw := iteratedDeriv_comp_add_const n (gramPow n) t
  refine isUDModOne_of_iteratedDeriv_decay
    (fun u => gramPow n (u + t)) n hn ?_ ?_ ?_ ?_
  · -- eventual smoothness, translated
    filter_upwards [eventually_gt_atTop gramThreshold] with u hu
    have hgt : gramThreshold < u + t := by linarith
    exact ContDiffAt.comp (g := gramPow n) (f := fun u : ℝ => u + t) u
      (contDiffAt_gramPow n n hgt) (contDiffAt_id.add contDiffAt_const)
  · -- eventual antitonicity of `|iteratedDeriv n ·|`, translated
    obtain ⟨x₀, hx₀⟩ := iteratedDeriv_n_gramPow_n_eventually_antitone n hn
    refine ⟨x₀, ?_⟩
    intro u₁ h₁ u₂ h₂ h₁₂
    simp only [hrw]
    exact hx₀ (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₁]))
      (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₂])) (by linarith)
  · -- decay to zero, translated
    have h0 := iteratedDeriv_n_gramPow_n_tendsto_zero n hn
    simp only [hrw]
    exact h0.comp hshift
  · -- `u · |·| → ∞`: from `(u+t) · |·(u+t)| → ∞` since
    -- `u + t ≤ u · (1 + t)` for `u ≥ 1`.
    have hcomp : Tendsto
        (fun u : ℝ => (u + t) * |iteratedDeriv n (gramPow n) (u + t)|)
        atTop atTop :=
      (mul_iteratedDeriv_n_gramPow_n_tendsto_atTop n hn).comp hshift
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have hdiv := hcomp.atTop_div_const h1t
    simp only [hrw]
    refine tendsto_atTop_mono' atTop ?_ hdiv
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have habs : (0 : ℝ) ≤ |iteratedDeriv n (gramPow n) (u + t)| :=
      abs_nonneg _
    rw [div_le_iff₀ h1t]
    nlinarith [mul_nonneg (mul_nonneg habs ht)
      (by linarith : (0 : ℝ) ≤ u - 1)]

end Gram.Theorem4
