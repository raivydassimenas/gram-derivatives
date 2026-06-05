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
           `iteratedDeriv_n_gramPow_n_isEquivalent` (§3 magnitude, ALL `n`;
             Faà di Bruno on `(·^n) ∘ gram` + Theorem 3 — see §3c),
           `iteratedDeriv_n_gramPow_n_tendsto_zero`,
           `mul_iteratedDeriv_n_gramPow_n_tendsto_atTop`,
           `iteratedDeriv_n_gramPow_n_eventually_pos` (helper),
           `iteratedDeriv_n_gramPow_n_eventually_antitone` (§4),
           `iteratedDeriv_one_gramPow_one_isEquivalent` (§3a, n=1 smoke test),
           `iteratedDeriv_two_gramPow_two_isEquivalent` (§3b, n=2 smoke test),
           `theorem4` itself (one-line application of the K–N criterion).
  Axioms (this file):
    • `isUDModOne_of_iteratedDeriv_decay` — the K–N criterion
      (antitone variant).  Permanent: no UD-mod-1 theory in Mathlib.
    • `iteratedDeriv_succ_n_gramPow_n_eventually_nonpos` — the sign of
      the `(n+1)`-th derivative of `(gram)^n` (used by §4 for eventual
      antitonicity).  Deferred: needs an order-`(n+1)` Faà di Bruno pass
      whose leading coefficient sign is `−n·n!·(2π)^n < 0`; not derivable
      from the §3 magnitude asymp alone — see the docstring.
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

/-- **Faà di Bruno expansion** of `(gram^n)^(n)` at `u > gramThreshold`:

    `iteratedDeriv n (gramPow n) u
       = ∑ c : OrderedFinpartition n,
           n.descFactorial c.length · (gram u)^(n − c.length)
             · ∏ j, iteratedDeriv (c.partSize j) gram u`.

Mirrors `faadi_bruno_gram` from `Theorem3.lean`, with the outer function `(·^n)`
in place of `θ` and `iteratedDeriv_pow` supplying the monomial derivatives. -/
private lemma faadi_bruno_gramPow (n : ℕ) (u : ℝ) (hu : gramThreshold < u) :
    iteratedDeriv n (gramPow n) u
      = ∑ c : OrderedFinpartition n,
          (n.descFactorial c.length : ℝ) * (gram u) ^ (n - c.length)
            * ∏ j, iteratedDeriv (c.partSize j) gram u := by
  have hcomp_fun : (gramPow n : ℝ → ℝ) = (fun x : ℝ => x ^ n) ∘ gram := by
    funext x; rfl
  have hg : ContDiffAt ℝ n (fun x : ℝ => x ^ n) (gram u) := contDiffAt_id.pow n
  have hf : ContDiffAt ℝ n gram u := contDiffAt_gram n hu
  rw [hcomp_fun, iteratedDeriv_comp_eq_sum_orderedFinpartition hg hf le_rfl]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [iteratedDeriv_pow]

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
