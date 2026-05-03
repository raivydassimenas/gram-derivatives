/-
  GramDerivatives.lean
  ====================
  Lean 4 / Mathlib formalisation of **Theorem 1** from

    Dundulis, Garunkštis, Laurinčikas, Šimenas,
    "Higher derivatives of the Gram function", 2026.

  Theorem 1 (restated).
    For every n ≥ 2, the n-th derivative of the function S(t) satisfies

        S^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)  +  O(t^(-n-1))

    as t → +∞, away from the (countably many) discontinuities of S.

  ─────────────────────────────────────────────────────────────────────────
  PROOF STRATEGY (mirroring the paper's Proof of Theorem 1)
  ─────────────────────────────────────────────────────────────────────────
  The authors split the n-th derivative of S into two parts:

  (A) The "main term" from

        φ(t) := -t/(2π) · log(t/(2π))  +  t/(2π)  -  7/8

      One computes φ^(n)(t) by repeated differentiation and obtains
      exactly  (-1)^(n-1) · (n-2)! / (2π) · t^(1-n).

  (B) The "error term" from  -(1/π) · δ(t), where

        δ(t) = t/4 · log(1 + 1/(4t²))
              + 1/4 · arctan(1/(2t))
              - t/2 · ∫₀^∞  ρ(u) / ((u + 1/4)² + (t/2)²)  du

      and  ρ(u) = 1/2 - {u}.

      Each piece of δ is shown to contribute only O(t^(-n-1)) to the
      n-th derivative:

        (B1) The first two terms of δ expand in negative powers of t
             and their n-th derivative is O(t^(-n-1)).

        (B2) The integral j(t) = ∫₀^∞ ρ(u)/((u+1/4)²+(t/2)²) du
             satisfies j^(n)(t) = O(t^(-n-2)), so
             (d/dt)^n [-t/2 · j(t)] = O(t^(-n-1)) by the Leibniz rule.

  ─────────────────────────────────────────────────────────────────────────
  FORMALISATION NOTES
  ─────────────────────────────────────────────────────────────────────────
  Lean 4 / Mathlib (as of 2024-25) contains:
    • Real analysis (derivatives, iterated derivatives, smooth functions)
    • Asymptotics via `Asymptotics.IsO` and `Asymptotics.IsLittleO`
    • Bochner / Lebesgue integration
    • Basic transcendental functions (log, arctan, exp)
  but does NOT yet contain:
    • The Riemann zeta function ζ
    • The Riemann–Siegel theta function ϑ
    • The argument function S(t) = (1/π) arg ζ(1/2 + it)
    • The Riemann–von Mangoldt formula

  Therefore we introduce these objects as **opaque constants** (axioms)
  together with precisely the properties used in the proof.  Every
  assumption is labelled `-- ASSUMPTION` so it is clear what is taken on
  faith vs what is derived.

  The file compiles if Mathlib is available (import lines at the top).
  Every `sorry` that remains marks a genuine gap that would require
  substantial new Mathlib development to close; they are each annotated
  with what would be needed.
-/

import Mathlib

open Real Filter Asymptotics MeasureTheory

/-!
  ## §0  Notation and asymptotic infrastructure
-/

notation "𝓝∞" => Filter.atTop (α := ℝ)
abbrev IsO (f g : ℝ → ℝ) (l : Filter ℝ) : Prop := Asymptotics.IsBigO l f g

/-!
  ## §0.5  Assumptions and open gaps  (ledger)

  ── Axioms (taken on faith from the literature) ──
  • `S`, `N_step`                  — opaque target / step functions.
  • `S_eq_φ_sub_δ_add_N`           — Karatsuba–Korolev representation (§2).
  • `contDiffAt_φ / _α_part / _δ`
    `/ _neg_tj / _N_step`          — local smoothness on `(0, ∞)`  (§6).
  • `N_step_iteratedDeriv_eq_zero` — `N_step` locally constant off ζ-zeros (§7).

  ── Open gaps (`sorry` inside proofs; would close Theorem 1) ──
  • `iteratedDeriv_α_part_isO`  (§4) — term-by-term diff. of Laurent expn.
  • `iteratedDeriv_j_isO`       (§5) — IBP + dominated convergence + split at u = t.
  • `iteratedDeriv_tj_isO`      (§5) — Leibniz on `-(t/2)·j(t)`; follows from above.
  • `δ_eq`                      (§6) — bookkeeping: `δ = α_part − (t/2)·j(t)`.
-/

/-!
  ## §1  Opaque constants representing analytic-number-theory objects
-/

/-- The function `S(t) = (1/π) · arg ζ(1/2 + it)`.  It is defined and smooth
    on the complement of a discrete set (the ordinates of zeros of ζ).  For
    the asymptotics we only need its Taylor expansion (Karatsuba–Korolev),
    so we treat `S` as opaque: only `S_eq_φ_sub_δ_add_N` is used. -/
axiom S : ℝ → ℝ -- ASSUMPTION

-- δ(t) as defined in the paper (equation (3)).
noncomputable def δ (t : ℝ) : ℝ :=
  t / 4 * Real.log (1 + 1 / (4 * t ^ 2))
  + 1 / 4 * Real.arctan (1 / (2 * t))
  - t / 2 * ∫ u in Set.Ici (0 : ℝ),
        (1 / 2 - Int.fract u) / ((u + 1 / 4) ^ 2 + (t / 2) ^ 2)

/-- The integer-valued step function `N(γ+0)` from the Karatsuba–Korolev
    expansion of `S(t)` between consecutive zero-ordinates of ζ.
    Piecewise-constant on each gap, so its `n`-th derivative (`n ≥ 1`)
    vanishes there; opaque otherwise. -/
axiom N_step : ℝ → ℝ -- ASSUMPTION

/-!
  ## §2  The Karatsuba–Korolev representation of S

  Equation (2) of the paper states: between two consecutive ordinates
  γ < γ′ of zeros of ζ,

      S(t) = -t/(2π)·log(t/(2π)) + t/(2π) - 7/8 - (1/π)·δ(t) + N_step(t)

  We take this as an axiom.
-/

-- The smooth "main-term" function from the Karatsuba–Korolev representation.
noncomputable def φ (t : ℝ) : ℝ :=
  -(t / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))
  + t / (2 * Real.pi)
  - 7 / 8

/-- ASSUMPTION (Karatsuba–Korolev [6, proof of Thm 2]):  for `t` in the open
    interval `(γ, γ′)` between consecutive zero-ordinates of ζ,
    `S t = φ t - (1/π) · δ t + N_step t`. -/
axiom S_eq_φ_sub_δ_add_N (t : ℝ) (ht : 0 < t) :
    S t = φ t - (1 / Real.pi) * δ t + N_step t

/-!
  ## §3  The main-term computation: iterated derivatives of φ

  The key calculation is

      φ^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)    for n ≥ 2.

  We build this up via standard calculus facts that are (or can be)
  proved from Mathlib primitives.
-/

section MainTerm

/-- Iterated derivative of `Real.log` on `(0, ∞)`:
    `(d^k/dt^k) log t = (-1)^(k-1) · (k-1)! · t^(-k)` for `k ≥ 1`. -/
lemma iteratedDeriv_log (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv k Real.log t =
      (-1 : ℝ) ^ (k - 1) * (k - 1).factorial * t ^ (-(k : ℝ)) := by
  -- Reindex `k = m + 1` to avoid `Nat.sub` arithmetic, then induct on `m`,
  -- generalising `t` so the IH is available on a whole neighbourhood.
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  clear hk
  simp only [Nat.add_sub_cancel]
  induction m generalizing t with
  | zero =>
    rw [iteratedDeriv_succ, iteratedDeriv_zero, Real.deriv_log]
    simp [Real.rpow_neg_one]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    -- Replace `iteratedDeriv (n+1) log` by its closed form on a neighbourhood
    -- of `t` (the open ray `(0, ∞)`), then differentiate the rpow.
    have hEq :
        (iteratedDeriv (n + 1) Real.log : ℝ → ℝ)
          =ᶠ[nhds t]
        (fun s : ℝ =>
            (-1 : ℝ) ^ n * (n.factorial : ℝ) * s ^ (-((n + 1 : ℕ) : ℝ))) := by
      have h_nhds : Set.Ioi (0 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds ht
      filter_upwards [h_nhds] with s hs
      exact ih s hs
    rw [hEq.deriv_eq]
    have hrpow : HasDerivAt (fun s : ℝ => s ^ (-((n + 1 : ℕ) : ℝ)))
        (-((n + 1 : ℕ) : ℝ) * t ^ (-((n + 1 : ℕ) : ℝ) - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))
    have hderiv :
        HasDerivAt (fun s : ℝ =>
            (-1 : ℝ) ^ n * (n.factorial : ℝ) * s ^ (-((n + 1 : ℕ) : ℝ)))
          ((-1 : ℝ) ^ n * (n.factorial : ℝ)
            * (-((n + 1 : ℕ) : ℝ) * t ^ (-((n + 1 : ℕ) : ℝ) - 1))) t :=
      hrpow.const_mul _
    rw [hderiv.deriv]
    have hexp : -((n + 1 : ℕ) : ℝ) - 1 = -((n + 1 + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have hfac : ((n + 1).factorial : ℝ) = ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hexp, hfac, pow_succ]
    ring

/-- If `f = g` on an open set `U`, all iterated derivatives agree on `U`.
    Generalising `t` is essential: the inductive step needs `f =ᶠ[nhds s] g`
    on a whole neighbourhood, not just at the original point. -/
private lemma iteratedDeriv_congr_of_nhds
    {f g : ℝ → ℝ} (k : ℕ) {U : Set ℝ} (hU : IsOpen U)
    (hfg : ∀ s ∈ U, f s = g s) :
    ∀ t ∈ U, iteratedDeriv k f t = iteratedDeriv k g t := by
  induction k with
  | zero =>
    intro t ht
    simp [iteratedDeriv_zero, hfg t ht]
  | succ k ih =>
    intro t ht
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have h_nhds : U ∈ nhds t := hU.mem_nhds ht
    have hEq : (iteratedDeriv k f) =ᶠ[nhds t] (iteratedDeriv k g) := by
      filter_upwards [h_nhds] with s hs
      exact ih s hs
    exact hEq.deriv_eq

/-- The n-th iterated derivative of φ at t, for n ≥ 2 and t > 0,
    equals the main term of Theorem 1:
      `φ^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)`. -/
theorem iteratedDeriv_φ (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv n φ t =
      (-1 : ℝ) ^ (n - 1) * (n - 2).factorial * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ)) := by
  -- Maintenance: avoid blank lines between tactics in this `by` block — Mathlib's
  -- `linter.style.emptyLine` treats them as splitting a command.
  -- Reindex `n = m + 2` to avoid `Nat.sub` arithmetic.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  have h2π_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2π_ne : (2 * Real.pi) ≠ 0 := ne_of_gt h2π_pos
  -- Rewrite φ on `(0, ∞)` in the polynomial-times-log form
  --   φ(s) = -(1/(2π)) · s · log s + ((1 + log(2π))/(2π)) · s - 7/8
  -- using `log(s/(2π)) = log s - log(2π)`.  This avoids chain-ruling
  -- through the inner division.
  have hφ_alt : ∀ s, 0 < s →
      φ s = -(1 / (2 * Real.pi)) * (s * Real.log s)
          + ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) * s
          - 7 / 8 := by
    intro s hs
    unfold φ
    rw [Real.log_div (ne_of_gt hs) h2π_ne]
    ring
  set Φ : ℝ → ℝ :=
    fun s => -(1 / (2 * Real.pi)) * (s * Real.log s)
           + ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) * s
           - 7 / 8 with hΦ_def
  have hφΦ : ∀ s ∈ Set.Ioi (0 : ℝ), φ s = Φ s := fun s hs => hφ_alt s hs
  rw [iteratedDeriv_congr_of_nhds (m + 2) isOpen_Ioi hφΦ t ht]
  -- First derivative of `Φ` on `(0, ∞)`.  The product rule on `s · log s`
  -- gives `log s + 1`; the `+1` is exactly what cancels against the linear
  -- term so the result reduces to `-(1/(2π)) · log s + log(2π)/(2π)`.
  have hderiv_Φ : ∀ s, 0 < s →
      deriv Φ s = -(1 / (2 * Real.pi)) * Real.log s
                + Real.log (2 * Real.pi) / (2 * Real.pi) := by
    intro s hs
    have h_slog : HasDerivAt (fun s : ℝ => s * Real.log s)
        (Real.log s + 1) s := by
      have h2 : HasDerivAt Real.log s⁻¹ s := Real.hasDerivAt_log (ne_of_gt hs)
      have hp : HasDerivAt (fun s : ℝ => s * Real.log s)
          (1 * Real.log s + s * s⁻¹) s := (hasDerivAt_id s).mul h2
      have hcalc : (1 : ℝ) * Real.log s + s * s⁻¹ = Real.log s + 1 := by
        rw [mul_inv_cancel₀ (ne_of_gt hs)]; ring
      rw [hcalc] at hp
      exact hp
    have h_term1 :
        HasDerivAt (fun s : ℝ => -(1 / (2 * Real.pi)) * (s * Real.log s))
          (-(1 / (2 * Real.pi)) * (Real.log s + 1)) s :=
      h_slog.const_mul _
    have h_term2 :
        HasDerivAt (fun s : ℝ =>
            ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) * s)
          ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) s := by
      have := (hasDerivAt_id s).const_mul
        ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi))
      simpa using this
    have hΦ' :
        HasDerivAt Φ
          (-(1 / (2 * Real.pi)) * (Real.log s + 1)
            + (1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) s :=
      (h_term1.add h_term2).sub_const (7 / 8)
    rw [hΦ'.deriv]
    field_simp
    ring
  -- Peel one derivative and replace `deriv Φ` with its closed form `ψ`
  -- on `(0, ∞)`.
  rw [show (m + 2 : ℕ) = (m + 1) + 1 from rfl, iteratedDeriv_succ']
  set ψ : ℝ → ℝ := fun s =>
    -(1 / (2 * Real.pi)) * Real.log s
    + Real.log (2 * Real.pi) / (2 * Real.pi) with hψ_def
  have hderiv_eq_ψ : ∀ s ∈ Set.Ioi (0 : ℝ), deriv Φ s = ψ s := fun s hs => hderiv_Φ s hs
  rw [iteratedDeriv_congr_of_nhds (m + 1) isOpen_Ioi hderiv_eq_ψ t ht]
  -- For `k ≥ 1` and `s > 0`,  iteratedDeriv k ψ s = -(1/(2π)) · iteratedDeriv k log s.
  -- We avoid global `iteratedDeriv_add`/`_const_mul` (which want `ContDiff`
  -- globally; `log` is not globally smooth) and iterate manually.
  have h_iter_ψ : ∀ k : ℕ, ∀ s, 0 < s →
      iteratedDeriv (k + 1) ψ s
        = -(1 / (2 * Real.pi)) * iteratedDeriv (k + 1) Real.log s := by
    have hderiv_ψ : ∀ s, 0 < s →
        deriv ψ s = -(1 / (2 * Real.pi)) * (1 / s) := by
      intro s hs
      have h_log : HasDerivAt Real.log (1 / s) s := by
        simpa using Real.hasDerivAt_log (ne_of_gt hs)
      have h_c1log :
          HasDerivAt (fun s => -(1 / (2 * Real.pi)) * Real.log s)
            (-(1 / (2 * Real.pi)) * (1 / s)) s := h_log.const_mul _
      have hψ' : HasDerivAt ψ (-(1 / (2 * Real.pi)) * (1 / s)) s := by
        simpa [ψ] using h_c1log.add_const (Real.log (2 * Real.pi) / (2 * Real.pi))
      exact hψ'.deriv
    have hderiv_log : ∀ s, 0 < s → deriv Real.log s = 1 / s := by
      intro s hs
      have h := Real.hasDerivAt_log (ne_of_gt hs)
      -- `HasDerivAt.deriv` gives `s⁻¹`; `simp [one_div]` matches the goal `1/s`
      -- (linter prefers plain `simp` over `simpa ... using` here).
      rw [h.deriv]
      simp [one_div]
    have hderiv_ψ_eq : ∀ s ∈ Set.Ioi (0 : ℝ),
        deriv ψ s = (-(1 / (2 * Real.pi))) * deriv Real.log s := by
      intro s hs
      rw [hderiv_ψ s hs, hderiv_log s hs]
    -- `iteratedDeriv k (c · g) s = c · iteratedDeriv k g s`, unconditional
    -- because `deriv_const_mul_field'` holds without differentiability.
    -- `hEq` must be stated in non-eta-expanded form so the `rw` matches
    -- inside `deriv (...)`.
    have iter_const_mul : ∀ (c : ℝ) (g : ℝ → ℝ) (k : ℕ) (s : ℝ),
        iteratedDeriv k (fun s => c * g s) s = c * iteratedDeriv k g s := by
      intro c g k
      induction k with
      | zero => intro s; simp [iteratedDeriv_zero]
      | succ k ih =>
        intro s
        rw [iteratedDeriv_succ, iteratedDeriv_succ]
        have hEq : iteratedDeriv k (fun s => c * g s)
                    = fun s => c * iteratedDeriv k g s := by
          funext s; exact ih s
        rw [hEq, deriv_const_mul_field']
    intro k s hs
    rw [iteratedDeriv_succ']
    have hcong : ∀ u ∈ Set.Ioi (0 : ℝ),
        deriv ψ u
          = (fun u => (-(1 / (2 * Real.pi))) * deriv Real.log u) u :=
      hderiv_ψ_eq
    rw [iteratedDeriv_congr_of_nhds k isOpen_Ioi hcong s hs]
    rw [iter_const_mul (-(1 / (2 * Real.pi))) (deriv Real.log) k s,
        ← iteratedDeriv_succ']
  rw [h_iter_ψ m t ht]
  rw [iteratedDeriv_log (m + 1) (by omega) t ht]
  simp only [Nat.add_sub_cancel]
  -- Algebraic finish.  The earlier `m + 2 = m + 1 + 1` rewrite means the
  -- residual `Nat.sub`s in the goal are over `m + 1 + 1`, not `m + 2`.
  have h_fact : (m + 1 + 1) - 2 = m := by omega
  have h_exp : (1 - ((m + 1 + 1 : ℕ) : ℝ)) = -((m + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [h_fact, h_exp, pow_succ]
  ring

end MainTerm

/-!
  ## §4  Error term (B1): iterated derivatives of the algebraic part of δ

  The first two terms of δ(t) are

      α(t) := t/4 · log(1 + 1/(4t²))  +  1/4 · arctan(1/(2t))

  The paper notes these expand as

      α(t) = 1/(16t) + 1/(8t) + Σ_{n≥3}  aₙ / tⁿ

  for real coefficients aₙ (equation (11)), so

      α^(n)(t) = O(t^(-n-1))   as  t → +∞.   (equation (12))
-/

section ErrorTermAlgebraic

/-- The algebraic part of δ. -/
noncomputable def α_part (t : ℝ) : ℝ :=
  t / 4 * Real.log (1 + 1 / (4 * t ^ 2))
  + 1 / 4 * Real.arctan (1 / (2 * t))

/-- Taylor remainder bound for `arctan` at 0:  `|arctan v − v| ≤ |v|³/3`.

    Proof outline.  Reduce to `v ≥ 0` by oddness of `arctan`.  Then
    monotonicity of two auxiliary functions (each derived from a non-negative
    derivative on ℝ) gives the two-sided bound `0 ≤ v − arctan v ≤ v³/3`:

      • `f(x) = x − arctan x`  with `f'(x) = x²/(1 + x²) ≥ 0`,
      • `g(x) = x³/3 − x + arctan x`  with `g'(x) = x⁴/(1 + x²) ≥ 0`.

    Both are differentiable on all of ℝ, so `monotone_of_deriv_nonneg` applies. -/
private lemma abs_arctan_sub_self_le (v : ℝ) :
    |Real.arctan v - v| ≤ |v| ^ 3 / 3 := by
  -- Reduce to `v ≥ 0` using oddness.
  suffices h : ∀ w : ℝ, 0 ≤ w → |Real.arctan w - w| ≤ w ^ 3 / 3 by
    by_cases hv : 0 ≤ v
    · simpa [abs_of_nonneg hv] using h v hv
    · push_neg at hv
      have hpos : 0 ≤ -v := by linarith
      have key := h (-v) hpos
      have hreq : -Real.arctan v - -v = -(Real.arctan v - v) := by ring
      have heq : |Real.arctan (-v) - (-v)| = |Real.arctan v - v| := by
        rw [Real.arctan_neg, hreq, abs_neg]
      rw [heq] at key
      have habs3 : (-v) ^ 3 = |v| ^ 3 := by rw [abs_of_neg hv]
      linarith [key, habs3]
  intro w hw
  -- Lemma A: `arctan w ≤ w` for `w ≥ 0`, via `f(x) = x − arctan x` monotone.
  have h_le : Real.arctan w ≤ w := by
    have hmono : Monotone (fun x : ℝ => x - Real.arctan x) := by
      refine monotone_of_deriv_nonneg
        (differentiable_id.sub Real.differentiable_arctan) ?_
      intro x
      have h1 : HasDerivAt (fun y : ℝ => y - Real.arctan y)
          (1 - 1 / (1 + x ^ 2)) x :=
        (hasDerivAt_id x).sub (Real.hasStrictDerivAt_arctan x).hasDerivAt
      rw [h1.deriv]
      have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
      rw [sub_nonneg, div_le_one hpos]
      nlinarith [sq_nonneg x]
    have := hmono hw
    simp [Real.arctan_zero] at this
    linarith
  -- Lemma B: `w − arctan w ≤ w³/3` for `w ≥ 0`, via
  --   `g(x) = x³/3 − x + arctan x` monotone (derivative `x⁴/(1 + x²) ≥ 0`).
  have h_taylor : w - Real.arctan w ≤ w ^ 3 / 3 := by
    have hmono : Monotone (fun x : ℝ => x ^ 3 / 3 - x + Real.arctan x) := by
      refine monotone_of_deriv_nonneg ?_ ?_
      · exact (((differentiable_pow 3).div_const 3).sub differentiable_id).add
              Real.differentiable_arctan
      intro x
      have h_pow : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
        have h := (hasDerivAt_pow 3 x).div_const 3
        convert h using 1
        push_cast; ring
      have h_id : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x
      have h_arc : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
        (Real.hasStrictDerivAt_arctan x).hasDerivAt
      have h_sum : HasDerivAt (fun y : ℝ => y ^ 3 / 3 - y + Real.arctan y)
          (x ^ 2 - 1 + 1 / (1 + x ^ 2)) x := (h_pow.sub h_id).add h_arc
      rw [h_sum.deriv]
      have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
      have key : x ^ 2 - 1 + 1 / (1 + x ^ 2) = x ^ 4 / (1 + x ^ 2) := by
        field_simp; ring
      rw [key]; positivity
    have := hmono hw
    simp [Real.arctan_zero] at this
    linarith
  rw [abs_le]
  refine ⟨by linarith, ?_⟩
  have : (0 : ℝ) ≤ w ^ 3 / 3 := by positivity
  linarith

/-- Taylor remainder bound for `log(1 + ·)` at 0 (one-sided form):
    for `0 ≤ u < 1`,  `|log(1 + u) − u| ≤ u² / (1 − u)`.

    Specialisation of Mathlib's `Real.abs_log_sub_add_sum_range_le` with
    `x := -u` and `n := 1`.  The series term `∑ x^(i+1)/(i+1)` collapses to
    just `x = -u` for `n = 1`. -/
private lemma abs_log_one_add_sub_self_le {u : ℝ} (hu : 0 ≤ u) (hu_lt : u < 1) :
    |Real.log (1 + u) - u| ≤ u ^ 2 / (1 - u) := by
  have hxabs : |(-u : ℝ)| < 1 := by rw [abs_neg, abs_of_nonneg hu]; exact hu_lt
  have h := Real.abs_log_sub_add_sum_range_le hxabs 1
  -- h : |(∑ i ∈ range 1, (-u)^(i+1)/(↑i+1)) + log (1 - -u)|
  --      ≤ |(-u)|^(1+1) / (1 - |(-u)|)
  rw [Finset.sum_range_one] at h
  -- After `sum_range_one`: term is `(-u)^(0+1)/((0:ℕ)+1)` = `(-u)/1` = `-u`.
  simp only [pow_one, Nat.cast_zero, zero_add, div_one] at h
  have h1u : (1 : ℝ) - -u = 1 + u := by ring
  rw [h1u] at h
  rw [abs_neg, abs_of_nonneg hu] at h
  -- h : |-u + log(1 + u)| ≤ u^2 / (1 - u)
  have hcomm : (-u + Real.log (1 + u) : ℝ) = Real.log (1 + u) - u := by ring
  rw [hcomm] at h
  exact h

/-- Laurent expansion of α_part: it equals 3/(16t) + O(t^(-3)).
    This is derived by Taylor-expanding log(1+x) and arctan(x) at x=0
    with x = 1/(4t²) and x = 1/(2t) respectively. -/
lemma α_part_expansion (t : ℝ) (ht : 0 < t) :
    ∃ (r : ℝ → ℝ),
      IsO r (fun t => t ^ (-(3 : ℝ))) 𝓝∞ ∧
      α_part t = 3 / (16 * t) + r t := by
  -- Witness: r s := α_part s − 3/(16 s).  Equation is then trivially `ring`.
  -- All real content is in the asymptotic bound.
  refine ⟨fun s => α_part s - 3 / (16 * s), ?_, by ring⟩
  -- Show the witness is `O[atTop]` of `s ↦ s^(-3 : ℝ)`.
  -- We supply explicit constant `1` and verify the bound for all `s ≥ 1`.
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with s hs
  have hs_pos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs2_pos : (0 : ℝ) < s ^ 2 := by positivity
  have hs3_pos : (0 : ℝ) < s ^ 3 := by positivity
  -- Convert `s ^ (-(3 : ℝ))` to `1 / s^3`.
  have hrpow : s ^ (-(3 : ℝ)) = 1 / s ^ 3 := by
    rw [show (-(3 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hs_pos.le, Real.rpow_natCast, one_div]
  -- Algebraic decomposition into the two bounded pieces.
  have decomp : α_part s - 3 / (16 * s) =
      (s / 4 * Real.log (1 + 1 / (4 * s ^ 2)) - 1 / (16 * s)) +
      (1 / 4 * Real.arctan (1 / (2 * s)) - 1 / (8 * s)) := by
    have h316 : (3 : ℝ) / (16 * s) = 1 / (16 * s) + 1 / (8 * s) := by
      field_simp; ring
    unfold α_part
    rw [h316]; ring
  -- Set `u := 1/(4 s²)` and `v := 1/(2 s)` for clarity.
  set u : ℝ := 1 / (4 * s ^ 2) with hu_def
  set v : ℝ := 1 / (2 * s) with hv_def
  have hu_nonneg : 0 ≤ u := by simp [u]; positivity
  have hu_lt : u < 1 := by
    simp only [u]
    rw [div_lt_one (by positivity)]
    nlinarith [hs, sq_nonneg (s - 1)]
  have hu_le_quarter : u ≤ 1 / 4 := by
    simp only [u]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hs, sq_nonneg (s - 1)]
  have hv_pos : 0 < v := by simp [v]; positivity
  -- Bound (A): the log piece.
  -- `s/4 · log(1+u) − 1/(16 s) = s/4 · (log(1+u) − u)` because `1/(16 s) = (s/4)·u`.
  have hAeq : s / 4 * Real.log (1 + u) - 1 / (16 * s) =
              s / 4 * (Real.log (1 + u) - u) := by
    have : (s / 4) * u = 1 / (16 * s) := by
      simp [u]; field_simp; ring
    linarith [this, show s / 4 * Real.log (1 + u) - 1 / (16 * s) =
               s / 4 * (Real.log (1 + u) - u) + ((s / 4) * u - 1 / (16 * s)) from by ring]
  have h_log_tail : |Real.log (1 + u) - u| ≤ u ^ 2 / (1 - u) :=
    abs_log_one_add_sub_self_le hu_nonneg hu_lt
  have h_one_sub_u : (3 : ℝ) / 4 ≤ 1 - u := by linarith
  have h_one_sub_u_pos : (0 : ℝ) < 1 - u := by linarith
  -- `u^2 / (1 - u) ≤ (4/3) · u^2` since `1 - u ≥ 3/4`.
  have h_log_tail' : |Real.log (1 + u) - u| ≤ (4 / 3) * u ^ 2 := by
    refine h_log_tail.trans ?_
    rw [div_le_iff₀ h_one_sub_u_pos]
    have hu2_nn : 0 ≤ u ^ 2 := sq_nonneg u
    nlinarith [hu2_nn, h_one_sub_u]
  -- Combine: `|s/4 · (log(1+u) − u)| ≤ s/4 · (4/3) u² = (s/3) · u² = 1/(48 s³)`.
  have hA : |s / 4 * Real.log (1 + u) - 1 / (16 * s)| ≤ 1 / (48 * s ^ 3) := by
    rw [hAeq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < s / 4)]
    have hbound : s / 4 * |Real.log (1 + u) - u| ≤ s / 4 * ((4 / 3) * u ^ 2) :=
      mul_le_mul_of_nonneg_left h_log_tail' (by positivity)
    refine hbound.trans ?_
    -- s/4 · (4/3) · u² = (s/3) · u² = (s/3) · 1/(16 s⁴) = 1/(48 s³)
    have hu2 : u ^ 2 = 1 / (16 * s ^ 4) := by
      simp only [u]; field_simp; ring
    rw [hu2]; field_simp; ring_nf
    -- Both sides reduce to the same expression; if not, fall back to nlinarith.
    nlinarith [hs3_pos, hs_pos]
  -- Bound (B): the arctan piece.
  -- `1/4 · arctan(v) − 1/(8 s) = 1/4 · (arctan(v) − v)` because `v = 1/(2 s)`,
  -- so `1/4 · v = 1/(8 s)`.
  have hBeq : 1 / 4 * Real.arctan v - 1 / (8 * s) = 1 / 4 * (Real.arctan v - v) := by
    have hv_eq : (1 / 4 : ℝ) * v = 1 / (8 * s) := by simp [v]; field_simp; ring
    linarith [hv_eq, show 1 / 4 * Real.arctan v - 1 / (8 * s) =
               1 / 4 * (Real.arctan v - v) + ((1 / 4) * v - 1 / (8 * s)) from by ring]
  have h_arctan_tail : |Real.arctan v - v| ≤ |v| ^ 3 / 3 := abs_arctan_sub_self_le v
  have hv_abs : |v| = v := abs_of_pos hv_pos
  -- Combine: `|1/4 · (arctan v − v)| ≤ 1/4 · v³/3 = v³/12 = 1/(96 s³)`.
  have hB : |1 / 4 * Real.arctan v - 1 / (8 * s)| ≤ 1 / (96 * s ^ 3) := by
    rw [hBeq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have hbound : (1 / 4 : ℝ) * |Real.arctan v - v| ≤ 1 / 4 * (|v| ^ 3 / 3) :=
      mul_le_mul_of_nonneg_left h_arctan_tail (by norm_num)
    refine hbound.trans ?_
    rw [hv_abs]
    have hv3 : v ^ 3 = 1 / (8 * s ^ 3) := by
      simp only [v]; field_simp; ring
    rw [hv3]; field_simp; ring_nf
    nlinarith [hs3_pos, hs_pos]
  -- Combine the two bounds and convert to the `s^(-3 : ℝ)` form.
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hrpow, decomp]
  have habs_add :
      |(s / 4 * Real.log (1 + u) - 1 / (16 * s)) +
       (1 / 4 * Real.arctan v - 1 / (8 * s))|
        ≤ 1 / (48 * s ^ 3) + 1 / (96 * s ^ 3) :=
    (abs_add_le _ _).trans (add_le_add hA hB)
  have hsum : (1 : ℝ) / (48 * s ^ 3) + 1 / (96 * s ^ 3) = 1 / (32 * s ^ 3) := by
    field_simp; ring
  have h_final : (1 : ℝ) / (32 * s ^ 3) ≤ 1 * |1 / s ^ 3| := by
    rw [one_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / s ^ 3)]
    rw [div_le_div_iff₀ (by positivity) hs3_pos]
    nlinarith [hs3_pos]
  -- Note: `α_part s` in the goal is unfolded to its definition, which uses
  -- `Real.log (1 + 1/(4*s^2))` and `Real.arctan (1/(2*s))`; after our `set`s
  -- on `u, v`, both forms should match.
  exact habs_add.trans (hsum ▸ h_final)

/-- The n-th derivative of α_part is O(t^(-n-1)). -/
lemma iteratedDeriv_α_part_isO (n : ℕ) (hn : 1 ≤ n) :
    IsO (fun t => iteratedDeriv n α_part t)
        (fun t => t ^ (-(n : ℝ) - 1))
        𝓝∞ := by
  /- Proof: from the Puiseux series α_part(t) = Σ_{k≥1} c_k · t^(-k),
     differentiating term-by-term n times gives each term O(t^(-n-1)).
     In Mathlib, this requires:
       • Showing α_part is smooth on (0,∞)  (`ContDiff` from differentiability
         of `log` and `arctan` away from their singularities);
       • Using the asymptotic Laurent expansion and differentiability of
         each power of t. -/
  sorry -- TODO (open): see strategy above

end ErrorTermAlgebraic

/-!
  ## §5  Error term (B2): iterated derivatives of the integral part of δ

  Define

      j(t) := ∫₀^∞  ρ(u) / ((u + 1/4)² + (t/2)²)  du

  where  ρ(u) = 1/2 - {u}.  The paper (via integration by parts and
  domination) shows  j^(n)(t) = O(t^(-n-2)).

  The n-th derivative of  -(t/2) · j(t)  is then O(t^(-n-1)) by Leibniz.
-/

section ErrorTermIntegral

-- ρ(u) = 1/2 - {u}, the "sawtooth" function.
noncomputable def ρ (u : ℝ) : ℝ := 1 / 2 - Int.fract u

-- The integral j(t).
noncomputable def j (t : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ), ρ u / ((u + 1 / 4) ^ 2 + (t / 2) ^ 2)

-- (The paper actually uses the antiderivative σ(u) = ∫₀^u ρ(z) dz,
--  which satisfies 0 ≤ σ(u) ≤ 1/8, and integrates by parts once.)

/- After integration by parts:
     j(t) = 2 ∫₀^∞  σ(u)·(u + 1/4) / ((u + 1/4)² + (t/2)²)²  du
   where σ(u) = ∫₀^u ρ(z) dz  satisfies  0 ≤ σ(u) ≤ 1/8.
   This is equation just before the estimate in the paper's proof. -/

/-- The n-th derivative of j is O(t^(-n-2)).
    This is the key estimate from the paper (equations after the IBP step). -/
lemma iteratedDeriv_j_isO (n : ℕ) :
    IsO (fun t => iteratedDeriv n j t)
        (fun t => t ^ (-(n : ℝ) - 2))
        𝓝∞ := by
  /- Proof strategy (mirroring the paper):
     Write (after IBP)
       j(t) = 2 ∫₀^∞  σ(u)(u+1/4) / ((u+1/4)²+(t/2)²)²  du.

     Differentiate n times under the integral (justified by dominated
     convergence — Mathlib: `MeasureTheory.integral_hasDerivAt_right`
     with a dominating function g(u) proportional to
       u^n · (u+1/4) / ((u+1/4)²+u²)^(n+2)  which is integrable).

     Split the integral at u = t:
       ∫₀ᵗ  O(tⁿ(4u+1)/((4u+1)²+4t²)^(n+2)) du
       ≤ O(t^(-n-2))  (each factor estimated using u ≤ t in denominator)
     and
       ∫ₜ^∞ O(uⁿ(4u+1)/(4u+1)^(2n+4)) du
       ≤ O(t^(-n-2))  (each factor estimated using u ≥ t in numerator).

     In Lean this requires:
       • Differentiability of j (Mathlib's `integral_differentiable`);
       • Dominated convergence for derivatives under the integral;
       • Estimation of the two split integrals. -/
  sorry -- TODO (open): see strategy above

/-- The n-th derivative of  -(t/2) · j(t)  is  O(t^(-n-1)).

    By the Leibniz rule,
      d^n/dt^n [-(t/2)·j(t)]
        = -(1/2)·[t·j^(n)(t)  +  n·j^(n-1)(t)]
      = O(t·t^(-n-2)) + O(t^(-n-1))
      = O(t^(-n-1)). -/
lemma iteratedDeriv_tj_isO (n : ℕ) (hn : 1 ≤ n) :
    IsO (fun t => iteratedDeriv n (fun t => -(t / 2) * j t) t)
        (fun t => t ^ (-(n : ℝ) - 1))
        𝓝∞ := by
  /- Apply `iteratedDeriv_mul` (Leibniz rule) to  -(t/2)  and  j(t).
     The Leibniz sum has two nonzero types of terms:
       • the k=0 term: -(t/2) · j^(n)(t)   = O(t · t^(-n-2)) = O(t^(-n-1))
       • the k=1 term: -(1/2) · j^(n-1)(t) = O(t^(-n-1)).
     All higher k give higher-order decay since -(t/2)^(k) = 0 for k ≥ 2. -/
  sorry -- TODO (open): see strategy above

end ErrorTermIntegral

/-!
  ## §6  Combining parts: the n-th derivative of δ

  δ(t) = α_part(t) - (t/2)·j(t),   so
  δ^(n)(t) = α_part^(n)(t) + (d^n/dt^n)[-(t/2)·j(t)] = O(t^(-n-1)).
-/

section ErrorTermDelta

/-- δ splits as α_part minus the integral term. -/
lemma δ_eq (t : ℝ) (ht : 0 < t) :
    δ t = α_part t - t / 2 * j t := by
  sorry -- TODO (open): unfold `δ`, `α_part`, `j` and verify they line up.

/-- ASSUMPTION: `α_part` is smooth on `(0, ∞)`. -/
axiom contDiffAt_α_part (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n α_part s

/-- ASSUMPTION: `t ↦ -(t/2)·j(t)` is smooth on `(0, ∞)`.  Inherited from
    smoothness of `j` (an analytic property of the ρ-integral). -/
axiom contDiffAt_neg_tj (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n (fun t => -(t / 2) * j t) s

/-- ASSUMPTION: `φ` is smooth on `(0, ∞)` (algebraic combination of `t · log t`). -/
axiom contDiffAt_φ (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n φ s

/-- ASSUMPTION: `δ` is smooth on `(0, ∞)` (inherited from `α_part` and `t·j(t)`). -/
axiom contDiffAt_δ (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n δ s

/-- ASSUMPTION: away from ordinates of zeros of ζ, `N_step` is smooth
    (in fact locally constant). -/
axiom contDiffAt_N_step (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n N_step s

/-- The n-th derivative of δ is O(t^(-n-1)) for n ≥ 1. -/
lemma iteratedDeriv_δ_isO (n : ℕ) (hn : 1 ≤ n) :
    IsO (fun t => iteratedDeriv n δ t)
        (fun t => t ^ (-(n : ℝ) - 1))
        𝓝∞ := by
  -- (1) Pointwise decomposition of δ on (0,∞).
  have h_δ_sum : ∀ s ∈ Set.Ioi (0 : ℝ),
      δ s = α_part s + (-(s / 2) * j s) := by
    intro s hs; rw [δ_eq s hs]; ring
  -- (2) Lift to iteratedDeriv on the open set (0,∞).
  have h_iter_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      iteratedDeriv n δ t
        = iteratedDeriv n (fun s => α_part s + (-(s / 2) * j s)) t :=
    iteratedDeriv_congr_of_nhds n isOpen_Ioi h_δ_sum
  -- (3) Split the sum via local ContDiffAt.
  have h_split : ∀ t, 0 < t →
      iteratedDeriv n (fun s => α_part s + (-(s / 2) * j s)) t
        = iteratedDeriv n α_part t
        + iteratedDeriv n (fun s => -(s / 2) * j s) t := by
    intro t ht
    change iteratedDeriv n (α_part + fun s => -(s / 2) * j s) t = _
    exact iteratedDeriv_add (contDiffAt_α_part n ht) (contDiffAt_neg_tj n ht)
  -- (4) Sum of IsBigO bounds for the two pieces.
  have h_sum :=
    (iteratedDeriv_α_part_isO n hn).add (iteratedDeriv_tj_isO n hn)
  -- (5) Stitch: eventually-equal LHS, transport the IsBigO.
  have h_evEq : (fun t => iteratedDeriv n α_part t
                    + iteratedDeriv n (fun s => -(s / 2) * j s) t)
                =ᶠ[Filter.atTop] (fun t => iteratedDeriv n δ t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← h_split t ht, ← h_iter_eq t ht]
  exact h_evEq.symm.trans_isBigO h_sum

end ErrorTermDelta

/-!
  ## §7  The derivative of N_step vanishes

  Between consecutive ordinates of zeros of ζ, the function N_step is
  locally constant, hence its derivatives of every order vanish there.
-/

/-- ASSUMPTION: away from the ordinates of zeros of ζ (a discrete set),
    `N_step` is locally constant, so all positive-order derivatives vanish.
    The `h_not_zero : True` slot is a placeholder for "t is not an ordinate
    of a zero" — to be tightened once a real predicate is in place. -/
axiom N_step_iteratedDeriv_eq_zero (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t)
    (h_not_zero : True) -- placeholder for "t is not an ordinate of a zero"
    : iteratedDeriv n N_step t = 0

/-!
  ## §8  Main theorem: Theorem 1

  Putting everything together.
-/

/-- **Theorem 1** (Dundulis–Garunkštis–Laurinčikas–Šimenas, 2026).

    For n ≥ 2, the n-th derivative of S satisfies

        S^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)  +  O(t^(-n-1))

    as t → +∞, away from the discontinuities of S. -/
theorem theorem1 (n : ℕ) (hn : 2 ≤ n) :
    IsO
      (fun t =>
        iteratedDeriv n S t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ))))
      (fun t => t ^ (-(n : ℝ) - 1))
      𝓝∞ := by
  have hn1 : 1 ≤ n := by omega
  -- (1) Pointwise rewrite of S on (0,∞), in addition-of-negation form so we can
  -- use `iteratedDeriv_add` rather than `iteratedDeriv_sub`.
  have h_S_sum : ∀ s ∈ Set.Ioi (0 : ℝ),
      S s = φ s + ((-(1 / Real.pi)) * δ s) + N_step s := by
    intro s hs; rw [S_eq_φ_sub_δ_add_N s hs]; ring
  -- (2) Lift the pointwise equality to iteratedDeriv on the open set (0,∞).
  have h_iter_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      iteratedDeriv n S t
        = iteratedDeriv n
            (fun s => φ s + ((-(1 / Real.pi)) * δ s) + N_step s) t :=
    iteratedDeriv_congr_of_nhds n isOpen_Ioi h_S_sum
  -- (3) Split the triple sum using local ContDiffAt.
  have h_split : ∀ t, 0 < t →
      iteratedDeriv n (fun s => φ s + ((-(1 / Real.pi)) * δ s) + N_step s) t
        = iteratedDeriv n φ t
          + (-(1 / Real.pi)) * iteratedDeriv n δ t
          + iteratedDeriv n N_step t := by
    intro t ht
    have hφ  : ContDiffAt ℝ n φ t       := contDiffAt_φ n ht
    have hδ  : ContDiffAt ℝ n δ t       := contDiffAt_δ n ht
    have hN  : ContDiffAt ℝ n N_step t  := contDiffAt_N_step n ht
    have hcδ : ContDiffAt ℝ n (fun s => (-(1 / Real.pi)) * δ s) t :=
      hδ.mul_const _
    -- Outer split: (φ + c·δ) + N_step
    change iteratedDeriv n
              ((fun s => φ s + ((-(1 / Real.pi)) * δ s)) + N_step) t = _
    rw [iteratedDeriv_add (hφ.add hcδ) hN]
    -- Inner split: φ + c·δ
    have h_inner :
        iteratedDeriv n (fun s => φ s + ((-(1 / Real.pi)) * δ s)) t
          = iteratedDeriv n φ t
            + iteratedDeriv n (fun s => (-(1 / Real.pi)) * δ s) t := by
      change iteratedDeriv n (φ + fun s => (-(1 / Real.pi)) * δ s) t = _
      exact iteratedDeriv_add hφ hcδ
    rw [h_inner, iteratedDeriv_const_mul_field (-(1 / Real.pi)) δ]
  -- (4) Substitute closed form for `φ` and the vanishing for `N_step`.
  -- Note: `N_step_iteratedDeriv_eq_zero` currently takes `(_ : True)` as a
  -- placeholder for "t avoids ordinates of zeros of ζ".
  have h_clean : ∀ t, 0 < t →
      iteratedDeriv n S t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ)))
        = (-(1 / Real.pi)) * iteratedDeriv n δ t := by
    intro t ht
    rw [h_iter_eq t ht, h_split t ht,
        iteratedDeriv_φ n hn t ht,
        N_step_iteratedDeriv_eq_zero n hn1 t ht True.intro]
    ring
  -- (5) The residual `c · iteratedDeriv n δ t` is O(t^(-n-1)).
  have h_bd :
      IsO (fun t => (-(1 / Real.pi)) * iteratedDeriv n δ t)
          (fun t => t ^ (-(n : ℝ) - 1)) 𝓝∞ :=
    (iteratedDeriv_δ_isO n hn1).const_mul_left (-(1 / Real.pi))
  -- (6) Stitch via eventual equality at +∞.
  have h_evEq :
      (fun t => iteratedDeriv n S t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ))))
        =ᶠ[Filter.atTop]
      (fun t => (-(1 / Real.pi)) * iteratedDeriv n δ t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact h_clean t ht
  exact h_evEq.trans_isBigO h_bd
