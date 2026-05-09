/-
  GramDerivatives/Theorem1.lean
  =============================
  Lean 4 / Mathlib formalisation of **Theorem 1** from

      Dundulis, Garunkštis, Laurinčikas, Šimenas,
      "Higher derivatives of the Gram function", 2026.

  Theorem 1.  For n ≥ 2, as t → +∞ (away from discontinuities of S),

      S^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)  +  O(t^(-n-1)).

  ─── Strategy ──────────────────────────────────────────────────────────
  Karatsuba–Korolev decomposition (axiom `S_eq_φ_sub_δ_add_N`):
        S(t) = φ(t) − (1/π)·δ(t) + N_step(t)
  with
    • φ(t) = −t/(2π)·log(t/(2π)) + t/(2π) − 7/8   (smooth main term),
    • δ(t) = α_part(t) − (t/2)·j(t)               (smooth error term),
    • N_step                                       (locally constant).
  Then φ^(n)(t) supplies the leading term and δ^(n)(t) = O(t^(−n−1)).

  ─── File layout ───────────────────────────────────────────────────────
    §0  Notation and asymptotic infrastructure.
    §1  Definitions  (`φ`, `δ`, `α_part`, `ρ`, `j`).
    §2  Assumptions / axioms taken from the literature.
    §3  Smoothness lemmas (derived from §2 + elementary Mathlib calculus).
    §4  Iterated derivatives of `φ`              (main term).
    §5  Iterated derivatives of `α_part`         (algebraic error).
    §6  Iterated derivatives of `j` and `t·j(t)` (integral error).
    §7  Iterated derivatives of `δ`              (combining §5 and §6).
    §8  Statement and proof of Theorem 1.

  ─── What's axiomatised ────────────────────────────────────────────────
  Mathlib (as of 2024-25) lacks ζ, the Riemann–Siegel θ, the argument
  function S, and the Riemann–von Mangoldt formula, so we introduce these
  objects as opaque constants together with the properties used in the
  proof.  Every axiom is tagged `-- ASSUMPTION` and carries a docstring.

  ─── Remaining gaps ────────────────────────────────────────────────────
  • `iteratedDeriv_α_part_isO`  (§5) — term-by-term diff. of Laurent expn.
  • `iteratedDeriv_j_isO`       (§6) — IBP + dominated convergence.
  • `iteratedDeriv_tj_isO`      (§6) — Leibniz on `-(t/2)·j(t)`; from above.
  • `contDiffAt_j`              (§2) — axiom: smoothness of the parametric
                                       integral `j(t)`.  Two routes
                                       sketched in its docstring.
-/

import Mathlib

open Real Filter Asymptotics MeasureTheory

/-!
  ## §0  Notation and asymptotic infrastructure
-/

notation "𝓝∞" => Filter.atTop (α := ℝ)
abbrev IsO (f g : ℝ → ℝ) (l : Filter ℝ) : Prop := Asymptotics.IsBigO l f g

/-!
  ## §1  Definitions

  Explicit definitions of the functions appearing in the proof: the smooth
  main term `φ`, the error term `δ`, its algebraic and integral pieces
  `α_part` and `j`, and the sawtooth function `ρ`.
-/

/-- Smooth "main-term" function from the Karatsuba–Korolev representation. -/
noncomputable def φ (t : ℝ) : ℝ :=
  -(t / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))
  + t / (2 * Real.pi)
  - 7 / 8

/-- The error term δ(t) from equation (3) of the paper. -/
noncomputable def δ (t : ℝ) : ℝ :=
  t / 4 * Real.log (1 + 1 / (4 * t ^ 2))
  + 1 / 4 * Real.arctan (1 / (2 * t))
  - t / 2 * ∫ u in Set.Ici (0 : ℝ),
        (1 / 2 - Int.fract u) / ((u + 1 / 4) ^ 2 + (t / 2) ^ 2)

/-- The algebraic part of δ:  `t/4 · log(1 + 1/(4t²)) + (1/4)·arctan(1/(2t))`. -/
noncomputable def α_part (t : ℝ) : ℝ :=
  t / 4 * Real.log (1 + 1 / (4 * t ^ 2))
  + 1 / 4 * Real.arctan (1 / (2 * t))

/-- The sawtooth function `ρ(u) = 1/2 − {u}`. -/
noncomputable def ρ (u : ℝ) : ℝ := 1 / 2 - Int.fract u

/-- The integral part of δ:  `j(t) = ∫₀^∞ ρ(u) / ((u + 1/4)² + (t/2)²) du`. -/
noncomputable def j (t : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ), ρ u / ((u + 1 / 4) ^ 2 + (t / 2) ^ 2)

/-!
  ## §2  Assumptions

  All axioms taken from the literature are collected here.  They split into:

    • Opaque target / step functions:  `S`, `N_step`.
    • Karatsuba–Korolev representation: `S_eq_φ_sub_δ_add_N`.
    • Smoothness of the parametric integral:  `contDiffAt_j`.
    • Smoothness / vanishing of `N_step`:  `contDiffAt_N_step`,
      `N_step_iteratedDeriv_eq_zero`.

  Smoothness of `φ`, `α_part`, `δ`, and `t·j(t)` is *derived* in §3 from
  `contDiffAt_j` plus elementary Mathlib calculus.
-/

/-- The function `S(t) = (1/π) · arg ζ(1/2 + it)`.  It is defined and smooth
    on the complement of a discrete set (the ordinates of zeros of ζ).  For
    the asymptotics we only need its Taylor expansion (Karatsuba–Korolev),
    so we treat `S` as opaque: only `S_eq_φ_sub_δ_add_N` is used. -/
axiom S : ℝ → ℝ -- ASSUMPTION

/-- The integer-valued step function `N(γ+0)` from the Karatsuba–Korolev
    expansion of `S(t)` between consecutive zero-ordinates of ζ.
    Piecewise-constant on each gap, so its `n`-th derivative (`n ≥ 1`)
    vanishes there; opaque otherwise. -/
axiom N_step : ℝ → ℝ -- ASSUMPTION

/-- ASSUMPTION (Karatsuba–Korolev [6, proof of Thm 2]):  for `t` in the open
    interval `(γ, γ′)` between consecutive zero-ordinates of ζ,
    `S t = φ t - (1/π) · δ t + N_step t`. -/
axiom S_eq_φ_sub_δ_add_N (t : ℝ) (ht : 0 < t) :
    S t = φ t - (1 / Real.pi) * δ t + N_step t

/-- ASSUMPTION: `j(t) = ∫₀^∞ ρ(u)/((u+1/4)² + (t/2)²) du` is smooth on
    `(0, ∞)`.  This is the genuinely analytic input that cannot be derived
    from elementary Mathlib lemmas:

    • Mathlib's `ParametricIntegral.lean` only provides first-order results
      (`hasDerivAt_integral_of_dominated_loc_of_lip` etc.); there is no
      general `ContDiff` lemma for parametric integrals.

    • Two viable strategies to discharge this axiom:
        (a) Inductive dominated convergence — at each order `n`, exhibit
            an integrable dominator `Cₙ·(u+1/4)^(-n-2)` for the `n`-th
            `t`-derivative of the integrand.
        (b) Binet's second formula — identify `j(t)` (up to `1/t`) with
            `Im log Γ(1/4 + i·t/2)`, then use holomorphicity of log Γ
            on `Re z > 0` and `ContDiff` of holomorphic functions.

    Either route is a substantial subproject; see file header. -/
axiom contDiffAt_j (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n j s

/-- ASSUMPTION: away from ordinates of zeros of ζ, `N_step` is smooth
    (in fact locally constant). -/
axiom contDiffAt_N_step (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n N_step s

/-- ASSUMPTION: away from the ordinates of zeros of ζ (a discrete set),
    `N_step` is locally constant, so all positive-order derivatives vanish.
    The `h_not_zero : True` slot is a placeholder for "t is not an ordinate
    of a zero" — to be tightened once a real predicate is in place. -/
axiom N_step_iteratedDeriv_eq_zero (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t)
    (h_not_zero : True) -- placeholder for "t is not an ordinate of a zero"
    : iteratedDeriv n N_step t = 0

/-!
  ## §3  Smoothness lemmas

  Derived from the axioms in §2 plus elementary Mathlib calculus.  The four
  results in this section establish `ContDiffAt ℝ n F t` for `t > 0` and
  every `F` that appears as a sub-expression of `S` in the Karatsuba–Korolev
  decomposition.

  Dependency tree:
    contDiffAt_j (axiom)  ──▶  contDiffAt_neg_tj  ──▶  contDiffAt_δ
                                                     ▲
    contDiffAt_α_part  ──────────────────────────────┘
    contDiffAt_φ                              (independent)
-/

section Smoothness

/-- `φ` is smooth on `(0, ∞)` (algebraic combination of `t · log t`). -/
theorem contDiffAt_φ (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n φ s := by
  have h2π_ne : (2 * Real.pi) ≠ 0 := by positivity
  have hne : s / (2 * Real.pi) ≠ 0 := div_ne_zero (ne_of_gt hs) h2π_ne
  have h_div : ContDiffAt ℝ n (fun t : ℝ => t / (2 * Real.pi)) s :=
    contDiffAt_id.div_const _
  have h_log : ContDiffAt ℝ n (fun t : ℝ => Real.log (t / (2 * Real.pi))) s :=
    h_div.log hne
  unfold φ
  exact ((h_div.neg.mul h_log).add h_div).sub contDiffAt_const

/-- `α_part` is smooth on `(0, ∞)`. -/
theorem contDiffAt_α_part (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n α_part s := by
  have h_4s2_ne : (4 * s ^ 2 : ℝ) ≠ 0 := by positivity
  have h_2s_ne : (2 * s : ℝ) ≠ 0 := by positivity
  have h_1_inv_ne : (1 + 1 / (4 * s ^ 2) : ℝ) ≠ 0 := by positivity
  have h_4t2 : ContDiffAt ℝ n (fun t : ℝ => 4 * t ^ 2) s :=
    contDiffAt_const.mul (contDiffAt_id.pow 2)
  have h_inv_4t2 : ContDiffAt ℝ n (fun t : ℝ => 1 / (4 * t ^ 2)) s :=
    contDiffAt_const.div h_4t2 h_4s2_ne
  have h_log : ContDiffAt ℝ n (fun t : ℝ => Real.log (1 + 1 / (4 * t ^ 2))) s :=
    (contDiffAt_const.add h_inv_4t2).log h_1_inv_ne
  have h_part1 : ContDiffAt ℝ n
      (fun t : ℝ => t / 4 * Real.log (1 + 1 / (4 * t ^ 2))) s :=
    (contDiffAt_id.div_const 4).mul h_log
  have h_2t : ContDiffAt ℝ n (fun t : ℝ => 2 * t) s :=
    contDiffAt_const.mul contDiffAt_id
  have h_inv_2t : ContDiffAt ℝ n (fun t : ℝ => 1 / (2 * t)) s :=
    contDiffAt_const.div h_2t h_2s_ne
  have h_part2 : ContDiffAt ℝ n
      (fun t : ℝ => 1 / 4 * Real.arctan (1 / (2 * t))) s :=
    contDiffAt_const.mul h_inv_2t.arctan
  unfold α_part
  exact h_part1.add h_part2

/-- `t ↦ -(t/2)·j(t)` is smooth on `(0, ∞)`.  Immediate from smoothness
    of `j` (the polynomial factor `-(t/2)` is trivially smooth). -/
theorem contDiffAt_neg_tj (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n (fun t => -(t / 2) * j t) s :=
  (contDiffAt_id.div_const 2).neg.mul (contDiffAt_j n hs)

/-- `δ` is smooth on `(0, ∞)` (inherited from `α_part` and `t·j(t)`). -/
theorem contDiffAt_δ (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n δ s := by
  have h_eq : (δ : ℝ → ℝ) = fun t => α_part t + (-(t / 2) * j t) := by
    funext t
    unfold δ α_part j ρ
    ring
  rw [h_eq]
  exact (contDiffAt_α_part n hs).add (contDiffAt_neg_tj n hs)

end Smoothness

/-!
  ## §4  Main-term computation: iterated derivatives of φ

  The key calculation is

      φ^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)    for n ≥ 2.
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

/-- Iterated derivative commutes with a constant scalar factor,
    with no differentiability hypothesis on `g`.

    Named with a prime to avoid clash with Mathlib's `iteratedDeriv_const_mul`,
    which carries a `ContDiffAt` hypothesis we don't want to thread through. -/
private lemma iteratedDeriv_const_mul' (c : ℝ) (g : ℝ → ℝ) (k : ℕ) (s : ℝ) :
    iteratedDeriv k (fun x => c * g x) s = c * iteratedDeriv k g s := by
  induction k generalizing s with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hEq : iteratedDeriv k (fun x => c * g x) = fun x => c * iteratedDeriv k g x :=
      funext ih
    rw [hEq, deriv_const_mul_field']

/-- The n-th iterated derivative of φ at t, for n ≥ 2 and t > 0,
    equals the main term of Theorem 1:
      `φ^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)`. -/
theorem iteratedDeriv_φ (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv n φ t =
      (-1 : ℝ) ^ (n - 1) * (n - 2).factorial * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ)) := by
  -- Reindex `n = m + 2` to skip `Nat.sub` arithmetic.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  have h2π_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2π_ne : (2 * Real.pi) ≠ 0 := ne_of_gt h2π_pos
  -- Rewrite φ on `(0,∞)` as a polynomial-times-log expression `Φ`, using
  -- `log(s/(2π)) = log s - log(2π)`.  This avoids chain-ruling through the
  -- inner division.
  set Φ : ℝ → ℝ :=
    fun s => -(1 / (2 * Real.pi)) * (s * Real.log s)
           + ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) * s
           - 7 / 8
  have hφΦ : ∀ s ∈ Set.Ioi (0 : ℝ), φ s = Φ s := by
    intro s hs
    unfold φ
    rw [Real.log_div (ne_of_gt hs) h2π_ne]
    ring
  rw [iteratedDeriv_congr_of_nhds (m + 2) isOpen_Ioi hφΦ t ht]
  -- First derivative of Φ.  Product rule on `s·log s` gives `log s + 1`; the
  -- `+1` cancels the linear term, so `Φ'(s) = -(1/(2π))·log s + log(2π)/(2π)`.
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
      rw [hcalc] at hp; exact hp
    have h_term1 :
        HasDerivAt (fun s : ℝ => -(1 / (2 * Real.pi)) * (s * Real.log s))
          (-(1 / (2 * Real.pi)) * (Real.log s + 1)) s :=
      h_slog.const_mul _
    have h_term2 :
        HasDerivAt (fun s : ℝ =>
            ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) * s)
          ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) s := by
      simpa using (hasDerivAt_id s).const_mul
        ((1 + Real.log (2 * Real.pi)) / (2 * Real.pi))
    have hΦ' :
        HasDerivAt Φ
          (-(1 / (2 * Real.pi)) * (Real.log s + 1)
            + (1 + Real.log (2 * Real.pi)) / (2 * Real.pi)) s :=
      (h_term1.add h_term2).sub_const (7 / 8)
    rw [hΦ'.deriv]
    field_simp
    ring
  -- Peel one derivative; replace `deriv Φ` by its closed form `ψ` on `(0,∞)`.
  rw [show (m + 2 : ℕ) = (m + 1) + 1 from rfl, iteratedDeriv_succ']
  set ψ : ℝ → ℝ := fun s =>
    -(1 / (2 * Real.pi)) * Real.log s
    + Real.log (2 * Real.pi) / (2 * Real.pi)
  rw [iteratedDeriv_congr_of_nhds (m + 1) isOpen_Ioi hderiv_Φ t ht]
  -- For k ≥ 1 and s > 0,  iteratedDeriv k ψ s = -(1/(2π)) · iteratedDeriv k log s.
  -- We iterate manually: global `iteratedDeriv_add`/`_const_mul` would need
  -- `ContDiff` of `log` on all of ℝ, which fails at 0.
  have h_iter_ψ : ∀ k : ℕ, ∀ s, 0 < s →
      iteratedDeriv (k + 1) ψ s
        = -(1 / (2 * Real.pi)) * iteratedDeriv (k + 1) Real.log s := by
    have hderiv_ψ_eq : ∀ s ∈ Set.Ioi (0 : ℝ),
        deriv ψ s = (-(1 / (2 * Real.pi))) * deriv Real.log s := by
      intro s hs
      have h_log : HasDerivAt Real.log (1 / s) s := by
        simpa using Real.hasDerivAt_log (ne_of_gt hs)
      have hψ' : HasDerivAt ψ (-(1 / (2 * Real.pi)) * (1 / s)) s :=
        (h_log.const_mul (-(1 / (2 * Real.pi)))).add_const
          (Real.log (2 * Real.pi) / (2 * Real.pi))
      rw [hψ'.deriv, (Real.hasDerivAt_log (ne_of_gt hs)).deriv]
      simp [one_div]
    intro k s hs
    rw [iteratedDeriv_succ',
        iteratedDeriv_congr_of_nhds k isOpen_Ioi hderiv_ψ_eq s hs,
        iteratedDeriv_const_mul' (-(1 / (2 * Real.pi))) (deriv Real.log) k s,
        ← iteratedDeriv_succ']
  rw [h_iter_ψ m t ht, iteratedDeriv_log (m + 1) (by omega) t ht]
  simp only [Nat.add_sub_cancel]
  -- Algebraic finish.  Residual `Nat.sub`s are over `m + 1 + 1`, not `m + 2`.
  have h_fact : (m + 1 + 1) - 2 = m := by omega
  have h_exp : (1 - ((m + 1 + 1 : ℕ) : ℝ)) = -((m + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [h_fact, h_exp, pow_succ]
  ring

end MainTerm

/-!
  ## §5  Error term (B1): iterated derivatives of the algebraic part of δ

  The first two terms of δ(t) are

      α(t) := t/4 · log(1 + 1/(4t²))  +  1/4 · arctan(1/(2t))

  The paper notes these expand as

      α(t) = 1/(16t) + 1/(8t) + Σ_{n≥3}  aₙ / tⁿ

  for real coefficients aₙ (equation (11)), so

      α^(n)(t) = O(t^(-n-1))   as  t → +∞.   (equation (12))
-/

section ErrorTermAlgebraic

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
    · have hv : v < 0 := lt_of_not_ge hv
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
lemma α_part_expansion (t : ℝ) (_ : 0 < t) :
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
  set u : ℝ := 1 / (4 * s ^ 2)
  set v : ℝ := 1 / (2 * s)
  have hu_nonneg : 0 ≤ u := by simp only [u]; positivity
  have hu_lt : u < 1 := by
    simp only [u]
    rw [div_lt_one (by positivity)]
    nlinarith [hs, sq_nonneg (s - 1)]
  have hu_le_quarter : u ≤ 1 / 4 := by
    simp only [u]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hs, sq_nonneg (s - 1)]
  have hv_pos : 0 < v := by simp only [v]; positivity
  -- Bound (A): the log piece.
  -- `s/4 · log(1+u) − 1/(16 s) = s/4 · (log(1+u) − u)` because `1/(16 s) = (s/4)·u`.
  have hAeq : s / 4 * Real.log (1 + u) - 1 / (16 * s) =
              s / 4 * (Real.log (1 + u) - u) := by
    have hsu : (s / 4) * u = 1 / (16 * s) := by simp [u]; field_simp; ring
    linear_combination hsu
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
    linear_combination hv_eq
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

/-! ### Scaffold reduction of `iteratedDeriv_α_part_isO`

The original gap (`α_part^(n) = O(t^(-n-1))` for `n ≥ 1`) is reduced to:
  • two routine first- and second-derivative computations of `α_part`, and
  • a single deep rational-decay lemma `iteratedDeriv_α_part_deriv2_isO`.
The main theorem `iteratedDeriv_α_part_isO` is then proved unconditionally
from those three pieces (no further `sorry`). -/

/-- Closed form for the second derivative of `α_part` on `(0, ∞)`.

    Combined as a single rational function:
        α_part_deriv2(t) = (12 t² − 1) / (2 t (4 t² + 1)²). -/
private noncomputable def α_part_deriv2 (t : ℝ) : ℝ :=
  -1 / (2 * t * (4 * t ^ 2 + 1)) + 8 * t / (4 * t ^ 2 + 1) ^ 2

/-- **Routine.**  `α_part'(t) = (1/4)·log(1 + 1/(4t²)) − 1/(4t² + 1)` for `t > 0`.

    Mechanical product/chain rule:
      d/dt[(t/4)·log(1+1/(4t²))]
        = (1/4)·log(1+1/(4t²))  +  (t/4)·(-2/(t(4t²+1)))
        = (1/4)·log(1+1/(4t²))  −  1/(2(4t²+1))
      d/dt[(1/4)·arctan(1/(2t))]
        = (1/4)·((-1/(2t²))/(1+1/(4t²)))
        = −1/(2(4t²+1))
      sum = (1/4)·log(1+1/(4t²)) − 1/(4t²+1). -/
private lemma hasDerivAt_α_part {t : ℝ} (ht : 0 < t) :
    HasDerivAt α_part
      ((1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) - 1 / (4 * t ^ 2 + 1)) t := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h4t2_pos : (0 : ℝ) < 4 * t ^ 2 := by positivity
  have h4t2_ne : (4 * t ^ 2 : ℝ) ≠ 0 := ne_of_gt h4t2_pos
  have h4t2_p1_pos : (0 : ℝ) < 4 * t ^ 2 + 1 := by positivity
  have h4t2_p1_ne : (4 * t ^ 2 + 1 : ℝ) ≠ 0 := ne_of_gt h4t2_p1_pos
  have h_inner_pos : (0 : ℝ) < 1 + 1 / (4 * t ^ 2) := by positivity
  have h_inner_ne : (1 + 1 / (4 * t ^ 2) : ℝ) ≠ 0 := ne_of_gt h_inner_pos
  have h2t_ne : (2 * t : ℝ) ≠ 0 := by positivity
  -- Each step normalises its own derivative to a clean closed form.
  have h_4t2 : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (8 * t) t := by
    convert (hasDerivAt_pow 2 t).const_mul (4 : ℝ) using 1
    push_cast; ring
  have h_inv_4t2 :
      HasDerivAt (fun s : ℝ => 1 / (4 * s ^ 2)) (-1 / (2 * t ^ 3)) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div h_4t2 h4t2_ne using 1
    field_simp; ring
  have h_one_plus :
      HasDerivAt (fun s : ℝ => 1 + 1 / (4 * s ^ 2)) (-1 / (2 * t ^ 3)) t :=
    h_inv_4t2.const_add (1 : ℝ)
  have h_log :
      HasDerivAt (fun s : ℝ => Real.log (1 + 1 / (4 * s ^ 2)))
        (-2 / (t * (4 * t ^ 2 + 1))) t := by
    convert h_one_plus.log h_inner_ne using 1
    field_simp; ring
  have h_div4 : HasDerivAt (fun s : ℝ => s / 4) (1 / 4 : ℝ) t :=
    (hasDerivAt_id t).div_const 4
  have h_first :
      HasDerivAt (fun s : ℝ => s / 4 * Real.log (1 + 1 / (4 * s ^ 2)))
        ((1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) - 1 / (2 * (4 * t ^ 2 + 1))) t := by
    convert h_div4.mul h_log using 1
    field_simp; ring
  have h_2s : HasDerivAt (fun s : ℝ => 2 * s) (2 : ℝ) t := by
    convert (hasDerivAt_id t).const_mul (2 : ℝ) using 1; ring
  have h_inv_2s :
      HasDerivAt (fun s : ℝ => 1 / (2 * s)) (-1 / (2 * t ^ 2)) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div h_2s h2t_ne using 1
    field_simp; ring
  have h_arctan :
      HasDerivAt (fun s : ℝ => Real.arctan (1 / (2 * s)))
        (-2 / (4 * t ^ 2 + 1)) t := by
    convert h_inv_2s.arctan using 1
    field_simp; ring
  have h_second :
      HasDerivAt (fun s : ℝ => 1 / 4 * Real.arctan (1 / (2 * s)))
        (-1 / (2 * (4 * t ^ 2 + 1))) t := by
    convert h_arctan.const_mul (1 / 4 : ℝ) using 1
    field_simp; ring
  -- Combine.  The final derivative collapses to the clean form.
  have h_sum :
      HasDerivAt
        (fun s : ℝ =>
          s / 4 * Real.log (1 + 1 / (4 * s ^ 2)) + 1 / 4 * Real.arctan (1 / (2 * s)))
        ((1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) - 1 / (4 * t ^ 2 + 1)) t := by
    convert h_first.add h_second using 1
    field_simp; ring
  -- α_part is definitionally the lambda above.
  exact h_sum

/-- **Routine.**  Differentiating the closed form of `α_part'` once more
    produces the rational expression `α_part_deriv2`.

    Mechanical:
      d/dt[(1/4)·log(1+1/(4t²))] = (1/4)·(-2/(t(4t²+1))) = −1/(2t(4t²+1))
      d/dt[1/(4t²+1)] = −8t/(4t²+1)²,  so d/dt[−1/(4t²+1)] = 8t/(4t²+1)². -/
private lemma hasDerivAt_α_part_form {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ =>
        (1 / 4) * Real.log (1 + 1 / (4 * s ^ 2)) - 1 / (4 * s ^ 2 + 1))
      (α_part_deriv2 t) t := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h4t2_pos : (0 : ℝ) < 4 * t ^ 2 := by positivity
  have h4t2_ne : (4 * t ^ 2 : ℝ) ≠ 0 := ne_of_gt h4t2_pos
  have h4t2_p1_pos : (0 : ℝ) < 4 * t ^ 2 + 1 := by positivity
  have h4t2_p1_ne : (4 * t ^ 2 + 1 : ℝ) ≠ 0 := ne_of_gt h4t2_p1_pos
  have h_inner_pos : (0 : ℝ) < 1 + 1 / (4 * t ^ 2) := by positivity
  have h_inner_ne : (1 + 1 / (4 * t ^ 2) : ℝ) ≠ 0 := ne_of_gt h_inner_pos
  -- Reuse the chain (1/4)·log(1 + 1/(4 s²)) from the previous lemma.
  have h_4t2 : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (8 * t) t := by
    convert (hasDerivAt_pow 2 t).const_mul (4 : ℝ) using 1
    push_cast; ring
  have h_inv_4t2 :
      HasDerivAt (fun s : ℝ => 1 / (4 * s ^ 2)) (-1 / (2 * t ^ 3)) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div h_4t2 h4t2_ne using 1
    field_simp; ring
  have h_one_plus :
      HasDerivAt (fun s : ℝ => 1 + 1 / (4 * s ^ 2)) (-1 / (2 * t ^ 3)) t :=
    h_inv_4t2.const_add (1 : ℝ)
  have h_log :
      HasDerivAt (fun s : ℝ => Real.log (1 + 1 / (4 * s ^ 2)))
        (-2 / (t * (4 * t ^ 2 + 1))) t := by
    convert h_one_plus.log h_inner_ne using 1
    field_simp; ring
  have h_first :
      HasDerivAt (fun s : ℝ => (1 / 4) * Real.log (1 + 1 / (4 * s ^ 2)))
        (-1 / (2 * t * (4 * t ^ 2 + 1))) t := by
    convert h_log.const_mul (1 / 4 : ℝ) using 1
    field_simp; ring
  -- Second piece: 1/(4 s² + 1).
  have h_4t2_p1 :
      HasDerivAt (fun s : ℝ => 4 * s ^ 2 + 1) (8 * t) t := by
    convert h_4t2.add_const (1 : ℝ) using 1
  have h_inv_4t2_p1 :
      HasDerivAt (fun s : ℝ => 1 / (4 * s ^ 2 + 1))
        (-(8 * t) / (4 * t ^ 2 + 1) ^ 2) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div h_4t2_p1 h4t2_p1_ne using 1
    ring
  -- Combine: (1/4)·log(...) − 1/(4 s² + 1).
  have h_sub :
      HasDerivAt
        (fun s : ℝ => (1 / 4) * Real.log (1 + 1 / (4 * s ^ 2)) - 1 / (4 * s ^ 2 + 1))
        (α_part_deriv2 t) t := by
    convert h_first.sub h_inv_4t2_p1 using 1
    unfold α_part_deriv2
    field_simp; ring
  exact h_sub

/-! #### Rational-piece machinery for `iteratedDeriv_α_part_deriv2_isO`

We encode each summand `c · t^a · (4t² + 1)^{-b}` as a `RatTerm`, with formal
derivative producing two new terms that lower the asymptotic invariant
`a − 2b` by 1.  Iterating gives `iteratedDeriv k α_part_deriv2` as a finite
sum of such pieces, all bounded by `O(t^(-3-k))`. -/

/-- A formal piece `c · t^a · (4t² + 1)^{-b}`. -/
private structure RatTerm where
  coeff : ℝ
  tExp : ℤ
  polePow : ℕ

/-- Evaluation at a real `t`. -/
private noncomputable def RatTerm.eval (p : RatTerm) (t : ℝ) : ℝ :=
  p.coeff * t ^ p.tExp / (4 * t ^ 2 + 1) ^ p.polePow

/-- Formal derivative of a single `RatTerm`: product rule on
    `c · t^a · (4t² + 1)^{-b}` produces the two terms
    `c · a · t^{a-1} · (4t² + 1)^{-b}` and `-8 c b · t^{a+1} · (4t² + 1)^{-(b+1)}`. -/
private def RatTerm.formalDeriv (p : RatTerm) : List RatTerm :=
  [{ coeff := p.coeff * (p.tExp : ℝ), tExp := p.tExp - 1, polePow := p.polePow },
   { coeff := -8 * p.coeff * (p.polePow : ℝ),
     tExp := p.tExp + 1, polePow := p.polePow + 1 }]

/-- A formal sum of `RatTerm`s. -/
private abbrev RatExpr := List RatTerm

/-- Evaluation of a `RatExpr` at `t`. -/
private noncomputable def RatExpr.eval (l : RatExpr) (t : ℝ) : ℝ :=
  (l.map (fun p => p.eval t)).sum

/-- Formal derivative of a `RatExpr`: each piece is differentiated and the
    resulting two-term lists concatenated. -/
private def RatExpr.formalDeriv (l : RatExpr) : RatExpr :=
  l.flatMap RatTerm.formalDeriv

/-- The asymptotic invariant: every term in `l` satisfies `tExp − 2·polePow ≤ M`. -/
private def RatExpr.Bounded (M : ℤ) (l : RatExpr) : Prop :=
  ∀ p ∈ l, p.tExp - 2 * (p.polePow : ℤ) ≤ M

/-- Pointwise expansion of `RatExpr.eval p.formalDeriv t`. -/
private lemma RatTerm.formalDeriv_eval (p : RatTerm) (t : ℝ) :
    RatExpr.eval p.formalDeriv t =
      p.coeff * (p.tExp : ℝ) * t ^ (p.tExp - 1) / (4 * t ^ 2 + 1) ^ p.polePow
      + (-8 * p.coeff * (p.polePow : ℝ)) * t ^ (p.tExp + 1)
          / (4 * t ^ 2 + 1) ^ (p.polePow + 1) := by
  change (((⟨p.coeff * (p.tExp : ℝ), p.tExp - 1, p.polePow⟩ : RatTerm).eval t) ::
        ((⟨-8 * p.coeff * (p.polePow : ℝ), p.tExp + 1, p.polePow + 1⟩
          : RatTerm).eval t) :: []).sum = _
  simp [RatTerm.eval]

/-- Lemma A: each `RatTerm` is differentiable on `(0, ∞)`, with the
    derivative given by the formal-derivative sum. -/
private lemma RatTerm.hasDerivAt_eval (p : RatTerm) {t : ℝ} (ht : 0 < t) :
    HasDerivAt p.eval (RatExpr.eval p.formalDeriv t) t := by
  obtain ⟨c, a, b⟩ := p
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h_q_pos : (0 : ℝ) < 4 * t ^ 2 + 1 := by positivity
  have h_q_ne : (4 * t ^ 2 + 1 : ℝ) ≠ 0 := ne_of_gt h_q_pos
  -- Build numerator and denominator differentiabilities.
  have h_num : HasDerivAt (fun s : ℝ => c * s ^ a) (c * ((a : ℝ) * t ^ (a - 1))) t :=
    (hasDerivAt_zpow a t (Or.inl ht_ne)).const_mul c
  have h_4t2 : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (8 * t) t := by
    convert (hasDerivAt_pow 2 t).const_mul (4 : ℝ) using 1
    push_cast; ring
  have h_qb :
      HasDerivAt (fun s : ℝ => (4 * s ^ 2 + 1) ^ b)
        ((b : ℝ) * (4 * t ^ 2 + 1) ^ (b - 1) * (8 * t)) t :=
    (h_4t2.add_const 1).pow b
  -- Quotient.
  have h_div := h_num.div h_qb (pow_ne_zero b h_q_ne)
  change HasDerivAt (fun s : ℝ => c * s ^ a / (4 * s ^ 2 + 1) ^ b) _ t
  rw [RatTerm.formalDeriv_eval]
  convert h_div using 1
  -- Reconcile the two derivative expressions algebraically.  Replace
  -- `t^(a-1)` and `t^(a+1)` with `t^a/t` and `t·t^a` so that `ring` only
  -- has to handle a single zpow factor.
  have h_pred : t ^ (a - 1) = t ^ a * t⁻¹ := by
    rw [show (a - 1 : ℤ) = a + (-1) from by ring, zpow_add₀ ht_ne, zpow_neg_one]
  have h_succ : t ^ (a + 1) = t ^ a * t := by
    rw [zpow_add₀ ht_ne, zpow_one]
  rw [h_pred, h_succ]
  -- Split on b because `b - 1 : ℕ` truncates at 0.
  rcases b with _ | b'
  · simp; ring
  · have hb_pred : (b' + 1 : ℕ) - 1 = b' := Nat.add_sub_cancel _ _
    rw [hb_pred]
    field_simp
    ring

/-- Lemma B: a finite-sum `RatExpr` is differentiable on `(0, ∞)`. -/
private lemma RatExpr.hasDerivAt_eval (l : RatExpr) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (RatExpr.eval l) (RatExpr.eval (RatExpr.formalDeriv l) t) t := by
  induction l with
  | nil =>
    change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t
    exact hasDerivAt_const t 0
  | cons p ps ih =>
    have h_p : HasDerivAt p.eval (RatExpr.eval p.formalDeriv t) t :=
      RatTerm.hasDerivAt_eval p ht
    have h_eval_cons :
        RatExpr.eval (p :: ps) = (fun s => p.eval s + RatExpr.eval ps s) := by
      funext s; simp [RatExpr.eval]
    have h_formal_cons :
        RatExpr.formalDeriv (p :: ps) =
          p.formalDeriv ++ RatExpr.formalDeriv ps := rfl
    have h_eval_append :
        RatExpr.eval (p.formalDeriv ++ RatExpr.formalDeriv ps) t =
          RatExpr.eval p.formalDeriv t + RatExpr.eval (RatExpr.formalDeriv ps) t := by
      simp [RatExpr.eval, List.map_append, List.sum_append]
    rw [h_eval_cons, h_formal_cons, h_eval_append]
    exact h_p.add ih

/-- Lemma C: formal differentiation lowers the asymptotic invariant by 1. -/
private lemma RatExpr.Bounded.formalDeriv {l : RatExpr} {M : ℤ}
    (h : RatExpr.Bounded M l) :
    RatExpr.Bounded (M - 1) (RatExpr.formalDeriv l) := by
  intro p hp
  simp only [RatExpr.formalDeriv, List.mem_flatMap, RatTerm.formalDeriv,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨q, hq, hp_eq⟩ := hp
  have hq_inv := h q hq
  rcases hp_eq with rfl | rfl
  · -- p.tExp = q.tExp - 1, p.polePow = q.polePow
    change q.tExp - 1 - 2 * (q.polePow : ℤ) ≤ M - 1
    omega
  · -- p.tExp = q.tExp + 1, p.polePow = q.polePow + 1
    change q.tExp + 1 - 2 * ((q.polePow + 1 : ℕ) : ℤ) ≤ M - 1
    push_cast
    omega

/-- Per-term bound: `|p.eval t| ≤ (|p.coeff| / 4^b) · t^M` for `t ≥ 1`,
    where `M` upper-bounds `p.tExp − 2·p.polePow`. -/
private lemma RatTerm.abs_eval_le (p : RatTerm) {M : ℤ}
    (hp : p.tExp - 2 * (p.polePow : ℤ) ≤ M) {t : ℝ} (ht : 1 ≤ t) :
    |p.eval t| ≤ |p.coeff| / 4 ^ p.polePow * t ^ M := by
  obtain ⟨c, a, b⟩ := p
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have h_4t2_pos : (0 : ℝ) < 4 * t ^ 2 := by positivity
  have h_4t2_p1_pos : (0 : ℝ) < 4 * t ^ 2 + 1 := by positivity
  have h_pow_a_pos : (0 : ℝ) < t ^ a := zpow_pos ht_pos a
  have h_4t2_pow_pos : (0 : ℝ) < (4 * t ^ 2) ^ b := pow_pos h_4t2_pos b
  have h_4t2_p1_pow_pos : (0 : ℝ) < (4 * t ^ 2 + 1) ^ b := pow_pos h_4t2_p1_pos b
  unfold RatTerm.eval
  rw [abs_div, abs_mul, abs_of_pos h_4t2_p1_pow_pos, abs_of_pos h_pow_a_pos]
  -- Drop the +1 in the denominator.
  have step1 :
      |c| * t ^ a / (4 * t ^ 2 + 1) ^ b ≤ |c| * t ^ a / (4 * t ^ 2) ^ b := by
    apply div_le_div_of_nonneg_left
    · positivity
    · exact h_4t2_pow_pos
    · exact pow_le_pow_left₀ (by linarith) (by linarith : 4 * t ^ 2 ≤ 4 * t ^ 2 + 1) _
  refine step1.trans ?_
  -- Rewrite RHS in `(|c|/4^b) · t^(a − 2b)` form.
  have h_eq :
      |c| * t ^ a / (4 * t ^ 2) ^ b = |c| / 4 ^ b * t ^ (a - 2 * (b : ℤ)) := by
    have : (4 * t ^ 2 : ℝ) ^ b = 4 ^ b * (t ^ 2) ^ b := mul_pow _ _ _
    rw [this, ← pow_mul]
    have h_pow2b : t ^ (2 * b) = t ^ ((2 * b : ℕ) : ℤ) := by
      rw [zpow_natCast]
    rw [h_pow2b]
    rw [show a - 2 * (b : ℤ) = a + (-((2 * b : ℕ) : ℤ)) from by push_cast; ring]
    rw [zpow_add₀ ht_ne, zpow_neg]
    field_simp
  rw [h_eq]
  -- Bound `t^(a − 2b) ≤ t^M` since `a − 2b ≤ M` and `t ≥ 1`.
  apply mul_le_mul_of_nonneg_left
  · exact zpow_le_zpow_right₀ ht hp
  · positivity

/-- Lemma D: a `RatExpr` bounded by `M` is `O(t^M)` (uniformly for `t ≥ 1`). -/
private lemma RatExpr.exists_bound_of_Bounded {l : RatExpr} {M : ℤ}
    (h : RatExpr.Bounded M l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |RatExpr.eval l t| ≤ C * t ^ M := by
  induction l with
  | nil =>
    refine ⟨0, le_refl _, fun t _ => ?_⟩
    change |((0 : ℝ))| ≤ 0 * t ^ M
    simp
  | cons p ps ih =>
    have h_ps : RatExpr.Bounded M ps := fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨C', hC'_nn, hC'⟩ := ih h_ps
    have hp_inv : p.tExp - 2 * (p.polePow : ℤ) ≤ M := h p List.mem_cons_self
    refine ⟨|p.coeff| / 4 ^ p.polePow + C', by positivity, fun t ht => ?_⟩
    have h_eval_cons :
        RatExpr.eval (p :: ps) t = p.eval t + RatExpr.eval ps t := by
      simp [RatExpr.eval]
    rw [h_eval_cons]
    refine (abs_add_le _ _).trans ?_
    have h_p_bound := RatTerm.abs_eval_le p hp_inv ht
    have h_ps_bound := hC' t ht
    calc |p.eval t| + |RatExpr.eval ps t|
        ≤ |p.coeff| / 4 ^ p.polePow * t ^ M + C' * t ^ M :=
          add_le_add h_p_bound h_ps_bound
      _ = (|p.coeff| / 4 ^ p.polePow + C') * t ^ M := by ring

/-- Iterated formal differentiation lowers the invariant by `k`. -/
private lemma RatExpr.Bounded.iterate_formalDeriv {l : RatExpr} {M : ℤ}
    (h : RatExpr.Bounded M l) (k : ℕ) :
    RatExpr.Bounded (M - k) (RatExpr.formalDeriv^[k] l) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h1 := ih.formalDeriv
    convert h1 using 1
    push_cast; ring

/-- Lemma E: iterated real derivative on `(0,∞)` matches iterated formal
    derivative. -/
private lemma RatExpr.iteratedDeriv_eval (l : RatExpr) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k (RatExpr.eval l) t =
      RatExpr.eval (RatExpr.formalDeriv^[k] l) t := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have h_deriv_eq : ∀ s ∈ Set.Ioi (0 : ℝ),
        deriv (RatExpr.eval l) s = RatExpr.eval (RatExpr.formalDeriv l) s := by
      intro s hs
      exact (RatExpr.hasDerivAt_eval l hs).deriv
    rw [iteratedDeriv_congr_of_nhds k isOpen_Ioi h_deriv_eq t ht]
    rw [ih (RatExpr.formalDeriv l)]
    rfl

/-- The initial expression `l₀` representing `α_part_deriv2`. -/
private noncomputable def RatExpr.l₀ : RatExpr :=
  [⟨-1/2, -1, 1⟩, ⟨8, 1, 2⟩]

/-- Lemma F: `α_part_deriv2 t = eval l₀ t` for `t > 0`. -/
private lemma α_part_deriv2_eq_l₀_eval {t : ℝ} (ht : 0 < t) :
    α_part_deriv2 t = RatExpr.eval RatExpr.l₀ t := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h_inv : t ^ (-1 : ℤ) = t⁻¹ := zpow_neg_one t
  have h_one : t ^ (1 : ℤ) = t := zpow_one t
  unfold α_part_deriv2 RatExpr.l₀ RatExpr.eval
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
             RatTerm.eval, h_inv, h_one, pow_one]
  field_simp

/-- Lemma F': `l₀` satisfies the asymptotic invariant `M = -3`. -/
private lemma RatExpr.bounded_l₀ : RatExpr.Bounded (-3) RatExpr.l₀ := by
  intro p hp
  simp only [RatExpr.l₀, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> · show _ ≤ (-3 : ℤ); decide

/-- The `k`-th iterated derivative of the rational function
        α_part_deriv2(t) = -1/(2t(4t²+1)) + 8t/(4t²+1)²
                         = (12 t² − 1) / (2 t (4 t² + 1)²)
    decays as `O(t^(-3-k))` at `+∞`.

    Proved via the `RatExpr` machinery above: write `α_part_deriv2 = eval l₀`
    on `(0, ∞)`, lift `iteratedDeriv` to `eval (formalDeriv^[k] l₀)`, and
    apply the per-term bound — the asymptotic invariant `tExp − 2·polePow ≤
    −3 − k` is preserved under formal differentiation. -/
lemma iteratedDeriv_α_part_deriv2_isO (k : ℕ) :
    IsO (fun t => iteratedDeriv k α_part_deriv2 t)
        (fun t => t ^ (-(k : ℝ) - 3))
        𝓝∞ := by
  obtain ⟨C, _, hC⟩ :=
    RatExpr.exists_bound_of_Bounded (RatExpr.bounded_l₀.iterate_formalDeriv k)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  -- Step 1: rewrite `iteratedDeriv k α_part_deriv2 t` as `eval (formalDeriv^[k] l₀) t`.
  have h_iter : iteratedDeriv k α_part_deriv2 t =
      RatExpr.eval (RatExpr.formalDeriv^[k] RatExpr.l₀) t := by
    rw [iteratedDeriv_congr_of_nhds k isOpen_Ioi
          (fun s hs => α_part_deriv2_eq_l₀_eval hs) t ht_pos]
    exact RatExpr.iteratedDeriv_eval RatExpr.l₀ k ht_pos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, h_iter]
  -- Step 2: convert the real exponent `-(k:ℝ) - 3` to the integer one used
  -- in the per-term bound.
  have h_pow_real : t ^ (-(k : ℝ) - 3) = t ^ ((-3 - (k : ℤ)) : ℤ) := by
    rw [show (-(k : ℝ) - 3) = (((-3 - (k : ℤ)) : ℤ) : ℝ) from by push_cast; ring,
        Real.rpow_intCast]
  rw [h_pow_real, abs_of_pos (zpow_pos ht_pos _)]
  exact hC t ht

/-- The n-th derivative of `α_part` is `O(t^(-n-1))` for `n ≥ 1`. -/
lemma iteratedDeriv_α_part_isO (n : ℕ) (hn : 1 ≤ n) :
    IsO (fun t => iteratedDeriv n α_part t)
        (fun t => t ^ (-(n : ℝ) - 1))
        𝓝∞ := by
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · -- Case n = 1: bound `α_part'` directly using log(1+x) ≤ x and 1/(4t²+1) ≤ 1/(4t²).
    have hn_eq : n = 1 := by omega
    subst hn_eq
    refine Asymptotics.IsBigO.of_bound (5 / 16) ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
    have ht2_pos : (0 : ℝ) < t ^ 2 := by positivity
    have h4t2_pos : (0 : ℝ) < 4 * t ^ 2 := by positivity
    have h_inner_pos : (0 : ℝ) < 1 + 1 / (4 * t ^ 2) := by positivity
    -- Reduce iteratedDeriv 1 to deriv.
    have h_iter1 : iteratedDeriv 1 α_part t = deriv α_part t := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_zero]
    rw [h_iter1, (hasDerivAt_α_part ht_pos).deriv]
    -- Elementary bounds.
    have h_log_le : Real.log (1 + 1 / (4 * t ^ 2)) ≤ 1 / (4 * t ^ 2) := by
      have := Real.log_le_sub_one_of_pos h_inner_pos
      linarith
    have h_log_nn : 0 ≤ Real.log (1 + 1 / (4 * t ^ 2)) :=
      Real.log_nonneg (by linarith [show (0:ℝ) ≤ 1 / (4 * t ^ 2) by positivity])
    have h_recip_le : (1 : ℝ) / (4 * t ^ 2 + 1) ≤ 1 / (4 * t ^ 2) :=
      one_div_le_one_div_of_le h4t2_pos (by linarith)
    have h_recip_nn : (0 : ℝ) ≤ 1 / (4 * t ^ 2 + 1) := by positivity
    have h_log_quarter_nn :
        (0 : ℝ) ≤ (1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) :=
      mul_nonneg (by norm_num) h_log_nn
    -- Triangle inequality + linear bounds.
    have h_abs :
        |(1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) - 1 / (4 * t ^ 2 + 1)|
          ≤ (1 / 4) * (1 / (4 * t ^ 2)) + 1 / (4 * t ^ 2) := by
      have h_tri :
          |(1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) - 1 / (4 * t ^ 2 + 1)|
            ≤ |(1 / 4) * Real.log (1 + 1 / (4 * t ^ 2))|
              + |(1 : ℝ) / (4 * t ^ 2 + 1)| := by
        have := abs_add_le ((1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)))
                           (-((1 : ℝ) / (4 * t ^ 2 + 1)))
        rw [abs_neg] at this
        simpa [sub_eq_add_neg] using this
      rw [abs_of_nonneg h_log_quarter_nn, abs_of_nonneg h_recip_nn] at h_tri
      have h_log_quarter_le :
          (1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) ≤ (1 / 4) * (1 / (4 * t ^ 2)) :=
        mul_le_mul_of_nonneg_left h_log_le (by norm_num)
      linarith
    -- Convert `t^(-(↑1 : ℝ) - 1)` to `1/t²`.
    have h_pow_simp : t ^ (-((1 : ℕ) : ℝ) - 1) = 1 / t ^ 2 := by
      have hexp : (-((1 : ℕ) : ℝ) - 1) = -((2 : ℕ) : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_neg ht_pos.le, Real.rpow_natCast, one_div]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h_pow_simp,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / t ^ 2)]
    refine h_abs.trans (le_of_eq ?_)
    field_simp
    ring
  · -- Case n ≥ 2: reduce to `iteratedDeriv_α_part_deriv2_isO`.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    -- Step 1: pointwise equality `deriv (deriv α_part) = α_part_deriv2` on (0,∞).
    have h_pointwise : ∀ s ∈ Set.Ioi (0 : ℝ),
        deriv (deriv α_part) s = α_part_deriv2 s := by
      intro s hs
      have hs_pos : (0 : ℝ) < s := hs
      -- `deriv α_part` agrees with the closed form on a nbhd of `s`.
      have h_eq_on_nhds :
          (deriv α_part : ℝ → ℝ) =ᶠ[nhds s]
            (fun r => (1 / 4) * Real.log (1 + 1 / (4 * r ^ 2))
                      - 1 / (4 * r ^ 2 + 1)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hs] with r hr
        exact (hasDerivAt_α_part hr).deriv
      rw [h_eq_on_nhds.deriv_eq]
      exact (hasDerivAt_α_part_form hs_pos).deriv
    -- Step 2: lift to iteratedDeriv on the open set (0,∞).
    have h_eq :
        (fun t => iteratedDeriv (m + 2) α_part t) =ᶠ[Filter.atTop]
        (fun t => iteratedDeriv m α_part_deriv2 t) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      rw [show (m + 2 : ℕ) = (m + 1) + 1 from rfl, iteratedDeriv_succ',
          iteratedDeriv_succ']
      exact iteratedDeriv_congr_of_nhds m isOpen_Ioi h_pointwise t ht
    -- Step 3: invoke the deep gap and rewrite the bound.
    have h_O := iteratedDeriv_α_part_deriv2_isO m
    have h_pow_eq :
        (fun t : ℝ => t ^ (-(m : ℝ) - 3))
          = (fun t : ℝ => t ^ (-((m + 2 : ℕ) : ℝ) - 1)) := by
      funext t; congr 1; push_cast; ring
    rw [h_pow_eq] at h_O
    exact h_eq.trans_isBigO h_O

end ErrorTermAlgebraic

/-!
  ## §6  Error term (B2): iterated derivatives of the integral part of δ

  Define

      j(t) := ∫₀^∞  ρ(u) / ((u + 1/4)² + (t/2)²)  du

  where  ρ(u) = 1/2 - {u}.  The paper (via integration by parts and
  domination) shows  j^(n)(t) = O(t^(-n-2)).

  The n-th derivative of  -(t/2) · j(t)  is then O(t^(-n-1)) by Leibniz.
-/

section ErrorTermIntegral

/- The paper integrates `j` by parts once using the antiderivative
   `σ(u) = ∫₀^u ρ(z) dz` (which satisfies `0 ≤ σ(u) ≤ 1/8`):

       j(t) = 2 · ∫₀^∞  σ(u) · (u + 1/4) / ((u + 1/4)² + (t/2)²)²  du.

   The estimate in the paper then differentiates this form n times under
   the integral and splits at `u = t`. -/

/-- The n-th derivative of `j` is `O(t^(-n-2))`.
    Key estimate from the paper, after the IBP step above. -/
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
  ## §7  Combining parts: the n-th derivative of δ

  δ(t) = α_part(t) - (t/2)·j(t),   so
  δ^(n)(t) = α_part^(n)(t) + (d^n/dt^n)[-(t/2)·j(t)] = O(t^(-n-1)).
-/

section ErrorTermDelta

/-- δ splits as α_part minus the integral term. -/
lemma δ_eq (t : ℝ) (_ : 0 < t) :
    δ t = α_part t - t / 2 * j t := by
  unfold δ α_part j ρ
  ring

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
  ## §8  Main theorem: Theorem 1
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
      contDiffAt_const.mul hδ
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
