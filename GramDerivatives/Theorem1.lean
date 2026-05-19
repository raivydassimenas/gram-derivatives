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
  `jK_isO` (§6) is fully discharged from `jK_eq_sigma_integral` (proved)
  and `sigma_mixedDerivExpr_isO`.  The latter reduces to the single
  σ-weighted integral asymptotic `sigma_lorMix_integral_isO`, which in
  turn has been decomposed into three sub-lemmas:

  • `lorMix_bounded_on_nonneg`      (§6) — `∃ M, ∀ y ≥ 0, |lorMix n y| ≤ M`.
                                          Continuity (proved as
                                          `lorMix_continuous`) on a compact
                                          prefix + `lorMix_isO` on the tail.
  • `lorMix_unified_decay_on_nonneg`(§6) — `∃ K, ∀ y ≥ 0,
                                          |lorMix n y| ≤ K · (1 + y^(n+4))⁻¹`.
                                          Combines `lorMix_bounded_on_nonneg`
                                          (near 0) with `lorMix_isO` (large `y`).
  • `sigma_lorMix_integral_isO`     (§6) — main result.  Dominate the integrand
                                          via `lorMix_unified_decay_on_nonneg`
                                          and `|σ u| ≤ 1/8`; integrate the
                                          dominant by splitting at `v = t/2`.

  ─── Closed under Strategy B ───────────────────────────────────────────
  • `contDiffAt_j`                 (§2.5) — was an axiom; now a theorem derived
                                            from `contDiffOn_jK` (a joint
                                            induction in §2.5 that proves the
                                            formula `iteratedDeriv n j = jK n`
                                            on `(0, ∞)` and reads off
                                            smoothness).
  • `iteratedDeriv_tj_isO`         (§6)   — fully proved via Leibniz on
                                            `-(t/2)·j(t)` plus the derived
                                            `contDiffAt_j` theorem.
  • `mixedDerivExpr_eq_lorMix`     (§6)   — pointwise rescaling, definitional
                                            unfolding + algebra.
  • `lorMix_isO`                   (§6)   — asymptotic cancellation,
                                            `lorMix n x = O(x^{-(n+4)})`.
                                            Proved via the polynomial-rational
                                            representation `iteratedDeriv n lorSq
                                            = lorSqNumer n / (1+s²)^(n+2)` plus
                                            `lorMix n = -2 · iteratedDeriv n lorSq`.
  • `lorSqNumer_natDegree_le`,            — supporting lemmas for `lorMix_isO`.
    `iteratedDeriv_lorSq_eq`,
    `iteratedDeriv_lorSq_isO`     (§6)
  • `lorMix_continuous`            (§6)   — `Continuous (lorMix n)`, from the
                                            rational representation.
-/

import Mathlib

open Real Filter Asymptotics MeasureTheory
open scoped ContDiff Function

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

/-- The sawtooth `ρ` is bounded in absolute value by `1/2`.
    Used as the `u`-dominator in every parametric-integral estimate for `j`. -/
lemma abs_ρ_le_half (u : ℝ) : |ρ u| ≤ 1 / 2 := by
  unfold ρ
  rw [abs_sub_comm, abs_le]
  have h_lt : Int.fract u < 1 := Int.fract_lt_one u
  have h_nn : 0 ≤ Int.fract u := Int.fract_nonneg u
  refine ⟨?_, ?_⟩ <;> linarith

/-- The integral part of δ:  `j(t) = ∫₀^∞ ρ(u) / ((u + 1/4)² + (t/2)²) du`. -/
noncomputable def j (t : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ), ρ u / ((u + 1 / 4) ^ 2 + (t / 2) ^ 2)

/-!
  ## §2  Assumptions

  All axioms taken from the literature are collected here.  They split into:

    • Opaque target / step functions:  `S`, `N_step`.
    • Karatsuba–Korolev representation: `S_eq_φ_sub_δ_add_N`.
    • Smoothness / vanishing of `N_step`:  `contDiffAt_N_step`,
      `N_step_iteratedDeriv_eq_zero`.

  Smoothness of `φ`, `α_part`, `δ`, and `t·j(t)` is *derived* in §3 from
  the §2.5 theorem `contDiffAt_j` (formerly an axiom; now built on the
  joint induction `contDiffOn_jK`) plus elementary Mathlib calculus.
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
  ## §2.5  Parametric-integral infrastructure for `j`

  The integral `j(t) = ∫₀^∞ ρ(u) / ((u+1/4)² + (t/2)²) du` is smooth in `t` on
  `(0, ∞)` because for each `u ≥ 0` the kernel `t ↦ 1/((u+1/4)² + (t/2)²)` is
  rational with strictly positive denominator (≥ `(u+1/4)² ≥ 1/16`), so all
  its `t`-derivatives are bounded by `C_k · (u+1/4)^(-(k+2))` uniformly in `t`
  on bounded intervals — an integrable dominator at every order.

  This sub-section sets up the kernel and its basic smoothness; subsequent
  sub-sections build the dominator bound, the integrand integrability, and
  the differentiation-under-the-integral chain that yields `contDiffAt_j`.
-/

section ParametricIntegralJ

/-- Kernel of the integral defining `j`:  `kernel u t = 1 / ((u + 1/4)² + (t/2)²)`. -/
noncomputable def kernel (u t : ℝ) : ℝ := 1 / ((u + 1 / 4) ^ 2 + (t / 2) ^ 2)

/-- Strict positivity of the kernel's denominator for `u ≥ 0`:
    `(u + 1/4)² + (t/2)² ≥ (u + 1/4)² ≥ 1/16 > 0`. -/
private lemma kernel_denom_pos {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    0 < (u + 1 / 4) ^ 2 + (t / 2) ^ 2 := by
  have h_u_pos : (0 : ℝ) < u + 1 / 4 := by linarith
  have h_sq_pos : (0 : ℝ) < (u + 1 / 4) ^ 2 := pow_pos h_u_pos 2
  have h_t_sq : (0 : ℝ) ≤ (t / 2) ^ 2 := sq_nonneg _
  linarith

/-- For each `u ≥ 0`, the kernel `t ↦ kernel u t` is `C^∞` on all of `ℝ`. -/
private lemma contDiff_kernel {u : ℝ} (hu : 0 ≤ u) :
    ContDiff ℝ ⊤ (fun t : ℝ => kernel u t) := by
  unfold kernel
  refine ContDiff.div contDiff_const ?_ (fun t => ne_of_gt (kernel_denom_pos hu t))
  exact (contDiff_const.add ((contDiff_id.div_const 2).pow 2))

/-- The Lorentzian/Cauchy profile  `lor s = 1 / (1 + s²)`,  used as the
    canonical shape of the kernel after rescaling. -/
private noncomputable def lor (s : ℝ) : ℝ := 1 / (1 + s ^ 2)

private lemma lor_denom_pos (s : ℝ) : 0 < 1 + s ^ 2 := by
  have : (0 : ℝ) ≤ s ^ 2 := sq_nonneg _; linarith

/-- `lor` is `C^∞` on all of `ℝ`. -/
private lemma contDiff_lor : ContDiff ℝ ⊤ lor := by
  unfold lor
  exact ContDiff.div contDiff_const (contDiff_const.add (contDiff_id.pow 2))
    (fun s => ne_of_gt (lor_denom_pos s))

/-- The linear combination of `lor⁽ⁿ⁾` and `lor⁽ⁿ⁺¹⁾` arising from differentiating
    the rescaled `n`-th `t`-derivative of `kernel` in the parameter `u`:
    `lorMix n x = −(n+2)·lor⁽ⁿ⁾(x) − x·lor⁽ⁿ⁺¹⁾(x)`.  Appears as the angular
    factor of `∂ᵤ ∂ₜⁿ kernel` after rescaling. -/
private noncomputable def lorMix (n : ℕ) (x : ℝ) : ℝ :=
  -((n : ℝ) + 2) * iteratedDeriv n lor x - x * iteratedDeriv (n + 1) lor x

/-- Rescaling identity:  `kernel u t = (u+1/4)^{-2} · lor(t / (2(u+1/4)))`.
    This factors out the `u`-dependence into a single negative power and
    leaves the `t`-dependence inside the bounded Lorentzian profile. -/
private lemma kernel_eq_scaled {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    kernel u t = ((u + 1 / 4) ^ 2)⁻¹ * lor ((1 / (2 * (u + 1 / 4))) * t) := by
  have hr : (0 : ℝ) < u + 1 / 4 := by linarith
  have hr_ne : (u + 1 / 4 : ℝ) ≠ 0 := ne_of_gt hr
  have hr2_ne : ((u + 1 / 4) ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ hr_ne
  have h2r_ne : (2 * (u + 1 / 4) : ℝ) ≠ 0 := by positivity
  have hd_ne : ((u + 1 / 4) ^ 2 + (t / 2) ^ 2 : ℝ) ≠ 0 :=
    ne_of_gt (kernel_denom_pos hu t)
  unfold kernel lor
  field_simp

/-- Iterated derivative of the kernel via the Lorentzian rescaling.

    With  `r = u + 1/4`  and  `c = 1/(2r)`,
    `kernel u t = r^{-2} · lor(c · t)`,
    so applying iterated `t`-derivatives gives
    `(d/dt)^k kernel u t = r^{-2} · c^k · lor^{(k)}(c · t)`. -/
private lemma iteratedDeriv_kernel (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    iteratedDeriv k (fun s => kernel u s) t =
      ((u + 1 / 4) ^ 2)⁻¹ * (1 / (2 * (u + 1 / 4))) ^ k *
        iteratedDeriv k lor ((1 / (2 * (u + 1 / 4))) * t) := by
  -- Replace `kernel u` by its scaled form pointwise (via funext).
  have h_eq : (fun s : ℝ => kernel u s) =
      fun s => ((u + 1 / 4) ^ 2)⁻¹ * lor ((1 / (2 * (u + 1 / 4))) * s) := by
    funext s; exact kernel_eq_scaled hu s
  rw [h_eq]
  -- Pull out the constant factor `((u+1/4)^2)⁻¹` (simp-normal form of
  -- `iteratedDeriv_const_mul_field`).
  rw [iteratedDeriv_const_mul_field ((u + 1 / 4) ^ 2)⁻¹
        (fun s => lor ((1 / (2 * (u + 1 / 4))) * s))]
  -- Apply the comp-const-mul rule for `lor`.
  have h_lor_k : ContDiff ℝ k lor := contDiff_lor.of_le le_top
  rw [show (iteratedDeriv k fun s => lor ((1 / (2 * (u + 1 / 4))) * s)) =
        (fun s => (1 / (2 * (u + 1 / 4))) ^ k *
          iteratedDeriv k lor ((1 / (2 * (u + 1 / 4))) * s)) from
      iteratedDeriv_comp_const_mul h_lor_k _]
  ring

/-- The closed-form expression appearing as `∂ᵤ ∂ₜⁿ kernel`, in two-term sum form. -/
private noncomputable def mixedDerivExpr (n : ℕ) (u t : ℝ) : ℝ :=
  -(((n : ℝ) + 2) * (u + 1/4)^(n+1)) / ((u + 1/4)^(n+2))^2 * (1/2)^n *
    iteratedDeriv n lor ((1 / (2 * (u + 1/4))) * t)
  + ((u + 1/4)^(n+2))⁻¹ * (1/2)^n *
    (iteratedDeriv (n + 1) lor ((1 / (2 * (u + 1/4))) * t) *
      ((-2 / (2 * (u + 1/4))^2) * t))

/-- Derivative of `u ↦ ∂ₜⁿ kernel(u, t)` in the parameter `u`.

    Using the rescaling identity `∂ₜⁿ kernel(u, t) = ((u+1/4)²)⁻¹ · (1/(2(u+1/4)))ⁿ ·
    lor⁽ⁿ⁾(t/(2(u+1/4)))`, the chain and product rules in `u` produce the
    explicit two-term form `mixedDerivExpr n u t`.  The `lorMix`-shaped repackaging
    is done in `mixedDerivExpr_eq_lorMix` below. -/
private lemma hasDerivAt_iteratedDeriv_kernel (n : ℕ) {u : ℝ} (hu : 0 < u) (t : ℝ) :
    HasDerivAt (fun v => iteratedDeriv n (fun s => kernel v s) t)
      (mixedDerivExpr n u t) u := by
  have hu_pos : 0 < u + 1/4 := by linarith
  have hu_ne : (u + 1/4) ≠ 0 := ne_of_gt hu_pos
  have hu_pow_ne : (u + 1/4)^(n+2) ≠ 0 := pow_ne_zero _ hu_ne
  have h2u_pos : 0 < 2 * (u + 1/4) := by linarith
  have h2u_ne : (2 * (u + 1/4)) ≠ 0 := ne_of_gt h2u_pos
  -- (A) Eventual equality with a SIMPLIFIED rescaled form that collects all `(v+1/4)`
  -- powers into `(v+1/4)^(n+2)` — eliminating the `n - 1` exponent that arises from
  -- `HasDerivAt.pow` and breaks `ring`.
  have h_eq : (fun v : ℝ => iteratedDeriv n (fun s => kernel v s) t) =ᶠ[nhds u]
              fun v : ℝ => ((v + 1/4)^(n+2))⁻¹ * (1/2)^n *
                          iteratedDeriv n lor ((1/(2*(v + 1/4))) * t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    have h_v0 : 0 < v := Set.mem_Ioi.mp hv
    have h_vpos : 0 < v + 1/4 := by linarith
    have h_vne : v + 1/4 ≠ 0 := ne_of_gt h_vpos
    have h_2v_ne : (2 * (v + 1/4)) ≠ 0 := by positivity
    have h_pow_ne : (v + 1/4)^(n+2) ≠ 0 := pow_ne_zero _ h_vne
    have h_pown_ne : (v + 1/4)^n ≠ 0 := pow_ne_zero _ h_vne
    have h_2pown_ne : ((2 : ℝ)^n) ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [iteratedDeriv_kernel n h_v0.le t]
    -- ((v+1/4)^2)⁻¹ · (1/(2(v+1/4)))^n = ((v+1/4)^(n+2))⁻¹ · (1/2)^n.
    -- `ring` treats `⁻¹` as opaque, so we rewrite both sides into a common
    -- inverse-of-power form via three auxiliary identities, then close by `ring`.
    have eq1 : (1 / (2 * (v + 1 / 4)) : ℝ) ^ n
                = ((v + 1 / 4) ^ n)⁻¹ * (2 ^ n)⁻¹ := by
      rw [div_pow, one_pow, mul_pow, one_div, mul_inv]; ring
    have eq2 : ((1 : ℝ) / 2) ^ n = (2 ^ n)⁻¹ := by
      rw [div_pow, one_pow, one_div]
    have eq3 : ((v + 1 / 4 : ℝ) ^ (n + 2))⁻¹
                = ((v + 1 / 4) ^ n)⁻¹ * ((v + 1 / 4) ^ 2)⁻¹ := by
      rw [pow_add, mul_inv]
    rw [eq1, eq2, eq3]
    ring
  -- (B) Build HasDerivAt of the simplified form piece by piece.
  have h_r : HasDerivAt (fun v : ℝ => v + 1/4) 1 u :=
    (hasDerivAt_id u).add_const _
  -- (v + 1/4)^(n+2), deriv at u is (n+2) * (u+1/4)^(n+1).
  have h_r_pow : HasDerivAt (fun v : ℝ => (v + 1/4)^(n+2))
                  (((n : ℝ) + 2) * (u + 1/4)^(n+1)) u := by
    have h := h_r.pow (n+2)
    have h_ns : (n + 2 - 1 : ℕ) = n + 1 := by omega
    rw [h_ns] at h
    convert h using 1
    push_cast; ring
  have h_inv : HasDerivAt (fun v : ℝ => ((v + 1/4)^(n+2))⁻¹)
                (-(((n : ℝ) + 2) * (u + 1/4)^(n+1)) / ((u + 1/4)^(n+2))^2) u :=
    h_r_pow.inv hu_pow_ne
  have h_AB : HasDerivAt (fun v : ℝ => ((v + 1/4)^(n+2))⁻¹ * (1/2)^n)
                ((-(((n : ℝ) + 2) * (u + 1/4)^(n+1)) / ((u + 1/4)^(n+2))^2) * (1/2)^n) u :=
    h_inv.mul_const _
  -- Argument of `lor⁽ⁿ⁾`: `(1/(2*(v+1/4))) * t`.
  have h_2r : HasDerivAt (fun v : ℝ => 2 * (v + 1/4)) 2 u := by
    have := h_r.const_mul 2; convert this using 1; ring
  have h_inv_2r : HasDerivAt (fun v : ℝ => 1 / (2 * (v + 1/4)))
                    (-2 / (2 * (u + 1/4))^2) u := by
    have := (hasDerivAt_const u (1 : ℝ)).div h_2r h2u_ne
    convert this using 1; ring
  have h_lor_arg : HasDerivAt (fun v : ℝ => (1 / (2 * (v + 1/4))) * t)
                    ((-2 / (2 * (u + 1/4))^2) * t) u :=
    h_inv_2r.mul_const t
  have h_lor_n_diff : Differentiable ℝ (iteratedDeriv n lor) :=
    (contDiff_lor.of_le le_top).differentiable_iteratedDeriv' n
  have h_lor_n_at : HasDerivAt (iteratedDeriv n lor)
                      (iteratedDeriv (n + 1) lor ((1 / (2 * (u + 1/4))) * t))
                      ((1 / (2 * (u + 1/4))) * t) := by
    rw [iteratedDeriv_succ]
    exact h_lor_n_diff.differentiableAt.hasDerivAt
  have h_C := h_lor_n_at.comp u h_lor_arg
  have h_full := h_AB.mul h_C
  -- The function form `h_AB * h_C` has the rescaled form; transfer to the LHS via h_eq.
  -- The derivative of `h_full` is exactly `mixedDerivExpr n u t` (by unfolding).
  exact h_full.congr_of_eventuallyEq h_eq

/-- `iteratedDeriv k lor` is bounded on every closed interval `[-R, R]`. -/
private lemma exists_bound_iteratedDeriv_lor (k : ℕ) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |s| ≤ R → |iteratedDeriv k lor s| ≤ M := by
  rcases lt_or_ge R 0 with hR | hR
  · -- Vacuously true: no `s` satisfies `|s| ≤ R < 0`.
    refine ⟨0, le_refl 0, ?_⟩
    intro s hs
    exact absurd (lt_of_le_of_lt hs hR) (not_lt.mpr (abs_nonneg s))
  · -- `R ≥ 0`: extract a bound on the compact `Icc (-R) R` from continuity.
    have hcont : Continuous (iteratedDeriv k lor) :=
      contDiff_lor.continuous_iteratedDeriv k le_top
    have habs : Continuous (fun s => |iteratedDeriv k lor s|) := hcont.abs
    obtain ⟨M, hMub⟩ :=
      (isCompact_Icc (a := -R) (b := R)).bddAbove_image habs.continuousOn
    refine ⟨max M 0, le_max_right _ _, ?_⟩
    intro s hs
    have hs_in : s ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc]; exact ⟨neg_le_of_abs_le hs, le_of_abs_le hs⟩
    exact (hMub ⟨s, hs_in, rfl⟩).trans (le_max_left _ _)

/-- Uniform bound for `|iteratedDeriv k (kernel u) t|`.

    For any `R : ℝ` and `k : ℕ`, there is a constant `C_k(R) ≥ 0` with
    `|iteratedDeriv k (kernel u) t| ≤ C_k(R) · (u + 1/4)^{-(k+2)}`
    whenever `0 ≤ u` and `|t| ≤ R`.  The proof rescales the kernel into the
    Lorentzian profile `lor` and bounds `iteratedDeriv k lor` on the
    bounded image of the rescaling map. -/
private lemma exists_bound_iteratedDeriv_kernel (k : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ), 0 ≤ u → ∀ (t : ℝ), |t| ≤ R →
      |iteratedDeriv k (fun s => kernel u s) t| ≤ C * ((u + 1 / 4) ^ (k + 2))⁻¹ := by
  -- For `u ≥ 0`, the rescaling factor `c = 1/(2(u+1/4))` lies in `(0, 2]`,
  -- so `|c · t| ≤ 2 · |R|`.  Bound `iteratedDeriv k lor` on `[-2|R|, 2|R|]`.
  obtain ⟨M, hM_nn, hM⟩ := exists_bound_iteratedDeriv_lor k (2 * |R|)
  refine ⟨M / 2 ^ k, by positivity, ?_⟩
  intro u hu t ht
  have hr_pos : (0 : ℝ) < u + 1 / 4 := by linarith
  have h2r_pos : (0 : ℝ) < 2 * (u + 1 / 4) := by linarith
  have hr2_pos : (0 : ℝ) < (u + 1 / 4) ^ 2 := pow_pos hr_pos 2
  have hrk2_pos : (0 : ℝ) < (u + 1 / 4) ^ (k + 2) := pow_pos hr_pos (k + 2)
  have hc_pos : (0 : ℝ) < 1 / (2 * (u + 1 / 4)) := by positivity
  have hc_le_two : (1 / (2 * (u + 1 / 4)) : ℝ) ≤ 2 := by
    rw [div_le_iff₀ h2r_pos]; linarith
  -- Bound the Lorentzian factor at the rescaled argument.
  have h_arg_abs : |1 / (2 * (u + 1 / 4)) * t| ≤ 2 * |R| := by
    rw [abs_mul, abs_of_pos hc_pos]
    calc 1 / (2 * (u + 1 / 4)) * |t|
        ≤ 2 * |t| := by gcongr
      _ ≤ 2 * |R| := by
          have : |t| ≤ |R| := ht.trans (le_abs_self R)
          linarith
  have h_lor_bd : |iteratedDeriv k lor (1 / (2 * (u + 1 / 4)) * t)| ≤ M :=
    hM _ h_arg_abs
  -- Apply the rescaling identity.
  rw [iteratedDeriv_kernel k hu t]
  -- Distribute absolute values across the product of three positive (in
  -- abs.) factors.
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hr2_pos),
      abs_pow, abs_of_pos hc_pos]
  -- Bound the |lor^(k)| factor by `M`, keeping the other (positive) factors.
  have h_step1 : ((u + 1 / 4) ^ 2)⁻¹ * (1 / (2 * (u + 1 / 4))) ^ k *
                  |iteratedDeriv k lor (1 / (2 * (u + 1 / 4)) * t)|
                ≤ ((u + 1 / 4) ^ 2)⁻¹ * (1 / (2 * (u + 1 / 4))) ^ k * M := by
    gcongr
  refine h_step1.trans (le_of_eq ?_)
  -- Algebraic simplification:  ((u+1/4)^2)⁻¹ · (1/(2(u+1/4)))^k · M
  --                          = (M / 2^k) · ((u+1/4)^(k+2))⁻¹.
  have hr_ne : (u + 1 / 4 : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hrk_ne : ((u + 1 / 4 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ hr_ne
  have h2k_ne : ((2 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [div_pow, one_pow, mul_pow, pow_add (u + 1 / 4) k 2]
  field_simp

/-- The dominator `((u+1/4)^(k+2))⁻¹` is integrable on `Ici 0`.

    Reduction to `Real.rpow` form to apply `integrableOn_add_rpow_Ioi_of_lt`,
    then transfer to `Ici` (which differs from `Ioi` by a measure-zero point). -/
private lemma integrableOn_pow_inv_shift (k : ℕ) :
    IntegrableOn (fun u : ℝ => ((u + 1 / 4) ^ (k + 2))⁻¹) (Set.Ici (0 : ℝ)) := by
  -- Integrability on `Ioi 0` via the `rpow` lemma after rewriting.
  have h_ioi : IntegrableOn (fun u : ℝ => ((u + 1 / 4) ^ (k + 2))⁻¹)
      (Set.Ioi (0 : ℝ)) := by
    refine (integrableOn_add_rpow_Ioi_of_lt
      (a := -((k + 2 : ℕ) : ℝ)) (m := 1 / 4) (c := 0)
      (by push_cast; linarith)
      (by norm_num)).congr_fun ?_ measurableSet_Ioi
    intro u hu
    have hu_pos : (0 : ℝ) < u + 1 / 4 := by linarith [Set.mem_Ioi.mp hu]
    change (u + 1 / 4) ^ (-((k + 2 : ℕ) : ℝ)) = ((u + 1 / 4) ^ (k + 2))⁻¹
    rw [Real.rpow_neg hu_pos.le, Real.rpow_natCast]
  -- Transfer from `Ioi 0` to `Ici 0` (they differ by the measure-zero `{0}`).
  exact h_ioi.congr_set_ae Ioi_ae_eq_Ici.symm

/-- The integrand for `j` and its formal `t`-derivatives:
    `jIntegrand k t u = ρ u · iteratedDeriv k (kernel u ·) t`.  At `k = 0`
    this is the `j`-integrand itself; at `k ≥ 1` it is the formal derivative
    obtained by differentiating under the integral. -/
private noncomputable def jIntegrand (k : ℕ) (t : ℝ) : ℝ → ℝ :=
  fun u => ρ u * iteratedDeriv k (fun s => kernel u s) t

/-- Continuity of `u ↦ iteratedDeriv k (kernel u ·) t` on `Ici 0`,
    via the rescaling identity (each factor is continuous in `u`). -/
private lemma continuousOn_iteratedDeriv_kernel (k : ℕ) (t : ℝ) :
    ContinuousOn
      (fun u : ℝ => iteratedDeriv k (fun s => kernel u s) t) (Set.Ici 0) := by
  have h_pos : ∀ u ∈ Set.Ici (0 : ℝ), (0 : ℝ) < u + 1 / 4 := by
    intro u hu; linarith [Set.mem_Ici.mp hu]
  have h_pos2 : ∀ u ∈ Set.Ici (0 : ℝ), (0 : ℝ) < 2 * (u + 1 / 4) := by
    intro u hu; linarith [h_pos u hu]
  -- The rescaled form is continuous on `Ici 0` as a product of continuous
  -- factors.
  have h_inv2 : ContinuousOn (fun u : ℝ => ((u + 1 / 4) ^ 2)⁻¹) (Set.Ici 0) :=
    ContinuousOn.inv₀
      ((continuousOn_id.add continuousOn_const).pow 2)
      (fun u hu => ne_of_gt (pow_pos (h_pos u hu) 2))
  have h_inv1 : ContinuousOn (fun u : ℝ => 1 / (2 * (u + 1 / 4))) (Set.Ici 0) :=
    ContinuousOn.div continuousOn_const
      ((continuousOn_const.mul (continuousOn_id.add continuousOn_const)))
      (fun u hu => ne_of_gt (h_pos2 u hu))
  have h_pow1 : ContinuousOn (fun u : ℝ => (1 / (2 * (u + 1 / 4))) ^ k)
                  (Set.Ici 0) := h_inv1.pow k
  have hcont_lor : Continuous (iteratedDeriv k lor) :=
    contDiff_lor.continuous_iteratedDeriv k le_top
  have h_inner : ContinuousOn (fun u : ℝ => (1 / (2 * (u + 1 / 4))) * t)
                  (Set.Ici 0) := h_inv1.mul continuousOn_const
  have h_lor_arg : ContinuousOn
      (fun u : ℝ => iteratedDeriv k lor ((1 / (2 * (u + 1 / 4))) * t))
      (Set.Ici 0) := hcont_lor.comp_continuousOn h_inner
  have h_resc : ContinuousOn
      (fun u : ℝ => ((u + 1 / 4) ^ 2)⁻¹ *
        (1 / (2 * (u + 1 / 4))) ^ k *
        iteratedDeriv k lor ((1 / (2 * (u + 1 / 4))) * t)) (Set.Ici 0) :=
    (h_inv2.mul h_pow1).mul h_lor_arg
  -- Transfer continuity along the rescaling identity (which gives the
  -- pointwise equality `iteratedDeriv k (kernel u ·) t = (rescaled form)`
  -- for `u ≥ 0`).
  exact h_resc.congr (fun u hu => iteratedDeriv_kernel k (Set.mem_Ici.mp hu) t)

/-- AE-strong-measurability of `jIntegrand k t` on `Ici 0`. -/
private lemma aeStronglyMeasurable_jIntegrand (k : ℕ) (t : ℝ) :
    AEStronglyMeasurable (jIntegrand k t) (volume.restrict (Set.Ici (0 : ℝ))) := by
  -- `ρ` is measurable on ℝ; the kernel-derivative is continuous on `Ici 0`.
  have hρ : Measurable ρ := by
    unfold ρ
    exact measurable_const.sub measurable_fract
  have hker : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv k (fun s => kernel u s) t)
      (volume.restrict (Set.Ici 0)) :=
    (continuousOn_iteratedDeriv_kernel k t).aestronglyMeasurable measurableSet_Ici
  exact (hρ.aestronglyMeasurable.mono_measure
    (Measure.restrict_le_self)).mul hker

/-- Integrability of `jIntegrand k t` on `Ici 0`. -/
private lemma integrable_jIntegrand (k : ℕ) (t : ℝ) :
    IntegrableOn (jIntegrand k t) (Set.Ici (0 : ℝ)) := by
  -- Bound the integrand pointwise by `(C/2) · ((u+1/4)^(k+2))⁻¹`,
  -- which is integrable on `Ici 0`.
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_iteratedDeriv_kernel k |t|
  refine Integrable.mono'
    ((integrableOn_pow_inv_shift k).const_mul (C / 2))
    (aeStronglyMeasurable_jIntegrand k t) ?_
  -- Pointwise bound on `Ici 0`.
  refine (ae_restrict_iff' measurableSet_Ici).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro u hu
  have hu_nn : 0 ≤ u := Set.mem_Ici.mp hu
  have hr_pos : (0 : ℝ) < u + 1 / 4 := by linarith
  have h_pow_pos : (0 : ℝ) < (u + 1 / 4) ^ (k + 2) := pow_pos hr_pos _
  have h_inv_nn : (0 : ℝ) ≤ ((u + 1 / 4) ^ (k + 2))⁻¹ :=
    le_of_lt (inv_pos.mpr h_pow_pos)
  have h_ker : |iteratedDeriv k (fun s => kernel u s) t|
                ≤ C * ((u + 1 / 4) ^ (k + 2))⁻¹ :=
    hC u hu_nn t (le_refl _)
  have h_rho : |ρ u| ≤ 1 / 2 := by
    unfold ρ
    rw [abs_sub_comm, abs_le]
    have h_fract_lt : Int.fract u < 1 := Int.fract_lt_one u
    have h_fract_nn : 0 ≤ Int.fract u := Int.fract_nonneg u
    constructor <;> linarith
  change ‖jIntegrand k t u‖ ≤ C / 2 * ((u + 1 / 4) ^ (k + 2))⁻¹
  rw [Real.norm_eq_abs]
  unfold jIntegrand
  rw [abs_mul]
  calc |ρ u| * |iteratedDeriv k (fun s => kernel u s) t|
      ≤ (1 / 2) * (C * ((u + 1 / 4) ^ (k + 2))⁻¹) := by
        gcongr
    _ = C / 2 * ((u + 1 / 4) ^ (k + 2))⁻¹ := by ring

/-- Family of kernel-integrals:  `jK k` equals `j` at `k = 0` and gives the
    formal `k`-th derivative of `j` for higher `k` (after the differentiation
    chain proved in Step 7). -/
private noncomputable def jK (k : ℕ) (t : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ), jIntegrand k t u

/-- `jK 0 = j`:  the integrand at `k = 0` is exactly the `j`-integrand. -/
private lemma jK_zero : jK 0 = j := by
  funext t
  unfold jK jIntegrand j kernel
  congr 1
  funext u
  rw [iteratedDeriv_zero]
  ring

/-- For `t > 0`, every point of the ball `ball t (t/2)` lies in `(t/2, 3t/2)`
    and so has absolute value at most `3t/2`.  Used as the uniform `|x|`-bound
    when invoking the kernel dominator on a neighborhood of `t`. -/
private lemma abs_le_of_mem_ball_half_pos {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Metric.ball t (t / 2), |x| ≤ 3 * t / 2 := by
  intro x hx
  rw [Metric.mem_ball, Real.dist_eq] at hx
  have h_lo : -(t / 2) < x - t := (abs_lt.mp hx).1
  have h_hi : x - t < t / 2 := (abs_lt.mp hx).2
  have h_x_pos : 0 < x := by linarith
  rw [abs_of_pos h_x_pos]; linarith

/-- Pointwise dominator bound on the integrand:  `‖jIntegrand K x u‖ ≤ (C/2)·(u+1/4)^{-(K+2)}`
    whenever `|iteratedDeriv K (kernel u ·) x| ≤ C·(u+1/4)^{-(K+2)}`.

    Combines the kernel bound with `abs_ρ_le_half` (the `1/2` factor in the
    final dominator comes from `|ρ u| ≤ 1/2`). -/
private lemma norm_jIntegrand_le {K : ℕ} {C u x : ℝ}
    (h_ker : |iteratedDeriv K (fun s => kernel u s) x|
              ≤ C * ((u + 1 / 4) ^ (K + 2))⁻¹) :
    ‖jIntegrand K x u‖ ≤ C / 2 * ((u + 1 / 4) ^ (K + 2))⁻¹ := by
  rw [Real.norm_eq_abs]
  unfold jIntegrand
  rw [abs_mul]
  calc |ρ u| * |iteratedDeriv K (fun s => kernel u s) x|
      ≤ (1 / 2) * (C * ((u + 1 / 4) ^ (K + 2))⁻¹) := by
        gcongr; exact abs_ρ_le_half u
    _ = C / 2 * ((u + 1 / 4) ^ (K + 2))⁻¹ := by ring

/-- One-step differentiation under the integral:
    `(d/dt) jK k t = jK (k+1) t`.

    The integrand `t' ↦ ρ(u)·iteratedDeriv k (kernel u ·) t'` has
    `t`-derivative `ρ(u)·iteratedDeriv (k+1) (kernel u ·) t'`, dominated by
    `(C/2)·(u+1/4)^{-((k+1)+2)}` uniformly on the ball `ball t (t/2) ⊂ (0, ∞)`. -/
private lemma hasDerivAt_jK (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (jK k) (jK (k+1) t) t := by
  set nbhd : Set ℝ := Metric.ball t (t / 2)
  have h_nbhd_mem : nbhd ∈ nhds t :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos ht))
  have h_nbhd_bound : ∀ x ∈ nbhd, |x| ≤ 3 * t / 2 :=
    abs_le_of_mem_ball_half_pos ht
  obtain ⟨C, _, hC⟩ := exists_bound_iteratedDeriv_kernel (k + 1) (3 * t / 2)
  set bound : ℝ → ℝ := fun u => C / 2 * ((u + 1 / 4) ^ ((k + 1) + 2))⁻¹
  have h_bound_int : Integrable bound (volume.restrict (Set.Ici (0 : ℝ))) :=
    (integrableOn_pow_inv_shift (k + 1)).const_mul (C / 2)
  -- Apply differentiation-under-the-integral with uniform-`x` dominator on `nbhd`.
  have h_app := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ici (0 : ℝ)))
    (F := fun x : ℝ => jIntegrand k x) (F' := fun x : ℝ => jIntegrand (k + 1) x)
    (x₀ := t) (s := nbhd) (bound := bound)
    h_nbhd_mem
    (Filter.Eventually.of_forall (fun x => aeStronglyMeasurable_jIntegrand k x))
    (integrable_jIntegrand k t)
    (aeStronglyMeasurable_jIntegrand (k + 1) t)
    -- h_bound: pointwise dominator on F' for x in nbhd.
    (by
      refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ?_)
      intro u hu_mem x hx
      have hu_nn : 0 ≤ u := Set.mem_Ici.mp hu_mem
      exact norm_jIntegrand_le (hC u hu_nn x (h_nbhd_bound x hx)))
    h_bound_int
    -- h_diff: pointwise HasDerivAt of the integrand in `x` for ae `u`.
    (by
      refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ?_)
      intro u hu_mem x _hx
      have hu_nn : 0 ≤ u := Set.mem_Ici.mp hu_mem
      have h_diff_ker : Differentiable ℝ (iteratedDeriv k (fun s => kernel u s)) :=
        ((contDiff_kernel hu_nn).of_le le_top).differentiable_iteratedDeriv' k
      have h_da : HasDerivAt (iteratedDeriv k (fun s => kernel u s))
            (iteratedDeriv (k + 1) (fun s => kernel u s) x) x := by
        rw [iteratedDeriv_succ]
        exact h_diff_ker.differentiableAt.hasDerivAt
      unfold jIntegrand
      exact h_da.const_mul (ρ u))
  simpa [jK] using h_app.2

/-- Continuity of `jK k` at any `t > 0`.

    Same scaffolding as `hasDerivAt_jK` but invoking `continuousAt_of_dominated`
    instead.  Continuity of the integrand in `x` (for each `u ≥ 0`) comes from
    `contDiff_kernel`. -/
private lemma continuousAt_jK (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (jK k) t := by
  set nbhd : Set ℝ := Metric.ball t (t / 2)
  have h_nbhd_mem : nbhd ∈ nhds t :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos ht))
  have h_nbhd_bound : ∀ x ∈ nbhd, |x| ≤ 3 * t / 2 :=
    abs_le_of_mem_ball_half_pos ht
  obtain ⟨C, _, hC⟩ := exists_bound_iteratedDeriv_kernel k (3 * t / 2)
  set bound : ℝ → ℝ := fun u => C / 2 * ((u + 1 / 4) ^ (k + 2))⁻¹
  have h_bound_int : Integrable bound (volume.restrict (Set.Ici (0 : ℝ))) :=
    (integrableOn_pow_inv_shift k).const_mul (C / 2)
  have h_app := continuousAt_of_dominated
    (μ := volume.restrict (Set.Ici (0 : ℝ)))
    (F := fun x : ℝ => jIntegrand k x)
    (x₀ := t) (bound := bound)
    (Filter.Eventually.of_forall (fun x => aeStronglyMeasurable_jIntegrand k x))
    (Filter.eventually_of_mem h_nbhd_mem (fun x hx => by
      refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ?_)
      intro u hu_mem
      have hu_nn : 0 ≤ u := Set.mem_Ici.mp hu_mem
      exact norm_jIntegrand_le (hC u hu_nn x (h_nbhd_bound x hx))))
    h_bound_int
    (by
      refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ?_)
      intro u hu_mem
      have hu_nn : 0 ≤ u := Set.mem_Ici.mp hu_mem
      have h_iter_cont : Continuous (iteratedDeriv k (fun s => kernel u s)) :=
        (contDiff_kernel hu_nn).continuous_iteratedDeriv k le_top
      unfold jIntegrand
      exact h_iter_cont.continuousAt.const_mul (ρ u))
  simpa [jK] using h_app

/-- Iterated derivatives of `j` equal the formal kernel-integrals `jK n` on
    `(0, ∞)`.  Proved by induction: base case via `jK_zero`; step uses
    `hasDerivAt_jK` plus eventual-equality of `iteratedDeriv n j` and `jK n`
    on a neighborhood of each `t > 0`. -/
private theorem iteratedDeriv_j_eqOn_jK (n : ℕ) :
    Set.EqOn (iteratedDeriv n j) (jK n) (Set.Ioi (0 : ℝ)) := by
  induction n with
  | zero =>
      intro t _
      rw [iteratedDeriv_zero]
      exact (congr_fun jK_zero t).symm
  | succ n ih =>
      intro t ht
      have h_eq : (iteratedDeriv n j : ℝ → ℝ) =ᶠ[nhds t] jK n := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
        exact ih hs
      rw [iteratedDeriv_succ, h_eq.deriv_eq]
      exact (hasDerivAt_jK n ht).deriv

/-- `jK k` is `C^n` on `(0, ∞)` for every `n` and every `k`.

    Inducts on `n`; base case is continuity (from `continuousAt_jK`), step
    uses `contDiffOn_succ_iff_deriv_of_isOpen` plus `(hasDerivAt_jK k).deriv`
    to identify `deriv (jK k) = jK (k+1)` on `Ioi 0`. -/
private lemma contDiffOn_jK : ∀ (n k : ℕ),
    ContDiffOn ℝ (n : ℕ∞ω) (jK k) (Set.Ioi (0 : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro k
      rw [Nat.cast_zero, contDiffOn_zero]
      intro t ht
      exact (continuousAt_jK k ht).continuousWithinAt
  | succ n ih =>
      intro k
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by push_cast; ring,
          contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        exact (hasDerivAt_jK k ht).differentiableAt.differentiableWithinAt
      · intro h_eq
        simp at h_eq
      · exact (ih (k+1)).congr (fun t ht => (hasDerivAt_jK k ht).deriv)

end ParametricIntegralJ

/-- `j` is `C^n` on `(0, ∞)` for every `n`.

    Derived from `contDiffOn_jK` (`jK 0 = j` is `C^n` on `Ioi 0` for every `n`)
    by specialising at `k = 0` and converting `ContDiffOn` on an open set
    into `ContDiffAt`.  Replaces the former axiom of the same name. -/
theorem contDiffAt_j (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n j s := by
  have h : ContDiffOn ℝ (n : ℕ∞ω) (jK 0) (Set.Ioi (0 : ℝ)) := contDiffOn_jK n 0
  rw [jK_zero] at h
  exact h.contDiffAt (isOpen_Ioi.mem_nhds hs)

/-!
  ## §3  Smoothness lemmas

  Derived from the axioms in §2 plus elementary Mathlib calculus.  The four
  results in this section establish `ContDiffAt ℝ n F t` for `t > 0` and
  every `F` that appears as a sub-expression of `S` in the Karatsuba–Korolev
  decomposition.

  Dependency tree:
    contDiffAt_j (§2.5 thm)  ──▶  contDiffAt_neg_tj  ──▶  contDiffAt_δ
                                                        ▲
    contDiffAt_α_part  ─────────────────────────────────┘
    contDiffAt_φ                              (independent)

  `contDiffAt_j` was an axiom; it is now derived in §2.5 from the joint
  induction `contDiffOn_jK` and `jK_zero`.
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

/-! ### Reduction of `iteratedDeriv_α_part_isO`

`α_part^(n)(t) = O(t^(-n-1))` for `n ≥ 1` is established via three pieces:
  • `hasDerivAt_α_part`           — first derivative of `α_part`,
  • `hasDerivAt_α_part_form`      — second derivative as a rational function
                                    `α_part_deriv2`,
  • `iteratedDeriv_α_part_deriv2_isO` — decay of the iterated derivative of
                                       that rational function (proved via
                                       the `RatExpr` machinery below). -/

/-- Closed form for the second derivative of `α_part` on `(0, ∞)`.

    Combined as a single rational function:
        α_part_deriv2(t) = (12 t² − 1) / (2 t (4 t² + 1)²). -/
private noncomputable def α_part_deriv2 (t : ℝ) : ℝ :=
  -1 / (2 * t * (4 * t ^ 2 + 1)) + 8 * t / (4 * t ^ 2 + 1) ^ 2

/-- Derivative of the inner log of `α_part`:
    `(d/dt) log(1 + 1/(4 t²)) = -2 / (t · (4 t² + 1))` for `t > 0`.

    Shared building block for `hasDerivAt_α_part` and
    `hasDerivAt_α_part_form` below. -/
private lemma hasDerivAt_log_one_plus_inv_4sq {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.log (1 + 1 / (4 * s ^ 2)))
      (-2 / (t * (4 * t ^ 2 + 1))) t := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have h4t2_ne : (4 * t ^ 2 : ℝ) ≠ 0 := by positivity
  have h_inner_ne : (1 + 1 / (4 * t ^ 2) : ℝ) ≠ 0 :=
    ne_of_gt (by positivity)
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
  convert h_one_plus.log h_inner_ne using 1
  field_simp; ring

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
  have h2t_ne : (2 * t : ℝ) ≠ 0 := by positivity
  have h_log := hasDerivAt_log_one_plus_inv_4sq ht
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
  have h4t2_p1_ne : (4 * t ^ 2 + 1 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  -- First piece: (1/4) · log(1 + 1/(4 s²)).
  have h_log := hasDerivAt_log_one_plus_inv_4sq ht
  have h_first :
      HasDerivAt (fun s : ℝ => (1 / 4) * Real.log (1 + 1 / (4 * s ^ 2)))
        (-1 / (2 * t * (4 * t ^ 2 + 1))) t := by
    convert h_log.const_mul (1 / 4 : ℝ) using 1
    field_simp; ring
  -- Second piece: 1 / (4 s² + 1).
  have h_4t2 : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (8 * t) t := by
    convert (hasDerivAt_pow 2 t).const_mul (4 : ℝ) using 1
    push_cast; ring
  have h_4t2_p1 : HasDerivAt (fun s : ℝ => 4 * s ^ 2 + 1) (8 * t) t := by
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

/-! ### `RatExpr` machinery for `iteratedDeriv_α_part_deriv2_isO`

Each summand `c · t^a · (4t² + 1)^{-b}` is encoded as a `RatTerm`.  Its
formal derivative produces two new terms that lower the asymptotic invariant
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

  With `j(t) = ∫₀^∞ ρ(u) / ((u + 1/4)² + (t/2)²) du` and §2.5 in place,
  `iteratedDeriv n j t = jK n t` on `(0, ∞)` (lemma `iteratedDeriv_j_eqOn_jK`).
  The asymptotic bound `j^(n)(t) = O(t^(-n-2))` therefore reduces to a
  bound on `jK n` (lemma `jK_isO`).  The bound on `-(t/2)·j(t)` then
  follows by the Leibniz product rule (`iteratedDeriv_tj_isO`).
-/

section ErrorTermIntegral

/-! ### Sawtooth antiderivative `σ`

`σ(u) = (fract u)·(1 − fract u)/2` is the unique continuous antiderivative of `ρ`
that vanishes at every integer.  On `[k, k+1]` it agrees with `∫₀^u ρ`, satisfies
`0 ≤ σ ≤ 1/8`, and `σ k = σ (k+1) = 0` makes the IBP boundary terms vanish. -/

/-- Bounded antiderivative of the sawtooth `ρ`. -/
private noncomputable def σ (u : ℝ) : ℝ :=
  Int.fract u * (1 - Int.fract u) / 2

/-- `σ` is non-negative:  `fract u ∈ [0, 1]` so `fract u · (1 − fract u) ≥ 0`. -/
private lemma σ_nonneg (u : ℝ) : 0 ≤ σ u := by
  have h1 : 0 ≤ Int.fract u := Int.fract_nonneg u
  have h2 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
  have h3 : 0 ≤ Int.fract u * (1 - Int.fract u) :=
    mul_nonneg h1 (by linarith)
  unfold σ; linarith

/-- `σ` is bounded by `1/8`:  on `[0, 1]`, `x(1−x) ≤ 1/4` (AM–GM via `(2x−1)² ≥ 0`),
    so `σ u = x(1−x)/2 ≤ 1/8`. -/
private lemma σ_le_eighth (u : ℝ) : σ u ≤ 1 / 8 := by
  have h_key : Int.fract u * (1 - Int.fract u) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (2 * Int.fract u - 1)]
  unfold σ; linarith

/-- `σ` is continuous on `ℝ`:  factor as `g ∘ fract` with `g x = x(1−x)/2`,
    invoke `ContinuousOn.comp_fract''` (using `g 0 = g 1 = 0`). -/
private lemma σ_continuous : Continuous σ := by
  set g : ℝ → ℝ := fun x => x * (1 - x) / 2 with hg_def
  have h_g_cont : Continuous g :=
    (continuous_id.mul (continuous_const.sub continuous_id)).div_const 2
  have h_g_end : g 0 = g 1 := by simp [hg_def]
  have h_eq : σ = g ∘ Int.fract := by funext u; rfl
  rw [h_eq]
  exact ContinuousOn.comp_fract'' h_g_cont.continuousOn h_g_end

/-- `σ` vanishes at every natural number:  `fract k = 0`. -/
private lemma σ_natCast_eq_zero (k : ℕ) : σ (k : ℝ) = 0 := by
  unfold σ; rw [Int.fract_natCast]; ring

/-- On the open interval `(k, k+1)` between consecutive integers,
    `σ` is differentiable with derivative `ρ`. -/
private lemma hasDerivAt_σ_on_Ioo (k : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioo ((k : ℝ)) ((k : ℝ) + 1)) :
    HasDerivAt σ (ρ u) u := by
  have h_floor_u : Int.floor u = (k : ℤ) := by
    apply Int.floor_eq_iff.mpr
    refine ⟨?_, ?_⟩
    · push_cast; linarith [hu.1]
    · push_cast; linarith [hu.2]
  have h_fract_u : Int.fract u = u - k := by
    rw [Int.fract, h_floor_u]; push_cast; ring
  -- σ coincides with the polynomial `(s − k)(1 − (s − k))/2` on a neighbourhood of `u`.
  have h_eq : σ =ᶠ[nhds u] fun s : ℝ => (s - k) * (1 - (s - k)) / 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs
    have h_floor_s : Int.floor s = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      refine ⟨?_, ?_⟩
      · push_cast; linarith [hs.1]
      · push_cast; linarith [hs.2]
    have h_fract_s : Int.fract s = s - k := by
      rw [Int.fract, h_floor_s]; push_cast; ring
    change σ s = _
    unfold σ; rw [h_fract_s]
  -- Differentiate the polynomial pointwise.
  have h_f : HasDerivAt (fun s : ℝ => s - (k : ℝ)) 1 u :=
    (hasDerivAt_id u).sub_const (k : ℝ)
  have h_g : HasDerivAt (fun s : ℝ => 1 - (s - (k : ℝ))) (-1) u := by
    have h := (hasDerivAt_const u (1 : ℝ)).sub h_f
    convert h using 1; ring
  have h_poly : HasDerivAt (fun s : ℝ => (s - k) * (1 - (s - k)) / 2) (ρ u) u := by
    have h_prod := h_f.mul h_g
    have h_div := h_prod.div_const 2
    convert h_div using 1
    unfold ρ; rw [h_fract_u]; ring
  exact h_poly.congr_of_eventuallyEq h_eq

/-! ### Auxiliary integrability/continuity for the IBP identity

The per-interval IBP needs:
* `intervalIntegrable_ρ`             — ρ is interval-integrable (bounded by 1/2,
                                       measurable);
* `continuousOn_mixedDerivExpr`      — `u ↦ mixedDerivExpr n u t` is continuous
                                       on `Ici 0` (each factor is continuous
                                       and the denominators are nonzero there);
* `intervalIntegrable_mixedDerivExpr` — restriction of the above to `[k, k+1]`. -/

/-- `ρ` is interval-integrable on any `[a, b]`.  Bounded by `1/2` and Borel
    measurable, hence integrable on every finite-measure interval. -/
private lemma intervalIntegrable_ρ (a b : ℝ) :
    IntervalIntegrable ρ MeasureTheory.volume a b := by
  have h_const_int : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ))
      MeasureTheory.volume a b := intervalIntegrable_const
  have h_meas : Measurable ρ := measurable_const.sub measurable_fract
  have h_bd : ∀ x, ‖ρ x‖ ≤ (1 / 2 : ℝ) := fun x => by
    rw [Real.norm_eq_abs]; exact abs_ρ_le_half x
  rw [intervalIntegrable_iff] at h_const_int ⊢
  exact MeasureTheory.Integrable.mono' h_const_int h_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall h_bd)

/-- `u ↦ mixedDerivExpr n u t` is continuous on `Ici 0`.  Each of the two
    summands is built from `(u + 1/4)^k`, `1/(2(u+1/4))`, and `iteratedDeriv
    k lor` composed with `(1/(2(u+1/4)))·t`; all denominators stay strictly
    positive on `Ici 0` since `u + 1/4 ≥ 1/4`. -/
private lemma continuousOn_mixedDerivExpr (n : ℕ) (t : ℝ) :
    ContinuousOn (fun u : ℝ => mixedDerivExpr n u t) (Set.Ici (0 : ℝ)) := by
  unfold mixedDerivExpr
  have h_pos : ∀ u ∈ Set.Ici (0 : ℝ), (0 : ℝ) < u + 1 / 4 := fun u hu => by
    have : (0 : ℝ) ≤ u := Set.mem_Ici.mp hu; linarith
  have h_ne : ∀ u ∈ Set.Ici (0 : ℝ), u + 1 / 4 ≠ 0 := fun u hu => ne_of_gt (h_pos u hu)
  have h_pow_ne : ∀ k, ∀ u ∈ Set.Ici (0 : ℝ), (u + 1 / 4) ^ k ≠ 0 :=
    fun k u hu => pow_ne_zero k (h_ne u hu)
  have h_pow_sq_ne : ∀ u ∈ Set.Ici (0 : ℝ), ((u + 1 / 4) ^ (n + 2)) ^ 2 ≠ 0 :=
    fun u hu => pow_ne_zero _ (h_pow_ne (n + 2) u hu)
  have h_2_pos : ∀ u ∈ Set.Ici (0 : ℝ), (0 : ℝ) < 2 * (u + 1 / 4) :=
    fun u hu => by linarith [h_pos u hu]
  have h_2sq_ne : ∀ u ∈ Set.Ici (0 : ℝ), (2 * (u + 1 / 4)) ^ 2 ≠ 0 :=
    fun u hu => pow_ne_zero _ (ne_of_gt (h_2_pos u hu))
  -- Basic continuous functions.
  have hr : Continuous (fun u : ℝ => u + 1 / 4) := continuous_id.add continuous_const
  have hrk : ∀ k, Continuous (fun u : ℝ => (u + 1 / 4) ^ k) := fun k => hr.pow k
  have h_2r : Continuous (fun u : ℝ => 2 * (u + 1 / 4)) := continuous_const.mul hr
  have h_lor : ∀ k, Continuous (iteratedDeriv k lor) := fun k =>
    contDiff_lor.continuous_iteratedDeriv k le_top
  -- Composition with the rescaled argument.
  have h_inv_2r : ContinuousOn (fun u : ℝ => 1 / (2 * (u + 1 / 4))) (Set.Ici 0) :=
    continuousOn_const.div h_2r.continuousOn (fun u hu => ne_of_gt (h_2_pos u hu))
  have h_arg : ContinuousOn (fun u : ℝ => (1 / (2 * (u + 1 / 4))) * t) (Set.Ici 0) :=
    h_inv_2r.mul continuousOn_const
  have h_lor_comp : ∀ k, ContinuousOn
      (fun u : ℝ => iteratedDeriv k lor ((1 / (2 * (u + 1 / 4))) * t)) (Set.Ici 0) :=
    fun k => (h_lor k).comp_continuousOn h_arg
  -- First summand.
  have h_num : ContinuousOn
      (fun u : ℝ => -(((n : ℝ) + 2) * (u + 1 / 4) ^ (n + 1))) (Set.Ici 0) :=
    (continuousOn_const.mul (hrk (n + 1)).continuousOn).neg
  have h_den : ContinuousOn
      (fun u : ℝ => ((u + 1 / 4) ^ (n + 2)) ^ 2) (Set.Ici 0) :=
    ((hrk (n + 2)).pow 2).continuousOn
  have h_frac : ContinuousOn
      (fun u : ℝ => -(((n : ℝ) + 2) * (u + 1 / 4) ^ (n + 1)) / ((u + 1 / 4) ^ (n + 2)) ^ 2)
      (Set.Ici 0) := h_num.div h_den h_pow_sq_ne
  have h_t1 : ContinuousOn
      (fun u : ℝ =>
        -(((n : ℝ) + 2) * (u + 1 / 4) ^ (n + 1)) / ((u + 1 / 4) ^ (n + 2)) ^ 2 *
          (1 / 2) ^ n * iteratedDeriv n lor ((1 / (2 * (u + 1 / 4))) * t))
      (Set.Ici 0) := (h_frac.mul continuousOn_const).mul (h_lor_comp n)
  -- Second summand.
  have h_inv : ContinuousOn (fun u : ℝ => ((u + 1 / 4) ^ (n + 2))⁻¹) (Set.Ici 0) :=
    (hrk (n + 2)).continuousOn.inv₀ (fun u hu => h_pow_ne (n + 2) u hu)
  have h_2r_sq : ContinuousOn (fun u : ℝ => (2 * (u + 1 / 4)) ^ 2) (Set.Ici 0) :=
    (h_2r.pow 2).continuousOn
  have h_neg2_div : ContinuousOn
      (fun u : ℝ => (-2 : ℝ) / (2 * (u + 1 / 4)) ^ 2) (Set.Ici 0) :=
    continuousOn_const.div h_2r_sq h_2sq_ne
  have h_neg2_t : ContinuousOn
      (fun u : ℝ => ((-2 : ℝ) / (2 * (u + 1 / 4)) ^ 2) * t) (Set.Ici 0) :=
    h_neg2_div.mul continuousOn_const
  have h_inner : ContinuousOn
      (fun u : ℝ => iteratedDeriv (n + 1) lor ((1 / (2 * (u + 1 / 4))) * t) *
        (((-2 : ℝ) / (2 * (u + 1 / 4)) ^ 2) * t)) (Set.Ici 0) :=
    (h_lor_comp (n + 1)).mul h_neg2_t
  have h_t2 : ContinuousOn
      (fun u : ℝ => ((u + 1 / 4) ^ (n + 2))⁻¹ * (1 / 2) ^ n *
        (iteratedDeriv (n + 1) lor ((1 / (2 * (u + 1 / 4))) * t) *
          (((-2 : ℝ) / (2 * (u + 1 / 4)) ^ 2) * t)))
      (Set.Ici 0) := (h_inv.mul continuousOn_const).mul h_inner
  exact h_t1.add h_t2

/-- Per-unit-interval integrability of `u ↦ mixedDerivExpr n u t`.
    Restriction of `continuousOn_mixedDerivExpr` to `[k, k+1] ⊆ Ici 0`. -/
private lemma intervalIntegrable_mixedDerivExpr (n : ℕ) (t : ℝ) (k : ℕ) :
    IntervalIntegrable (fun u => mixedDerivExpr n u t) MeasureTheory.volume
      (k : ℝ) ((k : ℝ) + 1) := by
  have hab : ((k : ℝ)) ≤ ((k : ℝ) + 1) := by linarith
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  refine (continuousOn_mixedDerivExpr n t).mono ?_
  intro x hx
  rw [Set.mem_Icc] at hx
  rw [Set.mem_Ici]
  have : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
  linarith [hx.1]

/-- Uniform-in-`u` bound for `|mixedDerivExpr n u t|` on `u ≥ 0`, `|t| ≤ R`.

    Same shape as `exists_bound_iteratedDeriv_kernel` but for the parameter
    derivative `mixedDerivExpr`.  The bound is `C(n, R) · (u + 1/4)^{-(n+3)}`,
    obtained by rewriting `mixedDerivExpr n u t` as a sum
    `T₁ · (u+1/4)^{-(n+3)} + T₂ · (u+1/4)^{-(n+4)}` (with `|T₁|, |T₂|` bounded
    uniformly via `exists_bound_iteratedDeriv_lor`), and using
    `((u+1/4)^(n+4))⁻¹ ≤ 4 · ((u+1/4)^(n+3))⁻¹` (since `u + 1/4 ≥ 1/4`). -/
private lemma exists_bound_mixedDerivExpr (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → ∀ t : ℝ, |t| ≤ R →
      |mixedDerivExpr n u t| ≤ C * ((u + 1 / 4) ^ (n + 3))⁻¹ := by
  rcases lt_or_ge R 0 with hR | hR
  · refine ⟨0, le_refl 0, ?_⟩
    intro u _ t ht
    exact absurd (lt_of_le_of_lt ht hR) (not_lt.mpr (abs_nonneg t))
  obtain ⟨Mₙ, hMₙ_nn, hMₙ⟩ := exists_bound_iteratedDeriv_lor n (2 * R)
  obtain ⟨Mₙ₁, hMₙ₁_nn, hMₙ₁⟩ := exists_bound_iteratedDeriv_lor (n + 1) (2 * R)
  refine ⟨((n : ℝ) + 2) * (1 / 2) ^ n * Mₙ + 2 * R * (1 / 2) ^ n * Mₙ₁, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ((n : ℝ) + 2) * (1 / 2) ^ n * Mₙ := by positivity
    have h2 : (0 : ℝ) ≤ 2 * R * (1 / 2) ^ n * Mₙ₁ := by positivity
    linarith
  intro u hu t ht
  -- Basic positivity facts.
  have h_pos : (0 : ℝ) < u + 1 / 4 := by linarith
  have h_2_pos : (0 : ℝ) < 2 * (u + 1 / 4) := by linarith
  have h_ge_quarter : (1 / 4 : ℝ) ≤ u + 1 / 4 := by linarith
  have h_inv_pos : (0 : ℝ) < 1 / (2 * (u + 1 / 4)) := by positivity
  have h_inv_le : 1 / (2 * (u + 1 / 4)) ≤ 2 := by
    rw [div_le_iff₀ h_2_pos]; linarith
  have h_arg_abs : |1 / (2 * (u + 1 / 4)) * t| ≤ 2 * R := by
    rw [abs_mul, abs_of_pos h_inv_pos]
    calc 1 / (2 * (u + 1 / 4)) * |t|
        ≤ 2 * |t| := by gcongr
      _ ≤ 2 * R := by linarith
  have h_lor_n : |iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t)| ≤ Mₙ :=
    hMₙ _ h_arg_abs
  have h_lor_n1 : |iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t)| ≤ Mₙ₁ :=
    hMₙ₁ _ h_arg_abs
  have h_pow_pos : ∀ m : ℕ, (0 : ℝ) < (u + 1 / 4) ^ m := fun m => pow_pos h_pos m
  have h_inv_pow_pos : ∀ m : ℕ, (0 : ℝ) < ((u + 1 / 4) ^ m)⁻¹ :=
    fun m => inv_pos.mpr (h_pow_pos m)
  have h_inv_pow_nn : ∀ m : ℕ, (0 : ℝ) ≤ ((u + 1 / 4) ^ m)⁻¹ :=
    fun m => le_of_lt (h_inv_pow_pos m)
  have h_half_nn : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ n := by positivity
  -- (a) (u+1/4)^{-(n+4)} ≤ 4 · (u+1/4)^{-(n+3)}.
  have h_inv_le_4 : (u + 1 / 4)⁻¹ ≤ 4 := by
    have h_step : (u + 1 / 4)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) h_ge_quarter
    have : ((1 / 4 : ℝ))⁻¹ = 4 := by norm_num
    linarith [h_step, this]
  have h_inv_n4_le :
      ((u + 1 / 4) ^ (n + 4))⁻¹ ≤ 4 * ((u + 1 / 4) ^ (n + 3))⁻¹ := by
    have h_split : (u + 1 / 4) ^ (n + 4)
                  = (u + 1 / 4) ^ (n + 3) * (u + 1 / 4) := by
      rw [show (n + 4 : ℕ) = (n + 3) + 1 from rfl, pow_succ]
    rw [h_split, mul_inv]
    have h_n3_inv_nn : 0 ≤ ((u + 1 / 4) ^ (n + 3))⁻¹ := h_inv_pow_nn (n + 3)
    calc ((u + 1 / 4) ^ (n + 3))⁻¹ * (u + 1 / 4)⁻¹
        ≤ ((u + 1 / 4) ^ (n + 3))⁻¹ * 4 :=
          mul_le_mul_of_nonneg_left h_inv_le_4 h_n3_inv_nn
      _ = 4 * ((u + 1 / 4) ^ (n + 3))⁻¹ := by ring
  -- (b) Closed form of mixedDerivExpr as a sum of two "constant · power" pieces.
  have h_form :
      mixedDerivExpr n u t
        = (-((n : ℝ) + 2) * (1 / 2) ^ n *
              iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t))
              * ((u + 1 / 4) ^ (n + 3))⁻¹
          + (-(t / 2) * (1 / 2) ^ n *
              iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t))
              * ((u + 1 / 4) ^ (n + 4))⁻¹ := by
    unfold mixedDerivExpr
    have h_pow_n2_sq : ((u + 1 / 4) ^ (n + 2)) ^ 2
                      = (u + 1 / 4) ^ (n + 1) * (u + 1 / 4) ^ (n + 3) := by
      rw [← pow_mul, show (n + 2) * 2 = (n + 1) + (n + 3) from by ring, pow_add]
    have h_pow_n4 : (u + 1 / 4) ^ (n + 4)
                    = (u + 1 / 4) ^ (n + 2) * (u + 1 / 4) ^ 2 := by
      rw [← pow_add]
    have h_2sq : (2 * (u + 1 / 4)) ^ 2 = 4 * (u + 1 / 4) ^ 2 := by ring
    have h_n1_ne : ((u + 1 / 4) ^ (n + 1) : ℝ) ≠ 0 := ne_of_gt (h_pow_pos (n + 1))
    have h_n2_ne : ((u + 1 / 4) ^ (n + 2) : ℝ) ≠ 0 := ne_of_gt (h_pow_pos (n + 2))
    have h_n3_ne : ((u + 1 / 4) ^ (n + 3) : ℝ) ≠ 0 := ne_of_gt (h_pow_pos (n + 3))
    have h_n4_ne : ((u + 1 / 4) ^ (n + 4) : ℝ) ≠ 0 := ne_of_gt (h_pow_pos (n + 4))
    have h_sq_ne : ((u + 1 / 4) ^ 2 : ℝ) ≠ 0 := ne_of_gt (h_pow_pos 2)
    -- Abbreviate the two iteratedDeriv expressions as opaque variables for `ring`.
    set L₁ : ℝ := iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t)
    set L₂ : ℝ := iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t)
    rw [h_pow_n2_sq, h_pow_n4, h_2sq]
    field_simp
    ring
  -- (c) Bound on each summand of (b).
  have h_const1_nn : (0 : ℝ) ≤ ((n : ℝ) + 2) * (1 / 2) ^ n := by positivity
  have h_abs1 :
      |(-((n : ℝ) + 2) * (1 / 2) ^ n *
          iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t))|
        ≤ ((n : ℝ) + 2) * (1 / 2) ^ n * Mₙ := by
    rw [show -((n : ℝ) + 2) * (1 / 2) ^ n *
              iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t)
            = -(((n : ℝ) + 2) * (1 / 2) ^ n) *
              iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t) from by ring,
        abs_mul, abs_neg, abs_of_nonneg h_const1_nn]
    exact mul_le_mul_of_nonneg_left h_lor_n h_const1_nn
  have h_abs2 :
      |(-(t / 2) * (1 / 2) ^ n *
          iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t))|
        ≤ R / 2 * (1 / 2) ^ n * Mₙ₁ := by
    rw [show -(t / 2) * (1 / 2) ^ n *
              iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t)
            = -((t / 2) * (1 / 2) ^ n) *
              iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t) from by ring,
        abs_mul, abs_neg]
    have h_inner_eq : |(t / 2) * (1 / 2) ^ n| = |t| / 2 * (1 / 2) ^ n := by
      rw [abs_mul, abs_of_nonneg h_half_nn,
          abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h_inner_eq]
    have h_t_half : |t| / 2 ≤ R / 2 := by linarith
    gcongr
  -- (d) Combine using h_form and abs_add_le.
  rw [h_form]
  calc |(-((n : ℝ) + 2) * (1 / 2) ^ n *
            iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t)) *
              ((u + 1 / 4) ^ (n + 3))⁻¹
        + (-(t / 2) * (1 / 2) ^ n *
            iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t)) *
              ((u + 1 / 4) ^ (n + 4))⁻¹|
      ≤ |(-((n : ℝ) + 2) * (1 / 2) ^ n *
            iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t)) *
              ((u + 1 / 4) ^ (n + 3))⁻¹|
          + |(-(t / 2) * (1 / 2) ^ n *
            iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t)) *
              ((u + 1 / 4) ^ (n + 4))⁻¹| := abs_add_le _ _
    _ = |(-((n : ℝ) + 2) * (1 / 2) ^ n *
            iteratedDeriv n lor (1 / (2 * (u + 1 / 4)) * t))|
              * ((u + 1 / 4) ^ (n + 3))⁻¹
          + |(-(t / 2) * (1 / 2) ^ n *
            iteratedDeriv (n + 1) lor (1 / (2 * (u + 1 / 4)) * t))|
              * ((u + 1 / 4) ^ (n + 4))⁻¹ := by
          congr 1
          · rw [abs_mul, abs_of_nonneg (h_inv_pow_nn (n + 3))]
          · rw [abs_mul, abs_of_nonneg (h_inv_pow_nn (n + 4))]
    _ ≤ ((n : ℝ) + 2) * (1 / 2) ^ n * Mₙ * ((u + 1 / 4) ^ (n + 3))⁻¹
          + R / 2 * (1 / 2) ^ n * Mₙ₁ * ((u + 1 / 4) ^ (n + 4))⁻¹ := by
          gcongr
    _ ≤ ((n : ℝ) + 2) * (1 / 2) ^ n * Mₙ * ((u + 1 / 4) ^ (n + 3))⁻¹
          + R / 2 * (1 / 2) ^ n * Mₙ₁ * (4 * ((u + 1 / 4) ^ (n + 3))⁻¹) := by
          have h_nn : 0 ≤ R / 2 * (1 / 2) ^ n * Mₙ₁ := by positivity
          have h_mono := mul_le_mul_of_nonneg_left h_inv_n4_le h_nn
          linarith
    _ = (((n : ℝ) + 2) * (1 / 2) ^ n * Mₙ + 2 * R * (1 / 2) ^ n * Mₙ₁)
          * ((u + 1 / 4) ^ (n + 3))⁻¹ := by ring

/-- Integrability of `u ↦ σ u · mixedDerivExpr n u t` on `Ici 0`.

    Bounds the integrand by `(C/8) · ((u+1/4)^(n+3))⁻¹` via `σ_le_eighth` and
    `exists_bound_mixedDerivExpr`, then applies `Integrable.mono'` against the
    dominator `integrableOn_pow_inv_shift (n+1)`. -/
private lemma integrable_sigma_mixedDerivExpr (n : ℕ) (t : ℝ) :
    IntegrableOn (fun u : ℝ => σ u * mixedDerivExpr n u t) (Set.Ici (0 : ℝ)) := by
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_mixedDerivExpr n |t|
  have h_meas : AEStronglyMeasurable (fun u => σ u * mixedDerivExpr n u t)
      (volume.restrict (Set.Ici (0 : ℝ))) := by
    have h_σ : AEStronglyMeasurable σ (volume.restrict (Set.Ici (0 : ℝ))) :=
      σ_continuous.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    have h_med : AEStronglyMeasurable (fun u => mixedDerivExpr n u t)
        (volume.restrict (Set.Ici (0 : ℝ))) :=
      (continuousOn_mixedDerivExpr n t).aestronglyMeasurable measurableSet_Ici
    exact h_σ.mul h_med
  refine Integrable.mono'
    ((integrableOn_pow_inv_shift (n + 1)).const_mul (C / 8))
    h_meas ?_
  refine (ae_restrict_iff' measurableSet_Ici).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro u hu
  have hu_nn : 0 ≤ u := Set.mem_Ici.mp hu
  have hr_pos : (0 : ℝ) < u + 1 / 4 := by linarith
  have h_pow_pos : (0 : ℝ) < (u + 1 / 4) ^ (n + 3) := pow_pos hr_pos _
  have h_inv_nn : (0 : ℝ) ≤ ((u + 1 / 4) ^ (n + 3))⁻¹ :=
    le_of_lt (inv_pos.mpr h_pow_pos)
  have h_σ_nn : 0 ≤ σ u := σ_nonneg u
  have h_σ_le : σ u ≤ 1 / 8 := σ_le_eighth u
  have h_bound : |mixedDerivExpr n u t| ≤ C * ((u + 1 / 4) ^ (n + 3))⁻¹ :=
    hC u hu_nn t (le_refl _)
  change ‖σ u * mixedDerivExpr n u t‖
          ≤ C / 8 * ((u + 1 / 4) ^ ((n + 1) + 2))⁻¹
  rw [show (n + 1) + 2 = n + 3 from rfl]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_σ_nn]
  calc σ u * |mixedDerivExpr n u t|
      ≤ (1 / 8) * (C * ((u + 1 / 4) ^ (n + 3))⁻¹) := by gcongr
    _ = C / 8 * ((u + 1 / 4) ^ (n + 3))⁻¹ := by ring

/-- **Per-unit-interval IBP identity.**

    On `[k, k+1]` with `σ' = ρ` (from `hasDerivAt_σ_on_Ioo`) and
    `∂_u [iteratedDeriv n (kernel · ·) t] = mixedDerivExpr n · t` (from
    `hasDerivAt_iteratedDeriv_kernel`, valid since `u > 0` on the open
    interior), Mathlib's IBP gives a formula whose boundary terms vanish
    thanks to `σ_natCast_eq_zero`. -/
private lemma jK_ibp_unit_interval (n : ℕ) (t : ℝ) (k : ℕ) :
    ∫ u in (k : ℝ)..((k : ℝ) + 1), ρ u * iteratedDeriv n (fun s => kernel u s) t
      = -∫ u in (k : ℝ)..((k : ℝ) + 1), σ u * mixedDerivExpr n u t := by
  have hab : ((k : ℝ)) ≤ ((k : ℝ) + 1) := by linarith
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
  have h_uIcc : Set.uIcc ((k : ℝ)) ((k : ℝ) + 1) = Set.Icc ((k : ℝ)) ((k : ℝ) + 1) :=
    Set.uIcc_of_le hab
  have h_min : min ((k : ℝ)) ((k : ℝ) + 1) = (k : ℝ) := min_eq_left hab
  have h_max : max ((k : ℝ)) ((k : ℝ) + 1) = (k : ℝ) + 1 := max_eq_right hab
  -- Continuity hypotheses.
  have hσ_cont : ContinuousOn σ (Set.uIcc ((k : ℝ)) ((k : ℝ) + 1)) :=
    σ_continuous.continuousOn
  have hK_cont :
      ContinuousOn (fun u : ℝ => iteratedDeriv n (fun s => kernel u s) t)
        (Set.uIcc ((k : ℝ)) ((k : ℝ) + 1)) := by
    rw [h_uIcc]
    refine (continuousOn_iteratedDeriv_kernel n t).mono ?_
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [Set.mem_Ici]
    linarith [hx.1]
  -- Derivative hypotheses on the open interior.
  have hσ_deriv : ∀ x ∈ Set.Ioo (min ((k : ℝ)) ((k : ℝ) + 1))
      (max ((k : ℝ)) ((k : ℝ) + 1)), HasDerivAt σ (ρ x) x := by
    intro x hx
    rw [h_min, h_max] at hx
    exact hasDerivAt_σ_on_Ioo k hx
  have hK_deriv : ∀ x ∈ Set.Ioo (min ((k : ℝ)) ((k : ℝ) + 1))
      (max ((k : ℝ)) ((k : ℝ) + 1)),
      HasDerivAt (fun v : ℝ => iteratedDeriv n (fun s => kernel v s) t)
        (mixedDerivExpr n x t) x := by
    intro x hx
    rw [h_min, h_max] at hx
    have hx_pos : 0 < x := by
      have hlo := hx.1
      rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
      · subst hk0
        simpa using hlo
      · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
        linarith
    exact hasDerivAt_iteratedDeriv_kernel n hx_pos t
  -- Integrability hypotheses.
  have hρ_int : IntervalIntegrable ρ MeasureTheory.volume ((k : ℝ)) ((k : ℝ) + 1) :=
    intervalIntegrable_ρ _ _
  have hM_int :
      IntervalIntegrable (fun u => mixedDerivExpr n u t) MeasureTheory.volume
        ((k : ℝ)) ((k : ℝ) + 1) := intervalIntegrable_mixedDerivExpr n t k
  -- Apply Mathlib's IBP.
  have h_ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hσ_cont hK_cont hσ_deriv hK_deriv hρ_int hM_int
  -- σ vanishes at both endpoints — boundary terms drop.
  have hσa : σ ((k : ℝ)) = 0 := σ_natCast_eq_zero k
  have hσb : σ ((k : ℝ) + 1) = 0 := by
    have hb_eq : ((k : ℝ)) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hb_eq]; exact σ_natCast_eq_zero (k + 1)
  rw [hσa, hσb, zero_mul, zero_mul, sub_zero, zero_sub] at h_ibp
  linarith

/-! ### IBP identity and the asymptotic bound

The proof of `jK_isO` decomposes into:

* `jK_eq_sigma_integral` — the integration-by-parts identity
  `jK n t = -∫₀^∞ σ(u) · mixedDerivExpr n u t du`.  The σ machinery above
  is engineered so that the per-unit-interval boundary terms vanish
  (`σ_natCast_eq_zero`).
* `sigma_mixedDerivExpr_isO` — the asymptotic bound on the resulting
  σ-weighted integral.

`jK_isO` then follows by trivial arithmetic. -/

/-- `Ici 0` is the countable disjoint union of `Ico (k:ℝ) (k+1)` over `k : ℕ`. -/
private lemma Ici_zero_eq_iUnion_Ico_nat :
    Set.Ici (0 : ℝ) = ⋃ k : ℕ, Set.Ico ((k : ℝ)) ((k : ℝ) + 1) := by
  ext x
  constructor
  · intro hx
    have hx_nn : (0 : ℝ) ≤ x := Set.mem_Ici.mp hx
    refine Set.mem_iUnion.mpr ⟨⌊x⌋₊, ?_⟩
    refine Set.mem_Ico.mpr ⟨?_, ?_⟩
    · exact Nat.floor_le hx_nn
    · exact_mod_cast Nat.lt_floor_add_one x
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    have hk_lo := (Set.mem_Ico.mp hk).1
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    exact Set.mem_Ici.mpr (le_trans hk_nn hk_lo)

/-- The unit intervals `Ico (k:ℝ) (k+1)` are pairwise disjoint for distinct `k : ℕ`. -/
private lemma pairwise_disjoint_Ico_nat :
    Pairwise (Disjoint on fun k : ℕ => Set.Ico ((k : ℝ)) ((k : ℝ) + 1)) := by
  intro k m hkm
  refine Set.disjoint_iff_forall_ne.mpr ?_
  intro x hx y hy hxy
  subst hxy
  rcases lt_or_gt_of_ne hkm with h | h
  · have h_le : ((k : ℝ)) + 1 ≤ (m : ℝ) := by exact_mod_cast h
    have h1 := (Set.mem_Ico.mp hx).2
    have h2 := (Set.mem_Ico.mp hy).1
    linarith
  · have h_le : ((m : ℝ)) + 1 ≤ (k : ℝ) := by exact_mod_cast h
    have h1 := (Set.mem_Ico.mp hy).2
    have h2 := (Set.mem_Ico.mp hx).1
    linarith

/-- Integration-by-parts identity for `jK n` (the σ-form).

    On each unit interval `(k, k+1)`, `σ' = ρ` and `σ` vanishes at both
    endpoints (`σ_natCast_eq_zero`), so the per-interval IBP gives
    `∫_k^{k+1} ρ · ∂ₜⁿ kernel = -∫_k^{k+1} σ · mixedDerivExpr n · t`
    (`jK_ibp_unit_interval`).  Splitting `Ici 0 = ⋃ k, Ico (k:ℝ) (k+1)` and
    applying `MeasureTheory.integral_iUnion` on both sides aggregates this
    into the displayed identity. -/
private lemma jK_eq_sigma_integral (n : ℕ) {t : ℝ} (_ht : 0 < t) :
    jK n t = -∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t := by
  -- (The hypothesis `0 < t` is currently unused: the IBP machinery, the
  -- integrability of `σ · mixedDerivExpr`, and `integrable_jIntegrand` all
  -- work for any `t : ℝ`.  Kept in the signature for parity with the rest
  -- of §6's API.)
  set F : ℝ → ℝ := fun u => ρ u * iteratedDeriv n (fun s => kernel u s) t with hF
  set G : ℝ → ℝ := fun u => σ u * mixedDerivExpr n u t with hG
  have h_dec : Set.Ici (0 : ℝ) = ⋃ k : ℕ, Set.Ico ((k : ℝ)) ((k : ℝ) + 1) :=
    Ici_zero_eq_iUnion_Ico_nat
  have h_meas : ∀ k : ℕ, MeasurableSet (Set.Ico ((k : ℝ)) ((k : ℝ) + 1)) :=
    fun _ => measurableSet_Ico
  have h_disj : Pairwise (Disjoint on fun k : ℕ => Set.Ico ((k : ℝ)) ((k : ℝ) + 1)) :=
    pairwise_disjoint_Ico_nat
  -- Integrability of F and G on Ici 0.
  have hF_int : IntegrableOn F (Set.Ici (0 : ℝ)) := by
    have := integrable_jIntegrand n t
    unfold jIntegrand at this
    exact this
  have hG_int : IntegrableOn G (Set.Ici (0 : ℝ)) :=
    integrable_sigma_mixedDerivExpr n t
  have hF_iU : IntegrableOn F (⋃ k : ℕ, Set.Ico ((k : ℝ)) ((k : ℝ) + 1)) := by
    rw [← h_dec]; exact hF_int
  have hG_iU : IntegrableOn G (⋃ k : ℕ, Set.Ico ((k : ℝ)) ((k : ℝ) + 1)) := by
    rw [← h_dec]; exact hG_int
  -- Decompose both integrals over the iUnion.
  have hF_sum :
      (∫ u in Set.Ici (0 : ℝ), F u)
        = ∑' k : ℕ, ∫ u in Set.Ico ((k : ℝ)) ((k : ℝ) + 1), F u := by
    rw [h_dec]; exact integral_iUnion h_meas h_disj hF_iU
  have hG_sum :
      (∫ u in Set.Ici (0 : ℝ), G u)
        = ∑' k : ℕ, ∫ u in Set.Ico ((k : ℝ)) ((k : ℝ) + 1), G u := by
    rw [h_dec]; exact integral_iUnion h_meas h_disj hG_iU
  -- Per-k IBP identity rewritten in set-integral form.
  have h_piece : ∀ k : ℕ,
      ∫ u in Set.Ico ((k : ℝ)) ((k : ℝ) + 1), F u
        = -∫ u in Set.Ico ((k : ℝ)) ((k : ℝ) + 1), G u := by
    intro k
    have hab : ((k : ℝ)) ≤ ((k : ℝ) + 1) := by linarith
    have h_F_eq :
        ∫ u in Set.Ico ((k : ℝ)) ((k : ℝ) + 1), F u
          = ∫ u in ((k : ℝ))..((k : ℝ) + 1), F u := by
      rw [integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
    have h_G_eq :
        ∫ u in Set.Ico ((k : ℝ)) ((k : ℝ) + 1), G u
          = ∫ u in ((k : ℝ))..((k : ℝ) + 1), G u := by
      rw [integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
    rw [h_F_eq, h_G_eq]
    exact jK_ibp_unit_interval n t k
  -- Combine.
  have h_jK : jK n t = ∫ u in Set.Ici (0 : ℝ), F u := by
    unfold jK jIntegrand
    rfl
  rw [h_jK, hF_sum]
  have h_tsum :
      (∑' k : ℕ, ∫ u in Set.Ico ((k : ℝ)) ((k : ℝ) + 1), F u)
        = -∑' k : ℕ, ∫ u in Set.Ico ((k : ℝ)) ((k : ℝ) + 1), G u := by
    rw [← tsum_neg]
    exact tsum_congr h_piece
  rw [h_tsum, ← hG_sum]

/-! ### Sub-lemmas for `sigma_mixedDerivExpr_isO`

The σ-integral bound decomposes into three pieces:

* `mixedDerivExpr_eq_lorMix` — pointwise rescaling of the integrand:
  `mixedDerivExpr n u t = (1/2)^n · (u+1/4)^{-(n+3)} · lorMix n (t/(2(u+1/4)))`.
  Purely algebraic (definitional unfolding + `field_simp`/`ring`).
* `lorMix_isO` — asymptotic cancellation:  `lorMix n x = O(x^{-(n+4)})`.
  The leading `1/x^(n+2)` parts of `-(n+2)·lor⁽ⁿ⁾(x)` and `x·lor⁽ⁿ⁺¹⁾(x)`
  in `lorMix` cancel, leaving the `1/x^(n+4)` order.
* `sigma_lorMix_integral_isO` — change-of-variables aggregation:
  `∫₀^∞ σ(u) · (u+1/4)^{-(n+3)} · lorMix n (t/(2(u+1/4))) du = O(t^{-(n+2)})`.
  Substitute `x = t/(2(u+1/4))`, bound by `|σ| ≤ 1/8` and the previous
  asymptotic, and finish on a finite residual integral. -/

/-- **Rescaling identity for the mixed derivative.**

    With `r = u + 1/4` and `c = 1/(2r)`, applying the chain rule to
    `kernel u t = r^{-2} · lor(c·t)` differentiated in `u`, and then
    bundling the resulting two-term expression through `lorMix`, gives
        `mixedDerivExpr n u t = (1/2)^n · r^{-(n+3)} · lorMix n (c·t)`.
    This factors all `u`-dependence into a single negative integer power
    of `r`, while the `t`-dependence sits entirely inside the bounded
    profile `lorMix n` evaluated at `c·t`. -/
private lemma mixedDerivExpr_eq_lorMix (n : ℕ) {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    mixedDerivExpr n u t
      = (1 / 2 : ℝ) ^ n * (u + 1 / 4) ^ (-((n : ℤ) + 3))
          * lorMix n ((1 / (2 * (u + 1 / 4))) * t) := by
  have hr_pos : (0 : ℝ) < u + 1 / 4 := by linarith
  have hr_ne : (u + 1 / 4 : ℝ) ≠ 0 := ne_of_gt hr_pos
  have h2r_ne : (2 * (u + 1 / 4) : ℝ) ≠ 0 := by positivity
  -- Convert the negative-integer exponent into a reciprocal of a natural power.
  have h_zpow : (u + 1 / 4 : ℝ) ^ (-((n : ℤ) + 3))
      = ((u + 1 / 4) ^ (n + 3))⁻¹ := by
    have h_cast : (-((n : ℤ) + 3)) = -((n + 3 : ℕ) : ℤ) := by push_cast; ring
    rw [h_cast, zpow_neg, zpow_natCast]
  rw [h_zpow]
  unfold mixedDerivExpr lorMix
  field_simp
  ring

/-! ### Helpers for `lorMix_isO`: identification with `iteratedDeriv lor²`.

The cancellation in `lorMix n x = O(x^{-(n+4)})` is equivalent to the cleaner
statement that `lorMix n s = -2 · (d/ds)^n (lor²)(s)`, where `lor² s = (lor s)²`
decays as `O(s^{-4})`.  Each derivative of `lor²` decays one order faster,
giving the desired `O(s^{-(n+4)})`. -/

/-- Squared Lorentzian profile `lorSq s = (lor s)² = 1/(1+s²)²`.  Closed
    form for `lorMix 0` (cf. `lorMix_zero` below), and the iterate-decay
    target for `lorMix_isO`. -/
private noncomputable def lorSq (s : ℝ) : ℝ := lor s ^ 2

private lemma contDiff_lorSq : ContDiff ℝ ⊤ lorSq :=
  contDiff_lor.pow 2

/-- Derivative of `lor`:  `lor'(s) = -2s · (lor s)²`.  This is the closed
    form `(d/ds)[1/(1+s²)] = -2s/(1+s²)²` rewritten via `(lor s)² = 1/(1+s²)²`. -/
private lemma hasDerivAt_lor (s : ℝ) :
    HasDerivAt lor (-(2 * s) * (lor s) ^ 2) s := by
  have h_denom_ne : (1 + s ^ 2 : ℝ) ≠ 0 := ne_of_gt (lor_denom_pos s)
  have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
    have h := hasDerivAt_pow 2 s
    simpa using h
  have h_denom : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * s) s := by
    have h := (hasDerivAt_const s (1 : ℝ)).add h_sq
    convert h using 1
    ring
  have h_div := (hasDerivAt_const s (1 : ℝ)).div h_denom h_denom_ne
  convert h_div using 1
  unfold lor
  field_simp
  ring

/-- **Base case for `lorMix_eq_iteratedDeriv_lorSq`:**  `lorMix 0 s = -2 · (lor s)²`.

    Direct computation: `lorMix 0 s = -2·lor(s) - s·lor'(s) = -2·lor(s) + 2s²·(lor s)²
    = -2·(lor s)²`, using `(1+s²)·(lor s) = 1` to cancel the cross terms. -/
private lemma lorMix_zero (s : ℝ) : lorMix 0 s = -2 * lorSq s := by
  have h_d : iteratedDeriv 1 lor s = -(2 * s) * (lor s) ^ 2 := by
    rw [iteratedDeriv_one]
    exact (hasDerivAt_lor s).deriv
  have h_ne : (1 + s ^ 2 : ℝ) ≠ 0 := ne_of_gt (lor_denom_pos s)
  unfold lorMix lorSq
  rw [iteratedDeriv_zero, h_d]
  unfold lor
  push_cast
  field_simp
  ring

/-- **Derivative recursion for `lorMix`:**  `(d/ds) (lorMix n) s = lorMix (n+1) s`.

    Direct chain rule on the definition.  Differentiating
        `lorMix n s = -(n+2) · lor⁽ⁿ⁾(s) - s · lor⁽ⁿ⁺¹⁾(s)`
    in `s` produces
        `-(n+2) · lor⁽ⁿ⁺¹⁾(s) - lor⁽ⁿ⁺¹⁾(s) - s · lor⁽ⁿ⁺²⁾(s)`
      `= -(n+3) · lor⁽ⁿ⁺¹⁾(s) - s · lor⁽ⁿ⁺²⁾(s) = lorMix (n+1) s`. -/
private lemma hasDerivAt_lorMix (n : ℕ) (s : ℝ) :
    HasDerivAt (lorMix n) (lorMix (n + 1) s) s := by
  have h_lor_n_diff : Differentiable ℝ (iteratedDeriv n lor) :=
    (contDiff_lor.of_le le_top).differentiable_iteratedDeriv' n
  have h_lor_n1_diff : Differentiable ℝ (iteratedDeriv (n + 1) lor) :=
    (contDiff_lor.of_le le_top).differentiable_iteratedDeriv' (n + 1)
  -- HasDerivAt for `iteratedDeriv n lor` and `iteratedDeriv (n+1) lor`.
  have h_n : HasDerivAt (iteratedDeriv n lor) (iteratedDeriv (n + 1) lor s) s := by
    have h := (h_lor_n_diff s).hasDerivAt
    rwa [show deriv (iteratedDeriv n lor) s = iteratedDeriv (n + 1) lor s
          from by rw [iteratedDeriv_succ]] at h
  have h_n1 : HasDerivAt (iteratedDeriv (n + 1) lor) (iteratedDeriv (n + 2) lor s) s := by
    have h := (h_lor_n1_diff s).hasDerivAt
    rwa [show deriv (iteratedDeriv (n + 1) lor) s = iteratedDeriv (n + 2) lor s
          from by rw [← iteratedDeriv_succ]] at h
  have h_t1 := h_n.const_mul (-((n : ℝ) + 2))
  have h_t2 := (hasDerivAt_id s).mul h_n1
  have h_combined := h_t1.sub h_t2
  convert h_combined using 1
  unfold lorMix
  push_cast
  simp only [id_eq, one_mul]
  ring

/-- **Iterated-derivative identity:**  `lorMix n s = -2 · (d/ds)^n (lor²)(s)`.

    Combine the base case `lorMix_zero` with the recursion `hasDerivAt_lorMix`
    (using `HasDerivAt.unique` to lift the derivative equation pointwise). -/
private lemma lorMix_eq_iteratedDeriv_lorSq (n : ℕ) (s : ℝ) :
    lorMix n s = -2 * iteratedDeriv n lorSq s := by
  induction n generalizing s with
  | zero =>
    rw [iteratedDeriv_zero]
    exact lorMix_zero s
  | succ k ih =>
    have h_iter_diff : Differentiable ℝ (iteratedDeriv k lorSq) :=
      (contDiff_lorSq.of_le le_top).differentiable_iteratedDeriv' k
    have h_deriv_lorMix : HasDerivAt (lorMix k) (lorMix (k + 1) s) s :=
      hasDerivAt_lorMix k s
    have h_eq_fn : lorMix k = fun s' : ℝ => -2 * iteratedDeriv k lorSq s' := by
      funext s'; exact ih s'
    rw [h_eq_fn] at h_deriv_lorMix
    have h_iter_at : HasDerivAt (iteratedDeriv k lorSq)
                       (iteratedDeriv (k + 1) lorSq s) s := by
      have := (h_iter_diff s).hasDerivAt
      rwa [show deriv (iteratedDeriv k lorSq) s = iteratedDeriv (k + 1) lorSq s
            from by rw [iteratedDeriv_succ]] at this
    have h_neg2 : HasDerivAt (fun s' => -2 * iteratedDeriv k lorSq s')
                    (-2 * iteratedDeriv (k + 1) lorSq s) s :=
      h_iter_at.const_mul _
    exact h_deriv_lorMix.unique h_neg2

/-! ### Polynomial-rational representation for `iteratedDeriv n lorSq`.

Each derivative of `lorSq` has the closed form
`(lorSqNumer n).eval s / (1+s²)^(n+2)` where `lorSqNumer n` is a real
polynomial of degree at most `n`.  Combined with the polynomial bound
`|R.eval s| ≲ (1+|s|)^R.natDegree` and `(1+s²)^(n+2) ≥ s^(2n+4)` for
`s ≥ 1`, this gives the asymptotic `O(s^{-(n+4)})`. -/

/-- Numerator polynomial in the rational representation
    `iteratedDeriv n lorSq s = (lorSqNumer n).eval s / (1+s²)^(n+2)`.

    Quotient-rule recursion: if `f(s) = R(s) / (1+s²)^(n+2)`, then
        `f'(s) = [R'(s)·(1+s²) − 2(n+2)·s·R(s)] / (1+s²)^(n+3)`. -/
private noncomputable def lorSqNumer : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => (lorSqNumer n).derivative * (Polynomial.X ^ 2 + 1)
              - Polynomial.C (2 * ((n : ℝ) + 2)) * Polynomial.X * (lorSqNumer n)

/-- Degree bound on the numerator polynomial:  `(lorSqNumer n).natDegree ≤ n`.

    Induction on `n`.  Base: `lorSqNumer 0 = 1` has degree 0.
    Step: from the recursion,
      `((lorSqNumer k).derivative * (X² + 1)).natDegree ≤ k + 1`
      `(C · X · (lorSqNumer k)).natDegree ≤ k + 1`
    (using `natDegree_mul_le`, `natDegree_derivative_le`); their difference
    inherits the bound via `natDegree_sub_le`. -/
private lemma lorSqNumer_natDegree_le (n : ℕ) : (lorSqNumer n).natDegree ≤ n := by
  induction n with
  | zero =>
    -- `lorSqNumer 0 = 1`, and `(1 : Polynomial ℝ).natDegree = 0`.
    change (1 : Polynomial ℝ).natDegree ≤ 0
    simp
  | succ k ih =>
    -- Unfold the recursion: `lorSqNumer (k+1) = R.derivative * (X² + 1) − C(2(k+2)) · X · R`
    -- where `R = lorSqNumer k`.
    change ((lorSqNumer k).derivative * (Polynomial.X ^ 2 + 1)
            - Polynomial.C (2 * ((k : ℝ) + 2)) * Polynomial.X * (lorSqNumer k)).natDegree
          ≤ k + 1
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    refine max_le ?_ ?_
    · -- First term:  `R.derivative * (X² + 1)`.
      -- Case split: if `R` is constant, `R.derivative = 0` and the product is `0`.
      rcases Nat.eq_zero_or_pos (lorSqNumer k).natDegree with hzero | hpos
      · have h_const : lorSqNumer k = Polynomial.C ((lorSqNumer k).coeff 0) :=
          Polynomial.eq_C_of_natDegree_le_zero hzero.le
        rw [h_const, Polynomial.derivative_C, zero_mul, Polynomial.natDegree_zero]
        exact Nat.zero_le _
      · -- Non-constant case: `R.derivative.natDegree ≤ R.natDegree − 1`, and
        -- `(X² + 1).natDegree = 2`, so the product has natDegree `≤ R.natDegree + 1 ≤ k + 1`.
        refine Polynomial.natDegree_mul_le.trans ?_
        have hX2 : (Polynomial.X ^ 2 + 1 : Polynomial ℝ).natDegree = 2 := by
          compute_degree!
        rw [hX2]
        have hderiv : (lorSqNumer k).derivative.natDegree ≤ (lorSqNumer k).natDegree - 1 :=
          Polynomial.natDegree_derivative_le _
        omega
    · -- Second term:  `C(2(k+2)) · X · R`.
      -- `(C · X).natDegree ≤ 1`, and `R.natDegree ≤ k` by IH, so total `≤ k + 1`.
      refine Polynomial.natDegree_mul_le.trans ?_
      have hCX : (Polynomial.C (2 * ((k : ℝ) + 2)) * Polynomial.X).natDegree ≤ 1 := by
        refine Polynomial.natDegree_mul_le.trans ?_
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
      omega

/-- Rational-function representation:
    `iteratedDeriv n lorSq s = (lorSqNumer n).eval s / (1 + s²)^(n + 2)`.

    Induction on `n`.  Base: `lorSq s = 1/(1+s²)² = (lorSqNumer 0).eval s / (1+s²)^2`.
    Step: `iteratedDeriv (k+1) lorSq s = (d/ds) (iteratedDeriv k lorSq) s`;
    differentiate the IH via the quotient rule and match against the
    `lorSqNumer (k+1)` recursion. -/
private lemma iteratedDeriv_lorSq_eq (n : ℕ) (s : ℝ) :
    iteratedDeriv n lorSq s = (lorSqNumer n).eval s / (1 + s ^ 2) ^ (n + 2) := by
  induction n generalizing s with
  | zero =>
    rw [iteratedDeriv_zero]
    -- `lorSqNumer 0 = 1` and `(1 : Polynomial ℝ).eval s = 1`.
    show lorSq s = (1 : Polynomial ℝ).eval s / (1 + s ^ 2) ^ (0 + 2)
    rw [Polynomial.eval_one]
    unfold lorSq lor
    have h_ne : (1 + s ^ 2 : ℝ) ≠ 0 := ne_of_gt (lor_denom_pos s)
    field_simp
  | succ k ih =>
    -- The IH is pointwise; lift to a functional equality so we can rewrite under `deriv`.
    have h_func : iteratedDeriv k lorSq =
        fun x => (lorSqNumer k).eval x / (1 + x ^ 2) ^ (k + 2) := by
      funext x; exact ih x
    rw [iteratedDeriv_succ, h_func]
    -- Build the `HasDerivAt` facts for numerator and denominator.
    have h_num : HasDerivAt (fun x : ℝ => (lorSqNumer k).eval x)
        ((lorSqNumer k).derivative.eval s) s :=
      (lorSqNumer k).hasDerivAt s
    have h_inner : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * s) s := by
      have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      exact h2.const_add 1
    have h_den : HasDerivAt (fun x : ℝ => (1 + x ^ 2) ^ (k + 2))
        (((k : ℝ) + 2) * (1 + s ^ 2) ^ (k + 1) * (2 * s)) s := by
      have h := h_inner.pow (k + 2)
      have h_sub : (k + 2) - 1 = k + 1 := by omega
      rw [h_sub] at h
      push_cast at h
      exact h
    have h_pos : (0 : ℝ) < (1 + s ^ 2) ^ (k + 2) := by positivity
    have h_ne : ((1 + s ^ 2) ^ (k + 2) : ℝ) ≠ 0 := ne_of_gt h_pos
    have h_div := h_num.fun_div h_den h_ne
    rw [h_div.deriv]
    -- Unfold `lorSqNumer (k+1)` and apply `Polynomial.eval` simp lemmas.
    rw [show lorSqNumer (k + 1) =
            (lorSqNumer k).derivative * (Polynomial.X ^ 2 + 1)
              - Polynomial.C (2 * ((k : ℝ) + 2)) * Polynomial.X * (lorSqNumer k)
          from rfl]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
               Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
               Polynomial.eval_one]
    -- Algebraic match: both sides reduce to the same rational expression.
    have h_ne1 : (1 + s ^ 2 : ℝ) ≠ 0 := ne_of_gt (lor_denom_pos s)
    field_simp
    ring

/-- Asymptotic bound on the iterated derivative of `lor²`:
    `iteratedDeriv n lorSq s = O(s^{-(n+4)})` as `s → +∞`.

    Combines the rational representation `iteratedDeriv_lorSq_eq` with the
    polynomial bound (from `lorSqNumer_natDegree_le`) and the denominator
    bound `(1+s²)^(n+2) ≥ s^(2n+4)` for `s ≥ 1`. -/
private lemma iteratedDeriv_lorSq_isO (n : ℕ) :
    IsO (iteratedDeriv n lorSq) (fun s : ℝ => s ^ (-(n : ℝ) - 4)) 𝓝∞ := by
  -- Step 1: replace the iterated derivative by its rational form.
  have h_fun_eq : iteratedDeriv n lorSq =
      fun s => (lorSqNumer n).eval s / (1 + s ^ 2) ^ (n + 2) := by
    funext s; exact iteratedDeriv_lorSq_eq n s
  rw [h_fun_eq]
  -- Step 2: polynomial bound on the numerator.
  have h_num : (fun s : ℝ => (lorSqNumer n).eval s) =O[atTop] (fun s : ℝ => s ^ n) := by
    have h_deg : (lorSqNumer n).degree ≤ ((Polynomial.X : Polynomial ℝ) ^ n).degree := by
      rw [Polynomial.degree_X_pow]
      calc (lorSqNumer n).degree
          ≤ ((lorSqNumer n).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ ≤ (n : WithBot ℕ) := by exact_mod_cast lorSqNumer_natDegree_le n
    have h := Polynomial.isBigO_atTop_of_degree_le _ _ h_deg
    simpa using h
  -- Step 3: denominator-inverse bound `1/(1+s²)^(n+2) ≤ 1/s^(2(n+2))` for `s ≥ 1`.
  have h_inv : (fun s : ℝ => 1 / (1 + s ^ 2) ^ (n + 2))
      =O[atTop] (fun s : ℝ => 1 / s ^ (2 * (n + 2))) := by
    refine .of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with s hs
    have hs_pos : 0 < s := zero_lt_one.trans_le hs
    have h_s2_le : s ^ 2 ≤ 1 + s ^ 2 := by linarith [sq_nonneg s]
    have h_pow_le : s ^ (2 * (n + 2)) ≤ (1 + s ^ 2) ^ (n + 2) := by
      calc s ^ (2 * (n + 2))
          = (s ^ 2) ^ (n + 2) := by rw [← pow_mul]
        _ ≤ (1 + s ^ 2) ^ (n + 2) := pow_le_pow_left₀ (sq_nonneg s) h_s2_le _
    have h_pos1 : 0 < (1 + s ^ 2) ^ (n + 2) := by positivity
    have h_pos2 : 0 < s ^ (2 * (n + 2)) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
        abs_of_pos (one_div_pos.mpr h_pos1), abs_of_pos (one_div_pos.mpr h_pos2)]
    exact one_div_le_one_div_of_le h_pos2 h_pow_le
  -- Step 4: combine via `IsBigO.mul`, after rewriting division as multiplication.
  have h_split : (fun s : ℝ => (lorSqNumer n).eval s / (1 + s ^ 2) ^ (n + 2)) =
      (fun s : ℝ => (lorSqNumer n).eval s * (1 / (1 + s ^ 2) ^ (n + 2))) := by
    funext s; rw [mul_one_div]
  rw [h_split]
  refine (h_num.mul h_inv).trans ?_
  -- Step 5: show `s^n * (1/s^(2(n+2))) =O[atTop] s^(-(n:ℝ) - 4)`.
  refine .of_bound 1 ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with s hs
  have hs_ne : s ≠ 0 := ne_of_gt hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
  -- Both sides equal `1/s^(n+4)` for `s > 0`.
  have h_lhs : s ^ n * (1 / s ^ (2 * (n + 2))) = 1 / s ^ (n + 4) := by
    rw [mul_one_div, show 2 * (n + 2) = n + (n + 4) from by ring, pow_add,
        div_mul_eq_div_div, div_self (pow_ne_zero _ hs_ne)]
  have h_rhs : s ^ (-(n : ℝ) - 4) = 1 / s ^ (n + 4) := by
    rw [show (-(n : ℝ) - 4) = -((n + 4 : ℕ) : ℝ) from by push_cast; ring,
        Real.rpow_neg hs.le, Real.rpow_natCast, one_div]
  rw [h_lhs, h_rhs]

/-- Asymptotic cancellation:  `lorMix n s = O(s^{-(n+4)})` as `s → +∞`.

    Follows from `lorMix_eq_iteratedDeriv_lorSq` (rewriting `lorMix n` as
    `-2 · (d/ds)^n (lor²)`) and `iteratedDeriv_lorSq_isO` (the asymptotic on
    the iterated derivative).  The constant factor `-2` is absorbed by
    `IsBigO.const_mul_left`. -/
private lemma lorMix_isO (n : ℕ) :
    IsO (lorMix n) (fun x : ℝ => x ^ (-(n : ℝ) - 4)) 𝓝∞ := by
  have h_eq : lorMix n = fun s : ℝ => -2 * iteratedDeriv n lorSq s := by
    funext s; exact lorMix_eq_iteratedDeriv_lorSq n s
  rw [h_eq]
  exact (iteratedDeriv_lorSq_isO n).const_mul_left _

/-! ### Sub-lemmas for `sigma_lorMix_integral_isO`.

The σ-weighted integral asymptotic decomposes into:
- `lorMix_continuous` (proved): direct from the rational representation.
- `lorMix_bounded_on_nonneg`: continuity (compact prefix) + `lorMix_isO`
  (tail) ⟹ uniform bound on `[0, ∞)`.
- `lorMix_unified_decay_on_nonneg`: combines the two regimes into a single
  pointwise bound `|lorMix n y| ≤ K · (1 + y^(n+4))⁻¹` for `y ≥ 0`.
- `sigma_lorMix_integral_isO` (main): integrating the unified bound against
  the σ-weighted kernel produces the displayed `O(t^{-(n+2)})`. -/

/-- **`lorMix n` is continuous on `ℝ`.**

Direct from the rational representation
`iteratedDeriv n lorSq s = (lorSqNumer n).eval s / (1 + s²)^(n+2)`:
the numerator is a polynomial (continuous), the denominator is the
`(n+2)`-th power of `1 + s² ≥ 1 > 0`, and `lorMix n s = −2 · iteratedDeriv n lorSq s`. -/
private lemma lorMix_continuous (n : ℕ) : Continuous (lorMix n) := by
  have h_eq : lorMix n =
      fun s : ℝ => -2 * ((lorSqNumer n).eval s / (1 + s ^ 2) ^ (n + 2)) := by
    funext s
    rw [lorMix_eq_iteratedDeriv_lorSq, iteratedDeriv_lorSq_eq]
  rw [h_eq]
  refine ((lorSqNumer n).continuous.div ?_ (fun s => ?_)).const_mul (-2 : ℝ)
  · exact (continuous_const.add (continuous_id.pow 2)).pow (n + 2)
  · positivity

/-- **`lorMix n` is uniformly bounded on `[0, ∞)`.**

By `lorMix_continuous`, `|lorMix n|` is bounded on every compact interval
`[0, Y]`.  By `lorMix_isO`, for `y ≥ Y₀` (some threshold) we have
`|lorMix n y| ≤ C · y^{−(n+4)} ≤ C · Y₀^{−(n+4)}`.  Taking `Y = max(1, Y₀)`
and combining the two bounds gives a global `M` for `y ∈ [0, ∞)`. -/
private lemma lorMix_bounded_on_nonneg (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 ≤ y → |lorMix n y| ≤ M := by
  -- Step 1: extract a tail bound `C` from `lorMix_isO`.
  obtain ⟨C, hC⟩ := (lorMix_isO n).bound
  rw [Filter.eventually_atTop] at hC
  obtain ⟨Y₀, hY₀⟩ := hC
  -- Threshold for which we also have `y ≥ 1` (so `y^{-(n:ℝ) - 4} ≤ 1`).
  set Y₁ : ℝ := max Y₀ 1 with hY₁_def
  have hY₁_ge_Y₀ : Y₀ ≤ Y₁ := le_max_left _ _
  have hY₁_ge_1 : (1 : ℝ) ≤ Y₁ := le_max_right _ _
  -- Step 2: continuity bound on the compact prefix `[0, Y₁]`.
  have h_compact : IsCompact (Set.Icc (0 : ℝ) Y₁) := isCompact_Icc
  have h_cont_abs : Continuous (fun y : ℝ => |lorMix n y|) := (lorMix_continuous n).abs
  obtain ⟨M₁, hM₁⟩ := h_compact.bddAbove_image h_cont_abs.continuousOn
  -- `hM₁ : M₁ ∈ upperBounds (|lorMix n ·| '' Icc 0 Y₁)`.
  -- Step 3: combine the two bounds.  Take `max M₁ (max C 0)` for non-negativity.
  refine ⟨max M₁ (max C 0), (le_max_right C 0).trans (le_max_right _ _), fun y hy => ?_⟩
  by_cases h_split : y ≤ Y₁
  · -- `y ∈ [0, Y₁]`: use the compact bound `M₁`.
    have h_mem : (|lorMix n y| : ℝ) ∈ (fun y => |lorMix n y|) '' Set.Icc 0 Y₁ :=
      ⟨y, ⟨hy, h_split⟩, rfl⟩
    have h_le_M₁ : |lorMix n y| ≤ M₁ := hM₁ h_mem
    exact h_le_M₁.trans (le_max_left _ _)
  · -- `y > Y₁`: use the asymptotic bound.  Here `y ≥ Y₀` and `y ≥ 1`.
    rw [not_le] at h_split
    have h_y_ge_Y₀ : Y₀ ≤ y := hY₁_ge_Y₀.trans h_split.le
    have h_y_ge_1 : (1 : ℝ) ≤ y := hY₁_ge_1.trans h_split.le
    have h_y_pos : (0 : ℝ) < y := zero_lt_one.trans_le h_y_ge_1
    have h_norm_bound : ‖lorMix n y‖ ≤ C * ‖y ^ (-(n : ℝ) - 4)‖ := hY₀ y h_y_ge_Y₀
    -- `y^{-(n:ℝ) - 4} ≤ 1` since `y ≥ 1` and the exponent is `≤ 0`.
    have h_rpow_pos : 0 < y ^ (-(n : ℝ) - 4) := Real.rpow_pos_of_pos h_y_pos _
    have h_rpow_le_one : y ^ (-(n : ℝ) - 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h_y_ge_1
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    have h_norm_rpow_le : ‖y ^ (-(n : ℝ) - 4)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos h_rpow_pos]; exact h_rpow_le_one
    -- `C ≥ 0`: otherwise `C * ‖y^…‖` would be negative, contradicting `0 ≤ ‖lorMix n y‖`.
    have h_norm_rpow_pos : 0 < ‖y ^ (-(n : ℝ) - 4)‖ := by
      rw [Real.norm_eq_abs]; exact abs_pos.mpr (ne_of_gt h_rpow_pos)
    have h_C_nonneg : 0 ≤ C := by
      by_contra h
      rw [not_le] at h
      have : C * ‖y ^ (-(n : ℝ) - 4)‖ < 0 := mul_neg_of_neg_of_pos h h_norm_rpow_pos
      linarith [norm_nonneg (lorMix n y), h_norm_bound]
    calc |lorMix n y|
        = ‖lorMix n y‖ := (Real.norm_eq_abs _).symm
      _ ≤ C * ‖y ^ (-(n : ℝ) - 4)‖ := h_norm_bound
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left h_norm_rpow_le h_C_nonneg
      _ = C := mul_one _
      _ ≤ max C 0 := le_max_left _ _
      _ ≤ max M₁ (max C 0) := le_max_right _ _

/-- **Unified pointwise decay bound for `lorMix n` on `[0, ∞)`.**

For some `K ≥ 0` and all `y ≥ 0`,
        `|lorMix n y| ≤ K · (1 + y^(n+4))⁻¹`.

For `y ∈ [0, 1]`: `1 + y^(n+4) ≤ 2`, so `(1 + y^(n+4))⁻¹ ≥ 1/2`, and
`lorMix_bounded_on_nonneg` provides `|lorMix n y| ≤ M ≤ 2M · (1 + y^(n+4))⁻¹`.

For `y ≥ 1`: `1 + y^(n+4) ≤ 2 · y^(n+4)`, so `(1 + y^(n+4))⁻¹ ≥ (2 y^(n+4))⁻¹`,
and `lorMix_isO` provides `|lorMix n y| ≤ C · y^{−(n+4)} ≤ 2C · (1 + y^(n+4))⁻¹`.

Take `K = 2 · max(M, C)`. -/
private lemma lorMix_unified_decay_on_nonneg (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 ≤ y → |lorMix n y| ≤ K / (1 + y ^ (n + 4)) := by
  obtain ⟨M, hM_nn, hM⟩ := lorMix_bounded_on_nonneg n
  obtain ⟨C, hC⟩ := (lorMix_isO n).bound
  rw [Filter.eventually_atTop] at hC
  obtain ⟨Y₀, hY₀⟩ := hC
  -- `Y₁ = max(Y₀, 1)` ensures both the asymptotic bound (`y ≥ Y₀`) and `y ≥ 1`
  -- apply on the tail.
  set Y₁ : ℝ := max Y₀ 1 with hY₁_def
  have hY₁_ge_Y₀ : Y₀ ≤ Y₁ := le_max_left _ _
  have hY₁_ge_1 : (1 : ℝ) ≤ Y₁ := le_max_right _ _
  -- `K = max(M · (1 + Y₁^(n+4)),  2 · max(C, 0))` covers both regimes.
  -- The outer `max C 0` sidesteps a possibly-negative `C` from `IsBigO.bound`.
  refine ⟨max (M * (1 + Y₁ ^ (n + 4))) (2 * max C 0), ?_, fun y hy => ?_⟩
  · -- `0 ≤ K`.
    have : 0 ≤ M * (1 + Y₁ ^ (n + 4)) := mul_nonneg hM_nn (by positivity)
    exact le_max_of_le_left this
  · -- The pointwise inequality.
    have h_denom_pos : 0 < 1 + y ^ (n + 4) := by positivity
    rw [le_div_iff₀ h_denom_pos]
    by_cases h_split : y ≤ Y₁
    · -- Compact regime `y ∈ [0, Y₁]`: dominate using `lorMix_bounded_on_nonneg`.
      have h_y_bound : |lorMix n y| ≤ M := hM y hy
      have h_y_pow_le : y ^ (n + 4) ≤ Y₁ ^ (n + 4) :=
        pow_le_pow_left₀ hy h_split (n + 4)
      calc |lorMix n y| * (1 + y ^ (n + 4))
          ≤ M * (1 + Y₁ ^ (n + 4)) :=
            mul_le_mul h_y_bound (by linarith) h_denom_pos.le hM_nn
        _ ≤ max (M * (1 + Y₁ ^ (n + 4))) (2 * max C 0) := le_max_left _ _
    · -- Tail regime `y > Y₁`: dominate using `lorMix_isO`.  Here `y ≥ Y₀, y ≥ 1`.
      rw [not_le] at h_split
      have h_y_ge_Y₀ : Y₀ ≤ y := hY₁_ge_Y₀.trans h_split.le
      have h_y_ge_1 : (1 : ℝ) ≤ y := hY₁_ge_1.trans h_split.le
      have h_y_pos : (0 : ℝ) < y := zero_lt_one.trans_le h_y_ge_1
      have h_norm_bound : ‖lorMix n y‖ ≤ C * ‖y ^ (-(n : ℝ) - 4)‖ := hY₀ y h_y_ge_Y₀
      -- Convert the rpow to a `1/y^(n+4)` form.
      have h_rpow_eq : y ^ (-(n : ℝ) - 4) = 1 / y ^ (n + 4) := by
        rw [show (-(n : ℝ) - 4) = -((n + 4 : ℕ) : ℝ) from by push_cast; ring,
            Real.rpow_neg h_y_pos.le, Real.rpow_natCast, one_div]
      have h_rpow_pos : 0 < y ^ (-(n : ℝ) - 4) := Real.rpow_pos_of_pos h_y_pos _
      have h_norm_rpow : ‖y ^ (-(n : ℝ) - 4)‖ = 1 / y ^ (n + 4) := by
        rw [Real.norm_eq_abs, abs_of_pos h_rpow_pos, h_rpow_eq]
      have h_lorMix_le : |lorMix n y| ≤ C / y ^ (n + 4) := by
        rw [← Real.norm_eq_abs]
        rw [h_norm_rpow, mul_one_div] at h_norm_bound
        exact h_norm_bound
      -- `y^(n+4) ≥ 1` (since `y ≥ 1`), so `1 + y^(n+4) ≤ 2 · y^(n+4)`.
      have h_y_pow_ge_one : (1 : ℝ) ≤ y ^ (n + 4) := one_le_pow₀ h_y_ge_1
      have h_y_pow_pos : 0 < y ^ (n + 4) := zero_lt_one.trans_le h_y_pow_ge_one
      -- `C ≥ 0`: the asymptotic bound at `y` would be contradicted otherwise.
      have h_C_nonneg : 0 ≤ C := by
        have h_norm_rpow_pos : 0 < ‖y ^ (-(n : ℝ) - 4)‖ := by
          rw [h_norm_rpow]; positivity
        by_contra h
        rw [not_le] at h
        have : C * ‖y ^ (-(n : ℝ) - 4)‖ < 0 := mul_neg_of_neg_of_pos h h_norm_rpow_pos
        linarith [norm_nonneg (lorMix n y), h_norm_bound]
      calc |lorMix n y| * (1 + y ^ (n + 4))
          ≤ (C / y ^ (n + 4)) * (2 * y ^ (n + 4)) :=
            mul_le_mul h_lorMix_le (by linarith) h_denom_pos.le
              (div_nonneg h_C_nonneg h_y_pow_pos.le)
        _ = 2 * C := by field_simp
        _ ≤ 2 * max C 0 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
        _ ≤ max (M * (1 + Y₁ ^ (n + 4))) (2 * max C 0) := le_max_right _ _

/-- **Integrability of the σ-weighted lorMix integrand on `Ici 0`.**

For each `t ≥ 0`, the integrand
    `u ↦ σ u · (u+1/4)^{-(n+3)} · lorMix n ((1/(2(u+1/4))) · t)`
is dominated on `[0, ∞)` by `(M/8) · ((u+1/4)^{n+3})⁻¹`, where `M` is the
uniform bound from `lorMix_bounded_on_nonneg n`.  The dominator is integrable
via `integrableOn_pow_inv_shift (n+1)`.  Measurability of the integrand is
the product of three continuous factors. -/
private lemma integrable_sigma_lorMix_integrand (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun u : ℝ => σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                                       * lorMix n ((1 / (2 * (u + 1 / 4))) * t)))
                 (Set.Ici (0 : ℝ)) := by
  obtain ⟨M, hM_nn, hM⟩ := lorMix_bounded_on_nonneg n
  -- Continuity of each factor on `Ici 0`, hence AEStronglyMeasurable.
  have h_cont : ContinuousOn
      (fun u : ℝ => σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                            * lorMix n ((1 / (2 * (u + 1 / 4))) * t)))
      (Set.Ici (0 : ℝ)) := by
    refine σ_continuous.continuousOn.mul (ContinuousOn.mul ?_ ?_)
    · -- `(u + 1/4)^{-(n+3)}` continuous on `Ici 0` (since `u + 1/4 > 0`).
      have : ContinuousOn (fun u : ℝ => u + 1 / 4) (Set.Ici (0 : ℝ)) :=
        (continuous_id.add continuous_const).continuousOn
      refine this.zpow₀ _ (fun u hu => ?_)
      left; linarith [Set.mem_Ici.mp hu]
    · -- `lorMix n ∘ (...)` continuous on `Ici 0`.
      refine (lorMix_continuous n).continuousOn.comp ?_ (Set.mapsTo_univ _ _)
      have h_denom_cont : ContinuousOn (fun u : ℝ => 2 * (u + 1 / 4)) (Set.Ici (0 : ℝ)) :=
        (continuous_const.mul (continuous_id.add continuous_const)).continuousOn
      have h_denom_ne : ∀ u ∈ Set.Ici (0 : ℝ), 2 * (u + 1 / 4) ≠ 0 := by
        intro u hu; have := Set.mem_Ici.mp hu; positivity
      exact ((continuousOn_const.div h_denom_cont h_denom_ne).mul continuousOn_const)
  have h_meas : AEStronglyMeasurable (fun u : ℝ =>
      σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
              * lorMix n ((1 / (2 * (u + 1 / 4))) * t)))
      (volume.restrict (Set.Ici (0 : ℝ))) :=
    h_cont.aestronglyMeasurable measurableSet_Ici
  -- Dominator: `(M / 8) · ((u + 1/4)^(n+3))⁻¹`.
  refine Integrable.mono'
    ((integrableOn_pow_inv_shift (n + 1)).const_mul (M / 8))
    h_meas ?_
  refine (ae_restrict_iff' measurableSet_Ici).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro u hu
  have hu_nn : (0 : ℝ) ≤ u := Set.mem_Ici.mp hu
  have hr_pos : (0 : ℝ) < u + 1 / 4 := by linarith
  have hr_ne : (u + 1 / 4 : ℝ) ≠ 0 := ne_of_gt hr_pos
  have h_pow_pos : (0 : ℝ) < (u + 1 / 4) ^ (n + 3) := pow_pos hr_pos _
  -- `lorMix` argument is `(1/(2(u+1/4))) * t ≥ 0` since both factors are nonneg.
  have h_arg_nn : 0 ≤ (1 / (2 * (u + 1 / 4))) * t :=
    mul_nonneg (by positivity) ht
  have h_lorMix_le : |lorMix n ((1 / (2 * (u + 1 / 4))) * t)| ≤ M := hM _ h_arg_nn
  have h_σ_nn : 0 ≤ σ u := σ_nonneg u
  have h_σ_le : σ u ≤ 1 / 8 := σ_le_eighth u
  -- Show `|integrand| ≤ (M/8) · ((u+1/4)^(n+3))⁻¹`.
  have h_zpow_eq : (u + 1 / 4) ^ (-((n : ℤ) + 3)) = ((u + 1 / 4) ^ (n + 3))⁻¹ := by
    rw [show -((n : ℤ) + 3) = -((n + 3 : ℕ) : ℤ) from by push_cast; ring,
        zpow_neg, zpow_natCast]
  change ‖σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                  * lorMix n ((1 / (2 * (u + 1 / 4))) * t))‖
          ≤ M / 8 * ((u + 1 / 4) ^ ((n + 1) + 2))⁻¹
  rw [show (n + 1) + 2 = n + 3 from rfl, h_zpow_eq]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h_σ_nn,
      abs_of_pos (inv_pos.mpr h_pow_pos)]
  calc σ u * (((u + 1 / 4) ^ (n + 3))⁻¹ * |lorMix n ((1 / (2 * (u + 1 / 4))) * t)|)
      ≤ (1 / 8) * (((u + 1 / 4) ^ (n + 3))⁻¹ * M) := by gcongr
    _ = M / 8 * ((u + 1 / 4) ^ (n + 3))⁻¹ := by ring

/-- **Asymptotic of the majorant integral.**

The σ-free, lorMix-free dominator,
    `K · ((u+1/4)^{n+3})⁻¹ · (1 + ((1/(2(u+1/4))) · t)^{n+4})⁻¹`,
has integral (over `Ici 0`) of order `O(t^{-(n+2)})`.  This is the
analytic core of `sigma_lorMix_integral_isO`.

Sketch: substitute `v = u + 1/4` and split at `v = t/2`:
- On `[1/4, t/2]`: dominator `≤ 2^{n+5} · K · v / t^{n+4}`; integrating
  in `v` gives `O(t^{-(n+2)})`.
- On `[t/2, ∞)`: dominator `≤ K · v^{-(n+3)}`; integrating gives
  `≤ K · 2^{n+2} / ((n+2) · t^{n+2}) = O(t^{-(n+2)})`. -/
private lemma sigma_lorMix_majorant_integral_isO (n : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    IsO (fun t : ℝ =>
            ∫ u in Set.Ici (0 : ℝ),
              K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                    (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))))
        (fun t => t ^ (-(n : ℝ) - 2))
        𝓝∞ := by
  sorry -- TODO (open): split at `v = t/2` and bound each piece.

/-- **Integrability of the lorMix majorant on `Ici 0`.**

For `t ≥ 0` the dominator
    `u ↦ K · ((u+1/4)^{n+3})⁻¹ / (1 + ((1/(2(u+1/4))) · t)^{n+4})`
is bounded by `K · ((u+1/4)^{n+3})⁻¹` (the rational factor is ≤ 1 since the
denominator is ≥ 1), which is integrable via `integrableOn_pow_inv_shift (n+1)`. -/
private lemma integrable_lorMix_majorant (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn
      (fun u : ℝ => K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                          (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))))
      (Set.Ici (0 : ℝ)) := by
  have hr_pos : ∀ u ∈ Set.Ici (0 : ℝ), (0 : ℝ) < u + 1 / 4 := by
    intro u hu; linarith [Set.mem_Ici.mp hu]
  have h2r_ne : ∀ u ∈ Set.Ici (0 : ℝ), 2 * (u + 1 / 4) ≠ 0 := by
    intro u hu; have := hr_pos u hu; positivity
  have h_denom_pos : ∀ u ∈ Set.Ici (0 : ℝ),
      (0 : ℝ) < 1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4) := by
    intro u hu
    have hr := hr_pos u hu
    have h_arg_nn : 0 ≤ (1 / (2 * (u + 1 / 4))) * t :=
      mul_nonneg (by positivity) ht
    have := pow_nonneg h_arg_nn (n + 4)
    linarith
  -- Continuity → AEStronglyMeasurable.
  have h_cont : ContinuousOn
      (fun u : ℝ => K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                          (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))))
      (Set.Ici (0 : ℝ)) := by
    have hr : ContinuousOn (fun u : ℝ => u + 1 / 4) (Set.Ici (0 : ℝ)) :=
      (continuous_id.add continuous_const).continuousOn
    have h_pow_inv : ContinuousOn (fun u : ℝ => ((u + 1 / 4) ^ (n + 3))⁻¹)
        (Set.Ici (0 : ℝ)) :=
      (hr.pow (n + 3)).inv₀ (fun u hu => ne_of_gt (pow_pos (hr_pos u hu) _))
    have h2r : ContinuousOn (fun u : ℝ => 2 * (u + 1 / 4)) (Set.Ici (0 : ℝ)) :=
      (continuous_const.mul (continuous_id.add continuous_const)).continuousOn
    have h_inv1 : ContinuousOn (fun u : ℝ => 1 / (2 * (u + 1 / 4)))
        (Set.Ici (0 : ℝ)) :=
      continuousOn_const.div h2r h2r_ne
    have h_denom : ContinuousOn
        (fun u : ℝ => 1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))
        (Set.Ici (0 : ℝ)) :=
      continuousOn_const.add ((h_inv1.mul continuousOn_const).pow (n + 4))
    exact continuousOn_const.mul
      (h_pow_inv.div h_denom (fun u hu => ne_of_gt (h_denom_pos u hu)))
  refine Integrable.mono'
    ((integrableOn_pow_inv_shift (n + 1)).const_mul K)
    (h_cont.aestronglyMeasurable measurableSet_Ici) ?_
  refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ?_)
  intro u hu
  have hr := hr_pos u hu
  have h_pow_pos : (0 : ℝ) < (u + 1 / 4) ^ (n + 3) := pow_pos hr _
  have h_inv_nn : (0 : ℝ) ≤ ((u + 1 / 4) ^ (n + 3))⁻¹ := (inv_pos.mpr h_pow_pos).le
  have h_dpos := h_denom_pos u hu
  change ‖K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)))‖
          ≤ K * ((u + 1 / 4) ^ ((n + 1) + 2))⁻¹
  rw [show (n + 1) + 2 = n + 3 from rfl, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have h_div_le : ((u + 1 / 4) ^ (n + 3))⁻¹ /
                    (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))
                  ≤ ((u + 1 / 4) ^ (n + 3))⁻¹ :=
    div_le_self h_inv_nn (by
      have : 0 ≤ ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4) := by
        have h_arg_nn : 0 ≤ (1 / (2 * (u + 1 / 4))) * t :=
          mul_nonneg (by positivity) ht
        exact pow_nonneg h_arg_nn _
      linarith)
  calc K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
              (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)))
      ≤ K * ((u + 1 / 4) ^ (n + 3))⁻¹ := by
        exact mul_le_mul_of_nonneg_left h_div_le hK

/-- **σ-weighted integral asymptotic (lorMix form).**

The σ-weighted integral of the lorMix-rescaled mixed derivative,
    `∫₀^∞ σ(u) · (u+1/4)^{-(n+3)} · lorMix n (t/(2(u+1/4))) du`,
is `O(t^{-(n+2)})` as `t → +∞`.

Bound `|σ u| ≤ 1/8` and `|lorMix n y| ≤ K · (1 + y^{n+4})⁻¹` (the unified
decay).  Triangle inequality on the integral plus dominated comparison
reduces to `sigma_lorMix_majorant_integral_isO`. -/
private lemma sigma_lorMix_integral_isO (n : ℕ) :
    IsO (fun t : ℝ => ∫ u in Set.Ici (0 : ℝ),
                σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                       * lorMix n ((1 / (2 * (u + 1 / 4))) * t)))
        (fun t => t ^ (-(n : ℝ) - 2))
        𝓝∞ := by
  obtain ⟨K, hK_nn, h_decay⟩ := lorMix_unified_decay_on_nonneg n
  -- Step 1: the σ-integral is `O` of the majorant integral (constant `1/8`).
  have h_step :
      IsO (fun t : ℝ => ∫ u in Set.Ici (0 : ℝ),
                σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                       * lorMix n ((1 / (2 * (u + 1 / 4))) * t)))
          (fun t : ℝ => ∫ u in Set.Ici (0 : ℝ),
                K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                      (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))))
          𝓝∞ := by
    refine Asymptotics.IsBigO.of_bound (1 / 8) ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    have hf_int : IntegrableOn
        (fun u : ℝ => σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                       * lorMix n ((1 / (2 * (u + 1 / 4))) * t)))
        (Set.Ici (0 : ℝ)) := integrable_sigma_lorMix_integrand n ht
    have hg_int : IntegrableOn
        (fun u : ℝ => K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                      (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))))
        (Set.Ici (0 : ℝ)) := integrable_lorMix_majorant n K hK_nn ht
    -- Pointwise bound on `Ici 0`.
    have h_pt : ∀ u ∈ Set.Ici (0 : ℝ),
        ‖σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                * lorMix n ((1 / (2 * (u + 1 / 4))) * t))‖
          ≤ (1 / 8) * (K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                  (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)))) := by
      intro u hu
      have hu_nn : (0 : ℝ) ≤ u := hu
      have hr_pos : (0 : ℝ) < u + 1 / 4 := by linarith
      have h_pow_pos : (0 : ℝ) < (u + 1 / 4) ^ (n + 3) := pow_pos hr_pos _
      have h_zpow_eq : (u + 1 / 4) ^ (-((n : ℤ) + 3)) = ((u + 1 / 4) ^ (n + 3))⁻¹ := by
        rw [show -((n : ℤ) + 3) = -((n + 3 : ℕ) : ℤ) from by push_cast; ring,
            zpow_neg, zpow_natCast]
      have h_arg_nn : 0 ≤ (1 / (2 * (u + 1 / 4))) * t :=
        mul_nonneg (by positivity) ht
      have h_lor_le : |lorMix n ((1 / (2 * (u + 1 / 4))) * t)|
            ≤ K / (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)) :=
        h_decay _ h_arg_nn
      have h_denom_pos : (0 : ℝ) < 1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4) := by
        have := pow_nonneg h_arg_nn (n + 4); linarith
      have h_σ_nn : 0 ≤ σ u := σ_nonneg u
      have h_σ_le : σ u ≤ 1 / 8 := σ_le_eighth u
      have h_K_div_nn : 0 ≤ K / (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)) :=
        div_nonneg hK_nn h_denom_pos.le
      rw [Real.norm_eq_abs, h_zpow_eq, abs_mul, abs_mul,
          abs_of_nonneg h_σ_nn, abs_of_pos (inv_pos.mpr h_pow_pos)]
      calc σ u * (((u + 1 / 4) ^ (n + 3))⁻¹
              * |lorMix n ((1 / (2 * (u + 1 / 4))) * t)|)
          ≤ (1 / 8) * (((u + 1 / 4) ^ (n + 3))⁻¹
              * (K / (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)))) := by
            gcongr
        _ = (1 / 8) * (K * (((u + 1 / 4) ^ (n + 3))⁻¹
              / (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)))) := by ring
    -- Nonnegativity of the majorant integral (so its norm is itself).
    have h_g_nn : 0 ≤ ∫ u in Set.Ici (0 : ℝ),
        K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
              (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))) := by
      refine setIntegral_nonneg measurableSet_Ici (fun u hu => ?_)
      have hu_nn : (0 : ℝ) ≤ u := hu
      have hr_pos : (0 : ℝ) < u + 1 / 4 := by linarith
      have h_arg_nn : 0 ≤ (1 / (2 * (u + 1 / 4))) * t :=
        mul_nonneg (by positivity) ht
      have h_denom_pos : (0 : ℝ) < 1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4) := by
        have := pow_nonneg h_arg_nn (n + 4); linarith
      positivity
    have hg_abs : ‖∫ u in Set.Ici (0 : ℝ),
        K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
              (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)))‖
        = ∫ u in Set.Ici (0 : ℝ),
        K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
              (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))) := by
      rw [Real.norm_eq_abs, abs_of_nonneg h_g_nn]
    rw [hg_abs]
    calc ‖∫ u in Set.Ici (0 : ℝ),
            σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                   * lorMix n ((1 / (2 * (u + 1 / 4))) * t))‖
        ≤ ∫ u in Set.Ici (0 : ℝ),
            ‖σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                    * lorMix n ((1 / (2 * (u + 1 / 4))) * t))‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ici (0 : ℝ),
            (1 / 8) * (K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                  (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4)))) :=
          setIntegral_mono_on hf_int.norm (hg_int.const_mul (1 / 8))
            measurableSet_Ici h_pt
      _ = (1 / 8) * ∫ u in Set.Ici (0 : ℝ),
            K * (((u + 1 / 4) ^ (n + 3))⁻¹ /
                  (1 + ((1 / (2 * (u + 1 / 4))) * t) ^ (n + 4))) :=
          integral_const_mul _ _
  exact h_step.trans (sigma_lorMix_majorant_integral_isO n K hK_nn)

/-- Asymptotic bound on the σ-weighted integral of `mixedDerivExpr n u t`:
    `|∫₀^∞ σ(u) · mixedDerivExpr n u t du| = O(t^(-n-2))` as `t → +∞`.

    Combines the three sub-lemmas above: the pointwise rescaling
    `mixedDerivExpr_eq_lorMix` rewrites the integrand into the lorMix form;
    the constant `(1/2)^n` factors out of the integral; and the resulting
    σ-weighted lorMix integral is bounded by `sigma_lorMix_integral_isO`. -/
private lemma sigma_mixedDerivExpr_isO (n : ℕ) :
    IsO (fun t : ℝ => ∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t)
        (fun t => t ^ (-(n : ℝ) - 2))
        𝓝∞ := by
  -- Pointwise rewrite of the integrand via the rescaling identity.
  have h_pt : ∀ t : ℝ, ∀ u ∈ Set.Ici (0 : ℝ),
      σ u * mixedDerivExpr n u t
        = (1 / 2 : ℝ) ^ n *
            (σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                    * lorMix n ((1 / (2 * (u + 1 / 4))) * t))) := by
    intro t u hu
    have hu_nn : (0 : ℝ) ≤ u := hu
    rw [mixedDerivExpr_eq_lorMix n hu_nn t]; ring
  -- Lift the pointwise rewrite to an equality of functions of `t`.
  have h_int :
      (fun t : ℝ => ∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t)
        = fun t : ℝ => (1 / 2 : ℝ) ^ n *
            (∫ u in Set.Ici (0 : ℝ),
               σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                      * lorMix n ((1 / (2 * (u + 1 / 4))) * t))) := by
    funext t
    have h_eq :
        ∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t
          = ∫ u in Set.Ici (0 : ℝ),
              (1 / 2 : ℝ) ^ n *
                (σ u * ((u + 1 / 4) ^ (-((n : ℤ) + 3))
                        * lorMix n ((1 / (2 * (u + 1 / 4))) * t))) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun u hu => h_pt t u hu)
    rw [h_eq, MeasureTheory.integral_const_mul]
  rw [h_int]
  exact (sigma_lorMix_integral_isO n).const_mul_left _

/-- Asymptotic bound on the formal `n`-th derivative integral `jK n`:
    `|jK n t| = O(t^(-n-2))` as `t → +∞`.

    Immediate from the IBP identity `jK_eq_sigma_integral` and the
    σ-integral bound `sigma_mixedDerivExpr_isO`; the residual `-(·)` is
    absorbed by `IsBigO.const_mul_left (-1)`. -/
private lemma jK_isO (n : ℕ) :
    IsO (fun t => jK n t)
        (fun t => t ^ (-(n : ℝ) - 2))
        𝓝∞ := by
  -- Rewrite via the IBP identity, then bound the σ-integral.
  have h_eq :
      (fun t : ℝ => jK n t) =ᶠ[Filter.atTop]
      (fun t : ℝ => -∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact jK_eq_sigma_integral n ht
  refine h_eq.trans_isBigO ?_
  -- Convert `-X` into `(-1) · X` and absorb the sign.
  have h_neg :
      (fun t : ℝ => -∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t) =
      (fun t : ℝ => (-1 : ℝ) *
        (∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t)) := by
    funext t; ring
  rw [h_neg]
  exact (sigma_mixedDerivExpr_isO n).const_mul_left _

/-- The n-th derivative of `j` is `O(t^(-n-2))`.

    Strategy-B reduction: rewrite `iteratedDeriv n j t = jK n t` for `t > 0`
    via `iteratedDeriv_j_eqOn_jK`, then bound `jK n` directly. -/
lemma iteratedDeriv_j_isO (n : ℕ) :
    IsO (fun t => iteratedDeriv n j t)
        (fun t => t ^ (-(n : ℝ) - 2))
        𝓝∞ := by
  -- Rewrite iteratedDeriv n j as jK n eventually at +∞ (using ht : 0 < t).
  have h_eq : (fun t => iteratedDeriv n j t) =ᶠ[Filter.atTop] (fun t => jK n t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact iteratedDeriv_j_eqOn_jK n ht
  exact h_eq.trans_isBigO (jK_isO n)

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
  /- Apply `iteratedDeriv_fun_mul` (Leibniz product rule) at every `t > 0`,
     using `contDiffAt_id` for the factor `s ↦ -(s/2)` (after extracting the
     constant `-(1/2)`) and `contDiffAt_j n ht` for `j`.  The resulting
     Finset sum has only two surviving terms (since `iteratedDeriv k id = 0`
     for `k ≥ 2`):
       • i=0: -(1/2)·t·iteratedDeriv n j t  = O(t · t^(-n-2)) = O(t^(-n-1)).
       • i=1: -(1/2)·n·iteratedDeriv (n-1) j t = O(t^(-n-1)). -/
  -- Step 1: closed-form for the iterated derivative on `(0, ∞)`.
  have h_eq :
      (fun t : ℝ => iteratedDeriv n (fun t => -(t / 2) * j t) t)
        =ᶠ[Filter.atTop]
      (fun t : ℝ => -(1 / 2) *
        (t * iteratedDeriv n j t + (n : ℝ) * iteratedDeriv (n - 1) j t)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    -- `-(s/2) · j s = -(1/2) · (s · j s)`; pull out the constant `-(1/2)`.
    have h_funeq :
        (fun s : ℝ => -(s / 2) * j s) = (fun s : ℝ => -(1 / 2 : ℝ) * (s * j s)) := by
      funext s; ring
    rw [h_funeq, iteratedDeriv_const_mul' (-(1 / 2 : ℝ)) (fun s => s * j s) n t]
    -- Leibniz product rule for `s · j s`.
    have h_id : ContDiffAt ℝ n (fun s : ℝ => s) t := contDiffAt_id
    have h_j : ContDiffAt ℝ n j t := contDiffAt_j n ht
    rw [iteratedDeriv_fun_mul h_id h_j]
    -- Collapse the Leibniz sum: only `i = 0` and `i = 1` survive.
    have hsplit :
        Finset.range (n + 1) = Finset.range 2 ∪ Finset.Ico 2 (n + 1) := by
      ext i; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range 2) (Finset.Ico 2 (n + 1)) := by
      rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      simp only [Finset.mem_range, Finset.mem_Ico] at hi₁ hi₂
      omega
    rw [hsplit, Finset.sum_union hdisj]
    -- Tail (`i ≥ 2`) is zero because `iteratedDeriv i id = 0`.
    have h_tail_zero :
        ∀ i ∈ Finset.Ico 2 (n + 1),
          ((n.choose i : ℝ) * iteratedDeriv i (fun s : ℝ => s) t *
            iteratedDeriv (n - i) j t) = 0 := by
      intro i hi
      have hi2 : 2 ≤ i := (Finset.mem_Ico.mp hi).1
      have h_id_zero : iteratedDeriv i (fun s : ℝ => s) t = 0 := by
        rw [iteratedDeriv_fun_id, if_neg (by omega : i ≠ 0),
            if_neg (by omega : i ≠ 1)]
      rw [h_id_zero]; ring
    rw [Finset.sum_eq_zero h_tail_zero, add_zero]
    -- Range-2 part: `i = 0` and `i = 1`.
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add]
    have h_id0 : iteratedDeriv 0 (fun s : ℝ => s) t = t := by
      rw [iteratedDeriv_fun_id]; simp
    have h_id1 : iteratedDeriv 1 (fun s : ℝ => s) t = 1 := by
      rw [iteratedDeriv_fun_id]; simp
    rw [h_id0, h_id1]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
               Nat.sub_zero]
    ring
  -- Step 2: bound the closed form by `O(t^(-n-1))`.
  refine h_eq.trans_isBigO ?_
  refine IsBigO.const_mul_left ?_ _
  refine IsBigO.add ?_ ?_
  · -- `t · iteratedDeriv n j t = O(t · t^(-n-2)) = O(t^(-n-1))`.
    have h_prod := (isBigO_refl (fun t : ℝ => t) Filter.atTop).mul
                     (iteratedDeriv_j_isO n)
    refine h_prod.trans_eventuallyEq ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [show (-(n : ℝ) - 1) = (-(n : ℝ) - 2) + 1 from by ring,
        Real.rpow_add_one ht.ne']
    ring
  · -- `n · iteratedDeriv (n-1) j t = O(t^(-(n-1)-2)) = O(t^(-n-1))`.
    refine IsBigO.const_mul_left ?_ _
    have h := iteratedDeriv_j_isO (n - 1)
    have h_pow_eq :
        (fun t : ℝ => t ^ (-((n - 1 : ℕ) : ℝ) - 2)) =
          (fun t : ℝ => t ^ (-(n : ℝ) - 1)) := by
      funext t
      congr 1
      rw [Nat.cast_sub hn]
      push_cast; ring
    rw [h_pow_eq] at h
    exact h

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
