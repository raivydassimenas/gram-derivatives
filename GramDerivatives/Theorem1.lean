/-
  GramDerivatives/Theorem1.lean
  =============================
  Lean 4 / Mathlib formalisation of **Theorem 1** from

      Dundulis, Garunkštis, Laurinčikas, Šimenas,
      "Higher derivatives of the Gram function", 2026.

  Theorem 1.  For n ≥ 2, as t → +∞ (away from discontinuities of S),

      S^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)  +  O(t^(-n-1)).

  ─── Strategy ──────────────────────────────────────────────────────────
  Abstract decomposition — for a step function `F` (any member of the
  class `StepFunction`), `S F` is *defined* by:
        S F (t) = φ(t) − (1/π)·δ(t) + F(t)
  with
    • φ(t) = −t/(2π)·log(t/(2π)) + t/(2π) − 7/8   (smooth main term),
    • δ(t) = α_part(t) − (t/2)·j(t)               (smooth error term),
    • F : StepFunction                             (any function locally
                                                    constant off a discrete
                                                    jump set `F.jumpSet`).
  Then φ^(n)(t) supplies the leading term and δ^(n)(t) = O(t^(−n−1)).
  Theorem 1 is proved for *every* such `F`: the proof uses only local
  constancy of `F` off its jump set — no Riemann ζ, no
  Karatsuba–Korolev result, and no facts about zeros of ζ.

  ─── File layout ───────────────────────────────────────────────────────
    §0  Notation and asymptotic infrastructure.
    §1  Definitions  (`φ`, `δ`, `α_part`, `ρ`, `j`).
    §2  The class `StepFunction` and its regular-point lemmas.
    §3  Smoothness lemmas (derived from §2 + elementary Mathlib calculus).
    §4  Iterated derivatives of `φ`              (main term).
    §5  Iterated derivatives of `α_part`         (algebraic error).
    §6  Iterated derivatives of `j` and `t·j(t)` (integral error).
    §7  Iterated derivatives of `δ`              (combining §5 and §6).
    §8  Statement and proof of Theorem 1.

  ─── What's axiomatised ────────────────────────────────────────────────
  Nothing.  This file contains **zero axioms**.  `StepFunction` is a
  bundled structure: a function `ℝ → ℝ` together with a discrete jump
  set (`jumpSet`, every point of which is isolated in it) off which the
  function is locally constant (`locallyConstant_off`).  The former
  axioms about the step function are now theorems about the class:
    • `StepFunction.contDiffAt` — a step function is smooth at every
      point off its jump set (a regular point), being locally constant
      there.
    • `StepFunction.iteratedDeriv_eq_zero` — every positive-order
      iterated derivative of a step function vanishes at regular points.

  Theorem 1's conclusion is relativized to the filter
  `𝓝∞₀[F.jumpSet] = 𝓝∞ ⊓ principal F.jumpSetᶜ` — going to `+∞` through
  regular points only.  This is mathematically necessary: at a jump
  point of `F`, the function `S F = φ − (1/π)·δ + F` jumps too, so
  Mathlib's `iteratedDeriv n (S F)` returns `0` there and the asymptotic
  fails.  Discreteness of the jump set guarantees this filter is
  nontrivial (`StepFunction.neBot_regularAtTop`), so the theorem is never
  vacuous.

  `S` is an ordinary `def` and `S_eq_φ_sub_δ_add_N` holds by `rfl`.  No
  Riemann ζ, Riemann–Siegel θ, or Karatsuba–Korolev input is assumed;
  the motivating instance `S(t) = (1/π)·arg ζ(1/2 + it)` — with `F`
  the ζ-zero counting step `N(γ+0)` — merely explains where the
  decomposition comes from.

  ─── Remaining gaps ────────────────────────────────────────────────────
  None.  `Theorem1.lean` builds with zero `sorry`.

  ─── How the integral error term is handled (§6) ───────────────────────
  §6 follows the proof of Theorem 1 in §2 of the paper literally.  With
  `σ` the bounded antiderivative of the sawtooth `ρ` (`0 ≤ σ ≤ 1/8`),
  integration by parts on each unit interval turns the formal derivative
  integral `jK n` into
        `jK n t = −∫₀^∞ σ(u) · ∂ᵤ∂ₜⁿ kernel(u,t) du`
  (`jK_eq_sigma_integral`) — the paper's
  `j(t) = 2∫₀^∞ σ(u)(u+1/4)/((u+1/4)²+(t/2)²)² du` differentiated `n`
  times *under the integral sign*.  Writing `a = 4u+1`, the `t`-profile of
  that integrand is `quadInv a t = ((a²+4t²)²)⁻¹`
  (`mixedDerivExpr_eq_quadInv`), and differentiating it `n` times gives
  the paper's finite sum
        `∂ₜⁿ (a²+4t²)⁻² = ∑_{r ≤ n} dsC n r · t^(2r−n)/(a²+4t²)^(r+2)`
  (`iteratedDeriv_quadInv`).  Each `u`-integral is then evaluated in closed
  form by the paper's substitution `v = (4u+1)² + 4t²`, `dv = 8(4u+1) du`:
        `∫₀^∞ (4u+1)/((4u+1)²+4t²)^(r+2) du = 1/(8(r+1)(1+4t²)^(r+1))`
  (`integral_quadPow`).  Combined with `σ ≤ 1/8` and `1 + 4t² ≥ 4t²` and
  summed over `r`, this is `sigma_mixedDerivExpr_isO`, hence `jK_isO` and
  `iteratedDeriv_j_isO`:  `j⁽ⁿ⁾(t) = O(t^(−n−2))`.

  Other formerly-axiomatic pieces of §2.5/§6 that are now theorems:
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
                                            unfolding + algebra; feeds the
                                            sign lemmas of §7a and the bridge
                                            `mixedDerivExpr_eq_quadInv`.
-/

import Mathlib

open Real Filter Asymptotics MeasureTheory
open scoped ContDiff Function

/-!
  ## §0  Notation and asymptotic infrastructure
-/

notation "𝓝∞" => Filter.atTop (α := ℝ)
abbrev IsO (f g : ℝ → ℝ) (l : Filter ℝ) : Prop := Asymptotics.IsBigO l f g

/-- Canonical `rpow`→reciprocal bridge:  `t ^ (-(m:ℕ):ℝ) = (t ^ m)⁻¹` for
    `t > 0`.  Centralises the recurring `Real.rpow_neg` + `Real.rpow_natCast`
    pairing; callers first normalise their exponent to `-(m:ℝ)`. -/
private lemma rpow_neg_nat_eq_inv {t : ℝ} (ht : 0 < t) (m : ℕ) :
    t ^ (-(m : ℝ)) = (t ^ m)⁻¹ := by
  rw [Real.rpow_neg ht.le, Real.rpow_natCast]

/-- Canonical `zpow`→reciprocal bridge:  `t ^ (-(m:ℕ):ℤ) = (t ^ m)⁻¹`.
    Centralises the recurring `zpow_neg` + `zpow_natCast` pairing; callers
    first normalise their integer exponent to `-(m:ℤ)`. -/
private lemma zpow_neg_nat_eq_inv (t : ℝ) (m : ℕ) :
    t ^ (-(m : ℤ)) = (t ^ m)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

/-!
  ## §1  Definitions

  Explicit definitions of the functions appearing in the proof: the smooth
  main term `φ`, the error term `δ`, its algebraic and integral pieces
  `α_part` and `j`, and the sawtooth function `ρ`.
-/

/-- Smooth "main-term" function in the decomposition of `S`. -/
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
  ## §2  The class `StepFunction`

  The step-function slot of the decomposition is fully abstract (no
  axioms): a `StepFunction` is any function `ℝ → ℝ` that is locally
  constant off a prescribed *discrete* jump set.

    • `jumpSet : Set ℝ` — an arbitrary discrete subset of `ℝ` (every
      point of `jumpSet` is isolated in it), recording where the
      function may jump.
    • `locallyConstant_off` — off `jumpSet`, the function is locally
      constant.  This is the *only* property of the step function that
      the proof of Theorem 1 uses.
    • Regular-point properties:  `StepFunction.contDiffAt` and
      `StepFunction.iteratedDeriv_eq_zero` require the input to lie
      *off* `jumpSet`.  This faithfully models the motivating instance
      `N(γ+0)` — the right-continuous Riemann ζ zero-counting function,
      whose jumps occur at the ordinates of ζ's nontrivial zeros — which
      is locally constant, and so smooth with vanishing positive-order
      derivatives, exactly at non-jump points.

  `S F` is *defined* by the decomposition `S F = φ − (1/π)·δ + F`, so
  `S_eq_φ_sub_δ_add_N` holds by `rfl` and is not an axiom.  Note:
  `S F` inherits `F`'s jumps, so `theorem1`'s conclusion is stated at
  the relativized filter `𝓝∞₀[F.jumpSet] = 𝓝∞ ⊓ principal F.jumpSetᶜ` —
  going to `+∞` through *regular* points only (see §8).  At a jump point
  of `S F`, Mathlib's `deriv` convention returns `0`, so the asymptotic
  genuinely fails there; relativization is mathematically necessary, not
  a formalism artefact.  Discreteness of `jumpSet` ensures the filter is
  nontrivial (`StepFunction.neBot_regularAtTop`).

  Smoothness of `φ`, `α_part`, `δ`, and `t·j(t)` is *derived* in §3 from
  the §2.5 theorem `contDiffAt_j` (formerly an axiom; now built on the
  joint induction `contDiffOn_jK`) plus elementary Mathlib calculus.
-/

/-- A **step function**: a function `ℝ → ℝ` that is locally constant off
    a prescribed discrete jump set.  Models any piecewise-constant
    function; the proof of Theorem 1 uses only `locallyConstant_off`.
    The motivating instance is the counting step `N(γ+0)` from the
    Karatsuba–Korolev expansion, whose jumps occur at the ordinates of
    ζ's nontrivial zeros. -/
structure StepFunction where
  /-- The underlying function. -/
  toFun : ℝ → ℝ
  /-- The set of points where the function may jump. -/
  jumpSet : Set ℝ
  /-- The jump set is discrete: every point of it is isolated in it. -/
  jumpSet_discrete :
    ∀ x ∈ jumpSet, ∃ ε > 0, ∀ y ∈ jumpSet, |y - x| < ε → y = x
  /-- Off the jump set, the function is locally constant. -/
  locallyConstant_off :
    ∀ ⦃s : ℝ⦄, s ∉ jumpSet → toFun =ᶠ[nhds s] fun _ => toFun s

instance : CoeFun StepFunction (fun _ => ℝ → ℝ) := ⟨StepFunction.toFun⟩

namespace StepFunction

/-- At every *regular* point `s ∉ F.jumpSet`, a step function is smooth
    (being locally constant there). -/
theorem contDiffAt (F : StepFunction) (n : ℕ) {s : ℝ}
    (h_reg : s ∉ F.jumpSet) : ContDiffAt ℝ n F s :=
  contDiffAt_const.congr_of_eventuallyEq (F.locallyConstant_off h_reg)

/-- At every regular point `t ∉ F.jumpSet`, all positive-order iterated
    derivatives of a step function vanish (because it is locally constant
    near such a `t`). -/
theorem iteratedDeriv_eq_zero (F : StepFunction) (n : ℕ) (hn : 1 ≤ n)
    {t : ℝ} (h_reg : t ∉ F.jumpSet) : iteratedDeriv n F t = 0 := by
  rw [(F.locallyConstant_off h_reg).iteratedDeriv_eq n, iteratedDeriv_const]
  exact if_neg (by omega)

end StepFunction

/-- The relativized "neighbourhood of `+∞`" filter: tend to `+∞` through
    regular points only (i.e., points not in the given jump set `J`).
    This is the filter at which `theorem1`'s asymptotic holds; at a jump
    point of `F`, `S F` has a jump too, so `iteratedDeriv n (S F)` takes
    Mathlib's default value of `0` there and the asymptotic genuinely
    fails. -/
notation "𝓝∞₀[" J "]" => Filter.atTop ⊓ Filter.principal ((J : Set ℝ))ᶜ

/-- Discreteness of the jump set makes the relativized filter
    `𝓝∞₀[F.jumpSet]` nontrivial, so `theorem1` is never vacuous: every
    ray `[a, ∞)` contains a regular point, since a discrete set cannot
    contain a whole ray. -/
theorem StepFunction.neBot_regularAtTop (F : StepFunction) :
    (𝓝∞₀[F.jumpSet]).NeBot := by
  rw [Filter.inf_principal_neBot_iff]
  intro U hU
  obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp hU
  -- It suffices to find a regular point in `[a, ∞)`.
  by_cases h : a + 1 ∈ F.jumpSet
  · -- `a + 1` jumps; by isolation, a slightly larger point is regular.
    obtain ⟨ε, hε, h_iso⟩ := F.jumpSet_discrete (a + 1) h
    have h2 : 0 < min ε 1 := lt_min hε one_pos
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    refine ⟨a + 1 + min ε 1 / 2, ha _ (by linarith), fun h_mem => ?_⟩
    have h_close : |a + 1 + min ε 1 / 2 - (a + 1)| < ε := by
      rw [show a + 1 + min ε 1 / 2 - (a + 1) = min ε 1 / 2 by ring,
          abs_of_pos (by linarith)]
      linarith
    linarith [h_iso _ h_mem h_close]
  · exact ⟨a + 1, ha _ (by linarith), h⟩

/-- The target function `S`, *defined* by the abstract decomposition
    `S F (t) = φ(t) − (1/π)·δ(t) + F(t)` for an arbitrary step function
    `F`.  Theorem 1's proof uses only this definition and the
    `StepFunction` fields — no Riemann ζ and no Karatsuba–Korolev input.
    The motivating instance is `(1/π)·arg ζ(1/2 + it)`, for which the
    decomposition is the Karatsuba–Korolev representation. -/
noncomputable def S (F : StepFunction) (t : ℝ) : ℝ :=
  φ t - (1 / Real.pi) * δ t + F t

/-- The defining decomposition of `S` — true by definition (`rfl`); was an
    axiom while `S` was opaque.  For the motivating instance
    `S(t) = (1/π)·arg ζ(1/2 + it)` it is the Karatsuba–Korolev
    representation ([6, proof of Thm 2]). -/
theorem S_eq_φ_sub_δ_add_N (F : StepFunction) (t : ℝ) :
    S F t = φ t - (1 / Real.pi) * δ t + F t := rfl

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
    exact rpow_neg_nat_eq_inv hu_pos (k + 2)
  -- Transfer from `Ioi 0` to `Ici 0` (they differ by the measure-zero `{0}`).
  exact h_ioi.congr_set_ae Ioi_ae_eq_Ici.symm

/-- Integrability on `Ici 0` from a pointwise dominator `C·((u+1/4)^(k+2))⁻¹`.

    Packages the recurring `Integrable.mono'` + `ae_restrict` scaffold shared by
    the parametric-integral integrability lemmas (`integrable_jIntegrand`,
    `integrable_sigma_mixedDerivExpr`, `integrableOn_mixedDerivExpr`):
    given AE-strong-measurability and a
    pointwise bound by the integrable dominator `integrableOn_pow_inv_shift k`,
    the function is integrable on `Ici 0`. -/
private lemma integrableOn_Ici_of_pow_inv_dominated {f : ℝ → ℝ} (k : ℕ) (C : ℝ)
    (h_meas : AEStronglyMeasurable f (volume.restrict (Set.Ici (0 : ℝ))))
    (h_bd : ∀ u ∈ Set.Ici (0 : ℝ), ‖f u‖ ≤ C * ((u + 1 / 4) ^ (k + 2))⁻¹) :
    IntegrableOn f (Set.Ici (0 : ℝ)) :=
  Integrable.mono' ((integrableOn_pow_inv_shift k).const_mul C) h_meas
    ((ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall h_bd))

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

/-- Integrability of `jIntegrand k t` on `Ici 0`. -/
private lemma integrable_jIntegrand (k : ℕ) (t : ℝ) :
    IntegrableOn (jIntegrand k t) (Set.Ici (0 : ℝ)) := by
  -- Bound the integrand pointwise via `norm_jIntegrand_le`, then dominate by
  -- the integrable `(C/2) · ((u+1/4)^(k+2))⁻¹`.
  obtain ⟨C, _, hC⟩ := exists_bound_iteratedDeriv_kernel k |t|
  refine integrableOn_Ici_of_pow_inv_dominated k (C / 2)
    (aeStronglyMeasurable_jIntegrand k t) ?_
  intro u hu
  exact norm_jIntegrand_le (hC u (Set.mem_Ici.mp hu) t (le_refl _))

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

/-- Shared neighbourhood + dominator data for the `jK` differentiation and
    continuity lemmas.  For `t > 0` and kernel-order `K`, produces a constant
    `C` for which `ball t (t/2)` is a neighbourhood of `t` and every `K`-th
    kernel derivative is dominated — pointwise in `u ≥ 0`, uniformly in
    `x ∈ ball t (t/2)` — by the integrable majorant `(C/2)·((u+1/4)^(K+2))⁻¹`. -/
private lemma jK_loc_data (K : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, Metric.ball t (t / 2) ∈ nhds t ∧
      (∀ u, 0 ≤ u → ∀ x ∈ Metric.ball t (t / 2),
        ‖jIntegrand K x u‖ ≤ C / 2 * ((u + 1 / 4) ^ (K + 2))⁻¹) ∧
      Integrable (fun u => C / 2 * ((u + 1 / 4) ^ (K + 2))⁻¹)
        (volume.restrict (Set.Ici (0 : ℝ))) := by
  obtain ⟨C, _, hC⟩ := exists_bound_iteratedDeriv_kernel K (3 * t / 2)
  exact ⟨C, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos ht)),
    fun u hu_nn x hx =>
      norm_jIntegrand_le (hC u hu_nn x (abs_le_of_mem_ball_half_pos ht x hx)),
    (integrableOn_pow_inv_shift K).const_mul (C / 2)⟩

/-- One-step differentiation under the integral:
    `(d/dt) jK k t = jK (k+1) t`.

    The integrand `t' ↦ ρ(u)·iteratedDeriv k (kernel u ·) t'` has
    `t`-derivative `ρ(u)·iteratedDeriv (k+1) (kernel u ·) t'`, dominated by
    `(C/2)·(u+1/4)^{-((k+1)+2)}` uniformly on the ball `ball t (t/2) ⊂ (0, ∞)`. -/
private lemma hasDerivAt_jK (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (jK k) (jK (k+1) t) t := by
  obtain ⟨C, h_nbhd_mem, h_dom, h_bound_int⟩ := jK_loc_data (k + 1) ht
  -- Apply differentiation-under-the-integral with uniform-`x` dominator on `ball t (t/2)`.
  have h_app := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ici (0 : ℝ)))
    (F := fun x : ℝ => jIntegrand k x) (F' := fun x : ℝ => jIntegrand (k + 1) x)
    (x₀ := t) (s := Metric.ball t (t / 2))
    (bound := fun u => C / 2 * ((u + 1 / 4) ^ ((k + 1) + 2))⁻¹)
    h_nbhd_mem
    (Filter.Eventually.of_forall (fun x => aeStronglyMeasurable_jIntegrand k x))
    (integrable_jIntegrand k t)
    (aeStronglyMeasurable_jIntegrand (k + 1) t)
    -- h_bound: pointwise dominator on F' for x in the ball.
    (by
      refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ?_)
      intro u hu_mem x hx
      exact h_dom u (Set.mem_Ici.mp hu_mem) x hx)
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
  obtain ⟨C, h_nbhd_mem, h_dom, h_bound_int⟩ := jK_loc_data k ht
  have h_app := continuousAt_of_dominated
    (μ := volume.restrict (Set.Ici (0 : ℝ)))
    (F := fun x : ℝ => jIntegrand k x)
    (x₀ := t) (bound := fun u => C / 2 * ((u + 1 / 4) ^ (k + 2))⁻¹)
    (Filter.Eventually.of_forall (fun x => aeStronglyMeasurable_jIntegrand k x))
    (Filter.eventually_of_mem h_nbhd_mem (fun x hx => by
      refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall ?_)
      intro u hu_mem
      exact h_dom u (Set.mem_Ici.mp hu_mem) x hx))
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
    ContDiffOn ℝ (n : WithTop ℕ∞) (jK k) (Set.Ioi (0 : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro k
      rw [Nat.cast_zero, contDiffOn_zero]
      intro t ht
      exact (continuousAt_jK k ht).continuousWithinAt
  | succ n ih =>
      intro k
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; ring,
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
  have h : ContDiffOn ℝ (n : WithTop ℕ∞) (jK 0) (Set.Ioi (0 : ℝ)) := contDiffOn_jK n 0
  rw [jK_zero] at h
  exact h.contDiffAt (isOpen_Ioi.mem_nhds hs)

/-!
  ## §3  Smoothness lemmas

  Derived from the axioms in §2 plus elementary Mathlib calculus.  The four
  results in this section establish `ContDiffAt ℝ n F t` for `t > 0` and
  every `F` that appears as a sub-expression of `S` in the decomposition.

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

/-- First derivative of `φ`:  `φ'(t) = −(1/(2π)) · log(t/(2π))` for `t > 0`.
    The `n = 1` companion of `iteratedDeriv_φ` (which starts at `n = 2`);
    needed for the first-derivative asymptotic of `θ` in `Corollary2.lean`. -/
theorem hasDerivAt_φ {t : ℝ} (ht : 0 < t) :
    HasDerivAt φ (-(1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))) t := by
  have h2π_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : t / (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
  -- `s ↦ s/(2π)`.
  have h_div : HasDerivAt (fun s : ℝ => s / (2 * Real.pi)) (1 / (2 * Real.pi)) t := by
    simpa using (hasDerivAt_id t).div_const (2 * Real.pi)
  -- `s ↦ log(s/(2π))`.
  have h_log : HasDerivAt (fun s : ℝ => Real.log (s / (2 * Real.pi)))
      ((1 / (2 * Real.pi)) / (t / (2 * Real.pi))) t := h_div.log hne
  -- `s ↦ −(s/(2π)) · log(s/(2π))`.
  have h_mul : HasDerivAt
      (fun s : ℝ => -(s / (2 * Real.pi)) * Real.log (s / (2 * Real.pi)))
      (-(1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))
        + -(t / (2 * Real.pi)) * ((1 / (2 * Real.pi)) / (t / (2 * Real.pi)))) t :=
    h_div.neg.mul h_log
  -- Assemble `φ` and clean up the derivative (the two `1/(2π)` terms cancel).
  have h_sum := (h_mul.add h_div).sub_const (7 / 8)
  have h_fun : (fun x : ℝ =>
      ((fun s : ℝ => -(s / (2 * Real.pi)) * Real.log (s / (2 * Real.pi)))
        + fun s : ℝ => s / (2 * Real.pi)) x - 7 / 8) = φ := by
    funext s
    simp only [Pi.add_apply]
    unfold φ; ring
  rw [h_fun] at h_sum
  convert h_sum using 1
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

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
    with x = 1/(4t²) and x = 1/(2t) respectively.

    Standalone witness for equation (11) of the paper; **not used** by
    Theorem 1's proof, which bounds the error term via `iteratedDeriv_α_part_isO`
    instead. -/
lemma α_part_expansion (t : ℝ) (_ : 0 < t) :
    ∃ (r : ℝ → ℝ),
      IsO r (fun t => t ^ (-(3 : ℝ))) 𝓝∞ ∧
      α_part t = 3 / (16 * t) + r t := by
  -- Witness: r s := α_part s − 3/(16 s).  Equation is then trivially `ring`.
  -- All real content is in the asymptotic bound.
  refine ⟨fun s => α_part s - 3 / (16 * s), ?_, by ring⟩
  -- Show the witness is `O[atTop]` of `s ↦ s^(-3 : ℝ)`.
  -- We supply explicit constant `1` and verify the bound for all `s ≥ 1`.
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with s hs
  have hs_pos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs2_pos : (0 : ℝ) < s ^ 2 := by positivity
  have hs3_pos : (0 : ℝ) < s ^ 3 := by positivity
  -- Convert `s ^ (-(3 : ℝ))` to `1 / s^3`.
  have hrpow : s ^ (-(3 : ℝ)) = 1 / s ^ 3 := by
    rw [show (-(3 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num,
        rpow_neg_nat_eq_inv hs_pos 3, one_div]
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

/-- `s ↦ 4·s²` has derivative `8·t` at `t`.  Recurring building block of the
    `α_part` derivative computations. -/
private lemma hasDerivAt_four_sq (t : ℝ) :
    HasDerivAt (fun s : ℝ => 4 * s ^ 2) (8 * t) t := by
  convert (hasDerivAt_pow 2 t).const_mul (4 : ℝ) using 1
  push_cast; ring

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
  have h_4t2 : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (8 * t) t := hasDerivAt_four_sq t
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
  have h_4t2 : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (8 * t) t := hasDerivAt_four_sq t
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
  have h_4t2 : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (8 * t) t := hasDerivAt_four_sq t
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
  refine IsBigO.of_bound C ?_
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
    refine IsBigO.of_bound (5 / 16) ?_
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
      rw [show (-((1 : ℕ) : ℝ) - 1) = -((2 : ℕ) : ℝ) from by push_cast; ring,
          rpow_neg_nat_eq_inv ht_pos 2, one_div]
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

  This section follows §2 of the paper step for step:

    1. the sawtooth antiderivative `σ` (`0 ≤ σ ≤ 1/8`) and the per-unit-interval
       integration by parts, giving
       `jK n t = −∫₀^∞ σ(u)·∂ᵤ∂ₜⁿ kernel(u,t) du`  (`jK_eq_sigma_integral`);
    2. differentiation under the integral sign, expanding
       `∂ₜⁿ ((a²+4t²)²)⁻¹` (`a = 4u+1`) into the paper's finite sum over
       `r` (`iteratedDeriv_quadInv`, `mixedDerivExpr_eq_quadInv`);
    3. the paper's substitution `v = (4u+1)² + 4t²` evaluating each
       `u`-integral in closed form (`integral_quadPow`);
    4. `σ ≤ 1/8`, `1 + 4t² ≥ 4t²` and summation over `r`
       (`sigma_mixedDerivExpr_isO`).
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
  refine integrableOn_Ici_of_pow_inv_dominated (n + 1) (C / 8) h_meas ?_
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

/-! ### Rescaled forms of the integration-by-parts integrand

Two equivalent closed forms of `mixedDerivExpr n u t = ∂ᵤ ∂ₜⁿ kernel(u,t)`
are used downstream:

* `mixedDerivExpr_eq_lorMix` — the Lorentzian rescaling
  `mixedDerivExpr n u t = (1/2)^n · (u+1/4)^{-(n+3)} · lorMix n (t/(2(u+1/4)))`,
  which exhibits the `u`-dependence as a single negative power and feeds the
  sign lemmas of §7a;
* `mixedDerivExpr_eq_quadInv` — the paper's form
  `mixedDerivExpr n u t = −128·(4u+1)·∂ₜⁿ (((4u+1)² + 4t²)²)⁻¹`,
  from which the estimate of `j⁽ⁿ⁾` is obtained by differentiating under the
  integral sign (see "The paper's differentiation-under-the-integral-sign
  computation" below). -/

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
    rw [show (-((n : ℤ) + 3)) = -((n + 3 : ℕ) : ℤ) from by push_cast; ring,
        zpow_neg_nat_eq_inv]
  rw [h_zpow]
  unfold mixedDerivExpr lorMix
  field_simp
  ring

/-! ### Identification of `lorMix` with `iteratedDeriv lor²`.

`lorMix n s = -2 · (d/ds)^n (lor²)(s)`, where `lor² s = (lor s)²`.  This is
the bridge between the two rescalings above:  the paper's profile
`quadInv a t = ((a²+4t²)²)⁻¹` is `a⁻⁴ · lorSq(2t/a)`, so
`mixedDerivExpr_eq_lorMix` and `mixedDerivExpr_eq_quadInv` are two readings
of the same identity.  It is also what gives the closed forms
`lorMix 0 = -2·lor²` and `lorMix 1 s = 8s·lor³` used by the sign lemmas
of §7a. -/

/-- Squared Lorentzian profile `lorSq s = (lor s)² = 1/(1+s²)²`.  Closed
    form for `lorMix 0` (cf. `lorMix_zero` below), and the profile behind
    the paper's `quadInv` (see `iteratedDeriv_quadInv_eq_lorSq`). -/
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

/-! ### The paper's differentiation-under-the-integral-sign computation

This sub-section follows the proof of Theorem 1 in §2 of the paper verbatim.
After the integration by parts of `jK_eq_sigma_integral`, the remaining task
is to differentiate

    `j(t) = 2 ∫₀^∞ σ(u) (u + 1/4) / ((u + 1/4)² + (t/2)²)² du`

`n` times *under the integral sign* and to estimate the result.  Writing
`a = 4u + 1` (so that `(u+1/4)² + (t/2)² = (a² + 4t²)/16`), the integrand's
`t`-dependence is carried entirely by

    `quadInv a t = ((a² + 4t²)²)⁻¹`,

and `∂ᵤ ∂ₜⁿ kernel(u,t) = −128 · a · ∂ₜⁿ quadInv a t`
(`mixedDerivExpr_eq_quadInv`).

Differentiating `quadInv` `n` times produces exactly the sum displayed in the
paper,

    `∂ₜⁿ (a² + 4t²)⁻² = ∑_{r} dsC n r · t^(2r−n) / (a² + 4t²)^(r+2)`

(`iteratedDeriv_quadInv`), whose coefficients `dsC n r` obey the two-term
recursion coming from the product rule; they vanish outside the paper's range
`⌈n/2⌉ ≤ r ≤ n`, but only `r ≤ n` (`dsC_eq_zero_of_lt`) is needed here — the
terms with `2r < n` carry a *negative* power of `t` and are therefore already
smaller than `t^(−n−2)`.

Each of the resulting `u`-integrals is evaluated in closed form by the paper's
substitution `v = (4u+1)² + 4t²`, `dv = 8(4u+1) du`:

    `∫₀^∞ (4u+1) / ((4u+1)² + 4t²)^(r+2) du = 1 / (8(r+1)(1 + 4t²)^(r+1))`

(`integral_quadPow`, obtained from the explicit antiderivative `quadAnti`).
Combining this with the paper's two elementary bounds `0 ≤ σ ≤ 1/8` and
`1 + 4t² ≥ 4t²` and summing over `r` yields `sigma_mixedDerivExpr_isO`, i.e.
`j⁽ⁿ⁾(t) ≪ₙ t^(−n−2)`. -/

/-- The `t`-profile of the integration-by-parts kernel, at scale `a = 4u + 1`:
    `quadInv a t = ((a² + 4t²)²)⁻¹`.  Up to the constant `64·a` this is the
    integrand `(u+1/4)/((u+1/4)² + (t/2)²)²` of the paper's IBP'd formula. -/
private noncomputable def quadInv (a : ℝ) (t : ℝ) : ℝ := ((a ^ 2 + 4 * t ^ 2) ^ 2)⁻¹

/-- Coefficients of the paper's expansion of `∂ₜⁿ (a² + 4t²)⁻²` as a sum of
    terms `t^(2r−n) / (a² + 4t²)^(r+2)`.

    They are `a`-independent and satisfy the product-rule recursion
    `dsC (n+1) r = dsC n r · (2r − n) − 8(r+1) · dsC n (r−1)`,
    obtained from
    `d/dt [t^p / (a²+4t²)^q] = p·t^(p−1)/(a²+4t²)^q − 8q·t^(p+1)/(a²+4t²)^(q+1)`
    with `p = 2r − n`, `q = r + 2`. -/
private noncomputable def dsC : ℕ → ℕ → ℝ
  | 0,     r     => if r = 0 then 1 else 0
  | n + 1, 0     => dsC n 0 * (0 - (n : ℝ))
  | n + 1, r + 1 => dsC n (r + 1) * (2 * ((r : ℝ) + 1) - n) - 8 * ((r : ℝ) + 2) * dsC n r

/-- The `r`-th elementary profile of the expansion:
    `dsPow m a r t = t^(2r−m) / (a² + 4t²)^(r+2)` (integer exponent, so no
    truncated subtraction: the terms with `2r < m` simply carry a negative
    power of `t`). -/
private noncomputable def dsPow (m : ℕ) (a : ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * (r : ℤ) - m) / (a ^ 2 + 4 * t ^ 2) ^ (r + 2)

/-- The expansion of `∂ₜⁿ (a²+4t²)⁻²` involves only `r ≤ n`:  `dsC n r = 0`
    for `r > n`.  Induction on `n` through the two-term recursion. -/
private lemma dsC_eq_zero_of_lt : ∀ (n r : ℕ), n < r → dsC n r = 0 := by
  intro n
  induction n with
  | zero =>
    intro r hr
    cases r with
    | zero => omega
    | succ k => simp [dsC]
  | succ m ih =>
    intro r hr
    cases r with
    | zero => omega
    | succ k =>
      have h1 : m < k := by omega
      have h2 : m < k + 1 := by omega
      simp [dsC, ih k h1, ih (k + 1) h2]

/-- Re-indexing identity behind the induction step of `iteratedDeriv_quadInv`.

    Differentiating the order-`n` expansion term by term produces, for each
    `r ≤ n`, a contribution `dsC n r · (2r−n)` at index `r` and a contribution
    `−8(r+2)·dsC n r` at index `r+1`; collecting them is exactly the `dsC`
    recursion.  Stated for an arbitrary weight family `W` (instantiated with
    `W r = dsPow (n+1) a r t`); the `r = n+1` boundary term vanishes by
    `dsC_eq_zero_of_lt`. -/
private lemma dsC_sum_step (n : ℕ) (W : ℕ → ℝ) :
    ∑ r ∈ Finset.range (n + 1),
        (dsC n r * (2 * (r : ℝ) - n) * W r - 8 * ((r : ℝ) + 2) * dsC n r * W (r + 1))
      = ∑ r ∈ Finset.range (n + 2), dsC (n + 1) r * W r := by
  have hR : ∑ r ∈ Finset.range (n + 2), dsC (n + 1) r * W r
      = (∑ r ∈ Finset.range (n + 1), dsC (n + 1) (r + 1) * W (r + 1))
        + dsC (n + 1) 0 * W 0 := Finset.sum_range_succ' _ _
  have hzero : dsC n (n + 1) = 0 := dsC_eq_zero_of_lt n (n + 1) (by omega)
  have hR2 : (∑ r ∈ Finset.range (n + 1), dsC (n + 1) (r + 1) * W (r + 1))
      = (∑ r ∈ Finset.range (n + 1), dsC n (r + 1) * (2 * ((r : ℝ) + 1) - n) * W (r + 1))
        - ∑ r ∈ Finset.range (n + 1), 8 * ((r : ℝ) + 2) * dsC n r * W (r + 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    change (dsC n (r + 1) * (2 * ((r : ℝ) + 1) - n)
      - 8 * ((r : ℝ) + 2) * dsC n r) * W (r + 1) = _
    ring
  have hshift : (∑ r ∈ Finset.range (n + 1), dsC n (r + 1) * (2 * ((r : ℝ) + 1) - n) * W (r + 1))
      = ∑ r ∈ Finset.range n, dsC n (r + 1) * (2 * ((r : ℝ) + 1) - n) * W (r + 1) := by
    rw [Finset.sum_range_succ, hzero]
    ring
  have hL1 : ∑ r ∈ Finset.range (n + 1), dsC n r * (2 * (r : ℝ) - n) * W r
      = (∑ r ∈ Finset.range n, dsC n (r + 1) * (2 * ((r : ℝ) + 1) - n) * W (r + 1))
        + dsC n 0 * (0 - (n : ℝ)) * W 0 := by
    rw [Finset.sum_range_succ' (fun r => dsC n r * (2 * (r : ℝ) - n) * W r) n]
    push_cast
    norm_num
  have hd0 : dsC (n + 1) 0 = dsC n 0 * (0 - (n : ℝ)) := rfl
  rw [Finset.sum_sub_distrib, hL1, hR, hR2, hshift, hd0]
  ring

/-- Derivative of a single term of the expansion:
    `d/dt [c · t^(2r−n)/(a²+4t²)^(r+2)]
       = c(2r−n)·t^(2r−(n+1))/(a²+4t²)^(r+2)
         − 8(r+2)c·t^(2(r+1)−(n+1))/(a²+4t²)^(r+3)`,
    i.e. a contribution at index `r` plus one at index `r+1` of the
    order-`(n+1)` expansion.  This is the product rule that generates the
    `dsC` recursion. -/
private lemma hasDerivAt_dsTerm (n r : ℕ) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => dsC n r * dsPow n a r s)
      (dsC n r * (2 * (r : ℝ) - n) * dsPow (n + 1) a r t
        - 8 * ((r : ℝ) + 2) * dsC n r * dsPow (n + 1) a (r + 1) t) t := by
  have hD : (0 : ℝ) < a ^ 2 + 4 * t ^ 2 := by positivity
  have hz : HasDerivAt (fun s : ℝ => s ^ (2 * (r : ℤ) - n))
      (((2 * (r : ℤ) - n : ℤ) : ℝ) * t ^ (2 * (r : ℤ) - n - 1)) t :=
    hasDerivAt_zpow _ _ (Or.inl ht.ne')
  have hbase : HasDerivAt (fun s : ℝ => a ^ 2 + 4 * s ^ 2) (8 * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (4 : ℝ)).const_add (a ^ 2)
    convert this using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => (a ^ 2 + 4 * s ^ 2) ^ (r + 2))
      (((r : ℝ) + 2) * (a ^ 2 + 4 * t ^ 2) ^ (r + 1) * (8 * t)) t := by
    have := hbase.pow (r + 2)
    convert this using 1
    push_cast
    ring
  have hinv := hd.inv (by positivity)
  have hmain := (hz.mul hinv).const_mul (dsC n r)
  simp only [Pi.mul_apply, Pi.inv_apply] at hmain
  have hfun : (fun s : ℝ => dsC n r * dsPow n a r s)
      = fun s : ℝ => dsC n r *
          (s ^ (2 * (r : ℤ) - n) * ((a ^ 2 + 4 * s ^ 2) ^ (r + 2))⁻¹) := by
    funext s; simp only [dsPow, div_eq_mul_inv]
  rw [hfun]
  convert hmain using 1
  have h1 : t ^ (2 * (r : ℤ) - ((n : ℤ) + 1)) = t ^ (2 * (r : ℤ) - n) / t := by
    rw [show (2 * (r : ℤ) - ((n : ℤ) + 1)) = (2 * (r : ℤ) - n) - 1 from by ring,
        zpow_sub₀ ht.ne', zpow_one]
  have h2 : t ^ (2 * ((r : ℤ) + 1) - ((n : ℤ) + 1)) = t ^ (2 * (r : ℤ) - n) * t := by
    rw [show (2 * ((r : ℤ) + 1) - ((n : ℤ) + 1)) = (2 * (r : ℤ) - n) + 1 from by ring,
        zpow_add₀ ht.ne', zpow_one]
  have h3 : t ^ (2 * (r : ℤ) - n - 1) = t ^ (2 * (r : ℤ) - n) / t := by
    rw [zpow_sub₀ ht.ne', zpow_one]
  simp only [dsPow]
  push_cast
  rw [h1, h2, h3]
  have hE1 : (a ^ 2 + 4 * t ^ 2) ^ (r + 1)
      = (a ^ 2 + 4 * t ^ 2) ^ r * (a ^ 2 + 4 * t ^ 2) ^ 1 := pow_add _ _ _
  have hE2 : (a ^ 2 + 4 * t ^ 2) ^ (r + 2)
      = (a ^ 2 + 4 * t ^ 2) ^ r * (a ^ 2 + 4 * t ^ 2) ^ 2 := pow_add _ _ _
  have hE3 : (a ^ 2 + 4 * t ^ 2) ^ (r + 1 + 2)
      = (a ^ 2 + 4 * t ^ 2) ^ r * (a ^ 2 + 4 * t ^ 2) ^ 3 := by
    rw [show r + 1 + 2 = r + 3 from rfl]; exact pow_add _ _ _
  rw [hE1, hE2, hE3]
  have hEpos : (0 : ℝ) < (a ^ 2 + 4 * t ^ 2) ^ r := pow_pos hD r
  generalize hEg : (a ^ 2 + 4 * t ^ 2) ^ r = E at hEpos ⊢
  generalize hPg : t ^ (2 * (r : ℤ) - n) = P
  field_simp
  ring

/-- **The paper's expansion of the `n`-th `t`-derivative under the integral
    sign** (`t > 0`, `a > 0`):

        `∂ₜⁿ ((a² + 4t²)²)⁻¹ = ∑_{r ≤ n} dsC n r · t^(2r−n) / (a² + 4t²)^(r+2)`.

    Induction on `n`: the derivative of the order-`n` expansion is computed
    term by term (`hasDerivAt_dsTerm`) and re-indexed by `dsC_sum_step`. -/
private lemma iteratedDeriv_quadInv (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ t : ℝ, 0 < t →
      iteratedDeriv n (quadInv a) t = ∑ r ∈ Finset.range (n + 1), dsC n r * dsPow n a r t := by
  induction n with
  | zero =>
    intro t ht
    simp [dsPow, dsC, quadInv]
  | succ n ih =>
    intro t ht
    have hev : iteratedDeriv n (quadInv a)
        =ᶠ[nhds t] fun s => ∑ r ∈ Finset.range (n + 1), dsC n r * dsPow n a r s := by
      filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr ht)] with s hs using ih s hs
    have hderiv : HasDerivAt (fun s => ∑ r ∈ Finset.range (n + 1), dsC n r * dsPow n a r s)
        (∑ r ∈ Finset.range (n + 1),
          (dsC n r * (2 * (r : ℝ) - n) * dsPow (n + 1) a r t
            - 8 * ((r : ℝ) + 2) * dsC n r * dsPow (n + 1) a (r + 1) t)) t := by
      have hsum := HasDerivAt.sum (u := Finset.range (n + 1))
        (A := fun (r : ℕ) (s : ℝ) => dsC n r * dsPow n a r s)
        (fun r _ => hasDerivAt_dsTerm n r ha ht)
      have heq : (∑ x ∈ Finset.range (n + 1), fun s : ℝ => dsC n x * dsPow n a x s)
          = fun s : ℝ => ∑ r ∈ Finset.range (n + 1), dsC n r * dsPow n a r s := by
        funext s; exact Finset.sum_apply s _ _
      rw [heq] at hsum
      simpa [Finset.sum_sub_distrib] using hsum
    rw [iteratedDeriv_succ, hev.deriv_eq, hderiv.deriv,
        dsC_sum_step n (fun r => dsPow (n + 1) a r t)]

/-- Rescaling `quadInv` onto the Lorentzian square:
    `quadInv a t = a⁻⁴ · lorSq(2t/a)`, hence
    `∂ₜⁿ quadInv a t = a⁻⁴ · (2/a)ⁿ · (lorSq)⁽ⁿ⁾(2t/a)`. -/
private lemma iteratedDeriv_quadInv_eq_lorSq (n : ℕ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    iteratedDeriv n (quadInv a) t
      = (a ^ 4)⁻¹ * (2 / a) ^ n * iteratedDeriv n lorSq ((2 / a) * t) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hfun : quadInv a = fun s : ℝ => (a ^ 4)⁻¹ * lorSq ((2 / a) * s) := by
    funext s
    have hd : (0 : ℝ) < a ^ 2 + 4 * s ^ 2 := by positivity
    have h1 : 1 + ((2 / a) * s) ^ 2 = (a ^ 2 + 4 * s ^ 2) / a ^ 2 := by
      field_simp; ring
    unfold quadInv lorSq lor
    rw [h1]
    field_simp
  rw [hfun, iteratedDeriv_const_mul_field (a ^ 4)⁻¹ (fun s => lorSq ((2 / a) * s)),
      show (iteratedDeriv n fun s : ℝ => lorSq ((2 / a) * s)) =
        (fun s : ℝ => (2 / a) ^ n * iteratedDeriv n lorSq ((2 / a) * s)) from
      iteratedDeriv_comp_const_mul (contDiff_lorSq.of_le le_top) _]
  ring

/-- **The IBP kernel in the paper's variables.**  With `a = 4u + 1`,

        `∂ᵤ ∂ₜⁿ kernel(u,t) = −128 · a · ∂ₜⁿ ((a² + 4t²)²)⁻¹`,

    which is `−2·(u+1/4)·∂ₜⁿ ((u+1/4)² + (t/2)²)⁻²` written out — the
    integrand of the paper's integration-by-parts formula for `j`. -/
private lemma mixedDerivExpr_eq_quadInv (n : ℕ) {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    mixedDerivExpr n u t
      = -128 * (4 * u + 1) * iteratedDeriv n (quadInv (4 * u + 1)) t := by
  have ha : (0 : ℝ) < 4 * u + 1 := by linarith
  have ha_ne : (4 * u + 1 : ℝ) ≠ 0 := ne_of_gt ha
  have hr : (0 : ℝ) < u + 1 / 4 := by linarith
  have hr_ne : (u + 1 / 4 : ℝ) ≠ 0 := ne_of_gt hr
  have h2a : (2 : ℝ) / (4 * u + 1) = 1 / (2 * (u + 1 / 4)) := by
    field_simp
    ring
  have hhalf : (1 : ℝ) / (2 * (u + 1 / 4)) = (1 / 2) * (u + 1 / 4)⁻¹ := by
    field_simp
  rw [mixedDerivExpr_eq_lorMix n hu t, lorMix_eq_iteratedDeriv_lorSq,
      iteratedDeriv_quadInv_eq_lorSq n ha, h2a, hhalf, mul_pow, inv_pow,
      show (-((n : ℤ) + 3)) = -((n + 3 : ℕ) : ℤ) from by push_cast; ring,
      zpow_neg_nat_eq_inv, pow_add,
      show (4 * u + 1 : ℝ) = 4 * (u + 1 / 4) from by ring]
  have hqpos : (0 : ℝ) < (u + 1 / 4) ^ n := pow_pos hr n
  generalize hL : iteratedDeriv n lorSq ((1 / 2 * (u + 1 / 4)⁻¹) * t) = L
  generalize hq : (u + 1 / 4 : ℝ) ^ n = q at hqpos ⊢
  generalize hc : (1 / 2 : ℝ) ^ n = c
  have hqne : q ≠ 0 := ne_of_gt hqpos
  field_simp
  ring

/-- The `u`-kernel of the paper's estimate:
    `quadKer r t u = (4u+1)/((4u+1)² + 4t²)^(r+2)`. -/
private noncomputable def quadKer (r : ℕ) (t u : ℝ) : ℝ :=
  (4 * u + 1) / ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ (r + 2)

private lemma quadKer_nonneg (r : ℕ) (t : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ quadKer r t u := by
  have : (0 : ℝ) < 4 * u + 1 := by linarith
  unfold quadKer
  positivity

/-- Antiderivative in `u` used for the paper's substitution
    `v = (4u+1)² + 4t²`, `dv = 8(4u+1) du`:

        `quadAnti r t u = −1/(8(r+1)) · ((4u+1)² + 4t²)^(−(r+1))`,

    whose `u`-derivative is `(4u+1)/((4u+1)² + 4t²)^(r+2)`. -/
private noncomputable def quadAnti (r : ℕ) (t : ℝ) (u : ℝ) : ℝ :=
  -(1 / (8 * ((r : ℝ) + 1))) * (((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ (r + 1))⁻¹

private lemma hasDerivAt_quadAnti (r : ℕ) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (quadAnti r t) (quadKer r t u) u := by
  unfold quadKer
  have hD : (0 : ℝ) < (4 * u + 1) ^ 2 + 4 * t ^ 2 := by positivity
  have hlin : HasDerivAt (fun v : ℝ => 4 * v + 1) 4 u := by
    simpa using ((hasDerivAt_id u).const_mul (4 : ℝ)).add_const (1 : ℝ)
  have hb : HasDerivAt (fun v : ℝ => (4 * v + 1) ^ 2 + 4 * t ^ 2) (8 * (4 * u + 1)) u := by
    have := (hlin.pow 2).add_const (4 * t ^ 2)
    convert this using 1
    push_cast
    ring
  have hp : HasDerivAt (fun v : ℝ => ((4 * v + 1) ^ 2 + 4 * t ^ 2) ^ (r + 1))
      (((r : ℝ) + 1) * ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ r * (8 * (4 * u + 1))) u := by
    have := hb.pow (r + 1)
    convert this using 1
    push_cast
    ring
  have hinv := hp.inv (by positivity)
  have hmain := hinv.const_mul (-(1 / (8 * ((r : ℝ) + 1))))
  convert hmain using 1
  have hE1 : ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ (r + 1)
      = ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ r * ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ 1 := pow_add _ _ _
  have hE2 : ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ (r + 2)
      = ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ r * ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ 2 := pow_add _ _ _
  rw [hE1, hE2]
  have hEpos : (0 : ℝ) < ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ r := pow_pos hD r
  generalize hEg : ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ r = E at hEpos ⊢
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  field_simp

private lemma tendsto_quadAnti (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (quadAnti r t) Filter.atTop (nhds 0) := by
  have hbig : Filter.Tendsto (fun u : ℝ => ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ (r + 1))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ (Filter.tendsto_atTop_add_const_right _ 1
      (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4)))
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    have h1 : (1 : ℝ) ≤ 4 * u + 1 := by linarith
    have h2 : (4 * u + 1) ≤ (4 * u + 1) ^ 2 + 4 * t ^ 2 := by nlinarith
    calc 4 * u + 1 ≤ (4 * u + 1) ^ 2 + 4 * t ^ 2 := h2
      _ ≤ ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ (r + 1) := le_self_pow₀ (by linarith) (by omega)
  have hinv := hbig.inv_tendsto_atTop
  have h0 := hinv.const_mul (-(1 / (8 * ((r : ℝ) + 1))))
  simp only [Pi.inv_apply, mul_zero] at h0
  exact h0

/-- Integrability of the paper's `u`-kernel on `(0, ∞)`:  it is the derivative
    of the bounded monotone antiderivative `quadAnti`. -/
private lemma integrableOn_quadPow (r : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (quadKer r t) (Set.Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun u _ => hasDerivAt_quadAnti r ht u)
    (fun _ hu => quadKer_nonneg r t (le_of_lt (Set.mem_Ioi.mp hu)))
    (tendsto_quadAnti r ht)

/-- **The paper's substitution `v = (4u+1)² + 4t²`, `dv = 8(4u+1) du`:**

        `∫₀^∞ (4u+1) / ((4u+1)² + 4t²)^(r+2) du
           = (1/8) ∫_{1+4t²}^∞ v^(−r−2) dv = 1/(8(r+1)(1 + 4t²)^(r+1))`.

    Formalised through the explicit antiderivative `quadAnti` (improper FTC),
    which is the same computation without a change of variables. -/
private lemma integral_quadPow (r : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ u in Set.Ioi (0 : ℝ), quadKer r t u
      = 1 / (8 * ((r : ℝ) + 1) * (1 + 4 * t ^ 2) ^ (r + 1)) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun u _ => hasDerivAt_quadAnti r ht u)
    (fun u hu => quadKer_nonneg r t (le_of_lt (Set.mem_Ioi.mp hu)))
    (tendsto_quadAnti r ht)]
  have hpos : (0 : ℝ) < (1 + 4 * t ^ 2) ^ (r + 1) := by positivity
  have hr : (0 : ℝ) < 8 * ((r : ℝ) + 1) := by positivity
  simp only [quadAnti]
  norm_num
  field_simp

/-- The majorant produced by the paper's estimate of `σ · ∂ᵤ∂ₜⁿ kernel`:
    `∑_{r ≤ n} 16·|dsC n r|·t^(2r−n)·(4u+1)/((4u+1)² + 4t²)^(r+2)`.
    (The `16 = 128/8` collects the constant `128` of `mixedDerivExpr_eq_quadInv`
    and the paper's bound `σ ≤ 1/8`.) -/
private noncomputable def jMajorant (n : ℕ) (t : ℝ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (n + 1), 16 * |dsC n r| * t ^ (2 * (r : ℤ) - n) * quadKer r t u

private lemma integrableOn_jMajorant (n : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (jMajorant n t) (Set.Ici (0 : ℝ)) := by
  have hIoi : IntegrableOn (jMajorant n t) (Set.Ioi (0 : ℝ)) := by
    refine integrable_finset_sum _ (fun r _ => ?_)
    exact ((integrableOn_quadPow r ht).const_mul
      (16 * |dsC n r| * t ^ (2 * (r : ℤ) - n)))
  exact hIoi.congr_set_ae Ioi_ae_eq_Ici.symm

/-- Pointwise form of the paper's estimate: after the integration by parts,
    `|σ(u) · ∂ᵤ∂ₜⁿ kernel(u,t)| ≤ jMajorant n t u` for `u ≥ 0`, `t > 0`.
    Uses `mixedDerivExpr_eq_quadInv`, the expansion `iteratedDeriv_quadInv`,
    and the paper's bound `0 ≤ σ ≤ 1/8`. -/
private lemma norm_sigma_mixedDerivExpr_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖σ u * mixedDerivExpr n u t‖ ≤ jMajorant n t u := by
  have ha : (0 : ℝ) < 4 * u + 1 := by linarith
  have hσ_nn : 0 ≤ σ u := σ_nonneg u
  have hσ_le : σ u ≤ 1 / 8 := σ_le_eighth u
  have hdsPow_pos : ∀ r : ℕ, 0 < dsPow n (4 * u + 1) r t := by
    intro r
    have h1 : (0 : ℝ) < t ^ (2 * (r : ℤ) - n) := zpow_pos ht _
    have h2 : (0 : ℝ) < ((4 * u + 1) ^ 2 + 4 * t ^ 2) ^ (r + 2) := by positivity
    unfold dsPow
    positivity
  have hterm : ∀ r : ℕ, (4 * u + 1) * dsPow n (4 * u + 1) r t
      = t ^ (2 * (r : ℤ) - n) * quadKer r t u := by
    intro r
    unfold dsPow quadKer
    ring
  -- Absolute value of the IBP integrand, expanded by the paper's formula.
  have habs : |mixedDerivExpr n u t|
      ≤ ∑ r ∈ Finset.range (n + 1),
          128 * |dsC n r| * (t ^ (2 * (r : ℤ) - n) * quadKer r t u) := by
    rw [mixedDerivExpr_eq_quadInv n hu t, iteratedDeriv_quadInv n ha t ht]
    have hsplit : |(-128 : ℝ) * (4 * u + 1)
          * ∑ r ∈ Finset.range (n + 1), dsC n r * dsPow n (4 * u + 1) r t|
        = 128 * (4 * u + 1)
          * |∑ r ∈ Finset.range (n + 1), dsC n r * dsPow n (4 * u + 1) r t| := by
      rw [abs_mul, abs_mul, abs_of_pos ha]
      norm_num
    rw [hsplit]
    have h1 : |∑ r ∈ Finset.range (n + 1), dsC n r * dsPow n (4 * u + 1) r t|
        ≤ ∑ r ∈ Finset.range (n + 1), |dsC n r| * dsPow n (4 * u + 1) r t := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [abs_mul, abs_of_pos (hdsPow_pos r)]
    calc 128 * (4 * u + 1)
            * |∑ r ∈ Finset.range (n + 1), dsC n r * dsPow n (4 * u + 1) r t|
        ≤ 128 * (4 * u + 1)
            * ∑ r ∈ Finset.range (n + 1), |dsC n r| * dsPow n (4 * u + 1) r t := by
          have : (0 : ℝ) ≤ 128 * (4 * u + 1) := by positivity
          exact mul_le_mul_of_nonneg_left h1 this
      _ = ∑ r ∈ Finset.range (n + 1),
            128 * |dsC n r| * (t ^ (2 * (r : ℤ) - n) * quadKer r t u) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← hterm r]
          ring
  calc ‖σ u * mixedDerivExpr n u t‖
      = σ u * |mixedDerivExpr n u t| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσ_nn]
    _ ≤ (1 / 8) * ∑ r ∈ Finset.range (n + 1),
            128 * |dsC n r| * (t ^ (2 * (r : ℤ) - n) * quadKer r t u) :=
        mul_le_mul hσ_le habs (abs_nonneg _) (by norm_num)
    _ = jMajorant n t u := by
        unfold jMajorant
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring

/-- The paper's final estimate of the majorant integral:  evaluating each
    `u`-integral by `integral_quadPow` and using `1 + 4t² ≥ 4t² ≥ t²` gives

        `∫₀^∞ jMajorant n t ≤ (∑_{r ≤ n} 2|dsC n r|) · t^(−n−2)`.

    Term by term this is the paper's
    `t^(2r−n)/(64(r+1)(1+4t²)^(r+1)) ≤ t^(−n−2)/(64(r+1)4^(r+1))`. -/
private lemma integral_jMajorant_le (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ u in Set.Ici (0 : ℝ), jMajorant n t u)
      ≤ (∑ r ∈ Finset.range (n + 1), 2 * |dsC n r|) * t ^ (-(n : ℤ) - 2) := by
  have hval : (∫ u in Set.Ici (0 : ℝ), jMajorant n t u)
      = ∑ r ∈ Finset.range (n + 1),
          16 * |dsC n r| * t ^ (2 * (r : ℤ) - n)
            * (1 / (8 * ((r : ℝ) + 1) * (1 + 4 * t ^ 2) ^ (r + 1))) := by
    rw [integral_Ici_eq_integral_Ioi]
    unfold jMajorant
    rw [integral_finset_sum _ (fun r _ =>
      ((integrableOn_quadPow r ht).const_mul (16 * |dsC n r| * t ^ (2 * (r : ℤ) - n))))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_const_mul]
    congr 1
    exact integral_quadPow r ht
  rw [hval, Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ => ?_
  -- The paper keeps the sharper factor `4^(r+1)` from `1 + 4t² ≥ 4t²`; only
  -- `1 + 4t² ≥ t²` (hence `(1 + 4t²)^(r+1) ≥ t^(2r+2)`) and `r + 1 ≥ 1` are
  -- needed for the `O(t^(-n-2))` conclusion.
  have hpow_ge : t ^ (2 * r + 2) ≤ (1 + 4 * t ^ 2) ^ (r + 1) := by
    calc t ^ (2 * r + 2) = (t ^ 2) ^ (r + 1) := by rw [← pow_mul]; ring_nf
      _ ≤ (1 + 4 * t ^ 2) ^ (r + 1) := by
          refine pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg t]) _
  have hd_ge : 8 * t ^ (2 * r + 2) ≤ 8 * ((r : ℝ) + 1) * (1 + 4 * t ^ 2) ^ (r + 1) := by
    have h1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) r; linarith
    nlinarith [pow_pos ht (2 * r + 2), pow_pos (show (0:ℝ) < 1 + 4 * t ^ 2 by positivity) (r + 1)]
  have hfrac : 1 / (8 * ((r : ℝ) + 1) * (1 + 4 * t ^ 2) ^ (r + 1))
      ≤ 1 / (8 * t ^ (2 * r + 2)) :=
    one_div_le_one_div_of_le (by positivity) hd_ge
  have hcoef_nn : (0 : ℝ) ≤ 16 * |dsC n r| * t ^ (2 * (r : ℤ) - n) := by
    have : (0 : ℝ) < t ^ (2 * (r : ℤ) - n) := zpow_pos ht _
    positivity
  have hzpow_id : t ^ (2 * (r : ℤ) - n) * (1 / (8 * t ^ (2 * r + 2)))
      = 1 / 8 * t ^ (-(n : ℤ) - 2) := by
    have hm : (t : ℝ) ^ (2 * r + 2) = t ^ (2 * (r : ℤ) + 2) := by
      rw [show (2 * (r : ℤ) + 2) = ((2 * r + 2 : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
    rw [hm, one_div, mul_inv, ← zpow_neg,
        show (t : ℝ) ^ (2 * (r : ℤ) - n) * (8⁻¹ * t ^ (-(2 * (r : ℤ) + 2)))
          = 8⁻¹ * (t ^ (2 * (r : ℤ) - n) * t ^ (-(2 * (r : ℤ) + 2))) from by ring,
        ← zpow_add₀ ht.ne',
        show (2 * (r : ℤ) - n + -(2 * (r : ℤ) + 2)) = -(n : ℤ) - 2 from by ring, one_div]
  calc 16 * |dsC n r| * t ^ (2 * (r : ℤ) - n)
          * (1 / (8 * ((r : ℝ) + 1) * (1 + 4 * t ^ 2) ^ (r + 1)))
      ≤ 16 * |dsC n r| * t ^ (2 * (r : ℤ) - n) * (1 / (8 * t ^ (2 * r + 2))) := by
        exact mul_le_mul_of_nonneg_left hfrac hcoef_nn
    _ = 2 * |dsC n r| * t ^ (-(n : ℤ) - 2) := by
        rw [mul_assoc, hzpow_id]; ring

/-- Asymptotic bound on the σ-weighted integral of `mixedDerivExpr n u t`:
    `|∫₀^∞ σ(u) · mixedDerivExpr n u t du| = O(t^(-n-2))` as `t → +∞`.

    This is the paper's estimate of `j⁽ⁿ⁾`: bound the integrand pointwise by
    the majorant produced by differentiating under the integral sign
    (`norm_sigma_mixedDerivExpr_le`), then integrate the majorant in closed
    form via the substitution `v = (4u+1)² + 4t²` (`integral_jMajorant_le`). -/
private lemma sigma_mixedDerivExpr_isO (n : ℕ) :
    IsO (fun t : ℝ => ∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t)
        (fun t => t ^ (-(n : ℝ) - 2))
        𝓝∞ := by
  refine IsBigO.of_bound (∑ r ∈ Finset.range (n + 1), 2 * |dsC n r|) ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have hrpow : t ^ (-(n : ℝ) - 2) = t ^ (-(n : ℤ) - 2) := by
    rw [show (-(n : ℝ) - 2) = (((-(n : ℤ) - 2 : ℤ)) : ℝ) from by push_cast; ring,
        Real.rpow_intCast]
  have hzpos : (0 : ℝ) < t ^ (-(n : ℤ) - 2) := zpow_pos ht _
  have hf_int : IntegrableOn (fun u : ℝ => σ u * mixedDerivExpr n u t) (Set.Ici (0 : ℝ)) :=
    integrable_sigma_mixedDerivExpr n t
  have hg_int : IntegrableOn (jMajorant n t) (Set.Ici (0 : ℝ)) := integrableOn_jMajorant n ht
  calc ‖∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr n u t‖
      ≤ ∫ u in Set.Ici (0 : ℝ), ‖σ u * mixedDerivExpr n u t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Set.Ici (0 : ℝ), jMajorant n t u :=
        setIntegral_mono_on hf_int.norm hg_int measurableSet_Ici
          (fun u hu => norm_sigma_mixedDerivExpr_le n ht (Set.mem_Ici.mp hu))
    _ ≤ (∑ r ∈ Finset.range (n + 1), 2 * |dsC n r|) * t ^ (-(n : ℤ) - 2) :=
        integral_jMajorant_le n ht
    _ = (∑ r ∈ Finset.range (n + 1), 2 * |dsC n r|) * ‖t ^ (-(n : ℝ) - 2)‖ := by
        rw [hrpow, Real.norm_eq_abs, abs_of_pos hzpos]

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

/-- `α_part` itself is `O(t⁻¹)` at `+∞` — the `n = 0` companion of
    `iteratedDeriv_α_part_isO`.  Elementary:  `log(1+x) ≤ x` and
    `arctan x ≤ x` for `x ≥ 0` give `0 ≤ α_part t ≤ 3/(16t)`. -/
lemma α_part_isO : IsO α_part (fun t => t ^ (-1 : ℝ)) 𝓝∞ := by
  refine IsBigO.of_bound (3 / 16) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have h_inner_pos : (0 : ℝ) < 1 + 1 / (4 * t ^ 2) := by positivity
  -- Elementary upper bounds for the two summands.
  have h_log_le : Real.log (1 + 1 / (4 * t ^ 2)) ≤ 1 / (4 * t ^ 2) := by
    have := Real.log_le_sub_one_of_pos h_inner_pos
    linarith
  have h_log_nn : 0 ≤ Real.log (1 + 1 / (4 * t ^ 2)) :=
    Real.log_nonneg (by linarith [show (0:ℝ) ≤ 1 / (4 * t ^ 2) by positivity])
  have h_arc_nn : 0 ≤ Real.arctan (1 / (2 * t)) :=
    Real.arctan_nonneg.mpr (by positivity)
  have h_arc_le : Real.arctan (1 / (2 * t)) ≤ 1 / (2 * t) := by
    calc Real.arctan (1 / (2 * t))
        ≤ Real.tan (Real.arctan (1 / (2 * t))) :=
          Real.le_tan h_arc_nn (Real.arctan_lt_pi_div_two _)
      _ = 1 / (2 * t) := Real.tan_arctan _
  -- `0 ≤ α_part t ≤ 1/(16t) + 1/(8t) = (3/16) · t⁻¹`.
  have h_b1 : t / 4 * Real.log (1 + 1 / (4 * t ^ 2)) ≤ 1 / (16 * t) := by
    have h := mul_le_mul_of_nonneg_left h_log_le
      (by positivity : (0 : ℝ) ≤ t / 4)
    have h_eq : t / 4 * (1 / (4 * t ^ 2)) = 1 / (16 * t) := by
      field_simp; ring
    linarith [h_eq ▸ h]
  have h_b2 : 1 / 4 * Real.arctan (1 / (2 * t)) ≤ 1 / (8 * t) := by
    have h := mul_le_mul_of_nonneg_left h_arc_le
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h_eq : (1 : ℝ) / 4 * (1 / (2 * t)) = 1 / (8 * t) := by
      field_simp; ring
    linarith [h_eq ▸ h]
  have h_nn : 0 ≤ α_part t := by
    unfold α_part
    have h1 : 0 ≤ t / 4 * Real.log (1 + 1 / (4 * t ^ 2)) :=
      mul_nonneg (by positivity) h_log_nn
    have h2 : 0 ≤ 1 / 4 * Real.arctan (1 / (2 * t)) :=
      mul_nonneg (by norm_num) h_arc_nn
    linarith
  -- Normalize the `rpow` and conclude.
  have h_pow : t ^ (-1 : ℝ) = t⁻¹ := by
    have := rpow_neg_nat_eq_inv ht_pos 1
    norm_num at this
    simpa using this
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_nn, h_pow,
      abs_of_pos (by positivity : (0 : ℝ) < t⁻¹)]
  have h_sum : α_part t ≤ 1 / (16 * t) + 1 / (8 * t) := by
    unfold α_part; linarith
  have h_total : 1 / (16 * t) + 1 / (8 * t) = 3 / 16 * t⁻¹ := by
    field_simp; ring
  linarith [h_total ▸ h_sum]

/-- `δ` itself is `O(t⁻¹)` at `+∞` — the `n = 0` case of the paper's
    `δ^(n)(t) = O(t^(−n−1))`.  This is the input for the leading-order
    `θ`-asymptotic (fact (θ1) of the Gram-asymptotics blueprint) in
    `Corollary2.lean`. -/
lemma δ_isO : IsO δ (fun t => t ^ (-1 : ℝ)) 𝓝∞ := by
  -- (1) `j = O(t⁻²)` — the `n = 0` case of `iteratedDeriv_j_isO`.
  have h_j : IsO j (fun t => t ^ (-(0 : ℕ) - 2 : ℝ)) 𝓝∞ := by
    have := iteratedDeriv_j_isO 0
    simpa [iteratedDeriv_zero] using this
  -- (2) `(t/2)·j = O(t · t⁻²) = O(t⁻¹)`.
  have h_tj : IsO (fun t => t / 2 * j t) (fun t => t ^ (-1 : ℝ)) 𝓝∞ := by
    have h_half : IsO (fun t : ℝ => t / 2) (fun t : ℝ => t) 𝓝∞ := by
      have h := (Asymptotics.isBigO_refl (fun t : ℝ => t) 𝓝∞).const_mul_left (1 / 2)
      exact h.congr_left fun t => by ring
    have h_mul := h_half.mul h_j
    refine h_mul.trans_eventuallyEq ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have h1 : t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
    rw [show (-(0 : ℕ) - 2 : ℝ) = -2 by norm_num]
    calc t * t ^ (-2 : ℝ) = t ^ (1 : ℝ) * t ^ (-2 : ℝ) := by rw [← h1]
      _ = t ^ ((1 : ℝ) + -2) := (Real.rpow_add ht 1 (-2)).symm
      _ = t ^ (-1 : ℝ) := by norm_num
  -- (3) Combine along `δ = α_part − (t/2)·j` (valid for `t > 0`).
  have h_sub := α_part_isO.sub h_tj
  have h_evEq : δ =ᶠ[Filter.atTop] (fun t => α_part t - t / 2 * j t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact δ_eq t ht
  exact h_evEq.trans_isBigO h_sub

/-!
  ## §7a  Pointwise bounds:  `|j t| ≤ 1/(2t²)` and `|δ'(t)| ≤ 1/t²`

  The §7 bounds are asymptotic (`IsO` at `𝓝∞`), i.e. only *eventual*.
  This section extracts from the same σ-integration-by-parts machinery
  **explicit pointwise** bounds valid for every `t > 0` — the input for
  the strict monotonicity of the Riemann–Siegel `θ` on `[7, ∞)`
  (`strictMonoOn_theta` in `Corollary2.lean`), where an eventual bound
  says nothing about any concrete `t`.

  Chain (throughout `t > 0`, `m_n := mixedDerivExpr n`):

    1. `m₀ ≤ 0 ≤ m₁` pointwise on `u ≥ 0` (signs of `lorMix 0/1`);
    2. `∫_{u≥0} m₀ = −kernel 0 t` and `∫_{u≥0} m₁ = 128t/(1+4t²)²`
       (improper FTC with antiderivative `u ↦ ∂ₜⁿ kernel(u,t)`, via
       `hasDerivAt_iteratedDeriv_kernel`);
    3. `|jK n t| = |∫ σ·m_n| ≤ (1/8)·|∫ m_n|`  (`0 ≤ σ ≤ 1/8` and the
       sign constancy from step 1);
    4. `|j t| ≤ 1/(2t²)` and `|jK 1 t| ≤ 1/t³`;
    5. product rule along `δ = α_part − (t/2)·j`  ⟹  `|δ'(t)| ≤ 1/t²`.
-/

/-- Closed form of the derivative of `lorSq`:  `(lor²)'(s) = −4s·(lor s)³`. -/
private lemma hasDerivAt_lorSq (s : ℝ) :
    HasDerivAt lorSq (-(4 * s) * lor s ^ 3) s := by
  unfold lorSq
  convert (hasDerivAt_lor s).pow 2 using 1
  ring

/-- Closed form `lorMix 1 s = 8s·(lor s)³` — via
    `lorMix 1 = −2·(lor²)'` (`lorMix_eq_iteratedDeriv_lorSq`). -/
private lemma lorMix_one (s : ℝ) : lorMix 1 s = 8 * s * lor s ^ 3 := by
  rw [lorMix_eq_iteratedDeriv_lorSq, iteratedDeriv_one, (hasDerivAt_lorSq s).deriv]
  ring

/-- Sign of the order-`0` mixed integrand:  `∂ᵤ kernel(u,t) ≤ 0` for
    `u ≥ 0` (the kernel decreases in `u`). -/
private lemma mixedDerivExpr_zero_nonpos {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    mixedDerivExpr 0 u t ≤ 0 := by
  rw [mixedDerivExpr_eq_lorMix 0 hu t, lorMix_zero]
  have hr : (0 : ℝ) < u + 1 / 4 := by linarith
  have h_zpow : (0 : ℝ) < (u + 1 / 4) ^ (-(((0 : ℕ) : ℤ) + 3)) := zpow_pos hr _
  have h_lorSq : 0 ≤ lorSq ((1 / (2 * (u + 1 / 4))) * t) := by
    unfold lorSq; positivity
  nlinarith [h_zpow, h_lorSq]

/-- Sign of the order-`1` mixed integrand:  `∂ᵤ ∂ₜ kernel(u,t) ≥ 0` for
    `u ≥ 0`, `t ≥ 0`. -/
private lemma mixedDerivExpr_one_nonneg {u : ℝ} (hu : 0 ≤ u) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mixedDerivExpr 1 u t := by
  rw [mixedDerivExpr_eq_lorMix 1 hu t, lorMix_one]
  have hr : (0 : ℝ) < u + 1 / 4 := by linarith
  have h_zpow : (0 : ℝ) < (u + 1 / 4) ^ (-(((1 : ℕ) : ℤ) + 3)) := zpow_pos hr _
  have h_lor : 0 < lor ((1 / (2 * (u + 1 / 4))) * t) := by
    unfold lor
    positivity
  have h_arg : 0 ≤ (1 / (2 * (u + 1 / 4))) * t := by positivity
  positivity

/-- `u ↦ mixedDerivExpr n u t` is integrable on `[0, ∞)`:  continuous
    (`continuousOn_mixedDerivExpr`) and dominated by `C·((u+1/4)^{n+3})⁻¹`
    (`exists_bound_mixedDerivExpr`). -/
private lemma integrableOn_mixedDerivExpr (n : ℕ) {t : ℝ} (_ht : 0 ≤ t) :
    IntegrableOn (fun u : ℝ => mixedDerivExpr n u t) (Set.Ici (0 : ℝ)) := by
  obtain ⟨C, _, hC⟩ := exists_bound_mixedDerivExpr n |t|
  refine integrableOn_Ici_of_pow_inv_dominated (n + 1) C
    ((continuousOn_mixedDerivExpr n t).aestronglyMeasurable measurableSet_Ici) ?_
  intro u hu
  rw [show (n + 1) + 2 = n + 3 from rfl, Real.norm_eq_abs]
  exact hC u (Set.mem_Ici.mp hu) t (le_refl _)

/-- **Improper FTC evaluation at kernel-order `0`:**
    `∫_{u≥0} ∂ᵤ kernel(u,t) du = −kernel 0 t`, the antiderivative being
    `u ↦ kernel u t` (which vanishes at `+∞`). -/
private lemma integral_mixedDerivExpr_zero {t : ℝ} (ht : 0 < t) :
    ∫ u in Set.Ici (0 : ℝ), mixedDerivExpr 0 u t = -kernel 0 t := by
  have h_int : IntegrableOn (fun u : ℝ => mixedDerivExpr 0 u t) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_mixedDerivExpr 0 ht.le).mono_set Set.Ioi_subset_Ici_self
  have h_cont : ContinuousWithinAt (fun u : ℝ => kernel u t) (Set.Ici (0 : ℝ)) 0 := by
    have h := (continuousOn_iteratedDeriv_kernel 0 t) 0 Set.self_mem_Ici
    simpa [iteratedDeriv_zero] using h
  have h_deriv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun v : ℝ => kernel v t) (mixedDerivExpr 0 u t) u := by
    intro u hu
    have h := hasDerivAt_iteratedDeriv_kernel 0 (Set.mem_Ioi.mp hu) t
    simpa [iteratedDeriv_zero] using h
  have h_denom : Filter.Tendsto (fun u : ℝ => (u + 1 / 4) ^ 2 + (t / 2) ^ 2)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id))
  have h_tendsto : Filter.Tendsto (fun u : ℝ => kernel u t) Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.div_atTop
      (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop)) h_denom
    simpa [kernel] using h
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have h_eval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    h_cont h_deriv h_int h_tendsto
  rw [h_eval]
  ring

/-- `|lor'(s)| ≤ 1`:  `|−2s·(lor s)²| = 2|s|/(1+s²)² ≤ 1` since
    `2|s| ≤ 1 + s² ≤ (1+s²)²`. -/
private lemma abs_iteratedDeriv_one_lor_le (s : ℝ) : |iteratedDeriv 1 lor s| ≤ 1 := by
  rw [iteratedDeriv_one, (hasDerivAt_lor s).deriv]
  have h_denom : (0 : ℝ) < 1 + s ^ 2 := lor_denom_pos s
  have h_2s : 2 * |s| ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg (|s| - 1), sq_abs s]
  have h_eq : -(2 * s) * lor s ^ 2 = -(2 * s) / (1 + s ^ 2) ^ 2 := by
    unfold lor
    field_simp
  rw [h_eq, abs_div, abs_neg, abs_mul, abs_two,
      abs_of_pos (by positivity : (0 : ℝ) < (1 + s ^ 2) ^ 2),
      div_le_one (by positivity)]
  calc 2 * |s| ≤ 1 + s ^ 2 := h_2s
    _ ≤ (1 + s ^ 2) ^ 2 := by nlinarith [sq_nonneg s]

/-- **Improper FTC evaluation at kernel-order `1`:**
    `∫_{u≥0} ∂ᵤ ∂ₜ kernel(u,t) du = 128t/(1+4t²)²`, the antiderivative
    being `u ↦ ∂ₜ kernel(u,t)` (which vanishes at `+∞` and equals
    `−128t/(1+4t²)²` at `u = 0`). -/
private lemma integral_mixedDerivExpr_one {t : ℝ} (ht : 0 < t) :
    ∫ u in Set.Ici (0 : ℝ), mixedDerivExpr 1 u t
      = 128 * t / (1 + 4 * t ^ 2) ^ 2 := by
  have h_int : IntegrableOn (fun u : ℝ => mixedDerivExpr 1 u t) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_mixedDerivExpr 1 ht.le).mono_set Set.Ioi_subset_Ici_self
  have h_cont : ContinuousWithinAt
      (fun u : ℝ => iteratedDeriv 1 (fun s => kernel u s) t) (Set.Ici (0 : ℝ)) 0 :=
    (continuousOn_iteratedDeriv_kernel 1 t) 0 Set.self_mem_Ici
  have h_deriv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun v : ℝ => iteratedDeriv 1 (fun s => kernel v s) t)
        (mixedDerivExpr 1 u t) u :=
    fun u hu => hasDerivAt_iteratedDeriv_kernel 1 (Set.mem_Ioi.mp hu) t
  -- The antiderivative tends to `0`:  `|F₁ u| ≤ 2·((u+1/4)²)⁻¹ → 0`.
  have h_tendsto : Filter.Tendsto
      (fun u : ℝ => iteratedDeriv 1 (fun s => kernel u s) t) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun u : ℝ => 2 * ((u + 1 / 4) ^ 2)⁻¹)
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
      have hr : (0 : ℝ) < u + 1 / 4 := by linarith
      rw [Real.norm_eq_abs, iteratedDeriv_kernel 1 hu t, pow_one, abs_mul, abs_mul,
          abs_of_pos (inv_pos.mpr (pow_pos hr 2)),
          abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (u + 1 / 4)))]
      have h_lor := abs_iteratedDeriv_one_lor_le ((1 / (2 * (u + 1 / 4))) * t)
      have h_half_le : 1 / (2 * (u + 1 / 4)) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      calc ((u + 1 / 4) ^ 2)⁻¹ * (1 / (2 * (u + 1 / 4)))
              * |iteratedDeriv 1 lor ((1 / (2 * (u + 1 / 4))) * t)|
          ≤ ((u + 1 / 4) ^ 2)⁻¹ * 2 * 1 := by
            gcongr
        _ = 2 * ((u + 1 / 4) ^ 2)⁻¹ := by ring
    · have h_sq : Filter.Tendsto (fun u : ℝ => (u + 1 / 4) ^ 2)
          Filter.atTop Filter.atTop :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
          (Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id)
      have h := Filter.Tendsto.div_atTop
        (tendsto_const_nhds (x := (2 : ℝ)) (f := Filter.atTop)) h_sq
      simpa [div_eq_mul_inv] using h
  -- Value of the antiderivative at `u = 0`.
  have h_f0 : iteratedDeriv 1 (fun s => kernel (0 : ℝ) s) t
      = -(128 * t / (1 + 4 * t ^ 2) ^ 2) := by
    rw [iteratedDeriv_kernel 1 le_rfl t, iteratedDeriv_one, (hasDerivAt_lor _).deriv]
    have h_ne : (1 + (1 / (2 * ((0 : ℝ) + 1 / 4)) * t) ^ 2 : ℝ) ≠ 0 := by positivity
    unfold lor
    field_simp
    ring
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have h_eval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    h_cont h_deriv h_int h_tendsto
  rw [h_eval, h_f0]
  ring

/-- **Explicit pointwise bound for `j`:**  `|j t| ≤ 1/(2t²)` for every
    `t > 0` (the `n = 0` case of the paper's `δ`-machinery bounds, with
    explicit constant).  Via `j = −∫ σ·m₀`, `0 ≤ σ ≤ 1/8`, `m₀ ≤ 0`, and
    `∫(−m₀) = kernel 0 t ≤ 4/t²`. -/
lemma abs_j_le {t : ℝ} (ht : 0 < t) : |j t| ≤ 1 / (2 * t ^ 2) := by
  have h_eq : j t = -∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr 0 u t := by
    rw [← jK_zero]
    exact jK_eq_sigma_integral 0 ht
  rw [h_eq, abs_neg]
  have h_int_σm : IntegrableOn (fun u : ℝ => σ u * mixedDerivExpr 0 u t)
      (Set.Ici (0 : ℝ)) := integrable_sigma_mixedDerivExpr 0 t
  have h_int_m : IntegrableOn (fun u : ℝ => mixedDerivExpr 0 u t) (Set.Ici (0 : ℝ)) :=
    integrableOn_mixedDerivExpr 0 ht.le
  have h_ptwise : ∀ u ∈ Set.Ici (0 : ℝ),
      |σ u * mixedDerivExpr 0 u t| ≤ (1 / 8) * (-mixedDerivExpr 0 u t) := by
    intro u hu
    have h_m := mixedDerivExpr_zero_nonpos (Set.mem_Ici.mp hu) t
    rw [abs_mul, abs_of_nonneg (σ_nonneg u), abs_of_nonpos h_m]
    exact mul_le_mul_of_nonneg_right (σ_le_eighth u) (by linarith)
  calc |∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr 0 u t|
      ≤ ∫ u in Set.Ici (0 : ℝ), |σ u * mixedDerivExpr 0 u t| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Ici (0 : ℝ), (1 / 8) * (-mixedDerivExpr 0 u t) :=
        MeasureTheory.setIntegral_mono_on h_int_σm.abs
          ((h_int_m.neg).const_mul _) measurableSet_Ici h_ptwise
    _ = (1 / 8) * (-∫ u in Set.Ici (0 : ℝ), mixedDerivExpr 0 u t) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_neg]
    _ = (1 / 8) * kernel 0 t := by rw [integral_mixedDerivExpr_zero ht]; ring
    _ ≤ 1 / (2 * t ^ 2) := by
        unfold kernel
        have h_denom_pos : (0 : ℝ) < ((0 : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2 := by positivity
        have h_ge : t ^ 2 / 4 ≤ ((0 : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2 := by nlinarith
        calc (1 / 8 : ℝ) * (1 / (((0 : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2))
            ≤ (1 / 8 : ℝ) * (1 / (t ^ 2 / 4)) := by
              gcongr
          _ = 1 / (2 * t ^ 2) := by
              field_simp
              ring

/-- **Explicit pointwise bound for `j' = jK 1`:**  `|jK 1 t| ≤ 1/t³` for
    every `t > 0`.  Via `jK 1 = −∫ σ·m₁`, `0 ≤ σ ≤ 1/8`, `m₁ ≥ 0`, and
    `∫ m₁ = 128t/(1+4t²)² ≤ 8/t³`. -/
private lemma abs_jK_one_le {t : ℝ} (ht : 0 < t) : |jK 1 t| ≤ 1 / t ^ 3 := by
  rw [jK_eq_sigma_integral 1 ht, abs_neg]
  have h_int_σm : IntegrableOn (fun u : ℝ => σ u * mixedDerivExpr 1 u t)
      (Set.Ici (0 : ℝ)) := integrable_sigma_mixedDerivExpr 1 t
  have h_int_m : IntegrableOn (fun u : ℝ => mixedDerivExpr 1 u t) (Set.Ici (0 : ℝ)) :=
    integrableOn_mixedDerivExpr 1 ht.le
  have h_ptwise : ∀ u ∈ Set.Ici (0 : ℝ),
      |σ u * mixedDerivExpr 1 u t| ≤ (1 / 8) * mixedDerivExpr 1 u t := by
    intro u hu
    have h_m := mixedDerivExpr_one_nonneg (Set.mem_Ici.mp hu) ht.le
    rw [abs_mul, abs_of_nonneg (σ_nonneg u), abs_of_nonneg h_m]
    exact mul_le_mul_of_nonneg_right (σ_le_eighth u) h_m
  calc |∫ u in Set.Ici (0 : ℝ), σ u * mixedDerivExpr 1 u t|
      ≤ ∫ u in Set.Ici (0 : ℝ), |σ u * mixedDerivExpr 1 u t| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Ici (0 : ℝ), (1 / 8) * mixedDerivExpr 1 u t :=
        MeasureTheory.setIntegral_mono_on h_int_σm.abs
          (h_int_m.const_mul _) measurableSet_Ici h_ptwise
    _ = (1 / 8) * (128 * t / (1 + 4 * t ^ 2) ^ 2) := by
        rw [MeasureTheory.integral_const_mul, integral_mixedDerivExpr_one ht]
    _ = 16 * t / (1 + 4 * t ^ 2) ^ 2 := by ring
    _ ≤ 1 / t ^ 3 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), pow_pos ht 4]

/-- Derivative decomposition of `δ` at any `t > 0`:
    `δ'(t) = α_part'(t) − ((1/2)·j t + (t/2)·jK 1 t)`, by the product
    rule along `δ = α_part − (·/2)·j` (`δ_eq`). -/
private lemma hasDerivAt_δ {t : ℝ} (ht : 0 < t) :
    HasDerivAt δ
      ((1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) - 1 / (4 * t ^ 2 + 1)
        - (1 / 2 * j t + t / 2 * jK 1 t)) t := by
  have h_j : HasDerivAt j (jK 1 t) t := by
    have h := hasDerivAt_jK 0 ht
    rwa [jK_zero] at h
  have h_half : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
  have h_tj : HasDerivAt (fun s : ℝ => s / 2 * j s) (1 / 2 * j t + t / 2 * jK 1 t) t :=
    h_half.mul h_j
  have h_sub := (hasDerivAt_α_part ht).sub h_tj
  refine h_sub.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  exact δ_eq s hs

/-- Explicit bound for the closed-form `α_part'`:
    `|α_part'(t)| ≤ 1/(4t²)` for `t > 0` — both summands of
    `(1/4)·log(1+1/(4t²)) − 1/(4t²+1)` lie in `[0, 1/(4t²)]`. -/
private lemma abs_α_deriv_le {t : ℝ} (ht : 0 < t) :
    |(1 / 4) * Real.log (1 + 1 / (4 * t ^ 2)) - 1 / (4 * t ^ 2 + 1)|
      ≤ 1 / (4 * t ^ 2) := by
  have h_x_pos : (0 : ℝ) < 1 / (4 * t ^ 2) := by positivity
  have h_log_le : Real.log (1 + 1 / (4 * t ^ 2)) ≤ 1 / (4 * t ^ 2) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 1 / (4 * t ^ 2))
    linarith
  have h_log_nn : 0 ≤ Real.log (1 + 1 / (4 * t ^ 2)) :=
    Real.log_nonneg (by linarith)
  have h_inv_le : 1 / (4 * t ^ 2 + 1) ≤ 1 / (4 * t ^ 2) := by
    gcongr
    linarith
  have h_inv_nn : (0 : ℝ) ≤ 1 / (4 * t ^ 2 + 1) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **Explicit pointwise bound for `δ'`** — the `n = 1` case of the
    paper's `δ^{(n)}(t) = O(t^{−n−1})` with explicit constant `1`:

        `|δ'(t)| ≤ 1/t²`   for every `t > 0`.

    Unlike `iteratedDeriv_δ_isO` this is not merely eventual; it is the
    input for the strict monotonicity of `θ` on `[7, ∞)` proved in
    `Corollary2.lean` (`strictMonoOn_theta`). -/
lemma abs_deriv_δ_le {t : ℝ} (ht : 0 < t) : |deriv δ t| ≤ 1 / t ^ 2 := by
  rw [(hasDerivAt_δ ht).deriv]
  have h_α := abs_le.mp (abs_α_deriv_le ht)
  have h_B : |1 / 2 * j t| ≤ 1 / (4 * t ^ 2) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc (1 / 2 : ℝ) * |j t| ≤ (1 / 2) * (1 / (2 * t ^ 2)) := by
          gcongr
          exact abs_j_le ht
      _ = 1 / (4 * t ^ 2) := by ring
  have h_C : |t / 2 * jK 1 t| ≤ 1 / (2 * t ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t / 2)]
    calc t / 2 * |jK 1 t| ≤ t / 2 * (1 / t ^ 3) := by
          gcongr
          exact abs_jK_one_le ht
      _ = 1 / (2 * t ^ 2) := by
          field_simp
  have h_B' := abs_le.mp h_B
  have h_C' := abs_le.mp h_C
  have h_id : 1 / (4 * t ^ 2) + (1 / (4 * t ^ 2) + 1 / (2 * t ^ 2)) = 1 / t ^ 2 := by
    field_simp
    ring
  rw [abs_le]
  constructor <;> linarith [h_α.1, h_α.2, h_B'.1, h_B'.2, h_C'.1, h_C'.2]

end ErrorTermDelta

/-!
  ## §8  Main theorem: Theorem 1
-/

/-- **Theorem 1** (Dundulis–Garunkštis–Laurinčikas–Šimenas, 2026).

    For every step function `F` and n ≥ 2, the n-th derivative of `S F`
    satisfies

        (S F)^(n)(t) = (-1)^(n-1) · (n-2)! / (2π) · t^(1-n)  +  O(t^(-n-1))

    as t → +∞ *through regular points* (i.e., points not in `F.jumpSet`).
    The conclusion is stated at the relativized filter `𝓝∞₀[F.jumpSet]`,
    which is the natural mathematical filter here: at a jump point of `F`
    (and hence of `S F`), `iteratedDeriv n (S F)` returns `0` by Mathlib's
    convention for non-differentiable points, so the asymptotic fails
    at such points by `O(t^(1-n))` — much larger than the claimed
    `O(t^(-n-1))`.  The filter is nontrivial by
    `StepFunction.neBot_regularAtTop`. -/
theorem theorem1 (F : StepFunction) (n : ℕ) (hn : 2 ≤ n) :
    IsO
      (fun t =>
        iteratedDeriv n (S F) t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ))))
      (fun t => t ^ (-(n : ℝ) - 1))
      𝓝∞₀[F.jumpSet] := by
  have hn1 : 1 ≤ n := by omega
  -- (1) Pointwise rewrite of S F on (0,∞), in addition-of-negation form so we
  -- can use `iteratedDeriv_add` rather than `iteratedDeriv_sub`.
  have h_S_sum : ∀ s ∈ Set.Ioi (0 : ℝ),
      S F s = φ s + ((-(1 / Real.pi)) * δ s) + F s := by
    intro s _; rw [S_eq_φ_sub_δ_add_N F s]; ring
  -- (2) Lift the pointwise equality to iteratedDeriv on the open set (0,∞).
  have h_iter_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      iteratedDeriv n (S F) t
        = iteratedDeriv n
            (fun s => φ s + ((-(1 / Real.pi)) * δ s) + F s) t :=
    iteratedDeriv_congr_of_nhds n isOpen_Ioi h_S_sum
  -- (3) Split the triple sum using local ContDiffAt — requires regularity
  -- (`t ∉ F.jumpSet`) since `F` is only `ContDiffAt` away from its jumps.
  have h_split : ∀ t, 0 < t → t ∉ F.jumpSet →
      iteratedDeriv n (fun s => φ s + ((-(1 / Real.pi)) * δ s) + F s) t
        = iteratedDeriv n φ t
          + (-(1 / Real.pi)) * iteratedDeriv n δ t
          + iteratedDeriv n F t := by
    intro t ht ht_reg
    have hφ  : ContDiffAt ℝ n φ t  := contDiffAt_φ n ht
    have hδ  : ContDiffAt ℝ n δ t  := contDiffAt_δ n ht
    have hN  : ContDiffAt ℝ n F t  := F.contDiffAt n ht_reg
    have hcδ : ContDiffAt ℝ n (fun s => (-(1 / Real.pi)) * δ s) t :=
      contDiffAt_const.mul hδ
    -- Outer split: (φ + c·δ) + F
    change iteratedDeriv n
              ((fun s => φ s + ((-(1 / Real.pi)) * δ s)) + ⇑F) t = _
    rw [iteratedDeriv_add (hφ.add hcδ) hN]
    -- Inner split: φ + c·δ
    have h_inner :
        iteratedDeriv n (fun s => φ s + ((-(1 / Real.pi)) * δ s)) t
          = iteratedDeriv n φ t
            + iteratedDeriv n (fun s => (-(1 / Real.pi)) * δ s) t := by
      change iteratedDeriv n (φ + fun s => (-(1 / Real.pi)) * δ s) t = _
      exact iteratedDeriv_add hφ hcδ
    rw [h_inner, iteratedDeriv_const_mul_field (-(1 / Real.pi)) δ]
  -- (4) Substitute closed form for `φ` and the vanishing for `F` at
  -- regular points.
  have h_clean : ∀ t, 0 < t → t ∉ F.jumpSet →
      iteratedDeriv n (S F) t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ)))
        = (-(1 / Real.pi)) * iteratedDeriv n δ t := by
    intro t ht ht_reg
    rw [h_iter_eq t ht, h_split t ht ht_reg,
        iteratedDeriv_φ n hn t ht,
        F.iteratedDeriv_eq_zero n hn1 ht_reg]
    ring
  -- (5) The residual `c · iteratedDeriv n δ t` is O(t^(-n-1)) on `𝓝∞`; mono
  -- to the smaller `𝓝∞₀[F.jumpSet]`.
  have h_bd :
      IsO (fun t => (-(1 / Real.pi)) * iteratedDeriv n δ t)
          (fun t => t ^ (-(n : ℝ) - 1)) 𝓝∞₀[F.jumpSet] :=
    ((iteratedDeriv_δ_isO n hn1).const_mul_left (-(1 / Real.pi))).mono inf_le_left
  -- (6) Stitch via eventual equality at `𝓝∞₀[F.jumpSet]`.
  have h_evEq :
      (fun t => iteratedDeriv n (S F) t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ))))
        =ᶠ[𝓝∞₀[F.jumpSet]]
      (fun t => (-(1 / Real.pi)) * iteratedDeriv n δ t) := by
    have h_pos : ∀ᶠ t in (𝓝∞₀[F.jumpSet] : Filter ℝ), 0 < t :=
      (Filter.eventually_gt_atTop (0 : ℝ)).filter_mono inf_le_left
    have h_reg : ∀ᶠ t in (𝓝∞₀[F.jumpSet] : Filter ℝ), t ∉ F.jumpSet :=
      Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun _ h => h))
    filter_upwards [h_pos, h_reg] with t ht ht_reg
    exact h_clean t ht ht_reg
  exact h_evEq.trans_isBigO h_bd
