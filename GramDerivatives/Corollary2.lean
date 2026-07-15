/-
  GramDerivatives/Corollary2.lean
  ===============================
  Lean 4 / Mathlib formalisation of **Corollary 2** from

      Dundulis, Garunkštis, Laurinčikas, Šimenas,
      "Higher derivatives of the Gram function", 2026.

  Corollary 2.  For n ≥ 2, as t → +∞,

      θ^(n)(t) = (-1)^n · (n-2)! / 2 · t^(1-n) + O(t^(-n-1)),

  where θ is the Riemann–Siegel theta function.

  ─── Strategy ──────────────────────────────────────────────────────────
  We bypass `theorem1` entirely.  Theorem 1's conclusion is at the
  relativized filter `𝓝∞₀[F.jumpSet]` (= `Filter.atTop ⊓ principal
  F.jumpSetᶜ`), because at a jump point of the step function `F` the
  function `S F` has a jump too and the asymptotic for
  `iteratedDeriv n (S F)` genuinely fails.  By contrast,
  `theta := δ − π·φ − π` is *smooth on all of `(0, ∞)`* — it doesn't
  involve any step function — so its asymptotic holds at the
  unrelativized filter `𝓝∞`.

  Concretely, for `n ≥ 1` and `t > 0`:

      iteratedDeriv n theta t = iteratedDeriv n δ t − π · iteratedDeriv n φ t,

  obtained by splitting the constant `−π` via `iteratedDeriv_const_eq_zero`
  and the product `π · φ` via `iteratedDeriv_const_mul'`.  Substituting
  the closed form `iteratedDeriv n φ t = (−1)^(n−1) · (n−2)! / (2π) · t^(1−n)`
  from `Theorem1.lean`, the leading-term contribution from `−π · φ^(n)`
  combines with the sign flip `(−1)^(n−1) → (−1)^n` to produce the
  Corollary 2 main term.  The remainder is `iteratedDeriv n δ t`, which
  is `O(t^(−n−1))` by `iteratedDeriv_δ_isO`.

  ─── What's axiomatised ────────────────────────────────────────────────
  Nothing.  `theta` is *defined* by

      theta t := δ t − π · φ t − π,

  the closed form obtained by solving the Riemann–von Mangoldt identity
  `N(t) = (1/π)·θ(t) + 1 + S(t)` for θ and substituting
  `S F = φ − (1/π)·δ + F` (from `Theorem1.lean`); the step-function
  terms cancel algebraically.  Smoothness (`contDiffAt_theta`) follows
  from `contDiffAt_δ` and `contDiffAt_φ`.

  The agreement of this `theta` with the analytic Riemann–Siegel theta
  function on `(0, ∞)` is informal — it is the content of the
  Karatsuba–Korolev representation.

  §5 additionally proves `theta_tendsto_atTop` (θ → +∞ at +∞), the
  existence input that lets `Theorem3.lean` *define* the Gram function
  as an inverse of `theta` instead of axiomatising it.

  Builds with zero `sorry`.
-/

import GramDerivatives.Theorem1

open Real Filter Asymptotics
open scoped ContDiff

/-!
  ## §1  The Riemann–Siegel theta function

  `theta : ℝ → ℝ` is *defined* as `δ − π·φ − π`, the closed form obtained
  by solving the Riemann–von Mangoldt identity for θ and substituting
  `S F = φ − (1/π)·δ + F` from `Theorem1.lean`.  Under this definition:

    • `contDiffAt_theta`  is a derived theorem (from smoothness of `φ`
      and `δ`).
    • `riemann_vonMangoldt` reduces, for every step function `F`, to an
      algebraic identity in which the `F t` terms cancel between the two
      sides; the identity then closes by `field_simp` + `ring`.

  The agreement of this `theta` with the analytic Riemann–Siegel theta
  function on `(0, ∞)` is the content of the Karatsuba–Korolev
  representation; that agreement is informal and not formalised here.
-/

/-- The Riemann–Siegel theta function, defined as the closed form
    `θ(t) := δ(t) − π · φ(t) − π` obtained from the Karatsuba–Korolev /
    Riemann–von Mangoldt identity combined with `S F = φ − (1/π)·δ + F`
    (from `Theorem1.lean`).  Identifies on `(0, ∞)` with the continuous
    branch of `arg(π^(-s/2) · Γ(s/2))` along the segment from `s = 1/2`
    to `s = 1/2 + i t`. -/
noncomputable def theta (t : ℝ) : ℝ := δ t - Real.pi * φ t - Real.pi

/-- `θ` is `C^∞` on `(0, ∞)` — derived from the smoothness of `δ` and
    `φ` and closure of `ContDiffAt` under `sub` and `const_mul`. -/
theorem contDiffAt_theta (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n theta s := by
  unfold theta
  exact ((contDiffAt_δ n hs).sub
    (contDiffAt_const.mul (contDiffAt_φ n hs))).sub contDiffAt_const

/-- The Riemann–von Mangoldt / Karatsuba–Korolev identity (equation (1)
    of the paper):

        N(t) = (1/π) · θ(t) + 1 + S(t).

    Under the definitions `theta := δ − π·φ − π` and
    `S F := φ − (1/π)·δ + F` (from `Theorem1.lean`), this reduces to
    a purely algebraic identity in `δ t`, `φ t`, `F t`, and `π`:
    the `F t` terms cancel between the two sides.  It holds for *every*
    step function `F` — no `StepFunction` field is used. -/
theorem riemann_vonMangoldt (F : StepFunction) (t : ℝ) (_ht : 0 < t) :
    F t = (1 / Real.pi) * theta t + 1 + S F t := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [theta, S]
  field_simp
  ring

/-!
  ## §2  Auxiliary lemmas

  Two helpers not available outside `Theorem1.lean`:
    • `iteratedDeriv` of a constant vanishes after the first derivative;
    • `iteratedDeriv` commutes with a constant scalar factor.
  The second duplicates a `private` helper in `Theorem1.lean`.
-/

/-- The n-th iterated derivative of a constant function (`n ≥ 1`) is zero. -/
private lemma iteratedDeriv_const_eq_zero {n : ℕ} (hn : 1 ≤ n)
    (c : ℝ) (t : ℝ) : iteratedDeriv n (fun _ : ℝ => c) t = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [iteratedDeriv_succ']
  have h_deriv : deriv (fun _ : ℝ => c) = fun _ : ℝ => 0 :=
    funext fun x => deriv_const x c
  rw [h_deriv]
  clear hn
  induction m generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have h_deriv0 : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ : ℝ => 0 :=
      funext fun x => deriv_const x (0 : ℝ)
    rw [h_deriv0]
    exact ih t

/-- Iterated derivative commutes with a constant scalar factor.
    Duplicates the private helper from `Theorem1.lean`. -/
private lemma iteratedDeriv_const_mul' (c : ℝ) (g : ℝ → ℝ) (k : ℕ) (s : ℝ) :
    iteratedDeriv k (fun x => c * g x) s = c * iteratedDeriv k g s := by
  induction k generalizing s with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hEq : iteratedDeriv k (fun x => c * g x) = fun x => c * iteratedDeriv k g x :=
      funext ih
    rw [hEq, deriv_const_mul_field']

/-!
  ## §3  Splitting `iteratedDeriv n theta`

  For `n ≥ 1` and `t > 0`, the iterated derivative of `theta := δ − π·φ − π`
  splits into

      iteratedDeriv n theta t = iteratedDeriv n δ t − π · iteratedDeriv n φ t.

  No step function is involved — this is purely a Mathlib-calculus
  consequence of the definition of `theta`.
-/

/-- For `n ≥ 1` and `t > 0`,

      θ^(n)(t) = δ^(n)(t) − π · φ^(n)(t).

    Obtained by splitting `theta = (δ − π·φ) − π` through `iteratedDeriv_sub`,
    dropping the constant `−π` via `iteratedDeriv_const_eq_zero`, and
    factoring the `π · φ` term via `iteratedDeriv_const_mul'`. -/
private lemma iteratedDeriv_theta_split (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv n theta t = iteratedDeriv n δ t - Real.pi * iteratedDeriv n φ t := by
  have hδ  : ContDiffAt ℝ n δ t := contDiffAt_δ n ht
  have hφ  : ContDiffAt ℝ n φ t := contDiffAt_φ n ht
  have hπφ : ContDiffAt ℝ n (fun s => Real.pi * φ s) t :=
    contDiffAt_const.mul hφ
  have hδπφ : ContDiffAt ℝ n (fun s => δ s - Real.pi * φ s) t := hδ.sub hπφ
  have hC : ContDiffAt ℝ n (fun _ : ℝ => Real.pi) t := contDiffAt_const
  -- Outer split: (δ − π·φ) − π.
  change iteratedDeriv n
      ((fun s : ℝ => δ s - Real.pi * φ s) - (fun _ : ℝ => Real.pi)) t = _
  rw [iteratedDeriv_sub hδπφ hC,
      iteratedDeriv_const_eq_zero hn Real.pi t,
      sub_zero]
  -- Inner split: δ − (π · φ).
  change iteratedDeriv n (δ - (fun s => Real.pi * φ s)) t = _
  rw [iteratedDeriv_sub hδ hπφ,
      iteratedDeriv_const_mul' Real.pi φ n t]

/-!
  ## §4  Main theorem: Corollary 2

  Substituting the closed form `iteratedDeriv n φ t = (−1)^(n−1) · (n−2)! / (2π) · t^(1−n)`
  into the splitting of §3 and bounding the remainder via `iteratedDeriv_δ_isO`.
-/

/-- **Corollary 2** (Dundulis–Garunkštis–Laurinčikas–Šimenas, 2026).

    For `n ≥ 2`, the `n`-th derivative of the Riemann–Siegel theta
    function satisfies

        θ^(n)(t) = (-1)^n · (n-2)! / 2 · t^(1-n) + O(t^(-n-1))

    as `t → +∞`.  Note: since `theta := δ − π·φ − π` is smooth on the
    entire half-line `(0, ∞)` (no step function), this conclusion is at the
    unrelativized filter `𝓝∞` — *not* at Theorem 1's `𝓝∞₀`. -/
theorem corollary2 (n : ℕ) (hn : 2 ≤ n) :
    IsO
      (fun t =>
        iteratedDeriv n theta t
        - ((-1 : ℝ) ^ n * (n - 2).factorial
           * (1 / 2) * t ^ (1 - (n : ℝ))))
      (fun t => t ^ (-(n : ℝ) - 1))
      𝓝∞ := by
  have hn1 : 1 ≤ n := by omega
  -- (1) Pointwise on (0, ∞), the residual reduces to iteratedDeriv n δ.
  have h_clean : ∀ t, 0 < t →
      iteratedDeriv n theta t
        - ((-1 : ℝ) ^ n * (n - 2).factorial * (1 / 2) * t ^ (1 - (n : ℝ)))
        = iteratedDeriv n δ t := by
    intro t ht
    rw [iteratedDeriv_theta_split n hn1 t ht, iteratedDeriv_φ n hn t ht]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    -- `(-1)^n = -(-1)^(n-1)` for `n ≥ 1`.
    have h_pow : (-1 : ℝ) ^ n = -((-1 : ℝ) ^ (n - 1)) := by
      have hne : (n - 1) + 1 = n := by omega
      conv_lhs => rw [← hne, pow_succ]
      ring
    rw [h_pow]
    field_simp
    ring
  -- (2) iteratedDeriv n δ is O(t^(-n-1)) at 𝓝∞.
  have h_bd : IsO (fun t => iteratedDeriv n δ t) (fun t => t ^ (-(n : ℝ) - 1)) 𝓝∞ :=
    iteratedDeriv_δ_isO n hn1
  -- (3) Stitch via eventual equality at +∞.
  have h_evEq :
      (fun t =>
        iteratedDeriv n theta t
        - ((-1 : ℝ) ^ n * (n - 2).factorial * (1 / 2) * t ^ (1 - (n : ℝ))))
        =ᶠ[Filter.atTop]
      (fun t => iteratedDeriv n δ t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact h_clean t ht
  exact h_evEq.trans_isBigO h_bd

/-!
  ## §5  `θ` tends to `+∞`

  `theta = δ − π·φ − π` grows without bound as `t → +∞`: the main term
  `−π·φ(t) − π = (t/2)·(log(t/(2π)) − 1) + 7π/8 − π` tends to `+∞`,
  while the error term `δ = α_part − (t/2)·j` is eventually bounded
  below (`α_part ≥ 0` elementarily and `(t/2)·j(t) = O(t⁻¹)` from
  `iteratedDeriv_j_isO` at order `0`).

  This is the existence input that lets `Theorem3.lean` *define* the
  Gram function as an inverse of `theta` on `[7, ∞)` (via the
  intermediate value theorem) instead of axiomatising it.
-/

/-- The Riemann–Siegel theta function tends to `+∞` at `+∞`.  Proved
    from the concrete definition `theta = δ − π·φ − π`: the `φ`-part
    contributes `(t/2)·(log(t/(2π)) − 1) → +∞` and `δ` is eventually
    bounded below by `−1`. -/
theorem theta_tendsto_atTop : Filter.Tendsto theta 𝓝∞ 𝓝∞ := by
  -- (1) The integral part: `|t/2 · j t| ≤ 1` eventually, since `j = O(t⁻²)`.
  have h_j : IsO j (fun t => t ^ (-(0 : ℝ) - 2)) 𝓝∞ := by
    simpa [iteratedDeriv_zero] using iteratedDeriv_j_isO 0
  have h_tj : ∀ᶠ t in (𝓝∞ : Filter ℝ), |t / 2 * j t| ≤ 1 := by
    obtain ⟨C, hC⟩ := h_j.bound
    filter_upwards [hC, Filter.eventually_ge_atTop (1 : ℝ),
        Filter.eventually_ge_atTop (max C 1)] with t hCt h1 hmax
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos h1
    have h_pow : t ^ (-(0 : ℝ) - 2) = (t ^ 2)⁻¹ := by
      rw [show -(0 : ℝ) - 2 = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      rw [zpow_neg, zpow_two]
      ring
    have hj_le : |j t| ≤ C * (t ^ 2)⁻¹ := by
      have h := hCt
      rw [Real.norm_eq_abs, Real.norm_eq_abs, h_pow,
          abs_of_pos (by positivity : (0 : ℝ) < (t ^ 2)⁻¹)] at h
      exact h
    have hC_le_t : C ≤ t := le_trans (le_max_left _ _) hmax
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t / 2)]
    have h_step : t / 2 * |j t| ≤ t / 2 * (C * (t ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hj_le (by positivity)
    have h_simp : t / 2 * (C * (t ^ 2)⁻¹) = C / (2 * t) := by
      field_simp
    rw [h_simp] at h_step
    have h_frac : C / (2 * t) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * t)]
      linarith
    linarith
  -- (2) The algebraic part: `α_part t ≥ 0` for `t > 0`.
  have h_α : ∀ᶠ t in (𝓝∞ : Filter ℝ), 0 ≤ α_part t := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    unfold α_part
    have h_inv : 0 ≤ 1 / (4 * t ^ 2) := by positivity
    have h_log : 0 ≤ Real.log (1 + 1 / (4 * t ^ 2)) :=
      Real.log_nonneg (by linarith)
    have h_arctan : 0 ≤ Real.arctan (1 / (2 * t)) := by
      have h := Real.arctan_mono (by positivity : (0 : ℝ) ≤ 1 / (2 * t))
      simpa [Real.arctan_zero] using h
    have h1 : 0 ≤ t / 4 * Real.log (1 + 1 / (4 * t ^ 2)) :=
      mul_nonneg (by positivity) h_log
    have h2 : 0 ≤ 1 / 4 * Real.arctan (1 / (2 * t)) :=
      mul_nonneg (by norm_num) h_arctan
    linarith
  -- (3) Hence `δ t ≥ −1` eventually.
  have h_δ : ∀ᶠ t in (𝓝∞ : Filter ℝ), -1 ≤ δ t := by
    filter_upwards [h_tj, h_α, Filter.eventually_gt_atTop (0 : ℝ)] with t htj hα ht
    rw [δ_eq t ht]
    have := le_abs_self (t / 2 * j t)
    linarith
  -- (4) Eventual lower bound for `theta` by an explicit minorant.
  have h_lower : ∀ᶠ t in (𝓝∞ : Filter ℝ),
      t / 2 * Real.log (t / (2 * Real.pi)) - t / 2
        + (7 * Real.pi / 8 - Real.pi - 1) ≤ theta t := by
    filter_upwards [h_δ, Filter.eventually_gt_atTop (0 : ℝ)] with t hδt ht
    have h_theta_eq : theta t
        = δ t + t / 2 * Real.log (t / (2 * Real.pi)) - t / 2
          + 7 * Real.pi / 8 - Real.pi := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      unfold theta φ
      field_simp
      ring
    rw [h_theta_eq]
    linarith
  -- (5) The minorant tends to `+∞`.
  have h_min : Filter.Tendsto
      (fun t : ℝ => t / 2 * Real.log (t / (2 * Real.pi)) - t / 2
        + (7 * Real.pi / 8 - Real.pi - 1)) 𝓝∞ 𝓝∞ := by
    have h_log : Filter.Tendsto (fun t : ℝ => Real.log (t / (2 * Real.pi)) - 1)
        𝓝∞ 𝓝∞ := by
      have h_inner : Filter.Tendsto (fun t : ℝ => t / (2 * Real.pi)) 𝓝∞ 𝓝∞ :=
        Filter.Tendsto.atTop_div_const (by positivity) Filter.tendsto_id
      exact Filter.tendsto_atTop_add_const_right _ (-1)
        (Real.tendsto_log_atTop.comp h_inner)
    have h_half : Filter.Tendsto (fun t : ℝ => t / 2) 𝓝∞ 𝓝∞ :=
      Filter.Tendsto.atTop_div_const (by norm_num) Filter.tendsto_id
    have h_prod : Filter.Tendsto
        (fun t : ℝ => t / 2 * (Real.log (t / (2 * Real.pi)) - 1)) 𝓝∞ 𝓝∞ :=
      Filter.Tendsto.atTop_mul_atTop₀ h_half h_log
    have h_shift := Filter.tendsto_atTop_add_const_right 𝓝∞
      (7 * Real.pi / 8 - Real.pi - 1) h_prod
    refine h_shift.congr fun t => ?_
    ring
  -- (6) Comparison.
  exact Filter.tendsto_atTop_mono' 𝓝∞ h_lower h_min
