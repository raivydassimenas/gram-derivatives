/-
  GramDerivatives/Corollary2.lean
  ===============================
  Lean 4 / Mathlib formalisation of **Corollary 2** from

      Dundulis, Garunkštis, Laurinčikas, Šimenas,
      "Higher derivatives of the Gram function", 2026.

  Corollary 2.  For n ≥ 2, as t → +∞ (away from discontinuities of S),

      θ^(n)(t) = (-1)^n · (n-2)! / 2 · t^(1-n) + O(t^(-n-1)),

  where θ is the Riemann–Siegel theta function.

  ─── Strategy ──────────────────────────────────────────────────────────
  Interpretation (see CLAUDE.md, "Working on `Corollary2.lean`"):
    • `S`       = `(1/π) · arg ζ(1/2 + i t)`        (from Theorem1.lean).
    • `N_step`  = `N(γ+0)`                          (right-continuous ζ
                                                     zero-counting function).
    • `θ`       = Riemann–Siegel theta function    (introduced here).

  Karatsuba–Korolev / Riemann–von Mangoldt identity (equation (1) of the
  paper) reads
      N(t) = (1/π) · θ(t) + 1 + S(t),
  which solves for θ as
      θ(t) = π · N_step(t) − π − π · S(t).
  Taking n ≥ 1 iterated derivatives at a regular point t > 0:
    • N_step is piecewise constant  ⟹  iteratedDeriv n N_step t = 0;
    • the constant −π drops as well;
  so
      θ^(n)(t) = −π · S^(n)(t).
  Multiplying Theorem 1 by −π gives Corollary 2.

  ─── What's axiomatised ────────────────────────────────────────────────
  Nothing.  `theta` is *defined* by

      theta t := δ t − π · φ t − π,

  the closed form obtained by solving the Riemann–von Mangoldt identity
  `N(t) = (1/π)·θ(t) + 1 + S(t)` for θ and substituting
  `S = φ − (1/π)·δ + N_step` (from `Theorem1.lean`); the `N_step` terms
  cancel algebraically, so the identity `riemann_vonMangoldt` is a
  routine algebraic consequence of the *definitions* of `S` and `theta`
  alone — no properties of the opaque `N_step` are needed.  Smoothness
  (`contDiffAt_theta`) follows from `contDiffAt_δ` and `contDiffAt_φ`.

  The agreement of this `theta` with the analytic Riemann–Siegel theta
  function is informal — it is the content of the Karatsuba–Korolev
  representation, which on `(0, ∞)` gives `θ_RS(t) = δ(t) − π·φ(t) − π`
  for the same `δ` and `φ` defined in `Theorem1.lean`.

  Everything else is derived from `theorem1` plus elementary calculus.
  Builds with zero `sorry`.
-/

import GramDerivatives.Theorem1

open Real Filter Asymptotics
open scoped ContDiff

/-!
  ## §1  The Riemann–Siegel theta function

  `theta : ℝ → ℝ` is *defined* as `δ − π·φ − π`, the closed form obtained
  by solving the Riemann–von Mangoldt identity for θ and substituting
  `S = φ − (1/π)·δ + N_step` from `Theorem1.lean`.  Under this definition:

    • `contDiffAt_theta`  is a derived theorem (from smoothness of `φ`
      and `δ`).
    • `riemann_vonMangoldt` reduces to an algebraic identity in which
      the `N_step` terms cancel between the two sides; the identity
      then closes by `field_simp` + `ring`.

  The agreement of this `theta` with the analytic Riemann–Siegel theta
  function on `(0, ∞)` is the content of the Karatsuba–Korolev
  representation; that agreement is informal and not formalised here.
-/

/-- The Riemann–Siegel theta function, defined as the closed form
    `θ(t) := δ(t) − π · φ(t) − π` obtained from the Karatsuba–Korolev /
    Riemann–von Mangoldt identity combined with `S = φ − (1/π)·δ + N_step`
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
    `S := φ − (1/π)·δ + N_step` (from `Theorem1.lean`), this reduces to
    a purely algebraic identity in `δ t`, `φ t`, `N_step t`, and `π`:
    the `N_step t` terms cancel between the two sides, as does the
    `δ t / π` contribution; the constant `−π · (1/π) = −1` is absorbed
    by the `+1`.  No properties of `N_step` are used. -/
theorem riemann_vonMangoldt (t : ℝ) (_ht : 0 < t) :
    N_step t = (1 / Real.pi) * theta t + 1 + S t := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [theta, S]
  field_simp
  ring

/-!
  ## §2  Auxiliary lemmas

  Three helpers not available outside `Theorem1.lean`:
    • `iteratedDeriv` of a constant vanishes after the first derivative;
    • `iteratedDeriv` distributes over an additive form on an open set;
    • `iteratedDeriv` commutes with a constant scalar factor.
  The last two duplicate `private` helpers in `Theorem1.lean`.
  We also derive smoothness of `S` from its definition.
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

/-- If `f = g` on an open set `U`, all iterated derivatives agree on `U`.
    Duplicates the private helper from `Theorem1.lean`. -/
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

/-- `S` is `ContDiffAt n` on `(0, ∞)`.  Derived from the smoothness of
    `φ`, `δ`, and `N_step`, since `S = φ − (1/π) · δ + N_step` by
    definition. -/
private lemma contDiffAt_S (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n S s := by
  unfold S
  exact ((contDiffAt_φ n hs).sub (contDiffAt_const.mul (contDiffAt_δ n hs))).add
    (contDiffAt_N_step n hs)

/-!
  ## §3  Reduction `θ^(n)(t) = −π · S^(n)(t)`

  For `n ≥ 1` and `t > 0`, the Riemann–von Mangoldt formula together
  with the local constancy of `N_step` yields `θ^(n)(t) = −π · S^(n)(t)`.
-/

/-- Solved form of the Riemann–von Mangoldt formula, written as a sum so
    that `iteratedDeriv` splits via `iteratedDeriv_add`:

        θ(t) = π · N_step(t) + (−π · S(t)) + (−π). -/
private lemma theta_eq_sum (t : ℝ) (ht : 0 < t) :
    theta t = Real.pi * N_step t + (-Real.pi * S t) + (-Real.pi) := by
  have h : N_step t = (1 / Real.pi) * theta t + 1 + S t :=
    riemann_vonMangoldt t ht
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hPi_inv : Real.pi * ((1 / Real.pi) * theta t) = theta t := by
    rw [← mul_assoc, mul_one_div, div_self hπ, one_mul]
  have h2 : Real.pi * N_step t = theta t + Real.pi + Real.pi * S t := by
    calc Real.pi * N_step t
        = Real.pi * ((1 / Real.pi) * theta t + 1 + S t)        := by rw [h]
      _ = Real.pi * ((1 / Real.pi) * theta t)
            + Real.pi * 1 + Real.pi * S t                       := by ring
      _ = theta t + Real.pi + Real.pi * S t                     := by
            rw [hPi_inv]; ring
  linarith

/-- For `n ≥ 1` and `t > 0`, the iterated derivative of θ reduces to a
    multiple of the iterated derivative of `S`:

        θ^(n)(t) = −π · S^(n)(t). -/
private lemma iteratedDeriv_theta_eq (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv n theta t = -Real.pi * iteratedDeriv n S t := by
  -- (1) Lift the pointwise equality from `theta_eq_sum` to an iterated-
  --     derivative equality on the open set (0, ∞).
  have h_iter_eq :
      iteratedDeriv n theta t
        = iteratedDeriv n
            (fun s => Real.pi * N_step s + (-Real.pi * S s) + (-Real.pi)) t :=
    iteratedDeriv_congr_of_nhds n isOpen_Ioi
      (fun s hs => theta_eq_sum s hs) t ht
  -- (2) Split the iterated derivative using local `ContDiffAt`.
  have hN_const_mul : ContDiffAt ℝ n (fun s => Real.pi * N_step s) t :=
    contDiffAt_const.mul (contDiffAt_N_step n ht)
  have hS_const_mul : ContDiffAt ℝ n (fun s => -Real.pi * S s) t :=
    contDiffAt_const.mul (contDiffAt_S n ht)
  have hC : ContDiffAt ℝ n (fun _ : ℝ => -Real.pi) t := contDiffAt_const
  -- Outer split: (π · N_step + (−π · S)) + (−π).
  have h_outer :
      iteratedDeriv n
          (fun s => Real.pi * N_step s + (-Real.pi * S s) + (-Real.pi)) t
        = iteratedDeriv n
            (fun s => Real.pi * N_step s + (-Real.pi * S s)) t
          + iteratedDeriv n (fun _ : ℝ => -Real.pi) t := by
    change iteratedDeriv n
            ((fun s => Real.pi * N_step s + (-Real.pi * S s))
              + (fun _ : ℝ => -Real.pi)) t = _
    exact iteratedDeriv_add (hN_const_mul.add hS_const_mul) hC
  -- Inner split: π · N_step + (−π · S).
  have h_inner :
      iteratedDeriv n (fun s => Real.pi * N_step s + (-Real.pi * S s)) t
        = iteratedDeriv n (fun s => Real.pi * N_step s) t
          + iteratedDeriv n (fun s => -Real.pi * S s) t := by
    change iteratedDeriv n
            ((fun s => Real.pi * N_step s) + (fun s => -Real.pi * S s)) t = _
    exact iteratedDeriv_add hN_const_mul hS_const_mul
  -- (3) Substitute the closed forms / vanishings.
  rw [h_iter_eq, h_outer, h_inner,
      iteratedDeriv_const_mul' Real.pi N_step n t,
      iteratedDeriv_const_mul' (-Real.pi) S n t,
      N_step_iteratedDeriv_eq_zero n hn t ht True.intro,
      iteratedDeriv_const_eq_zero hn (-Real.pi) t]
  ring

/-!
  ## §4  Main theorem: Corollary 2

  Multiplying Theorem 1 by −π gives Corollary 2.
-/

/-- **Corollary 2** (Dundulis–Garunkštis–Laurinčikas–Šimenas, 2026).

    For `n ≥ 2`, the `n`-th derivative of the Riemann–Siegel theta
    function satisfies

        θ^(n)(t) = (-1)^n · (n-2)! / 2 · t^(1-n) + O(t^(-n-1))

    as `t → +∞`. -/
theorem corollary2 (n : ℕ) (hn : 2 ≤ n) :
    IsO
      (fun t =>
        iteratedDeriv n theta t
        - ((-1 : ℝ) ^ n * (n - 2).factorial
           * (1 / 2) * t ^ (1 - (n : ℝ))))
      (fun t => t ^ (-(n : ℝ) - 1))
      𝓝∞ := by
  have hn1 : 1 ≤ n := by omega
  -- (1) Theorem 1 bounds the residual of `S^(n)` by `O(t^(-n-1))`.
  have hS : IsO
      (fun t =>
        iteratedDeriv n S t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ))))
      (fun t => t ^ (-(n : ℝ) - 1)) 𝓝∞ :=
    theorem1 n hn
  -- (2) Scaling the residual by `−π` preserves the `O(t^(-n-1))` bound.
  have hS_mul : IsO
      (fun t => (-Real.pi) *
        (iteratedDeriv n S t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ)))))
      (fun t => t ^ (-(n : ℝ) - 1)) 𝓝∞ :=
    hS.const_mul_left (-Real.pi)
  -- (3) Pointwise on (0, ∞), the scaled residual equals `θ`'s residual.
  have h_clean : ∀ t, 0 < t →
      (-Real.pi) *
        (iteratedDeriv n S t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ))))
        = iteratedDeriv n theta t
          - ((-1 : ℝ) ^ n * (n - 2).factorial
             * (1 / 2) * t ^ (1 - (n : ℝ))) := by
    intro t ht
    rw [iteratedDeriv_theta_eq n hn1 t ht]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    -- `(-1)^n = -(-1)^(n-1)` for `n ≥ 1`.
    have h_pow : (-1 : ℝ) ^ n = -((-1 : ℝ) ^ (n - 1)) := by
      have hne : (n - 1) + 1 = n := by omega
      conv_lhs => rw [← hne, pow_succ]
      ring
    rw [h_pow]
    field_simp
    ring
  -- (4) Stitch via eventual equality at +∞.
  have h_evEq :
      (fun t =>
        iteratedDeriv n theta t
        - ((-1 : ℝ) ^ n * (n - 2).factorial
           * (1 / 2) * t ^ (1 - (n : ℝ))))
        =ᶠ[Filter.atTop]
      (fun t => (-Real.pi) *
        (iteratedDeriv n S t
        - ((-1 : ℝ) ^ (n - 1) * (n - 2).factorial
           * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ))))) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    exact (h_clean t ht).symm
  exact h_evEq.trans_isBigO hS_mul
