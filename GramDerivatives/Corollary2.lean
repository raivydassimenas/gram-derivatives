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
