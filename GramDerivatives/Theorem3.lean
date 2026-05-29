/-
  GramDerivatives/Theorem3.lean
  =============================
  Lean 4 / Mathlib formalisation of **Theorem 3** from

      Dundulis, Garunkštis, Laurinčikas, Šimenas,
      "Higher derivatives of the Gram function", 2026.

  Theorem 3.  For n ≥ 2, as u → +∞,

      t_u^(n) = (-1)^(n+1) · 2π · (n − 2)! / (u^(n-1) · log² u)
                · (1 + (2 + o(1)) · log log u / log u),

  where `t_u` is the Gram function — the inverse of the Riemann–Siegel
  theta function `θ` on the half-line where `θ` is monotonically
  increasing.

  ─── Strategy ──────────────────────────────────────────────────────────
  Setup (see CLAUDE.md, "Working on `Theorem3.lean`"):
    • `gram`            = the Gram function `t_u` (axiomatised).
    • `gram_spec`       = θ(t_u) = (u − 1)·π                  (eq. (7)).
    • `contDiffAt_gram` = smoothness on (θ(7)/π + π, ∞)
                          (inverse function theorem applied to θ).
    • `gram_asymp`,
      `gram_deriv_asymp`
                        = base-case asymptotics (eqs. (8), (9), Lavrik
                          [14] and Korolev [10]).

  Proof outline (paper §2):
    Induction on k ≥ 2 with inductive hypothesis
        t_u^(k) = (-1)^(k+1) · 2π · (k − 2)! / (u^(k-1) · log² u)
                  · (1 + (2 + o(1)) · log log u / log u).
    Base case k = 2: differentiate θ(t_u) = (u − 1)π twice,
        θ''(t_u) · (t_u')² + θ'(t_u) · t_u'' = 0,
    solve for `t_u''`, and substitute Corollary-2 asymptotics for
    `θ'(t_u), θ''(t_u)` plus the eq.-(9) asymptotic for `t_u'`.
    Inductive step: differentiate the implicit relation k times via
    Faà di Bruno / general Leibniz, isolate `t_u^(k)`, and substitute.

  ─── Status ────────────────────────────────────────────────────────────
  Complete: `theorem3` is fully proven by strong induction on `n ≥ 2`.
  Base case `n = 2` is `theorem3_two` (§1.14); the inductive step combines
  the atomic-term asymptotic (`theorem3_atomic_term`, §2.4) with the
  cOther contribution bound (`cOther_contribution_isLittleO`, §2.5.4) via
  the Faà di Bruno solved form `iteratedDeriv_n_gram_solved_eventually`
  (§2.3).  All remaining `-- ASSUMPTION` axioms are listed under §1.
-/

import GramDerivatives.Corollary2

open Real Filter Asymptotics
open scoped ContDiff Topology

/-!
  ## §0  Notation

  Reuse the `IsO`/`𝓝∞` notation from `Theorem1.lean` and add a
  companion `Iso` abbreviation for `Asymptotics.IsLittleO`, which we
  need to encode the `(2 + o(1))` factor in Theorem 3.
-/

/-- Little-o asymptotic notation, parallel to the `IsO` (big-O)
    abbreviation in `Theorem1.lean`. -/
abbrev Iso (f g : ℝ → ℝ) (l : Filter ℝ) : Prop := Asymptotics.IsLittleO l f g

/-!
  ## §1  The Gram function

  We introduce `gram : ℝ → ℝ` as an opaque axiom together with the four
  classical analytic facts the proof of Theorem 3 needs:
    • the defining relation `θ(t_u) = (u − 1)π`         (`gram_spec`);
    • smoothness on the open half-line where `θ` is monotonic
                                                         (`contDiffAt_gram`);
    • the Lavrik asymptotic for `t_u` itself             (`gram_asymp`);
    • the Korolev asymptotic for the first derivative    (`gram_deriv_asymp`).
-/

/-- The threshold above which `θ` is monotonically increasing on `[7, ∞)`
    gets transported by `θ` to `u ≥ θ(7)/π + π`. -/
noncomputable def gramThreshold : ℝ := theta 7 / Real.pi + Real.pi

/-- ASSUMPTION: the Gram function `t_u : ℝ → ℝ`, the inverse of the
    Riemann–Siegel theta function `θ` on the half-line `[7, ∞)` where
    `θ` is monotonically increasing.  Defined on all of `ℝ` for
    convenience; only values for `u > gramThreshold` are meaningful. -/
axiom gram : ℝ → ℝ -- ASSUMPTION

/-- ASSUMPTION: the defining relation of the Gram function (equation (7)
    of the paper):

        θ(t_u) = (u − 1) · π     for  u ≥ θ(7)/π + π. -/
axiom gram_spec (u : ℝ) (hu : gramThreshold ≤ u) :
    theta (gram u) = (u - 1) * Real.pi -- ASSUMPTION

/-- ASSUMPTION: `gram` is `C^∞` on the open half-line `(θ(7)/π + π, ∞)`.
    Morally, this follows from the inverse function theorem applied to
    `theta` (whose derivative does not vanish there). -/
axiom contDiffAt_gram (n : ℕ) {u : ℝ} (hu : gramThreshold < u) :
    ContDiffAt ℝ n gram u -- ASSUMPTION

/-- ASSUMPTION: Lavrik's asymptotic for the Gram function (equation (8),
    [14, Lemma 2]):

        t_u = (2π u / log u) · (1 + (1 + o(1)) · log log u / log u). -/
axiom gram_asymp :
    Iso
      (fun u : ℝ =>
        gram u
        - (2 * Real.pi * u / Real.log u)
        - (2 * Real.pi * u / Real.log u)
          * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ =>
        (2 * Real.pi * u / Real.log u)
        * (Real.log (Real.log u) / Real.log u))
      𝓝∞ -- ASSUMPTION

/-- ASSUMPTION: Korolev's asymptotic for the first derivative of the
    Gram function (equation (9), [10, Lemma 1.1]):

        t_u' = (2π / log u) · (1 + (1 + o(1)) · log log u / log u). -/
axiom gram_deriv_asymp :
    Iso
      (fun u : ℝ =>
        iteratedDeriv 1 gram u
        - (2 * Real.pi / Real.log u)
        - (2 * Real.pi / Real.log u)
          * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ =>
        (2 * Real.pi / Real.log u)
        * (Real.log (Real.log u) / Real.log u))
      𝓝∞ -- ASSUMPTION

/-!
  ## §1.5  Local `iteratedDeriv` helpers

  These three helpers duplicate the corresponding `private` lemmas in
  `Theorem1.lean` and `Corollary2.lean`.  Keeping a local copy avoids
  exposing them in those files' public APIs.
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

/-- If `f = g` on an open set `U`, all iterated derivatives agree on `U`. -/
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

/-- Iterated derivative commutes with a constant scalar factor. -/
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
  ## §1.7  Asymptotic algebra package

  Foundational asymptotic lemmas used throughout the proof of Theorem 3.

  Building blocks for `log`/`log log`:

    • `loglog_isLittleO_log`          — `log log u = o(log u)`.
    • `loglog_div_log_isLittleO_one`  — `log log u / log u = o(1)`.
    • `log_pos_atTop`, `loglog_pos_atTop` — positivity for large `u`.

  Building blocks for the Lavrik shorthand `L(u) = 2π u / log u`:

    • `id_div_log_tendsto_atTop`       — `u / log u → +∞`.
    • `linear_div_log_tendsto_atTop`   — `2π u / log u → +∞`.
    • `gramL_mul_loglog_isLittleO_gramL` — `L · (log log / log) = o(L)`.

  Consequences for the Gram function (derived from `gram_asymp`, **no
  new axioms**):

    • `gram_residual_isLittleO_gramL`  — `(gram − L − L · ll/l) = o(L)`.
    • `gram_sub_gramL_isLittleO_gramL` — `(gram − L) = o(L)`.
    • `gram_isEquivalent_gramL`        — `gram ~ L` at `+∞`.
    • `gram_tendsto_atTop`             — `gram u → +∞`.
    • `eventually_gram_pos`            — `∀ᶠ u, 0 < gram u`.

  Together these provide the positivity and asymptotic-equivalence
  toolkit that the base case and induction steps will need.
-/

/-- `log log u = o(log u)` as `u → +∞`. -/
private lemma loglog_isLittleO_log :
    Iso (fun u : ℝ => Real.log (Real.log u)) (fun u : ℝ => Real.log u) 𝓝∞ :=
  Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop

/-- `log log u / log u → 0` as `u → +∞`. -/
private lemma loglog_div_log_isLittleO_one :
    Iso (fun u : ℝ => Real.log (Real.log u) / Real.log u)
        (fun _ : ℝ => (1 : ℝ)) 𝓝∞ :=
  (Asymptotics.isLittleO_one_iff ℝ).mpr loglog_isLittleO_log.tendsto_div_nhds_zero

/-- `0 < log u` eventually as `u → +∞`. -/
private lemma log_pos_atTop : ∀ᶠ u in (𝓝∞ : Filter ℝ), 0 < Real.log u :=
  Real.tendsto_log_atTop.eventually_gt_atTop 0

/-- `0 < log log u` eventually as `u → +∞`. -/
private lemma loglog_pos_atTop :
    ∀ᶠ u in (𝓝∞ : Filter ℝ), 0 < Real.log (Real.log u) := by
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with u hu using hu

/-- `u / log u → +∞` as `u → +∞`.  Standard consequence of
    `Real.isLittleO_log_id_atTop`. -/
private lemma id_div_log_tendsto_atTop :
    Tendsto (fun u : ℝ => u / Real.log u) 𝓝∞ 𝓝∞ := by
  -- Step 1.  `log u / u → 0`.
  have h₀ : Tendsto (fun u : ℝ => Real.log u / u) 𝓝∞ (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  -- Step 2.  Eventually `0 < log u / u`.
  have h_pos : ∀ᶠ u in (𝓝∞ : Filter ℝ), 0 < Real.log u / u := by
    filter_upwards [log_pos_atTop, Filter.eventually_gt_atTop (0 : ℝ)] with u hl hu
    exact div_pos hl hu
  -- Step 3.  Refine to `𝓝[>] 0`.
  have h₁ : Tendsto (fun u : ℝ => Real.log u / u) 𝓝∞ (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨h₀, h_pos⟩
  -- Step 4.  Invert.
  have h₂ : Tendsto (fun u : ℝ => (Real.log u / u)⁻¹) 𝓝∞ 𝓝∞ :=
    h₁.inv_tendsto_nhdsGT_zero
  -- Step 5.  `(log u / u)⁻¹ = u / log u` (eventually, when `log u ≠ 0`).
  refine h₂.congr' ?_
  filter_upwards [log_pos_atTop, Filter.eventually_gt_atTop (0 : ℝ)] with u hl hu
  field_simp

/-- `2π · u / log u → +∞` as `u → +∞`. -/
private lemma linear_div_log_tendsto_atTop :
    Tendsto (fun u : ℝ => 2 * Real.pi * u / Real.log u) 𝓝∞ 𝓝∞ := by
  have h : Tendsto (fun u : ℝ => (2 * Real.pi) * (u / Real.log u)) 𝓝∞ 𝓝∞ :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      id_div_log_tendsto_atTop
  exact h.congr (fun u => by ring)

/-- Shorthand for the Lavrik leading term `L(u) = 2π u / log u`. -/
private noncomputable def gramL (u : ℝ) : ℝ := 2 * Real.pi * u / Real.log u

/-- `L · (log log / log) =o[atTop] L`.  Since `log log u / log u → 0` and
    `L =O[atTop] L`, the product is little-o of `L`. -/
private lemma gramL_mul_loglog_isLittleO_gramL :
    Iso (fun u : ℝ => gramL u * (Real.log (Real.log u) / Real.log u)) gramL 𝓝∞ := by
  have h := (Asymptotics.isBigO_refl gramL 𝓝∞).mul_isLittleO loglog_div_log_isLittleO_one
  simpa using h

/-- `gram_asymp` rewritten as `(gram − L − L · (loglog/log)) =o[atTop] L`. -/
private lemma gram_residual_isLittleO_gramL :
    Iso
      (fun u : ℝ =>
        gram u - gramL u - gramL u * (Real.log (Real.log u) / Real.log u))
      gramL 𝓝∞ := by
  -- `gram_asymp` is `=o (L · ll/l)`, and we've shown `(L · ll/l) =o L`.
  -- Therefore the residual is `o(L)` by transitivity.
  have h0 : Iso
      (fun u : ℝ =>
        gram u - 2 * Real.pi * u / Real.log u
        - 2 * Real.pi * u / Real.log u * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ =>
        2 * Real.pi * u / Real.log u * (Real.log (Real.log u) / Real.log u))
      𝓝∞ := gram_asymp
  -- Rewrite `2π u / log u` as `gramL u`.
  have h1 : Iso
      (fun u : ℝ =>
        gram u - gramL u - gramL u * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ => gramL u * (Real.log (Real.log u) / Real.log u)) 𝓝∞ := by
    refine h0.congr (fun u => by simp [gramL]) (fun u => by simp [gramL])
  exact h1.trans gramL_mul_loglog_isLittleO_gramL

/-- `gram − L =o[atTop] L`. -/
private lemma gram_sub_gramL_isLittleO_gramL :
    Iso (fun u : ℝ => gram u - gramL u) gramL 𝓝∞ := by
  -- `gram − L = (gram − L − L·(ll/l)) + L·(ll/l)`, each piece `o(L)`.
  have h1 := gram_residual_isLittleO_gramL
  have h2 := gramL_mul_loglog_isLittleO_gramL
  have h := h1.add h2
  refine h.congr_left ?_
  intro u; ring

/-- `gram ~ L` at `+∞`: the Gram function is asymptotically equivalent to
    `2π u / log u`. -/
private lemma gram_isEquivalent_gramL : IsEquivalent 𝓝∞ gram gramL :=
  gram_sub_gramL_isLittleO_gramL

/-- `gram u → +∞` as `u → +∞`.  Derived from `gram_asymp` together with
    the elementary fact `2π u / log u → +∞`. -/
private lemma gram_tendsto_atTop : Tendsto gram 𝓝∞ 𝓝∞ := by
  refine gram_isEquivalent_gramL.symm.tendsto_atTop ?_
  exact linear_div_log_tendsto_atTop.congr (fun u => by simp [gramL])

/-- Eventually `0 < gram u` as `u → +∞`. -/
private lemma eventually_gram_pos :
    ∀ᶠ u in (𝓝∞ : Filter ℝ), 0 < gram u :=
  gram_tendsto_atTop.eventually_gt_atTop 0

/-!
  ## §1.8  Mirror chain for `deriv gram`

  Exactly the same machinery as §1.7 applied to `gram_deriv_asymp` (the
  Korolev base-case asymptotic for `t_u'`) gives an asymptotic equivalence
  `deriv gram ~ 2π / log u` and eventual positivity of `deriv gram`.

  We also derive the structural identity `θ'(gram u) · gram'(u) = π`
  from `gram_spec` via the chain rule.  This is the trick (paper §2,
  base case) that lets us avoid an explicit asymptotic for `θ'(t_u)` —
  Corollary 2 doesn't cover `n = 1` directly, but the implicit relation
  expresses `θ'(t_u)` algebraically in terms of `t_u'`.
-/

/-- Shorthand for the Korolev leading term `L'(u) = 2π / log u`. -/
private noncomputable def gramLDeriv (u : ℝ) : ℝ := 2 * Real.pi / Real.log u

/-- `L' · (log log / log) =o[atTop] L'`. -/
private lemma gramLDeriv_mul_loglog_isLittleO_gramLDeriv :
    Iso (fun u : ℝ => gramLDeriv u * (Real.log (Real.log u) / Real.log u))
        gramLDeriv 𝓝∞ := by
  have h := (Asymptotics.isBigO_refl gramLDeriv 𝓝∞).mul_isLittleO
              loglog_div_log_isLittleO_one
  simpa using h

/-- `(deriv gram − L' − L' · ll/l) =o[atTop] L'`. -/
private lemma gram_deriv_residual_isLittleO_gramLDeriv :
    Iso
      (fun u : ℝ =>
        iteratedDeriv 1 gram u - gramLDeriv u
        - gramLDeriv u * (Real.log (Real.log u) / Real.log u))
      gramLDeriv 𝓝∞ := by
  have h0 : Iso
      (fun u : ℝ =>
        iteratedDeriv 1 gram u - 2 * Real.pi / Real.log u
        - 2 * Real.pi / Real.log u * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ =>
        2 * Real.pi / Real.log u * (Real.log (Real.log u) / Real.log u))
      𝓝∞ := gram_deriv_asymp
  have h1 : Iso
      (fun u : ℝ =>
        iteratedDeriv 1 gram u - gramLDeriv u
        - gramLDeriv u * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ => gramLDeriv u * (Real.log (Real.log u) / Real.log u)) 𝓝∞ := by
    refine h0.congr (fun u => by simp [gramLDeriv]) (fun u => by simp [gramLDeriv])
  exact h1.trans gramLDeriv_mul_loglog_isLittleO_gramLDeriv

/-- `(deriv gram − L') =o[atTop] L'`. -/
private lemma gram_deriv_sub_gramLDeriv_isLittleO_gramLDeriv :
    Iso (fun u : ℝ => iteratedDeriv 1 gram u - gramLDeriv u) gramLDeriv 𝓝∞ := by
  have h1 := gram_deriv_residual_isLittleO_gramLDeriv
  have h2 := gramLDeriv_mul_loglog_isLittleO_gramLDeriv
  have h := h1.add h2
  refine h.congr_left ?_
  intro u; ring

/-- `deriv gram ~ L'` at `+∞`. -/
private lemma gram_deriv_isEquivalent_gramLDeriv :
    IsEquivalent 𝓝∞ (iteratedDeriv 1 gram) gramLDeriv :=
  gram_deriv_sub_gramLDeriv_isLittleO_gramLDeriv

/-- Eventually `0 < deriv gram u`.  Proved using the `IsEquivalent`
    fact together with `L'(u) > 0` for `log u > 0`. -/
private lemma eventually_deriv_gram_pos :
    ∀ᶠ u in (𝓝∞ : Filter ℝ), 0 < deriv gram u := by
  -- Convert `iteratedDeriv 1 gram = deriv gram`.
  have h_eqv := gram_deriv_isEquivalent_gramLDeriv
  -- Use `IsEquivalent.tendsto_nhdsWithin_iff`-style: write `deriv gram - L' = o(L')`
  -- and bound `|deriv gram - L'| ≤ (1/2)|L'|` eventually, so `deriv gram ≥ L'/2 > 0`.
  have h_half : ∀ᶠ u in (𝓝∞ : Filter ℝ),
      |iteratedDeriv 1 gram u - gramLDeriv u| ≤ (1 / 2) * |gramLDeriv u| := by
    have := gram_deriv_sub_gramLDeriv_isLittleO_gramLDeriv.def (c := 1/2) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  -- `L'(u) > 0` whenever `log u > 0`.
  have h_L'_pos : ∀ᶠ u in (𝓝∞ : Filter ℝ), 0 < gramLDeriv u := by
    filter_upwards [log_pos_atTop] with u hu
    have : 0 < 2 * Real.pi / Real.log u := by positivity
    simpa [gramLDeriv]
  filter_upwards [h_half, h_L'_pos] with u h_bd h_L'
  have h_abs_L' : |gramLDeriv u| = gramLDeriv u := abs_of_pos h_L'
  rw [h_abs_L'] at h_bd
  have h_iter_eq : iteratedDeriv 1 gram u = deriv gram u := by
    rw [iteratedDeriv_one]
  rw [h_iter_eq] at h_bd
  -- `|deriv gram - L'| ≤ L'/2` ⟹ `deriv gram ≥ L'/2 > 0`.
  have h_lower : gramLDeriv u - 1/2 * gramLDeriv u ≤ deriv gram u := by
    have := abs_sub_le_iff.mp h_bd
    linarith [this.2]
  linarith

/-- **Chain rule for `gram_spec` (first derivative).**

    Differentiating `θ(gram u) = (u − 1)π` once via the chain rule
    gives `θ'(gram u) · gram'(u) = π`.  Asymptotic-free; holds
    pointwise whenever `u > gramThreshold` and `gram u > 0`. -/
private lemma deriv_theta_gram_mul_deriv_gram (u : ℝ)
    (hu : gramThreshold < u) (hgram : 0 < gram u) :
    deriv theta (gram u) * deriv gram u = Real.pi := by
  -- (1) Differentiability of `theta` at `gram u` and `gram` at `u`.
  have hθ_diff : DifferentiableAt ℝ theta (gram u) :=
    (contDiffAt_theta 1 hgram).differentiableAt (by norm_num)
  have hg_diff : DifferentiableAt ℝ gram u :=
    (contDiffAt_gram 1 hu).differentiableAt (by norm_num)
  -- (2) Chain rule: `HasDerivAt (theta ∘ gram) (θ'(gram u) · gram'(u)) u`.
  have h_comp : HasDerivAt (theta ∘ gram)
      (deriv theta (gram u) * deriv gram u) u :=
    hθ_diff.hasDerivAt.comp u hg_diff.hasDerivAt
  -- (3) On `Ioi gramThreshold`, `theta ∘ gram` equals `s ↦ (s − 1)π`.
  have h_evEq : (theta ∘ gram) =ᶠ[𝓝 u] (fun s : ℝ => (s - 1) * Real.pi) := by
    have hIoi : Set.Ioi gramThreshold ∈ (𝓝 u : Filter ℝ) :=
      isOpen_Ioi.mem_nhds hu
    filter_upwards [hIoi] with s hs
    simp [Function.comp_apply, gram_spec s hs.le]
  -- (4) Compare with `HasDerivAt (· - 1) * π = π · 1 = π`.
  have h_lin : HasDerivAt (fun s : ℝ => (s - 1) * Real.pi) Real.pi u := by
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 u := (hasDerivAt_id u).sub_const 1
    simpa using h1.mul_const Real.pi
  -- (5) Two `HasDerivAt`s for the same function ⟹ same derivative.
  have h_comp' : HasDerivAt (theta ∘ gram) Real.pi u :=
    h_lin.congr_of_eventuallyEq h_evEq
  exact h_comp.unique h_comp'

/-!
  ## §1.9  Transport of Corollary 2 along `gram → +∞`

  Composing Corollary 2 (the `θ^(k)(t)` asymptotic for `t → +∞`, valid
  for `k ≥ 2`) with `gram_tendsto_atTop` (`gram u → +∞`) gives the
  corresponding asymptotic for `θ^(k)(gram u)` as `u → +∞`.
-/

/-- Transport of `corollary2 k` along `gram → +∞`:

      iteratedDeriv k theta (gram u)
        − ((-1)^k · (k − 2)! · (1/2) · (gram u)^(1 − k))
      = O((gram u)^(−k − 1))    as u → +∞,

    for `k ≥ 2`. -/
private lemma iteratedDeriv_theta_at_gram_isO (k : ℕ) (hk : 2 ≤ k) :
    IsO
      (fun u : ℝ =>
        iteratedDeriv k theta (gram u)
        - ((-1 : ℝ) ^ k * (k - 2).factorial * (1 / 2) * (gram u) ^ (1 - (k : ℝ))))
      (fun u : ℝ => (gram u) ^ (-(k : ℝ) - 1))
      𝓝∞ :=
  (corollary2 k hk).comp_tendsto gram_tendsto_atTop

/-!
  ## §1.10  Structural identity at n = 2

  Differentiating `θ(gram u) = (u − 1)π` twice via
  `iteratedDeriv_comp_two` and using the first-derivative chain rule to
  eliminate `θ'(gram u)` yields the **purely algebraic** identity

      gram''(u) = −(1/π) · θ''(gram u) · (gram'(u))³

  valid wherever `u > gramThreshold`, `gram u > 0`, and
  `gram'(u) ≠ 0`.  This is the n = 2 case of the implicit
  differentiation argument from the paper.
-/

/-- The function `u ↦ (u − 1) · π` has vanishing second iterated
    derivative everywhere. -/
private lemma iteratedDeriv_two_linear_eq_zero (u : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => (s - 1) * Real.pi) u = 0 := by
  have hderiv : deriv (fun s : ℝ => (s - 1) * Real.pi) = fun _ : ℝ => Real.pi := by
    funext x
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have h2 : HasDerivAt (fun s : ℝ => (s - 1) * Real.pi) Real.pi x := by
      simpa using h1.mul_const Real.pi
    exact h2.deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', hderiv]
  exact iteratedDeriv_const_eq_zero (by omega) Real.pi u

/-- **n = 2 Faà di Bruno reduction.**  At every `u` with `u >
    gramThreshold` and `gram u > 0`,

        θ''(gram u) · (gram'(u))² + θ'(gram u) · gram''(u) = 0.

    Asymptotic-free; follows from `iteratedDeriv_comp_two` applied to
    `θ ∘ gram` whose value on `Ioi gramThreshold` is `(u − 1)π`. -/
private lemma faadi_bruno_gram_two (u : ℝ)
    (hu : gramThreshold < u) (hg : 0 < gram u) :
    iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 2
      + deriv theta (gram u) * iteratedDeriv 2 gram u = 0 := by
  -- (1) On `Ioi gramThreshold`, `theta ∘ gram` agrees with `s ↦ (s − 1)π`.
  have hθg_eq : ∀ s ∈ Set.Ioi gramThreshold,
      (theta ∘ gram) s = (s - 1) * Real.pi := by
    intro s hs
    simp [Function.comp_apply, gram_spec s hs.le]
  -- (2) Lift to second iterated derivative.
  have h_iter_eq :
      iteratedDeriv 2 (theta ∘ gram) u
        = iteratedDeriv 2 (fun s : ℝ => (s - 1) * Real.pi) u :=
    iteratedDeriv_congr_of_nhds 2 isOpen_Ioi hθg_eq u hu
  -- (3) RHS evaluates to 0.
  have h_rhs : iteratedDeriv 2 (fun s : ℝ => (s - 1) * Real.pi) u = 0 :=
    iteratedDeriv_two_linear_eq_zero u
  -- (4) LHS expanded via `iteratedDeriv_comp_two`.
  have hθ : ContDiffAt ℝ 2 theta (gram u) := contDiffAt_theta 2 hg
  have hg2 : ContDiffAt ℝ 2 gram u := contDiffAt_gram 2 hu
  have h_comp :
      iteratedDeriv 2 (theta ∘ gram) u
        = iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 2
          + deriv theta (gram u) * iteratedDeriv 2 gram u :=
    iteratedDeriv_comp_two hθ hg2
  -- (5) Combine.
  linarith [h_iter_eq.trans h_rhs, h_comp]

/-- **Solved form** of the n = 2 Faà di Bruno reduction.

    Eliminating `θ'(gram u)` via the first-derivative chain rule
    `θ'(gram u) · gram'(u) = π` (and assuming `gram'(u) > 0`),

        gram''(u) = −(1/π) · θ''(gram u) · (gram'(u))³. -/
private lemma iteratedDeriv_two_gram_eq (u : ℝ)
    (hu : gramThreshold < u) (hg : 0 < gram u) (hg' : 0 < deriv gram u) :
    iteratedDeriv 2 gram u
      = -(1 / Real.pi) * iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 3 := by
  -- Step (A): the n = 2 Faà di Bruno reduction.
  have h_fd := faadi_bruno_gram_two u hu hg
  -- Step (B): the chain rule identity.
  have h_chain := deriv_theta_gram_mul_deriv_gram u hu hg
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h_gd' : deriv gram u ≠ 0 := ne_of_gt hg'
  -- Solve `h_fd` for `iteratedDeriv 2 gram u` and substitute the
  -- chain-rule identity for `deriv theta (gram u)`.
  -- From `h_chain`: `deriv theta (gram u) = π / deriv gram u`.
  have h_θ' : deriv theta (gram u) = Real.pi / deriv gram u := by
    field_simp at h_chain ⊢
    linarith
  -- Substitute into `h_fd`:
  have h_iter : iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 2
      + (Real.pi / deriv gram u) * iteratedDeriv 2 gram u = 0 := by
    rw [← h_θ']; exact h_fd
  -- Now isolate `iteratedDeriv 2 gram u`.
  have h_iter' :
      (Real.pi / deriv gram u) * iteratedDeriv 2 gram u
        = - iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 2 := by
    linarith
  -- Multiply both sides by `deriv gram u / π`.
  have key :
      iteratedDeriv 2 gram u
        = (deriv gram u / Real.pi)
          * (- iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 2) := by
    have h_pi_div : Real.pi / deriv gram u ≠ 0 := div_ne_zero hπ h_gd'
    field_simp at h_iter' ⊢
    linarith
  rw [key]; ring

/-- Eventually-true form of `iteratedDeriv_two_gram_eq`, packaged for
    asymptotic work via `EventuallyEq.trans_isBigO`/`isLittleO`. -/
private lemma iteratedDeriv_two_gram_eventually_eq :
    (fun u : ℝ => iteratedDeriv 2 gram u)
      =ᶠ[(𝓝∞ : Filter ℝ)]
    (fun u : ℝ =>
      -(1 / Real.pi) * iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 3) := by
  filter_upwards [Filter.eventually_gt_atTop gramThreshold,
                   eventually_gram_pos,
                   eventually_deriv_gram_pos] with u hu hg hg'
  exact iteratedDeriv_two_gram_eq u hu hg hg'

/-!
  ## §2  Main theorem: Theorem 3

  The `n`-th derivative of the Gram function inherits an asymptotic of
  the same shape as the leading Lavrik / Korolev terms, with `(2 + o(1))`
  in place of `(1 + o(1))` for the secondary `log log u / log u`
  correction.  The constant in front, `(-1)^(n+1) · 2π · (n − 2)! /
  (u^(n-1) · log² u)`, is derived from Corollary 2 via the implicit
  relation `θ(t_u) = (u − 1)π`.
-/

/-- The leading term of the n-th derivative of the Gram function:

        (-1)^(n+1) · 2π · (n − 2)! / (u^(n-1) · log² u). -/
private noncomputable def gramLeading (n : ℕ) (u : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (2 * Real.pi) * (n - 2).factorial
    / (u ^ (n - 1) * Real.log u ^ 2)

/-- Closed form for `gramLeading 2 u`: `-2π / (u · log² u)`. -/
private lemma gramLeading_two (u : ℝ) :
    gramLeading 2 u = -(2 * Real.pi) / (u * Real.log u ^ 2) := by
  change ((-1 : ℝ) ^ (2 + 1) * (2 * Real.pi) * (Nat.factorial (2 - 2))
        / (u ^ (2 - 1) * Real.log u ^ 2)) = _
  norm_num

/-- Algebraic factorisation: the leading order of
    `-(1/(2π)) · (gramL u)⁻¹ · (gramLDeriv u)^3` is exactly
    `gramLeading 2 u`.  Valid whenever `u ≠ 0` and `log u ≠ 0`. -/
private lemma gramLeading_two_factorization {u : ℝ}
    (hu : u ≠ 0) (hlog : Real.log u ≠ 0) :
    -(1 / (2 * Real.pi)) * (gramL u)⁻¹ * (gramLDeriv u) ^ 3
      = gramLeading 2 u := by
  unfold gramL gramLDeriv
  rw [gramLeading_two]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-!
  ## §1.11  Leading-order asymptotic at n = 2

  Combining
    • the n = 2 solved form `iteratedDeriv_two_gram_eventually_eq`,
    • the Corollary-2 transport `iteratedDeriv_theta_at_gram_isO`,
    • the equivalences `gram ~ gramL`, `deriv gram ~ gramLDeriv`,
    • the algebraic identity `gramLeading_two_factorization`,
  we obtain

      iteratedDeriv 2 gram ~[𝓝∞] gramLeading 2.

  This is the *leading* asymptotic equivalence — the refined
  `(1 + (2 + o(1)) · log log u / log u)` correction is a further step.
-/

/-- `(gram u)⁻¹ → 0` as `u → +∞`. -/
private lemma gram_inv_tendsto_zero :
    Tendsto (fun u : ℝ => (gram u)⁻¹) 𝓝∞ (𝓝 0) :=
  gram_tendsto_atTop.inv_tendsto_atTop

/-- `((gram u)⁻¹)^3 = o((gram u)⁻¹)` as `u → +∞`. -/
private lemma inv_gram_pow_three_isLittleO_inv_gram :
    Iso (fun u : ℝ => ((gram u)⁻¹) ^ 3) (fun u : ℝ => (gram u)⁻¹) 𝓝∞ := by
  -- Factor `x⁻¹^3 = x⁻¹ · x⁻¹^2`, where `x⁻¹^2 = o(1)`.
  have h_sq_tendsto : Tendsto (fun u : ℝ => ((gram u)⁻¹) ^ 2) 𝓝∞ (𝓝 0) := by
    have := gram_inv_tendsto_zero.pow 2
    simpa using this
  have h_sq_o : Asymptotics.IsLittleO 𝓝∞
      (fun u : ℝ => ((gram u)⁻¹) ^ 2) (fun _ : ℝ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr h_sq_tendsto
  have h_refl : Asymptotics.IsBigO 𝓝∞ (fun u : ℝ => (gram u)⁻¹) (fun u : ℝ => (gram u)⁻¹) :=
    Asymptotics.isBigO_refl _ _
  have h_prod := h_refl.mul_isLittleO h_sq_o
  refine h_prod.congr' ?_ ?_
  · filter_upwards with u using by ring
  · filter_upwards with u using by ring

/-- The n = 2 instance of Corollary 2 transported along `gram → ∞`,
    sharpened to an asymptotic equivalence:

        iteratedDeriv 2 theta (gram u)  ~[𝓝∞]  (1/2) · (gram u)⁻¹. -/
private lemma iteratedDeriv_two_theta_at_gram_isEquivalent :
    IsEquivalent 𝓝∞
      (fun u : ℝ => iteratedDeriv 2 theta (gram u))
      (fun u : ℝ => (1 / 2 : ℝ) * (gram u)⁻¹) := by
  -- Raw IsO statement from Corollary 2 transport.
  have h_isO := iteratedDeriv_theta_at_gram_isO 2 (le_refl 2)
  -- Eventually rewrite LHS: simplify constants and `(gram u)^(1-2:ℝ) = (gram u)⁻¹`.
  have h_lhs :
      (fun u : ℝ => iteratedDeriv 2 theta (gram u)
        - ((-1 : ℝ) ^ (2 : ℕ) * ((Nat.factorial (2 - 2) : ℕ) : ℝ)
            * (1 / 2) * (gram u) ^ (1 - (2 : ℝ))))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ =>
        iteratedDeriv 2 theta (gram u) - (1 / 2 : ℝ) * (gram u)⁻¹) := by
    filter_upwards with u
    have h_exp : (1 - (2 : ℝ)) = (-1 : ℝ) := by ring
    have h_rpow : (gram u) ^ (-1 : ℝ) = (gram u)⁻¹ := Real.rpow_neg_one _
    rw [h_exp, h_rpow]
    norm_num
  -- Eventually rewrite RHS: `(gram u)^(-2-1:ℝ) = ((gram u)⁻¹)^3`.
  have h_rhs :
      (fun u : ℝ => (gram u) ^ (-(2 : ℝ) - 1))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ => ((gram u)⁻¹) ^ 3) := by
    filter_upwards with u
    have h_exp : (-(2 : ℝ) - 1) = ((-3 : ℤ) : ℝ) := by push_cast; ring
    rw [h_exp, Real.rpow_intCast]
    change (gram u) ^ (-3 : ℤ) = ((gram u)⁻¹) ^ 3
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, inv_pow]
  -- Cleaned-up IsO: `θ''(gram u) - (1/2)·(gram u)⁻¹ = O(((gram u)⁻¹)^3)`.
  have h_isO_clean :
      Asymptotics.IsBigO 𝓝∞
        (fun u : ℝ =>
          iteratedDeriv 2 theta (gram u) - (1 / 2 : ℝ) * (gram u)⁻¹)
        (fun u : ℝ => ((gram u)⁻¹) ^ 3) :=
    (h_isO.congr' h_lhs h_rhs : _)
  -- Use `((gram u)⁻¹)^3 = o((1/2)·(gram u)⁻¹)`.
  have h_o : Iso (fun u : ℝ => ((gram u)⁻¹) ^ 3)
      (fun u : ℝ => (1 / 2 : ℝ) * (gram u)⁻¹) 𝓝∞ := by
    have h := inv_gram_pow_three_isLittleO_inv_gram
    have h' := h.const_mul_right (c := (1 / 2 : ℝ)) (by norm_num)
    -- `h'` has the right shape already.
    exact h'
  -- The IsEquivalent says: residual = o(target).
  exact h_isO_clean.trans_isLittleO h_o

/-- `deriv gram ~[𝓝∞] gramLDeriv` (unpacking `iteratedDeriv 1 = deriv`). -/
private lemma deriv_gram_isEquivalent_gramLDeriv :
    IsEquivalent 𝓝∞ (deriv gram) gramLDeriv := by
  have h := gram_deriv_isEquivalent_gramLDeriv
  rwa [iteratedDeriv_one] at h

/-- `(deriv gram)^3 ~[𝓝∞] gramLDeriv^3`. -/
private lemma deriv_gram_pow_three_isEquivalent :
    IsEquivalent 𝓝∞ (fun u : ℝ => (deriv gram u) ^ 3) (fun u : ℝ => (gramLDeriv u) ^ 3) :=
  deriv_gram_isEquivalent_gramLDeriv.pow 3

/-- `(gram u)⁻¹ ~[𝓝∞] (gramL u)⁻¹`. -/
private lemma gram_inv_isEquivalent_gramL_inv :
    IsEquivalent 𝓝∞ (fun u : ℝ => (gram u)⁻¹) (fun u : ℝ => (gramL u)⁻¹) :=
  gram_isEquivalent_gramL.inv

/-- **Leading-order asymptotic equivalence at n = 2.**

        iteratedDeriv 2 gram  ~[𝓝∞]  gramLeading 2.

    Combines `iteratedDeriv_two_gram_eventually_eq` (the solved form
    `gram'' = −(1/π) · θ''(gram) · (gram')³`) with the asymptotic
    equivalences `θ''(gram u) ~ (1/2)·(gram u)⁻¹`,
    `(gram u)⁻¹ ~ (gramL u)⁻¹`, `(deriv gram u)³ ~ (gramLDeriv u)³`,
    and the algebraic identity `gramLeading_two_factorization`. -/
private lemma iteratedDeriv_two_gram_isEquivalent_gramLeading_two :
    IsEquivalent 𝓝∞ (iteratedDeriv 2 gram) (gramLeading 2) := by
  -- (A) Lift the solved form to an eventually-equality at `𝓝∞`.
  have h_solved := iteratedDeriv_two_gram_eventually_eq
  -- (B) IsEquivalent chain for the RHS of (A):
  --     -(1/π) · θ''(gram u) · (deriv gram u)^3
  --       ~ -(1/π) · ((1/2)·(gram u)⁻¹) · (gramLDeriv u)^3
  --       ~ -(1/π) · ((1/2)·(gramL u)⁻¹) · (gramLDeriv u)^3
  --     = -(1/(2π)) · (gramL u)⁻¹ · (gramLDeriv u)^3
  --     = gramLeading 2 u  (eventually)
  -- Step B1: θ''(gram u) · (deriv gram u)^3 ~ (1/2)·(gram u)⁻¹ · (gramLDeriv u)^3.
  have h_step1 : IsEquivalent 𝓝∞
      (fun u : ℝ => iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 3)
      (fun u : ℝ => (1 / 2 : ℝ) * (gram u)⁻¹ * (gramLDeriv u) ^ 3) :=
    iteratedDeriv_two_theta_at_gram_isEquivalent.mul deriv_gram_pow_three_isEquivalent
  -- Step B2: replace (gram u)⁻¹ with (gramL u)⁻¹ inside the product.
  have h_const_eqv :
      IsEquivalent 𝓝∞ (fun _ : ℝ => (1 / 2 : ℝ)) (fun _ : ℝ => (1 / 2 : ℝ)) :=
    IsEquivalent.refl
  have h_gd_eqv :
      IsEquivalent 𝓝∞ (fun u : ℝ => (gramLDeriv u) ^ 3) (fun u : ℝ => (gramLDeriv u) ^ 3) :=
    IsEquivalent.refl
  have h_step2 : IsEquivalent 𝓝∞
      (fun u : ℝ => (1 / 2 : ℝ) * (gram u)⁻¹ * (gramLDeriv u) ^ 3)
      (fun u : ℝ => (1 / 2 : ℝ) * (gramL u)⁻¹ * (gramLDeriv u) ^ 3) :=
    (h_const_eqv.mul gram_inv_isEquivalent_gramL_inv).mul h_gd_eqv
  -- Combine B1 + B2.
  have h_prod_eqv : IsEquivalent 𝓝∞
      (fun u : ℝ => iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 3)
      (fun u : ℝ => (1 / 2 : ℝ) * (gramL u)⁻¹ * (gramLDeriv u) ^ 3) :=
    h_step1.trans h_step2
  -- Multiply by the constant `-(1/π)` (treat as IsEquivalent.mul with refl).
  have h_constπ :
      IsEquivalent 𝓝∞
        (fun _ : ℝ => -(1 / Real.pi)) (fun _ : ℝ => -(1 / Real.pi)) :=
    IsEquivalent.refl
  have h_mul_const : IsEquivalent 𝓝∞
      (fun u : ℝ =>
        -(1 / Real.pi) * (iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 3))
      (fun u : ℝ =>
        -(1 / Real.pi) * ((1 / 2 : ℝ) * (gramL u)⁻¹ * (gramLDeriv u) ^ 3)) :=
    h_constπ.mul h_prod_eqv
  -- Regroup `-(1/π) · ((1/2) · …) = -(1/(2π)) · …` and apply
  -- `gramLeading_two_factorization` to land on `gramLeading 2 u`.
  have h_target_eq :
      (fun u : ℝ =>
        -(1 / Real.pi) * ((1 / 2 : ℝ) * (gramL u)⁻¹ * (gramLDeriv u) ^ 3))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ => gramLeading 2 u) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), log_pos_atTop] with u hu hlog
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
    have h_factor := gramLeading_two_factorization hu_ne hlog_ne
    -- `h_factor : -(1/(2π)) · (gramL u)⁻¹ · (gramLDeriv u)^3 = gramLeading 2 u`.
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h_regroup :
        -(1 / Real.pi) * ((1 / 2 : ℝ) * (gramL u)⁻¹ * (gramLDeriv u) ^ 3)
        = -(1 / (2 * Real.pi)) * (gramL u)⁻¹ * (gramLDeriv u) ^ 3 := by
      field_simp
    rw [h_regroup, h_factor]
  -- Massage the LHS of `h_mul_const` to match the RHS of `h_solved`.
  have h_lhs_eq :
      (fun u : ℝ =>
        -(1 / Real.pi) * (iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 3))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ =>
        -(1 / Real.pi) * iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 3) := by
    filter_upwards with u using by ring
  have h_eqv1 : IsEquivalent 𝓝∞
      (fun u : ℝ =>
        -(1 / Real.pi) * iteratedDeriv 2 theta (gram u) * (deriv gram u) ^ 3)
      (fun u : ℝ => gramLeading 2 u) := by
    refine (h_lhs_eq.symm.trans_isEquivalent h_mul_const).trans_eventuallyEq h_target_eq
  -- Finally, stitch `h_solved` (eventually-equal) with `h_eqv1`.
  exact h_solved.trans_isEquivalent h_eqv1

/-!
  ## §1.12  Refined θ''(gram u) bound

  Corollary 2 transported along `gram → ∞` gives
      `θ''(gram u) − (1/2)·(gram u)⁻¹ = O((gram u)⁻³)`.
  To refine the n = 2 case of Theorem 3 to the
  `(1 + 2 · log log u / log u)` precision, we need to upgrade this
  `O((gram u)⁻³)` bound to `o((gramL u)⁻¹ · log log u / log u)` — the
  same scale as the secondary correction term we want to expose.

  The argument hinges on `(gramL u)⁻² = o(log log u / log u)`, which
  reduces to `log³ u / u² → 0`.
-/

/-- `log³ u / u² → 0` as `u → +∞`.  (Polynomial growth of `u²` dominates
    any power of `log u`.) -/
private lemma log_cube_div_u_sq_tendsto_zero :
    Tendsto (fun u : ℝ => Real.log u ^ 3 / u ^ 2) 𝓝∞ (𝓝 0) := by
  have h_log_cube : (fun u : ℝ => Real.log u ^ 3) =o[(𝓝∞ : Filter ℝ)] (fun u : ℝ => u) :=
    Real.isLittleO_pow_log_id_atTop
  have h_quot : Tendsto (fun u : ℝ => Real.log u ^ 3 / u) (𝓝∞ : Filter ℝ) (𝓝 0) :=
    h_log_cube.tendsto_div_nhds_zero
  have h_inv : Tendsto (fun u : ℝ => u⁻¹) (𝓝∞ : Filter ℝ) (𝓝 0) := tendsto_inv_atTop_zero
  have h_prod : Tendsto (fun u : ℝ => (Real.log u ^ 3 / u) * u⁻¹) (𝓝∞ : Filter ℝ) (𝓝 (0 * 0)) :=
    h_quot.mul h_inv
  rw [mul_zero] at h_prod
  refine h_prod.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
  field_simp

/-- `(gramL u)⁻² = o(log log u / log u)` as `u → +∞`.

    Boils down to `log³ u / (4π² · u² · log log u) → 0`. -/
private lemma inv_gramL_sq_isLittleO_frac :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gramL u)⁻¹) ^ 2)
      (fun u : ℝ => Real.log (Real.log u) / Real.log u) := by
  refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
  · -- `frac u = 0 ⟹ (gramL u)⁻² = 0` (vacuously, since frac u > 0 eventually).
    filter_upwards [log_pos_atTop, loglog_pos_atTop] with u hu_log hu_loglog h_zero
    exfalso
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hu_log
    have h_loglog_zero : Real.log (Real.log u) = 0 := by
      rcases div_eq_zero_iff.mp h_zero with h | h
      · exact h
      · exact absurd h hlog_ne
    linarith
  · -- `((gramL u)⁻²) / (log log u / log u) → 0`.
    have h_log_cube := log_cube_div_u_sq_tendsto_zero
    have h_loglog_inv :
        Tendsto (fun u : ℝ => (Real.log (Real.log u))⁻¹) (𝓝∞ : Filter ℝ) (𝓝 0) := by
      have h := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
      exact h.inv_tendsto_atTop
    have h_prod : Tendsto
        (fun u : ℝ => (Real.log u ^ 3 / u ^ 2) * (4 * Real.pi ^ 2 : ℝ)⁻¹
                      * (Real.log (Real.log u))⁻¹)
        (𝓝∞ : Filter ℝ) (𝓝 (0 * (4 * Real.pi ^ 2 : ℝ)⁻¹ * 0)) := by
      exact ((h_log_cube.mul_const _).mul h_loglog_inv)
    have h_lim : (0 : ℝ) * (4 * Real.pi ^ 2 : ℝ)⁻¹ * 0 = 0 := by ring
    rw [h_lim] at h_prod
    refine h_prod.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), log_pos_atTop, loglog_pos_atTop]
      with u hu_pos hu_log hu_loglog
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hu_log
    have hloglog_ne : Real.log (Real.log u) ≠ 0 := ne_of_gt hu_loglog
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    change (Real.log u ^ 3 / u ^ 2) * (4 * Real.pi ^ 2 : ℝ)⁻¹ * (Real.log (Real.log u))⁻¹
      = ((gramL u)⁻¹) ^ 2 / (Real.log (Real.log u) / Real.log u)
    unfold gramL
    field_simp
    ring

/-- `(gram u)⁻¹ =O[𝓝∞] (gramL u)⁻¹`.  Follows from the equivalence
    `gram ~ gramL` (positivity is automatic since both → +∞). -/
private lemma inv_gram_isBigO_inv_gramL :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => (gram u)⁻¹) (fun u : ℝ => (gramL u)⁻¹) :=
  gram_inv_isEquivalent_gramL_inv.isBigO

/-- `(gram u)⁻² = o(log log u / log u)` as `u → +∞`.

    Composition of `gram⁻¹ ~ gramL⁻¹` (so `(gram u)⁻² ~ (gramL u)⁻²`)
    with `(gramL u)⁻² = o(frac u)`. -/
private lemma inv_gram_sq_isLittleO_frac :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gram u)⁻¹) ^ 2)
      (fun u : ℝ => Real.log (Real.log u) / Real.log u) := by
  have h_eqv : IsEquivalent (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gram u)⁻¹) ^ 2) (fun u : ℝ => ((gramL u)⁻¹) ^ 2) :=
    gram_inv_isEquivalent_gramL_inv.pow 2
  exact h_eqv.trans_isLittleO inv_gramL_sq_isLittleO_frac

/-- `(gram u)⁻³ = o((gramL u)⁻¹ · log log u / log u)`.

    Factor `(gram u)⁻³ = (gram u)⁻¹ · (gram u)⁻²`, then apply
    `O · o = o`. -/
private lemma inv_gram_cube_isLittleO_inv_gramL_mul_frac :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gram u)⁻¹) ^ 3)
      (fun u : ℝ => (gramL u)⁻¹ * (Real.log (Real.log u) / Real.log u)) := by
  have h_prod := inv_gram_isBigO_inv_gramL.mul_isLittleO inv_gram_sq_isLittleO_frac
  refine h_prod.congr_left ?_
  intro u; ring

/-- **Refined θ''(gram u) asymptotic.**

        θ''(gram u) − (1/2) · (gram u)⁻¹
          = o((gramL u)⁻¹ · log log u / log u)

    as `u → +∞`.  This is the n = 2 transport of Corollary 2 with the
    error term re-scaled to the precision used by Theorem 3. -/
private lemma iteratedDeriv_two_theta_at_gram_isLittleO_refined :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => iteratedDeriv 2 theta (gram u) - (1 / 2 : ℝ) * (gram u)⁻¹)
      (fun u : ℝ => (gramL u)⁻¹ * (Real.log (Real.log u) / Real.log u)) := by
  -- Raw IsO from Corollary 2 transport.
  have h_isO := iteratedDeriv_theta_at_gram_isO 2 (le_refl 2)
  -- Rewrite LHS to `θ''(gram u) - (1/2)·(gram u)⁻¹`.
  have h_lhs :
      (fun u : ℝ => iteratedDeriv 2 theta (gram u)
        - ((-1 : ℝ) ^ (2 : ℕ) * ((Nat.factorial (2 - 2) : ℕ) : ℝ)
            * (1 / 2) * (gram u) ^ (1 - (2 : ℝ))))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ =>
        iteratedDeriv 2 theta (gram u) - (1 / 2 : ℝ) * (gram u)⁻¹) := by
    filter_upwards with u
    have h_exp : (1 - (2 : ℝ)) = (-1 : ℝ) := by ring
    have h_rpow : (gram u) ^ (-1 : ℝ) = (gram u)⁻¹ := Real.rpow_neg_one _
    rw [h_exp, h_rpow]
    norm_num
  -- Rewrite RHS to `((gram u)⁻¹)^3`.
  have h_rhs :
      (fun u : ℝ => (gram u) ^ (-(2 : ℝ) - 1))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ => ((gram u)⁻¹) ^ 3) := by
    filter_upwards with u
    have h_exp : (-(2 : ℝ) - 1) = ((-3 : ℤ) : ℝ) := by push_cast; ring
    rw [h_exp, Real.rpow_intCast]
    change (gram u) ^ (-3 : ℤ) = ((gram u)⁻¹) ^ 3
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, inv_pow]
  -- IsO with `((gram u)⁻¹)^3` bound.
  have h_isO_clean :
      Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
        (fun u : ℝ =>
          iteratedDeriv 2 theta (gram u) - (1 / 2 : ℝ) * (gram u)⁻¹)
        (fun u : ℝ => ((gram u)⁻¹) ^ 3) :=
    (h_isO.congr' h_lhs h_rhs : _)
  -- Compose with `((gram u)⁻¹)^3 = o((gramL u)⁻¹ · frac u)`.
  exact h_isO_clean.trans_isLittleO inv_gram_cube_isLittleO_inv_gramL_mul_frac

/-!
  ## §1.13  Cubic-over-linear asymptotic expansion

  Abstract algebraic identity: if `δ, δ' = ε + o(ε)` and `ε → 0`, then

      (1 + δ)⁻¹ · (1 + δ')³ - (1 + 2ε) = o(ε).

  Applied to `δ := gram u / gramL u - 1` and
  `δ' := deriv gram u / gramLDeriv u - 1`, this yields the refined
  expansion of `(gram u)⁻¹ · (deriv gram u)³`:

      (gram u)⁻¹·(gram'(u))³
        = (gramL u)⁻¹·(gramLDeriv u)³·(1 + 2ε)
          + o((gramL u)⁻¹·(gramLDeriv u)³·ε).
-/

/-- **Abstract cubic-over-linear asymptotic.**  If `δ, δ' = ε + o(ε)`
    and `ε → 0`, then
        `(1 + δ)⁻¹ · (1 + δ')³ - (1 + 2ε) = o(ε)`. -/
private lemma prod_inv_cube_expansion_aux
    {α : Type*} {l : Filter α} {δ δ' ε : α → ℝ}
    (hδ : (fun u => δ u - ε u) =o[l] ε)
    (hδ' : (fun u => δ' u - ε u) =o[l] ε)
    (hε : Tendsto ε l (𝓝 0)) :
    (fun u => (1 + δ u)⁻¹ * (1 + δ' u) ^ 3 - (1 + 2 * ε u)) =o[l] ε := by
  -- (1) δ = O(ε), δ' = O(ε).
  have hδ_O : (fun u => δ u) =O[l] ε := by
    have h := hδ.isBigO.add (Asymptotics.isBigO_refl ε l)
    refine h.congr_left ?_
    intro u; ring
  have hδ'_O : (fun u => δ' u) =O[l] ε := by
    have h := hδ'.isBigO.add (Asymptotics.isBigO_refl ε l)
    refine h.congr_left ?_
    intro u; ring
  -- (2) δ, δ' → 0.
  have hδ_zero : Tendsto δ l (𝓝 0) := hδ_O.trans_tendsto hε
  have hδ'_zero : Tendsto δ' l (𝓝 0) := hδ'_O.trans_tendsto hε
  -- (3) δ = o(1), δ' = o(1).
  have hδ_o : (fun u => δ u) =o[l] (fun _ : α => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hδ_zero
  have hδ'_o : (fun u => δ' u) =o[l] (fun _ : α => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hδ'_zero
  -- (4) `1 + δ → 1`.
  have h_sum_tendsto : Tendsto (fun u => 1 + δ u) l (𝓝 1) := by
    have := hδ_zero.const_add 1
    simpa using this
  -- (5) `(1 + δ)⁻¹ → 1`, hence `=O 1`.
  have h_inv_tendsto : Tendsto (fun u => (1 + δ u)⁻¹) l (𝓝 1) := by
    have h := h_sum_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  have h_inv_O : (fun u => (1 + δ u)⁻¹) =O[l] (fun _ : α => (1 : ℝ)) :=
    h_inv_tendsto.isBigO_one ℝ
  -- (6) Eventually `1 + δ u ≠ 0`.
  have h_sum_ne : ∀ᶠ u in l, (1 + δ u) ≠ 0 :=
    h_sum_tendsto.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  -- (7) Build the bound `N(u) := 3(δ' - ε) - (δ - ε) + 3δ'² + δ'³ - 2εδ`,
  --     which equals the numerator `(1 + δ')³ - (1 + δ)(1 + 2ε)`.
  -- Show `N = o(ε)`.
  have h_term1 : (fun u => 3 * (δ' u - ε u)) =o[l] ε := hδ'.const_mul_left 3
  have h_term2 : (fun u => -(δ u - ε u)) =o[l] ε := hδ.neg_left
  have h_δ'_sq : (fun u => (δ' u) ^ 2) =o[l] ε := by
    have h := hδ'_o.mul_isBigO hδ'_O  -- o(1) · O(ε) =o (1·ε) = o(ε)
    refine h.congr ?_ ?_
    · intro u; ring  -- δ' u * δ' u = (δ' u)^2
    · intro u; ring  -- 1 * ε u = ε u
  have h_term3 : (fun u => 3 * (δ' u) ^ 2) =o[l] ε := h_δ'_sq.const_mul_left 3
  have h_δ'_cube : (fun u => (δ' u) ^ 3) =o[l] ε := by
    have h := hδ'_o.mul h_δ'_sq  -- o(1) · o(ε) =o (1·ε) = o(ε)
    refine h.congr ?_ ?_
    · intro u; ring  -- δ' u * (δ' u)^2 = (δ' u)^3
    · intro u; ring  -- 1 * ε u = ε u
  have h_εδ : (fun u => ε u * δ u) =o[l] ε := by
    have h := (Asymptotics.isBigO_refl ε l).mul_isLittleO hδ_o  -- O(ε) · o(1) =o (ε·1) = o(ε)
    refine h.congr_right ?_
    intro u; ring  -- ε u * 1 = ε u
  have h_term5 : (fun u => -(2 * (ε u * δ u))) =o[l] ε :=
    (h_εδ.const_mul_left 2).neg_left
  -- N = term1 + term2 + term3 + δ'^3 + term5 (rewritten as a sum of o(ε)'s).
  have h_N_o :
      (fun u => 3 * (δ' u - ε u) + -(δ u - ε u) + 3 * (δ' u) ^ 2 + (δ' u) ^ 3
                + -(2 * (ε u * δ u))) =o[l] ε :=
    ((((h_term1.add h_term2).add h_term3).add h_δ'_cube).add h_term5)
  -- Multiply by `(1 + δ)⁻¹ = O(1)`: still o(ε).
  have h_prod : (fun u => (1 + δ u)⁻¹ *
      (3 * (δ' u - ε u) + -(δ u - ε u) + 3 * (δ' u) ^ 2 + (δ' u) ^ 3
       + -(2 * (ε u * δ u))))
      =o[l] ε := by
    have h := h_inv_O.mul_isLittleO h_N_o
    refine h.congr_right ?_
    intro u; ring
  -- Final: rewrite to the target form using the algebraic identity.
  refine h_prod.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [h_sum_ne] with u hne
  show (1 + δ u)⁻¹ * (3 * (δ' u - ε u) + -(δ u - ε u) + 3 * (δ' u) ^ 2 + (δ' u) ^ 3
         + -(2 * (ε u * δ u)))
      = (1 + δ u)⁻¹ * (1 + δ' u) ^ 3 - (1 + 2 * ε u)
  field_simp
  ring

/-!
  ### §1.13.1  Cubic-over-linear expansion for the Gram function

  Specializing the abstract lemma to
    • `δ  := gram u / gramL u - 1`,
    • `δ' := deriv gram u / gramLDeriv u - 1`,
    • `ε  := log log u / log u`,
  with `δ - ε`, `δ' - ε` both `o(ε)` from the Lavrik / Korolev residuals.
-/

/-- `gram_asymp` restated using the `gramL` shorthand:
    `(gram − gramL − gramL · ε) =o (gramL · ε)`. -/
private lemma gram_asymp_in_gramL :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ =>
        gram u - gramL u - gramL u * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ => gramL u * (Real.log (Real.log u) / Real.log u)) := by
  have h := gram_asymp
  refine h.congr (fun u => by simp [gramL]) (fun u => by simp [gramL])

/-- `gram_deriv_asymp` restated using `gramLDeriv`. -/
private lemma gram_deriv_asymp_in_gramLDeriv :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ =>
        iteratedDeriv 1 gram u - gramLDeriv u
        - gramLDeriv u * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ => gramLDeriv u * (Real.log (Real.log u) / Real.log u)) := by
  have h := gram_deriv_asymp
  refine h.congr (fun u => by simp [gramLDeriv]) (fun u => by simp [gramLDeriv])

/-- `gram u / gramL u - 1 - log log u / log u = o(log log u / log u)` as
    `u → +∞`.  Direct consequence of `gram_asymp_in_gramL`. -/
private lemma gram_quot_residual :
    (fun u : ℝ => gram u / gramL u - 1 - (Real.log (Real.log u) / Real.log u))
      =o[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ => Real.log (Real.log u) / Real.log u) := by
  have h := gram_asymp_in_gramL
  -- Eventually gramL u ≠ 0.
  have hL_tendsto : Tendsto gramL (𝓝∞ : Filter ℝ) 𝓝∞ :=
    linear_div_log_tendsto_atTop.congr (fun u => by simp [gramL])
  have hL_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramL u ≠ 0 := by
    filter_upwards [hL_tendsto.eventually_gt_atTop (0 : ℝ)] with u hu
    exact ne_of_gt hu
  -- Multiply by (gramL u)⁻¹ on both sides.
  have h_mul := h.mul_isBigO (Asymptotics.isBigO_refl (fun u : ℝ => (gramL u)⁻¹) _)
  refine h_mul.congr' ?_ ?_
  · filter_upwards [hL_ne] with u hLu
    field_simp
  · filter_upwards [hL_ne] with u hLu
    field_simp

/-- `deriv gram u / gramLDeriv u - 1 - log log u / log u
      = o(log log u / log u)`. -/
private lemma deriv_gram_quot_residual :
    (fun u : ℝ =>
      deriv gram u / gramLDeriv u - 1 - (Real.log (Real.log u) / Real.log u))
      =o[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ => Real.log (Real.log u) / Real.log u) := by
  have h := gram_deriv_asymp_in_gramLDeriv
  -- Eventually gramLDeriv u ≠ 0.
  have hL'_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramLDeriv u ≠ 0 := by
    filter_upwards [log_pos_atTop] with u hu
    unfold gramLDeriv
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hu
    positivity
  have h_mul := h.mul_isBigO (Asymptotics.isBigO_refl (fun u : ℝ => (gramLDeriv u)⁻¹) _)
  refine h_mul.congr' ?_ ?_
  · filter_upwards [hL'_ne] with u hL'u
    rw [iteratedDeriv_one]
    field_simp
  · filter_upwards [hL'_ne] with u hL'u
    field_simp

/-- `frac u = log log u / log u → 0` as `u → +∞`. -/
private lemma frac_tendsto_zero :
    Tendsto (fun u : ℝ => Real.log (Real.log u) / Real.log u) (𝓝∞ : Filter ℝ) (𝓝 0) := by
  have h := loglog_div_log_isLittleO_one
  exact (Asymptotics.isLittleO_one_iff ℝ).mp h

/-- **Cubic-over-linear expansion** for the Gram function:

      (gram u)⁻¹ · (deriv gram u)^3
        = (gramL u)⁻¹ · (gramLDeriv u)^3 · (1 + 2 · log log u / log u)
          + o((gramL u)⁻¹ · (gramLDeriv u)^3 · log log u / log u). -/
private lemma inv_gram_mul_deriv_gram_cube_expansion :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => (gram u)⁻¹ * (deriv gram u) ^ 3
        - (gramL u)⁻¹ * (gramLDeriv u) ^ 3
            * (1 + 2 * (Real.log (Real.log u) / Real.log u)))
      (fun u : ℝ => (gramL u)⁻¹ * (gramLDeriv u) ^ 3
        * (Real.log (Real.log u) / Real.log u)) := by
  -- Set δ := gram u / gramL u - 1, δ' := deriv gram u / gramLDeriv u - 1.
  -- Then (gram u)⁻¹ · (deriv gram u)^3 / ((gramL u)⁻¹ · (gramLDeriv u)^3)
  --    = (1 + δ)⁻¹ · (1 + δ')^3 (when gramL u, gramLDeriv u ≠ 0 and 1+δ ≠ 0).
  set δ : ℝ → ℝ := fun u => gram u / gramL u - 1 with hδ_def
  set δ' : ℝ → ℝ := fun u => deriv gram u / gramLDeriv u - 1 with hδ'_def
  set ε : ℝ → ℝ := fun u => Real.log (Real.log u) / Real.log u with hε_def
  -- Hypotheses for the abstract lemma.
  have hδ_resid : (fun u => δ u - ε u) =o[(𝓝∞ : Filter ℝ)] ε := by
    have := gram_quot_residual
    refine this.congr_left ?_
    intro u
    change gram u / gramL u - 1 - Real.log (Real.log u) / Real.log u
        = (gram u / gramL u - 1) - Real.log (Real.log u) / Real.log u
    ring
  have hδ'_resid : (fun u => δ' u - ε u) =o[(𝓝∞ : Filter ℝ)] ε := by
    have := deriv_gram_quot_residual
    refine this.congr_left ?_
    intro u
    change deriv gram u / gramLDeriv u - 1 - Real.log (Real.log u) / Real.log u
        = (deriv gram u / gramLDeriv u - 1) - Real.log (Real.log u) / Real.log u
    ring
  have hε_tendsto : Tendsto ε (𝓝∞ : Filter ℝ) (𝓝 0) := frac_tendsto_zero
  -- Apply the abstract lemma.
  have h_abstract := prod_inv_cube_expansion_aux hδ_resid hδ'_resid hε_tendsto
  -- h_abstract : (fun u => (1 + δ u)⁻¹ * (1 + δ' u)^3 - (1 + 2 * ε u)) =o ε.
  -- Multiply both sides by (gramL u)⁻¹ * (gramLDeriv u)^3 (=O of itself).
  have h_factor :
      Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
        (fun u : ℝ => (gramL u)⁻¹ * (gramLDeriv u) ^ 3)
        (fun u : ℝ => (gramL u)⁻¹ * (gramLDeriv u) ^ 3) :=
    Asymptotics.isBigO_refl _ _
  have h_mul := h_factor.mul_isLittleO h_abstract
  -- h_mul : (fun u => F · ((1+δ)⁻¹(1+δ')³ - (1+2ε))) =o (F · ε)
  -- where F := (gramL u)⁻¹ * (gramLDeriv u)^3.
  -- Rewrite both sides to match the target.
  refine h_mul.congr' ?_ ?_
  · -- LHS: F·((1+δ)⁻¹(1+δ')³ - (1+2ε))
    --     = F·(1+δ)⁻¹(1+δ')³ - F·(1+2ε)
    --     = (gram u)⁻¹·(deriv gram u)³ - (gramL u)⁻¹·(gramLDeriv u)³·(1+2ε)
    --   (provided gramL u, gramLDeriv u ≠ 0)
    have hL_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramL u ≠ 0 := by
      have hL_tendsto : Tendsto gramL (𝓝∞ : Filter ℝ) 𝓝∞ :=
        linear_div_log_tendsto_atTop.congr (fun u => by simp [gramL])
      filter_upwards [hL_tendsto.eventually_gt_atTop (0 : ℝ)] with u hu
      exact ne_of_gt hu
    have hL'_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramLDeriv u ≠ 0 := by
      filter_upwards [log_pos_atTop] with u hu
      unfold gramLDeriv
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      have hlog_ne : Real.log u ≠ 0 := ne_of_gt hu
      positivity
    filter_upwards [hL_ne, hL'_ne] with u hLu hL'u
    change (gramL u)⁻¹ * (gramLDeriv u) ^ 3
          * ((1 + δ u)⁻¹ * (1 + δ' u) ^ 3 - (1 + 2 * ε u))
        = (gram u)⁻¹ * (deriv gram u) ^ 3
          - (gramL u)⁻¹ * (gramLDeriv u) ^ 3 * (1 + 2 * ε u)
    have hδ_val : 1 + δ u = gram u / gramL u := by
      change 1 + (gram u / gramL u - 1) = gram u / gramL u
      ring
    have hδ'_val : 1 + δ' u = deriv gram u / gramLDeriv u := by
      change 1 + (deriv gram u / gramLDeriv u - 1) = deriv gram u / gramLDeriv u
      ring
    rw [hδ_val, hδ'_val]
    field_simp
  · -- RHS: F · ε = (gramL u)⁻¹ * (gramLDeriv u)^3 * ε. Same as goal RHS.
    rfl

/-!
  ## §1.14  Theorem 3, n = 2 case

  Assembly: combine
    • `iteratedDeriv_two_gram_eventually_eq`  — solved form,
    • `iteratedDeriv_two_theta_at_gram_isLittleO_refined`  — refined θ'',
    • `inv_gram_mul_deriv_gram_cube_expansion`  — cubic-over-linear,
    • `gramLeading_two_factorization`  — algebraic identity,
  to prove the n = 2 case of Theorem 3.
-/

/-- **Theorem 3, n = 2 case.**

    `iteratedDeriv 2 gram u
       - gramLeading 2 u
       - 2 · gramLeading 2 u · (log log u / log u)
     = o(gramLeading 2 u · (log log u / log u))`

    as `u → +∞`.  Equivalently,

    `t_u'' = (gramLeading 2)(u) · (1 + (2 + o(1)) · log log u / log u)`. -/
private theorem theorem3_two :
    Iso
      (fun u : ℝ =>
        iteratedDeriv 2 gram u
        - gramLeading 2 u
        - 2 * gramLeading 2 u * Real.log (Real.log u) / Real.log u)
      (fun u : ℝ => gramLeading 2 u * Real.log (Real.log u) / Real.log u)
      𝓝∞ := by
  -- Shorthand `F := (gramL u)⁻¹ · (gramLDeriv u)^3` so that
  -- `gramLeading 2 u = -(1/(2π)) · F u` (eventually).
  set F : ℝ → ℝ := fun u => (gramL u)⁻¹ * (gramLDeriv u) ^ 3 with hF_def
  -- (i) `r_θ · (deriv gram u)^3 = o(F · frac)`.
  have h_rθ_mul :
      (fun u : ℝ =>
        (iteratedDeriv 2 theta (gram u) - (1 / 2 : ℝ) * (gram u)⁻¹)
          * (deriv gram u) ^ 3)
        =o[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u)) := by
    have h_rθ := iteratedDeriv_two_theta_at_gram_isLittleO_refined
    have h_deriv_cube_O :
        (fun u : ℝ => (deriv gram u) ^ 3) =O[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => (gramLDeriv u) ^ 3) :=
      deriv_gram_pow_three_isEquivalent.isBigO
    have h := h_rθ.mul_isBigO h_deriv_cube_O
    refine h.congr_right ?_
    intro u
    change (gramL u)⁻¹ * (Real.log (Real.log u) / Real.log u) * (gramLDeriv u) ^ 3
        = (gramL u)⁻¹ * (gramLDeriv u) ^ 3 * (Real.log (Real.log u) / Real.log u)
    ring
  -- (ii) `s₁ := (gram u)⁻¹ · (deriv gram u)³ - F · (1 + 2 · frac) = o(F · frac)`.
  have h_s1 := inv_gram_mul_deriv_gram_cube_expansion
  -- (iii) Multiply (i) by `-(1/π)` and (ii) by `-(1/(2π))`.
  have h_term1 :
      (fun u : ℝ =>
        -(1 / Real.pi) * ((iteratedDeriv 2 theta (gram u) - (1 / 2 : ℝ) * (gram u)⁻¹)
                          * (deriv gram u) ^ 3))
        =o[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u)) :=
    h_rθ_mul.const_mul_left _
  have h_term2 :
      (fun u : ℝ =>
        -(1 / (2 * Real.pi)) * ((gram u)⁻¹ * (deriv gram u) ^ 3
          - F u * (1 + 2 * (Real.log (Real.log u) / Real.log u))))
        =o[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u)) :=
    h_s1.const_mul_left _
  have h_sum := h_term1.add h_term2
  -- (iv) Algebraic identity: the sum equals
  --      `iteratedDeriv 2 gram u - gramLeading 2 u - 2·gramLeading 2 u · frac u`
  --      (eventually).
  have hL_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramL u ≠ 0 := by
    have hL_tendsto : Tendsto gramL (𝓝∞ : Filter ℝ) 𝓝∞ :=
      linear_div_log_tendsto_atTop.congr (fun u => by simp [gramL])
    filter_upwards [hL_tendsto.eventually_gt_atTop (0 : ℝ)] with u hu
    exact ne_of_gt hu
  have hL'_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramLDeriv u ≠ 0 := by
    filter_upwards [log_pos_atTop] with u hu
    unfold gramLDeriv
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hu
    positivity
  have h_solved := iteratedDeriv_two_gram_eventually_eq
  have h_lhs_eq :
      (fun u : ℝ =>
        -(1 / Real.pi) * ((iteratedDeriv 2 theta (gram u) - (1 / 2 : ℝ) * (gram u)⁻¹)
                          * (deriv gram u) ^ 3)
        + -(1 / (2 * Real.pi)) * ((gram u)⁻¹ * (deriv gram u) ^ 3
          - F u * (1 + 2 * (Real.log (Real.log u) / Real.log u))))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ =>
        iteratedDeriv 2 gram u
        - gramLeading 2 u
        - 2 * gramLeading 2 u * Real.log (Real.log u) / Real.log u) := by
    filter_upwards [h_solved, Filter.eventually_gt_atTop (0 : ℝ), log_pos_atTop,
                    hL_ne, hL'_ne]
      with u h_id hu hlog hLu hL'u
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h_F_val : F u = (gramL u)⁻¹ * (gramLDeriv u) ^ 3 := rfl
    have h_factor := gramLeading_two_factorization hu_ne hlog_ne
    -- `h_factor : -(1/(2π)) · (gramL u)⁻¹ · (gramLDeriv u)^3 = gramLeading 2 u`
    -- i.e., `-(1/(2π)) · F u = gramLeading 2 u`.
    have h_gramLeading_val : gramLeading 2 u = -(1 / (2 * Real.pi)) * F u := by
      rw [h_F_val]; linarith
    rw [h_id, h_gramLeading_val]
    ring
  -- (v) Apply `h_lhs_eq` to `h_sum`.
  have h_E_isO_F :
      (fun u : ℝ =>
        iteratedDeriv 2 gram u
        - gramLeading 2 u
        - 2 * gramLeading 2 u * Real.log (Real.log u) / Real.log u)
        =o[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u)) :=
    h_sum.congr' h_lhs_eq Filter.EventuallyEq.rfl
  -- (vi) Convert RHS from `F · (log log u / log u)` to
  --      `gramLeading 2 u * (log log u) / log u` via the eventual factorisation
  --      `F u = -(2π) · gramLeading 2 u`.
  have h_RHS_eq :
      (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ =>
        -(2 * Real.pi) * (gramLeading 2 u * Real.log (Real.log u) / Real.log u)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), log_pos_atTop] with u hu hlog
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h_F_val : F u = (gramL u)⁻¹ * (gramLDeriv u) ^ 3 := rfl
    have h_factor := gramLeading_two_factorization hu_ne hlog_ne
    have h_F_to_gramLeading : F u = -(2 * Real.pi) * gramLeading 2 u := by
      rw [h_F_val]
      have hπ2 : (2 * Real.pi) ≠ 0 := by positivity
      have : gramLeading 2 u = -(1 / (2 * Real.pi)) * ((gramL u)⁻¹ * (gramLDeriv u) ^ 3) := by
        rw [← h_factor]; ring
      rw [this]; field_simp
    rw [h_F_to_gramLeading]; ring
  have h_E_isO_RHS' :=
    h_E_isO_F.congr' Filter.EventuallyEq.rfl h_RHS_eq
  -- (vii) Remove the constant factor `-(2π)`.
  have hπ2 : -(2 * Real.pi) ≠ (0 : ℝ) := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have : (2 * Real.pi) ≠ 0 := by positivity
    intro h; apply this; linarith
  exact (Asymptotics.isLittleO_const_mul_right_iff hπ2).mp h_E_isO_RHS'

/-!
  ## §2.0  Strong-IH packaging

  The inductive hypothesis we carry through the proof of Theorem 3 is the
  full `(1 + (2 + o(1))·ll/l)` precision at every index `k ≥ 2`, packaged
  as the predicate `GramAsymp k`.  From this we derive the two
  asymptotic-equivalence consequences (`iteratedDeriv k gram ~ gramLeading k`
  and the corresponding `IsBigO` bound) used throughout the induction step.
-/

/-- The inductive-hypothesis predicate for Theorem 3 at index `k`.

    For `k ≥ 2`, `GramAsymp k` packages the asymptotic
        t_u^(k) = gramLeading k u · (1 + (2 + o(1)) · log log u / log u). -/
private def GramAsymp (k : ℕ) : Prop :=
  Iso
    (fun u : ℝ =>
      iteratedDeriv k gram u - gramLeading k u
      - 2 * gramLeading k u * Real.log (Real.log u) / Real.log u)
    (fun u : ℝ => gramLeading k u * Real.log (Real.log u) / Real.log u)
    𝓝∞

/-- `theorem3_two` repackaged as `GramAsymp 2`. -/
private lemma gramAsymp_two : GramAsymp 2 := theorem3_two

/-- `gramLeading k u * log log u / log u =o[𝓝∞] gramLeading k u`.

    Uses the left-associative grouping `(a * b) / c` (matching `GramAsymp`),
    not the parenthesised `a * (b / c)`. -/
private lemma gramLeading_mul_loglog_isLittleO_gramLeading (k : ℕ) :
    Iso (fun u : ℝ => gramLeading k u * Real.log (Real.log u) / Real.log u)
        (gramLeading k) 𝓝∞ := by
  have h : (fun u : ℝ => gramLeading k u * (Real.log (Real.log u) / Real.log u))
      =o[(𝓝∞ : Filter ℝ)] gramLeading k := by
    have h0 := (Asymptotics.isBigO_refl (gramLeading k) 𝓝∞).mul_isLittleO
                  loglog_div_log_isLittleO_one
    simpa using h0
  refine h.congr_left ?_
  intro u
  ring

/-- From `GramAsymp k` (the `(2 + o(1))·ll/l` precision form), derive the
    asymptotic equivalence `iteratedDeriv k gram - gramLeading k = o(gramLeading k)`. -/
private lemma iteratedDeriv_sub_gramLeading_isLittleO
    {k : ℕ} (h : GramAsymp k) :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => iteratedDeriv k gram u - gramLeading k u)
      (gramLeading k) := by
  have h_mll := gramLeading_mul_loglog_isLittleO_gramLeading k
  -- residual part (h itself) is =o(gramLeading k · ll/l) =o gramLeading k.
  have h1 : Asymptotics.IsLittleO 𝓝∞
      (fun u : ℝ =>
        iteratedDeriv k gram u - gramLeading k u
        - 2 * gramLeading k u * Real.log (Real.log u) / Real.log u)
      (gramLeading k) := h.trans h_mll
  -- the `2 · gramLeading k · ll/l` correction is also =o gramLeading k.
  have h2 : Asymptotics.IsLittleO 𝓝∞
      (fun u : ℝ => 2 * gramLeading k u * Real.log (Real.log u) / Real.log u)
      (gramLeading k) := by
    have h' := h_mll.const_mul_left (c := (2 : ℝ))
    refine h'.congr_left ?_
    intro u
    ring
  have h_sum := h1.add h2
  refine h_sum.congr_left ?_
  intro u; ring

/-- `iteratedDeriv k gram ~[𝓝∞] gramLeading k`, derived from `GramAsymp k`. -/
private lemma iteratedDeriv_isEquivalent_gramLeading
    {k : ℕ} (h : GramAsymp k) :
    IsEquivalent 𝓝∞ (iteratedDeriv k gram) (gramLeading k) :=
  iteratedDeriv_sub_gramLeading_isLittleO h

/-- `iteratedDeriv k gram =O[𝓝∞] gramLeading k`, derived from `GramAsymp k`. -/
private lemma iteratedDeriv_isBigO_gramLeading
    {k : ℕ} (h : GramAsymp k) :
    Asymptotics.IsBigO 𝓝∞ (iteratedDeriv k gram) (gramLeading k) :=
  (iteratedDeriv_isEquivalent_gramLeading h).isBigO

/-!
  ## §2.1  Faà di Bruno expansion at `θ ∘ gram`

  Generalises the `n = 2` setup `faadi_bruno_gram_two` (§1.10) to arbitrary
  `n ≥ 2`.  Combines:
    • `iteratedDeriv_comp_eq_sum_orderedFinpartition` from Mathlib's
      Faà di Bruno API (works for any `n` via partitions of `Fin n`);
    • the linearity of `θ ∘ gram` on `Ioi gramThreshold`, which forces every
      iterated derivative `≥ 2` of `θ ∘ gram` to vanish.
-/

/-- For `n ≥ 2`, the `n`-th iterated derivative of the linear function
    `s ↦ (s − 1) · π` vanishes everywhere. -/
private lemma iteratedDeriv_linear_eq_zero (n : ℕ) (hn : 2 ≤ n) (u : ℝ) :
    iteratedDeriv n (fun s : ℝ => (s - 1) * Real.pi) u = 0 := by
  have hderiv : deriv (fun s : ℝ => (s - 1) * Real.pi) = fun _ : ℝ => Real.pi := by
    funext x
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have h2 : HasDerivAt (fun s : ℝ => (s - 1) * Real.pi) Real.pi x := by
      simpa using h1.mul_const Real.pi
    exact h2.deriv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [iteratedDeriv_succ', hderiv]
  exact iteratedDeriv_const_eq_zero (by omega) Real.pi u

/-- **Faà di Bruno applied to `θ ∘ gram`.**  For `n ≥ 2`, at every point
    `u > gramThreshold` with `gram u > 0`:

        0 = ∑ c : OrderedFinpartition n,
              θ^(c.length)(gram u) · ∏ j, iteratedDeriv (c.partSize j) gram u.

    The `0` on the LHS comes from `θ ∘ gram = (s ↦ (s − 1)π)` on
    `Ioi gramThreshold` and the iterated derivative of a linear function
    vanishing at order `≥ 2`.  The RHS is Mathlib's
    `iteratedDeriv_comp_eq_sum_orderedFinpartition`. -/
private lemma faadi_bruno_gram (n : ℕ) (hn : 2 ≤ n) (u : ℝ)
    (hu : gramThreshold < u) (hg : 0 < gram u) :
    (0 : ℝ) =
      ∑ c : OrderedFinpartition n,
        iteratedDeriv c.length theta (gram u)
          * ∏ j, iteratedDeriv (c.partSize j) gram u := by
  -- (1) θ ∘ gram = (s ↦ (s − 1)π) on Ioi gramThreshold.
  have hθg_eq : ∀ s ∈ Set.Ioi gramThreshold,
      (theta ∘ gram) s = (s - 1) * Real.pi := by
    intro s hs
    simp [Function.comp_apply, gram_spec s hs.le]
  -- (2) Lift the pointwise equality to iterated derivatives on the open set.
  have h_iter_eq :
      iteratedDeriv n (theta ∘ gram) u
        = iteratedDeriv n (fun s : ℝ => (s - 1) * Real.pi) u :=
    iteratedDeriv_congr_of_nhds n isOpen_Ioi hθg_eq u hu
  -- (3) The RHS is 0.
  have h_rhs : iteratedDeriv n (fun s : ℝ => (s - 1) * Real.pi) u = 0 :=
    iteratedDeriv_linear_eq_zero n hn u
  -- (4) Expand the LHS via Faà di Bruno.
  have hθ : ContDiffAt ℝ n theta (gram u) := contDiffAt_theta n hg
  have hg_smooth : ContDiffAt ℝ n gram u := contDiffAt_gram n hu
  have h_comp :
      iteratedDeriv n (theta ∘ gram) u
        = ∑ c : OrderedFinpartition n,
            iteratedDeriv c.length theta (gram u)
              * ∏ j, iteratedDeriv (c.partSize j) gram u :=
    iteratedDeriv_comp_eq_sum_orderedFinpartition hθ hg_smooth le_rfl
  -- (5) Combine.
  linarith [h_iter_eq.trans h_rhs, h_comp]

/-- Eventually-equality version of `faadi_bruno_gram`, packaged for use
    with `EventuallyEq.trans_isBigO` / `IsLittleO.congr`. -/
private lemma faadi_bruno_gram_eventually (n : ℕ) (hn : 2 ≤ n) :
    (fun _ : ℝ => (0 : ℝ))
      =ᶠ[(𝓝∞ : Filter ℝ)]
    (fun u : ℝ =>
      ∑ c : OrderedFinpartition n,
        iteratedDeriv c.length theta (gram u)
          * ∏ j, iteratedDeriv (c.partSize j) gram u) := by
  filter_upwards [Filter.eventually_gt_atTop gramThreshold, eventually_gram_pos]
    with u hu hg
  exact faadi_bruno_gram n hn u hu hg

/-!
  ## §2.2  Partition classification

  Two distinguished partitions of `Fin n` (for `n ≥ 1`) drive the analysis:

    • `cTarget n hn` — length 1, single part of size `n`.  Its Faà di Bruno
      contribution is `θ′(gram u) · iteratedDeriv n gram u`, the term we
      solve for.
    • `OrderedFinpartition.atomic n` — length `n`, all parts of size 1.
      Its contribution is `θ^(n)(gram u) · (deriv gram u)^n`, the dominant
      non-target term.

  All other partitions form the finset `cOther n hn`; for these we will
  show every part has size `< n` (needed to invoke the inductive hypothesis).
-/

/-- The unique length-1 ordered finpartition of `Fin n`: a single part of
    size `n`, embedded as the identity `Fin n → Fin n`. -/
private def cTarget (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize := fun _ => n
  partSize_pos := fun _ => hn
  emb := fun _ j => j
  emb_strictMono := fun _ => strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro a _ b _ h
    exact absurd (Subsingleton.elim a b) h
  cover j := ⟨⟨0, Nat.one_pos⟩, j, rfl⟩

@[simp] private lemma cTarget_length (n : ℕ) (hn : 0 < n) :
    (cTarget n hn).length = 1 := rfl

@[simp] private lemma cTarget_partSize (n : ℕ) (hn : 0 < n)
    (i : Fin (cTarget n hn).length) :
    (cTarget n hn).partSize i = n := rfl

/-- Sum of part sizes equals `n`.  This is the cardinality of `Fin n` viewed
    as the disjoint union (via `equivSigma`) of the parts. -/
private lemma sum_partSize_eq {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  classical
  calc ∑ i, c.partSize i
      = ∑ i, Fintype.card (Fin (c.partSize i)) := by
        simp [Fintype.card_fin]
    _ = Fintype.card (Σ i, Fin (c.partSize i)) := by rw [Fintype.card_sigma]
    _ = Fintype.card (Fin n) := Fintype.card_congr c.equivSigma
    _ = n := Fintype.card_fin _

/-- For a strictly-monotone surjection `f : Fin n → Fin n`, `f = id`.

    Standard inductive argument: `f 0 = 0` by surjectivity together with
    `0` being the minimum, and then for each `k`, `f (k+1) = k+1` by
    bounding `j` (the unique preimage of `k+1`) between `k+1` and `k+1`. -/
private lemma fin_strictMono_surj_eq_id {n : ℕ} {f : Fin n → Fin n}
    (h_mono : StrictMono f) (h_surj : Function.Surjective f) :
    ∀ i : Fin n, f i = i := by
  suffices key : ∀ k : ℕ, ∀ hk : k < n, f ⟨k, hk⟩ = ⟨k, hk⟩ by
    intro i
    have := key i.val i.isLt
    simpa [Fin.eta] using this
  intro k
  induction k with
  | zero =>
    intro hk
    obtain ⟨j, hj⟩ := h_surj ⟨0, hk⟩
    have h_le : f ⟨0, hk⟩ ≤ f j := h_mono.monotone (by
      rw [Fin.le_iff_val_le_val]; exact Nat.zero_le _)
    rw [hj] at h_le
    have h_zero : (f ⟨0, hk⟩).val ≤ 0 := h_le
    exact Fin.eq_of_val_eq (Nat.le_zero.mp h_zero)
  | succ k ih =>
    intro hk
    have hk' : k < n := by omega
    have h_prev := ih hk'
    obtain ⟨j, hj⟩ := h_surj ⟨k+1, hk⟩
    -- Pre-compute lower bound on (f ⟨k+1, hk⟩).val from IH + strict mono.
    have h_lower : k < (f ⟨k+1, hk⟩).val := by
      have h_lt : (⟨k, hk'⟩ : Fin n) < ⟨k+1, hk⟩ := by
        exact Fin.mk_lt_mk.mpr (by omega)
      have h_mono_lt := h_mono h_lt
      rw [h_prev] at h_mono_lt
      exact h_mono_lt
    have h_j_le : j.val ≤ k + 1 := by
      by_contra h_gt
      push_neg at h_gt
      have h_jlt : (⟨k+1, hk⟩ : Fin n) < j := by
        exact Fin.mk_lt_mk.mpr (by omega)
      have h_strict := h_mono h_jlt
      rw [hj] at h_strict
      -- h_strict : f ⟨k+1, hk⟩ < ⟨k+1, hk⟩, so (f ⟨k+1, hk⟩).val < k+1.
      have h_upper : (f ⟨k+1, hk⟩).val < k + 1 := h_strict
      omega  -- combined with h_lower: k < ... < k+1, contradiction.
    have h_j_ge : k + 1 ≤ j.val := by
      by_contra h_lt
      push_neg at h_lt
      have h_j_le_k : j.val ≤ k := Nat.lt_succ_iff.mp h_lt
      have h_jle : j ≤ (⟨k, hk'⟩ : Fin n) := by
        rw [Fin.le_iff_val_le_val]; exact h_j_le_k
      have h_fj_le : f j ≤ f ⟨k, hk'⟩ := h_mono.monotone h_jle
      rw [h_prev, hj] at h_fj_le
      have : k + 1 ≤ k := h_fj_le
      omega
    have h_j_val : j.val = k + 1 := le_antisymm h_j_le h_j_ge
    have h_j_eq : j = ⟨k+1, hk⟩ := Fin.eq_of_val_eq h_j_val
    rw [h_j_eq] at hj
    exact hj

/-- **Uniqueness of the length-1 partition**: any `c : OrderedFinpartition n`
    with `c.length = 1` is `cTarget n hn`. -/
private lemma eq_cTarget_of_length_one {n : ℕ} (hn : 0 < n)
    (c : OrderedFinpartition n) (h_len : c.length = 1) :
    c = cTarget n hn := by
  -- Use the abstract `sum_partSize_eq` BEFORE destructuring (avoids
  -- reconstructing the equivSigma inside a destructured shape).
  have h_sum_abs := sum_partSize_eq c
  rcases c with ⟨length, partSize, partSize_pos, emb, emb_strictMono,
                  parts_strictMono, disjoint, cover⟩
  simp only at h_len
  subst h_len
  -- Now `length = 1` everywhere.
  -- Step 1: partSize 0 = n via the (already-proved) sum identity.
  have h_ps_zero : partSize 0 = n := by
    have := h_sum_abs
    rw [Fin.sum_univ_one] at this
    exact this
  -- Step 2: partSize is constant n.
  have h_partSize_eq : partSize = (fun _ : Fin 1 => n) := by
    funext i
    have : i = 0 := Subsingleton.elim _ _
    rw [this]; exact h_ps_zero
  subst h_partSize_eq
  -- Step 3: emb is the identity (after partSize substitution, emb 0 : Fin n → Fin n).
  have h_emb_id : ∀ j, emb 0 j = j := by
    apply fin_strictMono_surj_eq_id (emb_strictMono 0)
    intro j
    obtain ⟨m, r, hr⟩ := cover j
    refine ⟨r, ?_⟩
    have hm : m = 0 := Subsingleton.elim _ _
    rw [← hm]; exact hr
  have h_emb_eq : emb = (fun _ j => j) := by
    funext m j
    have : m = 0 := Subsingleton.elim _ _
    rw [this]; exact h_emb_id j
  subst h_emb_eq
  rfl

/-- For `c : OrderedFinpartition n` with `c.length ≥ 2`, every part has
    size `< n`.  By the sum identity, `partSize j + (length − 1) ≤ n`. -/
private lemma partSize_lt_of_length_ge_two {n : ℕ}
    (c : OrderedFinpartition n) (h_len : 2 ≤ c.length)
    (j : Fin c.length) : c.partSize j < n := by
  have h_sum := sum_partSize_eq c
  have h_pos : 0 < c.length := by omega
  -- Pull out partSize j and bound the rest.
  have h_split :
      c.partSize j + ∑ i ∈ Finset.univ.erase j, c.partSize i = n := by
    have h_erase := Finset.add_sum_erase (Finset.univ : Finset (Fin c.length))
                                          c.partSize (Finset.mem_univ j)
    rw [h_erase]; exact h_sum
  have h_rest_ge :
      (c.length - 1 : ℕ) ≤ ∑ i ∈ Finset.univ.erase j, c.partSize i := by
    have h_card : (Finset.univ.erase j : Finset (Fin c.length)).card
                    = c.length - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin]
    rw [← h_card]
    calc ((Finset.univ.erase j : Finset (Fin c.length)).card : ℕ)
        = ∑ _i ∈ Finset.univ.erase j, 1 := by simp
      _ ≤ ∑ i ∈ Finset.univ.erase j, c.partSize i :=
          Finset.sum_le_sum (fun i _ => c.partSize_pos i)
  omega

/-- The "other" partitions: everything except `cTarget` and `atomic`. -/
private noncomputable def cOther (n : ℕ) (hn : 0 < n) :
    Finset (OrderedFinpartition n) :=
  (Finset.univ.erase (cTarget n hn)).erase (OrderedFinpartition.atomic n)

/-- For `n ≥ 3`, `cTarget ≠ atomic`. -/
private lemma cTarget_ne_atomic (n : ℕ) (hn : 2 ≤ n) :
    cTarget n (by omega) ≠ OrderedFinpartition.atomic n := by
  intro h_eq
  have : (1 : ℕ) = n := by
    have := congr_arg OrderedFinpartition.length h_eq
    simpa using this
  omega

/-- For `c ∈ cOther`, every part has size `< n`.

    Proof: `c ≠ cTarget` and `c.length ≥ 1` (since `n ≥ 1`).  We show
    `c.length ≥ 2`: otherwise `c.length = 1` would force `c = cTarget` by
    `eq_cTarget_of_length_one`, contradicting `c ≠ cTarget`. -/
private lemma partSize_lt_of_mem_cOther {n : ℕ} (hn : 2 ≤ n)
    {c : OrderedFinpartition n} (hc : c ∈ cOther n (by omega))
    (j : Fin c.length) : c.partSize j < n := by
  have h_ne_target : c ≠ cTarget n (by omega) := by
    intro h_eq
    -- c ∈ erase (erase univ cTarget) atomic ⟹ c ≠ cTarget.
    have h1 : c ∈ Finset.univ.erase (cTarget n (by omega)) := by
      exact (Finset.mem_erase.mp hc).2
    have : c ≠ cTarget n (by omega) := (Finset.mem_erase.mp h1).1
    exact this h_eq
  have h_pos : 0 < c.length := by
    -- partition of nonempty Fin n must have length ≥ 1
    have := c.length_pos (by omega : 0 < n)
    exact this
  by_cases h_len_one : c.length = 1
  · exact absurd (eq_cTarget_of_length_one (by omega : 0 < n) c h_len_one) h_ne_target
  · have h_ge_two : 2 ≤ c.length := by omega
    exact partSize_lt_of_length_ge_two c h_ge_two j

/-!
  ## §2.3  Solve for `iteratedDeriv n gram u`

  The Faà di Bruno equation `0 = ∑ c, term c` splits into three pieces:
    • the **target** at `c = cTarget`, contributing
        `θ′(gram u) · iteratedDeriv n gram u`,
    • the **atomic** at `c = atomic`, contributing
        `θ^(n)(gram u) · (deriv gram u)^n`,
    • the **rest** at `c ∈ cOther`.

  Solving for `iteratedDeriv n gram u` and substituting the chain-rule
  identity `θ′(gram u) · deriv gram u = π` gives the form used in §2.4–§2.6.
-/

/-- Pointwise solved form of the Faà di Bruno equation for `iteratedDeriv n gram`.

    Eliminating `θ′(gram u)` via the chain rule and isolating
    `iteratedDeriv n gram u`. -/
private lemma iteratedDeriv_n_gram_solved (n : ℕ) (hn : 3 ≤ n) (u : ℝ)
    (hu : gramThreshold < u) (hg : 0 < gram u) (hg' : 0 < deriv gram u) :
    iteratedDeriv n gram u =
      -(deriv gram u / Real.pi)
        * (iteratedDeriv n theta (gram u) * (deriv gram u) ^ n
           + ∑ c ∈ cOther n (by omega),
               iteratedDeriv c.length theta (gram u)
                 * ∏ j, iteratedDeriv (c.partSize j) gram u) := by
  -- Shared positivity witness so `cTarget n hpos` reduces identically.
  have hpos : 0 < n := by omega
  set f : OrderedFinpartition n → ℝ := fun c =>
    iteratedDeriv c.length theta (gram u)
      * ∏ j, iteratedDeriv (c.partSize j) gram u with hf_def
  -- (1) Faà di Bruno: 0 = ∑ c, f c.
  have h_fb : (0 : ℝ) = ∑ c, f c := faadi_bruno_gram n (by omega) u hu hg
  -- (2) Membership facts for the sum splitting.
  have h_target_mem : cTarget n hpos ∈
      (Finset.univ : Finset (OrderedFinpartition n)) := Finset.mem_univ _
  have h_ne_atomic : cTarget n hpos ≠ OrderedFinpartition.atomic n :=
    cTarget_ne_atomic n (by omega)
  have h_atomic_in_erase :
      OrderedFinpartition.atomic n ∈
        (Finset.univ : Finset (OrderedFinpartition n)).erase (cTarget n hpos) := by
    rw [Finset.mem_erase]
    exact ⟨h_ne_atomic.symm, Finset.mem_univ _⟩
  -- (3) Sum decompositions.
  have h_decomp1 : f (cTarget n hpos) +
      ∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase (cTarget n hpos), f c
      = ∑ c, f c :=
    Finset.add_sum_erase _ f h_target_mem
  have h_decomp2 : f (OrderedFinpartition.atomic n) +
      ∑ c ∈ ((Finset.univ : Finset (OrderedFinpartition n)).erase
              (cTarget n hpos)).erase (OrderedFinpartition.atomic n), f c
      = ∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase (cTarget n hpos), f c :=
    Finset.add_sum_erase _ f h_atomic_in_erase
  -- (3a) The "rest" sum (= cOther by definition).
  have h_decomp2' : f (OrderedFinpartition.atomic n) +
      ∑ c ∈ cOther n hpos, f c =
      ∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase (cTarget n hpos), f c :=
    h_decomp2
  -- (4) `f cTarget` evaluates to `θ′(gram u) * iteratedDeriv n gram u`.
  have h_target_val : f (cTarget n hpos)
      = iteratedDeriv 1 theta (gram u) * iteratedDeriv n gram u := by
    change iteratedDeriv 1 theta (gram u) *
           ∏ _j : Fin 1, iteratedDeriv n gram u =
           iteratedDeriv 1 theta (gram u) * iteratedDeriv n gram u
    rw [Fin.prod_univ_one]
  -- (5) `f atomic` evaluates to `θ^(n)(gram u) * (deriv gram u)^n`.
  have h_atomic_val : f (OrderedFinpartition.atomic n)
      = iteratedDeriv n theta (gram u) * (deriv gram u) ^ n := by
    change iteratedDeriv n theta (gram u) *
           ∏ _j : Fin n, iteratedDeriv 1 gram u =
           iteratedDeriv n theta (gram u) * (deriv gram u) ^ n
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedDeriv_one]
  -- (6) Combine the decompositions to get the key algebraic identity:
  --     0 = f cTarget + (f atomic + ∑ cOther, f c)
  have h_key : (0 : ℝ) = f (cTarget n hpos) +
      (f (OrderedFinpartition.atomic n) + ∑ c ∈ cOther n hpos, f c) := by
    linarith [h_fb, h_decomp1, h_decomp2']
  -- (7) Substitute the values for f cTarget and f atomic.
  rw [h_target_val, h_atomic_val, iteratedDeriv_one] at h_key
  -- h_key : 0 = θ'(gram u) * ID n + (θ^n(gram u) * (deriv gram u)^n + ∑)
  -- (8) Apply the chain-rule identity θ′(gram u) · deriv gram u = π.
  have h_chain := deriv_theta_gram_mul_deriv_gram u hu hg
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h_gd_ne : deriv gram u ≠ 0 := ne_of_gt hg'
  have h_θ' : deriv theta (gram u) = Real.pi / deriv gram u := by
    field_simp
    linarith
  rw [h_θ'] at h_key
  -- (9) Solve for iteratedDeriv n gram u algebraically.
  have h_solve : iteratedDeriv n gram u = (deriv gram u / Real.pi) *
      ((Real.pi / deriv gram u) * iteratedDeriv n gram u) := by
    field_simp
  rw [h_solve]
  have h_iter_subst :
      (Real.pi / deriv gram u) * iteratedDeriv n gram u =
        -(iteratedDeriv n theta (gram u) * (deriv gram u) ^ n
           + ∑ c ∈ cOther n hpos, f c) := by
    linarith
  rw [h_iter_subst]
  ring

/-- Eventually-equality version of `iteratedDeriv_n_gram_solved`. -/
private lemma iteratedDeriv_n_gram_solved_eventually (n : ℕ) (hn : 3 ≤ n) :
    (fun u : ℝ => iteratedDeriv n gram u)
      =ᶠ[(𝓝∞ : Filter ℝ)]
    (fun u : ℝ =>
      -(deriv gram u / Real.pi)
        * (iteratedDeriv n theta (gram u) * (deriv gram u) ^ n
           + ∑ c ∈ cOther n (by omega),
               iteratedDeriv c.length theta (gram u)
                 * ∏ j, iteratedDeriv (c.partSize j) gram u)) := by
  filter_upwards [Filter.eventually_gt_atTop gramThreshold,
                  eventually_gram_pos, eventually_deriv_gram_pos]
    with u hu hg hg'
  exact iteratedDeriv_n_gram_solved n hn u hu hg hg'

/-!
  ## §2.4  Atomic-term asymptotic expansion

  Generalises §1.12 + §1.13 + §1.14 to all `n ≥ 2`.  The atomic
  contribution is

      −(1/π) · θ^(n)(gram u) · (deriv gram u)^(n+1)

  and we show it equals `gramLeading n u · (1 + 2 · ll/l) + o(...)`.

  Key trick: factor

      (gram u)^(1-n) · (deriv gram u)^(n+1)
        = [(gramL u)⁻¹ · (gramLDeriv u)^3] · [(gram u)^(2-n) · (deriv gram u)^(n-2)] · …

  so we can recycle `prod_inv_cube_expansion_aux` (the existing `n = 2`
  building block).  The "extra factor" `((1+δ')/(1+δ))^(n-2)` is
  `1 + o(ε)` by a simple `(1+η)^k - 1 = o(ε)` helper.
-/

/-- `(1 + η u)^k - 1 = o(ε)` when `η = o(ε)` and `ε → 0`.  Induction on `k`. -/
private lemma pow_one_plus_isLittleO_aux {α : Type*} {l : Filter α} (k : ℕ)
    {η ε : α → ℝ}
    (hη : η =o[l] ε)
    (hε : Tendsto ε l (𝓝 0)) :
    (fun u => (1 + η u) ^ k - 1) =o[l] ε := by
  -- η → 0 (from η = O(ε) and ε → 0).
  have h_η_tendsto : Tendsto η l (𝓝 0) := hη.isBigO.trans_tendsto hε
  induction k with
  | zero =>
    simp only [pow_zero, sub_self]
    exact Asymptotics.isLittleO_zero _ _
  | succ k ih =>
    -- (1+η)^(k+1) - 1 = (1+η)*((1+η)^k - 1) + η.
    have h_1η_tendsto : Tendsto (fun u => 1 + η u) l (𝓝 1) := by
      have := h_η_tendsto.const_add 1
      simpa using this
    have h_1η_O : (fun u => 1 + η u) =O[l] (fun _ => (1 : ℝ)) :=
      h_1η_tendsto.isBigO_one ℝ
    have h_prod : (fun u => (1 + η u) * ((1 + η u) ^ k - 1)) =o[l] ε := by
      have h := h_1η_O.mul_isLittleO ih
      refine h.congr_right ?_
      intro u; ring
    have h_sum : (fun u => (1 + η u) * ((1 + η u) ^ k - 1) + η u) =o[l] ε :=
      h_prod.add hη
    refine h_sum.congr_left ?_
    intro u
    ring

/-- **Generalised cubic-over-linear asymptotic.**  Generalises
    `prod_inv_cube_expansion_aux` from `(1+δ)⁻¹ · (1+δ')^3` to
    `((1+δ)^(m+1))⁻¹ · (1+δ')^(m+3)` for arbitrary `m : ℕ`.

    Indexed by `m` so all exponents are explicit additions (no
    natural-number subtraction).  Specialises to
    `prod_inv_cube_expansion_aux` at `m = 0`.

    Proof: factor
        ((1+δ)^(m+1))⁻¹ · (1+δ')^(m+3)
          = [(1+δ)⁻¹ · (1+δ')^3] · ((1+δ')/(1+δ))^m
          = A · B,
    where `A − (1 + 2ε) = o(ε)` by `prod_inv_cube_expansion_aux` and
    `B − 1 = o(ε)` by `pow_one_plus_isLittleO_aux` applied to
    `η := (δ' − δ)/(1+δ) = o(ε)`.  Combine via
    `A · B − (1+2ε) = (A − (1+2ε)) · B + (1+2ε) · (B − 1)`. -/
private lemma prod_inv_pow_expansion_aux
    {α : Type*} {l : Filter α} {δ δ' ε : α → ℝ} (m : ℕ)
    (hδ : (fun u => δ u - ε u) =o[l] ε)
    (hδ' : (fun u => δ' u - ε u) =o[l] ε)
    (hε : Tendsto ε l (𝓝 0)) :
    (fun u => ((1 + δ u) ^ (m + 1))⁻¹ * (1 + δ' u) ^ (m + 3)
      - (1 + 2 * ε u)) =o[l] ε := by
  -- (1) δ, δ' = O(ε), → 0, → (1 + δ), (1 + δ') → 1.
  have hδ_O : (fun u => δ u) =O[l] ε := by
    have h := hδ.isBigO.add (Asymptotics.isBigO_refl ε l)
    refine h.congr_left ?_; intro u; ring
  have hδ'_O : (fun u => δ' u) =O[l] ε := by
    have h := hδ'.isBigO.add (Asymptotics.isBigO_refl ε l)
    refine h.congr_left ?_; intro u; ring
  have hδ_zero : Tendsto δ l (𝓝 0) := hδ_O.trans_tendsto hε
  have hδ'_zero : Tendsto δ' l (𝓝 0) := hδ'_O.trans_tendsto hε
  have h1δ_tend : Tendsto (fun u => 1 + δ u) l (𝓝 1) := by
    have := hδ_zero.const_add 1; simpa using this
  have h1δ'_tend : Tendsto (fun u => 1 + δ' u) l (𝓝 1) := by
    have := hδ'_zero.const_add 1; simpa using this
  have h1δ_ne : ∀ᶠ u in l, (1 + δ u) ≠ 0 :=
    h1δ_tend.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  -- (2) η := (δ' - δ)/(1 + δ).  Show η = o(ε).
  have hδ'_sub_δ : (fun u => δ' u - δ u) =o[l] ε := by
    have h := hδ'.sub hδ
    refine h.congr_left ?_; intro u; ring
  have h1δ_inv_tend : Tendsto (fun u => (1 + δ u)⁻¹) l (𝓝 1) := by
    have := h1δ_tend.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using this
  have h1δ_inv_O : (fun u => (1 + δ u)⁻¹) =O[l] (fun _ : α => (1 : ℝ)) :=
    h1δ_inv_tend.isBigO_one ℝ
  have hη : (fun u => (δ' u - δ u) * (1 + δ u)⁻¹) =o[l] ε := by
    have h := hδ'_sub_δ.mul_isBigO h1δ_inv_O
    refine h.congr_right ?_; intro u; ring
  -- (3) B − 1 = ((1+δ')/(1+δ))^m − 1 = o(ε).
  have h_quot_eq : (fun u => (1 + δ' u) / (1 + δ u) - 1)
      =ᶠ[l] (fun u => (δ' u - δ u) * (1 + δ u)⁻¹) := by
    filter_upwards [h1δ_ne] with u hne
    field_simp
    ring
  have h_quot_o : (fun u => (1 + δ' u) / (1 + δ u) - 1) =o[l] ε :=
    hη.congr' h_quot_eq.symm Filter.EventuallyEq.rfl
  have h_B_sub_one : (fun u => ((1 + δ' u) / (1 + δ u)) ^ m - 1) =o[l] ε := by
    have h := pow_one_plus_isLittleO_aux m h_quot_o hε
    refine h.congr_left ?_
    intro u
    have : (1 + ((1 + δ' u) / (1 + δ u) - 1)) = (1 + δ' u) / (1 + δ u) := by ring
    rw [this]
  -- (4) A − (1 + 2ε) = o(ε) — the n = 2 building block.
  have h_A_sub : (fun u => (1 + δ u)⁻¹ * (1 + δ' u) ^ 3 - (1 + 2 * ε u)) =o[l] ε :=
    prod_inv_cube_expansion_aux hδ hδ' hε
  -- (5) B = O(1) and (1 + 2ε) = O(1).
  have h_B_tend : Tendsto (fun u => ((1 + δ' u) / (1 + δ u)) ^ m) l (𝓝 1) := by
    have h_div : Tendsto (fun u => (1 + δ' u) / (1 + δ u)) l (𝓝 (1 / 1)) :=
      h1δ'_tend.div h1δ_tend (by norm_num : (1 : ℝ) ≠ 0)
    have := h_div.pow m
    simpa using this
  have h_B_O : (fun u => ((1 + δ' u) / (1 + δ u)) ^ m) =O[l] (fun _ : α => (1 : ℝ)) :=
    h_B_tend.isBigO_one ℝ
  have h_1plus2ε_tend : Tendsto (fun u => 1 + 2 * ε u) l (𝓝 1) := by
    have := (hε.const_mul 2).const_add 1; simpa using this
  have h_1plus2ε_O : (fun u => 1 + 2 * ε u) =O[l] (fun _ : α => (1 : ℝ)) :=
    h_1plus2ε_tend.isBigO_one ℝ
  -- (6) term1 := (A − (1 + 2ε)) · B = o(ε) · O(1) = o(ε).
  have h_term1 :
      (fun u => ((1 + δ u)⁻¹ * (1 + δ' u) ^ 3 - (1 + 2 * ε u))
                * ((1 + δ' u) / (1 + δ u)) ^ m) =o[l] ε := by
    have h := h_A_sub.mul_isBigO h_B_O
    refine h.congr_right ?_; intro u; ring
  -- (7) term2 := (1 + 2ε) · (B − 1) = O(1) · o(ε) = o(ε).
  have h_term2 :
      (fun u => (1 + 2 * ε u) * (((1 + δ' u) / (1 + δ u)) ^ m - 1)) =o[l] ε := by
    have h := h_1plus2ε_O.mul_isLittleO h_B_sub_one
    refine h.congr_right ?_; intro u; ring
  -- (8) Sum is o(ε).
  have h_sum := h_term1.add h_term2
  -- (9) Algebraic identity (eventually, using 1 + δ ≠ 0).
  refine h_sum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [h1δ_ne] with u hne
  have h_pow_ne : (1 + δ u) ^ m ≠ 0 := pow_ne_zero _ hne
  change ((1 + δ u)⁻¹ * (1 + δ' u) ^ 3 - (1 + 2 * ε u))
          * ((1 + δ' u) / (1 + δ u)) ^ m
        + (1 + 2 * ε u) * (((1 + δ' u) / (1 + δ u)) ^ m - 1)
        = ((1 + δ u) ^ (m + 1))⁻¹ * (1 + δ' u) ^ (m + 3) - (1 + 2 * ε u)
  -- Expand the division power and the (m+1), (m+3) powers.
  rw [div_pow, pow_succ (1 + δ u) m,
      show m + 3 = m + 1 + 2 from by ring, pow_add, pow_succ (1 + δ' u) m]
  field_simp
  ring

/-- **Algebraic factorisation** of `gramLeading n u` in terms of `gramL`
    and `gramLDeriv`. -/
private lemma gramLeading_factorization (n : ℕ) (hn : 2 ≤ n) {u : ℝ}
    (hu : u ≠ 0) (hlog : Real.log u ≠ 0) :
    (-(1 / Real.pi)) * ((-1 : ℝ) ^ n * (n - 2).factorial / 2)
      * ((gramL u) ^ (n - 1))⁻¹ * (gramLDeriv u) ^ (n + 1)
      = gramLeading n u := by
  -- Eliminate natural-number subtractions by writing `n = m + 2`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  unfold gramL gramLDeriv gramLeading
  rw [h1, h2]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  -- Expand `(a/b)^k` and `(a·b)^k` so `field_simp` can clear denominators.
  simp only [div_pow, mul_pow]
  field_simp
  ring

/-- **Generalised `(gram u)`-power asymptotic.**  For `n ≥ 2`,

        ((gram u)⁻¹)^(n+1) = o(((gramL u)⁻¹)^(n-1) · log log u / log u).

    Specialises to `inv_gram_cube_isLittleO_inv_gramL_mul_frac` at `n = 2`
    (where `(n+1) = 3` and `(n-1) = 1`).

    Proof: factor `((gram u)⁻¹)^(n+1) = ((gram u)⁻¹)^(n-1) · ((gram u)⁻¹)^2`,
    use `gram⁻¹ ~ gramL⁻¹` (so `((gram u)⁻¹)^(n-1) = O(((gramL u)⁻¹)^(n-1))`)
    and `((gram u)⁻¹)^2 = o(ε)` from `inv_gram_sq_isLittleO_frac`. -/
private lemma inv_gram_pow_isLittleO_inv_gramL_pow_mul_frac (n : ℕ) (hn : 2 ≤ n) :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gram u)⁻¹) ^ (n + 1))
      (fun u : ℝ =>
        ((gramL u)⁻¹) ^ (n - 1) * (Real.log (Real.log u) / Real.log u)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  rw [h1]
  -- ((gram u)⁻¹)^(m+1) =O[𝓝∞] ((gramL u)⁻¹)^(m+1).
  have h_factor : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gram u)⁻¹) ^ (m + 1))
      (fun u : ℝ => ((gramL u)⁻¹) ^ (m + 1)) :=
    (gram_inv_isEquivalent_gramL_inv.pow (m + 1)).isBigO
  -- ((gram u)⁻¹)^2 = o(ε).
  have h_sq := inv_gram_sq_isLittleO_frac
  -- Product is o(((gramL u)⁻¹)^(m+1) · ε).
  have h_prod := h_factor.mul_isLittleO h_sq
  refine h_prod.congr_left ?_
  intro u
  show ((gram u)⁻¹) ^ (m + 1) * ((gram u)⁻¹) ^ 2
      = ((gram u)⁻¹) ^ (m + 2 + 1)
  rw [← pow_add]

/-- **Refined θ^(n)(gram u) asymptotic.**  For `n ≥ 2`,

        iteratedDeriv n theta (gram u)
          − (-1)^n · (n − 2)! · (1/2) · ((gram u)⁻¹)^(n − 1)
          = o(((gramL u)⁻¹)^(n − 1) · log log u / log u)

    as `u → +∞`.  Specialises to
    `iteratedDeriv_two_theta_at_gram_isLittleO_refined` at `n = 2`.

    Proof: take the raw `IsO` from `iteratedDeriv_theta_at_gram_isO`, convert
    the rpow exponents `(1 − n)` and `(−n − 1)` into `Nat`-power inverses
    `((gram u)⁻¹)^(n − 1)` and `((gram u)⁻¹)^(n + 1)` using `Real.rpow_neg`
    and `Real.rpow_natCast` (valid because `gram u > 0` eventually), then
    compose with `inv_gram_pow_isLittleO_inv_gramL_pow_mul_frac`. -/
private lemma iteratedDeriv_n_theta_at_gram_isLittleO_refined (n : ℕ) (hn : 2 ≤ n) :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => iteratedDeriv n theta (gram u)
        - ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) * (1 / 2)
           * ((gram u)⁻¹) ^ (n - 1)))
      (fun u : ℝ =>
        ((gramL u)⁻¹) ^ (n - 1) * (Real.log (Real.log u) / Real.log u)) := by
  -- Raw IsO statement from Corollary 2 transport.
  have h_isO := iteratedDeriv_theta_at_gram_isO n hn
  -- Eventually rewrite LHS rpow `(gram u)^(1 − (n:ℝ))` as `((gram u)⁻¹)^(n − 1)`.
  have h_pos := eventually_gram_pos
  have h_cast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h := Nat.cast_sub (R := ℝ) (show (1 : ℕ) ≤ n from by omega)
    simpa using h
  have h_lhs :
      (fun u : ℝ => iteratedDeriv n theta (gram u)
        - ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) * (1 / 2)
           * (gram u) ^ (1 - (n : ℝ))))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ => iteratedDeriv n theta (gram u)
        - ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) * (1 / 2)
           * ((gram u)⁻¹) ^ (n - 1))) := by
    filter_upwards [h_pos] with u hgu
    have h_exp : (1 - (n : ℝ)) = -((n - 1 : ℕ) : ℝ) := by rw [h_cast_sub]; ring
    rw [h_exp, Real.rpow_neg hgu.le, Real.rpow_natCast, inv_pow]
  -- Eventually rewrite RHS rpow `(gram u)^(-(n:ℝ) - 1)` as `((gram u)⁻¹)^(n + 1)`.
  have h_rhs :
      (fun u : ℝ => (gram u) ^ (-(n : ℝ) - 1))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ => ((gram u)⁻¹) ^ (n + 1)) := by
    filter_upwards [h_pos] with u hgu
    have h_exp : (-(n : ℝ) - 1) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h_exp, Real.rpow_neg hgu.le, Real.rpow_natCast, inv_pow]
  -- Apply both rewrites to the IsO.
  have h_isO_clean :
      Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
        (fun u : ℝ => iteratedDeriv n theta (gram u)
          - ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) * (1 / 2)
             * ((gram u)⁻¹) ^ (n - 1)))
        (fun u : ℝ => ((gram u)⁻¹) ^ (n + 1)) :=
    (h_isO.congr' h_lhs h_rhs : _)
  -- Compose with the o-bound for ((gram u)⁻¹)^(n+1).
  exact h_isO_clean.trans_isLittleO (inv_gram_pow_isLittleO_inv_gramL_pow_mul_frac n hn)

/-- **Generalised cubic-over-linear expansion** for `(gram u)`-powers.

    For `n ≥ 2`,

        ((gram u)⁻¹)^(n-1) · (deriv gram u)^(n+1)
          = ((gramL u)⁻¹)^(n-1) · (gramLDeriv u)^(n+1)
              · (1 + 2 · (log log u / log u))
            + o(((gramL u)⁻¹)^(n-1) · (gramLDeriv u)^(n+1) · (log log u / log u)).

    Specialises to `inv_gram_mul_deriv_gram_cube_expansion` at `n = 2`.

    Specialisation of `prod_inv_pow_expansion_aux` to
        δ  := gram u / gramL u - 1,
        δ' := deriv gram u / gramLDeriv u - 1,
        ε  := log log u / log u. -/
private lemma inv_gram_pow_mul_deriv_gram_pow_expansion (n : ℕ) (hn : 2 ≤ n) :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gram u)⁻¹) ^ (n - 1) * (deriv gram u) ^ (n + 1)
        - ((gramL u)⁻¹) ^ (n - 1) * (gramLDeriv u) ^ (n + 1)
            * (1 + 2 * (Real.log (Real.log u) / Real.log u)))
      (fun u : ℝ => ((gramL u)⁻¹) ^ (n - 1) * (gramLDeriv u) ^ (n + 1)
        * (Real.log (Real.log u) / Real.log u)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h_n_sub_one : m + 2 - 1 = m + 1 := by omega
  have h_n_plus_one : m + 2 + 1 = m + 3 := by omega
  rw [h_n_sub_one, h_n_plus_one]
  -- Set δ, δ', ε as in `inv_gram_mul_deriv_gram_cube_expansion`.
  set δ : ℝ → ℝ := fun u => gram u / gramL u - 1 with hδ_def
  set δ' : ℝ → ℝ := fun u => deriv gram u / gramLDeriv u - 1 with hδ'_def
  set ε : ℝ → ℝ := fun u => Real.log (Real.log u) / Real.log u with hε_def
  have hδ_resid : (fun u => δ u - ε u) =o[(𝓝∞ : Filter ℝ)] ε := by
    have := gram_quot_residual
    refine this.congr_left ?_; intro u
    change gram u / gramL u - 1 - Real.log (Real.log u) / Real.log u
        = (gram u / gramL u - 1) - Real.log (Real.log u) / Real.log u
    ring
  have hδ'_resid : (fun u => δ' u - ε u) =o[(𝓝∞ : Filter ℝ)] ε := by
    have := deriv_gram_quot_residual
    refine this.congr_left ?_; intro u
    change deriv gram u / gramLDeriv u - 1 - Real.log (Real.log u) / Real.log u
        = (deriv gram u / gramLDeriv u - 1) - Real.log (Real.log u) / Real.log u
    ring
  have hε_tendsto : Tendsto ε (𝓝∞ : Filter ℝ) (𝓝 0) := frac_tendsto_zero
  -- Apply the abstract lemma.
  have h_abs := prod_inv_pow_expansion_aux m hδ_resid hδ'_resid hε_tendsto
  -- Multiply by F := ((gramL u)⁻¹)^(m+1) * (gramLDeriv u)^(m+3) (=O of itself).
  have h_F_O := Asymptotics.isBigO_refl
    (fun u : ℝ => ((gramL u)⁻¹) ^ (m + 1) * (gramLDeriv u) ^ (m + 3)) (𝓝∞ : Filter ℝ)
  have h_mul := h_F_O.mul_isLittleO h_abs
  -- Eventually `gramL u ≠ 0`, `gramLDeriv u ≠ 0`, `gram u > 0`.
  have hL_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramL u ≠ 0 := by
    have hL_tend : Tendsto gramL (𝓝∞ : Filter ℝ) 𝓝∞ :=
      linear_div_log_tendsto_atTop.congr (fun u => by simp [gramL])
    filter_upwards [hL_tend.eventually_gt_atTop (0 : ℝ)] with u hu
    exact ne_of_gt hu
  have hL'_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramLDeriv u ≠ 0 := by
    filter_upwards [log_pos_atTop] with u hu
    unfold gramLDeriv
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hu
    positivity
  -- Rewrite the LHS to match the goal.
  refine h_mul.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hL_ne, hL'_ne, eventually_gram_pos] with u hLu hL'u hgu
  have hg_ne : gram u ≠ 0 := ne_of_gt hgu
  have hδ_val : 1 + δ u = gram u / gramL u := by
    change 1 + (gram u / gramL u - 1) = gram u / gramL u; ring
  have hδ'_val : 1 + δ' u = deriv gram u / gramLDeriv u := by
    change 1 + (deriv gram u / gramLDeriv u - 1) = deriv gram u / gramLDeriv u; ring
  change ((gramL u)⁻¹) ^ (m + 1) * (gramLDeriv u) ^ (m + 3)
        * (((1 + δ u) ^ (m + 1))⁻¹ * (1 + δ' u) ^ (m + 3) - (1 + 2 * ε u))
      = ((gram u)⁻¹) ^ (m + 1) * (deriv gram u) ^ (m + 3)
        - ((gramL u)⁻¹) ^ (m + 1) * (gramLDeriv u) ^ (m + 3) * (1 + 2 * ε u)
  rw [hδ_val, hδ'_val]
  -- Pull inverses outside the powers and expand the quotient powers.
  simp only [inv_pow, div_pow, inv_div]
  have h_gL_pow : (gramL u) ^ (m + 1) ≠ 0 := pow_ne_zero _ hLu
  have h_gL'_pow : (gramLDeriv u) ^ (m + 3) ≠ 0 := pow_ne_zero _ hL'u
  have h_g_pow : (gram u) ^ (m + 1) ≠ 0 := pow_ne_zero _ hg_ne
  field_simp

/-!
  ## §2.4 closure: Atomic-term asymptotic

  Combine the refined θ^(n)(gram u) bound with the generalised
  cubic-over-linear expansion to obtain the **atomic-term asymptotic**
  for the Faà di Bruno expansion of `iteratedDeriv n gram u`.

      −(1/π) · θ^(n)(gram u) · (deriv gram u)^(n+1)
        − gramLeading n u
        − 2 · gramLeading n u · (log log u / log u)
      = o(gramLeading n u · (log log u / log u)).

  This is the n-version of `theorem3_two` modulo the structural
  identity `iteratedDeriv 2 gram u = −(1/π) · θ''(gram u) · (deriv gram u)^3`.
-/

/-- **Atomic-term asymptotic expansion** for the Faà di Bruno expansion
    of `iteratedDeriv n gram u` (for `n ≥ 2`).

    Combines `iteratedDeriv_n_theta_at_gram_isLittleO_refined`,
    `inv_gram_pow_mul_deriv_gram_pow_expansion`, and
    `gramLeading_factorization`. -/
private lemma theorem3_atomic_term (n : ℕ) (hn : 2 ≤ n) :
    Iso
      (fun u : ℝ =>
        -(1 / Real.pi) * iteratedDeriv n theta (gram u) * (deriv gram u) ^ (n + 1)
        - gramLeading n u
        - 2 * gramLeading n u * Real.log (Real.log u) / Real.log u)
      (fun u : ℝ => gramLeading n u * Real.log (Real.log u) / Real.log u)
      𝓝∞ := by
  -- Shorthand `F := ((gramL u)⁻¹)^(n-1) · (gramLDeriv u)^(n+1)`.
  set F : ℝ → ℝ := fun u => ((gramL u)⁻¹) ^ (n - 1) * (gramLDeriv u) ^ (n + 1) with hF_def
  -- Constant `c := −(1/π) · (−1)^n · (n − 2)! / 2`.
  set c : ℝ := -(1 / Real.pi) * ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) / 2)
    with hc_def
  -- (i) Residual r_θ · (deriv gram u)^(n+1) = o(F · ε).
  have h_rθ_mul :
      (fun u : ℝ =>
        (iteratedDeriv n theta (gram u)
          - (-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) * (1 / 2)
            * ((gram u)⁻¹) ^ (n - 1))
          * (deriv gram u) ^ (n + 1))
        =o[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u)) := by
    have h_rθ := iteratedDeriv_n_theta_at_gram_isLittleO_refined n hn
    have h_deriv_O :
        (fun u : ℝ => (deriv gram u) ^ (n + 1)) =O[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => (gramLDeriv u) ^ (n + 1)) :=
      (deriv_gram_isEquivalent_gramLDeriv.pow (n + 1)).isBigO
    have h := h_rθ.mul_isBigO h_deriv_O
    refine h.congr_right ?_
    intro u
    change ((gramL u)⁻¹) ^ (n - 1) * (Real.log (Real.log u) / Real.log u)
            * (gramLDeriv u) ^ (n + 1)
        = ((gramL u)⁻¹) ^ (n - 1) * (gramLDeriv u) ^ (n + 1)
            * (Real.log (Real.log u) / Real.log u)
    ring
  -- (ii) Cubic-over-linear expansion: s := ... = o(F · ε).
  have h_s := inv_gram_pow_mul_deriv_gram_pow_expansion n hn
  -- (iii) Constant multiples.
  have h_term1 :
      (fun u : ℝ =>
        -(1 / Real.pi) * ((iteratedDeriv n theta (gram u)
          - (-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) * (1 / 2)
            * ((gram u)⁻¹) ^ (n - 1))
          * (deriv gram u) ^ (n + 1)))
        =o[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u)) :=
    h_rθ_mul.const_mul_left _
  have h_term2 :
      (fun u : ℝ => c * (((gram u)⁻¹) ^ (n - 1) * (deriv gram u) ^ (n + 1)
          - F u * (1 + 2 * (Real.log (Real.log u) / Real.log u))))
        =o[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u)) :=
    h_s.const_mul_left _
  have h_sum := h_term1.add h_term2
  -- (iv) Eventual nonzeros.
  have hL_ne : ∀ᶠ u in (𝓝∞ : Filter ℝ), gramL u ≠ 0 := by
    have hL_tend : Tendsto gramL (𝓝∞ : Filter ℝ) 𝓝∞ :=
      linear_div_log_tendsto_atTop.congr (fun u => by simp [gramL])
    filter_upwards [hL_tend.eventually_gt_atTop (0 : ℝ)] with u hu
    exact ne_of_gt hu
  -- (v) Algebraic identity: the sum equals the target residual (eventually).
  have h_lhs_eq :
      (fun u : ℝ =>
        -(1 / Real.pi) * ((iteratedDeriv n theta (gram u)
          - (-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) * (1 / 2)
            * ((gram u)⁻¹) ^ (n - 1))
          * (deriv gram u) ^ (n + 1))
        + c * (((gram u)⁻¹) ^ (n - 1) * (deriv gram u) ^ (n + 1)
          - F u * (1 + 2 * (Real.log (Real.log u) / Real.log u))))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ =>
        -(1 / Real.pi) * iteratedDeriv n theta (gram u) * (deriv gram u) ^ (n + 1)
        - gramLeading n u
        - 2 * gramLeading n u * Real.log (Real.log u) / Real.log u) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), log_pos_atTop, hL_ne]
      with u hu hlog hLu
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
    have h_inv_pow : ((gramL u) ^ (n - 1))⁻¹ = ((gramL u)⁻¹) ^ (n - 1) :=
      (inv_pow _ _).symm
    have h_factor := gramLeading_factorization n hn hu_ne hlog_ne
    -- gramLeading n u = c · F u (using inv_pow to convert).
    have h_gL_eq : gramLeading n u = c * F u := by
      have h1 : c * F u = -(1 / Real.pi)
            * ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) / 2)
            * (((gramL u) ^ (n - 1))⁻¹ * (gramLDeriv u) ^ (n + 1)) := by
        rw [hc_def, hF_def, h_inv_pow]
      rw [h1]
      have h2 : -(1 / Real.pi)
            * ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) / 2)
            * (((gramL u) ^ (n - 1))⁻¹ * (gramLDeriv u) ^ (n + 1))
          = -(1 / Real.pi)
            * ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) / 2)
            * ((gramL u) ^ (n - 1))⁻¹ * (gramLDeriv u) ^ (n + 1) := by ring
      rw [h2, ← h_factor]
    rw [h_gL_eq]
    ring
  have h_E_isO_F :
      (fun u : ℝ =>
        -(1 / Real.pi) * iteratedDeriv n theta (gram u) * (deriv gram u) ^ (n + 1)
        - gramLeading n u
        - 2 * gramLeading n u * Real.log (Real.log u) / Real.log u)
        =o[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u)) :=
    h_sum.congr' h_lhs_eq Filter.EventuallyEq.rfl
  -- (vi) Convert RHS bound from F · ε to gramLeading n · ε.  Since
  -- `gramLeading n u = c · F u` eventually and `c ≠ 0`, we have
  -- `F u · ε = (1/c) · (gramLeading n u · ε)`.
  have hc_ne : c ≠ 0 := by
    rw [hc_def]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h_neg_one_pow : ((-1 : ℝ) ^ n) ≠ 0 :=
      pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)
    have h_fact_ne : ((Nat.factorial (n - 2) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos (n - 2)).ne'
    intro h
    have h_lhs_ne : (-(1 / Real.pi)) ≠ 0 := by
      have : (1 / Real.pi) ≠ 0 := one_div_ne_zero hπ
      exact neg_ne_zero.mpr this
    have h_rhs_ne : ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) / 2) ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero h_neg_one_pow h_fact_ne
      · norm_num
    exact (mul_ne_zero h_lhs_ne h_rhs_ne) h
  have h_RHS_eq :
      (fun u : ℝ => F u * (Real.log (Real.log u) / Real.log u))
      =ᶠ[(𝓝∞ : Filter ℝ)]
      (fun u : ℝ => c⁻¹ * (gramLeading n u * Real.log (Real.log u) / Real.log u)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), log_pos_atTop, hL_ne]
      with u hu hlog hLu
    have hu_ne : u ≠ 0 := ne_of_gt hu
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
    have h_inv_pow : ((gramL u) ^ (n - 1))⁻¹ = ((gramL u)⁻¹) ^ (n - 1) :=
      (inv_pow _ _).symm
    have h_factor := gramLeading_factorization n hn hu_ne hlog_ne
    have h_gL_eq : gramLeading n u = c * F u := by
      have h1 : c * F u = -(1 / Real.pi)
            * ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) / 2)
            * (((gramL u) ^ (n - 1))⁻¹ * (gramLDeriv u) ^ (n + 1)) := by
        rw [hc_def, hF_def, h_inv_pow]
      rw [h1]
      have h2 : -(1 / Real.pi)
            * ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) / 2)
            * (((gramL u) ^ (n - 1))⁻¹ * (gramLDeriv u) ^ (n + 1))
          = -(1 / Real.pi)
            * ((-1 : ℝ) ^ n * ((Nat.factorial (n - 2) : ℕ) : ℝ) / 2)
            * ((gramL u) ^ (n - 1))⁻¹ * (gramLDeriv u) ^ (n + 1) := by ring
      rw [h2, ← h_factor]
    rw [h_gL_eq]
    field_simp
  have h_E_isO_RHS' :=
    h_E_isO_F.congr' Filter.EventuallyEq.rfl h_RHS_eq
  -- (vii) Strip the constant factor `c⁻¹`.
  have hc_inv_ne : c⁻¹ ≠ 0 := inv_ne_zero hc_ne
  exact (Asymptotics.isLittleO_const_mul_right_iff hc_inv_ne).mp h_E_isO_RHS'

/-!
  ## §2.5  Per-factor bigO bounds

  Explicit-polynomial upper bounds for each factor in the Faà di Bruno
  expansion of `θ ∘ gram`:
    • `iteratedDeriv 1 gram u   = O(1 / log u)`              — Korolev (eq. 9).
    • `iteratedDeriv k gram u   = O(1 / (u^{k-1} log² u))`   — `GramAsymp k`, `k ≥ 2`.
    • `θ^(ℓ)(gram u)            = O(log^{ℓ-1} u / u^{ℓ-1})` — Corollary 2 transported.

  These are the building blocks for the per-summand estimate in §2.5.3.
-/

/-- `((gramL u)⁻¹)^m =O[𝓝∞] (fun u => Real.log u^m / u^m)`.  Pointwise
    constant identity `((gramL u)⁻¹)^m = (1/(2π))^m · log^m u / u^m`. -/
private lemma inv_gramL_pow_isBigO_explicit (m : ℕ) :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gramL u)⁻¹) ^ m)
      (fun u : ℝ => Real.log u ^ m / u ^ m) := by
  have h := Asymptotics.isBigO_const_mul_self
    ((1 / (2 * Real.pi)) ^ m)
    (fun u : ℝ => Real.log u ^ m / u ^ m) (𝓝∞ : Filter ℝ)
  refine h.congr_left ?_
  intro u
  change (1 / (2 * Real.pi)) ^ m * (Real.log u ^ m / u ^ m) = ((gramL u)⁻¹) ^ m
  have h_lhs : (1 / (2 * Real.pi)) ^ m * (Real.log u ^ m / u ^ m)
             = Real.log u ^ m / ((2 * Real.pi) ^ m * u ^ m) := by
    rw [div_pow, one_pow, div_mul_div_comm, one_mul]
  have h_rhs : ((gramL u)⁻¹) ^ m
             = Real.log u ^ m / ((2 * Real.pi) ^ m * u ^ m) := by
    unfold gramL
    rw [inv_div, div_pow, mul_pow]
  rw [h_lhs, h_rhs]

/-- `θ^(ℓ)(gram u) =O[𝓝∞] ((gramL u)⁻¹)^(ℓ − 1)` for `ℓ ≥ 2`.

    Comes from the refined Corollary-2 transport
    `iteratedDeriv_n_theta_at_gram_isLittleO_refined` combined with
    `gram⁻¹ ~ gramL⁻¹` and the trivial bound
    `((gramL u)⁻¹)^(ℓ-1) · log log u / log u =o ((gramL u)⁻¹)^(ℓ-1)`. -/
private lemma theta_iter_at_gram_isBigO_inv_gramL_pow (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => iteratedDeriv ℓ theta (gram u))
      (fun u : ℝ => ((gramL u)⁻¹) ^ (ℓ - 1)) := by
  -- Refined residual: (θ^(ℓ)(gram u) − C · ((gram u)⁻¹)^(ℓ-1))
  --                    =o[𝓝∞] (((gramL u)⁻¹)^(ℓ-1) · ll/l).
  have h_refined := iteratedDeriv_n_theta_at_gram_isLittleO_refined ℓ hℓ
  -- ((gramL u)⁻¹)^(ℓ-1) · ll/l =o ((gramL u)⁻¹)^(ℓ-1) (since ll/l → 0).
  have h_ll_o_one := loglog_div_log_isLittleO_one
  have h_mul_o_self : Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gramL u)⁻¹) ^ (ℓ - 1) * (Real.log (Real.log u) / Real.log u))
      (fun u : ℝ => ((gramL u)⁻¹) ^ (ℓ - 1)) := by
    have h := (Asymptotics.isBigO_refl
      (fun u : ℝ => ((gramL u)⁻¹) ^ (ℓ - 1)) (𝓝∞ : Filter ℝ)).mul_isLittleO h_ll_o_one
    simpa using h
  -- Residual =O ((gramL u)⁻¹)^(ℓ-1).
  have h_residual_O : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => iteratedDeriv ℓ theta (gram u)
        - ((-1 : ℝ) ^ ℓ * ((Nat.factorial (ℓ - 2) : ℕ) : ℝ) * (1 / 2)
           * ((gram u)⁻¹) ^ (ℓ - 1)))
      (fun u : ℝ => ((gramL u)⁻¹) ^ (ℓ - 1)) :=
    (h_refined.trans_isBigO h_mul_o_self.isBigO).isBigO
  -- ((gram u)⁻¹)^(ℓ-1) =O ((gramL u)⁻¹)^(ℓ-1).
  have h_gram_to_gramL : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ((gram u)⁻¹) ^ (ℓ - 1))
      (fun u : ℝ => ((gramL u)⁻¹) ^ (ℓ - 1)) :=
    (gram_inv_isEquivalent_gramL_inv.pow (ℓ - 1)).isBigO
  -- Leading term =O target.
  have h_lead_O : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => (-1 : ℝ) ^ ℓ * ((Nat.factorial (ℓ - 2) : ℕ) : ℝ) * (1 / 2)
                    * ((gram u)⁻¹) ^ (ℓ - 1))
      (fun u : ℝ => ((gramL u)⁻¹) ^ (ℓ - 1)) :=
    (Asymptotics.isBigO_const_mul_self
      ((-1 : ℝ) ^ ℓ * ((Nat.factorial (ℓ - 2) : ℕ) : ℝ) * (1 / 2))
      (fun u : ℝ => ((gram u)⁻¹) ^ (ℓ - 1)) (𝓝∞ : Filter ℝ)).trans h_gram_to_gramL
  -- Sum: θ^(ℓ)(gram u) = (residual + lead) =O ((gramL u)⁻¹)^(ℓ-1).
  have h_total := h_residual_O.add h_lead_O
  refine h_total.congr_left ?_
  intro u
  ring

/-- `θ^(ℓ)(gram u) =O[𝓝∞] (fun u => Real.log u^(ℓ-1) / u^(ℓ-1))` for `ℓ ≥ 2`. -/
private lemma theta_iter_at_gram_isBigO_explicit (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => iteratedDeriv ℓ theta (gram u))
      (fun u : ℝ => Real.log u ^ (ℓ - 1) / u ^ (ℓ - 1)) :=
  (theta_iter_at_gram_isBigO_inv_gramL_pow ℓ hℓ).trans
    (inv_gramL_pow_isBigO_explicit (ℓ - 1))

/-- `gramLeading k =O[𝓝∞] (fun u => 1 / (u^(k-1) · log² u))`.  Strips the
    explicit constant `(−1)^(k+1) · 2π · (k − 2)!`. -/
private lemma gramLeading_isBigO_explicit (k : ℕ) :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ) (gramLeading k)
      (fun u : ℝ => 1 / (u ^ (k - 1) * Real.log u ^ 2)) := by
  have h := Asymptotics.isBigO_const_mul_self
    ((-1 : ℝ) ^ (k + 1) * (2 * Real.pi) * ((Nat.factorial (k - 2) : ℕ) : ℝ))
    (fun u : ℝ => 1 / (u ^ (k - 1) * Real.log u ^ 2)) (𝓝∞ : Filter ℝ)
  refine h.congr_left ?_
  intro u
  show (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) * ((Nat.factorial (k - 2) : ℕ) : ℝ)
       * (1 / (u ^ (k - 1) * Real.log u ^ 2)) = gramLeading k u
  unfold gramLeading
  ring

/-- `iteratedDeriv k gram =O[𝓝∞] (fun u => 1 / (u^(k-1) · log² u))` for
    `k ≥ 2`, given the inductive hypothesis `GramAsymp k`. -/
private lemma iteratedDeriv_isBigO_explicit (k : ℕ) (ih : GramAsymp k) :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (iteratedDeriv k gram)
      (fun u : ℝ => 1 / (u ^ (k - 1) * Real.log u ^ 2)) :=
  (iteratedDeriv_isBigO_gramLeading ih).trans (gramLeading_isBigO_explicit k)

/-- `iteratedDeriv 1 gram =O[𝓝∞] (fun u => 1 / Real.log u)`.  From Korolev
    (eq. 9), packaged via `iteratedDeriv 1 gram ~ gramLDeriv` and
    `gramLDeriv u = 2π · (1/log u)`. -/
private lemma iteratedDeriv_one_gram_isBigO_explicit :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (iteratedDeriv 1 gram)
      (fun u : ℝ => 1 / Real.log u) := by
  have h1 : Asymptotics.IsBigO (𝓝∞ : Filter ℝ) (iteratedDeriv 1 gram) gramLDeriv :=
    gram_deriv_isEquivalent_gramLDeriv.isBigO
  have h2 : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      gramLDeriv (fun u : ℝ => 1 / Real.log u) := by
    have h := Asymptotics.isBigO_const_mul_self
      (2 * Real.pi) (fun u : ℝ => 1 / Real.log u) (𝓝∞ : Filter ℝ)
    refine h.congr_left ?_
    intro u
    change 2 * Real.pi * (1 / Real.log u) = gramLDeriv u
    unfold gramLDeriv
    ring
  exact h1.trans h2

/-!
  ## §2.5.3a  Structural helpers

  Two structural lemmas about `OrderedFinpartition`:
    • `eq_atomic_of_partSize_all_one`: a finpartition with every part of size
      `1` is the `atomic` finpartition (an extensionality fact, mirror of the
      existing `eq_cTarget_of_length_one`).
    • `exists_partSize_ge_two_of_mem_cOther`: every `c ∈ cOther` has at least
      one part of size `≥ 2`.  This is the key witness used in §2.5.3 to pick
      the index `j₀` at which we apply the *tight* bound
      `iteratedDeriv (c.partSize j₀) gram = O(1/(u^{k-1} log² u))` while using
      the weaker `1/(u^{k-1} log u)` bound at the remaining indices.
-/

/-- A finpartition all of whose parts have size 1 equals `OrderedFinpartition.atomic n`.

    Combined with `partSize_pos`, this is the structural converse to
    `OrderedFinpartition.atomic_partSize : (atomic n).partSize j = 1`. -/
private lemma eq_atomic_of_partSize_all_one {n : ℕ}
    (c : OrderedFinpartition n) (h_all_one : ∀ j, c.partSize j = 1) :
    c = OrderedFinpartition.atomic n := by
  -- Length = n (from `sum_partSize_eq`).
  have h_sum := sum_partSize_eq c
  have h_const_one :
      (fun i : Fin c.length => c.partSize i) = (fun _ => 1) := funext h_all_one
  rw [h_const_one] at h_sum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
             smul_eq_mul, mul_one] at h_sum
  have h_len_eq_n : c.length = n := h_sum
  -- Destructure.
  rcases c with ⟨length, partSize, partSize_pos, emb, emb_strictMono,
                 parts_strictMono, disjoint, cover⟩
  simp only at h_len_eq_n h_all_one
  subst length
  have h_partSize : partSize = (fun _ : Fin n => 1) := funext h_all_one
  subst h_partSize
  -- Show `emb m = (fun _ => m)` (forced by strict-mono + cover ⇒ identity).
  have h_emb_zero_id : ∀ m, emb m ⟨0, Nat.zero_lt_one⟩ = m := by
    apply fin_strictMono_surj_eq_id
    · intro a b h_lt; exact parts_strictMono h_lt
    · intro x
      obtain ⟨m, r, hr⟩ := cover x
      refine ⟨m, ?_⟩
      change emb m ⟨0, Nat.zero_lt_one⟩ = x
      have hr_eq : r = ⟨0, Nat.zero_lt_one⟩ := Subsingleton.elim _ _
      rw [← hr_eq]; exact hr
  have h_emb : emb = fun (m : Fin n) (_ : Fin 1) => m := by
    funext m j
    have hj : j = ⟨0, Nat.zero_lt_one⟩ := Subsingleton.elim _ _
    rw [hj]; exact h_emb_zero_id m
  subst h_emb
  rfl

/-- For `c ∈ cOther n hn` (with `n ≥ 2`), some part has size `≥ 2`.

    Contrapositive: if all parts have size `1` then `c = atomic`, contradicting
    `c ∈ cOther` (which excludes the atomic partition). -/
private lemma exists_partSize_ge_two_of_mem_cOther {n : ℕ} (hn : 2 ≤ n)
    {c : OrderedFinpartition n} (hc : c ∈ cOther n (by omega : 0 < n)) :
    ∃ j : Fin c.length, 2 ≤ c.partSize j := by
  by_contra h
  push_neg at h
  -- All partSize = 1 (since partSize_pos and partSize < 2 ⟹ = 1).
  have h_all_one : ∀ j, c.partSize j = 1 := fun j =>
    Nat.le_antisymm (Nat.lt_succ_iff.mp (h j)) (c.partSize_pos j)
  -- Hence c = atomic n.
  have h_eq : c = OrderedFinpartition.atomic n :=
    eq_atomic_of_partSize_all_one c h_all_one
  -- But c ∈ cOther excludes atomic.
  have h_ne_atomic : c ≠ OrderedFinpartition.atomic n :=
    (Finset.mem_erase.mp hc).1
  exact h_ne_atomic h_eq

/-- For `c ∈ cOther n hn` (with `n ≥ 2`), `c.length ≥ 2`. -/
private lemma length_ge_two_of_mem_cOther {n : ℕ} (hn : 2 ≤ n)
    {c : OrderedFinpartition n} (hc : c ∈ cOther n (by omega : 0 < n)) :
    2 ≤ c.length := by
  have h_pos : 0 < c.length := c.length_pos (by omega : 0 < n)
  by_contra h
  push_neg at h
  have h_len_one : c.length = 1 := by omega
  -- c.length = 1 ⟹ c = cTarget — but c ∈ cOther excludes cTarget.
  have h_eq : c = cTarget n (by omega : 0 < n) :=
    eq_cTarget_of_length_one (by omega) c h_len_one
  have h_mem_inner : c ∈ Finset.univ.erase (cTarget n (by omega : 0 < n)) :=
    (Finset.mem_erase.mp hc).2
  have h_ne : c ≠ cTarget n (by omega : 0 < n) :=
    (Finset.mem_erase.mp h_mem_inner).1
  exact h_ne h_eq

/-- `1/log u =o[𝓝∞] 1`.  Standard since `log u → +∞`. -/
private lemma one_div_log_isLittleO_one :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => 1 / Real.log u) (fun _ : ℝ => (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_one_iff]
  exact Real.tendsto_log_atTop.inv_tendsto_atTop.congr (fun _ => (one_div _).symm)

/-- `1/(u^a · log² u) =O[𝓝∞] 1/(u^a · log u)`.  Pulls out a factor of
    `1/log u = o(1)`. -/
private lemma inv_polylog_weaken (a : ℕ) :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => 1 / (u ^ a * Real.log u ^ 2))
      (fun u : ℝ => 1 / (u ^ a * Real.log u)) := by
  have h_eq : (fun u : ℝ => 1 / (u ^ a * Real.log u ^ 2))
              =ᶠ[(𝓝∞ : Filter ℝ)]
              (fun u : ℝ => (1 / (u ^ a * Real.log u)) * (1 / Real.log u)) := by
    filter_upwards [log_pos_atTop, Filter.eventually_gt_atTop (0 : ℝ)] with u hlog hu
    have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
    have hu_ne : u ≠ 0 := ne_of_gt hu
    field_simp
  have h_aux : (fun u : ℝ => (1 / (u ^ a * Real.log u)) * (1 / Real.log u))
              =o[(𝓝∞ : Filter ℝ)]
              (fun u : ℝ => (1 / (u ^ a * Real.log u)) * (1 : ℝ)) :=
    (Asymptotics.isBigO_refl _ _).mul_isLittleO one_div_log_isLittleO_one
  have h_o : (fun u : ℝ => 1 / (u ^ a * Real.log u ^ 2))
            =o[(𝓝∞ : Filter ℝ)]
            (fun u : ℝ => 1 / (u ^ a * Real.log u)) := by
    refine h_aux.congr' h_eq.symm ?_
    filter_upwards with u
    ring
  exact h_o.isBigO

/-- **Unified weak per-derivative bound.**  For `1 ≤ k < n`, given the strong
    inductive hypothesis `∀ k', 2 ≤ k' → k' < n → GramAsymp k'`:

      `iteratedDeriv k gram =O[𝓝∞] (fun u => 1 / (u^(k-1) · log u))`.

    For `k = 1`, this is Korolev (`iteratedDeriv_one_gram_isBigO_explicit`).
    For `k ≥ 2`, weakens the tight `1/(u^(k-1) · log² u)` bound via
    `inv_polylog_weaken`. -/
private lemma iteratedDeriv_gram_isBigO_weak (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (ih : ∀ k', 2 ≤ k' → k' < n → GramAsymp k') :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (iteratedDeriv k gram)
      (fun u : ℝ => 1 / (u ^ (k - 1) * Real.log u)) := by
  by_cases h_one : k = 1
  · subst h_one
    have h := iteratedDeriv_one_gram_isBigO_explicit
    refine h.congr_right ?_
    intro u
    change 1 / Real.log u = 1 / (u ^ (1 - 1) * Real.log u)
    rw [Nat.sub_self, pow_zero, one_mul]
  · have hk2 : 2 ≤ k := by omega
    exact (iteratedDeriv_isBigO_explicit k (ih k hk2 hkn)).trans (inv_polylog_weaken (k - 1))

/-- **`IsBigO` of finset products.**  If `f i =O[l] g i` for every `i ∈ s`,
    then `∏ i ∈ s, f i x =O[l] ∏ i ∈ s, g i x`.  Proof: induct on `s`. -/
private lemma isBigO_finset_prod {ι : Type*} (s : Finset ι) {f g : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, Asymptotics.IsBigO (𝓝∞ : Filter ℝ) (f i) (g i)) :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ∏ i ∈ s, f i u)
      (fun u : ℝ => ∏ i ∈ s, g i u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Asymptotics.isBigO_refl _ _
  | @insert a s ha ih =>
    have h_s : ∀ i ∈ s, Asymptotics.IsBigO (𝓝∞ : Filter ℝ) (f i) (g i) := fun i hi =>
      h i (Finset.mem_insert_of_mem hi)
    have h_rest := ih h_s
    have h_a := h a (Finset.mem_insert_self a s)
    have h_combined : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => f a u * ∏ i ∈ s, f i u)
      (fun u : ℝ => g a u * ∏ i ∈ s, g i u) := h_a.mul h_rest
    refine (h_combined.congr_left ?_).congr_right ?_
    · intro u; rw [Finset.prod_insert ha]
    · intro u; rw [Finset.prod_insert ha]

/-!
  ## §2.5.3  Per-summand `cOther` bound

  Combine the per-factor bounds with the structural witness
  `exists_partSize_ge_two_of_mem_cOther`: apply the tight bound at one such
  `j₀` and the weak bound at the remaining indices.  The combined product
  factorises as `1/(u^(n-1) · log² u)` after telescoping the explicit
  log-and-power exponents (`Finset.pow_sum`, `Finset.prod_const`).
-/

/-- Sum of `(c.partSize j - 1)` over all parts equals `n - c.length`.  Uses
    `sum_partSize_eq` and `partSize_pos`. -/
private lemma sum_partSize_sub_one_eq {n : ℕ} (c : OrderedFinpartition n) :
    ∑ j : Fin c.length, (c.partSize j - 1) = n - c.length := by
  have h_sum := sum_partSize_eq c
  have h_pos := c.partSize_pos
  -- c.length ≤ n.
  have h_len_le : c.length ≤ n := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin c.length)))
                                (f := fun _ => 1) (g := c.partSize)
                                (fun i _ => h_pos i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
               smul_eq_mul, mul_one] at h
    rw [h_sum] at h
    exact h
  -- Add c.length back: ∑ (partSize j - 1) + c.length = n.
  have h_back : (∑ j : Fin c.length, (c.partSize j - 1)) + c.length = n := by
    have h_eq : ∑ j : Fin c.length, ((c.partSize j - 1) + 1)
                = ∑ j : Fin c.length, c.partSize j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact Nat.sub_add_cancel (h_pos j)
    rw [Finset.sum_add_distrib] at h_eq
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
               smul_eq_mul, mul_one] at h_eq
    rw [h_sum] at h_eq
    exact h_eq
  omega

/-- Closed form for the "weak per-factor" product over a finset `s ⊆ Fin c.length`:

      `∏ j ∈ s, 1/(u^(c.partSize j - 1) · log u)
         = 1 / (u^(∑ j ∈ s, c.partSize j - 1) · log u ^ s.card)`. -/
private lemma prod_weak_factor_closed_form {n : ℕ} (c : OrderedFinpartition n)
    (s : Finset (Fin c.length)) {u : ℝ}
    (hu : 0 < u) (hlog : Real.log u ≠ 0) :
    ∏ j ∈ s, (1 / (u ^ (c.partSize j - 1) * Real.log u))
      = 1 / (u ^ (∑ j ∈ s, (c.partSize j - 1)) * Real.log u ^ s.card) := by
  classical
  have hu_ne : u ≠ 0 := ne_of_gt hu
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_insert ha,
        Finset.card_insert_of_notMem ha]
    have h_u_pow_t : u ^ (∑ j ∈ t, (c.partSize j - 1)) ≠ 0 := pow_ne_zero _ hu_ne
    have h_u_pow_a : u ^ (c.partSize a - 1) ≠ 0 := pow_ne_zero _ hu_ne
    have h_log_pow : Real.log u ^ t.card ≠ 0 := pow_ne_zero _ hlog
    rw [pow_add, pow_succ]
    field_simp

/-- **Per-summand `cOther` bound.**  For `c ∈ cOther n` and the strong IH
    `∀ k', 2 ≤ k' → k' < n → GramAsymp k'`,

      `θ^(c.length)(gram u) · ∏ⱼ iteratedDeriv (c.partSize j) gram u
         =O[𝓝∞] 1 / (u^(n-1) · log² u)`. -/
private lemma cOther_summand_isBigO {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ k', 2 ≤ k' → k' < n → GramAsymp k')
    {c : OrderedFinpartition n} (hc : c ∈ cOther n (by omega : 0 < n)) :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ =>
        iteratedDeriv c.length theta (gram u) *
        ∏ j, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ => 1 / (u ^ (n - 1) * Real.log u ^ 2)) := by
  classical
  -- (1) Structural data for c ∈ cOther.
  have h_len : 2 ≤ c.length := length_ge_two_of_mem_cOther hn hc
  obtain ⟨j₀, hj₀⟩ := exists_partSize_ge_two_of_mem_cOther hn hc
  have hj₀_lt : c.partSize j₀ < n := partSize_lt_of_mem_cOther hn hc j₀
  -- (2) θ^(c.length)(gram u) bound.
  have h_θ : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => iteratedDeriv c.length theta (gram u))
      (fun u : ℝ => Real.log u ^ (c.length - 1) / u ^ (c.length - 1)) :=
    theta_iter_at_gram_isBigO_explicit c.length h_len
  -- (3) Tight bound at j₀.
  have h_tight : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (iteratedDeriv (c.partSize j₀) gram)
      (fun u : ℝ => 1 / (u ^ (c.partSize j₀ - 1) * Real.log u ^ 2)) :=
    iteratedDeriv_isBigO_explicit (c.partSize j₀) (ih (c.partSize j₀) hj₀ hj₀_lt)
  -- (4) Weak bound at each j ≠ j₀.
  have h_weak : ∀ j ∈ (Finset.univ.erase j₀ : Finset (Fin c.length)),
      Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
        (iteratedDeriv (c.partSize j) gram)
        (fun u : ℝ => 1 / (u ^ (c.partSize j - 1) * Real.log u)) := by
    intro j _
    have h_pos : 1 ≤ c.partSize j := c.partSize_pos j
    have h_lt : c.partSize j < n := partSize_lt_of_mem_cOther hn hc j
    exact iteratedDeriv_gram_isBigO_weak n (c.partSize j) h_pos h_lt ih
  -- (5) Product of weak bounds.
  have h_prod_weak : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ∏ j ∈ Finset.univ.erase j₀, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ => ∏ j ∈ Finset.univ.erase j₀,
                      1 / (u ^ (c.partSize j - 1) * Real.log u)) :=
    isBigO_finset_prod _ h_weak
  -- (6) Split ∏ⱼ at j₀.
  have h_prod_split :
      (fun u : ℝ => ∏ j, iteratedDeriv (c.partSize j) gram u)
        =
      (fun u : ℝ => iteratedDeriv (c.partSize j₀) gram u *
                    ∏ j ∈ Finset.univ.erase j₀, iteratedDeriv (c.partSize j) gram u) := by
    funext u
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)).symm
  -- (7) Combine: ∏ⱼ iteratedDeriv =O tight(j₀) · ∏_{erase j₀} weak.
  have h_prod_O : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ∏ j, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ => (1 / (u ^ (c.partSize j₀ - 1) * Real.log u ^ 2)) *
                    ∏ j ∈ Finset.univ.erase j₀,
                      1 / (u ^ (c.partSize j - 1) * Real.log u)) := by
    rw [h_prod_split]
    exact h_tight.mul h_prod_weak
  -- (8) Multiply by θ-bound.
  have h_total_O : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ =>
        iteratedDeriv c.length theta (gram u) *
        ∏ j, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ =>
        (Real.log u ^ (c.length - 1) / u ^ (c.length - 1)) *
        ((1 / (u ^ (c.partSize j₀ - 1) * Real.log u ^ 2)) *
         ∏ j ∈ Finset.univ.erase j₀,
           1 / (u ^ (c.partSize j - 1) * Real.log u))) :=
    h_θ.mul h_prod_O
  -- (9) Pointwise simplify the bound to `1/(u^(n-1) · log² u)` eventually.
  refine h_total_O.trans ?_
  -- Goal: the explicit bound function is =O[𝓝∞] (1/(u^(n-1) · log² u)).
  -- We show it's eventually equal.
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), log_pos_atTop]
    with u hu hlog
  have hu0 : 0 < u := by linarith
  have hu_ne : u ≠ 0 := ne_of_gt hu0
  have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
  -- Step A: closed form for the erase j₀ product.
  have h_erase_card : (Finset.univ.erase j₀ : Finset (Fin c.length)).card
                      = c.length - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j₀),
        Finset.card_univ, Fintype.card_fin]
  have h_prod_closed :
      ∏ j ∈ (Finset.univ.erase j₀ : Finset (Fin c.length)),
        1 / (u ^ (c.partSize j - 1) * Real.log u) =
      1 / (u ^ (∑ j ∈ (Finset.univ.erase j₀ : Finset (Fin c.length)),
                  (c.partSize j - 1))
           * Real.log u ^ (c.length - 1)) := by
    rw [prod_weak_factor_closed_form c _ hu0 hlog_ne, h_erase_card]
  -- Step B: telescope the u-exponent.
  -- (c.length - 1) + (c.partSize j₀ - 1) + ∑_{erase j₀}(partSize j - 1) = n - 1.
  have h_sum_partSize_sub_one : ∑ j : Fin c.length, (c.partSize j - 1) = n - c.length :=
    sum_partSize_sub_one_eq c
  have h_sum_erase :
      (c.partSize j₀ - 1) +
        ∑ j ∈ (Finset.univ.erase j₀ : Finset (Fin c.length)), (c.partSize j - 1)
      = n - c.length := by
    have h_add_erase := Finset.add_sum_erase
      (Finset.univ : Finset (Fin c.length))
      (fun j => c.partSize j - 1) (Finset.mem_univ j₀)
    rw [h_add_erase, h_sum_partSize_sub_one]
  -- u-exponent: (c.length - 1) + (c.partSize j₀ - 1) + (n - c.length - (partSize j₀ - 1)).
  -- Working in ℕ, equivalently c.length - 1 + n - c.length.
  have h_len_le : c.length ≤ n := by
    -- From sum_partSize_eq and partSize_pos.
    have h_sum := sum_partSize_eq c
    have h_pos := c.partSize_pos
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin c.length)))
                                (f := fun _ => 1) (g := c.partSize)
                                (fun i _ => h_pos i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
               smul_eq_mul, mul_one] at h
    rw [h_sum] at h
    exact h
  -- Final pointwise calc.
  rw [h_prod_closed]
  have hu_pow_ne : ∀ k : ℕ, u ^ k ≠ 0 := fun k => pow_ne_zero _ hu_ne
  have hlog_pow_ne : ∀ k : ℕ, Real.log u ^ k ≠ 0 := fun k => pow_ne_zero _ hlog_ne
  -- LHS: (log u)^(c.length - 1) / u^(c.length - 1) *
  --       ((1/(u^(partSize j₀ - 1) · log² u)) *
  --        (1/(u^∑_erase(partSize-1) · log^(c.length - 1) u)))
  -- = 1 / (u^(n-1) · log² u)
  set m : ℕ := c.length - 1 with hm_def
  set s_erase : ℕ := ∑ j ∈ (Finset.univ.erase j₀ : Finset (Fin c.length)),
                       (c.partSize j - 1) with hs_def
  -- u-exponent telescope:
  --   m + ((partSize j₀ - 1) + s_erase) = (c.length - 1) + (n - c.length) = n - 1.
  have h_telescope_u :
      m + (c.partSize j₀ - 1) + s_erase = n - 1 := by
    have : (c.partSize j₀ - 1) + s_erase = n - c.length := h_sum_erase
    omega
  -- log-exponent telescope:
  --   m + 2 + m = (c.length - 1) + 2 + (c.length - 1) -- on numerator side m
  --   Numerator log u^m, denominator log² u · log^m u → log^(m+2-m) = log² u net effect.
  -- The identity:
  --   (log u)^m / u^m · 1/(u^(partSize j₀ - 1) · log² u) ·
  --   1/(u^s_erase · log^m u)
  --   = (log u)^m / (u^m · u^(partSize j₀ - 1) · u^s_erase · log² u · log^m u)
  --   = 1 / (u^(m + (partSize j₀ - 1) + s_erase) · log² u)
  --   = 1 / (u^(n-1) · log² u).
  -- Algebraic manipulation:
  have h_pow_add_u : u ^ (m + (c.partSize j₀ - 1) + s_erase)
                    = u ^ m * u ^ (c.partSize j₀ - 1) * u ^ s_erase := by
    rw [pow_add, pow_add]
  -- Use h_telescope_u to rewrite to u^(n-1).
  have h_u_n_sub_1 : u ^ (n - 1) =
      u ^ m * u ^ (c.partSize j₀ - 1) * u ^ s_erase := by
    rw [← h_telescope_u, pow_add, pow_add]
  -- Final norm: |LHS| ≤ 1 * |1 / (u^(n-1) · log² u)|.
  -- Compute LHS algebraically.
  have h_lhs :
      Real.log u ^ m / u ^ m *
        (1 / (u ^ (c.partSize j₀ - 1) * Real.log u ^ 2) *
          (1 / (u ^ s_erase * Real.log u ^ m)))
      = 1 / (u ^ (n - 1) * Real.log u ^ 2) := by
    rw [h_u_n_sub_1]
    have hum := hu_pow_ne m
    have hus := hu_pow_ne s_erase
    have huj0 := hu_pow_ne (c.partSize j₀ - 1)
    have hlogm := hlog_pow_ne m
    have hlog2 : Real.log u ^ 2 ≠ 0 := pow_ne_zero _ hlog_ne
    field_simp
  rw [h_lhs]
  rw [one_mul]

/-!
  ## §2.5.4  Sum over `cOther` and contribution to the residual

  Sum the per-summand bounds over `cOther` and multiply by `-(deriv gram u / π)`
  (the prefactor in the §2.3 solved form).  Conclude that the cOther
  contribution is `o[𝓝∞] (gramLeading n u · log log u / log u)`.
-/

/-- Sum of per-summand bounds: `∑ c ∈ cOther n, c-summand =O[𝓝∞] 1/(u^(n-1) · log² u)`. -/
private lemma cOther_sum_isBigO {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ k', 2 ≤ k' → k' < n → GramAsymp k') :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => ∑ c ∈ cOther n (by omega : 0 < n),
        iteratedDeriv c.length theta (gram u) *
        ∏ j, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ => 1 / (u ^ (n - 1) * Real.log u ^ 2)) :=
  Asymptotics.IsBigO.sum (fun _ hc => cOther_summand_isBigO hn ih hc)

/-- `gramLeading n u · log log u / log u =O[𝓝∞] 1/(u^(n-1) · log² u) · log log u`.
    Hidden constant `|gramLeading n u| ≤ const / (u^(n-1) · log² u)`. -/
private lemma gramLeading_mul_loglog_div_log_eq {n : ℕ} (u : ℝ)
    (hu : u ≠ 0) (hlog : Real.log u ≠ 0) :
    gramLeading n u * Real.log (Real.log u) / Real.log u
      = ((-1 : ℝ) ^ (n + 1) * (2 * Real.pi) * ((n - 2).factorial : ℝ))
        * (Real.log (Real.log u) / (u ^ (n - 1) * Real.log u ^ 3)) := by
  unfold gramLeading
  have hu_pow : u ^ (n - 1) ≠ 0 := pow_ne_zero _ hu
  have hlog_pow : Real.log u ^ 2 ≠ 0 := pow_ne_zero _ hlog
  field_simp

/-- `1 = o(log log u)` at `+∞`.  Standard consequence of `log log u → +∞`. -/
private lemma one_isLittleO_loglog :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun _ : ℝ => (1 : ℝ))
      (fun u : ℝ => Real.log (Real.log u)) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · -- Tendsto (fun u => 1 / log log u) 𝓝∞ (𝓝 0).
    have h_tend : Tendsto (fun u : ℝ => Real.log (Real.log u)) 𝓝∞ 𝓝∞ :=
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    refine h_tend.inv_tendsto_atTop.congr ?_
    intro u
    exact (one_div _).symm
  · filter_upwards [loglog_pos_atTop] with u hu h_zero
    exact absurd h_zero (ne_of_gt hu)

/-- `-(deriv gram u / π) =O[𝓝∞] 1 / log u`.

    Combines `iteratedDeriv_one_gram_isBigO_explicit` (Korolev) with
    `iteratedDeriv_one gram = deriv gram`. -/
private lemma neg_deriv_gram_div_pi_isBigO_inv_log :
    Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => -(deriv gram u / Real.pi))
      (fun u : ℝ => 1 / Real.log u) := by
  have h_pre := iteratedDeriv_one_gram_isBigO_explicit
  have h_const : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => -(deriv gram u / Real.pi))
      (iteratedDeriv 1 gram) := by
    have h := Asymptotics.isBigO_const_mul_self (-(1 / Real.pi))
      (iteratedDeriv 1 gram) (𝓝∞ : Filter ℝ)
    refine h.congr_left ?_
    intro u
    rw [iteratedDeriv_one]
    ring
  exact h_const.trans h_pre

/-- `1 / log u · 1/(u^(n-1) · log² u) =ᶠ[𝓝∞] 1/(u^(n-1) · log³ u)`. -/
private lemma inv_log_mul_inv_polylog_eq {n : ℕ} :
    (fun u : ℝ => (1 / Real.log u) * (1 / (u ^ (n - 1) * Real.log u ^ 2)))
      =ᶠ[(𝓝∞ : Filter ℝ)]
    (fun u : ℝ => 1 / (u ^ (n - 1) * Real.log u ^ 3)) := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), log_pos_atTop] with u hu hlog
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
  have hu_pow : u ^ (n - 1) ≠ 0 := pow_ne_zero _ hu_ne
  have hlog2 : Real.log u ^ 2 ≠ 0 := pow_ne_zero _ hlog_ne
  have h_log_cube : Real.log u ^ 3 = Real.log u * Real.log u ^ 2 := by ring
  rw [h_log_cube]
  field_simp

/-- The cOther contribution `-(deriv gram u / π) · ∑ cOther` is
    `o[𝓝∞] (gramLeading n u · log log u / log u)`. -/
private lemma cOther_contribution_isLittleO {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ k', 2 ≤ k' → k' < n → GramAsymp k') :
    Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ =>
        -(deriv gram u / Real.pi) *
        ∑ c ∈ cOther n (by omega : 0 < n),
          iteratedDeriv c.length theta (gram u) *
          ∏ j, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ => gramLeading n u * Real.log (Real.log u) / Real.log u) := by
  -- (1) -(deriv gram u / π) · ∑ c-summand =O 1/(u^(n-1) · log³ u).
  have h_deriv_O := neg_deriv_gram_div_pi_isBigO_inv_log
  have h_sum := cOther_sum_isBigO hn ih
  have h_prod_full : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ =>
        -(deriv gram u / Real.pi) *
        ∑ c ∈ cOther n (by omega : 0 < n),
          iteratedDeriv c.length theta (gram u) *
          ∏ j, iteratedDeriv (c.partSize j) gram u)
      (fun u : ℝ => 1 / (u ^ (n - 1) * Real.log u ^ 3)) := by
    have h := h_deriv_O.mul h_sum
    exact h.congr' Filter.EventuallyEq.rfl inv_log_mul_inv_polylog_eq
  -- (2) 1/(u^(n-1) · log³ u) =o log log u / (u^(n-1) · log³ u).
  have h_one_o_loglog := one_isLittleO_loglog
  have h_polylog_o_loglog_polylog : Asymptotics.IsLittleO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => 1 / (u ^ (n - 1) * Real.log u ^ 3))
      (fun u : ℝ => Real.log (Real.log u) / (u ^ (n - 1) * Real.log u ^ 3)) := by
    have h := h_one_o_loglog.mul_isBigO
      (Asymptotics.isBigO_refl (fun u : ℝ => 1 / (u ^ (n - 1) * Real.log u ^ 3)) 𝓝∞)
    refine (h.congr_left ?_).congr_right ?_
    · intro u; rw [one_mul]
    · intro u; ring
  -- (3) log log u / (u^(n-1) · log³ u) =O gramLeading n u · log log u / log u.
  have c_ne : ((-1 : ℝ) ^ (n + 1) * (2 * Real.pi) * ((n - 2).factorial : ℝ)) ≠ 0 := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h1 : (-1 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    have h3 : ((n - 2).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  have h_loglog_polylog_O_gramLeading : Asymptotics.IsBigO (𝓝∞ : Filter ℝ)
      (fun u : ℝ => Real.log (Real.log u) / (u ^ (n - 1) * Real.log u ^ 3))
      (fun u : ℝ => gramLeading n u * Real.log (Real.log u) / Real.log u) := by
    have h_const_inv := Asymptotics.isBigO_const_mul_self
      (((-1 : ℝ) ^ (n + 1) * (2 * Real.pi) * ((n - 2).factorial : ℝ))⁻¹)
      (fun u : ℝ => gramLeading n u * Real.log (Real.log u) / Real.log u)
      (𝓝∞ : Filter ℝ)
    have h_eq : (fun u : ℝ =>
        ((-1 : ℝ) ^ (n + 1) * (2 * Real.pi) * ((n - 2).factorial : ℝ))⁻¹ *
          (gramLeading n u * Real.log (Real.log u) / Real.log u))
        =ᶠ[(𝓝∞ : Filter ℝ)]
        (fun u : ℝ => Real.log (Real.log u) / (u ^ (n - 1) * Real.log u ^ 3)) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), log_pos_atTop] with u hu hlog
      have hu_ne : u ≠ 0 := ne_of_gt hu
      have hlog_ne : Real.log u ≠ 0 := ne_of_gt hlog
      rw [gramLeading_mul_loglog_div_log_eq u hu_ne hlog_ne,
          ← mul_assoc, inv_mul_cancel₀ c_ne, one_mul]
    exact h_const_inv.congr' h_eq Filter.EventuallyEq.rfl
  -- (4) Chain: full =O 1/(...) =o log log u /(...)) =O gramLeading n u · ll/l.
  exact (h_prod_full.trans_isLittleO h_polylog_o_loglog_polylog).trans_isBigO
    h_loglog_polylog_O_gramLeading

/-!
  ## §2.6  Theorem 3, induction step

  Combine `theorem3_atomic_term` with `cOther_contribution_isLittleO` via
  `iteratedDeriv_n_gram_solved_eventually` to close the induction step.  Base
  case `n = 2` is `gramAsymp_two = theorem3_two`.
-/

/-- **Theorem 3** (Dundulis–Garunkštis–Laurinčikas–Šimenas, 2026).

    For `n ≥ 2`, the `n`-th derivative of the Gram function satisfies

        t_u^(n) = (-1)^(n+1) · 2π · (n − 2)! / (u^(n-1) · log² u)
                  · (1 + (2 + o(1)) · log log u / log u)

    as `u → +∞`.  Equivalently, the residual

        t_u^(n) − leading(u) − 2 · leading(u) · log log u / log u

    is little-o of `leading(u) · log log u / log u`. -/
theorem theorem3 (n : ℕ) (hn : 2 ≤ n) :
    Iso
      (fun u : ℝ =>
        iteratedDeriv n gram u
        - gramLeading n u
        - 2 * gramLeading n u * Real.log (Real.log u) / Real.log u)
      (fun u : ℝ => gramLeading n u * Real.log (Real.log u) / Real.log u)
      𝓝∞ := by
  -- Strong induction on `N ≥ 2`, with `theorem3 n hn` extracted at the end.
  suffices h : ∀ N : ℕ, 2 ≤ N → GramAsymp N from h n hn
  clear hn n
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih_strong =>
    intro hN
    by_cases h_two : N = 2
    · subst h_two; exact gramAsymp_two
    · have h_ge_three : 3 ≤ N := by omega
      -- Strong inductive hypothesis in the form expected by §2.5.4.
      have ih : ∀ k', 2 ≤ k' → k' < N → GramAsymp k' :=
        fun k' h2 hlt => ih_strong k' hlt h2
      -- Atomic-term residual is `o(target)`.
      have h_atomic := theorem3_atomic_term N hN
      -- cOther contribution is `o(target)`.
      have h_cOther := cOther_contribution_isLittleO hN ih
      -- Their sum is `o(target)`.
      have h_sum := h_atomic.add h_cOther
      -- §2.3 solved form: `iteratedDeriv N gram u = atomic + cOther` (eventually).
      have h_solved := iteratedDeriv_n_gram_solved_eventually N h_ge_three
      -- Lift the eventual equality to swap `h_sum`'s LHS for the target shape.
      refine h_sum.congr' ?_ Filter.EventuallyEq.rfl
      filter_upwards [h_solved] with u h_iter
      -- `h_iter` rewrites `iteratedDeriv N gram u` on the RHS, after which `ring`
      -- (with `(deriv gram u)^(N+1) = (deriv gram u)^N · deriv gram u`) closes.
      change
        (-(1 / Real.pi) * iteratedDeriv N theta (gram u) * (deriv gram u) ^ (N + 1)
            - gramLeading N u
            - 2 * gramLeading N u * Real.log (Real.log u) / Real.log u)
          + -(deriv gram u / Real.pi) *
            ∑ c ∈ cOther N (by omega : 0 < N),
              iteratedDeriv c.length theta (gram u) *
              ∏ j, iteratedDeriv (c.partSize j) gram u
          =
          iteratedDeriv N gram u
            - gramLeading N u
            - 2 * gramLeading N u * Real.log (Real.log u) / Real.log u
      rw [h_iter, pow_succ]
      ring
