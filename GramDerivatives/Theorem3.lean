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
  This file is a **stub**: axiom signatures and the top-level statement
  are in place; the proof of `theorem3` is `sorry` and will be filled in
  later.
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
  sorry
