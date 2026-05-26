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
