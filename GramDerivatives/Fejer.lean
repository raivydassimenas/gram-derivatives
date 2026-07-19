import GramDerivatives.VanDerCorput
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Fejér's theorem and the higher-derivative Kuipers–Niederreiter criterion

This file proves the **last remaining analytic input** of the project: the
higher-derivative Fejér / Kuipers–Niederreiter criterion
`isUDModOne_of_iteratedDeriv_decay`, formerly an `axiom` in `Theorem4.lean`.

The chain of results, following Kuipers–Niederreiter, *Uniform Distribution
of Sequences*, Chapter 1:

* **Theorem 2.5** (discrete Fejér theorem), `isUDModOne_of_antitone_diff`:
  if the difference sequence `d n = a (n+1) − a n` is positive, antitone,
  tends to `0`, and `n · d n → ∞`, then `(a n)` is u.d. mod 1.  The proof is
  Abel summation against `1/d n`, powered by the quadratic Taylor bound
  `‖exp(iθ) − 1 − iθ‖ ≤ 3θ²` and the Cesàro lemma `Filter.Tendsto.cesaro`.

* **Corollary 2.1** (Fejér's theorem for functions) appears here directly in
  iterated-derivative form as the base case `l = 1` of the master lemma
  `isUDModOne_of_iteratedDeriv_pos_antitone`: the mean value theorem
  transfers the hypotheses on `f'` to the difference sequence of
  `(f (n + n₀))ₙ`, and an index unshift (`isUDModOne_of_shift`) recovers
  `(f n)ₙ`.

* The **inductive step** (Pańkowski's higher-derivative extension) reduces
  level `l + 1` to level `l` through van der Corput's difference theorem
  `isUDModOne_of_forall_diff` (proved in `VanDerCorput.lean`): each shifted
  difference `g u = f (u + h) − f u` satisfies the level-`l` hypotheses by
  the mean value theorem applied to `iteratedDeriv l f`.

* Finally `isUDModOne_of_iteratedDeriv_decay` derives from eventual
  nonvanishing (via `u·|f^(l)(u)| → ∞`) and continuity that `f^(l)` has
  eventually constant sign, and applies the master lemma to `f` or `−f`.

The file is **axiom-free**; together with `VanDerCorput.lean` it eliminates
the project's final `-- ASSUMPTION`.
-/

open Filter
open scoped Topology BigOperators

namespace Gram.UD

/-! ## §1  Index unshift

`IsUDModOne.shift` (`UDModOne.lean`) shows u.d. mod 1 survives dropping the
first term; here we go the other way — u.d. of a tail implies u.d. of the
full sequence — so that finitely many initial terms can be discarded before
applying the discrete Fejér estimate. -/

/-- If the once-shifted sequence `(a (n+1))ₙ` is u.d. mod 1, so is `(a n)ₙ`:
the two Cesàro averages differ by a boundary term of norm `≤ 2/N`. -/
theorem IsUDModOne.unshift {a : ℕ → ℝ}
    (h : IsUDModOne fun n => a (n + 1)) : IsUDModOne a := by
  intro k hk
  set e : ℕ → ℂ := fun n =>
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)) with he
  have hnorm : ∀ n, ‖e n‖ = 1 := by
    intro n
    simp [he, Complex.norm_exp]
  -- The unshifted partial sum telescopes against the shifted one.
  have hsum : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, e n)
        = (∑ n ∈ Finset.range N, e (n + 1)) + e 0 - e N := by
    intro N
    have h1 := Finset.sum_range_succ' e N
    have h2 := Finset.sum_range_succ e N
    linear_combination h1 - h2
  -- The boundary term `(1/N)·(e 0 - e N)` vanishes at infinity.
  have herr :
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * (e 0 - e N)) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun N => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat 2)
    calc ‖(1 / (N : ℂ)) * (e 0 - e N)‖
        = 1 / (N : ℝ) * ‖e 0 - e N‖ := by
          rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      _ ≤ 1 / (N : ℝ) * 2 := by
          have : ‖e 0 - e N‖ ≤ 2 := by
            calc ‖e 0 - e N‖ ≤ ‖e 0‖ + ‖e N‖ := norm_sub_le _ _
              _ = 2 := by rw [hnorm, hnorm]; norm_num
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 / (N : ℝ) := by ring
  have hlim := (h k hk).add herr
  rw [add_zero] at hlim
  refine hlim.congr fun N => ?_
  change (1 / (N : ℂ)) * (∑ n ∈ Finset.range N, e (n + 1))
        + (1 / (N : ℂ)) * (e 0 - e N)
      = (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, e n
  rw [hsum N]; ring

/-- If a tail `(a (n + m))ₙ` is u.d. mod 1, so is `(a n)ₙ`. -/
theorem isUDModOne_of_shift (m : ℕ) {a : ℕ → ℝ}
    (h : IsUDModOne fun n => a (n + m)) : IsUDModOne a := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    refine ih (IsUDModOne.unshift (a := fun n => a (n + m)) ?_)
    have heq : (fun n : ℕ => a (n + 1 + m)) = fun n : ℕ => a (n + (m + 1)) := by
      funext n; congr 1; omega
    exact heq ▸ h

/-! ## §2  A global quadratic bound for the complex exponential -/

/-- Global second-order Taylor bound `‖exp(iθ) − 1 − iθ‖ ≤ 3θ²` for real `θ`
(Kuipers–Niederreiter, inequality (2.13), with a cruder constant): for
`|θ| ≤ 1` this is Mathlib's `Complex.norm_exp_sub_one_sub_id_le`; for
`|θ| ≥ 1` the triangle inequality gives `2 + |θ| ≤ 3θ²`. -/
private lemma norm_exp_mul_I_sub_one_sub_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖
      ≤ 3 * θ ^ 2 := by
  have hnormθI : ‖(θ : ℂ) * Complex.I‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt |θ| 1 with hθ | hθ
  · have h := Complex.norm_exp_sub_one_sub_id_le
      (x := (θ : ℂ) * Complex.I) (by rw [hnormθI]; exact hθ)
    calc ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖
        ≤ ‖(θ : ℂ) * Complex.I‖ ^ 2 := h
      _ = θ ^ 2 := by rw [hnormθI, sq_abs]
      _ ≤ 3 * θ ^ 2 := by nlinarith [sq_nonneg θ]
  · have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I θ
    have hθ2 : (1 : ℝ) ≤ θ ^ 2 := by nlinarith [abs_nonneg θ, sq_abs θ]
    have habs : |θ| ≤ θ ^ 2 := by nlinarith [abs_nonneg θ, sq_abs θ]
    calc ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖
        ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ + ‖(θ : ℂ) * Complex.I‖ :=
          norm_sub_le _ _
      _ ≤ (‖Complex.exp ((θ : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) + |θ| := by
          rw [hnormθI]
          exact add_le_add
            (norm_sub_le (Complex.exp ((θ : ℂ) * Complex.I)) 1) le_rfl
      _ = 2 + |θ| := by rw [h1, norm_one]; ring
      _ ≤ 3 * θ ^ 2 := by linarith

/-! ## §3  The discrete Fejér theorem (Kuipers–Niederreiter, Theorem 2.5) -/

/-- **Discrete Fejér theorem** (Kuipers–Niederreiter, Theorem 2.5, antitone
positive case): if the difference sequence `d n = a (n+1) − a n` is positive
and antitone with `d n → 0` and `n · d n → ∞`, then `(a n)ₙ` is uniformly
distributed mod one.

Proof: fix a nonzero frequency `k` and let `e n = exp(2πik·a n)`.  Abel
summation against `1/d n` (inequality (2.14) of the book) bounds
`2π|k| · ‖∑_{n<N} e n‖` by `2/d N + 12π²k² ∑_{n<N} d n`; dividing by `N`,
the first term dies by `N·d N → ∞` and the second by the Cesàro lemma. -/
theorem isUDModOne_of_antitone_diff {a : ℕ → ℝ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1) - a n)
    (hanti : ∀ m n : ℕ, m ≤ n → a (n + 1) - a n ≤ a (m + 1) - a m)
    (h0 : Tendsto (fun n : ℕ => a (n + 1) - a n) atTop (𝓝 0))
    (hInf : Tendsto (fun n : ℕ => (n : ℝ) * (a (n + 1) - a n)) atTop atTop) :
    IsUDModOne a := by
  intro k hk
  set d : ℕ → ℝ := fun n => a (n + 1) - a n with hd_def
  set c : ℂ := 2 * Real.pi * Complex.I * (k : ℂ) with hc_def
  set e : ℕ → ℂ := fun n => Complex.exp (c * (a n : ℂ)) with he_def
  set C : ℝ := 12 * Real.pi ^ 2 * (k : ℝ) ^ 2 with hC_def
  have hknorm : (1 : ℝ) ≤ |(k : ℝ)| := by
    have := Int.one_le_abs hk
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |(k : ℝ)| := Int.cast_abs
  have hcnorm : ‖c‖ = 2 * Real.pi * |(k : ℝ)| := by
    rw [hc_def,
      show ((k : ℤ) : ℂ) = (((k : ℝ) : ℝ) : ℂ) from by push_cast; ring,
      show ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ) : ℝ) : ℂ) from by
        push_cast; ring]
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hcpos : (0 : ℝ) < 2 * Real.pi * |(k : ℝ)| := by
    have := Real.pi_pos; nlinarith
  have hnorm : ∀ n, ‖e n‖ = 1 := by
    intro n
    simp [he_def, hc_def, Complex.norm_exp]
  -- The one-step increment identity.
  have hstep : ∀ n : ℕ, e (n + 1)
      = e n * Complex.exp (((2 * Real.pi * (k : ℝ) * d n : ℝ) : ℂ)
          * Complex.I) := by
    intro n
    simp only [he_def]
    rw [← Complex.exp_add]
    congr 1
    have hsplit : ((a (n + 1) : ℝ) : ℂ) = (a n : ℂ) + ((d n : ℝ) : ℂ) := by
      simp only [hd_def]; push_cast; ring
    rw [hsplit]
    simp only [hc_def]
    push_cast
    ring
  -- The quadratic increment bound, from `norm_exp_mul_I_sub_one_sub_le`.
  have hkey : ∀ n : ℕ, ‖e (n + 1) - e n - c * (d n : ℂ) * e n‖
      ≤ C * d n ^ 2 := by
    intro n
    have hw : e (n + 1) - e n - c * (d n : ℂ) * e n
        = e n * (Complex.exp (((2 * Real.pi * (k : ℝ) * d n : ℝ) : ℂ)
              * Complex.I) - 1
            - ((2 * Real.pi * (k : ℝ) * d n : ℝ) : ℂ) * Complex.I) := by
      rw [hstep n]
      simp only [hc_def]
      push_cast
      ring
    rw [hw, norm_mul, hnorm, one_mul]
    calc ‖Complex.exp (((2 * Real.pi * (k : ℝ) * d n : ℝ) : ℂ) * Complex.I)
          - 1 - ((2 * Real.pi * (k : ℝ) * d n : ℝ) : ℂ) * Complex.I‖
        ≤ 3 * (2 * Real.pi * (k : ℝ) * d n) ^ 2 :=
          norm_exp_mul_I_sub_one_sub_le _
      _ = C * d n ^ 2 := by simp only [hC_def]; ring
  -- The Abel-summation error term and its bound (inequality (2.14)).
  set err : ℕ → ℂ := fun n =>
    e (n + 1) / (d (n + 1) : ℂ) - e n / (d n : ℂ) - c * e n with herr_def
  have hd_ne : ∀ n, ((d n : ℝ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (hpos n).ne'
  have hinv_mono : ∀ n : ℕ, 1 / d n ≤ 1 / d (n + 1) := fun n =>
    one_div_le_one_div_of_le (hpos (n + 1)) (hanti n (n + 1) (Nat.le_succ n))
  have herr_bound : ∀ n : ℕ,
      ‖err n‖ ≤ C * d n + (1 / d (n + 1) - 1 / d n) := by
    intro n
    have hsplit : err n
        = (e (n + 1) - e n - c * (d n : ℂ) * e n) / (d n : ℂ)
          + e (n + 1) * (1 / (d (n + 1) : ℂ) - 1 / (d n : ℂ)) := by
      simp only [herr_def]
      field_simp [hd_ne n, hd_ne (n + 1)]
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(e (n + 1) - e n - c * (d n : ℂ) * e n) / (d n : ℂ)‖
        ≤ C * d n := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hpos n), div_le_iff₀ (hpos n)]
      calc ‖e (n + 1) - e n - c * (d n : ℂ) * e n‖ ≤ C * d n ^ 2 := hkey n
        _ = C * d n * d n := by ring
    have h2 : ‖e (n + 1) * (1 / (d (n + 1) : ℂ) - 1 / (d n : ℂ))‖
        = 1 / d (n + 1) - 1 / d n := by
      rw [norm_mul, hnorm, one_mul,
        show 1 / ((d (n + 1) : ℝ) : ℂ) - 1 / ((d n : ℝ) : ℂ)
            = ((1 / d (n + 1) - 1 / d n : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (sub_nonneg.mpr (hinv_mono n))
    linarith [h1, h2.le, h2.ge]
  -- Abel summation: the weighted sum telescopes.
  have hsum_id : ∀ N : ℕ, c * ∑ n ∈ Finset.range N, e n
      = (e N / (d N : ℂ) - e 0 / (d 0 : ℂ))
        - ∑ n ∈ Finset.range N, err n := by
    intro N
    have htel := Finset.sum_range_sub (fun n => e n / (d n : ℂ)) N
    calc c * ∑ n ∈ Finset.range N, e n
        = ∑ n ∈ Finset.range N, c * e n := Finset.mul_sum _ _ _
      _ = ∑ n ∈ Finset.range N,
            ((e (n + 1) / (d (n + 1) : ℂ) - e n / (d n : ℂ)) - err n) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          simp only [herr_def]; ring
      _ = (∑ n ∈ Finset.range N,
            (e (n + 1) / (d (n + 1) : ℂ) - e n / (d n : ℂ)))
            - ∑ n ∈ Finset.range N, err n :=
          Finset.sum_sub_distrib
            (f := fun n => e (n + 1) / (d (n + 1) : ℂ) - e n / (d n : ℂ))
            (g := err)
      _ = _ := by rw [htel]
  -- The resulting norm bound on the raw Weyl sum.
  have hnormsum : ∀ N : ℕ,
      2 * Real.pi * |(k : ℝ)| * ‖∑ n ∈ Finset.range N, e n‖
        ≤ 2 / d N + C * ∑ n ∈ Finset.range N, d n := by
    intro N
    have hediv : ∀ n : ℕ, ‖e n / (d n : ℂ)‖ = 1 / d n := fun n => by
      rw [norm_div, hnorm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hpos n)]
    have htel2 := Finset.sum_range_sub (fun n => 1 / d n) N
    calc 2 * Real.pi * |(k : ℝ)| * ‖∑ n ∈ Finset.range N, e n‖
        = ‖c * ∑ n ∈ Finset.range N, e n‖ := by rw [norm_mul, hcnorm]
      _ = ‖(e N / (d N : ℂ) - e 0 / (d 0 : ℂ))
            - ∑ n ∈ Finset.range N, err n‖ := by rw [hsum_id N]
      _ ≤ ‖e N / (d N : ℂ) - e 0 / (d 0 : ℂ)‖
            + ‖∑ n ∈ Finset.range N, err n‖ := norm_sub_le _ _
      _ ≤ (‖e N / (d N : ℂ)‖ + ‖e 0 / (d 0 : ℂ)‖)
            + ∑ n ∈ Finset.range N, ‖err n‖ := by
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
      _ ≤ (1 / d N + 1 / d 0)
            + ∑ n ∈ Finset.range N,
                (C * d n + (1 / d (n + 1) - 1 / d n)) := by
          rw [hediv N, hediv 0]
          gcongr with n hn
          exact herr_bound n
      _ = (1 / d N + 1 / d 0)
            + (C * ∑ n ∈ Finset.range N, d n + (1 / d N - 1 / d 0)) := by
          rw [Finset.sum_add_distrib, htel2, ← Finset.mul_sum]
      _ = 2 / d N + C * ∑ n ∈ Finset.range N, d n := by ring
  -- The vanishing bound sequence.
  have hB : Tendsto (fun N : ℕ =>
      (2 / ((N : ℝ) * d N)
        + C * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, d n))
        / (2 * Real.pi * |(k : ℝ)|)) atTop (𝓝 0) := by
    have t1 : Tendsto (fun N : ℕ => 2 / ((N : ℝ) * d N)) atTop (𝓝 0) := by
      have h := hInf.inv_tendsto_atTop
      have h2 := h.const_mul (2 : ℝ)
      rw [mul_zero] at h2
      exact h2.congr fun N => by
        simp only [Pi.inv_apply]
        rw [div_eq_mul_inv]
    have t2 : Tendsto (fun N : ℕ =>
        (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, d n) atTop (𝓝 0) := h0.cesaro
    have t3 := t2.const_mul C
    rw [mul_zero] at t3
    have t4 := (t1.add t3).div_const (2 * Real.pi * |(k : ℝ)|)
    rw [add_zero, zero_div] at t4
    exact t4
  -- Stitch: squeeze the Cesàro averages of the Weyl exponentials.
  refine squeeze_zero_norm' ?_ hB
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsum_le : ‖∑ n ∈ Finset.range N, e n‖
      ≤ (2 / d N + C * ∑ n ∈ Finset.range N, d n)
        / (2 * Real.pi * |(k : ℝ)|) := by
    rw [le_div_iff₀ hcpos]
    calc ‖∑ n ∈ Finset.range N, e n‖ * (2 * Real.pi * |(k : ℝ)|)
        = 2 * Real.pi * |(k : ℝ)| * ‖∑ n ∈ Finset.range N, e n‖ := by ring
      _ ≤ _ := hnormsum N
  have hnorm_avg : ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, e n‖
      = (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N, e n‖ := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  rw [hnorm_avg]
  calc (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N, e n‖
      ≤ (1 / (N : ℝ)) * ((2 / d N + C * ∑ n ∈ Finset.range N, d n)
          / (2 * Real.pi * |(k : ℝ)|)) := by
        exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = (2 / ((N : ℝ) * d N)
          + C * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, d n))
          / (2 * Real.pi * |(k : ℝ)|) := by
        have hdN : d N ≠ 0 := (hpos N).ne'
        have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
        have hc0 : 2 * Real.pi * |(k : ℝ)| ≠ 0 := hcpos.ne'
        field_simp

/-! ## §4  Tail calculus for iterated derivatives

Pointwise `ContDiffAt` hypotheses on a tail `(A, ∞)` yield continuity,
differentiability, and the mean value theorem for `iteratedDeriv m f` there,
via `iteratedDerivWithin` on the open tail (the same scaffolding as
`Theorem4.lean` §4). -/

private lemma continuousOn_iteratedDeriv_tail {f : ℝ → ℝ} {m : ℕ} {A : ℝ}
    (hC : ∀ u : ℝ, A < u → ContDiffAt ℝ m f u) :
    ContinuousOn (iteratedDeriv m f) (Set.Ioi A) := by
  have hCD : ContDiffOn ℝ m f (Set.Ioi A) := fun u hu =>
    (hC u hu).contDiffWithinAt
  have hEqOn : Set.EqOn (iteratedDerivWithin m f (Set.Ioi A))
      (iteratedDeriv m f) (Set.Ioi A) :=
    iteratedDerivWithin_of_isOpen isOpen_Ioi
  exact (hCD.continuousOn_iteratedDerivWithin le_rfl
    isOpen_Ioi.uniqueDiffOn).congr hEqOn.symm

private lemma differentiableAt_iteratedDeriv_tail {f : ℝ → ℝ} {m : ℕ} {A : ℝ}
    (hC : ∀ u : ℝ, A < u → ContDiffAt ℝ (m + 1) f u) {x : ℝ} (hx : A < x) :
    DifferentiableAt ℝ (iteratedDeriv m f) x := by
  have hCD : ContDiffOn ℝ (m + 1) f (Set.Ioi A) := fun u hu =>
    (hC u hu).contDiffWithinAt
  have hLT : ((m : ℕ) : WithTop ℕ∞) < ((m + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self m
  have hdiffW := hCD.differentiableOn_iteratedDerivWithin hLT
    isOpen_Ioi.uniqueDiffOn
  have hEqOn : Set.EqOn (iteratedDerivWithin m f (Set.Ioi A))
      (iteratedDeriv m f) (Set.Ioi A) :=
    iteratedDerivWithin_of_isOpen isOpen_Ioi
  have hx' : x ∈ Set.Ioi A := hx
  have h1 : DifferentiableWithinAt ℝ (iteratedDeriv m f) (Set.Ioi A) x :=
    (hdiffW x hx').congr (fun v hv => (hEqOn hv).symm) (hEqOn hx').symm
  exact h1.differentiableAt (isOpen_Ioi.mem_nhds hx')

private lemma hasDerivAt_iteratedDeriv_tail {f : ℝ → ℝ} {m : ℕ} {A : ℝ}
    (hC : ∀ u : ℝ, A < u → ContDiffAt ℝ (m + 1) f u) {x : ℝ} (hx : A < x) :
    HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
  have h := (differentiableAt_iteratedDeriv_tail hC hx).hasDerivAt
  rwa [show deriv (iteratedDeriv m f) x = iteratedDeriv (m + 1) f x from
    congrArg (· x) iteratedDeriv_succ.symm] at h

/-- Mean value theorem for `iteratedDeriv m f` on an interval inside the
smooth tail: the increment is `(y − x)` times a value of the next
derivative at an interior point. -/
private lemma exists_iteratedDeriv_slope {f : ℝ → ℝ} {m : ℕ} {A : ℝ}
    (hC : ∀ u : ℝ, A < u → ContDiffAt ℝ (m + 1) f u)
    {x y : ℝ} (hAx : A < x) (hxy : x < y) :
    ∃ ξ ∈ Set.Ioo x y,
      iteratedDeriv m f y - iteratedDeriv m f x
        = (y - x) * iteratedDeriv (m + 1) f ξ := by
  have hcont : ContinuousOn (iteratedDeriv m f) (Set.Icc x y) := by
    have hlow : ((m : ℕ) : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_succ m
    have hcont' := continuousOn_iteratedDeriv_tail (m := m) (A := A)
      (fun u hu => (hC u hu).of_le hlow)
    exact hcont'.mono fun u hu => lt_of_lt_of_le hAx hu.1
  have hderiv : ∀ t ∈ Set.Ioo x y,
      HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f t) t :=
    fun t ht => hasDerivAt_iteratedDeriv_tail hC (lt_trans hAx ht.1)
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope (iteratedDeriv m f) (iteratedDeriv (m + 1) f)
      hxy hcont hderiv
  refine ⟨ξ, hξ, ?_⟩
  rw [hslope]
  have hne : y - x ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  field_simp

/-! ## §5  The master lemma: sign-normalized higher-derivative criterion

Induction on the derivative order `l ≥ 1`.  The base case is Fejér's theorem
(K–N Corollary 2.1), transferred to the difference sequence by the mean value
theorem; the inductive step feeds the shifted differences
`g u = f (u + h) − f u` to van der Corput's difference theorem. -/

/-- Sign-normalized master lemma: if `f` is eventually `C^l`, its `l`-th
derivative is eventually positive, antitone on a tail, tends to `0`, and
`u · f^(l)(u) → ∞`, then `(f n)ₙ` is uniformly distributed mod one. -/
theorem isUDModOne_of_iteratedDeriv_pos_antitone (l : ℕ) (hl : 1 ≤ l)
    (f : ℝ → ℝ)
    (hC : ∀ᶠ u : ℝ in atTop, ContDiffAt ℝ l f u)
    (hpos : ∀ᶠ u : ℝ in atTop, 0 < iteratedDeriv l f u)
    (hanti : ∃ x₀ : ℝ, AntitoneOn (iteratedDeriv l f) (Set.Ici x₀))
    (h0 : Tendsto (iteratedDeriv l f) atTop (𝓝 0))
    (hInf : Tendsto (fun u : ℝ => u * iteratedDeriv l f u) atTop atTop) :
    IsUDModOne fun k : ℕ => f k := by
  induction l, hl using Nat.le_induction generalizing f with
  | base =>
    -- ### Base case `l = 1`: Fejér's theorem via the mean value theorem.
    obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp hC
    obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp hpos
    obtain ⟨x₀, hx₀⟩ := hanti
    set A : ℝ := max (max A₁ A₂) x₀ with hA_def
    have hAA₁ : A₁ ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
    have hAA₂ : A₂ ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
    have hAx₀ : x₀ ≤ A := le_max_right _ _
    have hC' : ∀ u : ℝ, A < u → ContDiffAt ℝ 1 f u := fun u hu =>
      hA₁ u (le_of_lt (lt_of_le_of_lt hAA₁ hu))
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt A
    set b : ℕ → ℝ := fun n => f ((n + n₀ : ℕ) : ℝ) with hb_def
    have hcast : ∀ n : ℕ, ((n + 1 + n₀ : ℕ) : ℝ) = ((n + n₀ : ℕ) : ℝ) + 1 := by
      intro n; push_cast; ring
    have hcA : ∀ n : ℕ, A < ((n + n₀ : ℕ) : ℝ) := by
      intro n
      have h1 : (n₀ : ℝ) ≤ ((n + n₀ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_left n₀ n
      linarith
    have hc_mem : ∀ n : ℕ, ((n + n₀ : ℕ) : ℝ) ∈ Set.Ici x₀ := fun n =>
      Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt hAx₀ (hcA n)))
    -- Mean value theorem on each unit interval `[n + n₀, n + n₀ + 1]`.
    have hMVT : ∀ n : ℕ,
        ∃ ξ ∈ Set.Ioo (((n + n₀ : ℕ) : ℝ)) (((n + n₀ : ℕ) : ℝ) + 1),
          b (n + 1) - b n = iteratedDeriv 1 f ξ := by
      intro n
      obtain ⟨ξ, hξ, heq⟩ := exists_iteratedDeriv_slope (m := 0) hC'
        (hcA n) (lt_add_one (((n + n₀ : ℕ) : ℝ)))
      refine ⟨ξ, hξ, ?_⟩
      simp only [iteratedDeriv_zero, zero_add, add_sub_cancel_left,
        one_mul] at heq
      simp only [hb_def]
      rw [hcast n]
      exact heq
    choose ξ hξ hξval using hMVT
    have hξ_gtA : ∀ n, A < ξ n := fun n => lt_trans (hcA n) (hξ n).1
    have hξ_mem : ∀ n, ξ n ∈ Set.Ici x₀ := fun n =>
      Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt hAx₀ (hξ_gtA n)))
    have hξ_pos_val : ∀ n, 0 < iteratedDeriv 1 f (ξ n) := fun n =>
      hA₂ _ (le_of_lt (lt_of_le_of_lt hAA₂ (hξ_gtA n)))
    -- The four hypotheses of the discrete Fejér theorem.
    have hbpos : ∀ n : ℕ, 0 < b (n + 1) - b n := fun n => by
      rw [hξval n]; exact hξ_pos_val n
    have hbanti : ∀ m n : ℕ, m ≤ n → b (n + 1) - b n ≤ b (m + 1) - b m := by
      intro m n hmn
      rcases eq_or_lt_of_le hmn with rfl | hlt
      · exact le_rfl
      · rw [hξval m, hξval n]
        refine hx₀ (hξ_mem m) (hξ_mem n) ?_
        have h1 : ξ m < ((m + n₀ : ℕ) : ℝ) + 1 := (hξ m).2
        have h2 : ((m + n₀ : ℕ) : ℝ) + 1 ≤ ((n + n₀ : ℕ) : ℝ) := by
          have h3 : ((m + n₀ + 1 : ℕ) : ℝ) ≤ ((n + n₀ : ℕ) : ℝ) :=
            Nat.cast_le.mpr (by omega)
          push_cast at h3 ⊢
          linarith
        have h4 : ((n + n₀ : ℕ) : ℝ) < ξ n := (hξ n).1
        linarith
    have hcN : Tendsto (fun n : ℕ => ((n + n₀ : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n₀)
    have hb0 : Tendsto (fun n : ℕ => b (n + 1) - b n) atTop (𝓝 0) := by
      have hupper : Tendsto
          (fun n : ℕ => iteratedDeriv 1 f (((n + n₀ : ℕ) : ℝ)))
          atTop (𝓝 0) := h0.comp hcN
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper (fun n => (hbpos n).le) fun n => ?_
      rw [hξval n]
      exact hx₀ (hc_mem n) (hξ_mem n) (hξ n).1.le
    have hbInf : Tendsto (fun n : ℕ => (n : ℝ) * (b (n + 1) - b n))
        atTop atTop := by
      have hcN1 : Tendsto (fun n : ℕ => ((n + n₀ : ℕ) : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 hcN
      have hX : Tendsto (fun n : ℕ =>
          (((n + n₀ : ℕ) : ℝ) + 1)
            * iteratedDeriv 1 f (((n + n₀ : ℕ) : ℝ) + 1)) atTop atTop :=
        hInf.comp hcN1
      refine tendsto_atTop_mono' atTop ?_ (hX.atTop_div_const two_pos)
      filter_upwards [eventually_ge_atTop (n₀ + 1)] with n hn
      rw [hξval n]
      have hc1_mem : ((n + n₀ : ℕ) : ℝ) + 1 ∈ Set.Ici x₀ :=
        Set.mem_Ici.mpr (by
          have := hc_mem n
          rw [Set.mem_Ici] at this
          linarith)
      have h1 : iteratedDeriv 1 f (((n + n₀ : ℕ) : ℝ) + 1)
          ≤ iteratedDeriv 1 f (ξ n) :=
        hx₀ (hξ_mem n) hc1_mem (hξ n).2.le
      have h2 : 0 < iteratedDeriv 1 f (((n + n₀ : ℕ) : ℝ) + 1) :=
        hA₂ _ (by have := hcA n; linarith)
      have h3 : ((n + n₀ : ℕ) : ℝ) + 1 ≤ 2 * (n : ℝ) := by
        have h5 : (n₀ + 1 : ℕ) ≤ n := hn
        have h6 : ((n₀ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h5
        push_cast at h6 ⊢
        linarith
      have h7 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h8 : 0 ≤ (2 * (n : ℝ) - (((n + n₀ : ℕ) : ℝ) + 1))
          * iteratedDeriv 1 f (((n + n₀ : ℕ) : ℝ) + 1) :=
        mul_nonneg (by linarith) h2.le
      have h9 : 0 ≤ (n : ℝ) * (iteratedDeriv 1 f (ξ n)
          - iteratedDeriv 1 f (((n + n₀ : ℕ) : ℝ) + 1)) :=
        mul_nonneg h7 (by linarith)
      nlinarith [h8, h9]
    have hb_ud : IsUDModOne b :=
      isUDModOne_of_antitone_diff hbpos hbanti hb0 hbInf
    exact isUDModOne_of_shift n₀ hb_ud
  | succ l hl ih =>
    -- ### Inductive step: reduce level `l + 1` to level `l` via the
    -- difference theorem.
    obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp hC
    obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp hpos
    obtain ⟨x₀, hx₀⟩ := hanti
    set A : ℝ := max (max A₁ A₂) x₀ with hA_def
    have hAA₁ : A₁ ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
    have hAA₂ : A₂ ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
    have hAx₀ : x₀ ≤ A := le_max_right _ _
    have hC' : ∀ u : ℝ, A < u → ContDiffAt ℝ (l + 1 : ℕ) f u := fun u hu =>
      hA₁ u (le_of_lt (lt_of_le_of_lt hAA₁ hu))
    apply isUDModOne_of_forall_diff
    intro h hh
    have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    have hh0 : (0 : ℝ) < (h : ℝ) := lt_of_lt_of_le one_pos hh1
    set g : ℝ → ℝ := fun u => f (u + (h : ℝ)) - f u with hg_def
    -- Smoothness of the shifted difference on the tail.
    have htrans : ∀ u : ℝ, A < u →
        ContDiffAt ℝ (l + 1 : ℕ) (fun x : ℝ => f (x + (h : ℝ))) u := by
      intro u hu
      have hfu : ContDiffAt ℝ (l + 1 : ℕ) f (u + (h : ℝ)) :=
        hC' (u + (h : ℝ)) (by linarith)
      have hinner : ContDiffAt ℝ (l + 1 : ℕ) (fun x : ℝ => x + (h : ℝ)) u :=
        contDiffAt_id.add contDiffAt_const
      exact ContDiffAt.comp (g := f) (f := fun x : ℝ => x + (h : ℝ)) u
        hfu hinner
    have hgC : ∀ u : ℝ, A < u → ContDiffAt ℝ (l + 1 : ℕ) g u := fun u hu =>
      (htrans u hu).sub (hC' u hu)
    -- Iterated derivatives of `g` on the tail.
    have hgd : ∀ m : ℕ, m ≤ l + 1 → ∀ u : ℝ, A < u →
        iteratedDeriv m g u
          = iteratedDeriv m f (u + (h : ℝ)) - iteratedDeriv m f u := by
      intro m hm u hu
      have hmcast : ((m : ℕ) : WithTop ℕ∞) ≤ ((l + 1 : ℕ) : WithTop ℕ∞) := by
        exact_mod_cast hm
      have h1 : ContDiffAt ℝ m (fun x : ℝ => f (x + (h : ℝ))) u :=
        (htrans u hu).of_le hmcast
      have h2 : ContDiffAt ℝ m f u := (hC' u hu).of_le hmcast
      have hshift : iteratedDeriv m (fun x : ℝ => f (x + (h : ℝ))) u
          = iteratedDeriv m f (u + (h : ℝ)) :=
        congrFun (iteratedDeriv_comp_add_const m f ((h : ℝ))) u
      calc iteratedDeriv m g u
          = iteratedDeriv m ((fun x : ℝ => f (x + (h : ℝ))) - f) u := rfl
        _ = iteratedDeriv m (fun x : ℝ => f (x + (h : ℝ))) u
              - iteratedDeriv m f u := iteratedDeriv_sub h1 h2
        _ = _ := by rw [hshift]
    -- Level-`l` hypotheses for `g`.
    have hgC_l : ∀ᶠ u : ℝ in atTop, ContDiffAt ℝ l g u := by
      filter_upwards [eventually_gt_atTop A] with u hu
      exact (hgC u hu).of_le (by exact_mod_cast Nat.le_succ l)
    have hgpos : ∀ᶠ u : ℝ in atTop, 0 < iteratedDeriv l g u := by
      filter_upwards [eventually_gt_atTop A] with u hu
      obtain ⟨ξ, hξ, heq⟩ := exists_iteratedDeriv_slope (m := l) hC' hu
        (by linarith : u < u + (h : ℝ))
      rw [hgd l (Nat.le_succ l) u hu, heq]
      have hξA : A < ξ := lt_trans hu hξ.1
      exact mul_pos (by linarith [hξ.1, hξ.2])
        (hA₂ ξ (le_of_lt (lt_of_le_of_lt hAA₂ hξA)))
    have hganti : ∃ x₁ : ℝ, AntitoneOn (iteratedDeriv l g) (Set.Ici x₁) := by
      refine ⟨A + 1, ?_⟩
      have hcont : ContinuousOn (iteratedDeriv l g) (Set.Ici (A + 1)) := by
        have hcont' := continuousOn_iteratedDeriv_tail (m := l) (A := A)
          (fun u hu => (hgC u hu).of_le (by exact_mod_cast Nat.le_succ l))
        exact hcont'.mono fun u hu => by
          have : A + 1 ≤ u := hu
          exact Set.mem_Ioi.mpr (by linarith)
      have hdiff : DifferentiableOn ℝ (iteratedDeriv l g)
          (interior (Set.Ici (A + 1))) := by
        rw [interior_Ici]
        intro u hu
        have huA : A < u := by
          have : A + 1 < u := hu
          linarith
        exact (differentiableAt_iteratedDeriv_tail (m := l) hgC
          huA).differentiableWithinAt
      refine antitoneOn_of_deriv_nonpos (convex_Ici _) hcont hdiff ?_
      intro u hu
      rw [interior_Ici] at hu
      have huA : A < u := by
        have : A + 1 < u := hu
        linarith
      rw [show deriv (iteratedDeriv l g) u = iteratedDeriv (l + 1) g u from
        congrArg (· u) iteratedDeriv_succ.symm]
      rw [hgd (l + 1) le_rfl u huA]
      have humem : u ∈ Set.Ici x₀ :=
        Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt hAx₀ huA))
      have huhmem : u + (h : ℝ) ∈ Set.Ici x₀ :=
        Set.mem_Ici.mpr (by
          have := le_of_lt (lt_of_le_of_lt hAx₀ huA)
          linarith)
      have h1 : iteratedDeriv (l + 1) f (u + (h : ℝ))
          ≤ iteratedDeriv (l + 1) f u :=
        hx₀ humem huhmem (by linarith)
      linarith
    have hg0 : Tendsto (iteratedDeriv l g) atTop (𝓝 0) := by
      have hupperlim : Tendsto
          (fun u : ℝ => (h : ℝ) * iteratedDeriv (l + 1) f u) atTop (𝓝 0) := by
        have := h0.const_mul ((h : ℝ))
        rwa [mul_zero] at this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hupperlim
        (hgpos.mono fun u hu => hu.le) ?_
      filter_upwards [eventually_gt_atTop A] with u hu
      obtain ⟨ξ, hξ, heq⟩ := exists_iteratedDeriv_slope (m := l) hC' hu
        (by linarith : u < u + (h : ℝ))
      rw [hgd l (Nat.le_succ l) u hu, heq]
      have humem : u ∈ Set.Ici x₀ :=
        Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt hAx₀ hu))
      have hξmem : ξ ∈ Set.Ici x₀ :=
        Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt hAx₀ (lt_trans hu hξ.1)))
      have h1 : iteratedDeriv (l + 1) f ξ ≤ iteratedDeriv (l + 1) f u :=
        hx₀ humem hξmem hξ.1.le
      have h2 : u + (h : ℝ) - u = (h : ℝ) := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 (by linarith)
    have hgInf : Tendsto (fun u : ℝ => u * iteratedDeriv l g u)
        atTop atTop := by
      have hX : Tendsto (fun u : ℝ =>
          (u + (h : ℝ)) * iteratedDeriv (l + 1) f (u + (h : ℝ)))
          atTop atTop :=
        hInf.comp (tendsto_atTop_add_const_right _ ((h : ℝ)) tendsto_id)
      refine tendsto_atTop_mono' atTop ?_ (hX.atTop_div_const two_pos)
      filter_upwards [eventually_gt_atTop A, eventually_ge_atTop ((h : ℝ)),
        eventually_gt_atTop (0 : ℝ)] with u hu huh hu0
      obtain ⟨ξ, hξ, heq⟩ := exists_iteratedDeriv_slope (m := l) hC' hu
        (by linarith : u < u + (h : ℝ))
      rw [hgd l (Nat.le_succ l) u hu, heq]
      have hξmem : ξ ∈ Set.Ici x₀ :=
        Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt hAx₀ (lt_trans hu hξ.1)))
      have huhmem : u + (h : ℝ) ∈ Set.Ici x₀ :=
        Set.mem_Ici.mpr (by
          have := le_of_lt (lt_of_le_of_lt hAx₀ hu)
          linarith)
      have h1 : iteratedDeriv (l + 1) f (u + (h : ℝ))
          ≤ iteratedDeriv (l + 1) f ξ :=
        hx₀ hξmem huhmem hξ.2.le
      have h2 : 0 < iteratedDeriv (l + 1) f (u + (h : ℝ)) :=
        hA₂ _ (by have := lt_of_le_of_lt hAA₂ hu; linarith)
      have h3 : u + (h : ℝ) - u = (h : ℝ) := by ring
      rw [h3]
      -- `(u + h) · F'(u + h) / 2  ≤  u · (h · F'(ξ))`
      have h4 : 0 ≤ (2 * u - (u + (h : ℝ)))
          * iteratedDeriv (l + 1) f (u + (h : ℝ)) :=
        mul_nonneg (by linarith) h2.le
      have h5 : 0 ≤ u * (((h : ℝ)) * (iteratedDeriv (l + 1) f ξ
          - iteratedDeriv (l + 1) f (u + (h : ℝ)))) :=
        mul_nonneg hu0.le (mul_nonneg (by linarith) (by linarith))
      have h6 : 0 ≤ u * (((h : ℝ) - 1)
          * iteratedDeriv (l + 1) f (u + (h : ℝ))) :=
        mul_nonneg hu0.le (mul_nonneg (by linarith) h2.le)
      nlinarith [h4, h5, h6]
    -- Apply the inductive hypothesis to `g` and convert.
    have hg_ud : IsUDModOne fun k : ℕ => g k :=
      ih g hgC_l hgpos hganti hg0 hgInf
    refine isUDModOne_congr_eventually
      (Eventually.of_forall fun n => ?_) hg_ud
    simp only [hg_def]
    push_cast
    ring

/-! ## §6  The higher-derivative Kuipers–Niederreiter / Fejér criterion

The sign-free form consumed by `Theorem4.lean`: eventual nonvanishing (from
`u·|f^(l)(u)| → ∞`) together with continuity of `f^(l)` on the tail forces an
eventually constant sign, and the master lemma applies to `f` or `−f`. -/

/-- **Higher-derivative Kuipers–Niederreiter / Fejér criterion**
(Kuipers–Niederreiter Theorem 2.5 with the higher-derivative extension used
by Pańkowski): if `f` is eventually `C^l` (`l ≥ 1`), `|f^(l)|` is antitone on
a tail, `f^(l) → 0`, and `u · |f^(l)(u)| → ∞`, then the integer-sampled
sequence `(f k)ₖ` is uniformly distributed modulo one. -/
theorem isUDModOne_of_iteratedDeriv_decay
    (f : ℝ → ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hC : ∀ᶠ u : ℝ in atTop, ContDiffAt ℝ l f u)
    (hmono : ∃ x₀ : ℝ,
        AntitoneOn (fun t : ℝ => |iteratedDeriv l f t|) (Set.Ici x₀))
    (h0 : Tendsto (fun u : ℝ => iteratedDeriv l f u) atTop (𝓝 0))
    (hInf : Tendsto (fun u : ℝ => u * |iteratedDeriv l f u|) atTop atTop) :
    IsUDModOne (fun k : ℕ => f k) := by
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp hC
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp (hInf.eventually_ge_atTop 1)
  obtain ⟨x₀, hx₀⟩ := hmono
  set B : ℝ := max (max A₁ A₂) x₀ with hB_def
  have hBA₁ : A₁ ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
  have hBA₂ : A₂ ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
  have hBx₀ : x₀ ≤ B := le_max_right _ _
  -- `f^(l)` never vanishes past `B`.
  have hne : ∀ u ∈ Set.Ioi B, iteratedDeriv l f u ≠ 0 := by
    intro u hu hzero
    have h1 := hA₂ u (le_of_lt (lt_of_le_of_lt hBA₂ hu))
    rw [hzero, abs_zero, mul_zero] at h1
    linarith
  -- `f^(l)` is continuous past `B`.
  have hcont : ContinuousOn (iteratedDeriv l f) (Set.Ioi B) := by
    have h := continuousOn_iteratedDeriv_tail (m := l) (A := A₁)
      (fun u hu => hA₁ u hu.le)
    exact h.mono fun u hu => lt_of_le_of_lt hBA₁ hu
  -- Constant sign on `(B, ∞)`, by the intermediate value theorem.
  have hdichot : (∀ u ∈ Set.Ioi B, 0 < iteratedDeriv l f u)
      ∨ (∀ u ∈ Set.Ioi B, iteratedDeriv l f u < 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨u₁, hu₁, hu₁'⟩, ⟨u₂, hu₂, hu₂'⟩⟩ := hcon
    have hF1 : iteratedDeriv l f u₁ ≤ 0 := hu₁'
    have hF2 : 0 ≤ iteratedDeriv l f u₂ := hu₂'
    rcases le_total u₁ u₂ with hle | hle
    · have hsub : Set.Icc u₁ u₂ ⊆ Set.Ioi B := fun v hv =>
        lt_of_lt_of_le hu₁ hv.1
      obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc hle (hcont.mono hsub)
        (Set.mem_Icc.mpr ⟨hF1, hF2⟩)
      exact hne v (hsub hv) hv0
    · have hsub : Set.Icc u₂ u₁ ⊆ Set.Ioi B := fun v hv =>
        lt_of_lt_of_le hu₂ hv.1
      obtain ⟨v, hv, hv0⟩ := intermediate_value_Icc' hle (hcont.mono hsub)
        (Set.mem_Icc.mpr ⟨hF1, hF2⟩)
      exact hne v (hsub hv) hv0
  rcases hdichot with hdpos | hdneg
  · -- Positive case: apply the master lemma to `f` itself.
    have hpos' : ∀ᶠ u : ℝ in atTop, 0 < iteratedDeriv l f u := by
      filter_upwards [eventually_gt_atTop B] with u hu
      exact hdpos u hu
    have hanti' : ∃ x₁ : ℝ,
        AntitoneOn (iteratedDeriv l f) (Set.Ici x₁) := by
      refine ⟨B + 1, ?_⟩
      have hsub : Set.Ici (B + 1) ⊆ Set.Ici x₀ := fun v hv => by
        have : B + 1 ≤ v := hv
        exact Set.mem_Ici.mpr (by linarith)
      refine (hx₀.mono hsub).congr fun v hv => ?_
      have hvB : B < v := by
        have : B + 1 ≤ v := hv
        linarith
      exact abs_of_pos (hdpos v hvB)
    have hInf' : Tendsto (fun u : ℝ => u * iteratedDeriv l f u)
        atTop atTop := by
      refine hInf.congr' ?_
      filter_upwards [eventually_gt_atTop B] with u hu
      rw [abs_of_pos (hdpos u hu)]
    exact isUDModOne_of_iteratedDeriv_pos_antitone l hl f hC hpos' hanti'
      h0 hInf'
  · -- Negative case: apply the master lemma to `−f` and negate back.
    have hCneg : ∀ᶠ u : ℝ in atTop,
        ContDiffAt ℝ l (fun x : ℝ => -(f x)) u :=
      hC.mono fun u hu => hu.neg
    have hposneg : ∀ᶠ u : ℝ in atTop,
        0 < iteratedDeriv l (fun x : ℝ => -(f x)) u := by
      filter_upwards [eventually_gt_atTop B] with u hu
      rw [iteratedDeriv_fun_neg]
      linarith [hdneg u hu]
    have hantineg : ∃ x₁ : ℝ,
        AntitoneOn (iteratedDeriv l (fun x : ℝ => -(f x))) (Set.Ici x₁) := by
      refine ⟨B + 1, ?_⟩
      have hsub : Set.Ici (B + 1) ⊆ Set.Ici x₀ := fun v hv => by
        have : B + 1 ≤ v := hv
        exact Set.mem_Ici.mpr (by linarith)
      refine (hx₀.mono hsub).congr fun v hv => ?_
      have hvB : B < v := by
        have : B + 1 ≤ v := hv
        linarith
      rw [iteratedDeriv_fun_neg]
      exact abs_of_neg (hdneg v hvB)
    have h0neg : Tendsto (iteratedDeriv l (fun x : ℝ => -(f x)))
        atTop (𝓝 0) := by
      have h := h0.neg
      rw [neg_zero] at h
      exact h.congr fun u => (iteratedDeriv_fun_neg l f u).symm
    have hInfneg : Tendsto
        (fun u : ℝ => u * iteratedDeriv l (fun x : ℝ => -(f x)) u)
        atTop atTop := by
      refine hInf.congr' ?_
      filter_upwards [eventually_gt_atTop B] with u hu
      rw [iteratedDeriv_fun_neg, abs_of_neg (hdneg u hu)]
    have hUDneg : IsUDModOne fun k : ℕ => -(f k) :=
      isUDModOne_of_iteratedDeriv_pos_antitone l hl (fun x : ℝ => -(f x))
        hCneg hposneg hantineg h0neg hInfneg
    refine isUDModOne_congr_eventually
      (Eventually.of_forall fun n => ?_) hUDneg.neg
    exact neg_neg _

end Gram.UD
