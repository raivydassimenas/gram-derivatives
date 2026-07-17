import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniform distribution modulo one

Concrete Weyl-criterion definitions of *uniform distribution modulo one* for
real sequences and real functions, expressed via Fourier exponentials
`exp(2πi · k · ·)` so that the reduction modulo `1` is built in through the
periodicity of the complex exponential.

These replace the opaque `Prop` wrappers previously used in
`GramDerivatives.Corollary5`. The one deep analytic theorem consumed
downstream (derivative-decay ⇒ UD, the discrete Fejér criterion) remains an
`-- ASSUMPTION` axiom in `Theorem4.lean`; this file itself is axiom-free —
the definitions of UD/CUD are honest, and both the index-shift lemma
`IsUDModOne.shift` and the Kuipers–Niederreiter discrete-to-continuous
bridge `isCUDModOne_of_forall_shift` (K–N Theorem 9.6(a)) are proved.
-/

open scoped Real Topology BigOperators
open Filter

namespace Gram.UD

/-- A real sequence `a : ℕ → ℝ` is **uniformly distributed modulo one** iff for
every nonzero integer `k` the Cesàro averages of the Weyl exponentials
`exp(2πi · k · aₙ)` tend to zero. This is the Fourier-side formulation of
classical equidistribution. -/
def IsUDModOne (a : ℕ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    Tendsto
      (fun N : ℕ =>
        (1 / (N : ℂ)) *
          ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)))
      atTop (nhds 0)

/-- A real function `f : ℝ → ℝ` is **continuously uniformly distributed modulo
one** iff for every nonzero integer `k` the time averages of the Weyl
exponentials `exp(2πi · k · f(t))` over `[0, T]` tend to zero as `T → ∞`. -/
noncomputable def IsCUDModOne (f : ℝ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    Tendsto
      (fun T : ℝ =>
        (1 / (T : ℂ)) *
          ∫ t in (0 : ℝ)..T,
            Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (f t : ℂ)))
      atTop (nhds 0)

/-- Shifting the index of a UD-mod-1 sequence by one preserves UD-mod-1.

The shifted Cesàro average
`(1/N) ∑ n<N, exp(2πi·k·a(n+1))` differs from
`(1/N) ∑ n<N, exp(2πi·k·a(n))` by `(1/N)·(exp(2πi·k·a(N)) - exp(2πi·k·a(0)))`,
which is bounded by `2/N` and hence vanishes; both averages then share the
same limit. -/
theorem IsUDModOne.shift {a : ℕ → ℝ} (h : IsUDModOne a) :
    IsUDModOne (fun k => a (k + 1)) := by
  intro k hk
  set e : ℕ → ℂ := fun n =>
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)) with he
  have hnorm : ∀ n, ‖e n‖ = 1 := by
    intro n
    simp [he, Complex.norm_exp]
  -- The shifted partial sum telescopes against the unshifted one.
  have hsum : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, e (n + 1))
        = (∑ n ∈ Finset.range N, e n) + e N - e 0 := by
    intro N
    have h1 := Finset.sum_range_succ' e N
    have h2 := Finset.sum_range_succ e N
    linear_combination h2 - h1
  -- The boundary term `(1/N)·(e N - e 0)` vanishes at infinity.
  have herr :
      Tendsto (fun N : ℕ => (1 / (N : ℂ)) * (e N - e 0)) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun N => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat 2)
    calc ‖(1 / (N : ℂ)) * (e N - e 0)‖
        = 1 / (N : ℝ) * ‖e N - e 0‖ := by
          rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      _ ≤ 1 / (N : ℝ) * 2 := by
          have : ‖e N - e 0‖ ≤ 2 := by
            calc ‖e N - e 0‖ ≤ ‖e N‖ + ‖e 0‖ := norm_sub_le _ _
              _ = 2 := by rw [hnorm, hnorm]; norm_num
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 / (N : ℝ) := by ring
  -- Stitch: shifted average = unshifted average + boundary term.
  have hlim := (h k hk).add herr
  rw [add_zero] at hlim
  refine hlim.congr fun N => ?_
  change (1 / (N : ℂ)) * (∑ n ∈ Finset.range N, e n)
        + (1 / (N : ℂ)) * (e N - e 0)
      = (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, e (n + 1)
  rw [hsum N]; ring

/-- **Kuipers–Niederreiter, Theorem 9.6(a)** (Ryll-Nardzewski): if for every
shift `t ∈ [0, 1]` the integer-sampled sequence `(f(k + t))ₖ` is uniformly
distributed modulo one, and `f` is measurable, then `f` is *continuously*
uniformly distributed modulo one.

(The classical statement only requires the hypothesis for *almost all*
`t ∈ [0, 1]`; the all-`t` form assumed here is what our application provides,
and it keeps the statement free of measure-theoretic quantifiers.)

Proof, for a fixed nonzero frequency `k` with Weyl exponential
`g = exp(2πik·f(·))`:
1. `∫₀ᴺ g = ∑_{n<N} ∫₀¹ g(n+t) dt` by splicing adjacent unit intervals, so the
   integer-cutoff time average `(1/N)·∫₀ᴺ g` is the `[0,1]`-integral of the
   Cesàro averages `(1/N)·∑_{n<N} g(n+t)`.
2. Those Cesàro averages tend to `0` pointwise in `t` (the UD hypothesis) and
   are uniformly bounded by `1`, so the dominated convergence theorem gives
   `(1/N)·∫₀ᴺ g → 0` along `ℕ`.
3. For real `T → ∞`, cut at `N = ⌊T⌋₊`: the leftover `∫_N^T g` has norm at
   most `T − N ≤ 1`, so the full average is squeezed by
   `‖(1/N)·∫₀ᴺ g‖ + 1/T → 0`. -/
theorem isCUDModOne_of_forall_shift {f : ℝ → ℝ} (hf : Measurable f)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUDModOne fun k : ℕ => f (k + t)) :
    IsCUDModOne f := by
  intro k hk
  set g : ℝ → ℂ := fun u =>
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (f u : ℂ)) with hg
  have hg_meas : Measurable g :=
    Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp hf))
  have hg_norm : ∀ u, ‖g u‖ = 1 := by
    intro u
    simp [hg, Complex.norm_exp]
  -- Any measurable function of norm `1` is interval integrable.
  have hint_aux : ∀ (φ : ℝ → ℂ), Measurable φ → (∀ u, ‖φ u‖ = 1) →
      ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b := by
    intro φ hφ hφn a b
    rw [intervalIntegrable_iff]
    have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Set.uIoc a b) MeasureTheory.volume :=
      MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
    exact hconst.mono' (hφ.aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun u => (hφn u).le)
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b :=
    hint_aux g hg_meas hg_norm
  -- Step 1: the integer-cutoff average is the `[0,1]`-integral of the Cesàro
  -- averages of the shifted sequences.
  have key : ∀ N : ℕ,
      (∫ t in (0 : ℝ)..1,
        (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g ((n : ℝ) + t))
        = (1 / (N : ℂ)) * ∫ u in (0 : ℝ)..(N : ℝ), g u := by
    intro N
    rw [show (∫ t in (0 : ℝ)..1,
          (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g ((n : ℝ) + t))
        = (1 / (N : ℂ)) *
            ∫ t in (0 : ℝ)..1, ∑ n ∈ Finset.range N, g ((n : ℝ) + t) from
      intervalIntegral.integral_const_mul _ _]
    congr 1
    rw [show (∫ t in (0 : ℝ)..1, ∑ n ∈ Finset.range N, g ((n : ℝ) + t))
        = ∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..1, g ((n : ℝ) + t) from
      intervalIntegral.integral_finset_sum
        (f := fun (n : ℕ) (t : ℝ) => g ((n : ℝ) + t))
        (fun n _ => hint_aux (fun t => g ((n : ℝ) + t))
          (hg_meas.comp (measurable_const_add ((n : ℝ))))
          (fun u => hg_norm _) 0 1)]
    have hpiece : ∀ n ∈ Finset.range N,
        (∫ t in (0 : ℝ)..1, g ((n : ℝ) + t))
          = ∫ u in ((n : ℕ) : ℝ)..(((n + 1 : ℕ) : ℝ)), g u := by
      intro n _
      rw [intervalIntegral.integral_comp_add_left g ((n : ℝ))]
      norm_num
    rw [Finset.sum_congr rfl hpiece,
      intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ => hg_int (i : ℝ) ((i + 1 : ℕ) : ℝ))]
    norm_num
  -- Step 2: dominated convergence along integer cutoffs.
  have hDCT : Tendsto
      (fun N : ℕ => (1 / (N : ℂ)) * ∫ u in (0 : ℝ)..(N : ℝ), g u)
      atTop (nhds 0) := by
    have hconv := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1) (l := atTop)
      (F := fun N : ℕ => fun t : ℝ =>
        (1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g ((n : ℝ) + t))
      (f := fun _ : ℝ => (0 : ℂ)) (bound := fun _ : ℝ => (1 : ℝ))
      (Filter.Eventually.of_forall fun N =>
        ((measurable_const.mul
          (Finset.measurable_sum (Finset.range N) fun n _ =>
            hg_meas.comp (measurable_const_add ((n : ℝ))))).aestronglyMeasurable.restrict))
      (Filter.Eventually.of_forall fun N =>
        MeasureTheory.ae_of_all _ fun t _ => by
          calc ‖(1 / (N : ℂ)) * ∑ n ∈ Finset.range N, g ((n : ℝ) + t)‖
              = 1 / (N : ℝ) * ‖∑ n ∈ Finset.range N, g ((n : ℝ) + t)‖ := by
                rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
            _ ≤ 1 / (N : ℝ) * N := by
                gcongr
                refine (norm_sum_le _ _).trans ?_
                simp [hg_norm]
            _ ≤ 1 := by
                rcases Nat.eq_zero_or_pos N with h0 | h0
                · simp [h0]
                · have : (0 : ℝ) < N := by exact_mod_cast h0
                  rw [div_mul_eq_mul_div, one_mul, div_self this.ne']
      )
      intervalIntegrable_const
      (MeasureTheory.ae_of_all _ fun t ht => by
        have hmem : t ∈ Set.Icc (0 : ℝ) 1 := by
          rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
          exact ⟨ht.1.le, ht.2⟩
        exact h t hmem k hk)
    rw [intervalIntegral.integral_zero] at hconv
    exact hconv.congr key
  -- Step 3: squeeze the real-time average by the floor-cutoff average.
  have hfloor : Tendsto
      (fun T : ℝ =>
        ‖(1 / ((⌊T⌋₊ : ℕ) : ℂ)) * ∫ u in (0 : ℝ)..((⌊T⌋₊ : ℕ) : ℝ), g u‖)
      atTop (nhds 0) := by
    simpa using (hDCT.norm.comp (tendsto_nat_floor_atTop (α := ℝ)))
  have hbound : Tendsto
      (fun T : ℝ =>
        ‖(1 / ((⌊T⌋₊ : ℕ) : ℂ)) * ∫ u in (0 : ℝ)..((⌊T⌋₊ : ℕ) : ℝ), g u‖
          + 1 / T)
      atTop (nhds 0) := by
    have hinv : Tendsto (fun T : ℝ => 1 / T) atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero
    simpa using hfloor.add hinv
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  set N : ℕ := ⌊T⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hT)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNT : (N : ℝ) ≤ T := Nat.floor_le hT0.le
  have hTN1 : T - (N : ℝ) ≤ 1 := by
    have := (Nat.lt_floor_add_one T).le
    push_cast at this ⊢
    linarith
  have hsplit : (∫ t in (0 : ℝ)..T, g t)
      = (∫ t in (0 : ℝ)..(N : ℝ), g t) + ∫ t in (N : ℝ)..T, g t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hg_int 0 (N : ℝ)) (hg_int (N : ℝ) T)).symm
  have htail : ‖∫ t in (N : ℝ)..T, g t‖ ≤ 1 := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1) (a := (N : ℝ)) (b := T) (f := g)
      (fun x _ => (hg_norm x).le)
    have habs : |T - (N : ℝ)| = T - (N : ℝ) := abs_of_nonneg (by linarith)
    calc ‖∫ t in (N : ℝ)..T, g t‖ ≤ 1 * |T - (N : ℝ)| := hle
      _ = T - (N : ℝ) := by rw [one_mul, habs]
      _ ≤ 1 := hTN1
  calc ‖(1 / (T : ℂ)) * ∫ t in (0 : ℝ)..T,
          Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (f t : ℂ))‖
      = 1 / T * ‖∫ t in (0 : ℝ)..T, g t‖ := by
        rw [norm_mul, norm_div, norm_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hT0]
    _ ≤ 1 / T * (‖∫ t in (0 : ℝ)..(N : ℝ), g t‖ + ‖∫ t in (N : ℝ)..T, g t‖) := by
        gcongr
        rw [hsplit]
        exact norm_add_le _ _
    _ ≤ 1 / T * ‖∫ t in (0 : ℝ)..(N : ℝ), g t‖ + 1 / T * 1 := by
        rw [mul_add]
        gcongr
    _ ≤ 1 / (N : ℝ) * ‖∫ t in (0 : ℝ)..(N : ℝ), g t‖ + 1 / T := by
        rw [mul_one]
        gcongr
    _ = ‖(1 / ((N : ℕ) : ℂ)) * ∫ u in (0 : ℝ)..((N : ℕ) : ℝ), g u‖ + 1 / T := by
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]

end Gram.UD
