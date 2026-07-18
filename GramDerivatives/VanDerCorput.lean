import GramDerivatives.UDModOne
import Mathlib.Algebra.Order.Chebyshev

/-!
# Van der Corput's fundamental inequality and difference theorem

Formalization of two results from Kuipers–Niederreiter, *Uniform Distribution
of Sequences*, Chapter 1, §3:

* **Lemma 3.1** (van der Corput's fundamental inequality),
  `vdc_fundamental_inequality`: for complex numbers `u 0, …, u (N-1)` and
  `1 ≤ H`,

  ```
  (H·‖∑_{n<N} uₙ‖)² ≤ (N+H−1) · (H·∑_{n<N}‖uₙ‖²
                        + 2H·∑_{j<H−1} ‖∑_{n<N−(j+1)} u_{n+j+1}·conj(uₙ)‖).
  ```

  (We use the crude multiplicity bound `H` for the correlation term of gap
  `j+1` instead of the sharp `H−(j+1)`; this weakening is harmless for the
  difference theorem and simplifies the bookkeeping.)

* **Theorem 3.1** (van der Corput's difference theorem),
  `isUDModOne_of_forall_diff`: if for every `h ≥ 1` the difference sequence
  `(a(n+h) − a(n))ₙ` is uniformly distributed mod one, then so is `(a(n))ₙ`.

The proof of the inequality follows the book: extend `u` by zero, pad by
`H−1` at the front (`padded`), write `H·∑uₙ` as the sum of the sliding-window
sums `S q = ∑_{h<H} padded (q+h)`, apply Cauchy–Schwarz in the form
`(∑ᵢxᵢ)² ≤ #s·∑ᵢxᵢ²`, and expand the squares into diagonal and correlation
terms.

Also §1 records two elementary stability facts for `IsUDModOne` used
downstream: invariance under negation and under eventual (cofinite)
modification of the sequence.
-/

open Filter Finset
open scoped BigOperators

namespace Gram.UD

/-! ## §1  Elementary stability lemmas for `IsUDModOne` -/

/-- Negating a sequence preserves UD mod 1 (swap the frequency `k ↦ −k`). -/
theorem IsUDModOne.neg {a : ℕ → ℝ} (h : IsUDModOne a) :
    IsUDModOne fun n => -(a n) := by
  intro k hk
  refine (h (-k) (neg_ne_zero.mpr hk)).congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  push_cast
  ring

/-- Changing finitely many terms of a sequence preserves UD mod 1: the two
Cesàro averages differ by a fixed vector divided by `N`. -/
theorem isUDModOne_congr_eventually {a b : ℕ → ℝ}
    (hab : ∀ᶠ n in atTop, a n = b n) (h : IsUDModOne a) : IsUDModOne b := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hab
  intro k hk
  set ea : ℕ → ℂ := fun n =>
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)) with hea
  set eb : ℕ → ℂ := fun n =>
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (b n : ℂ)) with heb
  set D : ℂ := ∑ n ∈ Finset.range n₀, (eb n - ea n) with hD
  have hsum : ∀ N, n₀ ≤ N →
      ∑ n ∈ Finset.range N, eb n = (∑ n ∈ Finset.range N, ea n) + D := by
    intro N hN
    have hDN : ∑ n ∈ Finset.range N, (eb n - ea n) = D := by
      rw [hD]
      refine (Finset.sum_subset
        (fun x hx => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) hN)) ?_).symm
      intro n _ hnn
      have hn : n₀ ≤ n := le_of_not_gt fun hlt => hnn (Finset.mem_range.mpr hlt)
      simp [hea, heb, hn₀ n hn]
    calc ∑ n ∈ Finset.range N, eb n
        = ∑ n ∈ Finset.range N, (ea n + (eb n - ea n)) :=
          Finset.sum_congr rfl fun n _ => by ring
      _ = (∑ n ∈ Finset.range N, ea n)
            + ∑ n ∈ Finset.range N, (eb n - ea n) := Finset.sum_add_distrib
      _ = _ := by rw [hDN]
  have hDlim : Tendsto (fun N : ℕ => (1 / (N : ℂ)) * D) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun N => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat ‖D‖)
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast,
      div_mul_eq_mul_div, one_mul]
  have hlim := (h k hk).add hDlim
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop n₀] with N hN
  rw [← mul_add, ← hsum N hN]

/-! ## §2  The sliding-window setup -/

section VdC

variable (u : ℕ → ℂ) (N H : ℕ)

/-- `u` extended by zero outside `[0, N)` and shifted right by `H − 1`:
`padded u N H m = u (m − (H−1))` for `m ∈ [H−1, N+H−1)`, and `0` otherwise. -/
private def padded : ℕ → ℂ := fun m =>
  if H - 1 ≤ m ∧ m < N + H - 1 then u (m - (H - 1)) else 0

private lemma padded_shift (hH : 1 ≤ H) (n : ℕ) (hn : n < N) :
    padded u N H (n + (H - 1)) = u n := by
  have h1 : H - 1 ≤ n + (H - 1) := Nat.le_add_left _ _
  have h2 : n + (H - 1) < N + H - 1 := by omega
  simp [padded, h1, h2]

private lemma padded_eq_zero_low {m : ℕ} (hm : m < H - 1) :
    padded u N H m = 0 := by
  unfold padded
  rw [if_neg]
  rintro ⟨h1, -⟩
  omega

private lemma padded_eq_zero_high {m : ℕ} (hm : N + H - 1 ≤ m) :
    padded u N H m = 0 := by
  unfold padded
  rw [if_neg]
  rintro ⟨-, h2⟩
  omega

/-- **Window-sum identity**: summing any function with the same support as
`padded u N H` over all length-`H` windows `[q, q+H)`, `q < N+H−1`, counts
every point of `[H−1, N+H−1)` exactly `H` times. -/
private lemma window_sum {M : Type*} [AddCommMonoid M] (F : ℕ → M)
    (hH : 1 ≤ H)
    (hlow : ∀ m < H - 1, F m = 0) (hhigh : ∀ m, N + H - 1 ≤ m → F m = 0) :
    ∑ q ∈ range (N + H - 1), ∑ h ∈ range H, F (q + h)
      = H • ∑ p ∈ Ico (H - 1) (N + H - 1), F p := by
  rw [Finset.sum_comm]
  have hinner : ∀ h ∈ range H,
      ∑ q ∈ range (N + H - 1), F (q + h)
        = ∑ p ∈ Ico (H - 1) (N + H - 1), F p := by
    intro h hh
    have hhH : h ≤ H - 1 := by
      have := Finset.mem_range.mp hh; omega
    -- Reindex to `Ico h (N+H−1+h)`.
    have h1 : ∑ q ∈ range (N + H - 1), F (q + h)
        = ∑ p ∈ Ico h (N + H - 1 + h), F p := by
      rw [Finset.sum_Ico_eq_sum_range]
      have : N + H - 1 + h - h = N + H - 1 := by omega
      rw [this]
      exact Finset.sum_congr rfl fun q _ => by rw [Nat.add_comm h q]
    rw [h1]
    -- Shrink to the support `Ico (H−1) (N+H−1)`.
    refine (Finset.sum_subset ?_ ?_).symm
    · intro p hp
      have := Finset.mem_Ico.mp hp
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro p hp hnp
      have hpm := Finset.mem_Ico.mp hp
      rcases Nat.lt_or_ge p (H - 1) with hcase | hcase
      · exact hlow p hcase
      · refine hhigh p ?_
        by_contra hcon
        exact hnp (Finset.mem_Ico.mpr ⟨hcase, Nat.lt_of_not_le hcon⟩)
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range]

/-- The support-interval sum of `padded` recovers `∑_{n<N} u n`. -/
private lemma padded_support_sum (hH : 1 ≤ H) :
    ∑ p ∈ Ico (H - 1) (N + H - 1), padded u N H p
      = ∑ n ∈ range N, u n := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hcard : N + H - 1 - (H - 1) = N := by omega
  rw [hcard]
  exact Finset.sum_congr rfl fun n hn => by
    rw [Nat.add_comm (H - 1) n]
    exact padded_shift u N H hH n (Finset.mem_range.mp hn)

/-- Same, for the pointwise squared norms. -/
private lemma padded_support_sum_sq (hH : 1 ≤ H) :
    ∑ p ∈ Ico (H - 1) (N + H - 1), ‖padded u N H p‖ ^ 2
      = ∑ n ∈ range N, ‖u n‖ ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hcard : N + H - 1 - (H - 1) = N := by omega
  rw [hcard]
  exact Finset.sum_congr rfl fun n hn => by
    rw [Nat.add_comm (H - 1) n,
      padded_shift u N H hH n (Finset.mem_range.mp hn)]

/-! ## §3  Correlation extraction -/

/-- Shift reindexing: `∑_{q<K} F(q+h) = ∑_{p ∈ [h, K+h)} F p`. -/
private lemma sum_shift {M : Type*} [AddCommMonoid M] (F : ℕ → M) (K h : ℕ) :
    ∑ q ∈ range K, F (q + h) = ∑ p ∈ Ico h (K + h), F p := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hKh : K + h - h = K := by omega
  rw [hKh]
  exact Finset.sum_congr rfl fun q _ => by rw [Nat.add_comm q h]

/-- **Correlation identity**: the window cross-terms of gap `δ ≥ 1` recover
the plain correlation sum `∑_{n<N−δ} u(n+δ)·conj(uₙ)` of the original
sequence, independently of the window offset `h`. -/
private lemma corr_eq (hH : 1 ≤ H) (h δ : ℕ) (hδ : 1 ≤ δ) (hhδ : h + δ < H) :
    ∑ q ∈ range (N + H - 1),
        padded u N H (q + (h + δ)) * (starRingEnd ℂ) (padded u N H (q + h))
      = ∑ n ∈ range (N - δ), u (n + δ) * (starRingEnd ℂ) (u n) := by
  calc ∑ q ∈ range (N + H - 1),
          padded u N H (q + (h + δ)) * (starRingEnd ℂ) (padded u N H (q + h))
      = ∑ q ∈ range (N + H - 1),
          (fun p => padded u N H (p + δ)
            * (starRingEnd ℂ) (padded u N H p)) (q + h) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hidx : q + (h + δ) = (q + h) + δ := by omega
        rw [hidx]
    _ = ∑ p ∈ Ico h (N + H - 1 + h),
          padded u N H (p + δ) * (starRingEnd ℂ) (padded u N H p) :=
        sum_shift
          (fun p => padded u N H (p + δ) * (starRingEnd ℂ) (padded u N H p))
          (N + H - 1) h
    _ = ∑ p ∈ Ico (H - 1) (N + H - 1 - δ),
          padded u N H (p + δ) * (starRingEnd ℂ) (padded u N H p) := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro p hp
          have hpm := Finset.mem_Ico.mp hp
          exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · intro p hp hnp
          have hpm := Finset.mem_Ico.mp hp
          rcases Nat.lt_or_ge p (H - 1) with hc | hc
          · rw [padded_eq_zero_low u N H hc, map_zero, mul_zero]
          · have hhigh : N + H - 1 ≤ p + δ := by
              by_contra hcon
              exact hnp (Finset.mem_Ico.mpr ⟨hc, by omega⟩)
            rw [padded_eq_zero_high u N H hhigh, zero_mul]
    _ = ∑ n ∈ range (N - δ), u (n + δ) * (starRingEnd ℂ) (u n) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have hcard : N + H - 1 - δ - (H - 1) = N - δ := by omega
        rw [hcard]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hnN : n < N - δ := Finset.mem_range.mp hn
        have e1 : H - 1 + n + δ = (n + δ) + (H - 1) := by omega
        have e2 : H - 1 + n = n + (H - 1) := by omega
        rw [e1, e2, padded_shift u N H hH (n + δ) (by omega),
          padded_shift u N H hH n (by omega)]

/-! ## §4  The fundamental inequality -/

/-- The gap-`δ` correlation sum `∑_{n<N−δ} u(n+δ)·conj(uₙ)`. -/
private noncomputable def corr (δ : ℕ) : ℂ :=
  ∑ n ∈ range (N - δ), u (n + δ) * (starRingEnd ℂ) (u n)

/-- The `(h', h)` window cross-correlation `∑_{q<N+H−1} padded(q+h')·conj(padded(q+h))`. -/
private noncomputable def windowCorr (h' h : ℕ) : ℂ :=
  ∑ q ∈ range (N + H - 1),
    padded u N H (q + h') * (starRingEnd ℂ) (padded u N H (q + h))

/-- The diagonal window terms sum to `H · ∑‖uₙ‖²`. -/
private lemma windowCorr_diag_re (hH : 1 ≤ H) :
    ∑ h ∈ range H, (windowCorr u N H h h).re
      = (H : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2 := by
  have hwin := window_sum N H (fun m => ‖padded u N H m‖ ^ 2) hH
    (fun m hm => by simp [padded_eq_zero_low u N H hm])
    (fun m hm => by simp [padded_eq_zero_high u N H hm])
  calc ∑ h ∈ range H, (windowCorr u N H h h).re
      = ∑ h ∈ range H, ∑ q ∈ range (N + H - 1), ‖padded u N H (q + h)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun h _ => ?_
        simp only [windowCorr]
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Complex.mul_conj, Complex.ofReal_re, ← Complex.norm_mul_self_eq_normSq,
          pow_two]
    _ = ∑ q ∈ range (N + H - 1), ∑ h ∈ range H, ‖padded u N H (q + h)‖ ^ 2 :=
        Finset.sum_comm
    _ = H • ∑ p ∈ Ico (H - 1) (N + H - 1), ‖padded u N H p‖ ^ 2 := hwin
    _ = (H : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2 := by
        rw [padded_support_sum_sq u N H hH, nsmul_eq_mul]

/-- Below the diagonal (`h < h'`), a window cross-correlation *is* the plain
gap-`(h'−h)` correlation sum of the original sequence. -/
private lemma windowCorr_eq_corr (hH : 1 ≤ H) {h h' : ℕ} (hlt : h < h')
    (hh' : h' < H) :
    windowCorr u N H h' h = corr u N (h' - h) := by
  have hd : h + (h' - h) = h' := by omega
  have hce := corr_eq u N H hH h (h' - h) (by omega) (by omega)
  rw [hd] at hce
  exact hce

/-- Conjugating a window cross-correlation swaps its indices. -/
private lemma windowCorr_conj (h h' : ℕ) :
    (starRingEnd ℂ) (windowCorr u N H h' h) = windowCorr u N H h h' := by
  simp only [windowCorr, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

/-- Triangular-count bound, lower version: summing `g` of the gap over the
strictly lower triangle costs at most `H` copies of `∑_{1≤δ≤H−1} g(δ)`. -/
private lemma sum_triangle_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) :
    ∑ h' ∈ range H, ∑ h ∈ range h', g (h' - h)
      ≤ (H : ℝ) * ∑ j ∈ range (H - 1), g (j + 1) := by
  have hinner : ∀ h' ∈ range H,
      ∑ h ∈ range h', g (h' - h) ≤ ∑ j ∈ range (H - 1), g (j + 1) := by
    intro h' hh'
    have hh'H : h' < H := Finset.mem_range.mp hh'
    have hrefl : ∑ h ∈ range h', g (h' - h) = ∑ j ∈ range h', g (j + 1) := by
      rw [← Finset.sum_range_reflect (fun j => g (j + 1)) h']
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < h' := Finset.mem_range.mp hj
      change g (h' - j) = g (h' - 1 - j + 1)
      congr 1
      omega
    rw [hrefl]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr ?_) fun j _ _ => hg _
    omega
  calc ∑ h' ∈ range H, ∑ h ∈ range h', g (h' - h)
      ≤ ∑ _h' ∈ range H, ∑ j ∈ range (H - 1), g (j + 1) :=
        Finset.sum_le_sum hinner
    _ = (H : ℝ) * ∑ j ∈ range (H - 1), g (j + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Triangular-count bound, upper version. -/
private lemma sum_triangle_le' (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) :
    ∑ h' ∈ range H, ∑ h ∈ Ico (h' + 1) H, g (h - h')
      ≤ (H : ℝ) * ∑ j ∈ range (H - 1), g (j + 1) := by
  have hinner : ∀ h' ∈ range H,
      ∑ h ∈ Ico (h' + 1) H, g (h - h') ≤ ∑ j ∈ range (H - 1), g (j + 1) := by
    intro h' hh'
    have hh'H : h' < H := Finset.mem_range.mp hh'
    have hre : ∑ h ∈ Ico (h' + 1) H, g (h - h')
        = ∑ i ∈ range (H - (h' + 1)), g (i + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      omega
    rw [hre]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr ?_) fun j _ _ => hg _
    omega
  calc ∑ h' ∈ range H, ∑ h ∈ Ico (h' + 1) H, g (h - h')
      ≤ ∑ _h' ∈ range H, ∑ j ∈ range (H - 1), g (j + 1) :=
        Finset.sum_le_sum hinner
    _ = (H : ℝ) * ∑ j ∈ range (H - 1), g (j + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Splitting a square double sum into diagonal, lower and upper triangles. -/
private lemma sum_square_split (f : ℕ → ℕ → ℝ) :
    ∑ h' ∈ range H, ∑ h ∈ range H, f h' h
      = (∑ h ∈ range H, f h h)
        + ((∑ h' ∈ range H, ∑ h ∈ range h', f h' h)
            + ∑ h' ∈ range H, ∑ h ∈ Ico (h' + 1) H, f h' h) := by
  have hrow : ∀ h' ∈ range H,
      ∑ h ∈ range H, f h' h
        = f h' h' + (∑ h ∈ range h', f h' h + ∑ h ∈ Ico (h' + 1) H, f h' h) := by
    intro h' hh'
    have hh'H : h' < H := Finset.mem_range.mp hh'
    rw [← Finset.sum_range_add_sum_Ico (f h') (le_of_lt hh'H),
      Finset.sum_eq_sum_Ico_succ_bot hh'H]
    ring
  calc ∑ h' ∈ range H, ∑ h ∈ range H, f h' h
      = ∑ h' ∈ range H,
          (f h' h' + (∑ h ∈ range h', f h' h + ∑ h ∈ Ico (h' + 1) H, f h' h)) :=
        Finset.sum_congr rfl hrow
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- **Window-square bound**: the second moment of the sliding-window sums is
controlled by the diagonal plus `2H` copies of the correlation sums. -/
private lemma windowSq_le (hH : 1 ≤ H) :
    ∑ q ∈ range (N + H - 1), ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2
      ≤ (H : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2
        + 2 * (H : ℝ) * ∑ j ∈ range (H - 1), ‖corr u N (j + 1)‖ := by
  have hq : ∀ q : ℕ, ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2
      = ∑ h' ∈ range H, ∑ h ∈ range H,
          (padded u N H (q + h') * (starRingEnd ℂ) (padded u N H (q + h))).re := by
    intro q
    calc ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2
        = ((∑ h' ∈ range H, padded u N H (q + h')) *
            (starRingEnd ℂ) (∑ h ∈ range H, padded u N H (q + h))).re := by
          rw [Complex.mul_conj, Complex.ofReal_re,
            ← Complex.norm_mul_self_eq_normSq, pow_two]
      _ = ((∑ h' ∈ range H, padded u N H (q + h')) *
            (∑ h ∈ range H, (starRingEnd ℂ) (padded u N H (q + h)))).re := by
          rw [map_sum]
      _ = (∑ h' ∈ range H, ∑ h ∈ range H,
            padded u N H (q + h') * (starRingEnd ℂ) (padded u N H (q + h))).re := by
          rw [Finset.sum_mul_sum]
      _ = ∑ h' ∈ range H, ∑ h ∈ range H,
            (padded u N H (q + h') * (starRingEnd ℂ) (padded u N H (q + h))).re := by
          rw [Complex.re_sum]
          exact Finset.sum_congr rfl fun h' _ => by rw [Complex.re_sum]
  have hexpand : ∑ q ∈ range (N + H - 1),
        ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2
      = ∑ h' ∈ range H, ∑ h ∈ range H, (windowCorr u N H h' h).re := by
    calc ∑ q ∈ range (N + H - 1), ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2
        = ∑ q ∈ range (N + H - 1), ∑ h' ∈ range H, ∑ h ∈ range H,
            (padded u N H (q + h') * (starRingEnd ℂ) (padded u N H (q + h))).re :=
          Finset.sum_congr rfl fun q _ => hq q
      _ = ∑ h' ∈ range H, ∑ q ∈ range (N + H - 1), ∑ h ∈ range H,
            (padded u N H (q + h') * (starRingEnd ℂ) (padded u N H (q + h))).re :=
          Finset.sum_comm
      _ = ∑ h' ∈ range H, ∑ h ∈ range H, ∑ q ∈ range (N + H - 1),
            (padded u N H (q + h') * (starRingEnd ℂ) (padded u N H (q + h))).re :=
          Finset.sum_congr rfl fun h' _ => Finset.sum_comm
      _ = ∑ h' ∈ range H, ∑ h ∈ range H, (windowCorr u N H h' h).re :=
          Finset.sum_congr rfl fun h' _ => Finset.sum_congr rfl fun h _ => by
            rw [windowCorr, Complex.re_sum]
  have hlow : ∑ h' ∈ range H, ∑ h ∈ range h', (windowCorr u N H h' h).re
      ≤ (H : ℝ) * ∑ j ∈ range (H - 1), ‖corr u N (j + 1)‖ := by
    refine le_trans
      (Finset.sum_le_sum fun h' hh' => Finset.sum_le_sum fun h hh => ?_)
      (sum_triangle_le H (fun δ => ‖corr u N δ‖) fun δ => norm_nonneg _)
    have hh'H : h' < H := Finset.mem_range.mp hh'
    have hlt : h < h' := Finset.mem_range.mp hh
    calc (windowCorr u N H h' h).re
        ≤ ‖windowCorr u N H h' h‖ := Complex.re_le_norm _
      _ = ‖corr u N (h' - h)‖ := by rw [windowCorr_eq_corr u N H hH hlt hh'H]
  have hupp : ∑ h' ∈ range H, ∑ h ∈ Ico (h' + 1) H, (windowCorr u N H h' h).re
      ≤ (H : ℝ) * ∑ j ∈ range (H - 1), ‖corr u N (j + 1)‖ := by
    refine le_trans
      (Finset.sum_le_sum fun h' hh' => Finset.sum_le_sum fun h hh => ?_)
      (sum_triangle_le' H (fun δ => ‖corr u N δ‖) fun δ => norm_nonneg _)
    have hmem := Finset.mem_Ico.mp hh
    have hlt : h' < h := by omega
    have hhH : h < H := hmem.2
    calc (windowCorr u N H h' h).re
        ≤ ‖windowCorr u N H h' h‖ := Complex.re_le_norm _
      _ = ‖windowCorr u N H h h'‖ := by
          rw [← windowCorr_conj u N H h h', RCLike.norm_conj]
      _ = ‖corr u N (h - h')‖ := by rw [windowCorr_eq_corr u N H hH hlt hhH]
  calc ∑ q ∈ range (N + H - 1), ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2
      = (∑ h ∈ range H, (windowCorr u N H h h).re)
          + ((∑ h' ∈ range H, ∑ h ∈ range h', (windowCorr u N H h' h).re)
              + ∑ h' ∈ range H, ∑ h ∈ Ico (h' + 1) H, (windowCorr u N H h' h).re) := by
        rw [hexpand]
        exact sum_square_split H fun h' h => (windowCorr u N H h' h).re
    _ ≤ ((H : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2)
          + (((H : ℝ) * ∑ j ∈ range (H - 1), ‖corr u N (j + 1)‖)
              + (H : ℝ) * ∑ j ∈ range (H - 1), ‖corr u N (j + 1)‖) :=
        add_le_add (le_of_eq (windowCorr_diag_re u N H hH))
          (add_le_add hlow hupp)
    _ = (H : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2
          + 2 * (H : ℝ) * ∑ j ∈ range (H - 1), ‖corr u N (j + 1)‖ := by ring

/-- **Van der Corput's fundamental inequality** (Kuipers–Niederreiter,
Lemma 3.1, with the crude multiplicity bound `H` in place of `H−(j+1)` for
the correlation term of gap `j+1`):

```
(H·‖∑_{n<N} uₙ‖)² ≤ (N+H−1)·(H·∑_{n<N}‖uₙ‖²
                     + 2H·∑_{j<H−1} ‖∑_{n<N−(j+1)} u_{n+j+1}·conj(uₙ)‖).
``` -/
theorem vdc_fundamental_inequality (hH : 1 ≤ H) :
    ((H : ℝ) * ‖∑ n ∈ range N, u n‖) ^ 2
      ≤ ((N + H - 1 : ℕ) : ℝ) *
          ((H : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2
            + 2 * (H : ℝ) * ∑ j ∈ range (H - 1),
                ‖∑ n ∈ range (N - (j + 1)),
                    u (n + (j + 1)) * (starRingEnd ℂ) (u n)‖) := by
  have hwin : ∑ q ∈ range (N + H - 1), ∑ h ∈ range H, padded u N H (q + h)
      = (H : ℂ) * ∑ n ∈ range N, u n := by
    rw [window_sum N H (padded u N H) hH
        (fun m hm => padded_eq_zero_low u N H hm)
        (fun m hm => padded_eq_zero_high u N H hm),
      padded_support_sum u N H hH, nsmul_eq_mul]
  have hnorm : (H : ℝ) * ‖∑ n ∈ range N, u n‖
      = ‖∑ q ∈ range (N + H - 1), ∑ h ∈ range H, padded u N H (q + h)‖ := by
    rw [hwin, norm_mul, Complex.norm_natCast]
  have hCS : ‖∑ q ∈ range (N + H - 1), ∑ h ∈ range H, padded u N H (q + h)‖ ^ 2
      ≤ ((N + H - 1 : ℕ) : ℝ) *
          ∑ q ∈ range (N + H - 1), ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2 := by
    calc ‖∑ q ∈ range (N + H - 1), ∑ h ∈ range H, padded u N H (q + h)‖ ^ 2
        ≤ (∑ q ∈ range (N + H - 1), ‖∑ h ∈ range H, padded u N H (q + h)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (norm_sum_le (range (N + H - 1))
              (fun q => ∑ h ∈ range H, padded u N H (q + h))) 2
      _ ≤ ((N + H - 1 : ℕ) : ℝ) *
            ∑ q ∈ range (N + H - 1), ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2 := by
          have hcs := sq_sum_le_card_mul_sum_sq (s := range (N + H - 1))
            (f := fun q => ‖∑ h ∈ range H, padded u N H (q + h)‖)
          rwa [Finset.card_range] at hcs
  calc ((H : ℝ) * ‖∑ n ∈ range N, u n‖) ^ 2
      = ‖∑ q ∈ range (N + H - 1), ∑ h ∈ range H, padded u N H (q + h)‖ ^ 2 := by
        rw [hnorm]
    _ ≤ ((N + H - 1 : ℕ) : ℝ) *
          ∑ q ∈ range (N + H - 1), ‖∑ h ∈ range H, padded u N H (q + h)‖ ^ 2 := hCS
    _ ≤ ((N + H - 1 : ℕ) : ℝ) *
          ((H : ℝ) * ∑ n ∈ range N, ‖u n‖ ^ 2
            + 2 * (H : ℝ) * ∑ j ∈ range (H - 1),
                ‖∑ n ∈ range (N - (j + 1)),
                    u (n + (j + 1)) * (starRingEnd ℂ) (u n)‖) :=
        mul_le_mul_of_nonneg_left (windowSq_le u N H hH) (Nat.cast_nonneg _)

end VdC

/-! ## §5  Van der Corput's difference theorem -/

/-- Arithmetic endgame for the difference theorem: from the fundamental
inequality with `∑‖uₙ‖² = N`, eventual bounds `Q ≤ 2N` and `c ≤ N/2`, and
`4/H < ε²`, conclude that the normalized Weyl sum is below `ε`. -/
private lemma endgame {s c Q H N ε : ℝ}
    (hH1 : 1 ≤ H) (hN0 : 0 < N) (hc0 : 0 ≤ c)
    (hQ : Q ≤ 2 * N) (hc : c ≤ 1 / 2 * N) (hε : 0 < ε) (hHε : 4 / H < ε ^ 2)
    (hvdc : (H * s) ^ 2 ≤ Q * (H * N + 2 * H * c)) :
    s / N < ε := by
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le one_pos hH1
  rw [div_lt_iff₀ hN0]
  have h2 : (H * s) ^ 2 ≤ (2 * N) * (H * N + 2 * H * (1 / 2 * N)) := by
    refine hvdc.trans (mul_le_mul hQ ?_ ?_ (by positivity))
    · have hmul := mul_le_mul_of_nonneg_left hc
        (show (0 : ℝ) ≤ 2 * H by positivity)
      linarith
    · exact add_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (by norm_num) hH0.le) hc0)
  have h3 : H ^ 2 * s ^ 2 ≤ 4 * H * N ^ 2 := by
    calc H ^ 2 * s ^ 2 = (H * s) ^ 2 := by ring
      _ ≤ (2 * N) * (H * N + 2 * H * (1 / 2 * N)) := h2
      _ = 4 * H * N ^ 2 := by ring
  have hHe' : 4 < ε ^ 2 * H := by rwa [div_lt_iff₀ hH0] at hHε
  have h4 : H ^ 2 * s ^ 2 < H ^ 2 * (ε * N) ^ 2 := by
    have hpos : (0 : ℝ) < H * N ^ 2 := by positivity
    calc H ^ 2 * s ^ 2 ≤ 4 * H * N ^ 2 := h3
      _ = 4 * (H * N ^ 2) := by ring
      _ < ε ^ 2 * H * (H * N ^ 2) := mul_lt_mul_of_pos_right hHe' hpos
      _ = H ^ 2 * (ε * N) ^ 2 := by ring
  have h5 : s ^ 2 < (ε * N) ^ 2 := lt_of_mul_lt_mul_left h4 (by positivity)
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h5

/-- **Van der Corput's difference theorem** (Kuipers–Niederreiter,
Theorem 3.1): if for every `h ≥ 1` the difference sequence
`(a (n + h) − a n)ₙ` is uniformly distributed mod one, then so is `(a n)ₙ`.

Proof: fix a nonzero frequency `k` and let `e n = exp(2πi·k·aₙ)`.  The
fundamental inequality bounds `‖∑_{n<N} e n‖²` by
`(N+H−1)/H² · (H·N + 2H·∑_j ‖A_j(N)‖)`, where the correlation sums
`A_j(N) = ∑_{n<N−j} e(n+j)·conj(e n)` are `o(N)` by the hypothesis applied to
the gap-`j` difference sequence (Weyl criterion at frequency `k`).  Choosing
`H` with `4/H < ε²` and then `N` large makes the average less than `ε`. -/
theorem isUDModOne_of_forall_diff {a : ℕ → ℝ}
    (hdiff : ∀ h : ℕ, 1 ≤ h → IsUDModOne fun n => a (n + h) - a n) :
    IsUDModOne a := by
  intro k hk
  set e : ℕ → ℂ := fun n =>
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)) with he
  -- The Weyl exponentials are unimodular.
  have he_norm : ∀ n, ‖e n‖ = 1 := by
    intro n
    change ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ))‖ = 1
    have hexp : 2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)
        = ((2 * Real.pi * k * a n : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, Complex.norm_exp_ofReal_mul_I]
  -- Correlation terms are the Weyl exponentials of the difference sequence.
  have he_corr : ∀ h n : ℕ, e (n + h) * (starRingEnd ℂ) (e n)
      = Complex.exp
          (2 * Real.pi * Complex.I * (k : ℂ) * ((a (n + h) - a n : ℝ) : ℂ)) := by
    intro h n
    change Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a (n + h) : ℂ))
        * (starRingEnd ℂ)
            (Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a n : ℂ)))
        = _
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      map_intCast]
    push_cast
    ring
  have hv_norm : ∀ h n : ℕ, ‖e (n + h) * (starRingEnd ℂ) (e n)‖ = 1 := by
    intro h n
    rw [norm_mul, RCLike.norm_conj, he_norm, he_norm, one_mul]
  -- Correlation sums are `o(N)`: the hypothesis via the Weyl criterion.
  have hA : ∀ h : ℕ, 1 ≤ h →
      Tendsto (fun N : ℕ =>
          ‖∑ n ∈ range (N - h), e (n + h) * (starRingEnd ℂ) (e n)‖ / (N : ℝ))
        atTop (nhds 0) := by
    intro h hh
    have hd := hdiff h hh k hk
    have hd' : Tendsto (fun N : ℕ =>
        (1 / (N : ℂ)) * ∑ n ∈ range N, e (n + h) * (starRingEnd ℂ) (e n))
        atTop (nhds 0) := by
      refine hd.congr fun N => ?_
      congr 1
      exact Finset.sum_congr rfl fun n _ => (he_corr h n).symm
    have hd2 : Tendsto (fun N : ℕ =>
        ‖∑ n ∈ range N, e (n + h) * (starRingEnd ℂ) (e n)‖ / (N : ℝ))
        atTop (nhds 0) := by
      have hnorm := hd'.norm
      rw [norm_zero] at hnorm
      refine hnorm.congr fun N => ?_
      rw [norm_mul, norm_div, norm_one, Complex.norm_natCast,
        div_mul_eq_mul_div, one_mul]
    have hg : Tendsto (fun N : ℕ =>
        ‖∑ n ∈ range N, e (n + h) * (starRingEnd ℂ) (e n)‖ / (N : ℝ)
          + (h : ℝ) / N) atTop (nhds 0) := by
      have hadd := hd2.add (tendsto_const_div_atTop_nhds_zero_nat (h : ℝ))
      rwa [add_zero] at hadd
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hg
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hnum : ‖∑ n ∈ range (N - h), e (n + h) * (starRingEnd ℂ) (e n)‖
        ≤ ‖∑ n ∈ range N, e (n + h) * (starRingEnd ℂ) (e n)‖ + (h : ℝ) := by
      have hsplit := Finset.sum_range_add_sum_Ico
        (fun n => e (n + h) * (starRingEnd ℂ) (e n)) (Nat.sub_le N h)
      have hIco : ‖∑ n ∈ Ico (N - h) N, e (n + h) * (starRingEnd ℂ) (e n)‖
          ≤ (h : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ n ∈ Ico (N - h) N, ‖e (n + h) * (starRingEnd ℂ) (e n)‖
            = ∑ _n ∈ Ico (N - h) N, (1 : ℝ) :=
              Finset.sum_congr rfl fun n _ => hv_norm h n
          _ = ((N - (N - h) : ℕ) : ℝ) := by
              rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          _ ≤ (h : ℝ) := by
              have hle : N - (N - h) ≤ h := by omega
              exact_mod_cast hle
      calc ‖∑ n ∈ range (N - h), e (n + h) * (starRingEnd ℂ) (e n)‖
          = ‖(∑ n ∈ range N, e (n + h) * (starRingEnd ℂ) (e n))
              - ∑ n ∈ Ico (N - h) N, e (n + h) * (starRingEnd ℂ) (e n)‖ := by
            rw [← hsplit]
            congr 1
            ring
        _ ≤ ‖∑ n ∈ range N, e (n + h) * (starRingEnd ℂ) (e n)‖
              + ‖∑ n ∈ Ico (N - h) N, e (n + h) * (starRingEnd ℂ) (e n)‖ :=
            norm_sub_le _ _
        _ ≤ _ := by linarith
    calc ‖∑ n ∈ range (N - h), e (n + h) * (starRingEnd ℂ) (e n)‖ / (N : ℝ)
        ≤ (‖∑ n ∈ range N, e (n + h) * (starRingEnd ℂ) (e n)‖ + (h : ℝ))
            / (N : ℝ) := by gcongr
      _ = ‖∑ n ∈ range N, e (n + h) * (starRingEnd ℂ) (e n)‖ / (N : ℝ)
            + (h : ℝ) / N := add_div _ _ _
  -- Unimodularity: the second moment is exactly `N`.
  have hsum1 : ∀ N : ℕ, ∑ n ∈ range N, ‖e n‖ ^ 2 = (N : ℝ) := by
    intro N
    calc ∑ n ∈ range N, ‖e n‖ ^ 2
        = ∑ _n ∈ range N, (1 : ℝ) :=
          Finset.sum_congr rfl fun n _ => by rw [he_norm n, one_pow]
      _ = (N : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- The ε-argument.
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨H, hH1, hHε⟩ : ∃ H : ℕ, 1 ≤ H ∧ 4 / (H : ℝ) < ε ^ 2 := by
    obtain ⟨H₀, hH₀⟩ := exists_nat_gt (4 / ε ^ 2)
    refine ⟨H₀ + 1, Nat.le_add_left 1 H₀, ?_⟩
    have hpos : (0 : ℝ) < ((H₀ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos H₀
    have hlt : 4 / ε ^ 2 < ((H₀ + 1 : ℕ) : ℝ) := by
      push_cast
      push_cast at hH₀
      linarith
    rw [div_lt_iff₀ (pow_pos hε 2)] at hlt
    rw [div_lt_iff₀ hpos]
    exact hlt.trans_eq (mul_comm _ _)
  have hCsum : Tendsto (fun N : ℕ => ∑ j ∈ range (H - 1),
      ‖∑ n ∈ range (N - (j + 1)), e (n + (j + 1)) * (starRingEnd ℂ) (e n)‖
        / (N : ℝ)) atTop (nhds 0) := by
    have hfin := tendsto_finset_sum (range (H - 1))
      (fun j _ => hA (j + 1) (Nat.le_add_left 1 j))
    rwa [Finset.sum_const_zero] at hfin
  have hslow := hCsum.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hslow, eventually_ge_atTop H, eventually_ge_atTop 1]
    with N hCN hNH hN1
  change ‖(1 / (N : ℂ)) * ∑ n ∈ range N, e n‖ < ε
  have hgoal : ‖(1 / (N : ℂ)) * ∑ n ∈ range N, e n‖
      = ‖∑ n ∈ range N, e n‖ / (N : ℝ) := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast,
      div_mul_eq_mul_div, one_mul]
  rw [hgoal]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hvdc := vdc_fundamental_inequality e N H hH1
  rw [hsum1 N] at hvdc
  have hc0 : (0 : ℝ) ≤ ∑ j ∈ range (H - 1),
      ‖∑ n ∈ range (N - (j + 1)), e (n + (j + 1)) * (starRingEnd ℂ) (e n)‖ :=
    Finset.sum_nonneg fun j _ => norm_nonneg _
  have hQ2 : ((N + H - 1 : ℕ) : ℝ) ≤ 2 * N := by
    have hq : (N + H - 1 : ℕ) ≤ 2 * N := by omega
    calc ((N + H - 1 : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := Nat.cast_le.mpr hq
      _ = 2 * N := by push_cast; ring
  rw [← Finset.sum_div, div_le_iff₀ hN0] at hCN
  exact endgame (by exact_mod_cast hH1) hN0 hc0 hQ2 hCN hε hHε hvdc

end Gram.UD
