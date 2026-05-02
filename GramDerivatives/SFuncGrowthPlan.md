# Plan for `iteratedDeriv_φ`

Target theorem (file `GramDerivatives/SFuncGrowth.lean`, line 285):

```lean
theorem iteratedDeriv_φ (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv n φ t =
      (-1 : ℝ) ^ (n - 1) * (n - 2).factorial
        * (1 / (2 * Real.pi)) * t ^ (1 - (n : ℝ))
```

where `φ t = -(t/(2π)) · log(t/(2π)) + t/(2π) - 7/8`.

## Mathematical strategy

The cleanest path uses the fact that `φ` becomes simple after **one** derivative:

```
φ(t)  = -(t/(2π)) · log(t/(2π)) + t/(2π) - 7/8
φ'(t) = -(1/(2π)) · log(t/(2π))                       (on t > 0; matches eq. (4) of the paper)
      = -(1/(2π)) · log(t)  +  log(2π)/(2π)            (split via log_div)
```

For `n ≥ 2`, write `n = m + 2`. Then

```
iteratedDeriv (m+2) φ t  =  iteratedDeriv (m+1) (deriv φ) t           -- iteratedDeriv_succ'
                        =  iteratedDeriv (m+1) ψ t                     -- ψ = closed form on (0,∞)
                        =  -(1/(2π)) · iteratedDeriv (m+1) log t  + 0  -- linearity; constant dies
                        =  -(1/(2π)) · (-1)^m · m! · t^(-(m+1))         -- iteratedDeriv_log (k=m+1)
                        =  (-1)^(m+1) · m! · (1/(2π)) · t^(1-(m+2))
                        =  (-1)^(n-1) · (n-2)! · (1/(2π)) · t^(1-n)
```

Crucially, the hypothesis `n ≥ 2` is what guarantees `n − 1 ≥ 1`, which is what kills the constant `log(2π)/(2π)` under `iteratedDeriv (m+1)`.

## Lean proof outline

### Step 0 — reshape the index

```lean
obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
clear hn
-- normalize: (m+2) - 1 = m + 1, (m+2) - 2 = m, (1 - ((m+2):ℝ)) = -((m+1):ℝ)
```

This avoids `Nat.sub` arithmetic later.

### Step 1 — first derivative of `φ` on `(0, ∞)`

State and prove a `HasDerivAt` for `φ`:

```lean
have hφ' : ∀ s, 0 < s →
    HasDerivAt φ (-(1 / (2 * Real.pi)) * Real.log (s / (2 * Real.pi))) s
```

Build it from primitives:

- `Real.hasDerivAt_log (ne_of_gt hs)` gives `HasDerivAt log s⁻¹ s`.
- `(hasDerivAt_id s).div_const (2*Real.pi)` for `s ↦ s/(2π)`.
- Combine via `.log` (composition through `s/(2π)` requires log of a positive number — use `Real.hasDerivAt_log` on `s/(2π)` and chain-rule with the inner derivative `1/(2π)`).
- `(hs/(2π) ↦ log) .mul (s ↦ -(s/(2π)))` for the product term, then `.add` the linear term, then `.sub_const (7/8)`.
- Algebraic clean-up: the inner `-s/(2π) · 1/(s/(2π)) · 1/(2π) = -1/(2π)` cancels with the `+1/(2π)` from the linear term (this is exactly what makes the final answer clean).

### Step 2 — split the log

Simplify `deriv φ` pointwise on `(0,∞)`:

```lean
have hderivφ : ∀ s, 0 < s →
    deriv φ s = -(1 / (2 * Real.pi)) * Real.log s
              + Real.log (2 * Real.pi) / (2 * Real.pi) := by
  intro s hs
  rw [(hφ' s hs).deriv, Real.log_div (ne_of_gt hs) (by positivity)]
  ring
```

### Step 3 — peel one derivative

```lean
rw [show m + 2 = (m + 1) + 1 from rfl, iteratedDeriv_succ']
-- goal: iteratedDeriv (m+1) (deriv φ) t = …
```

### Step 4 — replace `deriv φ` with the closed form on a neighbourhood

Define

```lean
set ψ : ℝ → ℝ :=
  fun s => -(1 / (2 * Real.pi)) * Real.log s
         + Real.log (2 * Real.pi) / (2 * Real.pi)
```

and show

```lean
have hEq : deriv φ =ᶠ[nhds t] ψ := by
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs using hderivφ s hs
```

Now we need: `iteratedDeriv (m+1) (deriv φ) t = iteratedDeriv (m+1) ψ t`. Mathlib provides this as `Filter.EventuallyEq.iteratedDeriv_eq` (variant: `iterated_deriv_within_eqOn`). If the exact name is missing in this Mathlib pin, prove a small helper by induction on `k`:

```lean
lemma iteratedDeriv_congr_of_nhds {f g : ℝ → ℝ} {t : ℝ}
    (h : f =ᶠ[nhds t] g) (k : ℕ) :
    iteratedDeriv k f t = iteratedDeriv k g t
```

The induction step uses that `f =ᶠ[nhds s] g` on a whole neighbourhood (open set), so `deriv (iteratedDeriv k f) t = deriv (iteratedDeriv k g) t` via `Filter.EventuallyEq.deriv_eq` plus the inductive equality propagated on the open set. Concretely: take `U = Set.Ioi 0`, prove `iteratedDeriv k (deriv φ) =ᶠ[nhds t] iteratedDeriv k ψ` (not just at `t`) by `filter_upwards [isOpen_Ioi.mem_nhds ht]` and reuse the IH at each `s ∈ U`.

After the rewrite:

```lean
-- goal: iteratedDeriv (m+1) ψ t = …
```

### Step 5 — additivity

ψ is `(linear in log) + (constant)`. Use

```lean
iteratedDeriv_add  -- needs ContDiff ℝ (m+1) for both summands on a neighbourhood
```

On `(0,∞)`, `Real.log` is `ContDiff ℝ ⊤` (use `Real.contDiffOn_log` or the global `Real.differentiable…`-tower restricted to `Ioi 0`), and the constant is `ContDiff ℝ ⊤` trivially. To stay global, you can use `iteratedDeriv_add` with the unconditional Mathlib version `iteratedDeriv_add (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)` — but `Real.log` is *not* `ContDiff` globally (singular at 0).

**Workaround**: keep working on the open set. Simpler alternative — peel derivatives one at a time using `iteratedDeriv_succ` plus `deriv_add` (which is unconditional when both are differentiable at the point). Concretely, prove by induction on `k`:

```lean
∀ s, 0 < s →
  iteratedDeriv k ψ s
    = -(1 / (2 * Real.pi)) * iteratedDeriv k Real.log s
      + (if k = 0 then Real.log (2 * Real.pi) / (2 * Real.pi) else 0)
```

The base case is by definition; the step case uses `deriv_add`, `deriv_const_mul`, `deriv_const`, plus `Real.log` being differentiable at `s > 0`. This avoids needing global `ContDiff`.

### Step 6 — apply `iteratedDeriv_log`

With `k = m + 1 ≥ 1`:

```lean
iteratedDeriv (m+1) Real.log t
  = (-1)^m * m.factorial * t ^ (-((m+1):ℝ))     -- by iteratedDeriv_log
```

(uses `m + 1 - 1 = m`).

### Step 7 — algebraic finish

Goal becomes:

```
-(1/(2π)) * ((-1)^m * m! * t^(-(m+1))) + 0
  =  (-1)^(m+1) * m! * (1/(2π)) * t^(1-(m+2))
```

- Push the minus sign into the power: `-(1) * (-1)^m = (-1)^(m+1)` via `pow_succ`.
- Match exponents: `-((m+1):ℝ) = 1 - ((m+2):ℝ)` by `push_cast; ring`.
- `m.factorial = ((m+2)-2).factorial` by `rfl` (after the `Nat.add_sub_cancel`-style normalization from Step 0).
- Close with `ring`.

## Risk register / where this can stick

1. **`Filter.EventuallyEq.iteratedDeriv_eq`**: existence/exact name in this Mathlib pin. Mitigation: hand-rolled `iteratedDeriv_congr_of_nhds` (≈10 lines).
2. **`iteratedDeriv_add` / `iteratedDeriv_const_mul`**: the global versions require `ContDiff`, which fails for `log` globally. Mitigation: induct manually on `k` using the local `deriv_add`/`deriv_const_mul` (Step 5 workaround).
3. **`HasDerivAt` for `φ`**: chain-rule bookkeeping for `log (s/(2π))` is the fiddliest piece. Easiest path is to rewrite `φ s` as `-(1/(2π)) * s * log s + ((1 + log(2π))/(2π)) * s - 7/8` *first* (using `Real.log_div`), then differentiate the polynomial-times-log form directly — this skips the inner chain rule altogether.

## Suggested alternative (often shorter)

Inline the rewrite trick from risk #3 and use `t · log t` as the only non-trivial atom:

```lean
have hφ_eq : ∀ s, 0 < s →
    φ s = -(1/(2*Real.pi)) * (s * Real.log s)
        + ((1 + Real.log (2*Real.pi)) / (2*Real.pi)) * s
        - 7/8
```

Then the n-th derivative is `-(1/(2π)) · (d/dt)^n[t·log t]` for `n ≥ 2`, and `(d/dt)^n[t·log t]` is computed by the same `deriv`-then-`iteratedDeriv_log` trick (its first derivative is `log t + 1`, which lives in the realm `iteratedDeriv_log` already handles). This collapses Steps 4–5 into a single induction.

**Estimated size**: 60–90 lines, dominated by the `HasDerivAt` calculation in Step 1 and the `iteratedDeriv_congr_of_nhds` helper if needed.
