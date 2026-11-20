# Declaration correspondence — source review only

The original file cannot elaborate at the fixed dependency pin. Therefore this comparison records the intended mathematical statements from the already existing upstream source, not a kernel equality between two elaborated old-pin declarations. ROOT expressly allowed the necessary explicit complex coefficient-ring API adaptation after the actual declaration-head errors were identified. We do not claim that every declaration header remains literally unchanged.

## derivative_logOf_mul_self

Before:

```lean
theorem derivative_logOf_mul_self
    {f : ℂ⟦X⟧} (hf : constantCoeff f = 1) :
    d⁄dX (logOf f) * f = d⁄dX f
```

After:

```lean
theorem derivative_logOf_mul_self
    {f : ℂ⟦X⟧} (hf : constantCoeff f = 1) :
    d⁄dX ℂ (logOf f) * f = d⁄dX ℂ f
```

| Component | Before and after |
|---|---|
| Quantifier | The same implicit formal series `f : ℂ⟦X⟧`. |
| Hypothesis | Exactly `constantCoeff f = 1`. |
| Objects | The same `f`, formal `logOf f`, multiplication, and equality in `ℂ⟦X⟧`. |
| Derivative | The formal complex-coefficient power-series derivative. The old-pin API requires the explicit argument `ℂ`. |
| Conclusion | `D(logOf f) * f = D(f)`; no extra assumption or restricted domain. |

The only head edits are the two explicit coefficient-ring arguments. The body adds one local identity for the logarithm series because the upstream named lemma is absent at the fixed pin. It does not add a global declaration or hypothesis.

## coeff_derivative_KSeries

Before:

```lean
theorem coeff_derivative_KSeries (K : ℕ → ℂ) (n : ℕ) :
    coeff n (d⁄dX (KSeries K)) = K (n + 1)
```

After:

```lean
theorem coeff_derivative_KSeries (K : ℕ → ℂ) (n : ℕ) :
    coeff n (d⁄dX ℂ (KSeries K)) = K (n + 1)
```

| Component | Before and after |
|---|---|
| Quantifiers | Exactly `K : ℕ → ℂ` and `n : ℕ`. |
| Hypotheses | None added or removed. |
| Objects | The same coefficient map, `KSeries K`, and index `n + 1`. |
| Derivative | The same formal derivative on `ℂ⟦X⟧`, now explicitly instantiated at `ℂ`. |
| Conclusion | The same coefficient identity for every natural `n`. |

All 15 declaration headers, before and after, are retained in `STATIC_SOURCE_REVIEW.json`. The remaining 13 headers are byte-for-byte identical as extracted. All three import lines and all top-level declaration names are unchanged. No notation, definitional wrapper, axiom, premise, weakened endpoint, or new global declaration was introduced.
