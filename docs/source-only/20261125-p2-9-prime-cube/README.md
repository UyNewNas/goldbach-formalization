# The original prime tuple lies in the target coordinate cube

**Status: SOURCE_ONLY_UNCOMPILED. Formal, kernel, endpoint and new native credit: 0.**

This package proves the missing coordinate bound for the complete Gamma5 prime tuple under its explicit carrier condition `M≤2N`. Every coordinate is at most `N`, so the same values fit `Fin(N+1)`. For `N≥2`, the existing original logarithmic-unit lemma then places the full tuple and the exact old-coordinate function in the original atlas `Cube`.

The complete-product condition remains `M≤2N` throughout. No conclusion `M≤N`, distinct-prime hypothesis, additional coprimality condition, or replacement product cutoff is introduced.

## Two thin layers

### Standard arithmetic core

`P2PrimeProductCoordinateCore.lean` imports only standard Mathlib and the standard Omega tactic. For `u : Fin d → ℕ`, `d≥2` and every `u_i≥2`, it proves

\[
 2u_i\le\prod_j u_j.
\]

The proof chooses another **position** `j≠i`. The values `u_j` and `u_i` may be equal. The existing fixed-pin `Finset.mul_le_prod` supplies
\(u_i u_j\le\prod u\), and `u_j≥2` supplies the required factor two.

The second public theorem cancels the factor two:

\[
 \prod_j u_j\le2N\quad\Longrightarrow\quad u_i\le N.
\]

No prime-factorization, analytic estimate, product-fibre argument, or new logarithm theorem is needed.

### Gamma5 and original Cube adapter

`P2FiniteMarkedGamma5PrimeCube.lean` specializes that result to the unchanged complete coordinate order `Fin(k+(2+r))`. Its two fresh slots ensure the rank is at least two even when `k=r=0`. Primality supplies each lower bound `2≤u_i`.

It provides:

- `prime_coordinates_le_target`: every slot is at most `N`.
- `prime_tuple_in_target_carrier`: a tuple in `Fin(N+1)` with exactly the same natural value at every position.
- `bounded_prime_tuple_in_target_carrier`: the same coordinate-preserving existence result from the original `Fin(2*N+1)` enumerator, under the explicit complete-product carrier condition.
- `prime_log_cube`: all original `log(u_i)/log N` coordinates lie in the unchanged `JointQueryEnclosure.Cube` for `N≥2`.
- `old_log_cube`: the precise `AtlasEulerBudget.oldLogCoordinates` function lies in that same Cube.

The transport statements preserve every individual coordinate. They do not sort or quotient the tuple and do not claim a history-sum reindexing theorem or a NativeSlot dictionary.

The logarithmic step directly reuses
`Part5OriginalH430SmoothPrefixRequests.physicalPrime_unit`. Its proof is not repeated. The condition `N≥2` is explicit at the logarithmic endpoints. The coordinate inequality and finite-carrier transport need no additional lower bound on `N`.

## Inputs and source boundaries

| Supplier | Exact Git blob / pin |
|---|---|
| Previous Atlas Euler budget | `51dfcfd07e9ce447a3e79ba25d34627a61f47de0` |
| Original SmoothPrefixRequests | `be8f6425f8444be63f96659f0c0bd4b0c5af3c3a` |
| Original JointQueryEnclosure Cube, inherited through the atlas budget | `d3141bf52bb42f486d8d4f1c0e4924fe0ab480ad` |
| Mathlib pin | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| Fixed-pin `Finset.mul_le_prod` owner | `3745e5cb7ff4b16ad6532357837698f4bf54c4a8` |

The standard core can be considered separately from the adapter's existing history imports. This package grants neither layer compile or kernel credit and does not qualify the old atlas/history receiving closure.

The adapter inherits the exact scalar/Euler/Family owner choices from the atlas-budget REGISTRY `cbeccf170c1e729e2a4b0ada1fcdf66a885d7632`. In particular, the current full Family owner postimage `a32b53fa19810f21d6e3e990d59ab113202d7ec3` takes priority when reachable with the extracted core. No existing source, queued module or accepted object is modified.

## Reuse and duplicate check

The relevant existing definitions in `FinitePrimeGeometryCore` were checked; they supply the original prime-box/logarithmic dictionaries but not this factor-two coordinate consequence. `PrimeCubeCutoff` concerns the strict arithmetic test `p^3<R` and cube-root cutoffs. `FrozenIntegerSupport` gives original history support. The needed logarithmic unit interval already exists in `SmoothPrefixRequests` and is reused here.

The existing Gamma5 physical/profile complete-product cap is not reproved. Callers supply its already-established consequence `M≤2N` as the explicit carrier condition to this small arithmetic bridge.

## Manuscript scope

The elementary consequence is used with the finite labelled prime-product family of the frozen 1106 manuscript (`argument.tex`, lines 359–374 and 400–407), the original Gamma5 pair/rough source (`sieve-appendix.tex`, lines 634–660), and the retained old coordinates (`sieve-appendix.tex`, lines 494–513). This fills an omitted finite arithmetic/coordinate deduction.

No new manuscript analytic assumption is added. Actual selected-history mask identification, NativeSlot occurrence dictionaries, ordinary-mass transport for those smooth masks, original-J and distribution/PP licences remain separate. The 29 H247/native-Wu binder endpoints remain a separate sufficient-condition/compatibility branch; their necessity for the manuscript's actual enhanced finite-family conclusion is unproved.

## Validation

The source was statically checked against the exact original Cube and logarithmic-unit interfaces and the fixed Mathlib product lemma. It preserves repeated values, empty old/tail blocks, the inclusive `2N` product boundary and the explicit low-target restriction on logarithms.

No Lean compilation, kernel replay, owned audit, cloud job, active installation, commit or ref movement was performed. Only exact source and document Git blobs were created.
