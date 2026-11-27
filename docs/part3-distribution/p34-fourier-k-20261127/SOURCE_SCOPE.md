# Existing Fourier–K suppliers: scope and source repairs

Baseline: PR #8 at `6a91582b56814dd0133a7e36094efabb2f6dcecd`.

The continuation verifies these existing modules:

1. `Part3ActualRamanujanBesselNormalConvergence`: an explicit summable
   exponential-polynomial majorant for the actual divisor/K terms, uniform on
   closed real-part strips and all heights above a positive lower bound. Both
   nonzero signs and entire parameter dependence are included **before** the
   common meromorphic Gamma/zeta factor.
2. `Part3ActualEisensteinCanonicalFourier`: scalar coefficients of the actual
   level-one parabolic sum and its actual primitive-pair counterpart, for real
   `s > 1`, positive height and arbitrary signed integer frequency. The actual
   totient and Ramanujan Dirichlet series evaluate the arithmetic factors.
3. `Part3ActualComplexEisensteinCanonicalFourier`: identification of the actual
   primitive Fourier integral with its explicit canonical value for `Re(s)>1`.
   The analytic identity principle extends the proved real identity. Zero and
   nonzero frequencies retain separate public endpoints.

The existing `EisensteinSeries.gammaSet 1 1 0`, orientation factor `1/2`,
integration interval `0..1` and negative coefficient phase are preserved. The
nonzero coefficient retains factor `2`, `|n|`, the actual finite divisor sum,
Gamma/zeta denominator and the actual positive-axis K integral. The independent
endpoint file includes a fully expanded nonzero formula and the literal vector
action of `primitivePairEquiv`.

## Repair boundary

The original sources were not a successfully elaborated baseline for this
closure. The continuation repairs 31 existing production modules and adds no
explicit production mathematical declaration. Their old source-only comments
remain provenance, not a description of this dated receipt.

Repairs include current theorem namespaces and argument lists, beta reduction
before rewrites, pointwise congruence under sums/integrals, current measure and
summability APIs, explicit matrix entries, and unused proof tactics. The ASCII
`+/-` in two block comments was a nested Lean comment opener; it is now `±`.

Several expressions originally requested the nonexistent `HPow Complex Real`
instance by propagating an expected complex type into a real power. Those
expressions now explicitly compute the real power before coercion to complex.
Real sums/integrals likewise receive explicit real type annotations where
needed. The obsolete `AddCircle.fourier` names refer to the existing global
`fourier`. The modular action is explicitly performed on the upper half plane
before coercion to complex. These corrections make the intended original
formulas elaborate; **compiled signature equality against ill-typed original
expressions is not claimed**. No theorem premise is added or removed.

The proof body of `primitivePairEquiv` now composes Mathlib's original primitive
pair bijection with `Equiv.setCongr` instead of an opaque type cast. Its actual
underlying row map is checked by `rfl`; the seed and Eisenstein definitions are
unchanged mathematically. The final full compiler types are part of the evidence.

## Inventory conventions

The three targets have 55 pre-existing explicit declarations: 42 theorems and
13 definitions. Compiler-generated constants bring their owner-based inventory
to 72 records: 59 theorem constants and 13 definitions. Per target the explicit
counts are 19, 13 and 23; the compiler counts are 25, 19 and 28. These are internal
construction declarations, not 55 new numbered manuscript claims.

The actual project closure has 105 modules and 2,537 compiler records. This
includes the earlier three accepted analytic suppliers and the older general
project dependencies; it is not a new cumulative total obtained by adding
historical acceptance counts. All 59 Part3/P0Ramanujan modules reject warnings.
The 46 untouched older general dependencies use normal compiler warnings.

## Remaining P3.4 boundary

This scope is entirely in the initial half plane, together with entire
parameter dependence of the prefactor-free K kernel. It does not supply
critical-line continuation, all-level Gamma0 automorphy, R22, the nonzero
Fricke/Whittaker amplitude attachment, DI normalization, ABL dilation or a
continuous Plancherel normalization. Full P3.4 remains incomplete.

The next all-level continuation source closure exists (133 project modules,
105 overlapping this checkpoint). It has not been compiled or accepted by this
receipt. In the bounded current checkout, the exact original
`Part3ActualFrickeNonzeroFourier.lean`,
`Part3OriginalMediumPhysicalE3Block.lean`, and
`Part3OriginalMediumDoubleLambdaColorWindows.lean` remain absent. This is a local
source-availability observation, not a global nonexistence or manuscript-gap
claim. No replacement spectral identity is inserted as an assumption.
